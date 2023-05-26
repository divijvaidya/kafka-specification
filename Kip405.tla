(*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements. See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
------------------------------- MODULE Kip405 -------------------------------
(*  An model demonstrating the Apache Kafka replication protocol after the 
    changes introduced by Kafka Tiered Storage (KIP-405).
*)
EXTENDS KafkaReplication, TLC

---------------------------------------------------------------------------
LOCAL GetLocalLogStartOffset(replica) == ReplicaLog!GetStartOffset(replica)

---------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

(*
 * Expiration of data in each replica based on the configured data retention settings.
 * 
 * With KIP 405, a replica cannot exire the data until the data has been archived. Replica fetches
 * this information from RLMM.
 *)
ReplicaDataExpireKIP405 ==
    /\ \E replica \in Replicas: \* TODO - should this be \A
        /\ ~RemoteLog!IsEmpty \* For optimization, only enable this state if remote log is non-empty
        /\ \E tillOffset \in GetCommittedOffsets(replica):
            /\ tillOffset < RemoteLog!GetEndOffset \* tillOffset should be present in remote storage
            /\ ReplicaLog!TruncateFromTailTillOffset(replica, tillOffset)
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * Entry criteria for this state: follower's endOffset < leader's local start offset
 * 1. Follower fetches data from leader about target epoch
 * 2. Follower builds history till that epoch from remote storage 
 * 3. Follower truncates from start until
 * 4. Follower fetches
 *)
\* targetEpoch should be defined at entry
\* leader should have a local start offset > follower end offset (after truncation)
\* follower should truncate from the start till leader.localLogstartOffset 
\* after this follower should have a localLogStartOffset = leaderLogStartOffset
\* followers epoch history chain.end >= targetEpoch
\*
FollowerBuildAuxState == \E leader, follower \in Replicas :
    /\ IsFollowingLeaderEpoch(leader, follower)
    \* The next conditions are to ensure that when we talk to the leader, leader should treat itself as leader.
    /\ ReplicaPresumesLeadership(leader)
    \* This is the enabling condition for going into BuildAux state
    /\ ReplicaLog!GetEndOffset(follower) < GetLocalLogStartOffset(leader) \* TODO - add another condition that this is available globally
    \* Truncate from start till leader's local log start offset
    \* This also updates the start offset & end offset of the follower
    /\ ReplicaLog!TruncateFullyAndStartAt(follower, GetLocalLogStartOffset(leader))
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(*
 * A replica which assumes itself to be the leader will write data to the remote storage till it's High watermark.
 *) 
LeaderArchiveToRemoteStorage == \E leader \in Replicas :
       /\ ReplicaPresumesLeadership(leader)
       /\ RemoteLog!GetEndOffset < GetHighWatermark(leader)
       /\ RemoteLog!Append(ReplicaLog!GetRecordAtOffset(leader, RemoteLog!GetEndOffset), RemoteLog!GetEndOffset)
       /\ UNCHANGED <<nextRecordId, replicaLog, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

---------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

\* TODO - import from original states and add after that
Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ FencedLeaderExpandIsr
    \/ FencedLeaderShrinkIsr
    \/ LeaderWrite
    \/ FencedLeaderIncHighWatermark 
    \/ FencedBecomeFollower
    \/ FencedFollowerFetch
    \/ ReplicaDataExpireKIP405
    \/ FollowerBuildAuxState
    \/ LeaderArchiveToRemoteStorage

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOk
---------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

(*  This invariant states that the local records until the true leader's HW are consistently replicated amongst the members of true ISR.
 *  This ensures that the local data that is exposed to the consumers will be present on any broker that becomes leader.
 *)
LocalLogConsistencyOk ==
    \/ quorumState.leader = None
    \/ LET leader == quorumState.leader IN
       LET hw == replicaState[leader].hw
       IN  \A isr \in quorumState.isr, offset \in RemoteLog!GetEndOffset .. (hw - 1) : \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(leader, record, offset)       
                /\ ReplicaLog!HasEntry(isr, record, offset)

(*  
 *  This invariant states that the records common to local log of a true ISR as well as remote log should be consistent.
 *)
OverlappingLogConsistencyOk ==
    \A isr \in quorumState.isr :
        /\ ~ ReplicaLog!IsEmpty(isr)
        => \A offset \in GetLocalLogStartOffset(isr) .. (RemoteLog!GetEndOffset - 1) : 
                \E record \in LogRecords : 
                    /\ RemoteLog!HasEntry(record, offset)       
                    /\ ReplicaLog!HasEntry(isr, record, offset)

(* 
 *  This invariant states that data which is not available locally would be available in remote log i.e.
 *  there are no holes in the log.
 *)
LogContinuityOk == \A replica \in Replicas :
    /\ IsTrueLeader(replica) => RemoteLog!GetEndOffset >= GetLocalLogStartOffset(replica) 

(*
 *  Uncommitted offsets on a leader cannot be moved to Remote Storage. However the leader's Hw might not have caught up to the true
 *  Hw after an election. Hence, this property should be verified with strong fairness.
 *)
ArchiveCommittedRecords == \A leader \in Replicas :
    /\ IsTrueLeader(leader) => RemoteLog!GetEndOffset <= GetHighWatermark(leader) 
---------------------------------------------------------------------------

(**************)
(* Tests *)
(**************)
           
TestReplicaHasMovedStartOffset ==
    ~\E replica, leader \in Replicas:
        /\ replica # leader
        /\ IsTrueLeader(leader)
        /\ ReplicaLog!GetStartOffset(replica) = 2 \* TODO - use the constant variable
        /\ ReplicaLog!GetStartOffset(leader) = 2
        /\ IsFollowingLeaderEpoch(leader, replica)
        /\ GetHighWatermark(replica) = 3
        /\ \E re \in replicaState[leader].isr:
            /\ re = replica

TestFollowerCatchesUpHw == ~\E replica, leader \in Replicas:
    /\ replica # leader
    /\ IsFollowingLeaderEpoch(leader, replica)
    /\ GetHighWatermark(leader) > 0
    /\ GetHighWatermark(replica) = GetHighWatermark(leader)

TestFollowerStartOffsetIncreases == ~\E replica, leader \in Replicas:
    /\ replica # leader
    /\ IsFollowingLeaderEpoch(leader, replica)
    /\ ReplicaLog!GetStartOffset(replica) = 2
    /\ ReplicaLog!GetStartOffset(leader) = ReplicaLog!GetStartOffset(replica)

TestFollowerEndOffsetIncreases == ~\E replica, leader \in Replicas:
    /\ replica # leader
    /\ IsFollowingLeaderEpoch(leader, replica)
    /\ ReplicaLog!GetEndOffset(replica) = 1

TestFollowerHwIncreases == ~\E replica, leader \in Replicas:
    /\ replica # leader
    /\ IsFollowingLeaderEpoch(leader, replica)
    /\ GetHighWatermark(replica) = 1
=============================================================================