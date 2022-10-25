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
 
-------------------------- MODULE KafkaReplication --------------------------

(**
 * This module contains the core Kafka replication state and its basic operators.
 * We model a single partition with a constant replication factor. A replica in this
 * model has its own state and can be either a leader or a follower at any given time.
 *
 * The controller in this model does not have its own state, but is able to influence
 * the behavior by directly modify a quorum state (i.e. zookeeper) and by propagating
 * LeaderAndIsr requests to the replicas.
 *)

EXTENDS Integers, Util

\* divij - inputs provided to the execution, usually defined in configuration
CONSTANTS 
    Replicas, 
    LogSize, 
    MaxRecords, 
    MaxLeaderEpoch

None == "NONE"
NilRecord == [id |-> -1, epoch |-> -1] 
Nil == -1

\* divij - the inputs defined in constants must satisfy the validations available in assume
ASSUME 
    /\ None \notin Replicas
    /\ MaxLeaderEpoch \in Nat

\* divij - stateful parameters 
VARIABLES
    \* This is a function from the replicas to their local logs.  
    replicaLog,

    \* This represents remote logs for a topic.  
    remoteLog,

    \* This is a function from the replicas to their local state. The replica state contains 
    \* leader/ISR information and the all-important high watermark.
    replicaState,
    
    \* Unique id generator for new records. Every producer write to a leader gets a new id
    \* so that we can ensure records are unique. 
    nextRecordId,

    \* This is a simple id sequence which is used to generate monotonically increasing
    \* leader epochs.
    nextLeaderEpoch,

    \* The LeaderAndIsr request is crucial in Kafka, so we want to model edge cases around 
    \* delivery of the request (e.g. lost requests and duplicates). We use a simple set of
    \* all LeaderAndIsr requests to enable this. Replicas choose arbitrarily from the set 
    \* which request to observe at any time, but generally they will ignore requests which
    \* contain a lower leader epoch than they expect.
    leaderAndIsrRequests,

    \* This is the model's equivalent of the state in Zookeeper, but generally we ignore 
    \* the complexity of Zookeeper itself. Instead we allow simple atomic operation to the 
    \* state directly within individual actions. We also elide details about propagation
    \* of quorum state, which enables ISR update fencing in Kafka. We assume unrealistically
    \* that quorum modifications are instantaneous and observed by all interested parties.
    quorumState

\* diviv - TODO Add remote log
vars == <<replicaLog, remoteLog, replicaState, nextLeaderEpoch, nextRecordId, leaderAndIsrRequests, quorumState>> 

LeaderEpochSeq == INSTANCE IdSequence WITH MaxId <- MaxLeaderEpoch, nextId <- nextLeaderEpoch
RecordSeq == INSTANCE IdSequence WITH MaxId <- MaxRecords - 1, nextId <- nextRecordId

\* All records get an id and a leader epoch. To model the behavior of Kafka prior to the 
\* addition of the leader epoch in the message format, we simply ignore the epoch in the message.
LogRecords == [id : RecordSeq!IdSet, epoch : LeaderEpochSeq!IdSet] 

\* divij - TODO: Add remote log
ReplicaLog == INSTANCE FiniteReplicatedLog WITH logs <- replicaLog
RemoteLog == INSTANCE RemoteStorageLog WITH remoteLog <- remoteLog
ReplicaOpt == Replicas \union {None}
LeaderEpochOpt == LeaderEpochSeq!IdSet \union {Nil}
QuorumState == [leaderEpoch: LeaderEpochOpt,
                leader : ReplicaOpt, 
                isr: SUBSET Replicas]
                
(**
 * Each replica has a cached copy of the quorum state and a local high watermark. These
 * get updated in accordance with the Kafka replication protocol. For example, the leader
 * epoch is updated when a LeaderAndIsr request is received. 
 *)   
 \* divij -> HW = LSO              
ReplicaState == [hw : ReplicaLog!Offsets \union {LogSize}, 
                 leaderEpoch: LeaderEpochOpt,
                 leader : ReplicaOpt, 
                 isr: SUBSET Replicas
                ]

TypeOk ==
    /\ LeaderEpochSeq!TypeOk
    /\ RecordSeq!TypeOk
    /\ ReplicaLog!TypeOk
    /\ RemoteLog!TypeOk
    /\ replicaState \in [Replicas -> ReplicaState]
    /\ quorumState \in QuorumState
    /\ leaderAndIsrRequests \subseteq QuorumState
    /\ \A replica \in Replicas:
        /\ ~ReplicaLog!IsEmpty(replica) => replicaState[replica].hw < ReplicaLog!GetEndOffset(replica) 

Init ==
    /\ LeaderEpochSeq!Init
    /\ RecordSeq!Init
    /\ ReplicaLog!Init
    /\ RemoteLog!Init
    /\ replicaState = [replica \in Replicas |-> [hw |-> ReplicaLog!GetStartOffset(replica), 
                                                 leaderEpoch |-> Nil, 
                                                 leader |-> None, 
                                                 isr |-> {}]]
    /\ quorumState = [leaderEpoch |-> Nil,
                      leader |-> None, 
                      isr |-> Replicas]
    /\ leaderAndIsrRequests = {}


GetHighWatermark(replica) == replicaState[replica].hw

(**
 * Check whether a broker believes itself to be the leader. The presumed leader will accept
 * writes, so we depend on replication fencing for correct behavior.
 *)
ReplicaPresumesLeadership(replica) == replicaState[replica].leader = replica
ReplicaIsFollowing(follower, leader) == replicaState[follower].leader = leader
IsTrueLeader(leader) ==
    /\ quorumState.leader = leader 
    /\ ReplicaPresumesLeadership(leader)
    /\ replicaState[leader].leaderEpoch = quorumState.leaderEpoch


 \* diviv TODO
 \* GlobalLogStartOffset == RemoteLog!GetStartOffset()

(**
 * Helper function to "send" a new LeaderAndIsr request. The leader epoch is bumped,
 * the quorum state is updated, and the new request is added to the LeaderAndIsr request set.
 *)
ControllerUpdateIsr(newLeader, newIsr) == \E newLeaderEpoch \in LeaderEpochSeq!IdSet :
    /\ LeaderEpochSeq!NextId(newLeaderEpoch)
    /\  LET newControllerState == [
            leader |-> newLeader,
            leaderEpoch |-> newLeaderEpoch, 
            isr |-> newIsr] 
        IN  /\ quorumState' = newControllerState 
            /\ leaderAndIsrRequests' = leaderAndIsrRequests \union {newControllerState} 
(**
 * The controller shrinks the ISR upon broker failure. We do not represent node failures
 * explicitly in this model. A broker can be taken out of the ISR and immediately begin
 * fetching, or it can wait some time and fetch later. One way to look at this is that 
 * we do not distinguish between a properly shutdown broker which ceases fetching and 
 * a zombie which may continue to make progres. All states are checked.
 * 
 * Note that the leader can fail or do a controlled shutdown just like any other broker.
 * The leader is set to None in this case and removed from the ISR (as long as there is
 * at least one other replica in the ISR). Election of a new leader is done in a separate
 * step.
 *)
ControllerShrinkIsr == \E replica \in Replicas :
    /\  \/  /\ quorumState.leader = replica
            /\ quorumState.isr = {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr)
        \/  /\ quorumState.leader = replica
            /\ quorumState.isr # {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr \ {replica})
        \/  /\ quorumState.leader # replica
            /\ replica \in quorumState.isr
            /\ ControllerUpdateIsr(quorumState.leader, quorumState.isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, replicaState>>

(**
 * Leader election by the controller is triggered by the failure of a broker or the need 
 * to balance leaders. For clean leader election, we choose a member of the ISR and we 
 * bump the leader epoch. In this model, the choice to elect a new leader can be made 
 * arbitarily by the controller. 
 *)
ControllerElectLeader == \E newLeader \in quorumState.isr :
    /\ quorumState.leader # newLeader 
    /\ ControllerUpdateIsr(newLeader, quorumState.isr)
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, replicaState>>

(**
 * A replica will become a leader if it receives a LeaderAndIsr request with a higher
 * epoch than is in its local state. Significantly, the high watermark upon becoming
 * a leader is typically behind the "true" high watermark from the previous leader. 
 *)
BecomeLeader == \E leaderAndIsrRequest \in leaderAndIsrRequests :
    LET leader == leaderAndIsrRequest.leader
    IN  /\ leader # None
        /\ leaderAndIsrRequest.leaderEpoch > replicaState[leader].leaderEpoch
        /\ replicaState' = [replicaState EXCEPT ![leader] = [
                hw |-> @.hw,
                leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,
                leader |-> leader,
                isr |-> leaderAndIsrRequest.isr]]
        /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A leader will accept a write from a producer as long as it presumes to be the leader.
 * In the event that it is wrong, we expect replication to fail, which will ultimately
 * result in an ISR shrink. Kafka's primary fencing of zombies comes in ISR shrinks.
 *)
LeaderWrite == \E replica \in Replicas, id \in RecordSeq!IdSet, offset \in ReplicaLog!Offsets :
    /\ ReplicaPresumesLeadership(replica)
    /\ RecordSeq!NextId(id)
    /\ LET record == [id |-> id, epoch |-> replicaState[replica].leaderEpoch]
       IN ReplicaLog!Append(replica, record, offset)
    /\ UNCHANGED <<remoteLog, replicaState, nextLeaderEpoch, quorumState, leaderAndIsrRequests>>

(**
 * Only the true leader (that is, the one currently designated in the quorum as the leader)
 * is allowed to update the ISR directly.
 *)
QuorumUpdateLeaderAndIsr(leader, newIsr) ==
    /\ IsTrueLeader(leader)
    /\ quorumState.leader = leader
    /\ quorumState' = [quorumState EXCEPT !.isr = newIsr]
    /\ replicaState' = [replicaState EXCEPT ![leader].isr = newIsr]

IsFollowerCaughtUp(leader, follower, leaderHw) ==
    /\ ReplicaIsFollowing(follower, leader) 
    /\  \/ leaderHw = 0
        \/  /\ leaderHw > 0 
            /\ LET offset == leaderHw - 1 IN \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(leader, record, offset)
                /\ ReplicaLog!HasOffset(follower, offset)

(**
 * ISR changes are fenced by the write to the quorum. There is some trickiness to make this
 * work in practice (i.e. propagation of the zkVersion), but this model ignores the details. 
 * We assume this logic is correct and simply allow the write if and only if the leader is 
 * the true leader in the quorum and has the current epoch.   
 *)
LeaderShrinkIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           endOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E replica \in isr \ {leader} :
           /\ ~ IsFollowerCaughtUp(leader, replica, endOffset) 
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {replica})
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is the old logic for incrementing the high watermark. As long as each
 * member of the ISR ackowledges the presumed leader and has replicated up to
 * the current offset (no leader epoch verification), then we increment the
 * high watermark. Note that we do not model the fetch behavior directly. As long
 * as the replicas have acknowledged the leader, they /could/ all send a fetch
 * to advance the high watermark. What we model here is the transition in this case.
 *)
LeaderIncHighWatermark == \E offset \in ReplicaLog!Offsets, leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ offset = replicaState[leader].hw
    /\ \A follower \in replicaState[leader].isr : 
        /\ ReplicaIsFollowing(follower, leader)
        /\ ReplicaLog!HasOffset(follower, offset)
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * This is a helper for the follower state change. All that changed with the addition of 
 * KIP-101 and KIP-279 were improvements to the truncation logic upon becoming follower.
 * It is crucial that we do the truncation step on leader epoch changes, not just on 
 * leader changes.
 *
 * TODO: Is this what we actually do in the code?   
 *) 
\* divij - TODO Break this into multiple states. Become follower -> Fetch -> Truncate -> BuildAuxState
\* divij - question - why is this considered atomic?
BecomeFollowerAndTruncateTo(leader, replica, truncationOffset) == \E leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\  \/  /\ leader = None
            /\ UNCHANGED replicaLog
        \/  /\ leader # None
            /\ ReplicaLog!TruncateTo(replica, truncationOffset)
    /\ replicaState' = [replicaState EXCEPT ![replica] = 
        [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
         leader |-> leader,
         isr |-> leaderAndIsrRequest.isr,                                                        
         hw |-> Min({truncationOffset, @.hw})]] 
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>
    
OffsetsWithLargerEpochs(replica, epoch) ==
    {entry.offset : entry \in 
        {entry \in ReplicaLog!GetAllEntries(replica) : entry.record.epoch > epoch}}

LookupOffsetForEpoch(leader, follower, epoch) == 
    IF ReplicaLog!IsEmpty(leader)
    THEN replicaState[follower].hw
    ELSE IF ReplicaLog!GetLatestRecord(leader).epoch = epoch
    THEN ReplicaLog!GetEndOffset(leader)
    ELSE LET offsetWithLargerEpochs == OffsetsWithLargerEpochs(leader, epoch)
         IN IF offsetWithLargerEpochs = {} 
            THEN replicaState[follower].hw 
            ELSE Min(offsetWithLargerEpochs) 

MatchingOffsets(replica1, replica2) ==
    {entry.offset : entry \in
        {entry \in ReplicaLog!GetAllEntries(replica1) : 
          ReplicaLog!HasEntry(replica2, entry.record, entry.offset)}}

(**
 * To find the offset to truncate to, we verify offset and epoch going backwards 
 * from the end of the follower's log. The truncation offset is one more than the 
 * first offset that matches.
 *
 * TODO: Does this match the implementation?
 * diviv - TODO - verify that even with TS, the leader have sufficient info to give this offset
 *)
FirstNonMatchingOffsetFromTail(leader, follower) ==
    IF ReplicaLog!IsEmpty(leader)
    THEN 0
    ELSE LET matchingOffsets == MatchingOffsets(follower, leader)
         IN IF matchingOffsets = {} 
            THEN 0
            ELSE Max(matchingOffsets) + 1 

(**
 * As long as a presumed leader and follower agree on the leader status, we will replicate 
 * the next record if possible. The main thing to note is the lack of proper fencing. 
 * We do not verify either the current leader epoch or the epoch of the most recent fetched
 * data. 
 *)
FollowerReplicate == \E follower, leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ ReplicaIsFollowing(follower, leader)
    /\ ReplicaLog!ReplicateTo(leader, follower) 
    /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
            leaderHw == replicaState[leader].hw
            followerHw == Min({leaderHw, newEndOffset}) 
       IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * The weak ISR property says that for any presumed leader, the replicas in its current
 * assumed ISR have replicated logs precisely up to the high watermark. This is a weak
 * property because the leaders are actually elected from the quorum ISR. Disagreement about
 * the true ISR can lead to the loss of committed data. In spite of its weakness, we 
 * intuitively expect it to be true, and it is illustrative to understand the cases in which
 * it doesn't
 *)
WeakIsr == \A r1 \in Replicas :
    \/ ~ ReplicaPresumesLeadership(r1)
    \/ LET  hw == replicaState[r1].hw
       IN   \/ hw = 0
            \/ \A r2 \in replicaState[r1].isr, offset \in 0 .. (hw - 1) : \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(r1, record, offset)        
                /\ ReplicaLog!HasEntry(r2, record, offset)  

(**
 * The strong ISR property says that if any replica presumes leadership, then all data below
 * its high watermark must be consistently replicated to all members of the true ISR. This 
 * ensures that any data which has been exposed to consumers will be present on any broker 
 * that becomes leader.
 *)
StrongIsr == \A r1 \in Replicas :
    \/ ~ ReplicaPresumesLeadership(r1)
    \/ LET  hw == replicaState[r1].hw
       IN   \/ hw = 0
            \/ \A r2 \in quorumState.isr, offset \in 0 .. (hw - 1) : \E record \in LogRecords : 
                /\ ReplicaLog!HasEntry(r1, record, offset)        
                /\ ReplicaLog!HasEntry(r2, record, offset) 

(**
 * The leader should always in the ISR, because even if all brokers failed, we still keep the leader in ISR
 *)
LeaderInIsr == quorumState.leader \in quorumState.isr

(**
 * divij - TODO - In zookeeper mode, we check if the replica is alive. In KRaft mode, only replicas which are not fenced nor in controlled shutdown are
 * allowed to join the ISR.
 *)
LOCAL IsFollowerIsrEligible(follower) == TRUE

IsFollowingLeaderEpoch(leader, follower) == 
    /\ ReplicaPresumesLeadership(leader)
    /\ replicaState[follower].leader = leader
    /\ replicaState[follower].leaderEpoch = replicaState[leader].leaderEpoch

NoSplitBrain(leader) ==
    /\ \A replica \in Replicas:
        /\ replicaState[replica].leader # None
        /\ IsFollowingLeaderEpoch(leader, replica)
(**
 * Followers can fetch as long as they have the same epoch as the leader. Prior to fetching,
 * followers are responsible for truncating the log so that it matches the leader's. The
 * local high watermark is updated at the time of fetching.
 *
 * diviv - todo - followers can only fetch the "local data" from the leader 
 *)
\*
FencedFollowerFetch == \E follower, leader \in Replicas : \* TODO - anything happeniing locally to the replica cannot be dependent on / conditional on states or change states which are not local to the leader
    /\ IsFollowingLeaderEpoch(leader, follower)
    /\ ReplicaLog!ReplicateTo(leader, follower)
    /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
            leaderHw == replicaState[leader].hw
            followerHw == Min({leaderHw, newEndOffset})
       IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * The high watermark is advanced if all members of the ISR are following the leader's
 * epoch and have replicated up to the current high watermark. Note that we depend only
 * on the leader's local ISR and not the quorum.
 *)
FencedLeaderIncHighWatermark == \E leader \in Replicas :
    /\ LET newLeaderHw == IF replicaState[leader].hw = 0 THEN 0 ELSE replicaState[leader].hw + 1
       IN  /\ ReplicaLog!HasOffset(leader, newLeaderHw)
           /\ \A follower \in replicaState[leader].isr : 
              /\ IsFollowingLeaderEpoch(leader, follower)
              /\ ReplicaLog!HasOffset(follower, newLeaderHw)
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = IF replicaState[leader].hw = 0 THEN 0 ELSE @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A replica is taken out of the ISR by the leader if it is not following the right epoch 
 * or if its end offset is lagging. In this model, the decision to shrink the ISR is made 
 * arbitrarily by the leader if either of these conditions is met. It can choose to shrink 
 * the ISR immediately after becoming leader or it can wait indefinitely before doing so.
 *)
FencedLeaderShrinkIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderEndOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E follower \in isr \ {leader} :
           /\ \/ ~ IsFollowingLeaderEpoch(leader, follower)
              \/ ReplicaLog!GetEndOffset(follower) < leaderEndOffset
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {follower})
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, nextLeaderEpoch, leaderAndIsrRequests>>

LOCAL HasHighWatermarkReachedCurrentEpoch(leader) ==
    LET hw == replicaState[leader].hw
    IN  \/ hw = ReplicaLog!GetEndOffset(leader)
        \/ \E record \in LogRecords :
            /\ ReplicaLog!HasEntry(leader, record, hw)
            /\ record.epoch = replicaState[leader].leaderEpoch

LOCAL HasFollowerReachedHighWatermark(leader, follower) == 
    LET hw == replicaState[leader].hw
    IN  \/ hw = 0
        \/ /\ hw > 0
           /\ ReplicaLog!HasOffset(follower, hw - 1)
(**
 * Generally speaking, a replica which has caught up to the high watermark is eligible
 * to join the ISR, but there is one subtlety. When a follower becomes leader, 
 * its high watermark is typically behind the leader. Since it does not know what the true
 * high watermark was at the time the leader failed (or shutdown), it must be conservative 
 * when adding new members to the ISR. We can be assured that all members of the current 
 * ISR have replicated up to whatever the leader's high watermark was, but it is not safe 
 * to assume the same for new replicas until they have replicated ALL of the messages from 
 * the previous leader. In other words, we need to wait until it has at least replicated up
 * to the start of the its own leader epoch.
 *)
FencedLeaderExpandIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
       IN  \E follower \in Replicas \ isr :
           /\ IsFollowingLeaderEpoch(leader, follower)
           /\ IsFollowerIsrEligible(follower)
           /\ HasFollowerReachedHighWatermark(leader, follower)
           /\ HasHighWatermarkReachedCurrentEpoch(leader)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \union {follower})
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, nextLeaderEpoch, leaderAndIsrRequests>>

LOCAL BecomeFollower(replica, leaderAndIsrRequest, newHighWatermark) ==
    replicaState' = [replicaState EXCEPT ![replica] = 
                         [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
                          leader |-> leaderAndIsrRequest.leader,
                          isr |-> leaderAndIsrRequest.isr,                                                        
                          hw |-> newHighWatermark]]



(**
 * The only improvement here over the KIP-279 truncation logic is that we ensure that the
 * leader and follower have the same epoch. Without it, we violate the strong ISR property
 * when a follower uses a leader with stale state to find the truncation offset. Later
 * the stale leader may do some truncation of its own before catching up to the follower's
 * epoch. You can verify this failure by replacing this action with `BecomeFollowerTruncateKip279`
 * in the spec below.
 * 
 *)
FencedBecomeFollowerAndTruncate == \E leader, replica \in Replicas, leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\  \/  /\ leader = None
            /\ BecomeFollower(replica, leaderAndIsrRequest, replicaState[replica].hw)
            /\ UNCHANGED replicaLog
        \/  /\ leader # None
            /\ ReplicaPresumesLeadership(leader)
            /\ replicaState[leader].leaderEpoch = leaderAndIsrRequest.leaderEpoch
            /\ LET truncationOffset == FirstNonMatchingOffsetFromTail(leader, replica)
                   newHighWatermark == Min({truncationOffset, replicaState[replica].hw})
               IN  /\ ReplicaLog!TruncateTo(replica, truncationOffset)
                   /\ BecomeFollower(replica, leaderAndIsrRequest, newHighWatermark)
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

GetCommittedOffsets(replica) ==
    IF ReplicaLog!IsEmpty(replica)
    THEN {}
    ELSE ReplicaLog!GetStartOffset(replica) .. GetHighWatermark(replica)


\* diviv - todo Add state LeaderDataEviction
\* the leader local log start offset changes
\* log start offset can only be done if RS end offset > log start offset
\* after this log start offset is a arbit offset <= RS.end offset <= HW 
\* for tla+ we need to explore all transitions

\* do we expire the epoch history too?
\* do we expire for all replicas instead of just the leader? (yes)
LeaderDataExpire == \E replica \in Replicas :
    /\ \E tillOffset \in GetCommittedOffsets(replica) :
        /\ ReplicaLog!TruncateFromTailTillOffset(replica, tillOffset)
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>


\* Create a state without log tracked.

LOCAL Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ FencedLeaderExpandIsr
    \/ FencedLeaderShrinkIsr
    \/ LeaderWrite
    \/ FencedLeaderIncHighWatermark 
    \/ FencedBecomeFollowerAndTruncate
    \/ FencedFollowerFetch
    \/ LeaderDataExpire
    
\* divij - TODO: Add a state in Next to trigger expiration


\* In the initial state, spec is true iff, init is true AND [][Next]_vars is true in every step
LOCAL Spec == Init /\ [][Next]_vars \* Init is true in initial state AND it is always true in every state that either next is true or vars is unchanged 
             /\ SF_vars(FencedLeaderIncHighWatermark) \* it is always eventually true that LeaderIncHighWatermark can happen and it will eventually happen with a change in vars
             /\ SF_vars(FencedLeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(FencedBecomeFollowerAndTruncate)
             /\ WF_vars(BecomeLeader) \* it is eventually always true that BecomeLeader can happen and it will happen with a change in vars
             
THEOREM Spec => []TypeOk
THEOREM Spec => []LeaderInIsr
THEOREM Spec => []WeakIsr
THEOREM Spec => []StrongIsr

=============================================================================
\* Modification History
\* Last modified Tue Oct 25 16:16:28 UTC 2022 by ec2-user
\* Last modified Thu Oct 20 09:38:17 PDT 2022 by diviv
\* Last modified Thu Jan 02 14:37:55 PST 2020 by guozhang
\* Last modified Mon Jul 09 14:24:02 PDT 2018 by jason
\* Created Sun Jun 10 16:16:51 PDT 2018 by jason
