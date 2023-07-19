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
 * 
 * Not covered - fetch isolation levels, 
 * 
 *)

EXTENDS Integers, Util, TLC

CONSTANTS 
    Replicas, 
    LogSize, 
    MaxRecords, 
    MaxLeaderEpoch

None == "NONE"
NilRecord == [id |-> -1, epoch |-> -1] 
Nil == -1

ASSUME 
    /\ None \notin Replicas
    /\ MaxLeaderEpoch \in Nat

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

vars == <<replicaLog, remoteLog, replicaState, nextLeaderEpoch, nextRecordId, leaderAndIsrRequests, quorumState>> 

LeaderEpochSeq == INSTANCE IdSequence WITH MaxId <- MaxLeaderEpoch, nextId <- nextLeaderEpoch
RecordSeq == INSTANCE IdSequence WITH MaxId <- MaxRecords - 1, nextId <- nextRecordId

\* All records get an id and a leader epoch. To model the behavior of Kafka prior to the 
\* addition of the leader epoch in the message format, we simply ignore the epoch in the message.
LogRecords == [id : RecordSeq!IdSet, epoch : LeaderEpochSeq!IdSet] 

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
 * 
 *)         
ReplicaState == [hw : ReplicaLog!Offsets \union {LogSize}, 
                 leaderEpoch: LeaderEpochOpt,
                 leader : ReplicaOpt, 
                 isr: SUBSET Replicas,
                 fetchState: {"FETCH", "TRUNCATE", "BUILDAUX"} \union Nil
                ]

GetHighWatermark(replica) == replicaState[replica].hw

LOCAL GetLocalLogStartOffset(replica) == ReplicaLog!GetStartOffset(replica)

Init ==
    /\ LeaderEpochSeq!Init
    /\ RecordSeq!Init
    /\ ReplicaLog!Init
    /\ RemoteLog!Init
    /\ replicaState = [replica \in Replicas |-> [hw |-> ReplicaLog!GetStartOffset(replica), 
                                                 leaderEpoch |-> Nil, 
                                                 leader |-> None, 
                                                 isr |-> {},
                                                 fetchState |-> Nil]]
    /\ quorumState = [leaderEpoch |-> Nil,
                      leader |-> None, 
                      isr |-> Replicas]
    /\ leaderAndIsrRequests = {}

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


 (**
 * Helper function to "send" a new LeaderAndIsr request. The leader epoch is bumped,
 * the quorum state is updated, and the new request is added to the LeaderAndIsr request set.
 * 
 * We need to bump the leader epoch if:
 * 1. The leader changed, or
 * 2. The new ISR does not contain all the nodes that the old ISR did, or
 * 3. The new replica list does not contain all the nodes that the old replica list did. 
 * TODO - https://github.com/apache/kafka/pull/13765 changes confition 2
 * 
 * Code Reference: PartitionChangeBuilder#triggerLeaderEpochBumpIfNeeded
 *)
ControllerUpdateIsr(newLeader, newIsr) == 
    /\ newIsr # quorumState.isr
    /\ \E newLeaderEpoch \in LeaderEpochSeq!IdSet :
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
        \* case when a leader which is in ISR is shutdown *\
    /\  \/  /\ quorumState.leader = replica
            /\ quorumState.isr = {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr)
        \* case when a leader which is not in ISR is shutdown *\  
        \/  /\ quorumState.leader = replica
            /\ quorumState.isr # {replica}
            /\ ControllerUpdateIsr(None, quorumState.isr \ {replica})
        \* case when a replica is removed from ISR *\
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
    /\ quorumState' = [quorumState EXCEPT !.isr = newIsr]
    /\ replicaState' = [replicaState EXCEPT ![leader].isr = newIsr]

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
    THEN ReplicaLog!GetStartOffset(leader)
    ELSE LET matchingOffsets == MatchingOffsets(follower, leader)
         IN IF matchingOffsets = {} 
            THEN ReplicaLog!GetStartOffset(leader)
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
 * TODO - In zookeeper mode, we check if the replica is alive. In KRaft mode, only replicas which are not fenced nor in controlled shutdown are
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
 * Followers can fetch as long as the leader epoch according to them is same as leader epoch according to the leader. In all other cases, the leader will send error
 * on fetch request which will lead to re-tries by the follower.
 * 
 * For newer protocol (> 2.7), truncateOnFetch is enabled which means that the follower truncates in the fetch state itself. The
 * local high watermark is updated at the time of fetching.
 * 
 * diviv - todo - followers can only fetch the "local data" from the leader 
 * 
 * A replica will start with fetch if it has an epoch in the
 *)
\*
FollowerFetch == \E follower, leader \in Replicas : \* TODO - anything happeniing locally to the replica cannot be dependent on / conditional on states or change states which are not local to the leader
    /\ replicaState.fetchState = "FETCH"
    /\ IsFollowingLeaderEpoch(leader, follower) \* Ensures that we won't get unknown leader epoch or fenced leader epoch
    /\ LET fetchOffset == ReplicaLog!GetEndOffset(follower)
           fetchEpoch == ReplicaLog!GetLatestEpoch(follower)
           leaderEpoch == ReplicaLog!GetLatestEpoch(leader)
       IN   IF fetchOffset > ReplicaLog!GetEndOffset(leader) \* Case of out of range error
            THEN    /\ ReplicaLog!TruncateTo(replica, ReplicaLog!GetEndOffset(leader))
                    \* state remains as fetching
                    \*/\ LET newHighWatermark == Min({ReplicaLog!GetEndOffset(replica), replicaState[replica].hw})
             \* DIVIJ TODO - couldn't find code where we update Hw       \*   IN replicaState' = [replicaState EXCEPT ![follower].hw = newHighWatermark]
            ELSE IF fetchOffset < ReplicaLog!GetStartOffset(leader) \* TODO This changes to Global start offset for TS \* Case of out of range error
            THEN    /\ ReplicaLog!TruncateFullyAndStartAt(replica, ReplicaLog!GetStartOffset(leader))
                    \* state remains as fetching
                    /\ LET newHighWatermark == ReplicaLog!GetEndOffset(replica)
                       IN replicaState' = [replicaState EXCEPT ![follower].hw = newHighWatermark]
            \* ELSE IF fetchEpoch > leaderEpoch || fetchOffset > TODO
            \* THEN    /\ replicaState' = [replicaState EXCEPT ![follower].fetchState = "TRUNCATE"]
            ELSE    /\ ReplicaLog!ReplicateTo(leader, follower)
                    /\ LET  leaderHw == replicaState[leader].hw
                       IN   /\ MaybeUpdateHw(follower, leaderHw)
                            /\ MaybeUpdateLogStartOffset(follower, ReplicaLog!GetStartOffset(leader)) \* TODO - We are not deleting data, just incrementing the offset. Also in TS, this should be set to local start offset 
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(* Corresponds to UnifiedLog#maybeIncrementLogStartOffset
 * 
 *)
MaybeIncrementLogStartOffset(replica, leaderLogStartOffset) ==
    /\ replicaState[replica].hw >= leaderLogStartOffset
    /\ leaderLogStartOffset > ReplicaLog!GetStartOffset(replica)
    /\ ReplicaLog!SetStartOffset(replica, leaderLogStartOffset)
    /\ ReplicaLog!TruncateFromTailTillOffset(replica, leaderLogStartOffset - 1)

(* Corresponds to UnifiedLog#maybeUpdateHighWatermark
 * 
 *)
MaybeUpdateHw(replica, newHw) ==
    /\ LET newHighWatermark ==
        /\ IF newHw < ReplicaLog!GetStartOffset(replica)
           THEN ReplicaLog!GetStartOffset(replica)
           ELSE IF newHw >= ReplicaLog!GetEndOffset(replica)
           THEN ReplicaLog!GetEndOffset(replica)
           ELSE newHw  
       IN replicaState' = [replicaState EXCEPT ![replica].hw = newHighWatermark]
(*
 * In a truncate state, a follower will ask the leader for the end offsets of the latest epoch for it's partition and it will truncate
 * itself to the end offset provided by the leader. The leader may send a fenced_leader_epoch in case the leader does not recognize the
 * current leader epoch (not the partition epoch) sent by the follower, in which case, replica will fence the partition, i.e. it will do nothing if it's current epoch epoch is larger 
 * than the leader epoch else fail the parition if it's current leader epoch is smaller than the leader epoch and will wait for new LISR
 *)
FollowerTruncate == \E follower, leader \in Replicas :
    /\ replicaState.fetchState = "TRUNCATE" 
        /\ IsFollowingLeaderEpoch(leader, follower)
        /\ LET truncOffset == LookupOffsetForEpoch(leader, follower, ReplicaLog!GetLatestEpoch(follower))
        IN ReplicaLog!TruncateTo(follower, truncOffset)
    /\ replicaState' = [replicaState EXCEPT ![follower].fetchState = "FETCH"]
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>
(**
 * The high watermark is advanced if all members of the ISR are following the leader's
 * epoch and have replicated up to the current high watermark. Note that we depend only
 * on the leader's local ISR and not the quorum.
 *)
FencedLeaderIncHighWatermark == \E leader \in Replicas :
    /\ LET newLeaderHw == replicaState[leader].hw + 1
       IN  /\ ReplicaLog!HasOffset(leader, newLeaderHw)
           /\ \A follower \in replicaState[leader].isr : 
              /\ IsFollowingLeaderEpoch(leader, follower)
              /\ ReplicaLog!HasOffset(follower, newLeaderHw)
    /\ replicaState' = [replicaState EXCEPT ![leader].hw = @ + 1]
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A replica is taken out of the ISR by the leader if it is not "caught up". A replica is
 * considered "caught-up" when its log end offset is equals to the log end offset of the leader OR when its last caught up time minus the current time is smaller than the max replica lag.
 * In this model, the decision to shrink the ISR is made arbitrarily by the leader if the former condition is not met. ShrinkIsr triggered by the delayed lag is not supported by this model.
 * The leader can choose to shrink the ISR immediately after becoming leader or it can wait indefinitely before doing so.
 *
 * Note that leader tells the controller to shrink the ISR using alterPartition API. Controller acknowledges the request and increments the partition epoch on the leader with the new ISR. This
 * model does not capture the concept of controller changing the isr and incrementing the partition epoch.
 * 
 * Code reference: ReplicaManager#maybeShrinkIsr
 *)
LeaderShrinkIsr == \E leader \in Replicas :
    /\ LET isr == replicaState[leader].isr
           leaderEndOffset == ReplicaLog!GetEndOffset(leader) 
       IN  \E follower \in isr \ {leader} :
        \*    /\ \/ ~ IsFollowingLeaderEpoch(leader, follower) TODO - should we include this?
              \/ IsFollowerCaughtUp(leader, follower)
           /\ QuorumUpdateLeaderAndIsr(leader, isr \ {follower})
    /\ UNCHANGED <<nextRecordId, replicaLog, remoteLog, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * A replica is considered "caught-up" by the leader when its log end offset is equals to the log end offset of the leader OR when its last caught up time minus the current time is smaller than the max replica lag.
 * In this model, the decision to shrink the ISR is made arbitrarily by the leader if the former condition is not met. ShrinkIsr triggered by the delayed lag is not supported by this model.
 *
 * Code reference: Partition#isFollowerOutOfSync()
 *)
IsFollowerCaughtUp(leader, follower) ==
    /\ ReplicaIsFollowing(follower, leader)
    /\ ReplicaLog!GetEndOffset(follower) = ReplicaLog!GetEndOffset(leader)

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

(*
 * corresponds to Partition#makeFollower
 * Update the leader epoch and leader. Set the ISR to empty.
 *)
LOCAL BecomeFollower(replica, leaderAndIsrRequest, newHighWatermark) ==
    replicaState' = [replicaState EXCEPT ![replica] = 
                         [leaderEpoch |-> leaderAndIsrRequest.leaderEpoch,                                                          
                          leader |-> leaderAndIsrRequest.leader,
                          isr |-> {}]]

(**
 * The only improvement here over the KIP-279 truncation logic is that we ensure that the
 * leader and follower have the same epoch. Without it, we violate the strong ISR property
 * when a follower uses a leader with stale state to find the truncation offset. Later
 * the stale leader may do some truncation of its own before catching up to the follower's
 * epoch. You can verify this failure by replacing this action with `BecomeFollowerTruncateKip279`
 * in the spec below.
 * 
 * Note: There is a call to leader here to fetch the end offset, start offset
 * 
 *)
FencedBecomeFollower == \E leader, replica \in Replicas, leaderAndIsrRequest \in leaderAndIsrRequests :
    /\ leader # replica
    /\ leaderAndIsrRequest.leader = leader
    /\ leaderAndIsrRequest.leaderEpoch > replicaState[replica].leaderEpoch
    /\  \/  /\ leader = None
            /\ BecomeFollower(replica, leaderAndIsrRequest)
            /\ UNCHANGED replicaLog
        \/  /\ leader # None
            /\ ReplicaPresumesLeadership(leader)
            /\ replicaState[leader].leaderEpoch = leaderAndIsrRequest.leaderEpoch
            /\ BecomeFollower(replica, leaderAndIsrRequest)
            /\ IF ReplicaLog!GetLatestEpoch # Nil
               THEN replicaState' = [replicaState EXCEPT ![replica] = [fetchState |-> "FETCH"]]
               ELSE replicaState' = [replicaState EXCEPT ![replica] = [fetchState |-> "TRUNCATE"]]
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(*
 * /\  IF ReplicaLog!GetEndOffset(replica) > ReplicaLog!GetEndOffset(leader)
                THEN /\ ReplicaLog!TruncateTo(replica, ReplicaLog!GetEndOffset(leader))
                     /\ LET newHighWatermark == Min({ReplicaLog!GetEndOffset(replica), replicaState[replica].hw})
                        IN BecomeFollower(replica, leaderAndIsrRequest)
                ELSE IF ReplicaLog!GetEndOffset(replica) < ReplicaLog!GetStartOffset(leader)
                THEN    /\ ReplicaLog!TruncateFullyAndStartAt(replica, ReplicaLog!GetStartOffset(leader))
                        /\ BecomeFollower(replica, leaderAndIsrRequest, ReplicaLog!GetEndOffset(replica))
                ELSE LET truncationOffset == FirstNonMatchingOffsetFromTail(leader, replica)  
                     IN /\ ReplicaLog!TruncateTo(replica, truncationOffset)
                        /\ LET newHighWatermark == Min({truncationOffset, replicaState[replica].hw})
                           IN BecomeFollower(replica, leaderAndIsrRequest)
 *)

GetCommittedOffsets(replica) ==
    IF ReplicaLog!IsEmpty(replica)
    THEN {}
    ELSE ReplicaLog!GetStartOffset(replica) .. GetHighWatermark(replica) - 1

\* ReplicaDataExpire == \E replica \in Replicas:
\*     /\ ~RemoteLog!IsEmpty \* For optimization, only enable this state if remote log is non-empty
\*     /\ \E tillOffset \in GetCommittedOffsets(replica):
\*         /\ ReplicaLog!TruncateFromTailTillOffset(replica, tillOffset)
\*     /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>
---------------------------------------------------------------------------

\* LOCAL Next ==
\*     \/ ControllerElectLeader 
\*     \/ ControllerShrinkIsr
\*     \/ BecomeLeader
\*     \/ FencedLeaderExpandIsr
\*     \/ FencedLeaderShrinkIsr
\*     \/ LeaderWrite
\*     \/ FencedLeaderIncHighWatermark 
\*     \/ FencedBecomeFollowerAndTruncate
\*     \/ FencedFollowerFetch
\*     \/ ReplicaDataExpire

\* \* In the initial state, spec is true iff, init is true AND [][Next]_vars is true in every step
\* LOCAL Spec == Init /\ [][Next]_vars \* Init is true in initial state AND it is always true in every state that either next is true or vars is unchanged 
\*              /\ SF_vars(FencedLeaderIncHighWatermark) \* it is always eventually true that LeaderIncHighWatermark can happen and it will eventually happen with a change in vars
\*              /\ SF_vars(FencedLeaderExpandIsr)
\*              /\ SF_vars(LeaderWrite)
\*              /\ WF_vars(FencedBecomeFollowerAndTruncate)
\*              /\ WF_vars(BecomeLeader) \* it is eventually always true that BecomeLeader can happen and it will happen with a change in vars
             
\* THEOREM Spec => []TypeOk
\* THEOREM Spec => []LeaderInIsr
\* THEOREM Spec => []WeakIsr
\* THEOREM Spec => []StrongIsr

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
TypeOk ==
    /\ LeaderEpochSeq!TypeOk
    /\ RecordSeq!TypeOk
    /\ ReplicaLog!TypeOk
    /\ RemoteLog!TypeOk
    /\ replicaState \in [Replicas -> ReplicaState]
    /\ quorumState \in QuorumState
    /\ leaderAndIsrRequests \subseteq QuorumState

Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ FencedLeaderExpandIsr
    \/ LeaderShrinkIsr
    \/ LeaderWrite
    \/ FencedLeaderIncHighWatermark 
    \/ FencedBecomeFollower
    \/ FollowerFetch
    \/ ReplicaDataExpireKIP405
    \/ FollowerBuildAuxState
    \/ LeaderArchiveToRemoteStorage

Spec == Init /\ [][Next]_vars

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
       IN  \A isr \in quorumState.isr, offset \in ReplicaLog!GetEndOffset .. (hw - 1) : \E record \in LogRecords : 
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
 *  TODO - instead of GetHighWatermark(leader), test this with largest Hw amongst the replicas in ISR. Then we don't want strong fairness here. 
 *)
ArchiveCommittedRecords == \A leader \in Replicas :
    /\ IsTrueLeader(leader) => RemoteLog!GetEndOffset <= GetHighWatermark(leader) 

(*
 * Check range of HW, e.g. HW <= end offset AND HW >= global start offset
 * 
 *)
HighWatermarkRangeOk == \A replica \in Replicas:
    \/ /\ ReplicaLog!IsEmpty(replica)
       /\ GetHighWatermark(replica) = ReplicaLog!GetEndOffset(replica)
       /\ GetHighWatermark(replica) = ReplicaLog!GetStartOffset(replica)
    \/ /\ GetHighWatermark(replica) <= ReplicaLog!GetEndOffset(replica)
\*       /\ GetHighWatermark(replica) >= ReplicaLog!GetStartOffset(replica) this is not true for TS when local log start offset > loca hw which is in TS

HighWatermarkOk == 
    /\ HighWatermarkRangeOk

(**
 * The leader should always in the ISR, because even if all brokers failed, we still keep the leader in ISR
 *)
LeaderInIsr == quorumState.leader \in quorumState.isr

(*
TODO - Start Offset always increases or returns to 0
TODO - `logStartOffset <= logStableOffset <= highWatermark` 
TODO - the ISR should eventually catch up with the leader
TODO - only committed messages are only given out to the consumer. A message is considered committed when all replicas in ISR have that message.
TODO - the new leader must have the committed message
TODO - whenever ISR changes, epic changes
 *)
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
