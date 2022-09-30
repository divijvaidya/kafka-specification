------------------------------- MODULE Kip405 -------------------------------
EXTENDS KafkaReplication

LOCAL GetLocalLogStartOffset(replica) == ReplicaLog!GetStartOffset(replica)

LeaderDataExpireKIP405 == \E leader \in Replicas :
    /\ leader # None
    /\ ReplicaPresumesLeadership(leader)
    /\ \E tillOffset \in ReplicaLog!GetWrittenOffsets(leader) :
        /\ RemoteLog!GetEndOffset > ReplicaLog!GetStartOffset(leader) 
        /\ ReplicaLog!TruncateFullyAndStartAt(leader, tillOffset)
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

FencedFollowerFetchKIP405 == \E follower, leader \in Replicas :
    /\ IsFollowingLeaderEpoch(leader, follower)
    \* Followers can only enter the fetch state when their end offset >= leader's local log start offset
    /\ ReplicaLog!GetEndOffset(follower) >= GetLocalLogStartOffset(leader)
    /\ ReplicaLog!ReplicateTo(leader, follower)
    /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
            leaderHw == replicaState[leader].hw
            followerHw == Min({leaderHw, newEndOffset})
       IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
    /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(**
 * Entry criteria for this state: follower's endOffset < leader's local start offset
 * 1. Follower fetches data from leader about target epoch
 * 2. Follower builds history till that epoch from remote storage 
 * 3. Follower truncates from start until
 * 4. Follower fetches
 *)
 \* diviv - todo - add new state FollowerBuildAuxState
\* targetEpoch should be defined at entry
\* leader should have a local start offset > follower end offset (after truncation)
\* follower should truncate from the start till leader.localLogstartOffset 
\* after this follower should have a localLogStartOffset = leaderLogStartOffset
\* followers epoch history chain.end >= targetEpoch
\*

FollowerBuildAuxState == \E leader, follower \in Replicas :
    /\ leader # None
    /\ leader # follower
    /\ ReplicaPresumesLeadership(leader)
    \* This is the enabling condition for going into BuildAux state
    /\ ReplicaLog!GetEndOffset(follower) < GetLocalLogStartOffset(leader)
    \* Truncate from start till leader's local log start offset
    \* This also updates the start offset & end offset of the follower
    /\ ReplicaLog!TruncateFullyAndStartAt(follower, GetLocalLogStartOffset(leader))
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>


Next ==
    \/ ControllerElectLeader 
    \/ ControllerShrinkIsr
    \/ BecomeLeader
    \/ FencedLeaderExpandIsr
    \/ FencedLeaderShrinkIsr
    \/ LeaderWrite
    \/ FencedLeaderIncHighWatermark 
    \/ FencedBecomeFollowerAndTruncate
    \/ FencedFollowerFetch
    \/ LeaderDataExpireKIP405
    \/ FollowerBuildAuxState

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(FencedLeaderIncHighWatermark)
             /\ SF_vars(FencedLeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(FencedBecomeFollowerAndTruncate)
             /\ WF_vars(BecomeLeader)

THEOREM Spec => []TypeOk
=============================================================================
\* Modification History
\* Last modified Fri Sep 30 15:32:31 CEST 2022 by diviv
\* Created Wed Sep 14 15:39:13 CEST 2022 by diviv
