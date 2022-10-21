------------------------------- MODULE Kip405 -------------------------------
\* If outage happens in S3, it is on path to leader re-election. But we asume that S3 availability. 
EXTENDS KafkaReplication, TLC

LOCAL GetLocalLogStartOffset(replica) == ReplicaLog!GetStartOffset(replica)
LOCAL GetGlobalLogStartOffset == RemoteLog!GetStartOffset


LeaderDataExpireKIP405 ==
    /\ LET highestRemoteOffset == RemoteLog!GetEndOffset - 1 IN \E replica \in Replicas: 
        /\ \E tillOffset \in 0..highestRemoteOffset:
            /\ Print(<<"inside offsets", tillOffset>>, TRUE)
            /\ RemoteLog!GetEndOffset > tillOffset
            /\ ReplicaLog!TruncateFullyAndStartAt(replica, tillOffset)
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

\* FencedFollowerFetchKIP405 == \E follower, leader \in Replicas :
\*     /\ IsFollowingLeaderEpoch(leader, follower)
\*     \* Followers can only enter the fetch state when their end offset >= leader's local log start offset
\*     \* TODO - The Hasentry condition already checks for this
\*     /\ ReplicaLog!GetEndOffset(follower) >= GetLocalLogStartOffset(leader)
\*     /\ ReplicaLog!ReplicateTo(leader, follower)
\*     /\ LET  newEndOffset == ReplicaLog!GetEndOffset(follower) + 1
\*             leaderHw == replicaState[leader].hw
\*             followerHw == Min({leaderHw, newEndOffset})
\*        IN   replicaState' = [replicaState EXCEPT ![follower].hw = followerHw]
\*     /\ UNCHANGED <<remoteLog, nextRecordId, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

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
    /\ IsFollowingLeaderEpoch(leader, follower)
    \* The next conditions are to ensure that when we talk to the leader, leader should treat itself as leader.
    /\ ReplicaPresumesLeadership(leader)
    \* This is the enabling condition for going into BuildAux state
    /\ ReplicaLog!GetEndOffset(follower) < GetLocalLogStartOffset(leader) \* TODO - add another condition that this is available globally
    \* Truncate from start till leader's local log start offset
    \* This also updates the start offset & end offset of the follower
    /\ ReplicaLog!TruncateFullyAndStartAt(follower, GetLocalLogStartOffset(leader))
    /\ UNCHANGED <<remoteLog, nextRecordId, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

\* diviv - todo - build a LeaderArchiveToRemoteStorage state
\* end offset of TS for a particular epoch chain <= hw (last stable offset) of leader
\* 
LeaderArchiveToRemoteStorage == \E leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ \E uploadOffset \in ReplicaLog!GetStartOffset(leader) .. GetHighWatermark(leader):
        /\ RemoteLog!Append(ReplicaLog!GetRecordAtOffset(leader, uploadOffset), uploadOffset)
    /\ UNCHANGED <<nextRecordId, replicaLog, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(** 
 * Invariant to test the contibuity of the logs
 *)
LogContinuityOK == \E replica \in Replicas :
    \* There are no holes in the log
    /\ RemoteLog!GetEndOffset >= ReplicaLog!GetStartOffset(replica)

LogArchiveOk == \E leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader) 
    /\ \A replica \in Replicas :
        /\ IsFollowingLeaderEpoch(leader, replica)
    => /\ RemoteLog!GetEndOffset < GetHighWatermark(leader) \* todo - is it < or <=11    \* Uncommitted offsets cannot be moved to Remote Storage
    
TestLeaderLogNotExpire == ~\E replica \in Replicas :
    ReplicaLog!GetStartOffset(replica) = 2

TestLeaderNotIncrementingHw == \A replica \in Replicas :
    replicaState[replica].hw = 0

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
    \/ LeaderArchiveToRemoteStorage

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(FencedLeaderIncHighWatermark)
             /\ SF_vars(FencedLeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(FencedBecomeFollowerAndTruncate)
             /\ WF_vars(BecomeLeader)

\* THEOREM Spec => []TypeOk
=============================================================================
\* Modification History
\* Last modified Thu Oct 20 10:04:24 PDT 2022 by diviv
\* Created Wed Sep 14 15:39:13 CEST 2022 by diviv
