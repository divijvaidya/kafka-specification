------------------------------- MODULE Kip405 -------------------------------
EXTENDS KafkaReplication, TLC

LOCAL GetLocalLogStartOffset(replica) == ReplicaLog!GetStartOffset(replica)
LOCAL GetGlobalLogStartOffset == RemoteLog!GetStartOffset

ReplicaDataExpireKIP405 == \E replica \in Replicas:
        /\ ~RemoteLog!IsEmpty \* Only enable this state is remote log is non-empty
        /\ \E tillOffset \in RemoteLog!GetRemoteOffsetRange:
            /\ ReplicaLog!TruncateFromTailTillOffset(replica, tillOffset)
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

\* LeaderArchiveToRemoteStorage state
\* end offset of TS for a particular epoch chain <= hw (last stable offset) of leader
\* 
LeaderArchiveToRemoteStorage == \E leader \in Replicas :
    /\ ReplicaPresumesLeadership(leader)
    /\ \E uploadOffset \in RemoteLog!GetEndOffset..GetHighWatermark(leader):
        /\ RemoteLog!Append(ReplicaLog!GetRecordAtOffset(leader, uploadOffset), uploadOffset)
    /\ UNCHANGED <<nextRecordId, replicaLog, replicaState, quorumState, nextLeaderEpoch, leaderAndIsrRequests>>

(** 
 * Invariant to test the continuity of the logs
 * TODO - Add invaraint that the epoch for latest remote offset is part of leader chain
 *)
LogContinuityOk == \E leader \in Replicas :
    \* There are no holes in the log when compared to true leader
    /\ IsTrueLeader(leader) => RemoteLog!GetEndOffset >= ReplicaLog!GetStartOffset(leader) 

(**
 * Uncommitted offsets on a leader cannot be moved to Remote Storage
 * - Enable for cases when NoSplitBrain
 * - TODO: Handle split brain
 *)
LogArchiveOk == \E leader \in Replicas :
    /\ NoSplitBrain(leader) => RemoteLog!GetEndOffset < GetHighWatermark(leader)

TestLeaderLogNotExpire == 
    /\ \E leader \in Replicas:
            /\ IsTrueLeader(leader)
            /\ ReplicaLog!GetStartOffset(leader) > 1
            /\ \A replica \in Replicas:
                /\ IsFollowingLeaderEpoch(replica, leader)
    => /\ \A replica \in Replicas :
           /\ ReplicaLog!GetStartOffset(replica) < 1
           
\* TODO           
\*AllInSyncReplicaHaveSameDataTillHw
           
TestReplicaHasMovedStartOffset ==
    \/ ~\E replica, leader \in Replicas:
        /\ ~ReplicaPresumesLeadership(replica)
        /\ ReplicaLog!GetStartOffset(replica) = 1
        /\ IsFollowingLeaderEpoch(replica, leader)
        /\ IsTrueLeader(leader)
    \/ ~\E leader \in Replicas:
        /\ IsTrueLeader(leader)
        /\ ReplicaLog!GetStartOffset(leader) = 1
    
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
    \/ ReplicaDataExpireKIP405
    \/ FollowerBuildAuxState
    \/ LeaderArchiveToRemoteStorage

Spec == Init /\ [][Next]_vars 
             /\ SF_vars(FencedLeaderIncHighWatermark)
             /\ SF_vars(FencedLeaderExpandIsr)
             /\ SF_vars(LeaderWrite)
             /\ WF_vars(FencedBecomeFollowerAndTruncate)
             /\ WF_vars(BecomeLeader)

THEOREM Spec => []TypeOk
=============================================================================
\* Modification History
\* Last modified Wed Oct 26 16:56:19 UTC 2022 by ec2-user
\* Last modified Thu Oct 20 10:04:24 PDT 2022 by diviv
\* Created Wed Sep 14 15:39:13 CEST 2022 by diviv
