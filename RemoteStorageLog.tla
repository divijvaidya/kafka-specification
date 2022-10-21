------------------------ MODULE RemoteStorageLog ------------------------
EXTENDS Integers

CONSTANTS 
    LogRecords, 
    LogSize,
    MaxLeaderEpoch,
    NilRecord

ASSUME 
    /\ LogSize \in Nat 
    /\ MaxLeaderEpoch \in Nat

MaxOffset == LogSize - 1

Offsets == 0 .. MaxOffset

Epochs == Nat

VARIABLE remoteLog

LOCAL EpochType == [startOffset : 0..MaxOffset,
                    endOffset :  0..LogSize]

LOCAL LogType == [endOffset : Offsets \union {LogSize},
                  records : [Offsets -> LogRecords \union {NilRecord}],
                  startOffset : Offsets \union {LogSize}]
                  
LOCAL EmptyLog == [endOffset |-> 0, 
                   startOffset |-> 0,
                   records |-> [offset \in Offsets |-> NilRecord]]

GetStartOffset == remoteLog.startOffset
GetEndOffset == remoteLog.endOffset
    
Append(record, offset) == 
    \* /\ offset = remoteLog.endOffset
    \* /\ remoteLog' = [remoteLog EXCEPT ![records] = [offset] = record, 
    \*                                   !endOffset = @ + 1]
    /\ remoteLog' = [endOffset |-> remoteLog.endOffset + 1, 
                     startOffset |-> remoteLog.startOffset,
                     records |-> [remoteLog.records EXCEPT ![offset] = record]]
TypeOk == 
    /\ remoteLog \in LogType
    /\ GetEndOffset >= GetStartOffset

Init == remoteLog = EmptyLog

Next == \E record \in LogRecords, offset \in Offsets : Append(record, offset)

Spec == Init /\ [][Next]_remoteLog

THEOREM Spec => []TypeOk

=============================================================================