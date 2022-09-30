------------------------ MODULE RemoteStorageLog ------------------------

CONSTANTS 
    LogRecords, 
    LogSize
    MaxEpoch

ASSUME 
    /\ LogSize \in Nat 
    /\ MaxEpoch \in Nat

MaxOffset == LogSize - 1

Offsets == 0 .. MaxOffset

Epochs == Nat

VARIABLE remoteLog

LOCAL EpochType == [startOffset : 0..MaxOffset,
                    endOffset :  0..LogSize]

LOCAL LogType == [endOffset : Offsets \union {LogSize},
                  records : [Offsets -> LogRecords \union {Nil}],
                  startOffset : Offsets \union {LogSize}]

LOCAL EmptyLog == [endOffset |-> 0, 
                   startOffset |-> 0,
                   records |-> [offset \in Offsets |-> Nil]]

GetStartOffset == remoteLog.startOffset
GetEndOffset == remoteLog.endOffset
    

Append(record, offset) == 
    /\ offset = log.endOffset
    /\ remoteLog' = [remoteLog EXCEPT !remoteLog.records[offset] = record, !remoteLog.endOffset = @ + 1]

TypeOk == 
    /\ remoteLog \in LogType
    /\ remoteLog.endOffset >= remoteLog.startOffset

Init == (* Global variables *)
    /\ remoteLog = EmptyLog

Next == \E record \in LogRecords, offset \in Offsets : Append(record, offset)

Spec == Init /\ [][Next]_remoteLog

THEOREM Spec => []TypeOk

=============================================================================