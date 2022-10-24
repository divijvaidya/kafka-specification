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
 
------------------------ MODULE FiniteReplicatedLog ------------------------

EXTENDS Integers, TLC

CONSTANTS 
    Replicas, 
    LogRecords, 
    NilRecord, 
    LogSize

(*
ASSUME
    /\ LogSize \in Nat
    /\ Nil \notin LogRecords
*)
VARIABLE logs \* divij - logs is a sequence of LogType where each index represents a replica

MaxOffset == LogSize - 1

Offsets == 0 .. MaxOffset

\*
\* Logs is a sequence where index is replica number
\* log = logs[replica]
\* log is a struct:
\*     - endOffset 
\*     - records is a sequence where index is offset
\*     - startOffset
\* 
LOCAL LogType == [endOffset : Offsets \union {LogSize},
                  records : [Offsets -> LogRecords \union {NilRecord}],
                  startOffset : Offsets \union {LogSize}]
                  
LOCAL EmptyLog == [endOffset |-> 0, 
                   startOffset |-> 0,
                   records |-> [offset \in Offsets |-> [id |-> -1, 
                                                        epoch |-> -1]]]

IsEmpty(replica) == logs[replica].endOffset = 0

IsFull(replica) == logs[replica].endOffset = LogSize


\* diviv - TODO - HasEntry should add offset > log.globalStartOffset
HasEntry(replica, record, offset) == LET log == logs[replica] IN
    /\ offset < log.endOffset
    /\ offset >= log.startOffset
    /\ log.records[offset] = record

\* diviv - TODO - HasLocalEntry should add offset > log.localstartOffset
HasLocalEntry(replica, record, offset) == LET log == logs[replica] IN
    /\ HasEntry(replica, record, offset)
    /\ offset < log.localStartOffset

IsLatestEntry(replica, record, offset) == LET log == logs[replica] IN
    /\ ~ IsEmpty(replica)
    /\ offset = log.endOffset - 1
    /\ record = log.records[offset]

GetLatestRecord(replica) == LET log == logs[replica] IN 
    IF IsEmpty(replica) 
    THEN NilRecord 
    ELSE log.records[log.endOffset - 1]

IsLatestRecord(replica, record) == \E offset \in Offsets : IsLatestEntry(replica, record, offset)

GetEndOffset(replica) == logs[replica].endOffset

GetStartOffset(replica) == logs[replica].startOffset

IsEndOffset(replica, offset) == logs[replica].endOffset = offset 

GetRecordAtOffset(replica, offset) == logs[replica].records[offset]

HasOffset(replica, offset) == 
    /\ offset < logs[replica].endOffset
    /\ offset >= logs[replica].startOffset

GetWrittenOffsets(replica) == 
    IF IsEmpty(replica)
    THEN {}
    ELSE logs[replica].startOffset .. (logs[replica].endOffset - 1) \* tillOffset should be till high water

LOCAL GetUnwrittenOffsets(replica) ==
    IF IsFull(replica)
    THEN {}
    ELSE logs[replica].endOffset .. MaxOffset
    
GetAllEntries(replica) == LET log == logs[replica] IN
    IF log.endOffset = 0
    THEN {}
    ELSE {[offset |-> offset, 
           record |-> GetRecordAtOffset(replica, offset)] : offset \in GetWrittenOffsets(replica)}
    
LOCAL ReplicaLogTypeOk(replica) == LET log == logs[replica] IN
    /\ Print(<<"inside replicaLogTypeOk:log ", log>>, TRUE)
    /\ Print(<<"inside replicaLogTypeOk:LogType", LogRecords>>, TRUE)
    /\ log \in LogType
\*    /\ \A offset \in GetWrittenOffsets(replica) : log.records[offset] \in LogRecords
\*    /\ \A offset \in GetUnwrittenOffsets(replica) : log.records[offset] = Nil
    \* /\ GetEndOffset(replica) >= GetStartOffset(replica)
    
TypeOk == \A replica \in Replicas : ReplicaLogTypeOk(replica)

Init == logs = [replica \in Replicas |-> EmptyLog]

Append(replica, record, offset) == LET log == logs[replica] IN
    /\ ~ IsFull(replica)
    /\ offset = log.endOffset
    /\ logs' = [logs EXCEPT ![replica].records[offset] = record, 
                            ![replica].endOffset = @ + 1] 

TruncateTo(replica, newEndOffset) == LET log == logs[replica] IN
    /\ newEndOffset \leq log.endOffset
    /\ logs' = [logs EXCEPT 
        ![replica].records = [offset \in Offsets |-> IF offset < newEndOffset THEN @[offset] ELSE NilRecord], 
        ![replica].endOffset = newEndOffset]

TruncateFullyAndStartAt2(replica, newStartOffset) == LET log == logs[replica] IN
    /\ newStartOffset \geq log.startOffset
    /\ logs' = [logs EXCEPT 
        \* Empty all data from the logs
        ![replica].records = [offset \in Offsets |-> [id |-> -1, 
                                                    epoch |-> -1]],  \* TODO - 
        ![replica].startOffset = newStartOffset,
        ![replica].endOffset = newStartOffset]

\* We don't need to update end offset because it is guaranteed that end offset will remain unchanged due to
\* the enabling condition /\ tillOffset < log.endOffset
TruncateFullyAndStartAt(replica, tillOffset) == LET log == logs[replica] IN
    /\ tillOffset \geq log.startOffset
    /\ tillOffset < log.endOffset
    /\ logs' = [logs EXCEPT 
        \* Empty all data from the logs
        ![replica].records = [offset \in Offsets |-> IF offset > tillOffset THEN @[offset] ELSE [id |-> -1, 
                                                                                                 epoch |-> -1]], 
        ![replica].startOffset = tillOffset + 1]
    

\* diviv - TODO - HasEntry should be changed HasLocalEntry 
ReplicateTo(fromReplica, toReplica) == \E offset \in Offsets, record \in LogRecords :
    /\ HasEntry(fromReplica, record, offset)
    /\ Append(toReplica, record, offset)

LOCAL Next == \E replica \in Replicas :
    \/ \E record \in LogRecords, offset \in Offsets : Append(replica, record, offset)
    \/ \E offset \in Offsets : TruncateTo(replica, offset)
    \/ \E offset \in Offsets : TruncateFullyAndStartAt(replica, offset)
    \/ \E otherReplica \in Replicas \ {replica} : ReplicateTo(replica, otherReplica)
        
LOCAL Spec == Init /\ [][Next]_logs

THEOREM Spec => []TypeOk
=============================================================================
\* Modification History
\* Last modified Fri Oct 21 07:42:34 PDT 2022 by diviv
\* Last modified Mon Jul 09 14:23:51 PDT 2018 by jason
\* Created Sat Jun 23 13:24:52 PDT 2018 by jason
