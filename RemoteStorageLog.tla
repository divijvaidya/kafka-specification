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
GetRemoteOffsetRange == GetStartOffset..GetEndOffset-1

IsEmpty == remoteLog.endOffset = 0

GetLatestRecord == 
    /\ IF IsEmpty 
       THEN NilRecord 
       ELSE remoteLog.records[remoteLog.endOffset - 1]

HasEntry(record, offset) ==
    /\ offset < remoteLog.endOffset
    /\ offset >= remoteLog.startOffset
    /\ remoteLog.records[offset] = record

Append(record, offset) == 
    \* /\ offset = remoteLog.endOffset
\*     /\ remoteLog' = [remoteLog EXCEPT ![records] = [offset] = record, 
\*                                       !endOffset = @ + 1]
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