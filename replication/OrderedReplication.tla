---------------------- MODULE AmbryReplication ---------------------

EXTENDS Naturals
(***************************************************************************)
(* This specification describes the replication in Ambry, in which         *)
(* messages can come to replicas of an Ambry partition. The messages can   *)
(* be "PUT", "DELETE", "TTL UPDATE" (undelete will be covered later).      *)
(***************************************************************************)


(* KNOWN ISSUES IN THE MODEL: (fixes are WIP) *)
(* The sucess target of put, delete and update-ttl operations is not configurable *)
(* Replication replicates everything in each iteration. It should rather replicate only those blobs that need replication *)
(* Stored messages per replica don't have ordering. Hence replication is also not ordered. *)
(* No concept of replica token. *)
(* All the messages are replicated in one shot. *)
(* No distinction between local and remote replicas. *)
(* Update ttl should have an expiration time and replicas should handle that. *)

(* TODO
1. MAKE THE REPLICA STORED MESSAGES AN ORDERED LOG
2. MAKE REPLICATION HAPPEN VIA A REPLICATOKEN SO THAT ONLY NEW MESSAGES ARE REPLICATED
3. CREATE THE CONCEPT OF EXPIRATION TIME OF A BLOB.
*)


CONSTANT NumBlobs \* Total number of blob messages in a replica.
CONSTANT NumReplicas \* Total number of replicas of a partition.

(* BlobIds is the set of all blobids that can be present in Ambry.
 * Ambry generates the blobid for each user requests.
 * In this spec, everytime new blob is written to Ambry, ambry increments a zero-based counter and uses that as the blobid.
 *)
BlobIds == 0 .. NumBlobs-1

Replicas == 0 .. NumReplicas-1 \* Replicas are the set of all replicas of a partition present in Ambry.

(* For the ReplicaStates, *)
(*     "CanTakeWrite" represents "Leader", "Standby" & "Bootstrapping" states *)
(*     "CannotTakeWrite" represents "Offline" & "Inactive" states *)
CanTakeWrite == "CanTakeWrite" \* represents "Leader", "Standby" & "Bootstrapping" states
CannotTakeWrite == "CannotTakeWrite" \* represents "Offline" & "Inactive" states

PUT == "Put" \* Represents PUT message i.e, request to create a blob.
UPDATE_TTL == "UpdateTtl" \* Represents an update ttl message. In Ambry, update ttl just makes a blob permanent.
DELETE == "Delete" \* Represents a request to delete a blob.

ReplicaStateSet == {CanTakeWrite, CannotTakeWrite}
BlobOpSet == {PUT, DELETE, UPDATE_TTL}


ASSUME NumBlobsIsPosNat == NumBlobs \in Nat
ASSUME NumReplicasIsPosNat == NumReplicas \in Nat


VARIABLES
    replicaStates, \* State of each replica.
    storedMessagesPerReplica, \* Set of all blob messages present in a replica.
    blobIdCtr, \* Counter to represent blobid. When a new blob has to be Put, this counter will be used as the blob's blobid.
    inflightReplicationMessages, \* Inflight replication messages
    inflightReplicationRequest, \* Inflight request by a source replica to get next set of replication data from target replica.
    inflightReplicationResponse, \* Inflight response to replication sent by a replica to the replication requester.
    orderedStoredMessagesPerReplica,
    replicaTokens,
    replicaOffsets,

    (* The variables below are not system state but are needed to check that all user operations are done.
     * Once all the operations are done, and each replica has had a chance to do replication atleast once, then we can check for consistency.
     *)
    deleteCtr, \* Count of delete operations.
    updateTtlCtr, \* Count of update ttl operations.
    recvReplicationReqSet, \* Set of replicas that executed RecvReplicationRequest.
    sendRecplicationSet, \* Set of replicas that executed SendReplicationRequest.
    recvReplicationRespSet \* Set of replicas that executed RecvReplicationResponse.

vars == <<replicaStates,
    storedMessagesPerReplica,
    blobIdCtr,
    inflightReplicationMessages,
    inflightReplicationRequest,
    inflightReplicationResponse, 
    orderedStoredMessagesPerReplica,
    replicaTokens,
    replicaOffsets,
    deleteCtr,
    updateTtlCtr,
    recvReplicationReqSet,
    sendRecplicationSet,
    recvReplicationRespSet>>

StoredMessagesSet ==
    { [ blobid |-> i, blobmessage |-> m, logoffset |-> offset ]
        : i \in BlobIds, m \in {DELETE, UPDATE_TTL}, offset \in 0 .. (NumBlobs*3) }

BlobCountConstraint ==
    /\ blobIdCtr <= NumBlobs

(* Replica storage record for a PUT message *)
PutMessage(message, offset) ==
    [ blobid |-> message.blobid, blobmessage |-> PUT, logoffset |-> offset ]

(* Replica storage record for a DELETE message *)
DeleteMessage(message, offset) ==
    [ blobid |-> message.blobid, blobmessage |-> DELETE, logoffset |-> offset  ]

(* Replica storage record for a UPDATE TTL message *)
UpdateTtlMessage(message, offset) ==
    [ blobid |-> message.blobid, blobmessage |-> UPDATE_TTL, logoffset |-> offset  ]

(* Replica storage record for a PUT message *)
PutRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> PUT, logoffset |-> offset ]

(* Replica storage record for a DELETE message *)
DeleteRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> DELETE, logoffset |-> offset  ]

(* Replica storage record for a UPDATE TTL message *)
UpdateTtlRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> UPDATE_TTL, logoffset |-> offset  ]

ReplicaHasPutMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = PUT

ReplicaHasDeleteMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = DELETE

ReplicaHasUpdateTtlMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = UPDATE_TTL

ReplicaCanTakePut(blobid, replicaid, orderedMessagesPerReplica, replicaStates) ==
    /\ replicaStates[replicaid] = CanTakeWrite
    /\ ~HasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

ReplicaCanTakeTtlUpdate(blobid, replicaid, orderedMessagesPerReplica, replicaStates) ==
    /\ replicaStates[replicaid] = CanTakeWrite
    /\ HasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    /\ ~HasDeleteMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    /\ ~HasUpdateTtlMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

ReplicaCanTakeDelete(blobid, replicaid, orderedMessagesPerReplica, replicaStates) ==
    /\ replicaStates[replicaid] = CanTakeWrite
    /\ HasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    /\ ~HasDeleteMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

ReplicationRequestMessage(sourceReplica, replicaToken) ==
    [ src |-> targetReplica, token |-> replicaToken ]

ReplicaRecordAtOffset(replicaid, orderedMessagesPerReplica, offset) ==
    IF orderedMessagesPerReplica[replicaid] # {} THEN 
        {msg \in orderedMessagesPerReplica[replicaid]: msg.logoffset = offset}
    ELSE {}

ReplicationResponseMessage(replicaid, replicaStoredMessages, msg) ==
    {[r |-> replicaid, messages |-> ReplicaRecordAtOffset(replicaid, replicaStoredMessages, msg.token)]}

TypeOK ==
    /\ replicaStates \in [Replicas -> ReplicaStateSet]
    /\ DOMAIN inflightReplicationMessages \subseteq Replicas
    /\ DOMAIN storedMessagesPerReplica \subseteq Replicas
    /\ DOMAIN orderedStoredMessagesPerReplica \subseteq Replicas
    /\ DOMAIN inflightReplicationRequest \subseteq Replicas
    /\ DOMAIN inflightReplicationResponse \subseteq Replicas
    /\ recvReplicationReqSet \subseteq Replicas
    /\ sendRecplicationSet \subseteq Replicas
    /\ recvReplicationRespSet \subseteq Replicas
    /\ DOMAIN replicaTokens \subseteq Replicas
    /\ DOMAIN replicaOffsets \subseteq Replicas


Init ==
    /\ storedMessagesPerReplica = [ r \in Replicas |-> {} ]
    /\ orderedStoredMessagesPerReplica = [ r \in Replicas |-> {} ]
    /\ inflightReplicationMessages = [ r \in Replicas |-> {} ]
    /\ inflightReplicationRequest = [ r \in Replicas |-> {} ]
    /\ inflightReplicationResponse = [ r \in Replicas |-> {} ]
    /\ replicaStates = [ r \in Replicas |-> CanTakeWrite ]
    /\ blobIdCtr = 0
    /\ deleteCtr = 0
    /\ updateTtlCtr = 0
    /\ recvReplicationReqSet = {}
    /\ sendRecplicationSet = {}
    /\ recvReplicationRespSet = {}
    /\ replicaTokens = [r \in Replicas |-> [ rr \in Replicas |-> 0 ] ]
    /\ replicaOffsets = [r \in Replicas |-> 0 ]

(* If each blob has seen PUTs, updateTtl and Delete then we can assume that all user operations have ended. *)
AllBlobOpsDone == 
    /\ blobIdCtr = NumBlobs
    /\ updateTtlCtr = NumBlobs
    /\ deleteCtr = NumBlobs

(* Ensures that each replica has had a chance to replicate atleast once after "AllBlobOpsDone" is true. *)
AllOpsDone ==
    /\ recvReplicationRespSet = Replicas

(* The replicas are consistent, if their local storage log agrees on all the operations. *)
Consistent ==
    \A r1, r2 \in Replicas:
        (r1 # r2) => (storedMessagesPerReplica[r1] = storedMessagesPerReplica[r2])

(* Bring down a replica. *)
ReplicaDown(r) ==
    /\ replicaStates' = [replicaStates EXCEPT ![r] = CannotTakeWrite]
    /\ UNCHANGED <<storedMessagesPerReplica, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, orderedStoredMessagesPerReplica, replicaTokens>>

(* Bring up a replica. *)
ReplicaUp(r) ==
    /\ replicaStates' = [replicaStates EXCEPT ![r] = CanTakeWrite]
    /\ UNCHANGED <<storedMessagesPerReplica, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, orderedStoredMessagesPerReplica, replicaTokens>>


RecvPut1 ==
    /\ \E r1 \in Replicas:
        /\ blobIdCtr' = blobIdCtr + 1
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF ((r = r1) /\ ReplicaCanTakePut(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN
                orderedStoredMessagesPerReplica[r] \union { PutRecord(blobIdCtr, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r1] = replicaOffsets[r1] + 1 ]
    /\ UNCHANGED <<replicaStates, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, replicaTokens, storedMessagesPerReplica>>


RecvPut ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakePut(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN
                orderedStoredMessagesPerReplica[r] \union { PutRecord(blobIdCtr, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakePut(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
        /\ blobIdCtr' = blobIdCtr + 1
    /\ UNCHANGED <<replicaStates, inflightReplicationMessages, deleteCtr, updateTtlCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, storedMessagesPerReplica, replicaTokens>>


RecvDelete(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeDelete(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN
                orderedStoredMessagesPerReplica[r] \union { DeleteRecord(blobIdCtr, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeDelete(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
        /\ deleteCtr' = deleteCtr + 1
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, updateTtlCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, storedMessagesPerReplica, replicaTokens>>


RecvUpdateTtl(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeTtlUpdate(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN
                orderedStoredMessagesPerReplica[r] \union { UpdateTtlRecord(blobIdCtr, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeTtlUpdate(blobIdCtr, replicaid, orderedStoredMessagesPerReplica, replicaStates)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
        /\ updateTtlCtr' = updateTtlCtr + 1
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, deleteCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet, storedMessagesPerReplica, replicaTokens>>

(* Ambry uses a pull model for replication.
 * In SendReplicationRequest action, a replica asks one of its peers to give the set of data the peer has.
 * This action just enqueues the request to a peer in "inflightReplicationRequest".
 *)
SendReplicationRequest(src) ==
    /\ replicaStates[src] = CanTakeWrite \* We want replica asking for replication pull to be writable.
    /\ \E tgt \in Replicas:
        /\ src # tgt
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![tgt] = inflightReplicationRequest[tgt] \union { ReplicationRequestMessage(src, replicaTokens[src][tgt]) } ]
    /\ IF AllBlobOpsDone THEN 
           sendRecplicationSet' = sendRecplicationSet \union {src}
       ELSE
           sendRecplicationSet' = sendRecplicationSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, storedMessagesPerReplica, deleteCtr, updateTtlCtr, inflightReplicationMessages, inflightReplicationResponse, recvReplicationReqSet, recvReplicationRespSet, storedMessagesPerReplica, replicaTokens, orderedStoredMessagesPerReplica, replicaOffsets>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationRequest action, a replica recieves replication request from a peer and sends all of its storage log.
 * This action enqueues the entire storage log "inflightReplicationResponse".
 *)
RecvReplicationRequest(r) ==
    /\ inflightReplicationRequest[r] # {}
    /\ storedMessagesPerReplica[r] # {} \* there should be something to replicate. \* {[r |-> r, messages |-> storedMessagesPerReplica[r]]}
    /\ \E msg \in inflightReplicationRequest[r]:
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![msg.src] = inflightReplicationResponse[msg.src] \union ReplicationResponseMessage(r, orderedStoredMessagesPerReplica, msg) ]
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![r] = inflightReplicationRequest[r] \ {msg}]
    /\ IF sendRecplicationSet = Replicas THEN 
           recvReplicationReqSet' = recvReplicationReqSet \union {r}
       ELSE
           recvReplicationReqSet' = recvReplicationReqSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, storedMessagesPerReplica, deleteCtr, updateTtlCtr, inflightReplicationMessages, sendRecplicationSet, recvReplicationRespSet>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationResponse action, a replica recieves replication response from a peer.
 * On reciept it checks if each message is present in its local storage log. If not presents, then it adds the message.
 *)
 (*
 Earlier the inflightReplicationResponse was 
 *)
RecvReplicationResponse(r) ==
    /\ inflightReplicationResponse[r] # {}
    /\ \E msg \in inflightReplicationResponse[r]:
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ orderedStoredMessagesPerReplica' = [rr \in DOMAIN orderedStoredMessagesPerReplica |-> 
                    IF ((rr = r) /\ ReplicaCanTakeTtlUpdate(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates)) THEN
                        orderedStoredMessagesPerReplica[rr] \union { UpdateTtlMessage(message, replicaOffsets[rr]) }
                    ELSE
                        orderedStoredMessagesPerReplica[rr]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ orderedStoredMessagesPerReplica' = [ orderedStoredMessagesPerReplica EXCEPT ![r] = 
                        IF ReplicaCanTakePut(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates) THEN
                            orderedStoredMessagesPerReplica[r] \union { PutMessage(message, replicaOffsets[rr]) }
                        ELSE 
                            orderedStoredMessagesPerReplica[r] ]
                ELSE
                    /\ orderedStoredMessagesPerReplica' = [rr \in DOMAIN orderedStoredMessagesPerReplica |-> 
                        IF ((rr = r) /\ ReplicaCanTakeDelete(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates)) THEN
                            orderedStoredMessagesPerReplica[r] \union { DeleteMessage(message, replicaOffsets[rr]) }
                        ELSE
                            orderedStoredMessagesPerReplica[rr]
                        ]
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                    IF (ReplicaCanTakeTtlUpdate(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates)) THEN
                        replicaOffsets[rr] + 1
                    ELSE
                        replicaOffsets[rr]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                        IF ReplicaCanTakePut(message.blobid, r, replicaOffsets, replicaStates) THEN
                            replicaOffsets[r] + 1
                        ELSE 
                            replicaOffsets[r]
                        ]
                ELSE
                    /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                        IF ReplicaCanTakeDelete(message.blobid, r, replicaOffsets, replicaStates) THEN
                            replicaOffsets[r] + 1
                        ELSE
                            replicaOffsets[r]
                    ]
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                    IF (ReplicaCanTakeTtlUpdate(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                        message.logoffset \* Should this be incremented by 1
                    ELSE
                        replicaTokens[r][msg.r]
                ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                        IF (ReplicaCanTakePut(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                            message.logoffset \* Should this be incremented by 1
                        ELSE
                            replicaTokens[r][msg.r]
                    ]
                ELSE
                    /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                        IF (ReplicaCanTakeDelete(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                            message.logoffset \* Should this be incremented by 1
                        ELSE
                            replicaTokens[r][msg.r]
                    ]
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![r] = inflightReplicationResponse[r] \ {msg}]
    /\ IF recvReplicationRespSet = Replicas THEN 
           recvReplicationRespSet' = recvReplicationRespSet \union {r}
       ELSE
           recvReplicationRespSet' = recvReplicationRespSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, deleteCtr, updateTtlCtr, inflightReplicationMessages, inflightReplicationRequest, recvReplicationReqSet, sendRecplicationSet>>

Next ==
    \/ RecvPut
    \/ \E blobid \in BlobIds:
       \/ RecvUpdateTtl(blobid)
    \/ \E blobid \in BlobIds:
       \/ RecvDelete(blobid)
    \/ \E r \in Replicas:
        \/ SendReplicationRequest(r)
        \/ RecvReplicationRequest(r)
        \/ RecvReplicationResponse(r)
    \/ \E r \in Replicas:
        \/ ReplicaUp(r)
    \/ \E r \in Replicas:
        \/ ReplicaDown(r)

(* Once all operations are done and replication has caught up, then the storage log of each replica should be consistent. *)
Safe ==
    [](AllOpsDone => Consistent)

Spec ==
    Init /\ [] [Next]_vars

==================================================================================================================

