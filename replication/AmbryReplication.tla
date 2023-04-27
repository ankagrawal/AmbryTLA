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
    deleteCtr,
    updateTtlCtr,
    recvReplicationReqSet,
    sendRecplicationSet,
    recvReplicationRespSet>>

StoredMessagesSet ==
    { [ blobid |-> i, blobmessage |-> m ]
        : i \in BlobIds, m \in {DELETE, UPDATE_TTL} }

BlobCountConstraint ==
    /\ blobIdCtr <= NumBlobs

(* Replica storage record for a PUT message *)
PutMessage(message) ==
    [ blobid |-> message.blobid, blobmessage |-> PUT ]

(* Replica storage record for a DELETE message *)
DeleteMessage(message) ==
    [ blobid |-> message.blobid, blobmessage |-> DELETE ]

(* Replica storage record for a UPDATE TTL message *)
UpdateTtlMessage(message) ==
    [ blobid |-> message.blobid, blobmessage |-> UPDATE_TTL ]

TypeOK ==
    /\ replicaStates \in [Replicas -> ReplicaStateSet]
    /\ DOMAIN inflightReplicationMessages \subseteq Replicas
    /\ DOMAIN storedMessagesPerReplica \subseteq Replicas
    /\ DOMAIN inflightReplicationRequest \subseteq Replicas
    /\ DOMAIN inflightReplicationResponse \subseteq Replicas
    /\ recvReplicationReqSet \subseteq Replicas
    /\ sendRecplicationSet \subseteq Replicas
    /\ recvReplicationRespSet \subseteq Replicas


Init ==
    /\ storedMessagesPerReplica = [ r \in Replicas |-> {} ]
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
    /\ UNCHANGED <<storedMessagesPerReplica, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Bring up a replica. *)
ReplicaUp(r) ==
    /\ replicaStates' = [replicaStates EXCEPT ![r] = CanTakeWrite]
    /\ UNCHANGED <<storedMessagesPerReplica, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Receive a PUT request with success target of 1.
 * For the request to succeed, its enough for one replica to be up to accept the write.
 *)
RecvPut1 ==
    /\ \E r1 \in Replicas:
        /\ blobIdCtr <= NumBlobs
        /\ blobIdCtr' = blobIdCtr + 1
        /\ replicaStates[r1] = CanTakeWrite
        /\ storedMessagesPerReplica' = [r \in DOMAIN storedMessagesPerReplica |-> 
            IF (r = r1) THEN
                storedMessagesPerReplica[r] \union { [blobid |-> blobIdCtr, blobmessage |-> PUT ] }
            ELSE
                storedMessagesPerReplica[r]
            ]
    /\ UNCHANGED <<replicaStates, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, deleteCtr, updateTtlCtr, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Receive a PUT request with success target of 2.
 * For the request to succeed, atleast two replicas must be up to accept the write.
 *)
RecvPut ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 = r2
        /\ blobIdCtr < NumBlobs
        /\ blobIdCtr' = blobIdCtr + 1
        /\ replicaStates[r1] = CanTakeWrite
        /\ replicaStates[r2] = CanTakeWrite
        /\ [blobid |-> blobIdCtr, blobmessage |-> PUT ] \notin storedMessagesPerReplica[r1]
        /\ [blobid |-> blobIdCtr, blobmessage |-> PUT ] \notin storedMessagesPerReplica[r2]
        /\ storedMessagesPerReplica' = [r \in DOMAIN storedMessagesPerReplica |-> 
            IF ((r = r1) \/ (r = r2)) THEN
                storedMessagesPerReplica[r] \union { [blobid |-> blobIdCtr, blobmessage |-> PUT ] }
            ELSE
                storedMessagesPerReplica[r]
            ]
    /\ UNCHANGED <<replicaStates, inflightReplicationMessages, deleteCtr, updateTtlCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Receive a DELETE request with success target of 2.
 * For the request to succeed, atleast two replicas
 *    - must be up AND
 *    - must have a PUT record for the blob.
 *)
RecvDelete(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ blobId < blobIdCtr
        /\ replicaStates[r1] = CanTakeWrite
        /\ replicaStates[r2] = CanTakeWrite
        /\ deleteCtr' = deleteCtr + 1
        /\ [blobid |-> blobId, blobmessage |-> PUT ] \in storedMessagesPerReplica[r1]
        /\ [blobid |-> blobId, blobmessage |-> PUT ] \in storedMessagesPerReplica[r2]
        /\ [blobid |-> blobId, blobmessage |-> DELETE ] \notin storedMessagesPerReplica[r2]
        /\ [blobid |-> blobId, blobmessage |-> DELETE ] \notin storedMessagesPerReplica[r1]
        /\ storedMessagesPerReplica' = [rr \in DOMAIN storedMessagesPerReplica |-> 
            IF ((rr = r1) \/ (rr = r2)) THEN
                storedMessagesPerReplica[rr] \union { [ blobid |-> blobId, blobmessage |-> DELETE ] }
            ELSE
                storedMessagesPerReplica[rr]
            ]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, updateTtlCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Receive a UPDATE TTL request with success target of 2.
 * For the request to succeed, atleast two replicas
 *    - must be up AND
 *    - must have a PUT record for the blob AND
 *    - must not have a DELETE record for the blob.
 *)
RecvUpdateTtl(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ blobId < blobIdCtr
        /\ replicaStates[r1] = CanTakeWrite
        /\ replicaStates[r2] = CanTakeWrite
        /\ [ blobid |-> blobId, blobmessage |-> PUT ] \in storedMessagesPerReplica[r1]
        /\ [ blobid |-> blobId, blobmessage |-> DELETE ] \notin storedMessagesPerReplica[r1]
        /\ [ blobid |-> blobId, blobmessage |-> PUT ] \in storedMessagesPerReplica[r2]
        /\ [ blobid |-> blobId, blobmessage |-> DELETE ] \notin storedMessagesPerReplica[r2]
        /\ [ blobid |-> blobId, blobmessage |-> UPDATE_TTL ] \notin storedMessagesPerReplica[r2]
        /\ [ blobid |-> blobId, blobmessage |-> UPDATE_TTL ] \notin storedMessagesPerReplica[r1]
        /\ storedMessagesPerReplica' = [rr \in DOMAIN storedMessagesPerReplica |-> 
            IF ((rr = r1) \/ (rr = r2)) THEN
                storedMessagesPerReplica[rr] \union { [ blobid |-> blobId, blobmessage |-> UPDATE_TTL ] }
            ELSE
                storedMessagesPerReplica[rr]
            ]
        /\ updateTtlCtr' = updateTtlCtr + 1
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, deleteCtr, inflightReplicationRequest, inflightReplicationResponse, recvReplicationReqSet, sendRecplicationSet, recvReplicationRespSet>>

(* Bring one replica up and one replica down *)
ReplicaStateChange ==
    \E m, n \in Replicas:
        \/ ReplicaDown(n)
        \/ ReplicaUp(m)

(* Ambry uses a pull model for replication.
 * In SendReplicationRequest action, a replica asks one of its peers to give the set of data the peer has.
 * This action just enqueues the request to peer in "inflightReplicationRequest".
 *)
SendReplicationRequest(src) ==
    /\ replicaStates[src] = CanTakeWrite \* We want replica asking for replication pull to be writable.
    /\ \E tgt \in Replicas:
        /\ src # tgt
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![tgt] = inflightReplicationRequest[tgt] \union {src} ]
    /\ IF AllBlobOpsDone THEN 
           sendRecplicationSet' = sendRecplicationSet \union {src}
       ELSE
           sendRecplicationSet' = sendRecplicationSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, storedMessagesPerReplica, deleteCtr, updateTtlCtr, inflightReplicationMessages, inflightReplicationResponse, recvReplicationReqSet, recvReplicationRespSet>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationRequest action, a replica recieves replication request from a peer and sends all of its storage log.
 * This action enqueues the entire storage log "inflightReplicationResponse".
 *)
RecvReplicationRequest(r) ==
    /\ inflightReplicationRequest[r] # {}
    /\ storedMessagesPerReplica[r] # {} \* there should be something to replicate.
    /\ \E src \in inflightReplicationRequest[r]:
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![src] = inflightReplicationResponse[src] \union {[r |-> r, messages |-> storedMessagesPerReplica[r]]} ]
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![r] = inflightReplicationRequest[r] \ {src}]
    /\ IF sendRecplicationSet = Replicas THEN 
           recvReplicationReqSet' = recvReplicationReqSet \union {r}
       ELSE
           recvReplicationReqSet' = recvReplicationReqSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, storedMessagesPerReplica, deleteCtr, updateTtlCtr, inflightReplicationMessages, sendRecplicationSet, recvReplicationRespSet>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationResponse action, a replica recieves replication response from a peer.
 * On reciept it checks if each message is present in its local storage log. If not presents, then it adds the message.
 *)
RecvReplicationResponse(r) ==
    /\ inflightReplicationResponse[r] # {}
    /\ \E msg \in inflightReplicationResponse[r]:
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ storedMessagesPerReplica' = [rr \in DOMAIN storedMessagesPerReplica |-> 
                    IF ((rr = r) /\ (PutMessage(message) \in storedMessagesPerReplica[r]) /\ (DeleteMessage(message) \notin storedMessagesPerReplica[r])) THEN
                        storedMessagesPerReplica[rr] \union { UpdateTtlMessage(message) }
                    ELSE
                        storedMessagesPerReplica[rr]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ storedMessagesPerReplica' = [storedMessagesPerReplica EXCEPT ![r] = storedMessagesPerReplica[r] \union { message } ]
                ELSE
                    /\ storedMessagesPerReplica' = [rr \in DOMAIN storedMessagesPerReplica |-> 
                        IF ((rr = r) /\ (PutMessage(message) \in storedMessagesPerReplica[r])) THEN
                            storedMessagesPerReplica[r] \union { DeleteMessage(message) }
                        ELSE
                            storedMessagesPerReplica[rr]
                        ]
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![r] = inflightReplicationResponse[r] \ {msg}]
    /\ IF recvReplicationRespSet = Replicas THEN 
           recvReplicationRespSet' = recvReplicationRespSet \union {r}
       ELSE
           recvReplicationRespSet' = recvReplicationRespSet
    /\ UNCHANGED <<replicaStates, blobIdCtr, deleteCtr, updateTtlCtr, inflightReplicationMessages, inflightReplicationRequest, recvReplicationReqSet, sendRecplicationSet>>

Next ==
    \/ ReplicaStateChange
    \/ RecvPut
    \/ \E blobid \in BlobIds:
       \/ RecvUpdateTtl(blobid)
    \/ \E blobid \in BlobIds:
       \/ RecvDelete(blobid)
    \/ \E r \in Replicas:
        \/ SendReplicationRequest(r)
        \/ RecvReplicationRequest(r)
        \/ RecvReplicationResponse(r)

(* Once all operations are done and replication has caught up, then the storage log of each replica should be consistent. *)
Safe ==
    [](AllOpsDone => Consistent)

Spec ==
    Init /\ [] [Next]_vars

==================================================================================================================

