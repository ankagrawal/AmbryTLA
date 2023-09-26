---------------------- MODULE OrderedReplication ---------------------

EXTENDS Naturals, FiniteSets
(***************************************************************************)
(* This specification describes the replication in Ambry, in which         *)
(* messages can come to replicas of an Ambry partition. The messages can   *)
(* be "PUT", "DELETE", "TTL UPDATE" (undelete will be covered later).      *)
(***************************************************************************)


CONSTANT NumBlobs \* Total number of blob messages in a replica.
CONSTANT NumReplicas \* Total number of replicas of a partition.

(* BlobIds is the set of all blobids that can be present in Ambry.
 * Ambry generates the blobid for each user requests.
 * In this spec, everytime new blob is written to Ambry, Ambry increments a zero-based counter and uses that as the blobid.
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
    blobIdCtr, \* Counter to represent blobid. When a new blob has to be Put, this counter will be used as the blob's blobid.
    inflightReplicationMessages, \* Inflight replication messages
    inflightReplicationRequest, \* Inflight request by a source replica to get next set of replication data from target replica.
    inflightReplicationResponse, \* Inflight response to replication sent by a replica to the replication requester.
    orderedStoredMessagesPerReplica, \* A per replica array where each array element is a set of messages in the replica, each message is a record like [ blobid |-> message.blobid, blobmessage |-> PUT, logoffset |-> offset ]
    replicaTokens, \* this is a 2d array. For each replica r, it stores an array representing the next offset token that replica r needs to fetch from each of the other replicas.
    replicaOffsets \* Represents the position at which next message will be written in a replica. This is stored in each message in the replica and gives the concept of order to the replica.


vars == <<replicaStates,
    blobIdCtr,
    inflightReplicationMessages,
    inflightReplicationRequest,
    inflightReplicationResponse, 
    orderedStoredMessagesPerReplica,
    replicaTokens,
    replicaOffsets>>

BlobCountConstraint ==
    /\ blobIdCtr < NumBlobs

(* Replica storage record for a PUT message *)
PutRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> PUT, logoffset |-> offset ]

(* Replica storage record for a DELETE message *)
DeleteRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> DELETE, logoffset |-> offset  ]

(* Replica storage record for a UPDATE TTL message *)
UpdateTtlRecord(blobId, offset) ==
    [ blobid |-> blobId, blobmessage |-> UPDATE_TTL, logoffset |-> offset  ]

(* Check if replica with the specified replica id has Put Message for the specified blobid *)
ReplicaHasPutMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = PUT

(* Check if replica with the specified replica id has DELETE Message for the specified blobid *)
ReplicaHasDeleteMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = DELETE

(* Check if replica with the specified replica id has UPDATE TTL Message for the specified blobid *)
ReplicaHasUpdateTtlMessage(blobid, replicaid, orderedMessagesPerReplica) ==
    \E msg \in orderedMessagesPerReplica[replicaid]:
        /\ msg.blobid = blobid
        /\ msg.blobmessage = UPDATE_TTL

(* Check if the replica with the specified replicaid can take PUT for the specified blobid.
   In order to be able to take PUTs, replica needs to be writable and shouldn't already have the PUT message in its log *)
ReplicaCanTakePut(blobid, replicaid, orderedMessagesPerReplica, replicaStates1) ==
    /\ replicaStates1[replicaid] = CanTakeWrite
    \* /\ ~ReplicaHasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

(* Check if the replica with the specified replicaid can take Update Ttl for the specified blobid.
   In order to be able to take Update Ttl, replica needs to be writable, should have a PUT message for the blobid,
      and shouldn't already have an update ttl or delete message for the blob in its log *)
ReplicaCanTakeTtlUpdate(blobid, replicaid, orderedMessagesPerReplica, replicaStates1) ==
    /\ replicaStates1[replicaid] = CanTakeWrite
    /\ ReplicaHasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    /\ ~ReplicaHasDeleteMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    \* /\ ~ReplicaHasUpdateTtlMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

(* Check if the replica with the specified replicaid can take Delete for the specified blobid.
   In order to be able to take Delete, replica needs to be writable, should have a PUT message for the blobid,
      and shouldn't already have a delete message for the blob in its log *)
ReplicaCanTakeDelete(blobid, replicaid, orderedMessagesPerReplica, replicaStates1) ==
    /\ replicaStates1[replicaid] = CanTakeWrite
    /\ ReplicaHasPutMessage(blobid, replicaid, orderedStoredMessagesPerReplica)
    \* /\ ~ReplicaHasDeleteMessage(blobid, replicaid, orderedStoredMessagesPerReplica)

ReplicationRequestMessage(sourceReplica, replicaToken) ==
    [ src |-> sourceReplica, token |-> replicaToken ]

ReplicaRecordAtOffset(replicaid, orderedMessagesPerReplica, offset) ==
    IF orderedMessagesPerReplica[replicaid] # {} THEN 
        {msg \in orderedMessagesPerReplica[replicaid]: msg.logoffset = offset}
    ELSE {}

ReplicationResponseMessage(replicaid, replicaStoredMessages, msg) ==
    {[r |-> replicaid, messages |-> ReplicaRecordAtOffset(replicaid, replicaStoredMessages, msg.token)]}

TypeOK ==
    /\ DOMAIN replicaStates \subseteq Replicas
    /\ DOMAIN inflightReplicationMessages \subseteq Replicas
    /\ DOMAIN orderedStoredMessagesPerReplica \subseteq Replicas
    /\ DOMAIN inflightReplicationRequest \subseteq Replicas
    /\ DOMAIN inflightReplicationResponse \subseteq Replicas
    /\ DOMAIN replicaTokens \subseteq Replicas
    /\ DOMAIN replicaOffsets \subseteq Replicas
    /\ blobIdCtr <= NumBlobs + 1

Init ==
    /\ orderedStoredMessagesPerReplica = [ r \in Replicas |-> {} ]
    /\ inflightReplicationMessages = [ r \in Replicas |-> {} ]
    /\ inflightReplicationRequest = [ r \in Replicas |-> {} ]
    /\ inflightReplicationResponse = [ r \in Replicas |-> {} ]
    /\ replicaStates = [ r \in Replicas |-> CanTakeWrite ]
    /\ blobIdCtr = 0
    /\ replicaTokens = [r \in Replicas |-> [ rr \in Replicas |-> 0 ] ]
    /\ replicaOffsets = [r \in Replicas |-> 0 ]

(* If each blob has seen PUTs, updateTtl and Delete then we can assume that all user operations have ended. *)
AllBlobOpsDone == 
    /\ blobIdCtr = NumBlobs

(* Take down the replica with the replica id r. *)
ReplicaDown(r) ==
    /\ replicaStates' = [replicaStates EXCEPT ![r] = CannotTakeWrite]
    /\ UNCHANGED <<blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, orderedStoredMessagesPerReplica, replicaTokens, replicaOffsets>>

(* Bring up a replica with the replica id r . *)
ReplicaUp(r) ==
    /\ replicaStates' = [replicaStates EXCEPT ![r] = CanTakeWrite]
    /\ UNCHANGED <<blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, orderedStoredMessagesPerReplica, replicaTokens, replicaOffsets>>

(* Recieve request to put a blob.
 *)
RecvPut ==
    /\ blobIdCtr <= NumBlobs \* To Remove
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakePut(blobIdCtr, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasPutMessage(blobIdCtr, r, orderedStoredMessagesPerReplica)) THEN
                orderedStoredMessagesPerReplica[r] \union { PutRecord(blobIdCtr, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakePut(blobIdCtr, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasPutMessage(blobIdCtr, r, orderedStoredMessagesPerReplica)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
    /\ blobIdCtr' = blobIdCtr + 1
    /\ blobIdCtr < NumBlobs
    /\ UNCHANGED <<replicaStates, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, replicaTokens>>


(* Recieve request to delete a blob.
 *)
RecvDelete(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ ReplicaCanTakeDelete(blobId, r1, orderedStoredMessagesPerReplica, replicaStates)
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeDelete(blobId, r, orderedStoredMessagesPerReplica, replicaStates) /\  ~ReplicaHasDeleteMessage(blobId, r, orderedStoredMessagesPerReplica)) THEN
                orderedStoredMessagesPerReplica[r] \union { DeleteRecord(blobId, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeDelete(blobId, r, orderedStoredMessagesPerReplica, replicaStates) /\  ~ReplicaHasDeleteMessage(blobId, r, orderedStoredMessagesPerReplica)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, replicaTokens>>


(* Recieve request to make a blob permanent.
 *)
RecvUpdateTtl(blobId) ==
    /\ \E r1, r2 \in Replicas:
        /\ r1 # r2
        /\ ReplicaCanTakeTtlUpdate(blobId, r1, orderedStoredMessagesPerReplica, replicaStates)
        /\ orderedStoredMessagesPerReplica' = [r \in DOMAIN orderedStoredMessagesPerReplica |-> 
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeTtlUpdate(blobId, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasUpdateTtlMessage(blobId, r, orderedStoredMessagesPerReplica)) THEN
                orderedStoredMessagesPerReplica[r] \union { UpdateTtlRecord(blobId, replicaOffsets[r]) }
            ELSE
                orderedStoredMessagesPerReplica[r]
            ]
        /\ replicaOffsets' = [ r \in DOMAIN replicaOffsets |->
            IF (((r = r1) \/ (r = r2)) /\ ReplicaCanTakeTtlUpdate(blobId, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasUpdateTtlMessage(blobId, r, orderedStoredMessagesPerReplica)) THEN 
                replicaOffsets[r] + 1
            ELSE 
                replicaOffsets[r]
            ]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest, inflightReplicationResponse, replicaTokens>>


(* Ambry uses a pull model for replication.
 * In SendReplicationRequest action, a replica asks one of its peers to give the set of data the peer has.
 * This action just enqueues the request to a peer in "inflightReplicationRequest".
 * The request contains a replicaToken, which is the next offset of the target replica that target replica needs to send as a response.
 *)
SendReplicationRequest(src) ==
    /\ replicaStates[src] = CanTakeWrite \* We want replica asking for the replication pull to be writable.
    /\ \E tgt \in Replicas:
        /\ src # tgt
        /\ orderedStoredMessagesPerReplica[tgt] # {}
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![tgt] = inflightReplicationRequest[tgt] \union { ReplicationRequestMessage(src, replicaTokens[src][tgt]) } ]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, inflightReplicationResponse, replicaTokens, orderedStoredMessagesPerReplica, replicaOffsets>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationRequest action, a replica recieves replication request from a peer.
 * The request contains a replica token, which is the offset of the message upto which the peer is uptodate.
 * The recieving replica checks if it has message after the offset in the replica token, and sends the message along with the new token.
 *)
RecvReplicationRequest(r) ==
    /\ inflightReplicationRequest[r] # {}
    /\ orderedStoredMessagesPerReplica[r] # {} \* there should be something to replicate.
    /\ \E msg \in inflightReplicationRequest[r]:
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![msg.src] = inflightReplicationResponse[msg.src] \union ReplicationResponseMessage(r, orderedStoredMessagesPerReplica, msg) ]
        /\ inflightReplicationRequest' = [inflightReplicationRequest EXCEPT ![r] = inflightReplicationRequest[r] \ {msg}]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, orderedStoredMessagesPerReplica, replicaOffsets, replicaTokens>>

(* Ambry uses a pull model for replication.
 * In RecvReplicationResponse action, a replica recieves replication response from a peer.
 * On reciept it checks if each message is present in its local storage log. If not present, then it adds the message, and updates its replica token.
 *)
RecvReplicationResponse(r) ==
    /\ inflightReplicationResponse[r] # {}
    /\ \E msg \in inflightReplicationResponse[r]:
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ orderedStoredMessagesPerReplica' = [rr \in DOMAIN orderedStoredMessagesPerReplica |-> 
                    IF ((rr = r) /\ ReplicaCanTakeTtlUpdate(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasUpdateTtlMessage(message.blobid, rr, orderedStoredMessagesPerReplica)) THEN
                        orderedStoredMessagesPerReplica[rr] \union { UpdateTtlRecord(message.blobid, replicaOffsets[rr]) }
                    ELSE
                        orderedStoredMessagesPerReplica[rr]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ orderedStoredMessagesPerReplica' = [ orderedStoredMessagesPerReplica EXCEPT ![r] = 
                        IF (ReplicaCanTakePut(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasPutMessage(message.blobid, r, orderedStoredMessagesPerReplica)) THEN
                            orderedStoredMessagesPerReplica[r] \union { PutRecord(message.blobid, replicaOffsets[r]) }
                        ELSE 
                            orderedStoredMessagesPerReplica[r] ]
                ELSE
                    /\ orderedStoredMessagesPerReplica' = [rr \in DOMAIN orderedStoredMessagesPerReplica |-> 
                        IF ((rr = r) /\ ReplicaCanTakeDelete(message.blobid, rr, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasDeleteMessage(message.blobid, r, orderedStoredMessagesPerReplica)) THEN
                            orderedStoredMessagesPerReplica[r] \union { DeleteRecord(message.blobid, replicaOffsets[rr]) }
                        ELSE
                            orderedStoredMessagesPerReplica[rr]
                        ]
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                    IF (ReplicaCanTakeTtlUpdate(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates) /\ ~ReplicaHasUpdateTtlMessage(message.blobid, r, orderedStoredMessagesPerReplica)) THEN
                        replicaOffsets[r] + 1
                    ELSE
                        replicaOffsets[r]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                        IF (ReplicaCanTakePut(message.blobid, r, replicaOffsets, replicaStates) /\ ~ReplicaHasPutMessage(message.blobid, r, orderedStoredMessagesPerReplica)) THEN
                            replicaOffsets[r] + 1
                        ELSE 
                            replicaOffsets[r]
                        ]
                ELSE
                    /\ replicaOffsets' = [ replicaOffsets EXCEPT ![r] = 
                        IF (ReplicaCanTakeDelete(message.blobid, r, replicaOffsets, replicaStates) /\ ~ReplicaHasDeleteMessage(message.blobid, r, orderedStoredMessagesPerReplica)) THEN
                            replicaOffsets[r] + 1
                        ELSE
                            replicaOffsets[r]
                        ]
        /\ \E message \in msg.messages:
            /\ IF message.blobmessage = UPDATE_TTL THEN
                /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                    IF (ReplicaCanTakeTtlUpdate(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                        message.logoffset + 1
                    ELSE
                        replicaTokens[r][msg.r]
                    ]
                ELSE IF message.blobmessage = PUT THEN
                    /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                        IF (ReplicaCanTakePut(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                            message.logoffset + 1
                        ELSE
                            replicaTokens[r][msg.r]
                        ]
                ELSE
                    /\ replicaTokens' = [ replicaTokens EXCEPT ![r][msg.r] =
                        IF (ReplicaCanTakeDelete(message.blobid, r, orderedStoredMessagesPerReplica, replicaStates)) THEN
                            message.logoffset + 1
                        ELSE
                            replicaTokens[r][msg.r]
                        ]
        /\ inflightReplicationResponse' = [inflightReplicationResponse EXCEPT ![r] = inflightReplicationResponse[r] \ {msg}]
    /\ UNCHANGED <<replicaStates, blobIdCtr, inflightReplicationMessages, inflightReplicationRequest>>

Next ==
    \/ RecvPut
    \/ \E blobid \in BlobIds:
       \/ RecvUpdateTtl(blobid)
    \* \/ \E blobid \in BlobIds:
    \*     \/ RecvDelete(blobid)
    \/ \E r \in Replicas:
       \/ SendReplicationRequest(r)
    \/ \E r \in Replicas:
        \/ RecvReplicationRequest(r)
    \/ \E r \in Replicas:
        \/ RecvReplicationResponse(r)
    \* \/ \E r \in Replicas:
    \*     \/ ReplicaUp(r)
    \* \/ \E r \in Replicas:
    \*    \/ ReplicaDown(r)


Spec ==
    Init /\ [] [Next]_vars

==================================================================================================================

