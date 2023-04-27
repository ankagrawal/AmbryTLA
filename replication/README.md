# AmbryReplication

TLA+ Specification for Ambry's Replication

## ISSUES IN THE MODEL:
1. The sucess target of put, delete and update-ttl operations is not configurable *)
2. Replication replicates everything in each iteration. It should rather replicate only those blobs that need replication *)
3. Stored messages per replica don't have ordering. Hence replication is also not ordered. *)
4. No concept of replica token. *)
5. All the messages are replicated in one shot. *)

## TODO:
1. TEST EVENTUALLY CONSISTENT AND REMAINS EVENTUALLY CONSISTENT
2. FIX THE CODESPACE SETUP
3. MAKE THE REPLICA STORED MESSAGES AN ORDERED LOG
4. MAKE REPLICATION HAPPEN VIA A REPLICATOKEN SO THAT ONLY NEW MESSAGES ARE REPLICATED
