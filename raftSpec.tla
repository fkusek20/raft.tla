------------------------------ MODULE raftSpec ------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further to track message counts for entry commitment.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS raftActionsSolution

\* Receive a message. (Handles messages intended FOR Raft servers)
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN /\ i \in Servers \* Receiver must be a Raft Server
       /\ ( \* Standard Raft message handling
            \/ UpdateTerm(i, j, m)
            \/ /\ m.mtype = RequestVoteRequest
               /\ HandleRequestVoteRequest(i, j, m)
            \/ /\ m.mtype = RequestVoteResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleRequestVoteResponse(i, j, m)
            \/ /\ m.mtype = AppendEntriesRequest
               /\ HandleAppendEntriesRequest(i, j, m) \* HovercRaft logic inside
            \/ /\ m.mtype = AppendEntriesResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleAppendEntriesResponse(i, j, m)
          )

\* Defines how the variables may transition for the full HovercRaft model.
Next ==
       \* --- Standard Raft Leader Election and Timeouts (for Raft Servers) ---
       \/ \E srv \in Servers : Timeout(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ RequestVote(srv1, srv2)
       \/ \E srv \in Servers : BecomeLeader(srv)

       \* --- HovercRaft Specific Actions ---
       \/ \E ldr \in Servers, v \in Value :             \* Client sends to system, Leader informs Switch
           state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)

       \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer : \* Switch replicates payload to a Raft server
           SwitchClientRequestReplicate(switchIndex, raftSrv, v)

       \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :      \* Leader ingests metadata from Switch's knowledge
           state[ldr] = Leader /\ LeaderIngestHovercRaftRequest(ldr, v)

       \* --- Standard Raft Log Replication and Commit (for Raft Servers) ---
       \/ \E srv \in Servers : AdvanceCommitIndex(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ AppendEntries(srv1, srv2) \* Sends metadata

       \* --- Handling Raft RPC Messages (for Raft Servers) ---
       \/ \E m \in {msg \in ValidMessage(messages) :
                msg.mdest \in Servers /\ \* Ensure Raft servers are destinations for Raft messages
                msg.mtype \in {RequestVoteRequest, RequestVoteResponse,
                               AppendEntriesRequest, AppendEntriesResponse}} :
           Receive(m) \* Receive action already filters for msg.mdest \in Servers

       \* --- Optional: Network Unreliability (for Raft messages) ---
       \* \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype = AppendEntriesRequest } : DuplicateMessage(m)
       \* \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype = RequestVoteRequest } : DropMessage(m)

\* Next-state relation for testing HovercRaft actions without leader election
MySwitchNext ==
   \/ \E ldr \in Servers, v \in Value :
       state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)
   \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer :
       SwitchClientRequestReplicate(switchIndex, raftSrv, v)
   \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :
       state[ldr] = Leader /\ LeaderIngestHovercRaftRequest(ldr, v)
   \/ \E srv \in Servers : AdvanceCommitIndex(srv)
   \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ AppendEntries(srv1, srv2)
   \/ \E m \in {msg \in ValidMessage(messages) :
            msg.mdest \in Servers /\ \* Ensure Raft servers are destinations for Raft messages
            msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} :
       Receive(m)

\* The main specification using the full Next definition
Spec == Init /\ [][Next]_vars

\* Specification for testing HovercRaft mechanics starting from Init
MyHovercRaftSpec == Init /\ [][MySwitchNext]_vars

MySwitchSpec == MyInit /\ [][MySwitchNext]_vars

MySpec == MyNewInit /\ [][MySwitchNext]_vars 

\* Specification for testing HovercRaft mechanics starting from Professor's state
\* ProfInit == (* ... define the professor's initial state here in raftInit.tla ... *)
\* ProfHovercRaftSpec == ProfInit /\ [][MySwitchNext]_vars

\* -------------------- Invariants --------------------

\* Fake invariant to check HovercRaft payload replication progress
\* Becomes FALSE when all Raft servers have buffered all payloads.


AllServersHaveOneUnorderedRequestInv ==

    \E s \in Servers :  Cardinality(unorderedRequests[s]) /= 2
    
NoRaftServerHasCommittedYet ==
    \A srv \in Servers : commitIndex[srv] = 0

\* Fake invariant to check Raft commit progress
\* Becomes FALSE when the first commit occurs (commitIndex > 0).


\* ---- Standard Raft Safety Invariants (Scoped to Raft Servers) ----



MoreThanOneLeaderInv ==
    \A i,j \in Servers :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

LogMatchingInv ==
    \A i, j \in Servers : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

LeaderCompletenessInv ==
    \A i \in Servers :
        state[i] = Leader =>
        \A j \in Servers : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])

LogInv ==
    \A i, j \in Servers :
        \/ CheckIsPrefix(Committed(i),Committed(j))
        \/ CheckIsPrefix(Committed(j),Committed(i))

THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv)

=============================================================================
\* Created by Ovidiu-Cristian Marcu
