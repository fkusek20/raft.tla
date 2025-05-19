---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit, Sequences

----
\* Define state transitions

\* Server i restarts from stable storage. (Assuming Restart is only for Raft Servers)
Restart(i) ==
    /\ i \in Servers
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, hovercraftVars>>

\* Server i times out and starts a new election. (Only Raft Servers timeout)
Timeout(i) ==
    /\ i \in Servers
    /\ state[i] \in {Follower, Candidate}
    /\ currentTerm[i] < MaxTerm
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* Candidate i sends j a RequestVote request. (Only between Raft Servers)
RequestVote(i, j) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* Leader i sends j an AppendEntries request containing exactly 1 METADATA entry.
AppendEntries(i, j) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET entryIndex == nextIndex[i][j]
           metaEntry == log[i][entryIndex]      \* Contains [term |-> t, value |-> v_id]
           entries == << metaEntry >>
           entryKey == <<entryIndex, metaEntry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,      \* Sends METADATA only
                mlog           |-> log[i],       \* History variable for proofs
                mcommitIndex   |-> Min({commitIndex[i], entryIndex - 1}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' = \* Modifies sentCount
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    \* serverVars, candidateVars, leaderVars (nextIndex, matchIndex), logVars (log, commitIndex)
    \* are potentially part of broader tuples.
    \* maxc, leaderCount are part of instrumentationVars but not changed here.
    \* hovercraftVars are not changed.
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, log, commitIndex, maxc, leaderCount, hovercraftVars>>

\* Candidate i transitions to leader. (Only Raft Servers become leader)
BecomeLeader(i) ==
    /\ i \in Servers
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [k \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [k \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, hovercraftVars>>

\* Action 1: Client request arrives at the system, processed by Leader, informs Switch
SwitchClientRequest(sw, ldr, v) ==
    /\ sw = switchIndex             \* Ensure sw is the actual switch
    /\ ldr \in Servers             \* Ensure ldr is a Raft server
    /\ state[ldr] = Leader         \* Ensure ldr is the current Raft leader
    /\ v \in Value
    /\ maxc < MaxClientRequests
    /\ v \notin DOMAIN switchBuffer  \* Only process new requests
    /\ LET leaderTerm == currentTerm[ldr]
           entry == [term    |-> leaderTerm,
                     value   |-> v,
                     payload |-> v] \* Payload is the value itself
       IN /\ switchBuffer' = switchBuffer @@ (v :> entry)
          /\ maxc' = maxc + 1
          \* The switch itself can "receive" the request ID into its buffer immediately
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![sw] = unorderedRequests[sw] \union {v}]
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, logVars,
                    commitIndex, leaderCount, entryCommitStats, switchSentRecord >>

\* Action 2: Switch replicates a payloaded request to a Raft server's buffer
SwitchClientRequestReplicate(sw, raftSrv, val) ==
    /\ sw = switchIndex                \* sw is the switch
    /\ raftSrv \in Servers             \* raftSrv is a Raft consensus server
    /\ val \in DOMAIN switchBuffer     \* val is a known request ID in the switch's buffer
    /\ LET entryToReplicate == switchBuffer[val]
           termOfEntry == entryToReplicate.term
           pairToRecord == <<val, termOfEntry>>
       IN \* Only replicate if not already sent for this term
          /\ pairToRecord \notin switchSentRecord[raftSrv]
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![raftSrv] = unorderedRequests[raftSrv] \union {val}]
          /\ switchSentRecord' = [switchSentRecord EXCEPT ![raftSrv] = switchSentRecord[raftSrv] \union {pairToRecord}]
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, logVars,
                    commitIndex, maxc, leaderCount, entryCommitStats, switchBuffer >>

\* Action 3: Leader ingests a request ID (for which payload is assumed replicated) into its own log
LeaderIngestHovercRaftRequest(ldr, val) ==
    /\ ldr \in Servers
    /\ state[ldr] = Leader
    /\ val \in DOMAIN switchBuffer      \* The leader must know of this value from the switchBuffer
    /\ val \in unorderedRequests[ldr] \* NEW: Leader must have it buffered
    /\ LET leaderTerm == currentTerm[ldr]
           metaEntry == [term |-> leaderTerm, value |-> val]
           valueAlreadyExists == \E idx \in 1..Len(log[ldr]) : log[ldr][idx].value = val
           isNewToLeaderLog == ~valueAlreadyExists
       IN /\ isNewToLeaderLog
          /\ LET newLeaderLog == Append(log[ldr], metaEntry)
                 newEntryIndex == Len(log[ldr]) + 1
                 newEntryKey == <<newEntryIndex, leaderTerm>>
             IN /\ log' = [log EXCEPT ![ldr] = newLeaderLog]
                /\ unorderedRequests' = [unorderedRequests EXCEPT ![ldr] = unorderedRequests[ldr] \ {val}]
                /\ entryCommitStats' =
                      IF newEntryIndex > 0
                      THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
                      ELSE entryCommitStats
                \* maxc was already updated by SwitchClientRequest, so it's unchanged here.
                \* commitIndex is not changed by this action directly.
          /\ UNCHANGED << messages, serverVars, candidateVars, matchIndex, nextIndex,
                          commitIndex, leaderCount, maxc, switchBuffer, switchSentRecord >>

\* Leader i advances its commitIndex. (Only Raft server leaders)
AdvanceCommitIndex(i) ==
    /\ i \in Servers
    /\ state[i] = Leader
    /\ LET Agree(index) == {i} \cup {k \in Servers : matchIndex[i][k] >= index}
           agreeIndexes == {index \in 1..Len(log[i]) :
                                /\ Agree(index) \in Quorum
                                /\ log[i][index].term = currentTerm[i]}
           newCommitIndex == IF agreeIndexes /= {} THEN Max(agreeIndexes) ELSE commitIndex[i]
           committedIndexes == { k \in Nat : k > commitIndex[i] /\ k <= newCommitIndex }
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ entryCommitStats' = \* Modifies committed flag
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ]
                   ELSE entryCommitStats[key] ]
    \* serverVars, candidateVars, leaderVars (nextIndex, matchIndex), log
    \* maxc, leaderCount are part of instrumentationVars but not changed here.
    \* hovercraftVars are not changed.
    /\ UNCHANGED <<messages, serverVars, candidateVars, nextIndex, matchIndex, log, maxc, leaderCount, hovercraftVars>>

----
\* Message handlers
\* i = recipient, j = sender (should be Raft servers for Raft messages)

\* Server i receives a RequestVote request from server j.
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ i \in Servers             \* Check receiver is Raft server
       /\ j \in Servers             \* Check sender is Raft server
       /\ m.mterm <= currentTerm[i]  \* Check term
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j] \* Grant vote branch
          \/ ~grant /\ UNCHANGED votedFor                       \* Deny vote branch
       /\ Reply([mtype        |-> RequestVoteResponse,         \* Send reply
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog         |-> log[i], \* History variable
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>
\* Server i receives a RequestVote response from server j.
HandleRequestVoteResponse(i, j, m) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* Server i receives an AppendEntries request from server j.
HandleAppendEntriesRequest(i, j, m) == \* i is follower, j is leader
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

        payloadRequirementMet ==
            \/ m.mentries = << >> \* Always okay if it's just a heartbeat (no entries)
            \/ LET receivedValue == m.mentries[1].value \* Get the ID from the leader's metadata entry
               IN receivedValue \in unorderedRequests[i]  \* Check if this ID is in the follower's buffer

    IN /\ m.mterm <= currentTerm[i]
       /\ i \in Servers             \* Follower 'i' must be a Raft consensus server
       /\ j \in Servers             \* Leader 'j' must be a Raft consensus server

       /\ \/ /\ \* BRANCH 1: REJECT REQUEST
                \/ m.mterm < currentTerm[i] \* Stale term
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \/ ~logOk  \* Raft log consistency failed
                      \/ (m.mentries /= << >> /\ ~payloadRequirementMet) \* OR, entries present but payload requirement not met
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0, \* Or perhaps commitIndex[i] for better leader hints
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, unorderedRequests>>

          \/ \* BRANCH 2: RETURN TO FOLLOWER STATE (Standard Raft logic)
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, unorderedRequests>>

          \/ \* BRANCH 3: ACCEPT REQUEST
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk                     \* Raft log consistency met
             /\ payloadRequirementMet     \* AND payload requirement met
             /\ LET index == m.mprevLogIndex + 1
                     newCommitIndex == Min({ m.mcommitIndex, m.mprevLogIndex + Len(m.mentries) })

                IN \/ \* SUB-BRANCH 3.1: ALREADY DONE / LOG MATCHES
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                             /\ log[i][index].value = m.mentries[1].value \* Match term and value (ID)
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>

                   \/ \* SUB-BRANCH 3.2: CONFLICT - REMOVE ENTRIES (Standard Raft logic, but reply FALSE)
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term \* Term mismatch
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> FALSE,
                                 mmatchIndex     |-> commitIndex[i], \* Hint to leader
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, commitIndex, unorderedRequests>>

                   \/ \* SUB-BRANCH 3.3: NO CONFLICT - APPEND ENTRY
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex \* Ready to append at the end
                       /\ LET entryToAppend == m.mentries[1]
                              appendedValue == entryToAppend.value \* This is the ID (e.g., "v1")
                          IN log' = [log EXCEPT ![i] = Append(log[i], entryToAppend)]
                             /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = unorderedRequests[i] \ {appendedValue}]
                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                             /\ Reply([mtype           |-> AppendEntriesResponse,
                                       mterm           |-> currentTerm[i],
                                       msuccess        |-> TRUE,
                                       mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                       msource         |-> i,
                                       mdest           |-> j],
                                       m)
                             /\ UNCHANGED <<serverVars>> \* serverVars includes state, currentTerm, votedFor

       \* Note: switchIndex is CONSTANT, hovercraftVars includes switchBuffer, unorderedRequests, switchSentRecord
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchBuffer, switchSentRecord>>

\* Server i receives an AppendEntries response from server j.
HandleAppendEntriesResponse(i, j, m) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET newMatchIndex == Max({matchIndex[i][j], m.mmatchIndex})
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>>
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' = \* Modifies ackCount
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>> \* If not successful, matchIndex and entryCommitStats don't change due to this branch.
    /\ Discard(m)
    \* serverVars, candidateVars, logVars (log, commitIndex)
    \* maxc, leaderCount are part of instrumentationVars but not changed here.
    \* hovercraftVars are not changed.
    /\ UNCHANGED <<serverVars, candidateVars, log, commitIndex, maxc, leaderCount, hovercraftVars>>

\* Any RPC with a newer term causes the recipient to advance its term first. (Applies only to Raft Servers)
UpdateTerm(i, j, m) ==
    /\ i \in Servers
    /\ j \in Server \* Sender can be Switch potentially, but recipient must be Raft server
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* Responses with stale terms are ignored. (Applies only to Raft Servers)
DropStaleResponse(i, j, m) ==
    /\ i \in Servers
    /\ j \in Server
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* Network state transitions (Optional - Keep if needed for modeling)
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

=============================================================================
Use code with caution.
Tla
File 2: raftSpec.tla (Complete & Fixed)
------------------------------ MODULE raftSpec ------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\* Modified for HovercRaft design based on professor's instructions.

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

\* Specification for testing HovercRaft mechanics starting from Professor's state
\* ProfInit == (* ... define the professor's initial state here in raftInit.tla ... *)
\* ProfHovercRaftSpec == ProfInit /\ [][MySwitchNext]_vars

\* -------------------- Invariants --------------------

\* Fake invariant to check HovercRaft payload replication progress
\* Becomes FALSE when all Raft servers have buffered all payloads.
AllServersHaveOneUnorderedRequestInv ==
    \E s \in Servers : Cardinality(unorderedRequests[s]) /= Cardinality(Value)

\* Fake invariant to check Raft commit progress
\* Becomes FALSE when the first commit occurs (commitIndex > 0).
NoRaftServerHasCommittedYet ==
    \A srv \in Servers : commitIndex[srv] = 0

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
Use code with caution.
Tla
Key Changes Made Summary:
raftActionsSolution.tla: Added hovercraftVars to the UNCHANGED clause of all standard Raft actions (Restart, Timeout, RequestVote, AppendEntries, BecomeLeader, AdvanceCommitIndex, HandleRequestVote*, HandleAppendEntriesResponse, UpdateTerm, Drop*, Duplicate*). Cleaned up the final UNCHANGED clause in HandleAppendEntriesRequest. Added scoping (\in Servers) where appropriate to actions that should only involve Raft consensus members.
raftSpec.tla: Defined a comprehensive Next operator including both Raft leader election (scoped to Servers) and the HovercRaft actions. Defined Spec using this Next. Kept MySwitchNext and MyHovercRaftSpec for focused testing. Correctly scoped the standard Raft safety invariants to use Servers. Added the NoRaftServerHasCommittedYet invariant. Cleaned up comments and structure.
This should provide a complete and corrected version based on the professor's design and fixing the UNCHANGED errors.
=============================================================================