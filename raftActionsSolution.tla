---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars>>

\* Server i times out and starts a new election. (Should exclude switchIndex in Next)
Timeout(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ currentTerm[i] < MaxTerm
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    \* Most implementations would probably just set the local vote
    \* atomically, but messaging localhost for it is weaker.
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars>>

\* Candidate i sends j a RequestVote request. (Should exclude switchIndex in Next)
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Leader i sends j an AppendEntries request containing exactly 1 entry.
\* Note: This sends standard [term, value] entries from the leader's log.
\* The leader's log is NOT YET being updated via the Switch mechanism.
\* (Should exclude switchIndex in Next)
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex]      \* Expects [term |-> t, value |-> v]
           entries == << entry >>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,      \* Contains standard entry
                mlog           |-> log[i],       \* History variable
                mcommitIndex   |-> Min({commitIndex[i], entryIndex - 1}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Candidate i transitions to leader. (Should exclude switchIndex in Next)
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats>>

\* Simulates client sending value v to the Switch server
\* THIS IS THE NEW ACTION ADDED AS PER PROFESSOR'S INSTRUCTIONS
SwitchClientRequest(v) ==
    /\ v \in Value                  \* Ensure v is a valid client value/payload
    /\ maxc < MaxClientRequests     \* Ensure we don't exceed the limit
    /\ LET entryTerm == 0           \* Switch doesn't use Raft terms, use placeholder 0
           newValue == v            \* The 'value' field acts as the reference/ID
           newPayload == v          \* The 'payload' field holds the actual data
           \* The entry stored by the Switch, including the payload
           entry == [term    |-> entryTerm,
                     value   |-> newValue,
                     payload |-> newPayload]
           newSwitchLog == Append(log[switchIndex], entry)
       IN /\ log' = [log EXCEPT ![switchIndex] = newSwitchLog] \* Update only the Switch's log
          /\ maxc' = maxc + 1
    \* Assume this action doesn't change the state of the actual Raft servers (r1, r2, r3...)
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, commitIndex,
                    nextIndex, matchIndex, leaderCount, entryCommitStats >>
                    \* Note: log is changed only at switchIndex by this action

\* Leader i advances its commitIndex. (Should exclude switchIndex in Next)
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET Agree(index) == {i} \cup {k \in Server : matchIndex[i][k] >= index}
           agreeIndexes == {index \in 1..Len(log[i]) :
                                /\ Agree(index) \in Quorum
                                /\ log[i][index].term = currentTerm[i]}
           newCommitIndex == IF agreeIndexes /= {} THEN Max(agreeIndexes) ELSE commitIndex[i]
           committedIndexes == { k \in Nat : k > commitIndex[i] /\ k <= newCommitIndex }
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ entryCommitStats' = [ key \in DOMAIN entryCommitStats |->
                                     IF key \in keysToUpdate
                                     THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ]
                                     ELSE entryCommitStats[key] ]
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount>>

----
\* Message handlers
\* i = recipient (should not be switchIndex), j = sender (should not be switchIndex), m = message

\* Server i receives a RequestVote request from server j.
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog         |-> log[i], \* History variable
                 msource      |-> i,
                 mdest        |-> j],
                 m)
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Server i receives a RequestVote response from server j.
HandleRequestVoteResponse(i, j, m) ==
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
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars>>

\* Server i receives an AppendEntries request from server j.
\* Note: Reverted to handle standard [term, value] entries. No buffer check.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ ~logOk  \* Reverted: Only reject if log doesn't match
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                     newCommitIndex == Min({ m.mcommitIndex, m.mprevLogIndex + Len(m.mentries) })
                IN \/ \* already done with request / log matches
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term \* Just check term
                             \* Optional: Check value too if needed: /\ log[i][index].value = m.mentries[1].value
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log>>
                   \/ \* conflict: remove entries
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog]
                       \* Must reply on conflict to trigger retry
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> FALSE,
                                 mmatchIndex     |-> commitIndex[i],
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, commitIndex>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entryToAppend == m.mentries[1]
                          IN log' = [log EXCEPT ![i] = Append(log[i], entryToAppend)]
                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                             /\ Reply([mtype           |-> AppendEntriesResponse,
                                       mterm           |-> currentTerm[i],
                                       msuccess        |-> TRUE,
                                       mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                       msource         |-> i,
                                       mdest           |-> j],
                                       m)
                             /\ UNCHANGED <<serverVars>>
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars>>

\* Server i receives an AppendEntries response from server j.
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET newMatchIndex == Max({matchIndex[i][j], m.mmatchIndex}) \* Keep Max logic
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>>
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<serverVars, candidateVars, logVars, instrumentationVars>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    \* Note: Removed buffer, payloadMap from UNCHANGED
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Network state transitions (Optional - Keep if needed for modeling)
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

=============================================================================