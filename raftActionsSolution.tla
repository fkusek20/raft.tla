---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit

----
\* Define state transitions

\* Modified to allow Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars elections, maxc, leaderCount, entryCommitStats
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, buffer, payloadMap>>

\* Modified to restrict Timeout to just Followers
\* Server i times out and starts a new election. Follower -> Candidate
Timeout(i) == /\ state[i] \in {Follower} \*, Candidate
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars. buffer, payloadMap>>

\* Modified to restrict Leader transitions, bounded by MaxBecomeLeader
\* Candidate i transitions to leader. Candidate -> Leader
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
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, buffer, payloadMap>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, buffer, payloadMap>>

\***************************** REQUEST VOTE **********************************************
\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, buffer, payloadMap>>

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
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
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars,  buffer, payloadMap>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
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
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars,  buffer, payloadMap>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars,  buffer, payloadMap>>

\***************************** AppendEntries **********************************************

\* Modified. Leader i receives a client request to add v to the log. up to MaxClientRequests.


\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry. It was up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i])  \* Ensure there are entries to send for this follower
    \* REMOVE/COMMENT OUT: /\ matchIndex[i][j] < nextIndex[i][j] (Can resend if needed)
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex] \* Entry is now [term |-> t, value |-> reqId]
           entries == << entry >>      \* Sending one entry containing the reqId
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,      \* This now contains the reqId entry
                mlog           |-> log[i],       \* History variable
                mcommitIndex   |-> Min({commitIndex[i], entryIndex - 1}), \* Commit up to previous index
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, buffer, payloadMap>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        \* ADD THIS CHECK: Check if payload for the first entry (if any) is available in the buffer
        payloadAvailable == \/ m.mentries = << >>
                            \/ LET entryReqId == m.mentries[1].value IN entryReqId \in buffer[i]
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \/ ~logOk
                      \/ (m.mentries /= << >> /\ ~payloadAvailable) \* MODIFY: Reject if payload missing!
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0, \* Leader will retry from earlier
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, buffer>> \* Buffer unchanged on reject
          \/ \* return to follower state (This part usually remains the same)
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, buffer>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ (m.mentries = << >> \/ payloadAvailable) \* MODIFY: Can only accept if payload IS available
             /\ LET index == m.mprevLogIndex + 1
                     newCommitIndex == Min({ m.mcommitIndex, m.mprevLogIndex + Len(m.mentries) }) \* Commit up to received entries
                IN \/ \* already done with request / log matches (entry contains reqId now)
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index] = m.mentries[1] \* Compare term and reqId
                       \* Advance commit index safely
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, buffer>> \* Buffer unchanged if entry already matches
                   \/ \* conflict: remove entries (This part usually remains similar, but reply FALSE)
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term \* Could also check reqId if needed, but term mismatch is primary
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog]
                       \* Reply FALSE so leader retries correctly
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> FALSE,
                                 mmatchIndex     |-> commitIndex[i], \* Tell leader where we are committed
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, commitIndex, buffer>> \* Buffer unchanged on conflict
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entryToAppend == m.mentries[1]
                              reqIdAppended == entryToAppend.value
                          IN log' = [log EXCEPT ![i] = Append(log[i], entryToAppend)]
                             \* ADD THIS LINE: Consume reqId from buffer after successful append!
                             /\ buffer' = [buffer EXCEPT ![i] = buffer[i] \ {reqIdAppended}]
                             \* Advance commit index safely
                             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                             /\ Reply([mtype           |-> AppendEntriesResponse,
                                       mterm           |-> currentTerm[i],
                                       msuccess        |-> TRUE,
                                       mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                       msource         |-> i,
                                       mdest           |-> j],
                                       m)
                             /\ UNCHANGED <<serverVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, payloadMap>>
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET newMatchIndex == m.mmatchIndex
                 \* Find the key for the *acknowledged* entry for stats
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>>
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                \* MODIFY: Use Max to prevent matchIndex going backwards
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({matchIndex[i][j], newMatchIndex})]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats
       \/ /\ \lnot m.msuccess \* not successful (likely due to log mismatch or missing payload on follower)
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})] \* Backtrack
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, buffer, payloadMap>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           \* Identify the keys in entryCommitStats corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          \* Update the 'committed' flag for the relevant entries in entryCommitStats
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record       
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount,  buffer, payloadMap>>





SwitchSend(payload_) ==
  /\ RequestID \ DOMAIN payloadMap # {}            \* make sure there is some free id
  /\ LET req == CHOOSE id \in (RequestID \ DOMAIN payloadMap) : TRUE IN
        \* Store payload mapped to the ID. Simplified structure here.
        /\ payloadMap' = payloadMap @@ (req :> [payload |-> payload_])
        \* Send message containing only the ID (payload is implicitly known via payloadMap)
        /\ Send([ mtype   |-> SwitchRequest,
                  reqId   |-> req
                  \* Optionally include payload if payloadMap isn't perfectly reliable:
                  \* , payload |-> payload_
                  ])
        /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, buffer>>

SwitchDeliver(s, msg) ==
  /\ msg.mtype = SwitchRequest
  /\ messages[msg] > 0
  /\ buffer'   = [buffer     EXCEPT ![s] = buffer[s] \union {msg.reqId}]
  /\ messages' = WithoutMessage(msg, messages) \* Consume the message for this server
  /\ UNCHANGED <<payloadMap, serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Leader proposes a request buffered via SwitchDeliver
LeaderProposeRequest(i) ==
    /\ state[i] = Leader
    /\ buffer[i] /= {}  \* There is a request buffered locally on the leader
    /\ maxc < MaxClientRequests
    /\ \E reqId \in buffer[i] : \* Choose one request ID from the buffer to propose
       /\ LET entry == [term |-> currentTerm[i], value |-> reqId] \* Log entry contains reqId IN THE VALUE FIELD
              newLog == Append(log[i], entry)
              newEntryIndex == Len(log[i]) + 1
              newEntryKey == <<newEntryIndex, currentTerm[i]>>
          IN log' = [log EXCEPT ![i] = newLog]
             /\ buffer' = [buffer EXCEPT ![i] = buffer[i] \ {reqId}] \* Consume the ID from leader's buffer
             /\ maxc' = maxc + 1
             /\ entryCommitStats' =
                   IF newEntryIndex > 0
                   THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
                   ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, nextIndex, matchIndex, commitIndex, leaderCount, payloadMap>>


DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars,  buffer, payloadMap>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED << serverVars,
                   candidateVars,
                   leaderVars,
                   logVars,
                   instrumentationVars,
                   buffer,
                   payloadMap >>
=============================================================================
\* Created by Ovidiu-Cristian Marcu
