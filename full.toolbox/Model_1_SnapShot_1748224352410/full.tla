-------------------------- MODULE full --------------------------

\* --------------------------- raftConstants ---------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server    \* All entities: e.g., {r1, r2, r3, r4, r5}
CONSTANTS Value     \* e.g., {"v1", "v2"}
CONSTANTS Follower, Candidate, Leader, Switch, NetAgg \* States
CONSTANTS Nil

CONSTANTS Servers   \* Raft group (subset of Server): e.g., {r2, r3, r4}
CONSTANTS switchIndex \* Specific ID for the switch (from Server)
CONSTANTS netAggIndex \* Specific ID for the NetAgg (from Server)

CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
          \* No distinct HovercRaft++ message types used in professor's solution,
          \* standard AE/AER are re-purposed by changing source/dest.

CONSTANTS MaxClientRequests
CONSTANTS MaxBecomeLeader
CONSTANTS MaxTerm

\* --------------------------- raftVariables ---------------------------


VARIABLE messages
VARIABLE switchBuffer
VARIABLE unorderedRequests
VARIABLE switchSentRecord
VARIABLE netAggSentCache \* For NetAgg to track what it sent for a given leader AE message
VARIABLE leaderCount
VARIABLE maxc
VARIABLE entryCommitStats

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

VARIABLE log
VARIABLE commitIndex
logVars == <<log, commitIndex>>

VARIABLE votesResponded
VARIABLE votesGranted
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

VARIABLE nextIndex
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>

hovercraftVars == <<switchBuffer, unorderedRequests, switchSentRecord, netAggSentCache>>

vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* --------------------------- raftHelpers ---------------------------


Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)
Reply(response, request) == messages' = WithoutMessage(request, WithMessage(response, messages))

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y
min(a, b) == IF a < b THEN a ELSE b

ValidMessage(msgs) == { m \in DOMAIN messages : msgs[m] > 0 }

CommittedTermPrefix(i, x) ==
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
      LET maxTermIndex == CHOOSE y \in DOMAIN log[i] :
                              /\ log[i][y].term <= x
                              /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    ELSE << >>

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A k \in 1..Len(seq1) : seq1[k] = seq2[k]

Committed(i) ==
    IF commitIndex[i] = 0
    THEN << >>
    ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Servers: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests )
                /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Symmetry == Permutations(Servers) \* Should be Servers if that's the symmetry group

\* --------------------------- raftInit ---------------------------


InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ]
        /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> "", payload |-> ""] ]
        /\ unorderedRequests = [ s \in Server |-> {} ]
        /\ switchSentRecord = [ s \in Server |-> {} ]
        /\ netAggSentCache = [m \in {} |-> {}]

MyInit == \* For MySwitchSpec: Starts with known roles for HovercRaft++
      LET leaderNode == CHOOSE l \in Servers : TRUE \* Pick one Raft server to be leader from CONSTANT Servers
          followers == Servers \ {leaderNode}
      IN
      /\ commitIndex = [s \in Server |-> 0]
      /\ currentTerm = [s \in Server |-> 2] \* Match professor's example term
      /\ entryCommitStats = << >>
      /\ leaderCount = [s \in Server |-> IF s = leaderNode THEN 1 ELSE 0]
      /\ log = [s \in Server |-> <<>>]
      /\ matchIndex = [ s \in Server |-> [t \in Server |-> 0] ]
      /\ maxc = 0
      /\ messages = << >>
      /\ nextIndex = [ s \in Server |-> [t \in Server |-> 1] ]
      /\ state = [s \in Server |-> IF s = leaderNode THEN Leader
                                   ELSE IF s = switchIndex THEN Switch
                                   ELSE IF s = netAggIndex THEN NetAgg
                                   ELSE IF s \in Servers THEN Follower
                                   ELSE Follower] \* Default for any other non-assigned server
      /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> "", payload |-> ""] ]
      /\ unorderedRequests = [ s \in Server |-> {} ]
      /\ switchSentRecord = [ s \in Server |-> {} ]
      /\ netAggSentCache = [m \in {} |-> {}]
      /\ votedFor = [s \in Server |-> IF s = leaderNode THEN Nil
                                      ELSE IF s \in Servers THEN leaderNode
                                      ELSE Nil]
      /\ voterLog = [s \in Server |-> IF s = leaderNode THEN [f \in followers |-> <<>>]
                                      ELSE [ign \in {} |-> <<>>] ]
      /\ votesGranted = [s \in Server |-> IF s = leaderNode THEN followers ELSE {}]
      /\ votesResponded = [s \in Server |-> IF s = leaderNode THEN followers ELSE {}]

\* --------------------------- raftActionsSolution ---------------------------

----
\* Define state transitions

Restart(i) ==
    /\ i \in Servers
    /\ state[i] = Leader
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [k \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [k \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, hovercraftVars>>

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

\* Standard Raft AppendEntries (e.g., for heartbeats or non-HovercRaft entries if any)
LeaderStandardAppendEntries(i, j) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i]) \* Or can be > Len(log[i]) for heartbeats
    /\ LET entryIndex == nextIndex[i][j]
           entriesToSend == IF nextIndex[i][j] > Len(log[i]) THEN << >> ELSE << log[i][entryIndex] >>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
           entryKey == IF Len(entriesToSend) > 0 THEN <<entryIndex, entriesToSend[1].term>> ELSE <<0,0>>
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entriesToSend,
                mlog           |-> log[i], \* For proof/history, not strictly needed for logic
                mcommitIndex   |-> commitIndex[i],
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF Len(entriesToSend) > 0 /\ entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats
    /\ UNCHANGED <<serverVars, candidateVars, nextIndex, matchIndex, log, commitIndex, maxc, leaderCount, hovercraftVars>>

BecomeLeader(i) ==
    /\ i \in Servers
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [k \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, hovercraftVars>>

SwitchClientRequest(sw, ldr, v) ==
    /\ sw = switchIndex
    /\ ldr \in Servers
    /\ state[ldr] = Leader
    /\ v \in Value
    /\ maxc < MaxClientRequests
    /\ v \notin DOMAIN switchBuffer
    /\ LET leaderTerm == currentTerm[ldr]
           entry == [term    |-> leaderTerm,
                     value   |-> v,
                     payload |-> v]
       IN /\ switchBuffer' = switchBuffer @@ (v :> entry)
          /\ maxc' = maxc + 1
          \* Professor's solution trace doesn't show unorderedRequests[sw] being updated here.
          \* /\ unorderedRequests' = [unorderedRequests EXCEPT ![sw] = unorderedRequests[sw] \union {v}]
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, logVars,
                    commitIndex, leaderCount, entryCommitStats, switchSentRecord, unorderedRequests, netAggSentCache >>

SwitchClientRequestReplicate(sw, raftSrv, val) ==
    /\ sw = switchIndex
    /\ raftSrv \in Servers
    /\ val \in DOMAIN switchBuffer
    /\ LET entryToReplicate == switchBuffer[val]
           termOfEntry == entryToReplicate.term
           pairToRecord == <<val, termOfEntry>>
       IN /\ pairToRecord \notin switchSentRecord[raftSrv]
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![raftSrv] = unorderedRequests[raftSrv] \union {val}]
          /\ switchSentRecord' = [switchSentRecord EXCEPT ![raftSrv] = switchSentRecord[raftSrv] \union {pairToRecord}]
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, logVars,
                    commitIndex, maxc, leaderCount, entryCommitStats, switchBuffer >>

\* Leader 'i' ingests request v, puts FULL entry in its log, sends METADATA AE to NetAgg
LeaderIngressHovercRaftRequest(i, v) ==
    /\ i \in Servers
    /\ state[i] = Leader
    /\ v \in DOMAIN switchBuffer
    /\ v \in unorderedRequests[i]
    /\ LET leaderTerm == currentTerm[i]
           fullEntryFromSwitch == switchBuffer[v]
           entryForLeaderLog == [term    |-> leaderTerm,
                                 value   |-> v,
                                 payload |-> fullEntryFromSwitch.payload]
           valueAlreadyExistsInLeaderLog == \E idx \in 1..Len(log[i]) : log[i][idx].value = v
           isNewToLog == ~valueAlreadyExistsInLeaderLog

           metadataEntryForNetAgg == [term |-> entryForLeaderLog.term, value |-> entryForLeaderLog.value]
           prevLogIndexForNetAggMsg == Len(log[i])
           prevLogTermForNetAggMsg == LastTerm(log[i])
           newEntryIndexInLeaderLog == Len(log[i]) + 1
           newEntryKey == <<newEntryIndexInLeaderLog, entryForLeaderLog.term>>

           msgToNetAgg == [mtype         |-> AppendEntriesRequest,
                           mterm         |-> leaderTerm,
                           mprevLogIndex |-> prevLogIndexForNetAggMsg,
                           mprevLogTerm  |-> prevLogTermForNetAggMsg,
                           mentries      |-> << metadataEntryForNetAgg >>,
                           mcommitIndex  |-> commitIndex[i],
                           msource       |-> i,
                           mdest         |-> netAggIndex]
       IN /\ isNewToLog
          /\ log' = [log EXCEPT ![i] = Append(log[i], entryForLeaderLog)]
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = unorderedRequests[i] \ {v}]
          /\ entryCommitStats' =
                IF newEntryIndexInLeaderLog > 0
                THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
                ELSE entryCommitStats
          /\ Send(msgToNetAgg)
    /\ UNCHANGED << serverVars, candidateVars, nextIndex, matchIndex,
                    commitIndex, leaderCount, maxc, switchBuffer, switchSentRecord, netAggSentCache >>

\* NetAgg receives AppendEntries metadata from Leader, prepares to replicate it
NetAggReceivesAppendEntries(na, m) ==
    /\ na = netAggIndex
    /\ state[na] = NetAgg
    /\ m.mdest = na
    /\ m.msource \in Servers
    /\ state[m.msource] = Leader
    /\ m.mtype = AppendEntriesRequest
    /\ m.mentries /= << >>
    /\ m \notin DOMAIN netAggSentCache
    /\ netAggSentCache' = netAggSentCache @@ (m :> {})
    /\ Discard(m)
    /\ UNCHANGED << serverVars, candidateVars, leaderVars, logVars, instrumentationVars,
                    switchBuffer, unorderedRequests, switchSentRecord >>

\* NetAgg (na) sends to Follower (flw) based on original Leader message (origLeaderMsgFromCache)
NetAggAppendsToFollower(na, flw, origLeaderMsgFromCache) ==
    /\ na = netAggIndex
    /\ state[na] = NetAgg
    /\ flw \in Servers
    /\ origLeaderMsgFromCache \in DOMAIN netAggSentCache
    /\ flw \notin netAggSentCache[origLeaderMsgFromCache]
    /\ LET metadataEntry == Head(origLeaderMsgFromCache.mentries)
           valToReplicate == metadataEntry.value
       IN /\ valToReplicate \in unorderedRequests[flw]
          /\ LET fullEntryFromSwitch == switchBuffer[valToReplicate]
                 msgToSendToFollower == [
                    mtype         |-> AppendEntriesRequest,
                    mterm         |-> origLeaderMsgFromCache.mterm,
                    mprevLogIndex |-> origLeaderMsgFromCache.mprevLogIndex,
                    mprevLogTerm  |-> origLeaderMsgFromCache.mprevLogTerm,
                    mentries      |-> <<fullEntryFromSwitch >>, \* Sends FULL entry
                    mcommitIndex  |-> origLeaderMsgFromCache.mcommitIndex,
                    msource       |-> na,
                    mdest         |-> flw
                 ]
             IN Send(msgToSendToFollower)
                /\ netAggSentCache' = [netAggSentCache EXCEPT ![origLeaderMsgFromCache] = @ \union {flw}]
                /\ LET leader == origLeaderMsgFromCache.msource
                       leaderLogEntryIndex == origLeaderMsgFromCache.mprevLogIndex + Len(origLeaderMsgFromCache.mentries)
                       entryKeyOnLeader == <<leaderLogEntryIndex, metadataEntry.term>>
                   IN entryCommitStats' =
                        IF entryKeyOnLeader \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKeyOnLeader].committed
                        THEN [entryCommitStats EXCEPT ![entryKeyOnLeader].sentCount = @ + 1]
                        ELSE entryCommitStats
    /\ UNCHANGED << serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount,
                    switchBuffer, unorderedRequests, switchSentRecord, messages >>

\* NetAgg (na) advances Leader's (ldr) commitIndex
NetAggAdvanceCommitIndex(na) ==
    /\ na = netAggIndex
    /\ state[na] = NetAgg
    /\ \E ldr \in Servers: state[ldr] = Leader \* Ensure there is a leader
    /\ LET leader == CHOOSE l \in Servers: state[l] = Leader
           Agree(index) == {leader} \cup {k \in Servers : matchIndex[leader][k] >= index}
           agreeIndexes == {index \in 1..Len(log[leader]) :
                                /\ Agree(index) \in Quorum
                                /\ log[leader][index].term = currentTerm[leader]}
           newLeaderCommitIndex == IF agreeIndexes /= {} THEN Max(agreeIndexes) ELSE commitIndex[leader]
           changed == newLeaderCommitIndex > commitIndex[leader]
           committedIndexes == { k \in Nat : /\ k > commitIndex[leader]
                                             /\ k <= newLeaderCommitIndex }
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }
       IN /\ changed \* Only take step if commitIndex actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![leader] = newLeaderCommitIndex]
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ]
                   ELSE entryCommitStats[key] ]
    /\ UNCHANGED <<messages, serverVars, candidateVars, nextIndex, matchIndex, log, maxc, leaderCount, hovercraftVars>>

HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ i \in Servers
       /\ j \in Servers
       /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

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

HandleAppendEntriesRequest(i, j, m) == \* i is follower, j is NetAgg or Leader
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

        payloadRequirementMet ==
            \/ m.mentries = << >>
            \/ LET entryFromMessage == m.mentries[1]
                   v == entryFromMessage.value
               IN v \in unorderedRequests[i]
    IN /\ m.mterm <= currentTerm[i]
       /\ i \in Servers
       /\ (j = netAggIndex \/ j \in Servers) \* Sender is NetAgg or Raft Leader

       /\ \/ /\ \* REJECT REQUEST
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ j = netAggIndex \* If from NetAgg, payload ID must be buffered
                   /\ m.mentries /= << >>
                   /\ \lnot payloadRequirementMet
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars, unorderedRequests>>

          \/ \* RETURN TO FOLLOWER STATE
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, unorderedRequests>>

          \/ \* ACCEPT REQUEST
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ ( (j = netAggIndex /\ payloadRequirementMet) \/ \* If from NetAgg, payload must be ready
                  (j \in Servers) \/                               \* Or if from Leader (e.g. heartbeat, standard Raft AE)
                  m.mentries = << >> )                             \* Or if it's an empty heartbeat
             /\ LET index == m.mprevLogIndex + 1
                    leaderCommit == m.mcommitIndex
                    maxPossibleCommit == m.mprevLogIndex + Len(m.mentries)
                    effectiveCommit == Min({leaderCommit, maxPossibleCommit})
                IN \/ \* ALREADY DONE/LOG MATCHES
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index] = m.mentries[1] \* Compare full entry
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], effectiveCommit})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>

                   \/ \* CONFLICT - REMOVE ENTRIES
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> FALSE,
                                 mmatchIndex     |-> commitIndex[i]],
                                 m)
                       /\ UNCHANGED <<serverVars, commitIndex, unorderedRequests>>

                   \/ \* NO CONFLICT: APPEND FULL ENTRY
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET fullEntryToAppend == m.mentries[1]
                              appendedValueID == fullEntryToAppend.value
                          IN log' = [log EXCEPT ![i] = Append(log[i], fullEntryToAppend)]
                             /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = unorderedRequests[i] \ {appendedValueID}]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], effectiveCommit})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars>>

       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars,
                       switchBuffer, switchSentRecord, netAggSentCache>>

\* Handles responses for BOTH Leader and NetAgg
HandleAppendEntriesResponse(receiver, sender, m) ==
    /\ receiver \in Servers \/ receiver = netAggIndex \* Receiver is Leader or NetAgg
    /\ sender \in Servers                             \* Sender is always a Raft Follower
    /\ m.mtype = AppendEntriesResponse
    /\ \E ldr \in Servers: state[ldr] = Leader \* There must be a Raft leader
    /\ LET LeaderId == CHOOSE l \in Servers: state[l] = Leader
       IN /\ m.mterm = currentTerm[LeaderId] \* Responses are for the current leader's term
          /\ \/ /\ m.msuccess
                /\ LET newMatchIndex == Max({matchIndex[LeaderId][sender], m.mmatchIndex})
                       entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[LeaderId])
                                    THEN <<newMatchIndex, log[LeaderId][newMatchIndex].term>>
                                    ELSE <<0, 0>>
                   IN /\ nextIndex'  = [nextIndex  EXCEPT ![LeaderId][sender] = newMatchIndex + 1]
                      /\ matchIndex' = [matchIndex EXCEPT ![LeaderId][sender] = newMatchIndex]
                      /\ entryCommitStats' =
                           IF /\ entryKey /= <<0, 0>>
                              /\ entryKey \in DOMAIN entryCommitStats
                              /\ ~entryCommitStats[entryKey].committed
                           THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                           ELSE entryCommitStats
             \/ /\ \lnot m.msuccess
                /\ nextIndex' = [nextIndex EXCEPT ![LeaderId][sender] = Max({nextIndex[LeaderId][sender] - 1, 1})]
                /\ UNCHANGED <<matchIndex, entryCommitStats>>
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, candidateVars, log, commitIndex, maxc, leaderCount, hovercraftVars>>

UpdateTerm(i, j, m) ==
    /\ i \in Servers \/ i = netAggIndex \* Can be Raft server or NetAgg
    /\ j \in Server
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = IF i \in Servers THEN [state EXCEPT ![i] = Follower] ELSE state \* NetAgg state doesn't change on term update
    /\ votedFor'       = IF i \in Servers THEN [votedFor EXCEPT ![i] = Nil] ELSE votedFor
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

DropStaleResponse(i, j, m) ==
    /\ i \in Servers \/ i = netAggIndex
    /\ j \in Server
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* --------------------------- raftSpec ---------------------------


Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest            /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ ( \/ DropStaleResponse(i, j, m) \/ HandleRequestVoteResponse(i, j, m) )
       \/ /\ m.mtype = AppendEntriesRequest
          /\ i = netAggIndex /\ j \in Servers /\ NetAggReceivesAppendEntries(i, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ i \in Servers   /\ (j = netAggIndex \/ j \in Servers) /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ HandleAppendEntriesResponse(i, j, m) \* Generic handler for Leader or NetAgg

Next ==
       \* --- Standard Raft Leader Election and Timeouts (for Raft Servers) ---
       \/ \E srv \in Servers : Timeout(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ RequestVote(srv1, srv2)
       \/ \E srv \in Servers : BecomeLeader(srv)

       \* --- HovercRaft Specific Actions ---
       \/ \E ldr \in Servers, v \in Value :
           state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)

       \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer :
           SwitchClientRequestReplicate(switchIndex, raftSrv, v)

       \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :
           state[ldr] = Leader /\ LeaderIngressHovercRaftRequest(ldr, v)

       \/ \E na \in {netAggIndex}, origLeaderMsg \in DOMAIN netAggSentCache, flw \in Servers : \* CORRECTED
           na /= flw /\ NetAggAppendsToFollower(na, flw, origLeaderMsg)

       \/ \E na \in {netAggIndex} : state[na]=NetAgg /\ NetAggAdvanceCommitIndex(na) \* CORRECTED, NetAgg triggers leader commit

       \/ \E srv1 \in Servers, srv2 \in Servers : \* Standard AE for heartbeats etc.
           srv1 /= srv2 /\ state[srv1]=Leader /\ LeaderStandardAppendEntries(srv1, srv2)

       \/ \E m \in ValidMessage(messages) : Receive(m)

MySwitchNext ==
   \/ \E ldr \in Servers, v \in Value :
       state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)
   \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer :
       SwitchClientRequestReplicate(switchIndex, raftSrv, v)
   \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :
       state[ldr] = Leader /\ LeaderIngressHovercRaftRequest(ldr, v)
   \/ \E na \in {netAggIndex}, origLeaderMsg \in DOMAIN netAggSentCache, flw \in Servers : \* CORRECTED
       na /= flw /\ NetAggAppendsToFollower(na, flw, origLeaderMsg)
   \/ \E na \in {netAggIndex} : state[na]=NetAgg /\ NetAggAdvanceCommitIndex(na) \* CORRECTED
   \/ \E srv1 \in Servers, srv2 \in Servers : \* Standard AE for heartbeats etc.
       srv1 /= srv2 /\ state[srv1]=Leader /\ LeaderStandardAppendEntries(srv1, srv2)
   \/ \E m \in ValidMessage(messages) : Receive(m)

Spec == Init /\ [][Next]_vars
MySpec == MyInit /\ [][MySwitchNext]_vars

\* -------------------- Invariants --------------------
AllServersHaveOneUnorderedRequestInv ==
    \E s \in Servers : Cardinality(unorderedRequests[s]) /= Cardinality(Value)

NoRaftServerHasCommittedYet ==
    \A srv \in Servers : commitIndex[srv] = 0

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

\* --------------------------- raftModelPerf ---------------------------


MaxCInv == (\E i \in Servers : state[i] = Leader) => maxc <= MaxClientRequests
LeaderCountInv == \A i \in Servers : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)
MaxTermInv == \A i \in Servers : currentTerm[i] <= MaxTerm

EntryCommitMessageCountInv ==
    LET NumRaftServers == Cardinality(Servers)
        NumFollowers == IF NumRaftServers > 0 THEN NumRaftServers - 1 ELSE 0
        MinFollowersForMajority == IF NumRaftServers > 0 THEN NumRaftServers \div 2 ELSE 0
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers)
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

EntryCommitAckQuorumInv ==
    LET NumRaftServers == Cardinality(Servers)
        MinFollowerAcksForMajority == IF NumRaftServers > 0 THEN NumRaftServers \div 2 ELSE 0
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

LeaderCommitted ==
    \E i \in Servers : commitIndex[i] /= 1
=============================================================================