--------------------------- MODULE full ---------------------------

\* --------------------------- raftConstants ---------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Server    \* All entities: e.g., {r1, r2, r3, r4}
CONSTANTS Value     \* e.g., {"v1", "v2"}
CONSTANTS Follower, Candidate, Leader, Switch \* States
CONSTANTS Nil

CONSTANTS Servers   \* Raft group (subset of Server): e.g., {r2, r3, r4}
CONSTANTS switchIndex \* Specific ID for the switch (from Server): e.g., r1

CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

CONSTANTS MaxClientRequests
CONSTANTS MaxBecomeLeader
CONSTANTS MaxTerm

\* --------------------------- raftVariables ---------------------------


VARIABLE messages
VARIABLE switchBuffer
VARIABLE unorderedRequests
VARIABLE switchSentRecord
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

hovercraftVars == <<switchBuffer, unorderedRequests, switchSentRecord>>

vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

\* --------------------------- raftHelpers ---------------------------

Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ] \* Allow up to 2 copies for some models
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
                /\ (\A m \in DOMAIN messages: messages[m] <= 1) \* Ensure at most 1 copy of message

Symmetry == Permutations(Servers)

\* --------------------------- raftInit ---------------------------


InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower] \* All start as Follower, even Switch
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

MyInit == \* For MySwitchSpec: Starts with a known leader and switch
      /\ commitIndex = [s \in Server |-> IF s = switchIndex THEN 0 ELSE 0]
      /\ currentTerm = [s \in Server |-> IF s = switchIndex THEN 2 ELSE 2] \* Example term
      /\ entryCommitStats = << >>
      /\ leaderCount = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN 1 ELSE 0] \* Assuming first in Servers is leader for consistency
      /\ log = [s \in Server |-> <<>>]
      /\ matchIndex = [ s \in Server |-> [t \in Server |-> 0] ]
      /\ maxc = 0
      /\ messages = << >>
      /\ nextIndex = [ s \in Server |-> [t \in Server |-> 1] ]
      /\ state = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN Leader
                                   ELSE IF s = switchIndex THEN Switch
                                   ELSE Follower]
      /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> "", payload |-> ""] ]
      /\ unorderedRequests = [ s \in Server |-> {} ]
      /\ switchSentRecord = [ s \in Server |-> {} ]
      /\ votedFor = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN Nil
                                      ELSE IF s \in Servers THEN (CHOOSE ldr \in Servers: TRUE)
                                      ELSE Nil]
      /\ voterLog = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN [ot \in Servers \ {(CHOOSE ldr \in Servers: TRUE)} |-> <<>>]
                                      ELSE [ign \in {} |-> <<>>] ]
      /\ votesGranted = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN Servers \ {(CHOOSE ldr \in Servers: TRUE)} ELSE {}]
      /\ votesResponded = [s \in Server |-> IF s = (CHOOSE ldr \in Servers: TRUE) THEN Servers \ {(CHOOSE ldr \in Servers: TRUE)} ELSE {}]

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

AppendEntries(i, j) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ i /= j
    /\ state[i] = Leader
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET entryIndex == nextIndex[i][j]
           logEntry == log[i][entryIndex]
           entryMetaData == [term |-> logEntry.term, value |-> logEntry.value]
           entries == << entryMetaData >>
           entryKey == <<entryIndex, logEntry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex - 1}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
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
          /\ unorderedRequests' = [unorderedRequests EXCEPT ![sw] = unorderedRequests[sw] \union {v}]
    /\ UNCHANGED << messages, serverVars, candidateVars, leaderVars, logVars,
                    commitIndex, leaderCount, entryCommitStats, switchSentRecord >>

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

LeaderIngestHovercRaftRequest(ldr, val) ==
    /\ ldr \in Servers
    /\ state[ldr] = Leader
    /\ val \in DOMAIN switchBuffer
    /\ val \in unorderedRequests[ldr]
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
          /\ UNCHANGED << messages, serverVars, candidateVars, matchIndex, nextIndex,
                          commitIndex, leaderCount, maxc, switchBuffer, switchSentRecord >>

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

HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        cacheMissHovercRaft ==
          /\ m.mentries /= <<>>
          /\ LET entry == m.mentries[1]
                 v == entry.value
                 msgTerm == entry.term
             IN
             \lnot ( /\ v \in unorderedRequests[i]
                     /\ v \in DOMAIN switchBuffer
                     /\ switchBuffer[v].term = msgTerm )
    IN /\ m.mterm <= currentTerm[i]
       /\ i \in Servers
       /\ j \in Servers
       /\ \/ /\ \* REJECT REQUEST
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
                \/ /\ m.mterm = currentTerm[i] \* Professor's additional reject condition
                   /\ state[i] = Follower
                   /\ cacheMissHovercRaft
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
             /\ \lnot cacheMissHovercRaft \* Must NOT be a cache miss to accept
             /\ LET index == m.mprevLogIndex + 1
                     newCommitIndex == Min({m.mcommitIndex, Len(log[i]) + Len(m.mentries)})
                IN \/ \* ALREADY DONE/LOG MATCHES (metadata)
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                             /\ log[i][index].value = m.mentries[1].value
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], m.mcommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>
                   \/ \* CONFLICT: REMOVE ENTRIES
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> FALSE,
                                 mmatchIndex     |-> commitIndex[i]], \* Hint to leader
                                 m)
                       /\ UNCHANGED <<serverVars, commitIndex, unorderedRequests>>
                   \/ \* NO CONFLICT: APPEND FULL ENTRY (reconstructed)
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entryMetaData == m.mentries[1]
                              fullEntryFromSwitch == switchBuffer[entryMetaData.value]
                              entryForLocalLog == [term    |-> entryMetaData.term,
                                                   value   |-> entryMetaData.value,
                                                   payload |-> fullEntryFromSwitch.payload]
                          IN log' = [log EXCEPT ![i] = Append(log[i], entryForLocalLog)]
                             /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = unorderedRequests[i] \ {entryMetaData.value}]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], m.mcommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchBuffer, switchSentRecord>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ i \in Servers
    /\ j \in Servers
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess
          /\ LET newMatchIndex == Max({matchIndex[i][j], m.mmatchIndex})
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
       \/ /\ \lnot m.msuccess
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, log, commitIndex, maxc, leaderCount, hovercraftVars>>

UpdateTerm(i, j, m) ==
    /\ i \in Servers
    /\ j \in Server
    /\ m.mterm > currentTerm[i]
    /\ m.mterm <= MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars>>

DropStaleResponse(i, j, m) ==
    /\ i \in Servers
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
    IN /\ i \in Servers
       /\ ( \/ UpdateTerm(i, j, m)
            \/ /\ m.mtype = RequestVoteRequest
               /\ HandleRequestVoteRequest(i, j, m)
            \/ /\ m.mtype = RequestVoteResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleRequestVoteResponse(i, j, m)
            \/ /\ m.mtype = AppendEntriesRequest
               /\ HandleAppendEntriesRequest(i, j, m)
            \/ /\ m.mtype = AppendEntriesResponse
               /\ \/ DropStaleResponse(i, j, m)
                  \/ HandleAppendEntriesResponse(i, j, m)
          )

Next ==
       \/ \E srv \in Servers : Timeout(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ RequestVote(srv1, srv2)
       \/ \E srv \in Servers : BecomeLeader(srv)
       \/ \E ldr \in Servers, v \in Value :
           state[ldr] = Leader /\ SwitchClientRequest(switchIndex, ldr, v)
       \/ \E raftSrv \in Servers, v \in DOMAIN switchBuffer :
           SwitchClientRequestReplicate(switchIndex, raftSrv, v)
       \/ \E ldr \in Servers, v \in DOMAIN switchBuffer :
           state[ldr] = Leader /\ LeaderIngestHovercRaftRequest(ldr, v)
       \/ \E srv \in Servers : AdvanceCommitIndex(srv)
       \/ \E srv1, srv2 \in Servers : srv1 /= srv2 /\ AppendEntries(srv1, srv2)
       \/ \E m \in {msg \in ValidMessage(messages) :
                msg.mdest \in Servers /\
                msg.mtype \in {RequestVoteRequest, RequestVoteResponse,
                               AppendEntriesRequest, AppendEntriesResponse}} :
           Receive(m)

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
            msg.mdest \in Servers /\
            msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} :
       Receive(m)

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