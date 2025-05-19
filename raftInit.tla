------------------------------ MODULE raftInit ------------------------------

EXTENDS raftHelpers

InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
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
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize new variable
        /\ entryCommitStats = [idx_term \in {} |-> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE]]
        /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> v, payload |-> v] ] \* Empty map
        /\ unorderedRequests = [ s \in Server |-> {} ] \* Empty set for each server (incl. switch)
        /\ switchSentRecord = [ s \in Server |-> {} ]  \* Empty set for each server (incl. switch)

\* MyInit remains unchanged for the core Raft state, entryCommitStats is handled in Init.
\* Example using ProfInit structure for MyInit
MyInit ==
    \* REMOVED: LET Servers == ... Server == ... switchIndex == ... Value == ...
    \* REMOVED: IN
      /\ commitIndex = [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0]
      /\ currentTerm = [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2]
      /\ entryCommitStats = << >>
      /\ leaderCount = [r1 |-> 0, r2 |-> 1, r3 |-> 0, r4 |-> 0]
      /\ log = [r1 |-> <<>>, r2 |-> <<>>, r3 |-> <<>>, r4 |-> <<>>]
      \* Use the CONSTANT 'Server' directly here
      /\ matchIndex = [ r1 |-> [s \in Server |-> 0],
                       r2 |-> [s \in Server |-> 0],
                       r3 |-> [s \in Server |-> 0],
                       r4 |-> [s \in Server |-> 0] ]
      /\ maxc = 0
      /\ messages = << >>
      \* Use the CONSTANT 'Server' directly here
      /\ nextIndex = [ r1 |-> [s \in Server |-> 1],
                      r2 |-> [s \in Server |-> 1],
                      r3 |-> [s \in Server |-> 1],
                      r4 |-> [s \in Server |-> 1] ]
      \* Use the CONSTANT 'Switch', 'Leader', 'Follower' directly here
      /\ state = [r1 |-> Switch, r2 |-> Leader, r3 |-> Follower, r4 |-> Follower]
      \* Use the CONSTANT 'Value' implicitly here
      /\ switchBuffer = [ v \in {} |-> [term |-> 0, value |-> v, payload |-> v] ] \* Starts empty
      \* Use the CONSTANT 'Server' directly here
      /\ unorderedRequests = [ s \in Server |-> {} ] \* Starts empty
      \* Use the CONSTANT 'Server' directly here
      /\ switchSentRecord = [ s \in Server |-> {} ]  \* Starts empty
      \* Use the CONSTANT 'Nil' directly here
      /\ votedFor = [r1 |-> Nil, r2 |-> Nil, r3 |-> "r2", r4 |-> "r2"]
      /\ voterLog = [r1 |-> << >>, r2 |-> [r3 |-> <<>>, r4 |-> <<>>], r3 |-> << >>, r4 |-> << >>]
      /\ votesGranted = [r1 |-> {}, r2 |-> {"r3", "r4"}, r3 |-> {}, r4 |-> {}]
      /\ votesResponded = [r1 |-> {}, r2 |-> {"r3", "r4"}, r3 |-> {}, r4 |-> {}]
    
    
 MyNewInit ==
    LET leaderNode == CHOOSE l \in Servers : TRUE \* Pick a leader from the CONSTANT Servers
        otherRaftNodes == Servers \ {leaderNode}
        TheSwitchId == switchIndex \* Use the CONSTANT switchIndex
    IN
    \* No need to assign to Servers' or switchIndex' here
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = leaderNode THEN 1 ELSE 0]
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |-> IF s = leaderNode THEN Leader
                               ELSE IF s = TheSwitchId THEN Switch
                               ELSE Follower]
    /\ switchBuffer = [v \in {} |-> [term |-> 0, value |-> "", payload |-> ""]]
    /\ unorderedRequests = [s \in Server |-> {}]
    /\ switchSentRecord = [s \in Server |-> {}]
    /\ votedFor = [s \in Server |-> IF s = leaderNode THEN Nil ELSE IF s \in Servers THEN leaderNode ELSE Nil]
    /\ voterLog = [s \in Server |-> IF s = leaderNode THEN [on \in otherRaftNodes |-> <<>>] ELSE [ign \in {} |-> <<>>] ]
    /\ votesGranted = [s \in Server |-> IF s = leaderNode THEN otherRaftNodes ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = leaderNode THEN otherRaftNodes ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ]
\* to be used directly in model Init the value
\*MyInit2 ==
\*    /\  commitIndex = (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  currentTerm = (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2)
\*    /\  entryCommitStats = << >>
\*    /\  leaderCount = (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  log = (r1 :> <<>> @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  matchIndex = ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) )
\*    /\  maxc = 0
\*    /\  messages = << >>
\*    /\  nextIndex = ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) )
\*    /\  state = (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower)
\*    /\  votedFor = (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1)
\*    /\  voterLog = (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  votesGranted = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
\*    /\  votesResponded = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})


=============================================================================
\* Created by Ovidiu-Cristian Marcu
