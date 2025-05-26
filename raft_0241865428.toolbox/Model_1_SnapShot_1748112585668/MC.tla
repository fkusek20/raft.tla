---- MODULE MC ----
EXTENDS raft_0241865428, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174811258357073000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Servers
const_174811258357074000 == 
{"r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_174811258357075000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:9switchIndex
const_174811258357076000 == 
"r1"
----

\* CONSTANT definitions @modelParameterConstants:13Value
const_174811258357077000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:14Server
const_174811258357078000 == 
{"r1", "r2", "r3", "r4", "r5"}
----

\* CONSTANT definitions @modelParameterConstants:15MaxClientRequests
const_174811258357079000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:16netAggIndex
const_174811258357080000 == 
"r5"
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174811258357081000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat May 24 20:49:43 CEST 2025 by kusek
