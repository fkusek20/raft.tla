---- MODULE MC ----
EXTENDS raft_0241865428, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_17480950367462000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Servers
const_17480950367463000 == 
{"r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_17480950367464000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:9switchIndex
const_17480950367465000 == 
"r1"
----

\* CONSTANT definitions @modelParameterConstants:13Value
const_17480950367466000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:14Server
const_17480950367467000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:15MaxClientRequests
const_17480950367468000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17480950367469000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat May 24 15:57:16 CEST 2025 by kusek
