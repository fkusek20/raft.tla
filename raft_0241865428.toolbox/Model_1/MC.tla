---- MODULE MC ----
EXTENDS raft_0241865428, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174767092177319000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Servers
const_174767092177320000 == 
{"r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_174767092177321000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:9switchIndex
const_174767092177322000 == 
"r1"
----

\* CONSTANT definitions @modelParameterConstants:13Value
const_174767092177323000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:14Server
const_174767092177324000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:15MaxClientRequests
const_174767092177325000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174767092177426000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Mon May 19 18:08:41 CEST 2025 by kusek
