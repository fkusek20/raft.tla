---- MODULE MC ----
EXTENDS raft_0241865428, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174811213199237000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4Servers
const_174811213199238000 == 
{"r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_174811213199239000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:9switchIndex
const_174811213199240000 == 
"r1"
----

\* CONSTANT definitions @modelParameterConstants:13Value
const_174811213199241000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:14Server
const_174811213199242000 == 
{"r1", "r2", "r3", "r4", "r5"}
----

\* CONSTANT definitions @modelParameterConstants:15MaxClientRequests
const_174811213199243000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:16netAggIndex
const_174811213199244000 == 
"r5"
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174811213199245000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat May 24 20:42:11 CEST 2025 by kusek
