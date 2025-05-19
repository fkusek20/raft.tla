---- MODULE MC ----
EXTENDS paulspec, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1747167261640108000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1747167261640109000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:11Value
const_1747167261640110000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:12Server
const_1747167261640111000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:13MaxClientRequests
const_1747167261640112000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1747167261640113000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Tue May 13 22:14:21 CEST 2025 by kusek
