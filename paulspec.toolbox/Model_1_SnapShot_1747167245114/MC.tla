---- MODULE MC ----
EXTENDS paulspec, TLC

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174716724199179000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174716724199180000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:11Value
const_174716724199181000 == 
{"v1", "v2"}
----

\* CONSTANT definitions @modelParameterConstants:12Server
const_174716724199182000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:13MaxClientRequests
const_174716724199183000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174716724199184000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Tue May 13 22:14:01 CEST 2025 by kusek
