Formlization of LTL and Simulation Relations in Coq 
This is a project done for Software Foundation course (CSCI8980), University of Minnesota

Coq is a useful proof assistant well-known in formalizing predicate and propositional logic. 
Linear Temporal Logic (LTL) is a logical formalism that can be used to specify important properties of a system. 
In general, formalizing LTL semantics in Coq is an interesting activity that can have useful applications.
This project first formalizes LTL in Coq, then provides a formalization of simulation relations using the first formulation.



LTL is used to specify the properties of a system. The kinds of systems we are interested in verifying using LTL can be modeled as transition systems. A transition system can be considered as an extended graph where states of the system are equal to the nodes of the graph, and the graph edges represent transitions between the states (i.e. the stepwise behavior of the system). In addition to these basic components of the graph, we work with a fixed set Atoms of atomic formulas. Semantically, atoms are atomic facts which may hold of a system. Atomic propositions (or atoms) state simple facts about a state. So, states are distinguished by the fact that which atoms they have or which atoms they satisfy.


Simulation relations are often used to show that one system correctly implements another (more abstract system), which is appropriate for the purpose of verification. 