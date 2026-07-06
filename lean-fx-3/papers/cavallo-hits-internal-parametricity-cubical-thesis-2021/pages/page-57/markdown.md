# Chapter 3

## Cubical type theory

Cubical type theory enhances Martin-Löf's type theory with a contentful notion of equality, the *path*. It will be the basic substrate with which we work for the remainder of this thesis; Parts II to IV each describe extensions of cubical type theory. We can separate the history of cubical type theory into several distinct if frequently interacting strands: the history of higher-dimensional models of intensional type theory, the history of higher-dimensional formalisms, and the history of constructivity and computation for the two.

**Higher-dimensional models** The earliest higher-dimensional model of **ITT** is Hofmann and Streicher's *groupoid interpretation* [HS98]. By higher-dimensional model, we mean one that refutes the uniqueness of identity proofs (UIP) principle. Said principle states that any pair of proofs of identity are themselves identical.

$$\frac{A \text{ type} \quad M, N \in A \quad P, Q \in \text{Id}(A, M, N)}{\text{uip} \in \text{Id}(\text{Id}(A, M, N), P, Q)}$$

Hofmann and Streicher's model was indeed designed for the purpose of refuting this principle, showing it independent of **ITT**. They interpret types as *groupoids*, categories in which every morphism is invertible. The identity type between elements $a$ and $b$ of a groupoid $G$ is then the set (*i.e.*, discrete groupoid) of morphisms between them, which may contain multiple elements. The model thus has *one* level of higher structure: there can be distinct proofs of identity between two objects, but any two proofs of identities between identities are necessarily identical.

Awodey and Warren [AW09] picked up this thread by establishing a connection between **ITT**'s identity type and the concept of a *weak factorization system* from homotopy theory. In his dissertation, Warren shows that one can construct $n$-dimensional models of **ITT** for every $n$—each refuting an $n$-dimensional version of UIP—as well as an infinite-dimensional model in *strict $\omega$-groupoids* that refutes all such principles. Van den Berg and

45