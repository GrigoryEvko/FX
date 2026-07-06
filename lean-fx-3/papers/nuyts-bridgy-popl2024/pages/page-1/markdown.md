[LOGO]

[LOGO]

# Internal and Observational Parametricity for Cubical Agda

ANTOINE VAN MUYLDER, KU Leuven, Belgium

ANDREAS NUYTS, KU Leuven, Belgium

DOMINIQUE DEVRIESE, KU Leuven, Belgium

Two approaches exist to incorporate parametricity into proof assistants based on dependent type theory. On the one hand, parametricity translations conveniently compute parametricity statements and their proofs solely based on individual well-typed polymorphic programs. But they do not offer internal parametricity: formal proofs that any polymorphic program of a certain type satisfies its parametricity statement. On the other hand, internally parametric type theories augment plain type theory with additional primitives out of which internal parametricity can be derived. But those type theories lack mature proof assistant implementations and deriving parametricity in them involves low-level intractable proofs. In this paper, we contribute Agda --bridges: the first practical internally parametric proof assistant. We provide the first mechanized proofs of crucial theorems for internal parametricity, like the relativity theorem. We identify a high-level sufficient condition for proving internal parametricity which we call the structure relatedness principle (SRP) by analogy with the structure identity principle (SIP) of HoTT/UF. We state and prove a general parametricity theorem for types that satisfy the SRP. Our parametricity theorem lets us obtain one-liner proofs of standard internal free theorems. We observe that the SRP is harder to prove than the SIP and provide in Agda --bridges a shallowly embedded type theory to compose types that satisfy the SRP. This type theory is an observational type theory of logical relations and our parametricity theorem ought to be one of its inference rules.

CCS Concepts: • Theory of computation → Type theory.

Additional Key Words and Phrases: cubical type theory, parametricity, structure relatedness principle, Agda

# ACM Reference Format:

Antoine Van Muylder, Andreas Nuyts, and Dominique Devriese. 2024. Internal and Observational Parametricity for Cubical Agda. Proc. ACM Program. Lang. 8, POPL, Article 8 (January 2024), 32 pages. https://doi.org/10.1145/3632850

# 1 INTRODUCTION

Theorems for free [Wadler 1989] are mathematical statements about polymorphic programs whose validity only depends on a program's type, not its implementation. Such theorems hold in programming languages that prevent polymorphic programs from inspecting their type arguments. This restriction forces polymorphic programs to behave parametrically, i.e., apply the same algorithm irrespective of the type they are invoked at.

For example, let us take a purely functional, polymorphic program taking two lists as input and outputting a single list, for an arbitrary type X (we use curly braces to indicate the presence of an implicit argument).

$$p : \forall \{X : \text{Type}\} \rightarrow \text{List } X \rightarrow \text{List } X \rightarrow \text{List } X \tag{1}$$

Authors' addresses: Antoine Van Muylder, KU Leuven, DistriNet, Belgium, antoine.vanmuylder@kuleuven.be; Andreas Nuyts, KU Leuven, DistriNet, Belgium, andreas.nuyts@kuleuven.be; Dominique Devriese, KU Leuven, DistriNet, Belgium, dominique.devriese@kuleuven.be.

[LOGO]

This work is licensed under a Creative Commons Attribution 4.0 International License.

© 2024 Copyright held by the owner/author(s).

ACM 2475-1421/2024/1-ART8

https://doi.org/10.1145/3632850

Proc. ACM Program. Lang., Vol. 8, No. POPL, Article 8. Publication date: January 2024.