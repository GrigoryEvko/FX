# Chapter 17

### 17.1 Related work

*Cohesive type theory* Lawvere's axiomatic cohesion [Law07] defines an abstract, categorical setting in which the objects of one category may be regarded as 'spaces' whose 'points' are drawn from another category. This framework was first applied in type theory by Schreiber and Shulman [SS12], in the form of an extension of **HoTT** by axioms capturing some consequences of a cohesive situation, in pursuit of synthetic quantum field theory. Shulman [Shu18] proceeded to develop a second theory, this one extending homotopy type theory by a combination of axioms and modal judgmental structure, to more precisely capture the axioms of cohesion.

Shulman's aim is to address **HoTT**'s inability to reason about non-homotopy-invariant constructions, *i.e.*, constructions that do not support coercion. His theory combines the homotopical structure of **HoTT** with a second layer of topological structure, the two layers interacting via cohesion. This enables the use of **HoTT**-style synthetic homotopy theory in the service of topological theorems, Brouwer's fixed-point theorem being the showcase example. Extensions to Shulman's theory incorporating additional modalities have been further used to capture *differential* topological structure [GLNPRSW17; Wel18] building on ideas of Schreiber [Sch13]. On a different note, Kavvos has studied connections between cohesion and calculi for information flow [Kav19].

A major difference between our work and Shulman's is that our cohesion is defined around an explicit judgmental (bridge) interval: the connected components functor collapses bridges, the global sections functor returns the type of elements in an empty bridge context, and so on. In contrast, Shulman's judgmental structure only includes modal features; the connection to topology is established via axioms relating the modal operators to the type of real numbers.

A more mundane difference is that we explicitly include two modes (pt and par). Shul-

289