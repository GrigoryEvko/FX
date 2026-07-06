restriction does not significantly alter the theory. The primary drawback of using left semi-model structures is practical: most of the literature focuses on Quillen model structures, so results must be re-proven for semi-model structures. A substantial body of work (see below) has been completed on this topic, and no serious difficulties have arisen so far.

In this paper, all Quillen model structures and left semi-model structures we encounter are "combinatorial" (in the sense of Definition A.5 below). In particular, they have fully formed weak factorization systems, rather than the weakened version assumed in [39], [18], or [23]. Assuming the existence of full factorization systems simplifies the definition, which we will adopt here. In [24], these are referred to as "factorization left semi-model categories," which is not the most general definition found in the literature.

**A.1 Definition.** A *premodel category* is a complete and cocomplete category $\mathcal{C}$ equipped with two weak factorization systems: (*anodyne cofibrations*, *fibrations*) and (*cofibrations*, *anodyne fibrations*), where the anodyne cofibrations are also cofibrations, or equivalently, the anodyne fibrations are fibrations.

**A.2 Definition.** An object $C$ is *fibrant* if the map $C \rightarrow 1$ is a fibration. An object is *cofibrant* if the map $\emptyset \rightarrow C$ is a cofibration.

**A.3 Definition.** A (*Spitzweck factorization*) *left semi-model category* is a pre-model category with a class $\mathcal{W}$ of morphisms, called weak equivalences, satisfying the following conditions:

(1) The class $\mathcal{W}$ contains all isomorphisms and satisfies the 2-out-of-3 property.
(2) A fibration is anodyne if and only if it is in $\mathcal{W}$.
(3) A cofibration with a cofibrant domain is anodyne if and only if it is in $\mathcal{W}$.

Note that if we remove the restriction "with cofibrant domain" in the third axiom, we recover the definition of a Quillen model structure. In the remainder of the paper, we will simply refer to these structures as left semi-model categories.

**A.4 Remark.** We should clarify the terminology here compared to what we used, for instance, in Definition 2.38. Often, as in the present paper, we begin with a premodel category with two weak factorization systems (anodyne cofibrations, fibrations) and (cofibrations, anodyne fibrations) that does not itself form a left semi-model category. However, we use a "saturation" construction described in Section 4 of [24], which adjusts the weak factorization systems without altering the underlying category, the cofibrations with cofibrant domains, or the fibrations with fibrant domains. The resulting premodel category is a left semi-model category. These new factorization systems are typically called "trivial" or "acyclic" instead of "anodyne." See Sections 3 and 4 of [24] for more details on this process.

In this paper, this distinction means that, contrary to what Definition A.3 might suggest, Theorem 2.43 does not imply that a cofibration (with a cofibrant domain) that is an equivalence is an anodyne cofibration as defined in Definition 2.38. Instead, the premodel structure that Theorem 2.43 asserts to be a left semi-model category involves weak factorization systems for (acyclic

59