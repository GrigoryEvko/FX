# The ∞-category of ∞-categories in simplicial type theory

Daniel Gratzer

gratzer@cs.au.dk

Aarhus University

Jonathan Weinberger

jweinberger@chapman.edu

Chapman University

Ulrik Buchholtz

ulrik.buchholtz@nottingham.ac.uk

University of Nottingham

## Abstract

Simplicial type theory (STT) was introduced by Riehl and Shulman to leverage homotopy type theory to prove results about (∞, 1)-categories. Initial work on simplicial type theory focused on "formal" arguments in higher category theory and, in particular, no non-trivial examples of ∞-category theory were constructible within STT. More recent work has changed this state of affairs by applying techniques developed initially for cubical type theory to construct the ∞-category of spaces. We complete this process by constructing the ∞-category of ∞-categories, recovering one of the main foundational results of ∞-category theory (straightening–unstraightening) purely type-theoretically. We also show how this construction enables new examples of the directed version of the structure identity principle: the structure homomorphism principle.

## Acknowledgments

Jonathan Weinberger is grateful to the Fowler of School of Engineering at Chapman University for generous support of this work. He is particularly thankful to the Fletcher Jones Foundation and their award of a Fletcher Jones Foundation Faculty Fellowship in Engineering '25–'28 and the ensuing generous funding of this work. He also thanks the Schmid School of Science and Technology as well as the Center of Excellence in Computation, Algebra, and Topology (CECAT), both at Chapman University, for providing an excellent research environment.

## 1 Introduction

A defining characteristic of dependent type theories is their focus on universes of (small) types. More than in other foundations of mathematics, such universes are critical for even proving such basic properties as 0 ≠ 1 [38]. This focus on universes is only intensified with homotopy type theory (HoTT) [39] where the universe is supplemented with the univalence axiom. Such univalent universes allow type theorists to view types as a synthetic incarnation of spaces (i.e., ∞-groupoids) with the intensional identity type a =_A b modeling paths in the type A. The utility of this viewpoint is demonstrated by development of synthetic homotopy theory inside of HoTT: a reconstruction of classical results in homotopy theory with simpler and more conceptual proofs.

A long-standing challenge in HoTT has been to broaden the reach of synthetic homotopy theory to include homotopy-coherent algebraic structures and, especially, the homotopical enhancement of category theory: (∞, 1)-category theory.¹ While numerous approaches to this problem have been proposed [1, 14, 17, 25–29, 33, 40–42] we will focus on the approach introduced by Riehl and Shulman [33]. There the authors leveraged a non-standard model of HoTT where types are realized by simplicial spaces. In particular,

they showed that the complete Segal spaces—a known model of ∞-categories [31]—then arise as certain types satisfying a pair of easily-defined properties. Thus, in this setting not every type is an ∞-category, but every ∞-category gives rise to a valid type.

Concretely, simplicial type theory extends HoTT with a directed interval, a postulated totally ordered lattice (I, 0, 1, ≤). This new type is meant to represent the ∞-category with two objects 0, 1 and a single non-identity morphism 0 → 1—an interpretation justified by the model of STT in simplicial spaces—and we then use I to define morphisms in an arbitrary type A as ordinary functions I → A. By constraining the endpoints of a synthetic morphism, we arrive at the definition of the space of synthetic morphisms in a type: hom_A(a, b) = Σ_{f:I→A} f 0 = a × f 1 = b.

Riehl and Shulman [33] then demonstrate that the definition of an ∞-category can be formulated concisely as a predicate isCat on types, essentially requiring every pair of composable morphisms have a unique composite. Furthermore, they show that ordinary functions between such types constitute functors and that other classical definitions in ∞-category theory become expressible. Subsequent work has further expanded this approach, developing fibered category theory [5, 43], limits and colimits [3], etc.

While not every type constitutes an ∞-category in STT, many type-theoretic operations preserve the property of being an ∞-category. For instance, 0 and 1 are the initial and terminal categories, A × B (A + B) is the (co)product category, and A → B is the category of functors. As an extension of HoTT, STT comes equipped with a (hierarchy of) universes and it is therefore natural to ask:

Is U a recognizable category, e.g., the category of categories?

Unfortunately, the answer is negative; U is the canonical example of a type that is not an ∞-category in STT. In fact, even if one considers simple subtypes of the universe (e.g., Σ_{A:U} isCat(A)) one does not obtain a category, as synthetic morphisms I → Σ_{A:U} isCat(A) neither compose nor faithfully represent functors. However, it has long been conjectured that the category of categories should be constructible in STT as a certain subtype of the universe.

We address this final gap in the foundations of STT by settling this conjecture affirmatively and constructing the category of categories as a subtype Cat ↩ U and verifying its essential properties.

### 1.1 Directed univalence and Cat

What criteria should be used to determine if a subtype Cat ↩ U is a valid definition of the category of categories? If one is not considering ∞-categories, the answer to this question is straightforward: Cat is a valid definition if the objects denote precisely small types satisfying isCat, synthetic morphisms are exactly functions (i.e., functors) between these types, and the composition and identity operations behave as expected. In the ∞-categorical case, the story does not end here; we must also convince ourselves that all the higher synthetic morphisms also behave "as expected". However, it is far from clear what the expected behavior ought to be! Instead,

¹In both the title and hereafter, we shall simply write "∞-category" or even "category" to refer to (∞, 1)-categories. If we wish to specifically discuss ordinary categories, we shall specifically denote them by 1-categories.