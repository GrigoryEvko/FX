5:2

E. CAVALLO AND R. HARPER

Vol. 17:4

from being a contrived counter-model, the groupoid model demonstrates that contentful equality arises quite naturally in mathematics. Hofmann and Streicher highlight isomorphism as the premiere example: two isomorphic sets are essentially “the same”, but the same two sets can be isomorphic in many different ways. Awodey and Warren [War08, AW09] and van den Berg and Garner [vdBG12] generalized the groupoid model construction to produce models where there are not only distinct proofs of identities, but distinct proofs of identities between proofs of identities and so on. Voevodsky, who was separately developing a simplicial model with similar properties [KL12], proposed to extend ITT with his univalence axiom, which asserts precisely that identifications between types correspond to isomorphisms.

Voevodsky’s univalence axiom codifies a kind of reasoning that is already ubiquitous in informal mathematics, that of treating isomorphic objects as interchangeable. In fact, the axiom has far-reaching consequences, as subsequently explored in the fields of homotopy type theory [Uni13] and univalent foundations [Voe15, VAG+]. As a simple but characteristic example, it implies function extensionality as a corollary: functions are identical when they are identical on all arguments [Uni13, §4.9]. Analogous extensionality principles for equality in conductive types (e.g., [ACS15]) and quotients (e.g., [KvR19]) follow as well. In short, univalence regularizes the behavior of equality throughout type theory.

Of course, there is one sense in which univalent ITT is spectacularly ill-behaved: by introducing an axiom, we destroy the computational content of type theory. There is no way to run a program written in ITT that uses the univalence axiom, because the “proof” of the axiom does not compute. This was finally addressed by the development of cubical type theories [CCHM15, AFH18, OP18, ABC+19, CMS20], a family of univalent type theories (with constructive models) where the univalence axiom follows from more fundamental primitives that do compute. The central principle of cubical type theory is that equalities in a type A—now called paths—are represented by maps from an interval object I into A.

Cubical type theory will be our starting point, our setting to explore contentful equality. In this work, we develop internal parametricity as an effective tool to reason about contentful equality, which—despite its remarkable usefulness—presents new difficulties as well.

The challenges of contentful equality. As users of ITT have long known, a lack of uniqueness of identity proofs has some frustrating consequences. To put it pithily, when equalities are not always equal, we sometimes need to prove that they are. For example, we typically need to know that composition of equalities (i.e., transitivity) is associative. When we have contentful equality in mind, these “coherence” proofs are mathematically significant, but their proofs are often tedious, uninteresting, and difficult to conceptualize, especially as one gets to the point of proving equalities between equalities between equalities.

The problem is most acute when we work with quotients. In cubical type theory, as in homotopy type theory and the univalent foundations, inductive types and quotient types both arise as specializations of higher inductive types [Uni13, CHM18, CH19a]. Where an inductive type is defined by constructors that generate elements of the type, a higher inductive type is defined by a specification of element and path constructors. As a simple example, we can specify the type $\mathbb{Z}/2\mathbb{Z}$ of integers mod 2 in cubical type theory as the following higher inductive type.

data $\mathbb{Z}/2\mathbb{Z}$ where
| in(n : $\mathbb{Z}$) $\in$ $\mathbb{Z}/2\mathbb{Z}$
| mod(n : $\mathbb{Z}$, x : $\mathbb{I}$) $\in$ $\mathbb{Z}/2\mathbb{Z}$ [x = 0 $\hookrightarrow$ in(n) | x = 1 $\hookrightarrow$ in(n + 2)]