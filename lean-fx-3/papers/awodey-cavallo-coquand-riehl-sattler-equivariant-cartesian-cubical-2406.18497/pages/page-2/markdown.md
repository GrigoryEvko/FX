|  6. The equivalence with classical homotopy theory | 61  |
| --- | --- |
|  6.1. Triangulation | 62  |
|  6.2. Eilenberg–Zilber categories | 69  |
|  6.3. The equivariant model structure is the test model structure | 74  |
|  Appendix A. Type-theoretic development and formalization | 75  |
|  A.1. Introduction | 75  |
|  A.2. Judgments of the homotopical interpretation | 77  |
|  A.3. Cubes and cofibrations | 77  |
|  A.4. Partial elements and contractible types | 78  |
|  A.5. Filling and equivariant filling | 78  |
|  A.6. The Frobenius condition | 79  |
|  A.7. Other type formers | 80  |
|  A.8. Tiny interval and universes | 81  |
|  References | 83  |

## 1. INTRODUCTION

1.1. **Interpreting homotopy type theory.** Martin-Löf's dependent type theory [ML75; NPS01] provides a foundation for constructive mathematics. It functions both as a formal language for mathematical arguments and as a programming language: proofs of mathematical statements in Martin-Löf type theory can be regarded as functions or algorithms with computational content. At the turn of the 21st century, higher-dimensional and ultimately homotopical interpretations of Martin-Löf type theory were discovered [HS97; AW09; BG12; KL21]. The novelty of these interpretations is concentrated in their treatment of *identities*, i.e. equalities: an identity between two elements of a type is interpreted as a *path* or higher cell connecting them. *Homotopy type theory* (HoTT) or *univalent foundations* (UF) [UF13] refers to the formal system of Martin-Löf type theory augmented by Voevodsky's *univalence axiom*, which asserts that a certain canonical map is an equivalence

$$(A =_U B) \simeq (A \simeq B) \quad (1.1.1)$$

between the type $A =_U B$ of identities between types $A, B$ in a universe $U$ and the type $A \simeq B$ of homotopy equivalences between them.

To establish the consistency of the univalence axiom with the rules of Martin-Löf type theory (relative to the consistency of the rest of mathematics), Voevodsky [KL21] built a model of homotopy type theory using the standard model of homotopy theory in simplicial sets. The construction makes use of the *Quillen model structure* on simplicial sets [Qui67], which exhibits this category as a setting for abstract homotopy theory. In particular, dependent type families are interpreted as the fibrations of this model structure (the *Kan fibrations*), and the interpretations of type formers rely on established properties of the model structure; for example, the interpretation of $\Pi$-types rests on the fact that the model structure is *right proper* [KL21, 2.3.1].

Voevodsky's definition of the model relies on classical principles of reasoning such as the law of excluded middle and the axiom of choice, a surprising dependency given the constructive character of type theory itself. Bezem, Coquand, and Parmann [BC15; BCP15; Par18] showed that components of the model are in fact inherently non-constructive (though see §1.7.3 below). Thus one is also interested in finding models that can be defined using only constructively valid reasoning. Such a model would, in particular, construct an explicit equivalence inverse to the map (1.1.1), supplying computational content to proofs that invoke the univalence axiom.

2