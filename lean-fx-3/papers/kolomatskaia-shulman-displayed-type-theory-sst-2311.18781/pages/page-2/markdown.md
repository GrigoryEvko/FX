|  4 Semantics | 39  |
| --- | --- |
|  4.1 The semantics of dependent type theory | 40  |
|  4.2 The simplicial model | 51  |
|  4.3 Modalities | 63  |
|  4.4 Semantics of dTT | 74  |
|  4.5 Semantics of semi-simplicial types | 80  |
|  5 Conclusion and Future Work | 97  |
|  A Verifications for the Simplicial Model | 103  |
|  A.1 Variables | 103  |
|  A.2 Π-types | 104  |
|  A.3 Universes | 105  |
|  A.4 ω-limits | 106  |

# 1 Introduction

Semi-simplicial types. Homotopy Type Theory (HoTT) [Uni13] is a perspective on intensional dependent type theory that regards types as homotopical spaces or ∞-groupoids. It has proven remarkably successful as a synthetic context in which to do homotopy theory and algebraic topology, and as an internal language for (∞, 1)-toposes [Shu19]. However, an enduring frustration has been its apparent inability to define general homotopy-coherent structures. Some infinite structures can be defined in HoTT, such as globular types and spectra; but others, such as A∞-spaces or (∞, 1)-categories, have so far resisted all attempts at definition. We know no convincing explanation for why they should be impossible, but the fact that all attempts appear to fail in a similar way suggests the operation of an as-yet-unarticulated principle.

Specifically, stating an 'infinite coherence' property generally seems to require an infinite structure within which to assemble the coherences, while defining such a structure itself seems to require infinite coherence, leading to an infinite regress. This is in contrast to the situation in classical homotopy theory where the infinite structures to describe coherence, such as operads and simplicial diagrams, can themselves be defined using strict point-set-level equalities, which are then automatically fully coherent. It is tempting to try to mimic this in homotopy type theory using definitional equalities in place of point-set ones, but this is difficult because definitional equality is not reified in the theory and we have limited tools for forcing it to hold.

One of the more flexible ways to enforce definitional equalities is to use type dependency, moving from a fibred perspective to an indexed one. In the simplest case, this means replacing a function p : E → B with a type family Ē : B → Type. This has a corresponding projection function π₁ : Σ Ē → B, but we can suppose a point ē : Σ Ē with a definitional equality π₁ ē ≡ b by supposing a point e : Ē b and letting ē = {b, e}.

Thus, it is natural to try to define infinitely coherent structures that can be expressed in a purely indexed way. The example of this sort which has attracted the most attention is that of semi-simplicial types, because they are well-known within homotopy theory and

2