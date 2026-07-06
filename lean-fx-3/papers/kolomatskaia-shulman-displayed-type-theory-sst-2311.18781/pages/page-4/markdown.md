even this problem is still unsolved: every attempt to internally encode the combinatorics that generate the type of $A_n$, as a function of $n$, seems to lead once again to an infinite regress.

In light of this situation, an alternative approach is to formulate more expressive type theories that can solve the problem of infinitely coherent objects. One such proposal is Two-Level Type Theory (2LTT) [ACKS23], which introduces an 'outer level' of 'exo-types' that are not homotopy-invariant. The exo-types admit a strict exo-equality type, essentially reifying definitional equality, which can then be used analogously to classical point-set equality to define infinitely coherent structures. And by the results of [Usk23], 2LTT can be interpreted in any $(\infty, 1)$-topos, so its semantics are not significantly less general than ordinary HoTT, and the type SST defined in 2LTT does interpret to the correct classifier. However, although the exo-equality is assumed to satisfy Uniqueness of Identity Proofs, to keep type-checking decidable it cannot satisfy a reflection rule making exo-equalities into definitional equalities. Thus, it can be quite cumbersome to work with in practice.

Another proposal is Simplicial Type Theory (STT) [RS17], which changes perspective to view individual types as simplicial spaces, with additional primitives for manipulating the simplicial structure. One can then simply impose conditions on one of these 'simplicial types' to make it represent (for instance) an $(\infty, 1)$-category. This suggests a 'synthetic' approach to higher category theory analogous to ordinary HoTT's synthetic approach to homotopy theory, which is potentially quite powerful; and the results of [RS17, Wei22] imply that it can be interpreted in the category of simplicial objects in any $(\infty, 1)$-topos. However, the strength of the synthetic approach is also its weakness: because simplicial types are postulated rather than defined, what we can do with them is limited to what is expressed by the axiomatization.

A coinductive definition of semi-simplicial types. In this paper we propose a third enhancement of homotopy type theory, called Displayed Type Theory (dTT), in which it is possible to define and work with semi-simplicial types (and many other things). This type theory is inspired by the following idea for a coinductive definition of a type SST of semi-simplicial types:

Idea 1.2. A semi-simplicial type A consists of

- a type Z A, and
- for each x : Z A, a semi-simplicial type S A x over A.

It may not be at all obvious why this should be a definition of semi-simplicial types, so let us unravel it a few steps:

0. Every semi-simplicial type A has a type Z A, whose points we call 0-simplices of A. Thus we may also write $A_0 = Z A$.
1. Every 0-simplex x : $A_0$ gives rise to a semi-simplicial type S A x over A, called the slice of A over x. Of course, if we don't know what a semi-simplicial type is, we can't be expected to know what one semi-simplicial type over another one is — at least, not completely. But we do know that every semi-simplicial type A has an underlying type Z A, so it stands to reason that a semi-simplicial type B over A should in particular have an underlying type $Z^d B$ over Z A, i.e. a type family $Z^d B : Z A \to \text{Type}$. Thus, in

4