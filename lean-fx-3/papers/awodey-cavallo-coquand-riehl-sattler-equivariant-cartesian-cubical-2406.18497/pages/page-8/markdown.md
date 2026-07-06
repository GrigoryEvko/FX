these classifiers have fibrant base objects (Proposition 5.3.9) and are univalent (Proposition 5.3.8).

The former property is closely connected to the model-categorical *fibration extension property* (Proposition 5.3.10), the latter to the *equivalence extension property* (Proposition 5.3.1).

The main technical work lies in the construction of univalent universes.

In the course of proving the main theorem, we actually construct *two* models of homotopy type theory and associated Quillen model structures: a model on the category $\mathsf{cSet}^{\Sigma}$ of cubical species, which does not model classical homotopy theory, and a model on $\mathsf{cSet}$, which does. To avoid repetition and with an eye towards future applications, we prove the core theorems that will establish the necessary properties of these model categories in more general axiomatic settings, proving results that are of independent interest.

1.6.1. *Outline.* Our development proceeds as follows.

- In §2, we recall Shulman's *notions of fibred structure*, which in particular include categories of right maps obtained from an algebraic weak factorization system. Again following Shulman, we define a *universe* for a notion of fibred structure to be a representable "resolution" via an acyclic fibration. We define our first example of a notion of fibred structure, the *uniform trivial fibrations*, following [Awo26].
- In §3, we work in the abstract setting of a *cylindrical premodel structure* as defined in [Sat20; CS25, §3]. We establish, individually, sufficient conditions under which a cylindrical premodel structure
  - satisfies the equivalence extension property;
  - satisfies the Frobenius condition,
  - supports fibrant and univalent universes of fibrations;
  - defines a Quillen model structure.

These constructions form the backbone of existing model-categorical cubical interpretations and could be applied with appropriate inputs from [ABCHFL21] or [Awo26] to recover the known model structures on, e.g., cartesian or De Morgan cubical sets. In the following sections, we apply them to two cylindrical premodel structures: first to $\mathsf{cSet}^{\Sigma}$ and then to $\mathsf{cSet}$ itself. As a rule of thumb, properties whose proofs rely only on *closure* properties of fibrations (such as the equivalence extension property) are derived directly in $\mathsf{cSet}$, while properties whose proofs rely on the *generation* of fibrations by box filling (such as the Frobenius condition) are first proven in $\mathsf{cSet}^{\Sigma}$ and then transferred to $\mathsf{cSet}$.

- In §4, we introduce the category $\mathsf{cSet}^{\Sigma}$ of cubical species. We define the *symmetric interval* $\mathbb{I} \in \mathsf{cSet}^{\Sigma}$ and use it to define, by essentially the same construction used for the ordinary cartesian cubical set model [ABCHFL21; CMS20; Awo26], a model of HoTT and Quillen model structure on $\mathsf{cSet}^{\Sigma}$.
- In §5, we transfer the cylindrical premodel structure on $\mathsf{cSet}^{\Sigma}$ to $\mathsf{cSet}$ by means of the constant functor $\Delta: \mathsf{cSet} \to \mathsf{cSet}^{\Sigma}$, defining the equivariant (trivial) fibrations to be those sent to (trivial) fibrations in $\mathsf{cSet}^{\Sigma}$ by $\Delta$. We show that this premodel structure satisfies 2-of-3, proving the first part of Theorem 1.6.1: the existence of a constructively definable model of HoTT and associated Quillen model structure on $\mathsf{cSet}$ whose fibrations are the equivariant fibrations.
- In §6, we prove the second part of Theorem 1.6.1, building a Quillen equivalence between the equivariant model structure on $\mathsf{cSet}$ and the Kan–Quillen model structure on $\mathsf{sSet}$. The left adjoint of this equivalence is the triangulation functor $T: \mathsf{cSet} \to \mathsf{sSet}$ mentioned above; we rely on a characterization, due to Reid Barton, of $T$ as restriction along a functor $i: \Delta \to \square$. Key to the proof is that $\Delta$ and $\square$ are *Eilenberg–Zilber categories*, which implies that the monomorphisms in their respective presheaf categories are cell complexes of quotients by automorphism groups of boundary inclusions into representables. In this way, the fact that $T$ reflects weak equivalences comes to rest on the contractibility of the quotients $I/H \in \mathsf{cSet}$, which we have seen in §1.5.2 is

8