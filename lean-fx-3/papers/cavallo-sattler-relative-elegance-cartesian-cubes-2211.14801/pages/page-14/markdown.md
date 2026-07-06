14

E. Cavallo and C. Sattler

### 3 Model structures from cubical models of type theory

As the cube category $\square_{\nu}$ is cartesian, we may obtain our cubical-type model structure on PSh($\square_{\nu}$) immediately by applying existing arguments [CMS20; Awo23], which build on a criterion for recognizing model structures introduced in the first part of [Sat17]. We will instead take the opportunity to present an improvement on the latter criterion, hoping to give an idea of the character of these model structures along the way.

We begin in Section 3.1 with a set of conditions necessary and sufficient to determine when a premodel structure—essentially, all the ingredients of a model structure except 2-out-of-3 for weak equivalences—is in fact a model structure. In Section 3.2, we give a simplified set of conditions for the case where the premodel structure is equipped with a compatible adjoint functorial cylinder. Finally, in Section 3.3 we show that such a cylindrical premodel structure satisfies these conditions when all its objects are cofibrant and it satisfies the fibration extension property. We shall apply this result in Section 4.2 to obtain our model structure on PSh($\square_{\nu}$); a reader who would prefer to take the existence of the model structure for granted may skip this section and read only Theorem 4.34 in Section 4.2.

### 3.1 Model structures from premodel structures

Definition 3.1 (Bar19, Definition 2.1.23) A premodel structure on a finitely complete and cocomplete category $\mathbf{M}$ consists of weak factorization systems $(C, \mathcal{F}_t)$ (the cofibrations and trivial fibrations) and $(C_t, \mathcal{F})$ (the trivial cofibrations and fibrations) on $\mathbf{M}$ such that $C_t \subseteq C$ (or equivalently $\mathcal{F}_t \subseteq \mathcal{F}$).

Remark 3.2 (Stability under (co)slicing) Given an object $X \in \mathbf{M}$, any weak factorization system on $\mathbf{M}$ descends to weak factorization systems on the slice over $X$ and the coslice under $X$, with left and right classes created by the respective forgetful functor to $\mathbf{M}$. In the same fashion, any premodel structure on $\mathbf{M}$ descends to slices and coslices of $\mathbf{M}$.

As any two of the classes $(C, \mathcal{W}, \mathcal{F})$ defining a model structure determines the third, any premodel structure induces a candidate class of weak equivalences.

Definition 3.3 We say that a morphism in a premodel structure is a weak equivalence if it factors as a trivial cofibration followed by a trivial fibration; we write $\mathcal{W}(C, \mathcal{F})$ for the class of such morphisms.

Remark 3.4 The above definition is only necessarily appropriate when examining when a premodel structure forms a model structure: there are premodel structures with a useful definition of weak equivalence not agreeing with $\mathcal{W}(C, \mathcal{F})$. For example, there are various weak model structures on semisimplicial sets in which not all trivial fibrations are weak equivalences [Hen20, Remark 5.5.7].

For the remainder of this section, we fix a premodel category $\mathbf{M}$ with factorization systems $(C, \mathcal{F}_t)$ and $(C_t, \mathcal{F})$. The following two propositions are standard.

2025/10/16 00:43