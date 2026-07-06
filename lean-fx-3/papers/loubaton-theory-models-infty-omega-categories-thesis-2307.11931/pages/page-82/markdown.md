CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

2.1.2.4. The category of $M$-stratified presheaves is then equivalent to the fully faithful subcategory of presheaves $X$ on $t_M B$ such that for any $b \in M$, $X(b_t) \to X(b)$ is a monomorphism. In particular, we have an adjunction

$$\pi : \mathrm{Psh}(t_M B) \xrightarrow{\perp} \mathrm{tPsh}_M(B) : \iota \tag{2.1.2.5}$$

Remark furthermore that the unit $X \to \iota\pi X$ is a trivial fibration. Indeed, the cellular model is given $C \cup \{b \to b_t, b \in M\}$, where $C$ is a cellular model for $B$, and the unit obviously has the right lifting property against it.

**Proposition 2.1.2.6.** *Suppose given a combinatorial on $\mathrm{Psh}(t_M B)$ whose cofibrations are monomorphisms. Then there exists a combinatorial model structure on $\mathrm{tPsh}_M(B)$ making the adjunction 2.1.2.5 a Quillen equivalence.*

*A morphism of $\mathrm{tPsh}_M(B)$ is a cofibration if and only if it is a monomorphism. A morphism is a fibration (resp. a weak equivalence) if and only if its image by $\iota$ is.*

*Proof.* We are willing to apply [Hir03, theorem 11.3.2]. As two adjoints of (2.1.2.5) preserve smallness, the first condition is obviously fulfilled. Using the fact that $\iota$ is fully faithful, the second condition of theorem *op cit* is equivalent to asking that for any acyclic cofibration $i$ of $\mathrm{Psh}(t_M B)$, the morphism $\iota\pi i$ is a weak equivalence. As the unit $id \to \iota\pi$ is pointwise a trivial fibration, this directly follows from the stability of weak equivalences by two out of three.

This provides the model structure. As the unit is pointwise a trivial fibration and the counit is the identity, the adjunction (2.1.2.5) induces a Quillen equivalence. $\square$

2.1.2.7. We now fix a Reedy category $B$, a subset $M$ of objects of $B$, and we suppose given a nice model structure on $\mathrm{tPsh}_M(B)$ (as defined in paragraph 2.1.1.8). A $M$-marked presheaf on $B$ is a stratified presheaf having the unique right lifting property against all entire acyclic cofibrations. In particular, any fibrant objects is marked.

We denote by $\mathrm{mPsh}_M(B)$ the full subcategory of marked presheaves on $B$. We then have an adjunction:

$$(\_)_{\mathrm{mk}} : \mathrm{tPsh}_M(B) \xrightarrow{\perp} \mathrm{mPsh}_M(B) : \iota \tag{2.1.2.8}$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified presheaf $(X, tX)$ to the marked presheaf $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked presheaf, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of presheaves, these two adjoints are the identity.

**Proposition 2.1.2.9.** *Let $X$ be a $M$-stratified presheaf on $B$. The canonical morphism $X \to \iota(X_{\mathrm{mk}})$ is an entire acyclic cofibration.*

72