2.1. PRELIMINARIES

Suppose first that $a$ is in $B$. In this case, $f$ and $g$ are also in $B$, and as this Reedy category is elegant by assumption, this implies $f = g$ and $y = z$. Suppose now that $a$ is of shape $b_t$ for $b \in B$. We denote by $\alpha$ the canonical morphism $\alpha : b \to b_t$. By definition of negative morphism, the codomain of $f$ and $g$ are in $B$. The morphisms $\alpha f$ and $\alpha g$ then are in $B$. Moreover, these two morphisms are negative, and we have $(\alpha f)^* y = \alpha^* x$, $(\alpha g)^* z = \alpha^* x$. As $B$ is elegant, $\alpha f = \alpha g$ and $y = z$. Eventually, remark that the first equality implies that $f$ is equal to $g$. $\square$

**Remark 2.1.2.7.** A cellular model for $t_M B$ is given by $C \cup \{b \to b_t, b \in M\}$ where $C$ is a cellular model for $B$.

**Proposition 2.1.2.8.** *Suppose given a combinatorial model structure on $\mathrm{Psh}(t_M B)$ whose cofibrations are monomorphisms. Then there exists a combinatorial model structure on $\mathrm{tPsh}_M(B)$ making the adjunction 2.1.2.5 a Quillen equivalence.*

*A morphism of $\mathrm{tPsh}_M(B)$ is a cofibration if and only if it is a monomorphism. A morphism is a fibration (resp. a weak equivalence) if and only if its image by $\iota$ is.*

*Proof.* We are willing to apply [Hir03, theorem 11.3.2]. As two adjoints of (2.1.2.5) preserve smallness, the first condition is obviously fulfilled. Using the fact that $\iota$ is fully faithful, the second condition of theorem *op cit* is equivalent to asking that for any acyclic cofibration $i$ of $\mathrm{Psh}(t_M B)$, the morphism $\iota \pi i$ is a weak equivalence.

However, remark that the unit $X \to \iota \pi X$ is a trivial fibration. Indeed, a cellular model is given $C \cup \{b \to b_t, b \in M\}$, where $C$ is a cellular model for $B$, and the unit obviously has the right lifting property against it. The result then directly follows from the stability of weak equivalences by two out of three.

This provides the model structure. As the unit is pointwise a trivial fibration and the counit is the identity, the adjunction (2.1.2.5) induces a Quillen equivalence. $\square$

We now fix a Reedy category $B$, a subset $M$ of objects of $B$, and we suppose given a nice model structure on $\mathrm{tPsh}_M(B)$ (as defined in definition 2.1.1.6).

**Definition 2.1.2.9.** A $M$-marked presheaf on $B$ is a stratified presheaf having the unique right lifting property against all entire acyclic cofibrations. In particular, any fibrant objects is marked.

We denote by $\mathrm{mPsh}_M(B)$ the full subcategory of marked presheaves on $B$. We then have an adjunction:

$$
(\_)_{\mathrm{mk}} : \mathrm{tPsh}_M(B) \xrightarrow{\perp} \mathrm{mPsh}_M(B) : \iota \tag{2.1.2.10}
$$

where the left adjoint $(\_)_{\mathrm{mk}}$ sends a stratified presheaf $(X, tX)$ to the marked presheaf $(X, \overline{tX})$, where $\overline{tX}$ is the smaller stratification that includes $tX$ and makes $(X, \overline{tX})$ a marked presheaf, and where the right adjoint is a fully faithful inclusion. Remark furthermore that at the level of presheaves, these two adjoints are the identity.

**Proposition 2.1.2.11.** *Let $X$ be a $M$-stratified presheaf on $B$. The canonical morphism $X \to \iota(X_{\mathrm{mk}})$ is an entire acyclic cofibration.*

67