now form a formula “ $f = g$ ” in context $(x, y : \text{Ob}, f, g : \text{Hom}(x, y))$ which is defined as

$$(f = g) := (\exists v : \text{Eq}(f, g), \top).$$

Therefore, in the language $\mathcal{L}_\omega^{\text{Cat}_\omega}$ we can form formulas involving equality between parallel morphisms. Then, we recover the “language of categories” as studied in [Bla78] and [Fre76]. For example, we can form the formula “ $x$ is initial” in context $(x : \text{Ob})$ as

$$\text{isInitial}(x) := \forall y : \text{Ob}, (\exists f : \text{Hom}(x, y)) \wedge (\forall f, g : \text{Hom}(x, y), f = g).$$

**Construction 2.5.** If $f : \Delta \rightarrow \Gamma$ is a context morphism and $\phi \in \mathcal{L}_\lambda^T(\Gamma)$, then we can define its pullback $f^*\phi$. This pullback is obtained by substituting the free variables of $\phi$ by the components of $f$. Formally, this is defined inductively as:

1. $f^*\top := \top$ and $f^*\bot := \bot$.
2. $f^*(\neg\Phi) := \neg f^*\Phi$.
3. $f^*(\bigvee_{i \in I} \Phi_i) := \bigvee_{i \in I} f^*\Phi_i$ and $f^*(\bigwedge_{i \in I} \Phi_i) := \bigwedge_{i \in I} f^*\Phi_i$.
4. If $\Gamma' \equiv (\Gamma, x_1 \in X_1, \dots, x_\alpha \in X_\alpha)$ then

$$f^*(\exists(x_1 \in X_1, \dots, x_\alpha \in X_\alpha)\Phi) := \exists(x_1 \in f^*X_1, \dots, x_\alpha \in f^*X_\alpha)f^*\Phi,$$

$$f^*(\forall(x_1 \in X_1, \dots, x_\alpha \in X_\alpha)\Phi) := \forall(x_1 \in f^*X_1, \dots, x_\alpha \in f^*X_\alpha)f^*\Phi,$$

where $f^*X_i$ denotes the pullback of types, obtained by substitution, that is, the types appearing in the canonical pullback of the generalized display map:

$$(\Delta, f^*X_1, \dots, f^*X_\alpha) \longrightarrow (\Gamma, X_1, \dots, X_\alpha)$$
$$\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \Delta \longrightarrow \Gamma.$$

**Definition 2.6.** For each context $\Gamma$ in $T$ we define the relation $\vdash_\Gamma$ on $\mathcal{L}_\lambda^T(\Gamma)$ as the smallest family of relations such that:

1. $\vdash_\Gamma$ is a transitive and reflexive relation on $\mathcal{L}_\lambda^T(\Gamma)$.
2. $\forall \Phi \in \mathcal{L}_\lambda^T(\Gamma)$, $\Phi \vdash_\Gamma \top$ and $\bot \vdash_\Gamma \Phi$.

11