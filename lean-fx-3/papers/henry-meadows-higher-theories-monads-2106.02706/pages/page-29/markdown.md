**Proposition 4.8.** *Let $X^{\bullet}$ and $Y^{\bullet}$ be two functors $\mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ as in Assumption 4.4. Let $\lambda : X^{\bullet} \rightarrow Y^{\bullet}$ be a natural transformation between them such that:*

1. *For each object $d \in \mathcal{D}$, the functor $\lambda(d) : X^d \rightarrow Y^d$ sends $X_d$ to $Y_d$.*
2. *For each morphism $f : d' \rightarrow d$ in $\mathcal{D}$, the natural transformation $\lambda(d)f_! \rightarrow f_!\lambda(d')$ obtained from the naturality square $\lambda(d')f^* \xrightarrow{\sim} f^*\lambda(d)$ through the partial adjunction between $f_!$ and $f^*$, is an isomorphism.*

*Then, there is a natural transformation $\lambda' : X_{\bullet} \rightarrow Y_{\bullet}$ between the functors $\mathcal{D} \rightarrow \mathbf{Cat}_{\infty}$ constructed in Proposition 4.5, which on objects is the restriction of $\lambda$ and whose naturality isomorphism is the natural isomorphism $\lambda(d)f_! \rightarrow f_!\lambda(d')$ mentioned above.*

*Proof.* Let $\mathcal{X}, \mathcal{Y} \rightarrow \mathcal{D}$ be the cartesian fibrations corresponding to $X, Y : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$. And let $\mathcal{X}', \mathcal{Y}' \rightarrow \mathcal{D}$ be the cocartesian fibration constructed in the proof of Proposition 4.5.

By functoriality of the Grothendieck (or unstraightening) construction, the natural transformation $\lambda$ induces a functor $V : \mathcal{X} \rightarrow \mathcal{Y}$ in $(\mathbf{Cat}_{\infty})_{/\mathcal{D}}$ that preserves cartesian arrows. Assumption 1, immediately shows that $V$ restricts to a functor $\mathcal{X}' \rightarrow \mathcal{Y}'$ (also in $(\mathbf{Cat}_{\infty})_{/\mathcal{D}}$). Assumption 2 translates to the fact that this functor sends cocartesian arrows to cocartesian arrows. Indeed, by uniqueness of cocartesian lifts, any cocartesian arrow in $\mathcal{X}$ is up to equivalence an arrow $(d, x) \rightarrow (d', f_!x)$ over $f : d \rightarrow d' \in \mathcal{D}$ corresponding to the unit of adjunction $x \rightarrow f^*f_!x$ as in the proof of Proposition 4.5, for $x \in X_d$. The functor $V$ sends such an arrow to the arrow $(d, \lambda^d(x)) \rightarrow (d, \lambda^{d'}f_!x)$. This in turn corresponds to $\lambda^d x \rightarrow f^*\lambda^{d'}f_!x$ which is the image of the co-unit $x \rightarrow f^*f_!x$ under $\lambda^d$ up to the isomorphism $\lambda^d f^* \simeq f^*\lambda^{d'}$. Under assumption (2), this maps identifies with the counit $\lambda^d(x) \rightarrow f^*f_!\lambda^d(x)$ and hence corresponds to a cocartesian arrow of $\mathcal{Y}'$.

As $V$ preserves cocartesian arrows from $\mathcal{X}'$ to $\mathcal{Y}'$, it corresponds to a natural transformation between the functors constructed in Proposition 4.5 with the properties claimed in the proposition. $\square$

**Proposition 4.9.** *Let $X^{\bullet} : \mathcal{D}^{op} \rightarrow \mathbf{Cat}_{\infty}$ be a functor with subcategories $X_{\bullet}$ as in Proposition 4.5. Then there are natural transformation:*

$$(\mathcal{X}_d)^{op} \rightarrow \operatorname{Fun}(\mathcal{X}^d, \mathcal{S})$$

29