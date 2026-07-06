- • $3^{rd}$ **invariance theorem:** Let $A, B \in \mathcal{M}$ two cofibrant objects of a weak Quillen model category $\mathcal{M}$ and $f: A \to B$ a weak equivalence between them. Then the map $f^*: \mathbb{L}_\lambda(B) \to \mathbb{L}_\lambda(A)$ induces a bijection

$$h\mathbb{L}_\lambda(B) \simeq h\mathbb{L}_\lambda(A).$$

- • $4^{th}$ **invariance theorem:** If $F: \mathcal{M} \to \mathcal{N}$ is a left Quillen equivalence between two weak model categories, then for any cofibrant object $A \in \mathcal{M}$ the induced map

$$h\mathbb{L}F_A: h\mathbb{L}_\lambda^{\mathcal{M}}(A) \to h\mathbb{L}_\lambda^{\mathcal{N}}(FA)$$

from theorem 4.5 is an isomorphism.

**Remark 4.3.** Note that if $F: \mathcal{M} \rightleftarrows \mathcal{N}: G$ a Quillen equivalence between weak model categories and $B$ is a cofibrant object of $\mathcal{N}$ which is not of the form $F(A)$ for $A \in \mathcal{M}$, then one can still use the $4^{th}$ invariance theorem to transfer a formula in $h\mathbb{L}(B)$ to a formula in $\mathcal{M}$. We do this by first finding an object of the form $F(A)$ which is homotopically equivalent to $B$, which is always possible as $F$ is a Quillen equivalence, and then transferring our formula $\phi \in h\mathbb{L}(B)$ to a formula in $h\mathbb{L}(F(A))$ using the $3^{rd}$ invariance theorem.

**Observation 4.4.** For any cofibrant object $\Gamma \in \mathcal{M}$, $\phi, \psi \in \mathbb{L}_\lambda^{\mathcal{M}}(\Gamma)$ we defined $\phi \approx \psi$ if and only if $|\phi|_X = |\psi|_X$ for all fibrant objects. However, note that if we take a cofibrant replacement $X^{\mathrm{COF}}$ of $X$, then by theorem 2.38 ($2^{nd}$ invariance theorem) we have, $X \vdash \phi(fv)$ if and only if $X^{\mathrm{COF}} \vdash \phi(v)$, where $f: X^{\mathrm{COF}} \xrightarrow{\sim} X$ and $v: \Gamma \to X^{\mathrm{COF}}$.

Therefore, when testing the relation $\approx$, it is enough to use bifibrant objects. More precisely, define $\phi \approx_b \psi$ if $|\phi|_X = |\psi|_X$ for any bifibrant object $X$. Then

$$\phi \approx \psi \text{ if and only if } \phi \approx_b \psi.$$

We now explain the construction of the map $h\mathbb{L}F_A: h\mathbb{L}_\lambda^{\mathcal{M}}(A) \to h\mathbb{L}_\lambda^{\mathcal{N}}(FA)$ mentioned in the $4^{th}$ invariance theorem.

**Construction 4.5.** The map $h\mathbb{L}F_A$ in the $4^{th}$ invariance theorem is the map coming from $\mathbb{L}F_A: \mathbb{L}_\lambda^{\mathcal{M}}(A) \to \mathbb{L}_\lambda^{\mathcal{N}}(FA)$ constructed in theorem 2.40. It just comes from the fact that $\mathbb{L}_\lambda^{\mathcal{M}}$ is the initial boolean algebra. Recall that it satisfies the formula:

$$G(X) \vdash \phi(v) \Leftrightarrow X \vdash F(\phi)(\tilde{v}).$$

57