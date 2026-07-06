show that $\exists$ and $\forall$ define left and right adjoints to $\pi^*$. Finally, the Beck-Chevalley condition follows from how $f^*$ is defined on formulas starting with a $\exists$ quantifier:

$$f^*(\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \exists\{x_\beta : f^*\Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}f^*\Phi,$$

which (after passing to the quotient $\mathcal{L} \rightarrow \mathbb{L}$) exactly says that $f^*\exists_\pi = \exists\pi f^*$ where $\pi$ is the generalized display map corresponding to forgetting the variables $\{x_\beta\}_{\gamma \leqslant \beta < \alpha} \in X_\alpha$.

We now check that it is an initial object in the category of $\lambda$-boolean algebras over $\mathcal{C}_T$. Let $\mathcal{B}$ be any $\lambda$-boolean algebra over $\mathcal{C}$. Any morphism $v : \mathbb{L}_\lambda^T \rightarrow \mathcal{B}$ has to satisfy:

1. $v(\perp) = \perp_\mathcal{B}$ and $v(\top) = \top_\mathcal{B}$.
2. $v(\neg\Phi) = \neg v(\Phi)$.
3. $v(\bigvee_{i \in I} \Phi_i) = \bigvee_{i \in I} v(\Phi_i)$ and $v(\bigwedge_{i \in I} \Phi_i) = \bigwedge_{i \in I} v(\Phi_i)$.

4.

$$v(\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}v(\Phi)$$

and

$$v(\forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}\Phi) = \forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha}v(\Phi).$$

These form an inductive definition for a function $\mathcal{L}_\lambda^T \rightarrow \mathcal{B}$. So there is a unique such function $v : \mathcal{L}_\lambda^T \rightarrow \mathcal{B}$. To conclude, we only need to check that this function $v$ descends to a function $\mathbb{L}_\lambda^T \rightarrow \mathcal{B}$ and is a morphism of $\lambda$-boolean algebras over $\mathcal{C}$. But this is rather immediate: We first observe, by induction over theorem 2.6, that if $\Phi \vdash \Psi$ then $v(\Phi) \leqslant v(\Psi)$. This implies that if $\Phi \dashv \Psi$ then $v(\Phi) = v(\Psi)$, so $v$ does define a function $\mathbb{L}_\lambda^T \rightarrow \mathcal{B}$. The naturality condition

$$v(f^*(\Phi)) = f^*(v(\Phi))$$

can be proved by induction on the formula $\Phi$, and the compatibility of $v$ with all the boolean algebra operations and the quantifiers follows immediately from the definition of $v$. $\square$

**Proposition 2.24.** *Given any (small) clan $\mathcal{C}$ and $\lambda$ a regular cardinal, there is an initial $\lambda$-boolean algebra over $\mathcal{C}$, which we denote by $\mathbb{L}_\lambda^\mathcal{C}$.*

20