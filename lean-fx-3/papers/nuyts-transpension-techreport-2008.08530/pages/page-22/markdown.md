$$\begin{aligned} \text{drop}_U^{W_0}(W, \psi) &= \text{drop}_U W : \exists_U^{W_0} \neg_U^{W_0}(W, \psi) \to (W, \psi), \\ \text{copy}_U^{W_0}(V, \varphi) &= \text{copy}_U(V, \pi_2 \circ \varphi) : (V, \varphi) \to \neg_U^{W_0} \exists_U^{W_0}(V, \varphi). \end{aligned}$$

*Proof.* Note that a slice category over a slice category is just a slice category, i.e. $(\mathcal{C}/y)/(x, \varphi) \cong \mathcal{C}/x$. In this light, the functor $\neg_U^{W_0}$ is not just the action of $\sqcup \ltimes U$ on slice objects over $W_0$, but also the action of $\neg_U$ on slice objects over $W_0$. Now since $\neg_U$ has left adjoint $\exists_U$, we get a left adjoint to $\neg_U^{W_0}$ by proposition 2.1.7. $\square$

**Proposition 3.5.9** (Functoriality of the slice category). A morphism of multipliers $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma^{W_0 \ltimes v} \circ \neg_U^{W_0} \to \neg_U^{W_0}$. Hence, if both multipliers are $\top$-slice (or equivalently slicewise) right adjoint, we also get $\exists_U^{W_0} \circ \Sigma^{W_0 \ltimes v} \to \exists_U^{W_0}$.

*Proof.* For any $(W, \psi) \in \mathcal{W}/W_0$, we have to prove $(W \ltimes U, (W_0 \ltimes v) \circ (\psi \ltimes U)) \to (W \ltimes U', \psi \ltimes U')$. The morphism $W \ltimes v : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1. $\square$

**Theorem 3.5.10** (Slicewise quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice (or equivalently slicewise) fully faithful and right adjoint, then we have a natural isomorphism $\text{drop}_U^{W_0} : \exists_U^{W_0} \neg_U^{W_0} \cong \text{Id}$.
2. copointed, then we have

- (a) $\text{hide}_U^{W_0} : \Sigma_U^{W_0} \to \exists_U^{W_0}$ (if $\top$-slice, or equivalently presheafwise, right adjoint),
- (b) $\text{spoil}_U^{W_0} : \neg_U^{W_0} \to \Omega_U^{W_0}$ (if $\Omega_U^{W_0}$ exists),
- (c) in any case $\Sigma_U^{W_0} \neg_U^{W_0} \to \text{Id}$.

3. a comonad, then there is a natural transformation $\Sigma^{W_0 \ltimes \delta} \circ \neg_U^{W_0} \to \neg_{U \ltimes U}^{W_0}$, where we compose multipliers as in theorem 3.6.1.
4. cartesian, then we have natural isomorphisms:

- (a) $\exists_U^{W_0}(V, \varphi) \cong \Sigma_U^{W_0}(V, \varphi) = (V, \pi_1 \circ \varphi)$,
- (b) $\neg_U^{W_0}(W, \psi) \cong \Omega_U^{W_0}(W, \psi)$,
- (c) $\exists_U^{W_0} \neg_U^{W_0}(W, \psi) \cong \Sigma_U^{W_0} \Omega_U^{W_0}(W, \psi) \cong (W \ltimes U, \psi \circ \pi_1)$.

Moreover, these isomorphisms become equality if $\exists_U^{W_0}$ is constructed from $\exists_U = \Sigma_U$ as in the proof of proposition 3.5.8, and $\Omega_U^{W_0}(W, \psi)$ is chosen wisely. (Both functors are defined only up to isomorphism.)

*Proof.* 1. This is a standard fact about fully faithful right adjoints such as $\neg_U^{W_0}$.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_U^{W_0} \neg_U^{W_0} \to \text{Id}$, and indeed we have

$$\pi_1 : \Sigma_U^{W_0} \neg_U^{W_0}(W, \psi) = (W \ltimes U, \pi_1 \circ (\psi \ltimes U)) = (W \ltimes U, \psi \circ \pi_1) \to (W, \psi).$$

3. This is a special case of proposition 3.5.9.
4. (a) The isomorphism is obtained from the next point by uniqueness of adjoints. We prove the equality if $\exists_U = \Sigma_U$. The co-unit is then given by $\text{drop}_U = \pi_1 : W \ltimes U \to W$. The construction of $\exists_U^{W_0}$ then reveals that $\exists_U^{W_0}(V, \varphi) = (V, \pi_1 \circ \varphi)$, which is the definition of $\Sigma_U^{W_0}(V, \varphi)$.
5. (b) This follows from the definitions.

22