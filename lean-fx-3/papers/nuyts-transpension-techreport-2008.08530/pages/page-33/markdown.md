(c) $\text{cospoil}_{\mathbf{y}U}^{\Psi|}: \Pi_{\mathbf{y}U}^{\Psi|} \to \forall_{\mathbf{y}U}^{\Psi|}$.

3. a comonad, then we can apply proposition 4.3.3 to $\sqcup \ltimes \delta: \sqcup \ltimes U \to \sqcup \ltimes (U \ltimes U)$.
4. cartesian, then we have natural isomorphisms:

(a) $\exists_{\mathbf{y}U}^{\Psi|} \cong \Sigma_{\mathbf{y}U}^{\Psi|}$,
(b) $\exists_{\mathbf{y}U}^{\Psi|} \cong \Omega_{\mathbf{y}U}^{\Psi|}$,
(c) $\forall_{\mathbf{y}U}^{\Psi|} \cong \Pi_{\mathbf{y}U}^{\Psi|}$,
(d) $\emptyset_{\mathbf{y}U}^{\Psi|} \cong \$$\mathbf{\$}_{\mathbf{y}U}^{\Psi|}$ (if $\Omega_U^{\Psi}$ exists).

Equality is achieved for any pair of functors if they are lifted in the same way from functors that were equal in theorem 4.1.11.

Proof. 1. This is a standard fact about fully faithful left/right adjoints.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_{\mathbf{y}U}^{\Psi|} \exists_{\mathbf{y}U}^{\Psi|} \to \text{Id}$, which follows immediately from $\pi_1: \Sigma_U^{\Psi} \exists_U^{\Psi} \to \text{Id}$.
3. Of course we can.
4. This is an immediate corollary of theorem 4.1.11.

Proposition 4.3.5 (Fresh exchange). If $\Psi \mid \Gamma \vdash \text{Ctx}$, i.e. $\Gamma \in \widehat{\mathcal{W}/\Psi}$, then we have an isomorphism of slice objects (natural in $\Gamma$):

$$(\Psi \ltimes \mathbf{y}U) \xrightarrow{\exists_{\mathbf{y}U}^{\Psi|}} \Gamma \xrightarrow{\cong} \Psi \cdot \Gamma \ltimes \mathbf{y}U \quad \begin{array}{c} \pi \\ \downarrow \\ \pi \ltimes \mathbf{y}U. \end{array} \quad \begin{array}{c} \pi \ltimes \mathbf{y}U \end{array} \tag{42}$$

This proposition explains the meaning of $\exists_{\mathbf{y}U}^{\Gamma}$: it is the type depending on a variable of type $\mathbf{y}U$ whose elements are required to be fresh for that variable, where the meaning of 'fresh' depends on the nature of the multiplier. If the multiplier is cartesian, then $\exists_{\mathbf{y}U}^{\Gamma}$ is clearly just weakening over $\mathbf{y}U$.

Proof. The slice object on the right is $\exists_{\mathbf{y}U}^{\Psi|}(\Psi \cdot \Gamma, \pi)$. By proposition 4.2.1, this is isomorphic to $\exists_{\mathbf{y}U}^{\Psi|}\Gamma$ over the equivalence from proposition 2.3.6 which sends $\Delta$ to $((\Psi \ltimes \mathbf{y}U) \cdot \Delta, \pi)$.

### 4.4 Investigating the transpension functor

Definition 4.4.1. 1. We define the indirect boundary $\Psi \ltimes \partial U$ as the pullback

$$\begin{array}{c} \Psi \ltimes \partial U \xrightarrow{\subseteq} \Psi \ltimes \mathbf{y}U \\ \downarrow \pi_2 \\ \partial U \xrightarrow{\subseteq} \mathbf{y}U, \end{array} \tag{43}$$

i.e. the subpresheaf of $\Psi \ltimes \mathbf{y}U$ consisting of all cells $\varphi$ such that $\pi_2 \circ \varphi$ is not dimensionally split.

2. We define the direct boundary, also denoted $\Psi \ltimes \partial U$, as the subpresheaf of $\Psi \ltimes \mathbf{y}U$ consisting of all cells $\varphi$ that are not directly dimensionally split.

By proposition 3.5.3, the indirect boundary is a subpresheaf of the direct boundary.

33