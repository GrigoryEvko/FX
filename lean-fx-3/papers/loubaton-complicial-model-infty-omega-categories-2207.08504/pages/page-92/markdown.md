CHAPTER 2. STUDY OF COMPLICIAL SETS

**Lemma 2.4.3.4.** *For any complicial set $Y$, the canonical morphism $N_j Y \to N_i Y$ is a weak equivalence.*

*Proof.* Let $Y$ be a complicial set. For any integer $n$, we have by adjunction a bijection

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\mathbf{D}_n, N_i Y)$$

and according to lemmas 2.4.3.2 and 2.4.3.3, we have bijections

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_i Y)$$

$$\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_j Y) \cong \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}((\mathbf{D}_n)_t, N_i Y).$$

Let $a$ be an element of $\operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(\partial \mathbf{D}_n, N_j Y)$. We recall that the category $\pi_n(a, N_j Y)$ is defined in 2.4.1.11. The previous equivalences implies that we have an isomorphism of category

$$\pi_n(a, N_j Y) \cong \pi_n(a, N_j Y).$$

which concludes the proof according to theorem 2.4.2.9. $\square$

*Proof of the proposition 2.4.3.1.* Let $X$ be any marked simplicial set and $Y$ a complicial set. We have equalities:

$$\begin{array}{ccc} \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(j_! X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, j^* Y) \\ \downarrow & & \downarrow \\ \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(i! X, Y) & = & \operatorname{Hom}_{ho(\mathrm{mPsh}(\Delta))}(X, i^* Y) \end{array}$$

Lemma 2.4.3.4 implies that the right hand morphism is a bijection, and so is the left hand morphism. For any $X$, $\psi(X)$ is then a weak equivalence. $\square$

## 2.4.4 Weak characterization of the identity

For the rest of this section, we fix a left Quillen functor $i: \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)$ such that there exists a zigzag of weakly invertible natural transformations:

$$i(\mathbf{D}_-) \rightsquigarrow \mathbf{D}_-.$$

**Lemma 2.4.4.1.** *Let $n$ be any integer, the following natural transformations are pointwise acyclic cofibrations:*

$$i\tau_n^i \to \tau_n^i i \tau_n^i \leftarrow \tau_n^i i.$$

*Proof.* These are natural transformations between left Quillen functors. The hypothesis implies that they induce weak equivalences on globes of dimension inferior or equal to $n$. Remark that for any $k > n$, as $i_{k-1}^-: \mathbf{D}_{k-1} \to (\mathbf{D}_k)_t$ is an acyclic cofibration and $\tau_n^i$ preserves them, $\tau_n^i \mathbf{D}_{k-1} \to \tau_n^i \mathbf{D}_k$ is an acyclic cofibration. A direct induction implies that $\mathbf{D}_n = \tau_n^i \mathbf{D}_n \to \tau_n^i \mathbf{D}_k$ is an acyclic cofibration. We then have a commutative diagram:

$$\begin{array}{ccc} i\tau_n^i(\mathbf{D}_k) & \longrightarrow & \tau_n^i i \tau_n^i(\mathbf{D}_k) \longleftarrow \tau_n^i i(\mathbf{D}_k) \\ & \searrow & \uparrow \searrow \\ & & i(\mathbf{D}_n) \end{array}$$

where all morphisms labelled by $\sim$ are weak equivalences.

By two out of three, this implies that these natural transformations induce weak equivalences on all globes, and proposition 2.4.3.1 concludes the proof. $\square$

92