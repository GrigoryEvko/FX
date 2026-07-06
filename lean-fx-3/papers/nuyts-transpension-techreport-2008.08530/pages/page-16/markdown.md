- If both multipliers are comonads, then $v$ is said to be a **comonad morphism of multipliers**$^{\S A}$ if it is a comonad morphism, i.e. if additionally $(W \ltimes \delta) \circ (W \ltimes v) = ((W \ltimes v) \ltimes v) \circ (W \ltimes \delta)$,
- A morphism of cartesian multipliers is **cartesian** if it is the cartesian product with $v$.

**Proposition 3.4.2.** A morphism of copointed multipliers, whose domain and codomain happen to be cartesian multipliers, is cartesian.

*Proof.* We have $\pi_2 \circ (W \ltimes v) = v \circ \pi_2$ and $\pi_1 \circ (W \ltimes v) = \pi_1$. Hence, $(W \ltimes v) = (\pi_1, v \circ \pi_2) = W \ltimes v$. $\square$

**Proposition 3.4.3** (Functoriality). A multiplier morphism $\sqcup \ltimes v : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma'^v \circ \bot_U \to \bot_{U'}$. Hence, for $\top$-slice right adjoint multipliers, we also have $\exists_{U'} \circ \Sigma'^v \to \exists_U$.

*Proof.* We have to show that for every $W \in \mathcal{W}$, we get $(W \ltimes U, v \circ \pi_2) \to (W \ltimes U', \pi_2)$. The morphism $W \ltimes v : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1. $\square$

### 3.4.2 Quantification and quotient theorem

**Theorem 3.4.4** ($\top$-slice quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice fully faithful and right adjoint, then we have a natural isomorphism $\mathsf{drop}_U : \exists_U \bot_U \cong \mathsf{Id}$.
2. copointed, then we have:

(a) \(\mathsf{hide}_U:\Sigma_U\to \exists_U\) (if T-slice right adjoint),
(b) \(\mathsf{soil}_U:\perp_U\to \Omega_U\) (if \(\Omega_U\) exists),
(c) in any case \(\Sigma_U\perp_U\to \mathrm{Id}\)

3. a comonad, then there is a natural transformation \(\Sigma^{\prime \delta}\circ \bot_U\to \bot_{U\times U}\), where we compose multipliers as in theorem 3.6.1.
4. cartesian, then we have:

(a) \(\exists_U\cong \Sigma_U\)
(b) \(\perp_U\cong \Omega_U\)
(c) \(\exists_U\perp_U\cong \Sigma_U\Omega_U = (\sqcup \ltimes U)\cong (\sqcup \ltimes U).\)

Moreover, these isomorphisms become equalities by choosing $\exists_U$ and $\Omega_U$ wisely (both are defined only up to isomorphism).

*Proof.* 1. This is a standard fact of fully faithful right adjoints such as $\bot_U$.

2. By lemma 2.1.1, it is sufficient to prove \(\Sigma_U \perp_U \to \operatorname{Id}\). But \(\Sigma_U \perp_U = (\sqcup \ltimes U)\), so this is exactly the statement that the multiplier is copointed.
3. This is a special case of proposition 3.4.3.
4. By uniqueness of the cartesian product, we have \(\perp_U \cong \Omega_U\). Then the multiplier is \(\top\)-slice right adjoint with \(\exists_U \cong \Sigma_U\). The last point is now trivial.

**Theorem 3.4.5** ($\top$-slice quotient theorem$^{\S A}$ for $\top$-slice objectwise pointable multipliers). If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice objectwise pointable, fully faithful and shard-free, then $\bot_U : \mathcal{W} \simeq \mathcal{V} // U$ is an equivalence of categories, where $\mathcal{V} // U$ is the full subcategory of $\mathcal{V} / U$ whose objects are the split epimorphic slice objects.

*Proof.* By $\top$-slice objectwise pointability, $\bot_U$ lands in $\mathcal{V} // U$. The other properties assert that $\bot_U$ is fully faithful and essentially surjective as a functor $\mathcal{W} \to \mathcal{V} // U$. $\square$

16