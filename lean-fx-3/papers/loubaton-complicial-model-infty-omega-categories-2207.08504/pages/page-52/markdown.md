CHAPTER 1. $$(0, \omega)$$-CATEGORIES AND PRESHEAVES ON $$\Theta$$

Remarks now that $$S$$ is contained in the set of $$(0, \omega)$$-categories admitting an atomic and loop free basis also fulfills. Using theorem 1.2.1.23, it is then sufficient to show that any augmented directed complex in $$\lambda(S)$$ has no non-trivial automorphisms. This directly follows from propositions 1.2.3.4, 1.2.3.8, 1.2.3.12 and 1.2.3.14.

It remains to show that $$S$$ contains globular sums. We proceed by induction, and we suppose that $$S$$ contains any globular sum of dimension $$k$$. Let $$[\mathbf{a}, n]$$ be a globular sum of dimension $$k + 1$$, and let $$\phi : [\mathbf{a}, n] \to [\mathbf{a}, n]$$ be an isomorphism. In particular $$\phi$$ induces an automorphism on $$[n]$$, and we then have $$\phi_i = i$$ for any $$i \leq n$$. The automorphism $$\phi$$ then induces for all $$i < n$$ an automorphism $$\phi_i : [a_i, 1] \cong [a_i, 1]$$. However, the stability by suspension of $$S$$ and the induction hypothesis implies that for any $$i < n$$, $$[a_i, 1]$$ has no non trivial automorphisms and $$\phi_i$$ is then the identity. This implies that $$\phi$$ is also the identity which concludes the proof.

**Proposition 1.2.4.20.** *Let $$n$$ be an integer $$n$$. The $$(0, \omega)$$-categories $$\mathbf{D}_n$$ and $$\underbrace{1 * 1 * \dots * 1}_{n}$$ have no non-trivial automorphisms.*

*Proof.* This is a direct consequence of lemma 1.2.4.19 as these two $$(0, \omega)$$-categories belong to $$S$$.

### 1.2.5 Gray tensor product of simplicial sets

**Notation 1.2.5.1.** We denote by

$$\mathrm{Psh}(\Theta) \xrightarrow[\iota]{\mathbf{F}} (0, \omega)\text{-cat}$$

the adjunction between presheaves on $$\Theta$$ and $$(0, \omega)$$-categories.

**Construction 1.2.5.2.** We define the functor $$_\otimes_- : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Theta) \to \mathrm{Psh}(\Theta)$$, called once again the *Gray tensor product*, as the left Kan extension of the functor

$$\Theta \times \Theta \xrightarrow{\otimes} (0, \omega)\text{-cat} \xrightarrow{\iota} \mathrm{Psh}(\Theta)$$

where $$\otimes : \Theta \times \Theta \to (0, \omega)$$-cat is the Gray tensor product defined in theorem 1.2.4.1.

By construction, the functor $$\mathbf{F}$$ preserves the Gray tensor product, and the functor $$\iota$$ preserves the Gray tensor product of globular sums.

The aim of this section is to prove the following result:

**Theorem 1.2.5.3.** *The functor*

$$_\otimes_- : \mathrm{Psh}(\Delta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Theta_2)$$

sends $$\mathrm{W}_1 \times \mathrm{W}_1$$ onto $$\overline{\mathrm{W}_2}$$, where $$\mathrm{W}_0$$ and $$\mathrm{W}_1$$ are defined in 1.1.2.15, and $$(\_)$$ in 1.1.3.2.

Informally, this result implies that we can define a Gray tensor product for $$(\infty, 1)$$-categories. It is therefore a special case of the main theorem of Campion's paper [Cam23a].

In the second part of this section, we will show a similar result for the op-joint.

**Proposition 1.2.5.4.** *The $$\Theta$$-set $$[1] \otimes [1]$$ is the colimit, computed in $$\mathrm{Psh}(\Theta)$$, of the diagram*

$$[2] \xleftarrow{\nabla} [1] \xrightarrow{[d^1, 1]} [[1], 1] \xleftarrow{[d^0, 1]} [1] \xrightarrow{\nabla} [2]$$

52