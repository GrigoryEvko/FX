## 3 Multipliers in the base category

### 3.1 Definition

**Definition 3.1.1.** Let $\mathcal{W}$ be a category with terminal object $\top$. An object $W$ is **pointable**$^{\S A}$ if $(\cdot): W \to \top$ is split epi. A category is **objectwise pointable**$^{\S A}$ if every object is pointable.

We have carefully chosen the above terminology to emphasize (1) that pointability is a property, not structure (the corresponding structure is called *pointed*), and (2) that objectwise pointability does *not* require that the pointings can be chosen naturally.

**Definition 3.1.2.** Let $\mathcal{W}$ be a category with terminal object $\top$. A **multiplier** for an object $U \in \mathcal{V}$ is a functor $\sqcup \ltimes U: \mathcal{W} \to \mathcal{V}$ such that $\top \ltimes U \cong U$.$^9$ This gives us a second projection $\pi_2: \forall W.W \ltimes U \to U$. We define the **fresh weakening functor** as $\exists_U: \mathcal{W} \to \mathcal{V}/U: W \mapsto (W \ltimes U, \pi_2)$, which is essentially the action of the multiplier on slice objects over $\top$.

We say that a multiplier is:

- **Endo** if it is an endofunctor (i.e. $\mathcal{V} = \mathcal{W}$), and in that case:

- **Copointed**$^{\S A}$ if there is also a first projection $\pi_1: \forall W.W \ltimes U \to W$,
- A **comonad**$^{\S A}$ if there is additionally a 'diagonal' natural transformation $\sqcup \ltimes \delta: \forall W.W \ltimes U \to (W \ltimes U) \ltimes U$ such that $\pi_1 \circ (W \ltimes \delta) = (\pi_1 \ltimes U) \circ (W \ltimes \delta) = \text{id}$.
- **Cartesian** if it satisfies the universal property of the cartesian product with $U$,

- $\top$-**slice faithful**$^{\S A}$ if $\exists_U$ is faithful, or equivalently (lemma 3.2.2) if $\sqcup \ltimes U$ is faithful,

- $\top$-**slice full**$^{\S A}$ if $\exists_U$ is full,

- $\top$-**slice objective pointable**$^{\S A}$ if $\pi_2: W \ltimes U \to U$ is always split epi, and in that case:

- $\top$-**slice shard-free**$^{\S A}$ if $\exists_U$ is essentially surjective on objects $(V, \psi)$ such that $\psi$ is split epi, i.e. if every such object in $\mathcal{V}/U$ is isomorphic to some $\exists_U W$.
- A split epi slice object $(V, \psi)$ that is not in the image of $\exists_U$ even up to isomorphism, will be called a **shard** of the multiplier.

- $\top$-**slice right adjoint**$^{\S A}$ if $\exists_U$ has a left adjoint $\exists_U: \mathcal{V}/U \to \mathcal{W}$.$^{10}$ We denote the unit as $\text{copy}_U: \text{Id} \to \exists_U \exists_U$ and the co-unit as $\text{drop}_U: \exists_U \exists_U \to \text{Id}$.

### 3.2 Basic properties

Some readers may prefer to first consult some examples (section 3.3).

**Proposition 3.2.1.** For any multiplier, we have $(\sqcup \ltimes U) = \Sigma_U \circ \exists_U$.

**Lemma 3.2.2.** The functor $\sqcup \ltimes U$ is faithful if and only if $\exists_U$ is faithful.

*Proof.* We have $(\sqcup \ltimes U) = \Sigma_U \circ \exists_U$ and $\Sigma_U: \mathcal{V}/U \to \mathcal{V}$ is faithful as is obvious from its definition.

**Proposition 3.2.3.** A multiplier with an objectwise pointable domain is $\top$-slice objectwise pointable.

*Proof.* The multiplier, as any functor, preserves split epimorphisms.

**Proposition 3.2.4.** Cartesian endomultipliers are comonads, and comonads are copointed.

**Proposition 3.2.5.** Cartesian endomultipliers are $\top$-slice right adjoint.

$^9$ $\sqcup \ltimes U$ is to be regarded as a single-character symbol, i.e. $\ltimes$ in itself is meaningless. In most concrete applications, however, the multiplier is defined as some monoidal product $\sqcup \otimes U$ with a given object $U$. For this reason, we also refrain from defining $U := \top \ltimes U$ because we may not have $\top \otimes U = U$ on the nose for the object of interest $U$.

$^{10}$ A functor $\sqcup \ltimes U$ with this property is usually called a *parametric* or *local right adjoint* [nLa21b], but the word 'local' is overloaded [nLa23a] and so is 'parametric', and we wanted uniform terminology.

10