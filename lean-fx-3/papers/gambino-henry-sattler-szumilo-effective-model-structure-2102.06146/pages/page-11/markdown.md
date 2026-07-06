For $S \in \mathsf{Set}$ and $X \in \mathcal{E}$, we write $S \cdot X$ for the tensor of $X$ with $S$, when it exists. If $\mathcal{E}$ has countable coproducts, then this tensor exists for countable $S$ and can be defined as

$$S \cdot X = \prod_{s \in S} X. \quad (2.1)$$

The global sections functor $\mathcal{E}(1, -): \mathcal{E} \rightarrow \mathsf{Set}$ has a partial left adjoint, defined by mapping a countable set $S$ to

$$\underline{S} =_{\text{def}} S \cdot 1 = \prod_{s \in S} 1. \quad (2.2)$$

We extend this notation to diagram categories in a levelwise fashion: if $\mathcal{E}$ has countable coproducts and $D$ a small category, then the levelwise global sections functor $\mathcal{E}^D \rightarrow \mathsf{Set}^D$ has a partial left adjoint, sending a levelwise countable diagram $K \in \mathsf{Set}^D$ to $\underline{K} \in \mathcal{E}^D$, which is defined by levelwise application of $S \mapsto \underline{S}$. These functors will be used frequently in the paper. For example, we will use them in Section 4 to transfer the sets of boundary inclusions and horn inclusions in (1.6) from $\mathsf{sSet}$ to $\mathsf{sE}$, so as to obtain generating sets for weak factorisation systems in $\mathsf{sE}$. We establish some of their basic properties in the next lemmas.

**Lemma 2.6.** *If $\mathcal{E}$ is countably lextensive, then for every countable set $S$ and $X \in \mathcal{E}$, we have $\underline{S} \times X \cong S \cdot X$, naturally in $S$.*

*Proof.* Since $\mathcal{E}$ is countably lextensive, it is countably distributive. Thus, product with $X$ preserves countable coproducts, in particular tensors with countable sets. This reduces the claim to the natural isomorphism $1 \times X \cong X$. $\square$

The next lemma will be used, sometimes implicitly, in Section 4.

**Lemma 2.7.** *If $\mathcal{E}$ is countably lextensive, then the functor $S \mapsto \underline{S}$ from countable sets to $\mathcal{E}$ preserves finite limits.*

*Proof.* The functor $S \mapsto \underline{S}$ preserves terminal objects by definition. It also preserves pullbacks. Indeed, every pullback diagram of (countable) sets decomposes as a (countable) coproduct of product diagrams. These products are preserved since products preserve countable coproducts in each variable by lextensivity. $\square$

The next lemma will be applied in Section 6.

**Lemma 2.8.** *Let $\mathcal{E}$ be an $\alpha$-lextensive category. If $D$ is a small category and $S: D \rightarrow \mathsf{Set}$ is a functor which takes values in $\alpha$-small sets, then there is an equivalence of categories*

$$\mathcal{E}^D \downarrow \underline{S} \simeq \mathcal{E}^{D \downarrow S}$$

*where $D \downarrow S$ denotes the category of elements of $S$.*

*Proof.* The proof is similar to that of Lemma 2.2. There is a functor $\mathcal{E}^{D \downarrow S} \rightarrow \mathcal{E}^D \downarrow \underline{S}$ which sends a functor $F: D \downarrow S \rightarrow \mathcal{E}$ to the functor $V: D \rightarrow \mathcal{E}$ defined by:

$$V(d) = \prod_{s \in S(d)} F(d, s).$$

11