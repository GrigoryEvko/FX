do not know if these are always homotopy equivalent when $X$ is neither fibrant nor cofibrant itself.

**2.45 Remark.** We do not know if $\infty\text{-Cat}^{+m}$ is actually a Quillen model category or not. In the unmarked case, this follows from the fact that all objects are fibrant. But that is no longer the case in this situation. In terms of the “two-sided model structure” mentioned in the previous remark, the question is whether $\infty\text{-Cat}^{+m}$ satisfies one of the equivalent conditions of Proposition 5.3 of [24].

We conclude this section with the following lemma that will be useful later:

**2.46 Lemma.** *The map*

$$i_n^+ : \mathbb{D}_n^\flat \to (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

where $e_{n+1}$ is the unique non-identity arrow of $\mathbb{D}_{n+1}$, is an anodyne cofibration.

*Proof.* We will show it is a retract of the map $j_+ \hat{\odot} i_n$ where $i_n$ is the map $\partial \mathbb{D}_n \to \mathbb{D}_n$. We then have to construct two morphisms $i, p$ fitting in a diagram of the form

$$(\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \xrightarrow{i} I \ominus \mathbb{D}_n^\flat$$
$$\downarrow p$$
$$(\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$$

and such that $p$ and $i$ send the domain of $i_n^+$ and of $j_+ \hat{\odot} i_n$ to each other.

In order to achieve this, we will use the explicit description of $\mathbb{D}_1 \otimes \mathbb{D}_n$ given in Example 2.12. The object we are interested in is $I \ominus \mathbb{D}_n^\flat$ which is the same polygraph endowed with the marking where all the arrows $a \otimes e_k^\iota$ are marked. We call $i: (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}}) \to I \ominus \mathbb{D}_n^\flat$ the unique morphism sending $e_{n+1}$ to $a \otimes e_n$. This is well defined because $a \otimes e_n$ is a marked arrow. Next, we define a map $p: I \ominus \mathbb{D}_n^\flat \to (\mathbb{D}_{n+1}, \overline{\{e_{n+1}\}})$ by:

$$p(a_0^\iota \otimes e_k^\mu) = e_k^\mu \text{ if } k < n.$$

$$p(a_0^\iota \otimes e_n) = e_n^\iota$$

$$p(a \otimes e_k^\iota) = \mathbb{I}_{e_k^\iota} \text{ if } k < n.$$

$$p(a \otimes e_n) = e_{n+1}$$

In order to check that this is well defined, we first need to check that this definition is compatible with the source and target given above, which follows from an immediate calculation. Then we need to show that this is compatible with the marking, which is the case as both $\mathbb{I}_{e_k^\iota}$ and $e_{n+1}$ are marked.

Finally, the composite $p \circ i$ sends the arrow $e_{n+1}$ to $p(a \otimes e_n) = e_{n+1}$ and hence is the identity of $\mathbb{D}_{n+1}$.

To conclude the proof, we just have to observe that the maps $p$ and $i$ defined above send the domain of $i_n^+$ and of $j_+ \hat{\odot} i_n$ to each other.

The domain of $j_+ \hat{\odot} i_n$ is the sub-polygraph of $I \ominus \mathbb{D}_n^\flat$ which contains all the generators except $a_0^- \otimes e_n$ and $a \otimes e_n$, while the domain of $i_n^+$ contains all generators of $\mathbb{D}_{n+1}$ except $e_{n+1}$ and $e_n^-$.

21