Vol. 17:3

MULTIMODAL DEPENDENT TYPE THEORY

11:45

9.2. Decomposing the standard model. The above mode theory arises from a careful and informative decomposition of the standard model of guarded recursion, namely the topos of trees $\mathbf{PSh}(\omega)$, along with the later and always endomodalities.

The topos of trees consists of presheaves over the natural numbers, seen as a poset with the usual order. An element $x_n \in X(n)$ of a presheaf $X : \mathbf{PSh}(\omega)$ represents an element computed after $n$ steps of computation. The restriction maps $r_n : X(n+1) \to X(n)$ trim an element computed after $n+1$ steps to its form at the preceding moment in time. The canonical example is given by $X(n) \triangleq \{\text{streams of length } n\}$, where $r_n$ deletes the last element of a stream of length $n+1$. The later and always endomodalities are given by delaying the computation by one step, and by taking global sections (total elements):

$$(\blacktriangleright X)(n) \triangleq \begin{cases} \{*\} & \text{if } n = 0 \\ X(n-1) & \text{if } n > 0 \end{cases} \qquad (\square X)(n) \triangleq \operatorname{Hom}_{\mathbf{PSh}(\omega)}(1, X)$$

To arrive at the mode theory above, one must notice that the comonad $\square$ results in a constant presheaf, namely one which consists of the same set at each time. We can thus decompose it into the adjunction

$$\blacktriangleright \begin{array}{c} \Gamma \\ \mathbf{PSh}(\omega) \xrightarrow{\top} \mathbf{Set} \\ \Delta \end{array} \tag{9.1}$$

$\Gamma$ maps $X : \mathbf{PSh}(\omega)$ to the set of its global sections $\operatorname{Hom}_{\mathbf{PSh}(\omega)}(1, X)$, and $\Delta$ maps a set $S$ to the constant presheaf $(\Delta S)(n) \triangleq S$. It is well-known that $\Delta \dashv \Gamma$, and 'always' is given by the induced comonad $\square \triangleq \Delta \circ \Gamma$. This explains the provenance of the two modes in Figure 11: $s$ stands for sets, and $t$ for timed sets, i.e. presheaves over $\omega$.

We want to bootstrap (9.1) into a model of MTT. We will do so by leveraging an impressive sequence of facts:

- Both categories in (9.1) are presheaf categories, and hence models of MLTT: see Section 8.
- Every functor in (9.1) is a right adjoint.
- The corresponding left adjoints are introduced by precomposition, and hence can easily be arranged into a modal context structure for the mode theory $\mathcal{M}_g$ as per Section 5.1.
- Hence, by uniqueness of adjoints the functors in (9.1) are induced by right Kan extension. Consequently, they can be bootstrapped into dependent right adjoints, by Lemma 8.2.
- Therefore, by Theorem 7.1, this data yields a model of MTT with mode theory $\mathcal{M}_g$.

Let us elaborate on this chain of reasoning. First, we identify the category Set and the category $\mathbf{PSh}(1)$ of presheaves over the terminal category. Second, we construct the two left adjoints. As $\omega$ has an initial object 0, we obtain a left adjoint to the discrete functor $\Delta$, given by

$$\Pi_0(X) \triangleq X(0)$$

It is easy to see that $\Pi_0 \dashv \Delta$: by naturality at the unique morphism $0 \leq n$ we see that any $\alpha : X \Rightarrow \Delta S$ is fully determined by the component $\alpha_0 : X(0) \to S$. Furthermore, recall from the work of [BMSS12] that the later modality $\blacktriangleright$ has a left adjoint $\blacktriangleleft : \mathbf{PSh}(\omega) \to \mathbf{PSh}(\omega)$