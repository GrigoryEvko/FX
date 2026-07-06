which leads to the modal logic $\mathbf{T}$.

We would expect that combining axioms 4 and $T$ generates the modal logic $\mathbf{S4}$. We can indeed generate a free category out of these two generating transformations, but there is more subtlety involved. The reason is that our mode theory reifies axioms as transformations—actual objects that can be composed in more than one way. For example, we can immediately find three transformations $\alpha : \square \Rightarrow \square$. One is simply the identity $1_{\square} : \square \Rightarrow \square$. But there are also two more, which combine the $T$ and 4 axioms:

$$(T * 1_{\square}) \circ 4 : \square \Rightarrow \square$$

$$(1_{\square} * T) \circ 4 : \square \Rightarrow \square$$

Moreover, there are two ways to construct a transformation $\square \Rightarrow \square^3$:

$$(4 * 1_{\square}) \circ 4 : \square \Rightarrow \square^3$$

$$(1_{\square} * 4) \circ 4 : \square \Rightarrow \square^3$$

It is not unreasonable to postulate that these different ways of constructing the same transformation are equal, i.e. that

$$(T * 1_{\square}) \circ 4 = 1_{\square} = (1_{\square} * T) \circ 4 \quad (4)$$

$$(4 * 1_{\square}) \circ 4 = (1_{\square} * 4) \circ 4 \quad (5)$$

In category theory such equations are called *coherence equations*: they state that multiple ways of performing a certain transformation are in fact identical in their effect (coherent). The addition of coherence equations means that a category is no longer freely generated.

A mode theory that satisfies these equations can be constructed explicitly: its modalities are of the form $\square^n$ for $n \in \mathbb{N}$; a transformation $\alpha : \square^n \Rightarrow \square^m$ is just an order preserving function $\alpha : [m] \rightarrow [n]$ where $[m] \stackrel{\text{def}}{=} \{k \in \mathbb{N} \mid k < m\}$; and composition of modalities is just their sum [SS86]. Category theorists will recognise this as the *walking comonad*, i.e. a tiny 2-category **Comnd** such that 2-functors **Comnd** $\longrightarrow$ **Cat** classify all categories equipped with a specific comonad. The fact that this kind of object occurs in category theory provides external justification for why the above list of equations is sound and complete.

Of course, this could be seen as being far more work than necessary. We could have constructed a mode theory $\mathcal{M}_{\mathbf{K4}}^{\text{idem}}$ with one mode $\bullet$, and one modality $\square : \bullet \rightarrow \bullet$ that satisfies the equation

$$\square \circ \square = \square$$

and no non-identity transformations. In this mode theory there is a unique transformation $\alpha : \square \Rightarrow \square \circ \square$: because the boundaries of this transformation are equal, it is just the identity transformation $1_{\square}$ on $\square$. With this mode theory we can prove a theorem

17