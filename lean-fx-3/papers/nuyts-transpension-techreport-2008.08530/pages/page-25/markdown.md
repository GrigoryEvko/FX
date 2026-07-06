Because $\exists_{U'}^{W_0 \ltimes U}$ is full, the morphism $\iota' \circ \chi' : \exists_{U'}^{W_0 \ltimes U}(W_1 \ltimes U, \psi_1 \ltimes U) \to \exists_{U'}^{W_0 \ltimes U}(V, \varphi)$ has a preimage $\chi : (W_1 \ltimes U, \psi_1 \ltimes U) \to (V, \varphi)$ under $\exists_{U'}^{W_0 \ltimes U}$. Thus, we see that $\varphi : V \to U$ is directly dimensionally split with section $\chi$. Because $\sqcup \ltimes U$ is directly slicewise shard-free, we find some slice object $(W, \psi) \in \mathcal{W}/W_0$ so that $\iota : (V, \varphi) \cong \exists_{U'}^{W_0}(W, \psi) \in \mathcal{V}/(W_0 \ltimes U)$. We conclude that

$$(V', \varphi') \cong \exists_{U'}^{W_0 \ltimes U}(V, \varphi) \cong \exists_{U'}^{W_0 \ltimes U} \exists_{U'}^{W_0}(W, \psi) = \exists_{U \ltimes U'}^{W_0}(W, \psi). \quad (28)$$

9. $\top$-slice right adjoint multipliers are slicewise right adjoint (proposition 3.5.8), and the composite of the left adjoints is a left adjoint to the composite. $\square$

## 4 Multipliers and presheaves

**Definition 4.0.1.** Every multiplier $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ gives rise to three adjoint endofunctors between $\widehat{\mathcal{W}}$ and $\widehat{\mathcal{V}}$ via theorem 2.3.2, which we will denote

$$(\sqcup \ltimes \mathbf{y}U) \dashv (\mathbf{y}U \multimap \sqcup) \dashv (\mathbf{y}U \swarrow \sqcup). \quad (29)$$

Correspondingly, a morphism of multipliers $\sqcup \ltimes v$ gives rise to natural transformations $\sqcup \ltimes \mathbf{y}v, \mathbf{y}v \multimap \sqcup$ and $\mathbf{y}v \swarrow \sqcup$.

We will not actually be using the latter two of these functors, although they can be retrieved at least up to isomorphism from the functors in definitions 2.3.17 and 4.3.1 via the equation $\sqcup \ltimes U = \Sigma_U \exists_U$.

Note that the functor $\sqcup \ltimes \mathbf{y}U : \widehat{\mathcal{W}} \to \widehat{\mathcal{V}}$ is quite reminiscent of the Day-convolution with $\mathbf{y}U$, which is the reason for our choice of notation. However, each of the notations is to be regarded as a single symbol, i.e. $\ltimes$, $\multimap$ and $\swarrow$ by themselves have no meaning.

### 4.1 Acting on elements

In section 3.5, we generalized $\exists_U : \mathcal{W} \to \mathcal{V}/U$ to act on slice objects as $\exists_{U'}^{W_0} : \mathcal{W}/W_0 \to \mathcal{V}/(W_0 \ltimes U)$. Here, we further generalize to a functor whose domain is the category of elements:

**Definition 4.1.1.** We define (using notation 2.3.3):

- $\exists_{U'}^{\Psi} : \mathcal{W}/\Psi \to \mathcal{V}/(\Psi \ltimes \mathbf{y}U) : (W, \psi) \mapsto (W \ltimes U, \psi \ltimes \mathbf{y}U)$,
- $\exists_{U}^{\in \Psi} : (W \Rightarrow \Psi) \to \{\varphi : W \ltimes U \Rightarrow \Psi \ltimes \mathbf{y}U \mid \pi_2 \circ \varphi = \pi_2 : W \ltimes U \to U\} : \psi \mapsto \psi \ltimes \mathbf{y}U$.

We say that $\sqcup \ltimes U$ is:

- **Presheafwise faithful**$^{\S A}$ if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is faithful,
- $\top$-slice elementally faithful$^{\S A}$ if for all $\Psi$, the natural transformation $\exists_{U}^{\in \Psi}$ is componentwise injective,
- **Presheafwise full**$^{\S A}$ if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is full,
- $\top$-slice elementally full$^{\S A}$ if for all $\Psi$, the natural transformation $\exists_{U}^{\in \Psi}$ is componentwise surjective,
- **Indirectly presheafwise shard-free**$^{\S A}$ (obsolete$^{14}$) if for all $\Psi$, the functor $\exists_{U'}^{\Psi}$ is essentially surjective on elements $(V, \varphi) \in \mathcal{V}/(\Psi \ltimes \mathbf{y}U)$ such that $\varphi$ is indirectly dimensionally split:

- We say that $\varphi : V \Rightarrow \Psi \ltimes \mathbf{y}U$ is **indirectly dimensionally split** if $\pi_2 \circ \varphi : V \to U$ is dimensionally split.

$^{14}$see definition 3.5.1

25