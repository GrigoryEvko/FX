i.e. a triangle in $\mathcal{W}/U$, the objects of which are in the image of $\mathbb{J}_U : \mathcal{W} \to \mathcal{W}/U$. Then, by fullness of $\mathbb{J}_U$ we get $\chi_0 : W \to W'$ such that $\mathbb{J}_U \chi_0 = \chi$, which by faithfulness of $\mathbb{J}_U$ makes the following diagram commute:

$$\begin{array}{c} W \xrightarrow{\chi_0} W' \\ \psi \searrow \searrow \searrow \psi' \\ W_0 \end{array} \tag{24}$$

Then $\chi_0$ is a morphism $\chi_0 : (W, \psi) \to (W', \psi')$ in $\mathcal{W}/W_0$ and $\mathbb{J}_U^{W_0} \chi_0 = \chi$.

**Proposition 3.5.6.** 1. If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full, then direct and indirect dimensional splitness are equivalent, with the same dimensional sections.

2. (Obsolete.) If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full and shard-free, then it is indirectly slicewise shard-free.
3. If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice full and shard-free, then it is directly slicewise shard-free.

*Proof.* 1. We already know that direct dimensional splitness implies indirect dimensional splitness with the same section (proposition 3.5.3). We prove the other implication.

Pick some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\pi_2 \circ \varphi : V \to U$ is dimensionally split with section $\chi : W \ltimes U \to V$. Because $\mathbb{J}_U$ is full, there is a morphism $\psi : W \to W_0$ such that $\psi \ltimes U = \varphi \circ \chi : W \ltimes U \to W_0 \ltimes U$. Thus, $\varphi$ is directly dimensionally split.

$$\begin{array}{c} V \xleftarrow{\chi} W \ltimes U \\ \varphi \searrow \searrow \searrow \psi \ltimes U \\ W_0 \ltimes U \\ \downarrow \pi_2 \\ U \end{array} \tag{25}$$

2. Pick some $(V, \varphi) \in \mathcal{V}/(W_0 \ltimes U)$ such that $\pi_2 \circ \varphi : V \to U$ is dimensionally split. Because $\mathbb{J}_U$ is essentially surjective on $\mathcal{V}//U$, there must be some $W \in \mathcal{W}$ such that $\iota : \mathbb{J}_U W = (W \ltimes U, \pi_2) \cong (V, \pi_2 \circ \varphi)$ as slice objects over $U$. Because $\mathbb{J}_U$ is full, there is a morphism $\psi : W \to W_0$ such that $\psi \ltimes U = \varphi \circ \iota : W \ltimes U \to W_0 \ltimes U$. Thus, $\iota^{-1} : (V, \varphi) \cong (W \ltimes U, \psi \ltimes U) = \mathbb{J}_U^{W_0}(W, \psi)$ as slice objects over $W_0 \ltimes U$.

$$\begin{array}{c} V \xleftarrow{\iota} W \ltimes U \\ \varphi \searrow \searrow \searrow \psi \ltimes U \\ W_0 \ltimes U \\ \downarrow \pi_2 \\ U \end{array} \tag{26}$$

3. Since indirect slicewise shard-freedom implies direct slicewise shard-freedom (proposition 3.5.3).

**Example 3.5.7** (Obsolete). In the category $\square^k$ of $k$-ary cartesian cubes (example 3.3.4), the diagonal $\delta : \mathbb{I} \to \mathbb{I} \times \mathbb{I}$ has the property that $\pi_2 \circ \delta$ is split epi, but $(\mathbb{I}, \delta)$ is not in the image of $\mathbb{J}_\mathbb{I}^1$. Thus, $\sqcup \ltimes \mathbb{I}$ is not *indirectly* slicewise shard-free, despite being $\top$-slice shard-free.

**Proposition 3.5.8.** If $\sqcup \ltimes U : \mathcal{W} \to \mathcal{V}$ is $\top$-slice right adjoint, then it is slicewise right adjoint, with

$$\exists_U^{W_0}(V, \varphi) = (\exists_U(V, \pi_2 \circ \varphi), \mathsf{drop}_U \circ \exists_U \varphi),$$

21