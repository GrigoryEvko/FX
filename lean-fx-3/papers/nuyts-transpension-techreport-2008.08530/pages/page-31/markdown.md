3. The functor $(\exists_U^{\prime \Psi})_1$ sends a presheaf $\Psi \mid \Gamma \vdash \mathrm{Ctx}$ over $\mathcal{W} / \Psi$ to the presheaf $\Psi \ltimes \mathbf{y}U \mid (\exists_U \Psi)_1 \Gamma \vdash \mathrm{Ctx}$ over $\mathcal{V} / (\Psi \ltimes \mathbf{y}U)$ determined by:

$$
(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y}U}) \Rightarrow \left(\exists_U^{\prime \Psi}\right)_1 \Gamma = \exists (W, \psi^{W \Rightarrow \Psi}). ((V, \varphi) \rightarrow \exists_U^{\prime \Psi}(W, \psi)) \times ((W, \psi) \Rightarrow \Gamma). \tag{38}
$$

On the other hand, $\exists_{\mathbf{y}U}^{\prime \Psi}(\Psi \Gamma, \pi)$ is the slice $(\Psi \Gamma \ltimes \mathbf{y}U, \pi \ltimes \mathbf{y}U) \in \widehat{\mathcal{V}} / (\Psi \ltimes \mathbf{y}U)$. Taking the preimage of $\pi \ltimes \mathbf{y}U$ (proposition 2.3.6), we get a presheaf $\Psi \ltimes \mathbf{y}U \mid \Delta \vdash \mathrm{Ctx}$ over $\mathcal{V} / (\Psi \ltimes \mathbf{y}U)$ determined by

$$
\begin{array}{l}
(V, \varphi^{V \Rightarrow \Psi \ltimes \mathbf{y}U}) \Rightarrow \Delta \\
= \{(\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi : V \Rightarrow \Psi \cdot \Gamma \ltimes \mathbf{y}U \mid (\pi \ltimes \mathbf{y}U) \circ (\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi = \varphi\} \\
= \{(\psi \cdot \gamma \ltimes \mathbf{y}U) \circ \chi : V \Rightarrow \Psi \cdot \Gamma \ltimes \mathbf{y}U \mid (\psi \ltimes \mathbf{y}U) \circ \chi = \varphi\} \\
\cong \exists W. (\chi : V \rightarrow W \ltimes U) \times (\psi : W \Rightarrow \Psi) \times (\gamma : (W, \psi) \Rightarrow \Gamma) \times ((\psi \ltimes \mathbf{y}U) \circ \chi = \varphi) \\
\cong \exists (W, \psi^{W \Rightarrow \Psi}). (\chi : (V, \varphi) \rightarrow \exists_U^{\prime \Psi}(W, \psi)) \times (\gamma : (W, \psi) \Rightarrow \Gamma).
\end{array}
$$

Indeed, we see that these functors are isomorphic.

4. Assume that $\sqcup \ltimes U$ is copointed. It is immediate from the construction of $\sqcup_1$ that $\sqcup_1$ preserves natural transformations. Moreover, we have $\mathrm{Id}_1 \cong \mathrm{Id}$, so we get $\pi_1 : (\sqcup \ltimes \mathbf{y}U) \rightarrow \mathrm{Id}$.

Conversely, assume that $\sqcup \ltimes \mathbf{y}U$ is copointed. Then we have $\mathbf{y}(\sqcup \ltimes U) \cong (\mathbf{y} \sqcup \ltimes \mathbf{y}U) \rightarrow \mathbf{y}$. Since $\mathbf{y}$ is fully faithful, we have proven $(\sqcup \ltimes U) \rightarrow \mathrm{Id}$.

5. Analogous to the previous point.

6. Assume that $\sqcup \ltimes U$ is cartesian. We apply the universal property of the cartesian product, and the co-Yoneda lemma:

$$
\begin{array}{l}
V \Rightarrow (\Gamma \ltimes \mathbf{y}U) = \exists W. (V \rightarrow W \ltimes U) \times (W \Rightarrow \Gamma) \\
\cong \exists W. (V \rightarrow W) \times (V \rightarrow U) \times (W \Rightarrow \Gamma) \\
\cong (V \rightarrow U) \times (V \Rightarrow \Gamma) \\
\cong (V \Rightarrow \mathbf{y}U) \times (V \Rightarrow \Gamma).
\end{array}
$$

Conversely, if $\sqcup \ltimes \mathbf{y}U$ is cartesian, we have

$$
\begin{array}{l}
V \rightarrow W \ltimes U = V \Rightarrow \mathbf{y}(W \ltimes U) \\
\cong V \Rightarrow \mathbf{y}W \ltimes \mathbf{y}U \\
\cong (V \Rightarrow \mathbf{y}W) \times (V \Rightarrow \mathbf{y}U) \\
\cong (V \rightarrow W) \times (V \rightarrow U).
\end{array}
$$

7. This follows from point 2 and proposition 2.3.4.

8. This follows from point 3 and proposition 2.3.4.

9. • We know that $(\exists_U)_1 \dashv (\exists_U)_1$ so moving it through the natural isomorphism yields a left adjoint to $\exists_{\mathbf{y}U}$.

• By proposition 4.1.9, $\exists_U^{\prime \Psi}$ exists. We know that $(\exists_U^{\prime \Psi})_1 \dashv (\exists_U^{\prime \Psi})_1$ so moving it through the natural isomorphism yields a left adjoint to $\exists_{\mathbf{y}U}^{\prime \Psi}$.

31