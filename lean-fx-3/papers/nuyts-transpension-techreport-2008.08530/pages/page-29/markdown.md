Next, we construct the unit $\mathsf{copy}_U^{/\Psi} : (V, \varphi) \to \mathbb{J}_U^{/\Psi} \exists_U^{/\Psi}(V, \varphi)$. If $\varphi = (\psi \ltimes \mathbf{y}U) \circ \varphi_0$, then we have

$$\begin{array}{l} \mathbb{J}_U^{/\Psi} \exists_U^{/\Psi}(V, \varphi) = \mathbb{J}_U^{/\Psi} \Sigma^{/\psi} \exists_U^{/W_0}(V, \varphi_0) \\ = \Sigma^{/\psi \ltimes \mathbf{y}U} \mathbb{J}_U^{/W_0} \exists_U^{/W_0}(V, \varphi_0). \end{array}$$

On the other hand, $(V, \varphi) = \Sigma^{/\psi \ltimes \mathbf{y}U}(V, \varphi_0)$, so as the unit we can take $\mathsf{copy}_U^{/\Psi} = \Sigma^{/\psi \ltimes \mathbf{y}U} \mathsf{copy}_U^{/W_0} = \mathsf{copy}_U^{/W_0} = \mathsf{copy}_U$.

The adjunction laws are then inherited from $\exists_U \dashv \mathbb{J}_U$.

**Proposition 4.1.10** (Functoriality of the category of elements). A morphism of multipliers $\sqcup \ltimes \upsilon : \sqcup \ltimes U \to \sqcup \ltimes U'$ gives rise to a natural transformation $\Sigma^{/\Psi \ltimes \mathbf{y}\upsilon} \circ \mathbb{J}_U^{/\Psi} \to \mathbb{J}_{U'}^{/\Psi}$. Hence, if both multipliers are $\top$-slice right adjoint, we also get $\exists_U^{/\Psi} \circ \Sigma^{/\Psi \ltimes \mathbf{y}\upsilon} \to \exists_U^{/\Psi}$.

*Proof.* For any $(W, \psi) \in \mathcal{W}/\Psi$, we have to prove $(W \ltimes U, (\Psi \ltimes \mathbf{y}\upsilon) \circ (\psi \ltimes \mathbf{y}U)) \to (W \ltimes U', \psi \ltimes \mathbf{y}U')$. The morphism $W \ltimes \upsilon : W \ltimes U \to W \ltimes U'$ does the job. The second statement follows from lemma 2.1.1.

**Theorem 4.1.11** (Presheafwise quantification theorem). If $\sqcup \ltimes U$ is

1. $\top$-slice (or equivalently presheafwise) fully faithful and right adjoint, then we have a natural isomorphism $\mathsf{drop}_U^{/\Psi} : \exists_U^{/\Psi} \mathbb{J}_U^{/\Psi} \cong \mathsf{Id}$.
2. copointed, then we have

(a) $\mathsf{hide}_U^{/\Psi} : \Sigma_U^{/\Psi} \to \exists_U^{/\Psi}$ (if $\top$-slice, or equivalently presheafwise, right adjoint),
(b) $\mathsf{spoil}_U^{/\Psi} : \mathbb{J}_U^{/\Psi} \to \Omega_U^{/\Psi}$ (if $\Omega_U^{/\Psi}$ exists),
(c) in any case $\Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi} \to \mathsf{Id}$.

3. a comonad, then there is a natural transformation $\Sigma^{/\Psi \ltimes \mathbf{y}\delta} \circ \mathbb{J}_U^{/\Psi} \to \mathbb{J}_{U \ltimes U}^{/\Psi}$.
4. cartesian, then we have natural isomorphisms:

(a) $\exists_U^{/\Psi}(V, \varphi) \cong \Sigma_U^{/\Psi}(V, \varphi) = (V, \pi_1 \circ \varphi)$,
(b) $\mathbb{J}_U^{/\Psi}(W, \psi) \cong \Omega_U^{/\Psi}(W, \psi)$,
(c) $\exists_U^{/\Psi} \mathbb{J}_U^{/\Psi}(W, \psi) \cong \Sigma_U^{/\Psi} \Omega_U^{/\Psi}(W, \psi) \cong (W \times \mathbf{y}U, \psi \circ \pi_1)$.

Moreover, these isomorphisms become equality if $\exists_U^{/\Psi}$ is constructed as above from $\exists_U^{/W_0} = \Sigma_U^{/W_0}$, and $\Omega_U^{/\Psi}(W, \psi)$ is chosen wisely. (Both functors are defined only up to isomorphism.)

*Proof.* 1. This is a standard fact about fully faithful right adjoints such as $\mathbb{J}_U^{/\Psi}$.

2. By lemma 2.1.1, it is sufficient to prove $\Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi} \to \mathsf{Id}$, and indeed we have $\pi_1 : \Sigma_U^{/\Psi} \mathbb{J}_U^{/\Psi}(W, \psi) = (W \ltimes U, \pi_1 \circ (\psi \ltimes \mathbf{y}U)) = (W \ltimes U, \psi \circ \pi_1) \to (W, \psi)$.
3. This is a special case of proposition 4.1.10.
4. (a) Let $\varphi = (\psi \ltimes \mathbf{y}U) \circ \varphi_0$. Then we have

$$\exists_U^{/\Psi}(V, \varphi) = \Sigma^{/\psi} \exists_U^{/W_0}(V, \varphi_0)$$

$$\cong \Sigma^{/\psi} \Sigma_U^{/W_0}(V, \varphi_0)$$

$$= \Sigma^{/\psi}(V, \pi_1 \circ \varphi_0)$$

$$= (V, \psi \circ \pi_1 \circ \varphi_0) = (V, \pi_1 \circ (\psi \ltimes \mathbf{y}U) \circ \varphi_0) = (V, \pi_1 \circ \varphi).$$

(b) This follows from the definitions.

29