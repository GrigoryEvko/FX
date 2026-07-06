Vol. 20:2

TRANSPENSION: THE RIGHT ADJOINT TO THE PI-TYPE

16:21

the latter two of which can be internalized as modalities (with an additional left name) $\Sigma \sigma \dashv \Omega[\sigma] \dashv \Pi \sigma$ with

$$\left[ \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma} \right] = \Sigma^{\sigma|}, \qquad \left[ \Omega[\sigma] \right] = \Omega^{\sigma|}, \qquad \left[ \mathbf{\Theta}_{\Pi \sigma}^{\Omega[\sigma]} \right] = \Omega^{\sigma|}, \qquad \left[ \Pi \sigma \right] = \Pi^{\sigma|}.$$

We denote the units and co-units as

$$\text{copy}^{\sigma|} : 1 \to \Omega^{\sigma|} \circ \Sigma^{\sigma|} \qquad \text{drop}^{\sigma|} : \Sigma^{\sigma|} \circ \Omega^{\sigma|} \to 1$$

$$\text{const}^{\sigma|} : 1 \to \Pi^{\sigma|} \circ \Omega^{\sigma|} \qquad \text{app}^{\sigma|} : \Omega^{\sigma|} \circ \Pi^{\sigma|} \to 1$$

$$\text{drop}_{\sigma} \dashv \text{const}_{\sigma} : 1 \Rightarrow \Pi \sigma \circ \Omega[\sigma] \qquad \text{copy}_{\sigma} \dashv \text{app}_{\sigma} : \Omega[\sigma] \circ \Pi \sigma \Rightarrow 1$$

Under the correspondence of semantic contexts $\mathbb{X} \mid \Gamma \text{ctx}$ (i.e. presheaves over $\mathcal{W}/[\mathbb{X}]$) with semantic types $[\mathbb{X}] \vdash \Gamma \text{type}$, the functor $\Omega^{\sigma|}$ is exactly the semantics of ordinary type substitution in the standard presheaf model [Hof97] and hence, if $\sigma$ is a weakening substitution, then $\Sigma^{\sigma|}$ and $\Pi^{\sigma|}$ are naturally isomorphic to the semantics of ordinary $\Sigma$- and $\Pi$-types.

The functor $\Omega^{\sqcup}$ and the modality $\Pi \sqcup$ are strictly functorial (they respect identity and composition of presheaf morphisms on the nose) whereas the functors $\Sigma^{\sqcup}$, $\Pi^{\sqcup}$ and the modality $\Omega[\sqcup]$ are pseudofunctorial$^{12}$.

Proof. The morphism $\sigma$ gives rise to a functor $\Sigma^{\sigma/\sigma} : \mathcal{W}/\Xi_1 \to \mathcal{W}/\Xi_2 : (W, \psi) \to (W, \sigma \psi)$ and hence via left Kan extension, precomposition and right Kan extension [Sta19] to a triple of adjoint functors $\Sigma^{\sigma|} \dashv \Omega^{\sigma|} \dashv \Pi^{\sigma|}$ between the presheaf categories. The claim about type substitution follows from unfolding the definitions and the claims about $\Sigma$- and $\Pi$-types then follow from uniqueness of adjoints.

Strict functoriality of $\Omega^{\sqcup}$ follows immediately from the construction. Strict functoriality of $\Pi \sqcup$ then follows from the fact that a modality $\mu$ is fully defined by the semantic left adjoint $[\mathbf{\Theta}_{\mu}]$. Pseudofunctoriality of the others follows by uniqueness of the adjoint. $\square$

Remark 5.2 (Substitution as a DRA). In presheaf models, contexts are essentially the same thing as closed types (a property called democracy). The shape substitution operation for contexts $\mathbf{\Theta}_{\Pi \sigma}^{\Omega[\sigma]}$ is modelled by $\Omega^{\sigma|}$, i.e. by ordinary substitution. However, the shape substitution operation applicable to types is the modal type former $\langle \Omega[\sigma] \mid \sqcup \rangle$, which is not equivalent. Indeed, if $\langle \Omega[\sigma] \mid T \rangle$ is closed, i.e. $\mathbb{X}_1 \mid \cdot \vdash \langle \Omega[\sigma] \mid T \rangle$ type, then $T$ lives in context $\mathbb{X}_2 \mid \cdot, \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma} \vdash T$ type, so it is not closed. The operation $\langle \Omega[\sigma] \mid \sqcup \rangle$ is in general still modelled as a substitution, but now it is one between the semantic contexts $[\mathbb{X}_1], [\Gamma]$ and $[\mathbb{X}_2], \Sigma^{\sigma|}[\Gamma]$ which are isomorphic. This is especially clear if $\sigma : [\mathbb{X}], [\Delta] \to [\mathbb{X}]$ is a weakening substitution for a context $\mathbb{X} \mid \Delta \text{ctx}$, in which case we are dealing with $[\mathbb{X}], [\Delta], [\Gamma]$ and $[\mathbb{X}], (\Sigma[\Delta][\Gamma])$. We can still let $\langle \Omega[\sigma] \mid \sqcup \rangle$ act on a closed type $\Xi_2 \mid \cdot \vdash S$ type, however, but we first have to weaken $S$ to bring it to context $\cdot, \mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$. The composite of these two operations – weakening over $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ and then applying $\langle \Omega[\sigma] \mid \sqcup \rangle$ – is in fact equivalent with the operation $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ on contexts.

This remark is relevant to the $\Omega[\sigma]$ modality specifically because its lock $\mathbf{\Theta}_{\Omega[\sigma]}^{\Sigma \sigma}$ does not preserve the empty context, whereas most other modalities' locks do.

$^{12}$However, Gratzer et al. [GKNB20a] have a strictification theorem for models of MTT which could be used to strictly $\Omega[\sqcup]$.