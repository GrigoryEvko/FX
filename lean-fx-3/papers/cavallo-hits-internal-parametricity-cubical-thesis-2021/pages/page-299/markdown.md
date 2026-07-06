Cubical set model 287

**Endpoints** We may define the endpoint objects in each mode by the judgment defined in Chapter 14: we set $2_m(\Psi) := \{r \mid \Psi \Vdash r \in \mathbf{I} \text{ @ } m\}$. We then interpret endpoint context extension by product: $[\Gamma, 2] := [\Gamma] \times 2_m$ for $\Gamma \text{ ctx @ } m$, and terms $\Gamma \vdash r : 2 \text{ @ } m$ by maps $[r] \in [\Gamma] \to 2_m$. We can check that the global sections functor $Disc^*$ takes $\mathbf{I}$ to $2_{\text{pt}}$ as follows.

$$Disc^*(\mathbf{I})(\Psi) = \mathbf{I}(\Psi.\text{dsc}) \cong \{r \mid \Psi.\text{dsc} \Vdash r \in \mathbf{I} \text{ @ par}\} \cong \{r \mid \Psi \Vdash r \in 2 \text{ @ pt}\} = 2_{\text{pt}}(\Psi)$$

We can also characterize each endpoint object as the coproduct $2_m \cong 1_m + 1_m$ of two copies of the terminal presheaf $1_m(\Psi) = \{\star\}$: there are two endpoints in any interval context. Being left adjoints, $Comp_!$, $Disc_!$, and $Disc^*$ all preserve coproducts. $Disc_!$ and $Disc^*$ are also right adjoints and thus preserve terminal objects, and we can manually check that $Comp_!(1_{\text{pt}}) \cong Comp_!(\mathcal{A}(\cdot)) \cong \mathcal{A}(\cdot) \cong 1_{\text{par}}$. It follows that the three preserve the endpoint object as required.

By interpreting the three basic modalities as above and composites by composition of functors, we can interpret each $\mu : m \to n$ by a functor $[\mu] : PSh(\widehat{\mathbb{D}}_n) \to PSh(\widehat{\mathbb{D}}_m)$, and so define $[\Gamma, \mu] := [\mu]$.

**Modal hypotheses** Given a modality $\mu : m \to n$, a semantic context $G \in PSh(\widehat{\mathbb{D}}_n)$, and a semantic pretype $T$ over a $\mu$, we will define a new semantic pretype $(\mu \mid T)$ over $G$. Let us first consider the special case $\mu = \text{cc}$. We may define $(\text{cc} \mid T)$ as follows.

$$\begin{aligned} (\text{cc} \mid T)(\Psi, g) &:= T(\Psi.\text{cc}, \text{cc}) \\ (\text{cc} \mid T)(\psi, g) &:= T((\psi : \Psi) \otimes \text{cc}, \text{cc}) \end{aligned}$$

Here we make implicit use of the Yoneda lemma [Mac98, §III.2]: for any presheaf $G \in PSh(\mathcal{C})$, the elements of $G(c)$ are in (natural) correspondence with morphisms $\mathcal{A}(c) \to G$, with any $g \in G(c)$ inducing $\alpha : \mathcal{A}(c) \to G$ defined by $\alpha(d)(f) := G(f)(g)$ and any $\alpha : \mathcal{A}(c) \to G$ inducing $\alpha(c)(id_c) \in G(c)$. In the above, we first regard $g \in G(\Psi)$ as a morphism $g : \mathcal{A}(\Psi) \to G$, apply the functorial action of $\text{cc}$ to obtain a morphism $\text{cc} : \mathcal{A}(\Psi.\text{cc}) \cong \text{cc} \to \text{cc}$, then apply the Yoneda lemma once more to regard this as an element $\text{cc} \in \text{cc}(\Psi.\text{cc})$. The effect, analogously to the computational setting, is that an element of $(\text{cc} \mid T)$ in some context instantiation $g$ is an element of $T$ over the connected component of $G$ to which $g$ belongs.

This definition relies on the fact that $\text{cc}$ takes interval contexts to interval contexts; this is not the case for all modalities, thanks to the presence of glo. In the general case, we compensate by quantifying over all closing substitutions using a categorical limit.

$$(\mu \mid T)(\Psi, g) := \lim \left( T(\Psi', \mu \circ h) \mid \Psi' \in \widehat{\mathbb{D}}_m, h : \mathcal{A}(\Psi') \to \mu \right)$$