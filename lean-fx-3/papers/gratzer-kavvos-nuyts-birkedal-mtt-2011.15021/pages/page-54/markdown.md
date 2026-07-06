11:54

D. GRATZER, G.A. KAVVOS, A. NUYTS, AND L. BIRKEDAL

Vol. 17:3

10.1. **The walking adjunction.** As ever, we begin by freely defining a mode theory $\mathcal{M}_{\mathrm{adj}}$. Its generators are two 1-cells $\nu : m \to n$ and $\mu : n \to m$, and two 2-cells

$$\eta : 1_m \Rightarrow \mu \circ \nu \qquad \qquad \epsilon : \nu \circ \mu \Rightarrow 1_n$$

subject to the triangle equations

$$\begin{array}{ccc} \mu & \xrightarrow{\eta * 1_\mu} & \mu \circ \nu \circ \mu \\ & \searrow & \downarrow 1_\mu * \epsilon \\ & \mu & \end{array} \qquad \begin{array}{ccc} \nu & \xrightarrow{1_\nu * \eta} & \nu \circ \mu \circ \nu \\ & \searrow & \downarrow \epsilon * 1_\nu \\ & \nu & \end{array}$$

$\mathcal{M}_{\mathrm{adj}}$ is sometimes called the *walking adjunction* [LS16, §5.1]. It is the *classifying 2-category* for an adjunction: 2-functors $\mathcal{M}_{\mathrm{adj}} \longrightarrow \mathcal{C}$ correspond precisely to (2-categorical) adjunctions in $\mathcal{C}$. The mode theory $\mathcal{M}_{\mathrm{adj}}$ has a very curious property: it is *self-dual*, i.e. there is an equivalence $\mathcal{M}_{\mathrm{adj}}^{\mathrm{coop}} \simeq \mathcal{M}_{\mathrm{adj}}$. This equivalence sends the modes to each other, the adjoints to themselves and the 2-cells $\eta$ and $\epsilon$ again to each other.

10.2. **Models of adjoint modalities.** Recall that a modal context structure of a model of MTT with mode theory $\mathcal{M}_{\mathrm{adj}}$ is a strict 2-functor $[\![-]\!] : \mathcal{M}_{\mathrm{adj}}^{\mathrm{coop}} \to \mathbf{Cat}$. The self-duality of $\mathcal{M}_{\mathrm{adj}}$ implies that such a context structure consists of two categories and an adjunction between them. We immediately obtain the following result.

**Corollary 10.1.** *If $\mathcal{C}$ and $\mathcal{D}$ carry models of MLTT, and there is a pair of dependent right adjoints between them whose 'left adjoints' are themselves adjoint, then we can construct a model of MTT with mode theory $\mathcal{M}_{\mathrm{adj}}$.*

*Proof.* Write $[\![\bullet_\nu]\!] : \mathcal{C} \to \mathcal{D}$ and $[\![\bullet_\mu]\!] : \mathcal{D} \to \mathcal{C}$ for the functors given as part of the DRAs. The notation is then suggestive: $[\![\bullet_\nu]\!] \dashv [\![\bullet_\mu]\!],$ and Theorem 7.1 applies. $\square$

Conversely,

**Theorem 10.2.** *Any model of $\mathcal{M}_{\mathrm{adj}}$ must interpret $[\![\bullet_\nu]\!]$ and $[\![\bullet_\mu]\!]$ as adjoint functors. Moreover, if $\mathbf{Mod}_\mu$ and $\mathbf{Mod}_\nu$ are induced by lifting the adjunctions $[\![\bullet_\mu]\!] \dashv R_\mu$ and $[\![\bullet_\nu]\!] \dashv R_\nu$ to a dependent right adjoints (by Lemma 7.4), then $R_\nu \dashv R_\mu$.*

*Proof.* Adjoint functors are precisely adjoint morphisms in the 2-category **Cat**. As $\mathcal{M}_{\mathrm{adj}}$ is the walking adjunction, and 2-functors preserve adjunctions, we have that $[\![\bullet_\nu]\!] \dashv [\![\bullet_\mu]\!].$

If $[\![\bullet_\nu]\!] \dashv R_\nu$, then by the uniqueness of adjoint pairs we must have that $R_\nu \cong [\![\bullet_\mu]\!]$. If moreover $[\![\bullet_\mu]\!] \dashv R_\mu$, then the previous isomorphism yields $R_\nu \dashv R_\mu$. $\square$

The last situation in this lemma is sometimes known as an 'adjunction of adjunctions' [LS16, §5.1]. In particular, the action of the right adjoint modality $\mu$ on contexts, viz. $[\![\bullet_\mu]\!]$, is in some sense internalized on types and terms by the action of the left adjoint modality $\nu$ on types and terms, viz. $\langle \nu \mid - \rangle$.