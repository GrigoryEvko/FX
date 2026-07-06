18–10

Semantics of multimodal adjoint type theory

But $$((\varpi \circ \mu) \downarrow (1_s \circ -))$$ has an initial object $$(\varpi \circ \mu, 1_{\varpi \circ \mu})$$, so this limit is isomorphic to $$\mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$. A similar argument applies to the apices of the cospans, so $$\widehat{\mathcal{C}}_{\varpi}(\mathbf{\Gamma})^{1_s}$$ is the limit of the diagram consisting of the objects $$\mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$, for all $$\mu : p \to r$$, and the cospans $$\mathcal{C}_{\varpi \circ \nu}(\mathbf{\Gamma}^\nu) \to \mathcal{C}_{\varpi \circ \nu \circ \varrho}(\mathbf{\Gamma}^\mu) \leftarrow \mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$ for all $$\alpha : \mu \Rightarrow \nu \circ \varrho$$. However, there is a canonical such object where $$\mu = 1_r$$, and for any other $$\mu$$ the 2-cell $$1_\mu : \mu \Rightarrow 1_r \circ \mu$$ determines a canonical cospan $$\mathcal{C}_{\varpi}(\mathbf{\Gamma}^{1_s}) \to \mathcal{C}_{\varpi \circ 1_r \circ \mu}(\mathbf{\Gamma}^\mu) \xleftarrow{\approx} \mathcal{C}_{\varpi \circ \mu}(\mathbf{\Gamma}^\mu)$$ in which the right-hand leg is an identity. Thus, the limit of this diagram is isomorphic to $$\mathcal{C}_{\varpi}(\mathbf{\Gamma}^{1_s})$$.

**Lemma 4.15** *The functors $$\mathbf{R}_r : \mathcal{C}_r \to \widehat{\mathcal{C}}_r$$ are lax natural, by doctrinal adjunction [20].*

## 5 MATT in the co-dextrification

We now show that for suitable $$\mathcal{C}$$, the co-dextrification $$\widehat{\mathcal{C}}$$ models MATT over $$\mathcal{L}[\mathcal{S}^\dagger]$$ (recall Assumption 2.4). In fact, we use only its abstract properties; this makes our arguments cleaner and more general.

### 5.1 Adjoint modal pre-models

Recall that a **natural pseudo-model** [39, Appendix A] is a strict natural transformation $$\tau : \mathrm{Tm} \to \mathrm{Ty}$$ between groupoid-valued pseudofunctors $$\mathrm{Tm}, \mathrm{Ty} : \mathcal{D}^{\mathrm{op}} \to \mathcal{G}pd$$ that has discrete fibers and is representable.

**Definition 5.1** Let $$\mathcal{L}$$ be a 2-category with a class $$\mathcal{S}$$ of morphisms. An **adjoint modal pre-model** is:

- (i) A modal context structure $$\widehat{\mathcal{C}} : \mathcal{L}[\mathcal{L}^\dagger]^{\mathrm{coop}} \to \mathcal{C}at$$, such that each $$\widehat{\mathcal{C}}_p$$ is locally cartesian closed. As before, we write its action on morphisms as $$\widehat{\mathcal{C}}^\mu$$, and we write $$\widehat{\mathcal{C}}_\mu = \widehat{\mathcal{C}}^{\mu^\dagger}$$.
- (ii) A pseudofunctor $$\mathcal{C} : \mathcal{L}[\mathcal{S}^\dagger] \to \mathcal{C}at$$, with action on morphisms $$\mathcal{C}_\mu$$.
- (iii) A pseudonatural transformation $$\mathsf{L} : \widehat{\mathcal{C}} \to \mathcal{C}$$ between pseudofunctors $$\mathcal{L} \to \mathcal{C}at$$. To be covariant on $$\mathcal{L}$$, we take the right adjoints in $$\widehat{\mathcal{C}}$$ but the left adjoints in $$\mathcal{C}$$; thus $$\mathcal{C}_\mu(\mathsf{L}^p(\Gamma)) \cong \mathsf{L}^q(\widehat{\mathcal{C}}_\mu(\Gamma))$$.
- (iv) Each functor $$\mathsf{L}^p : \widehat{\mathcal{C}}_p \to \mathcal{C}_p$$ preserves finite limits and has a fully faithful right adjoint $$\mathsf{R}_p$$.
- (v) Each category $$\mathcal{C}_p$$ is a natural pseudo-model $$(\mathcal{C}_p, \tau_p)$$.

**Example 5.2** If $$\mathcal{C} : \mathcal{L} \to \mathcal{C}at$$ is a pseudofunctor such that each $$\mathcal{C}_p$$ is locally cartesian closed with $$\kappa$$-small limits, each functor $$\mathcal{C}_\mu$$ preserves $$\kappa$$-small limits, and $$\mathcal{C}_\mu$$ has a right adjoint if $$\mu \in \mathcal{S}$$, then the co-dextrification $$\widehat{\mathcal{C}}$$ extends it to an adjoint modal pre-model.

**Remark 5.3** If each $$\mathsf{L}^p$$ is an identity, then Definition 5.1 is just a modal context structure $$\widehat{\mathcal{C}} : \mathcal{L}[\mathcal{L}^\dagger]^{\mathrm{coop}} \to \mathcal{C}at$$ consisting of locally cartesian closed natural pseudo-models such that $$\widehat{\mathcal{C}}_\mu$$ has a right adjoint when $$\mu \in \mathcal{S}$$. In this case, the results we will prove in this section specialize to a more ordinary version of [29] for the modal case, when the lock functors already exist but we need to strictly the type formers.

**Lemma 5.4** *In an adjoint modal pre-model, if $$A \xrightarrow{f} B \xrightarrow{g} C$$ are morphisms such that $$f$$ is a pullback of a map in the image of $$\mathsf{R}_p$$, then the pushforward $$g_*(f)$$ is also a pullback of a map in the image of $$\mathsf{R}_p$$.*

**Proof.** The pullbacks of maps in the image of $$\mathsf{R}_p$$ are a left-exact-reflective subcategory of $$\widehat{\mathcal{C}}_p/C$$; the reflection $$\mathsf{L}^{f/C}$$ applies $$\mathsf{L}^p$$ and pulls back to $$C$$. For any $$h : D \to C$$, morphisms $$h \to g_*(f)$$ in $$\widehat{\mathcal{C}}_p/C$$ are equivalent to morphisms $$g^*(h) \to f$$ in $$\widehat{\mathcal{C}}_p/B$$. By assumption on $$f$$, any such morphism factors through $$\mathsf{L}^{f/B}(g^*(h))$$, which is $$g^*(\mathsf{L}^{f/C}(h))$$ by left-exactness of $$\mathsf{L}^p$$. Thus, it also corresponds to a map $$\mathsf{L}^{f/C}(h) \to g_*(f)$$. Taking $$h = g_*(f)$$ we conclude that $$g_*(f) \cong \mathsf{L}^{f/C}(g_*(f))$$ and hence lies in the subcategory. $$\square$$

### 5.2 The left adjoint splitting

The **left adjoint splitting** [29] of a natural pseudo-model $$(\mathcal{D}, \tau)$$ is $$\tau^! : \mathrm{Tm}^! \to \mathrm{Ty}^!$$ where:

- An element $$A \in \mathrm{Ty}^!(\Gamma)$$ consists of an object $$\mathsf{V}_A \in \mathcal{D}$$, a type $$\mathsf{E}_A \in \mathrm{Ty}(\mathsf{V}_A)$$, and a morphism $${}^r A^! : \Gamma \to \mathsf{V}_A$$. We call $$\mathsf{V}_A$$ the *local universe*.