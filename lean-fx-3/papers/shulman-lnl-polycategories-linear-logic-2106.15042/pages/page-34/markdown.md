1:34

M. SHULMAN

Vol. 19:2

desired universal morphisms and/or limits and colimits with the appropriately restricted universal properties for the corresponding subclass of LNL polycategories, which as noted in Theorem 4.12 and Example 4.25 can be characterized by saying that certain cones are $\pi$-extremal rather than globally universal. For instance, there is a doctrine $\mathbb{D}$ with $|\mathbb{D}| = \text{SYMMULTI}$ for which the $\mathbb{D}$-categories are bicomplete closed symmetric monoidal categories; another doctrine with $|\mathbb{D}| = \text{SYMMULTI}$ for which the $\mathbb{D}$-categories are symmetric monoidal categories (not necessarily closed or bicomplete); a doctrine with $|\mathbb{D}| = \text{LNLMULTI}$ for which the $\mathbb{D}$-categories are LNL adjunctions; and so on. Similarly, taking $|\mathbb{D}| = \text{CBPV}$ or ECBV as in Proposition 3.13 and Theorem 4.12, we have doctrines for CBPV adjunction models, EEC+ models, and ECBV models.

Non-subterminal examples can incorporate further adjunctions. For instance, based on Example 4.8 we can formulate a doctrine for symmetric monoidal adjunctions. By combining this idea with arity restrictions as in Proposition 3.13 (CBPV structures), we obtain doctrines for models of polarized linear calculi as in [CFMM16]:

Example 5.4. Let LINPOL be the LNL multicategory with two objects P, N, both linear, a unique morphism $\Gamma \to \mathbb{P}$ when $\Gamma$ consists entirely of P's, and a unique morphism $\Gamma \to \mathbb{N}$ when $\Gamma$ contains no more than one N. If we equip it with the single-projection cones $(\mathbb{P}, \mathbb{P}) \to \underline{\mathbb{P}}$ and $(\cdot) \to \underline{\mathbb{P}}$ (with vertex underlined), we obtain a doctrine whose categories consist of a symmetric monoidal category $\mathcal{E}$, a category $\mathcal{L}$ enriched over the Day convolution monoidal structure on $[\mathcal{E}^{\text{op}}, \text{Set}]$, and an $[\mathcal{E}^{\text{op}}, \text{Set}]$-enriched functor $R : \mathcal{L} \to [\mathcal{E}^{\text{op}}, \text{Set}]$. As in Proposition 3.13, by adding the following cones we enforce additional universal properties:

- (i) From $\underline{\mathbb{P}} \to \mathbb{N}$ we make $R$ land inside $\mathcal{E}$.
- (ii) From $\mathbb{P} \to \underline{\mathbb{N}}$ we give $R : \mathcal{L} \to \mathcal{E}$ a left adjoint.
- (iii) From $(\underline{\mathbb{P}}, \mathbb{N}) \to \mathbb{N}$ we make $\mathcal{L}$ enriched over $\mathcal{E}$.
- (iv) From $(\mathbb{P}, \underline{\mathbb{N}}) \to \mathbb{N}$ we give $\mathcal{L}$ powers by representables.
- (v) From $(\mathbb{P}, \mathbb{N}) \to \underline{\mathbb{N}}$ we give $\mathcal{L}$ copowers by representables.

In particular, with items (i), (ii) and (iv) we obtain a doctrine for the $\mathbf{IMLL}_p^\eta$ models of [CFMM16]. And if we additionally include cones for $\oplus, 0$ of positive objects and $\&, \top$ of negative ones, we obtain their $\mathbf{IMALL}_p^\eta$ models.

Now let LNLPOL have two linear objects P, N and one nonlinear object X, with all nonlinear homsets singletons, a unique morphism $(\Theta \mid \Gamma) \to \mathbb{P}$ if $\Gamma$ consists entirely of P's, and a unique morphism $(\Theta \mid \Gamma) \to \mathbb{N}$ when $\Gamma$ contains no more than one N. With the above cones for an $\mathbf{IMLL}_p^\eta$ model, cones for $\times, 1$, and also the morphisms $\underline{\mathbb{X}} \to \mathbb{P}$ and $\mathbb{X} \to \underline{\mathbb{P}}$ representing a U defined on positive objects and an F valued in positive objects, this yields a doctrine for the $\mathbf{IMELL}_p^\eta$ models of [CFMM16]. Adding $\oplus, 0$ of positive objects, $\&, \top$ of negative ones, plus $+, \varnothing$, we obtain $\mathbf{IMLL}_p^\eta$ models.

Note that the morphisms in $\mathbb{D}$-Cat preserve the specified universal properties up to canonical isomorphism. This is 2-categorically correct, but means that $\mathbb{D}$-Cat is not well-endowed with strict limits and colimits. Thus, following the philosophy of homotopy theory, we embed it in a larger but better-behaved category.

Definition 5.5. Given an LNL doctrine $\mathbb{D}$, a $\mathbb{D}$-sketch is an LNL polycategory $\mathcal{P}$ together with a functor $\pi : \mathcal{P} \to |\mathbb{D}|$, and for each $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$ a set (perhaps empty) of lifts