1:6

M. SHULMAN

Vol. 19:2

polycategories with no nonlinear objects, i.e. symmetric polycategories. We can argue similarly for the following suggestively-named subterminals:

- SYMMULTI, which has one linear object, no nonlinear objects, co-unary linear homsets singletons, and others empty.
- CAT, which has one linear object, no nonlinear objects, and only the identity morphism.
- CARTMULTI, which has one nonlinear object, no linear objects, all nonlinear homsets singletons, and all linear homsets empty.
- LNLMULTI, which has one linear object, one nonlinear object, all nonlinear homsets and co-unary linear homsets singletons, and others empty.

For consistency, we may write the terminal object of LNLPoly as LNLPOLY.

We will consider other slices of LNLPoly later in the paper. For ease of reference, Table 3 on page 54 summarizes the definitions of all the small LNL polycategories over which we slice.

The slice category over any subterminal object $\mathcal{S}$ is coreflective, with coreflector $(-) \times \mathcal{S}$. Thus, all five of these subcategories are coreflective. In particular, any LNL polycategory $\mathcal{P}$ has an underlying symmetric polycategory, which we denote $\mathcal{P}^{\mathrm{L}}$, and an underlying cartesian multicategory, which we denote $\mathcal{P}^{\mathrm{NL}}$.

**Remark 2.4.** With a little more work, we can also represent *planar* (i.e. non-symmetric) multicategories inside LNLPoly. Specifically, any planar multicategory $\mathcal{M}$ freely generates a symmetric multicategory $\Sigma\mathcal{M}$, which has the same objects as $\mathcal{M}$, and such that a morphism in $\Sigma\mathcal{M}(\Gamma; B)$ is a pair $(f, \sigma)$ where $f \in \mathcal{M}(\Gamma'; B)$ and $\sigma : \Gamma \xrightarrow{\sim} \Gamma'$ is a structural permutation. The functor $\Sigma$ thus defined from planar multicategories to symmetric multicategories (or to LNL polycategories) is faithful but not full: the morphisms in its image are those that preserve the permutations $\sigma$. But we can enforce this condition by restriction to a suitable slice.

Let PLMULTI be the image under $\Sigma$ of the terminal planar multicategory; thus it has one (linear) object, and its morphisms with arity $n$ and co-arity 1 are labeled by permutations of $n$ objects. Then each $\Sigma\mathcal{M}$ comes with a canonical projection to PLMULTI that records the permutations $\sigma$, and a morphism $\Sigma\mathcal{M} \to \Sigma\mathcal{M}'$ is in the image of $\Sigma$ precisely when it commutes with these projections. Thus, the category of planar multicategories is equivalent to the slice category of the category of symmetric multicategories, and hence also of LNLPoly, over PLMULTI. Note that unlike the slices considered in Remark 2.3, PLMULTI is not subterminal, corresponding to the fact that $\Sigma$ is not full.

**Remark 2.5.** An analogous construction is *not* possible for planar *polycategories*; freely adding symmetric actions to a planar polycategory does not yield a symmetric one, as not all composites are definable [Kos05, Example 1.3]. Informally, the gap between planar and symmetric is wider in the classical case than in the intuitionistic one. This is one reason that in this paper we focus on the symmetric case.

**Remark 2.6.** As pointed out by a referee, it is natural to also wonder about *cyclic* multicategories [GK95, CGR14, HRY19, DCH21]. These behave very differently, because their cyclic action mixes domains and codomains — generally with an involution applied to the objects — thereby enabling them to represent morphisms with codomains of arbitrary arity as well. Hence, as shown in [Shu20, §7], cyclic *symmetric* multicategories are almost equivalent to symmetric *polycategories* with strict duals (“*-polycategories” [Hyl02]). The situation with cyclic *planar* multicategories is less clear, but they seem likely to be related