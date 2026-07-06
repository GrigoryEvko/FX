1:20

M. SHULMAN

Vol. 19:2

**Corollary 3.14.** *A linearly subunary LNL multicategory with ×, 1, ∪, →, →, ×, and restricted F (or equivalently 1) is equivalent to a cartesian monoidal category E, a E-enriched category L with powers and copowers, and an object 1 ∈ L.*

*Proof.* Proposition 3.13 implies exactly this characterization except that instead of 1 we have a E-enriched adjunction F : E ⇔ L : ∪. But this is uniquely determined by F1 ≅ 1, since FX ≅ X × 1 and UA ≅ 1 → A.

As before, the arity restrictions can be enforced by slicing: if CBPV ∈ LNLPoly is the subterminal with one nonlinear object, one linear object, all nonlinear homsets and co-unary subunary linear homsets singletons, and others empty, then the linearly subunary LNL multicategories constitute the slice LNLPoly/CBPV. By adding appropriate combinations of universal properties, we obtain various related structures in the literature. Thus we have the following locally full sub-2-categories of LNLPoly:

- CBPV pre-structures, as in Proposition 3.13.
- **CBPV adjunction models** or **EC+ models** [EMS12], which are CBPV pre-structures having ∪, →, and F, +, ∅, &, ⊤ with restricted universal properties.
- **EEC+ models** [EMS12], which are EC+ models having also →, →, × as well as ⊕, 0 with restricted universal properties. Thus they are structures as in Corollary 3.14 where E and L both have finite products and coproducts.
- **MLJₚⁿ models** [CFMM16], which are CBPV pre-structures having only ∪, →, and restricted F.
- **LJₚⁿ models**, which are MLJₚⁿ models having also restricted +, ∅, &, ⊤.
- **ECBV models** [MS14], which are linearly *unary* LNL multicategories (that is, all linear morphisms have linear domain *and* codomain of length exactly 1) having ×, 1, →, ×, but no F or ∪. Of course, this arity restriction is given by slicing over a different object ECBV.

We now consider the “classical” case: LNL polycategories that are not co-unary.

**Proposition 3.15.** *An LNL polycategory in which the modality F exists is uniquely determined by a functor of symmetric multicategories*

$$\mathsf{F} : \mathcal{P}^{\mathrm{NL}} \to \mathrm{SYMMULTI}^*(\mathcal{P}^{\mathrm{L}})$$

where $\mathcal{P}^{\mathrm{NL}}$ is a cartesian multicategory, $\mathcal{P}^{\mathrm{L}}$ a symmetric polycategory, and SYMMULTI* denotes the underlying symmetric multicategory of a symmetric polycategory. Also:

(i) *The modality ∪ also exists if and only if the functor F has a right adjoint*

$$\mathrm{SYMMULTI}^*(\mathcal{P}^{\mathrm{L}}) \to \mathcal{P}^{\mathrm{NL}}$$

*in the 2-category of symmetric multicategories.*

(ii) *If ×, 1, ⊗, 1, ∇, ⊥ exist, then F is equivalently a strong symmetric monoidal functor from a cartesian monoidal category to (the ⊗ monoidal structure of) a symmetric linearly distributive one.*

(iii) *Thus, an LNL polycategory with ×, 1, ⊗, 1, ∇, ⊥, F, ∪ is equivalently an LNL adjunction M ⇔ L in which L is linearly distributive. Moreover, it also has (·)* if and only if L is *-autonomous.*

*Proof.* As in Proposition 3.1, we make the modality F in an LNL polycategory into a functor using its universal property; while given a functor as above we define the general linear homsets by

$$\mathcal{P}(X_1, \dots, X_n \mid \Gamma; \Delta) = \mathcal{P}^{\mathrm{L}}(\mathsf{F}X_1, \dots, \mathsf{F}X_n, \Gamma; \Delta)$$