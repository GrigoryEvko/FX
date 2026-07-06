4.1. PRELIMINARIES

We allow ourselves the following abuse of language: when a ∞-groupoid X is contractible, we will use the expression the element of X to refer to any element of X. For example, we'll talk about the composition of two functors, or the colimit/limit of a functor. The adjective unique should be understood as the ∞-groupoid of choice is contractible.

An equivalence v in a (∞, 1)-category C between an object a and an object b is denoted by v : a ∼ b.

The maximal sub ∞-groupoid of an (∞, 1)-category C is denoted by τ₀(C).

Eventually, we will identify (strict) categories with the (∞, 1)-categories obtained by applying the simplicial nerve.

Cardinality hypothesis. We fix during this chapter three Grothendieck universes U ∈ V ∈ W, such that ω ∈ U. All defined notions depend on a choice of cardinality. When nothing is specified, this corresponds to the implicit choice of the cardinality V. With this convention in mind, we denote by Set the W-small 1-category of V-small sets, ∞-grd the W-small (∞, 1)-category of V-small ∞-groupoids and (∞, 1)-cat the W-small (∞, 1)-category of V-small (∞, 1)-categories.

## 4.1 Preliminaries

### 4.1.1 Explicit computation of some colimits

4.1.1.1. We have an adjunction:

$$\pi_0 : \infty\text{-grd} \xrightarrow{\perp} \text{Set} : \iota \tag{4.1.1.2}$$

For a category B, we denote by Psh(B) the category of functors Bᵒᵖ → Set. For a (∞, 1)-category A, we denote by Psh∞(A) the (∞, 1)-category of functors Aᵒᵖ → ∞-grd. A presheaf on B, (resp. a ∞-presheaves on A) is U-small if it is pointwise a U-small set (resp. a U-small ∞-groupoid).

cartesian fibration with T-small fibers as done in [CN22]. In both cases, the straightening/unstraightening correspondence provides a morphism

$$\mathrm{N}(\mathrm{Psh}(\Delta)_\mathbf{T}) \to \mathrm{Qcat}$$

that exhibits Qcat as the quasi-categorical localization of N(Psh(Δ)T) with respect to the weak equivalences of the Joyal's model structure ([CN22, theorem 8.13]).

The constructions we use to build new objects - (co)limits of functor between quasi-categories, quasi-categories of functor, localization of quasi-categories, sub maximal Kan complex, full sub quasi-category, adjunction, left and right Kan extension, Yoneda lemma - are well documented in the Joyal model structure (see [Lur09a] or [Cis19]), and therefore have direct incarnation in the quasi-category Qcat.

175