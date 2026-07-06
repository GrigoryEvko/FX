CHAPTER 1. (0,ω)-CATEGORIES AND PRESHEAVES ON Θ

Construction 1.1.2.21. Let n ∈ ℕ ∪ {ω}. The functor i : Δ[Θₙ] → Θₙ₊₁ defined in definition 1.1.2.16 induces an adjunction:

$$i_{!}: \mathrm{Psh}(\Delta[\Theta_{n}]) \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1}): i^{*}$$

where the left adjoint is the left Kan extension of the functor Δ[Θₙ] → Θ → Psh(Θₙ₊₁). Remark that there is an obvious inclusion iₗ(Mₙ₊₁) ⊂ Wₙ₊₁. In virtue of the last construction, this induces an adjunction between derived categories:

$$\mathbf{L}i_{!}: \mathrm{Psh}(\Delta[\Theta_{n}])_{\mathrm{M}_{n+1}} \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}}: \mathbf{R}i^{*} \tag{1.1.2.22}$$

The theorem 1.1.2.19 and the corollary 1.1.3.4 (which is proved in the next section) induce equivalences

$$(0, \omega)\text{-cat} \cong \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}} \cong \mathrm{Psh}(\Delta[\Theta_{n}])_{\mathrm{M}_{n+1}}.$$

### 1.1.3 The link between presheaves on Θ and on Δ[Θ]

Definition 1.1.3.1. Let C be a cocomplete category. A functor F : A → C is Reedy cofibrant if A has a structure of Reedy elegant category (definition 1.1.2.8) and for every object a, the induced morphism colim_∂ₐ F → F(a) is a monomorphism.

Definition 1.1.3.2. A class of monomorphism T of a cocomplete category C is precocomplete if

- It is closed by transfinite compositions and pushouts.
- It is closed by left cancellation, i.e for any pair of composable morphisms f and g, if gf and f are in S, so is g.
- For any Reedy cofibrant diagram F : A → Arr(C) that is pointwise in S, the morphism colim_A F is in S.

For a set of morphisms S, we denote S̅ the smallest precocomplete class of morphisms containing S.

The aim of this subsection is to demonstrate the following proposition:

Theorem 1.1.3.3. For any a ∈ Θ and b ∈ Δ[Θ], morphisms iₗi*a → a and b → i*iₗb are respectively in W̅ and M̅.

As a corollary, we directly have:

Corollary 1.1.3.4. For any n ∈ ℕ ∪ {ω}, the adjunction

$$\mathbf{L}i_{!}: \mathrm{Psh}(\Delta[\Theta]_{n})_{\mathrm{M}_{n}} \xleftarrow{\longleftrightarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n}}: \mathbf{R}i^{*}$$

given in (1.1.2.22) is an adjoint equivalence.

Proof. This is a consequence of theorem 1.1.3.3 and of the fact that W̅ₙ (resp. M̅ₙ) is a included in the smallest class containing Wₙ (resp. Mₙ) and stable by two out of three and colimits. □

Definition 1.1.3.5. We denote by

$$[\_, \_] : \mathrm{Psh}(\Theta) \times \mathrm{Psh}(\Delta) \to \mathrm{Psh}(\Delta[\Theta])$$

20