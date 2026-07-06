CHAPTER 1. THE CATEGORY OF (0, ω)-CATEGORIES

with unit ν and counit ε, as well as a set of morphisms T of D such that F(S) ⊂ T. By adjunction property, it implies that for any T-local object d ∈ D, G(d) is S-local. The previous adjunction induces a derived adjunction

$$\mathbf{L}F : C_S \xrightarrow{\perp} D_T : \mathbf{R}G$$

where LF is defined by the formula c ↦ F_T F(c) and RG is the restriction of G to D_T. The unit is given by ν ∘ F_S and the counit by the restriction of ε to D_T.

1.1.2.17. The functor i : Δ[Θ] → Θ defined in paragraph 1.1.2.15 induces an adjunction:

$$i_! : \mathrm{Psh}(\Delta[\Theta]) \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta) : i^*$$

where the left adjoint is the left Kan extension of the functor Δ[Θ] → Θ → Psh(Θ). Remark that there is an obvious inclusion i_!(M) ⊂ W. In virtue of the last paragraph, this induces an adjunction between derived categories:

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta])_\mathrm{M} \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta)_\mathrm{W} : \mathbf{R}i^* \tag{1.1.2.18}$$

The corollary 12.3 of [BSP21] and the corollary 1.1.3.4 (which is proved in the next section) induce equivalences

$$(0, \omega)\text{-cat} \cong \mathrm{Psh}(\Theta)_\mathrm{W} \cong \mathrm{Psh}(\Delta[\Theta])_\mathrm{M}.$$

Similarly, for any integer n, the inclusion i : Δ[Θ_n] → Θ_{n+1} induces an adjunction between derived categories:

$$\mathbf{L}i_! : \mathrm{Psh}(\Delta[\Theta]_n)_{\mathrm{M}_n} \xrightarrow{\longleftarrow} \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_n} : \mathbf{R}i^* \tag{1.1.2.19}$$

and corollary 12.3 of [BSP21] and corollary 1.1.3.4 induce equivalences

$$(0, n+1)\text{-cat} \cong \mathrm{Psh}(\Theta_{n+1})_{\mathrm{W}_{n+1}} \cong \mathrm{Psh}(\Delta[\Theta_n])_{\mathrm{M}_{n+1}}.$$

### 1.1.3 The link between presheaves on Θ and on Δ[Θ]

1.1.3.1. A class of monomorphism T is precocomplete if

- It is closed by transfinite compositions and pushouts.
- It is closed by left cancellation, i.e for any pair of composable morphisms f and g, if gf and f are in S, so is g.
- For any elegant Reedy category A, and any functor F : A → Arr(C) such that the induced morphism colim_{∂a} F → F(a) is a monomorphism for any object a, and such that F is pointwise in S, then colim_A F is in S.

For a set of morphisms S, we denote S̅ the smallest precocomplete class of morphisms containing S.

34