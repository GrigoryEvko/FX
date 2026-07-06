16

Eliminating reversals from cubical type theories

Proof. As a functor category, R has finite limits computed pointwise in R. In particular, the fact that representable maps are closed under pullback in R implies the same of Span(R).

It remains to show that the representable maps in Span(R) are exponentiable. Let f: Z → Y and p: Y → X be maps in Span(R) and suppose p is representable. As p₀ and p₁ are exponentiable, we have dependent products g₀ := (p₀)₊f₀: Πₚ₀Z₀ → X₀ and g₁ := (p₁)₊f₁: Πₚ₁Z₁ → X₁. Write k for the composite

$$\begin{array}{c} Y_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \\ \Biggl\downarrow^g \\ Y_{\mathrm{r}} \times_{Y_0 \times Y_1} ((Y_0 \times_{X_0} \Pi_{p_0} Z_0) \times (Y_1 \times_{X_1} \Pi_{p_1} Z_1)) \xrightarrow{Y_{\mathrm{r}} \times_{Y_0 \times Y_1} (\epsilon_{Z_0} \times \epsilon_{Z_1}))} Y_{\mathrm{r}} \times_{Y_0 \times Y_1} Z_0 \times Z_1 \end{array}$$

induced by the counits of the (pullback, pushforward) adjunction, and write q for the (representable) pullback

$$\begin{array}{c} Y_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \longrightarrow Y_{\mathrm{r}} \\ \downarrow^q \\ X_{\mathrm{r}} \times_{X_0 \times X_1} (\Pi_{p_0} Z_0 \times \Pi_{p_1} Z_1) \longrightarrow X_{\mathrm{r}}. \end{array}$$

Writing the components of q₊k*(fᵣ, (d⁰, d¹)): Π_q k* Zᵣ → Xᵣ ×_{X₀×X₁} (Πₚ₀Z₀ × Πₚ₁Z₁) as ⟨gᵣ, d⁰, d¹⟩, the morphism of spans

$$\begin{array}{c} \Pi_{p_0} Z_0 \xleftarrow{d^0} \Pi_q k^* Z_r \xrightarrow{d^1} \Pi_{p_1} Z_1 \\ \downarrow^g \\ X_0 \xleftarrow{d^0} X_r \xrightarrow{d^1} X_1 \end{array}$$

is a pushforward of f along p.

By definition, the projections π₀, π₁: Span(R) → R are RMC functors. Restricting our attention now to MLTTΣ,Id, we define an RMC functor Refl fitting in the diagram

$$\begin{array}{c} \text{MLTT}_{\Sigma,\text{Id}} \\ \downarrow^1 \\ \text{Refl} \\ \text{MLTT}_{\Sigma,\text{Id}} \xleftarrow{\pi_0} \text{Span}(\text{MLTT}_{\Sigma,\text{Id}}) \xrightarrow{\pi_1} \text{MLTT}_{\Sigma,\text{Id}} \end{array}$$

by giving an interpretation. For Φ ∈ MLTTΣ,Id, we write the span ReflΦ as Φ ← dΦ⁰ → PΦ → Φ, i.e., with P: MLTTΣ,Id → MLTTΣ,Id denoting the composite of Refl with the apex projection.

To interpret the type and term judgments, we will use the environment Ty^∞ of 1-to-1 correspondences from Definition 10.

- ▶ Definition 44. Write Tm^∞ := ((A, A', A̅, ···) : Ty^∞, a : A, a' : A', ā : Ā(a, a')) ∈ MLTTΣ,Id and d⁰, d¹: Tm^∞ → Tm for the instantiations projecting (A, a) and (A', a') respectively.
- ▶ Component 45 (Refl, sorts). For sorts, we define ReflTy := {Ty ← d⁰ → Ty^∞ → d¹ → Ty} and ReflTm := {Tm ← d⁰ → Tm^∞ → d¹ → Tm}, with ReflπTm: ReflTy → ReflTm the evident projection.

Defining Refl for a type former T: Φ ⇒ Ty now amounts to giving, over the environment (p : PΦ), a 1-to-1 correspondence R(p, −, −) between T(dΦ⁰(p)) and T(dΦ¹(p)). Similarly, interpreting a term former t: (x : Φ) ⇒ Tm(I(x)) amounts to giving over (p : PΦ) an inhabitant of R(p, t(dΦ⁰(p)), t(dΦ¹(p))).