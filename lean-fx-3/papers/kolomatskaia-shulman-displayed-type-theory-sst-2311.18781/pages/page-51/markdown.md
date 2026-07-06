Of course, all these constructions must also be stable under substitution:

$$\left( \lim \left( \widetilde{\Upsilon} \ \gamma \right) \right)^{\sigma} \equiv \lim \left( \widetilde{\Upsilon} \ (\sigma \ \theta) \right)$$

$$\left( \lim \left( \bar{\alpha} \ \gamma \right) \right)^{\sigma} \equiv \lim \left( \bar{\alpha} \ (\sigma \ \theta) \right)$$

$$\left( \operatorname{res}^{\partial n} \ \gamma \ (\alpha \ \gamma) \right)^{\sigma} \equiv \operatorname{res}^{\partial n} \ \theta \ (\alpha \ (\sigma \ \theta) \right)$$

$$\left( \operatorname{res}^{n} \ \gamma \ (\alpha \ \gamma) \right)^{\sigma} \equiv \operatorname{res}^{n} \ \theta \ (\alpha \ (\sigma \ \theta) \right)$$

◁

## 4.2 THE SIMPLICIAL MODEL

In this section we fix a model of dependent type theory with all of the structure described above, which we call the discrete model (dm). From it, we will construct a derived model called the simplicial model (sm). We will do this, first, by way of constructing the truncated simplicial models (smⁿ) for n ≥ -2.

### 4.2.1 The Augmented Semi-Simplex Category

Let B be the type of binary digits, which are 0, 1 : B. For n ≥ m ≥ -1, let B⁽ⁿ⁾,⁽ᵐ⁾ be the type of length n + 1 binary sequences such that exactly m + 1 of the digits have value 1. When b₁ : B⁽ⁿ⁾,⁽ᵐ⁾ and b₀ : B⁽ᵐ⁾,⁽ᵏ⁾, we have a composition b₁ ∘ b₀ : B⁽ⁿ⁾,⁽ᵏ⁾ obtained by replacing the 1 digits in b₁ with the digits of b₀. For example 1010011 ∘ 0110 = 0010010. The category whose objects are ⟨n⟩ and whose morphisms ⟨m⟩ → ⟨n⟩ are B⁽ⁿ⁾,⁽ᵐ⁾ is the augmented semi-simplex category Δ⁺. Note that each of the representables B⁽ⁿ⁾,⁻ only has finitely many elements. We write ∅ for the length-zero sequence, which is the unique element of B⁽⁻¹⁾,⁽⁻¹⁾.

The identities 1⁽ⁿ⁾ are given by length n + 1 sequences of the digit 1. Further, for any b : B⁽ⁿ⁾,⁽ᵏ⁾, we obtain 0b : B⁽ⁿ⁺¹⁾,⁽ᵏ⁾ and 1b : B⁽ⁿ⁺¹⁾,⁽ᵏ⁺¹⁾ by left appending the indicated digit. The following identities hold:

$$0b_1 \circ b_0 \equiv 0 \ (b_1 \circ b_0)$$

$$1b_1 \circ 1b_0 \equiv 1 \ (b_1 \circ b_0)$$

$$1b_1 \circ 0b_0 \equiv 0 \ (b_1 \circ b_0)$$

Note that by the second rule, along with the fact that 11⁽ⁿ⁾ ≡ 1⁽ⁿ⁺¹⁾, the assignments ⟨n⟩ ↦ ⟨n + 1⟩ and b ↦ 1b define an endofunctor of Δ⁺.

Additionally, for every n ≥ -2, we have the full subcategory Δₙ⁺ of Δ⁺ on those objects ⟨k⟩ with k ≤ n. Thus Δ₋₂⁺ is the empty category, while Δ₋₁⁺ is the terminal category.

### 4.2.2 Truncated Simplicial Objects

The objects of the n-truncated simplicial model smⁿ are C-valued presheaves on Δₙ⁺, denoted:

$$\Gamma \operatorname{ob}_{\operatorname{sm}^n}$$

Thus the underlying category of smⁿ is CΔₙ⁺. For each such presheaf and n ≥ m ≥ -2, we have Γₘ ob_dm, where Γ₋₂ ≡ ()_dm is the distinguished terminal object of C.

51