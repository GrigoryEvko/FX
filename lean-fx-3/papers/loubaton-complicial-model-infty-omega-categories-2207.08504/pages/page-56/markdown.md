CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Remark moreover that if A, B, C, D, and E are representable, lemma 1.2.5.8 implies that α(α(f, g), h) and α(f, α(g, h)) are morphisms of (0, ω)-categories, and they are then equal to the image by τ₂ⁱ and F of the two previous morphism. The equality given in lemma 1.2.5.10 then implies

$$\alpha(\alpha(f, g), h) = \alpha(f, \alpha(g, h))$$

Lemma 1.2.5.13. Let n and m be two integers. The canonical morphism

$$\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \to [n] \otimes [m]$$

is in W̅₂.

Proof. Let Δᵍˡᵒᵇ be the subcategory of Δ whose morphisms are the globular ones. We consider the functor g : Δᵍˡᵒᵇ × Δᵍˡᵒᵇ → Psh(Θ₂) by the formula

$$g([n], [m]) := \tau_0([n] \otimes [m]) \cup_{x \in S_{n,m}} x$$

where Sₙ,ₘ is the set of 1-generators of τ₁([n] ⊗ [m]). We have a canonical transformation g(n, m) → τ₁([n] ⊗ [m]) which is pointwise in W̅₂ by repeated application of theorem 1.2.2.1. For any pair of integers n, m, the morphism

$$g([n], [m]) \cong \underset{\mathrm{Sp}_{[n]} \times \mathrm{Sp}_{[m]}}{\mathrm{colim}} g \to \tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]})$$

then also belongs to W̅₂. By two out of three, so is the morphism

$$\tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]}) \to \tau_1([n] \otimes [m])$$

Remark now that we have a cocartesian square

$$\begin{array}{c} \tau_1(\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]}) \longrightarrow \mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \tau_1([n] \otimes [m]) \longrightarrow \tau_1([n] \otimes [m]) \cup_{x \in T_{n,m}} x \end{array}$$

where Tₙ,ₘ is the set of 2-generators of [n] ⊗ [m]. The theorem 1.2.2.1 implies that

$$\tau_1([n] \otimes [m]) \cup_{x \in T_{n,m}} x \to [n] \otimes [m]$$

is in W̅₂, and by stability by composition and pushout, so is

$$\mathrm{Sp}_{[n]} \otimes \mathrm{Sp}_{[m]} \to [n] \otimes [m].$$

Proposition 1.2.5.14. Let K be a simplicial set. The canonical morphism

$$1 \coprod_{K \otimes \{0\}} K \otimes [1] \coprod_{K \otimes \{1\}} 1 \to [K, 1]$$

is in W̅₂.

56