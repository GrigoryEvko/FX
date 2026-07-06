CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

(1) there exists no element of (B_{A⊗[1])_1} whose source is in is F and target in E.
(2) for any x, y ∈ E and v ∈ (B_{A⊗[1])_1} such that ∂v = y - x, there exist an element w ∈ (B_{A⊗[1])_1} such that ∂⁻w = y and an element α ∈ (B_{A⊗[1])_2} with ∂⁺α = w + v.
(3) for any x, y ∈ F and v ∈ (B_{A⊗[1])_1} such that ∂v = y - x, there exist an element w ∈ (B_{A⊗[1])_1} such that ∂⁺w = x and an element α ∈ (B_{A⊗[1])_2} with ∂⁻α = w + v.

Suppose now that there exists an object a of (B_A)_0 such that a ⊗ {1} in E. As we have ∂a ⊗ [1] = a ⊗ {1} - a ⊗ {0}, a ⊗ {1} is in E. There exist then an element α ∈ (B_{A⊗[1])_2} with ∂⁺α = a ⊗ [1] + w with ∂⁺a ⊗ [1] = ∂⁻w. However, by construction of A ⊗ [1], there exist no such element α. This implies that any element of E is of shape a ⊗ {0} and we can show similarly that every element of F is of shape a ⊗ {1}.

Conversely, we claim that the partition ((B_{A⊗{0})_0}, (B_{A⊗{1})_0}) fulfills these conditions. The first one is obvious. For the second, there exist a ∈ (B_A)_0 and u ∈ (B_A)_0 such that y = a ⊗ {0} and v := u ⊗ {0} and we then choose w := a ⊗ [1] and α := u ⊗ [1]. We proceed similarly for the last condition.

The partition ((B_{A⊗{0})_0}, (B_{A⊗{1})_0}) is then the unique one fulfilling the previous three condition. As φ preserves such partition, this implies that φ(B_{A⊗{0})}) = B_{A⊗{0}} and φ(B_{A⊗{1})}) = B_{A⊗{1}}.

Now, remark that for any element e ∈ (A ⊗ [1])_{n+1}^*, there exists x ∈ A_n^* such that x ⊗ [1] ≤ e if and only if there exists y ∈ A_{n-1}^* such that y ⊗ [1] ≤ ∂⁺e. By a direct induction, this implies that there exists x ∈ A_n^* such that x ⊗ [1] ≤ e if and only if ∂₀⁻e is in A₀^* ⊗ {0} and ∂₀⁺e is in A₀^* ⊗ {1}.

Combined with the previous observation, this implies that for any element x of the basis of A_n, φ(x ⊗ {ε}) is of shape x' ⊗ {ε} with ε ∈ {0, 1}. The automorphism φ then induces by restriction automorphisms φ_{A⊗{0}}: A ⊗ {0} → A ⊗ {0} and φ_{A⊗{1}}: A ⊗ {1} → A ⊗ {1}, and the hypothesis implies that they are the identity.

We now show by induction on n that φ_n : (A ⊗ [1])_n → (A ⊗ [1])_n is the identity. Suppose the result true at the stage n. For any element x of the basis of A_n, we then have

$$\partial\phi(x \otimes [1]) = \phi(\partial(x \otimes [1])) = \partial(x \otimes [1]).$$

By the definition of the derivative of A ⊗ [1], and as φ preserves the basis, this forces the equality φ(x ⊗ [1]) = x ⊗ [1]. As we already know that for any element x of the basis of A_{n+1} we have φ(x ⊗ {ε}) = x ⊗ {ε}t for any ε ∈ {0, 1}, this concludes the induction.

We then have φ = id and A ⊗ [1] has no non trivial automorphisms.

Definition 1.2.3.5. We define the Gray cone

$$\begin{array}{c c c} \text{ADC} & \to & \text{ADC} \\ K & \mapsto & K \star 1 \end{array}$$

where K ⋆ 1 is defined as the following pushout:

$$\begin{array}{c} K \otimes \{1\} \longrightarrow K \otimes [1] \\ \downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(1.2.3.6)} \\ 1 \longrightarrow K \star 1 \end{array}$$

According to [AM20, corollary 6.21], if K admits a loop free and unitary basis, this is also the case for K ⋆ 1. The Gray cone then induces a functor:

$$\begin{array}{c c c} \text{ADC}_\text{B} & \to & \text{ADC}_\text{B} \\ K & \mapsto & K \star 1 \end{array}$$

42