CHAPTER 1. (0, ω)-CATEGORIES AND PRESHEAVES ON Θ

Every morphism [b, m] → i*[a, n] that does not preserve extremal points then factors through x₀. The lemma 1.1.3.13 implies that for any integer k, the canonical square

$$\coprod_{(\Theta_{/\mathbf{a}}^{-\rightarrow})_{k+1}} [b, d^0 \cup d^n] \cup [\partial b, n] \longrightarrow x_k$$
$$\downarrow \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \quad \text{(1.1.3.15)}$$
$$\coprod_{(\Theta_{/\mathbf{a}}^{-\rightarrow})_{k+1}} [b, n] \longrightarrow x_{k+1}$$

is cocartesian. The lemma 1.1.3.7 and the stability under pushout of M̅ imply that xₖ → xₖ₊₁ is in M̅. As i*[a, n] is the transfinite composition of the sequence x₀ → x₁ → ..., this implies that x₀ → i*[a, n] is in M̅ which conclude the proof.

**Lemma 1.1.3.16.** *The morphism i* Spₐ → i*a is in M̅ for any globular sum a.*

*Proof.* Let [a, n] := a. As M̅ is closed under pushouts and composition, lemma 1.1.3.14 implies that the morphism

$$i^*[\{a_0, ..., a_{n-2}\}, n-1] \cup i^*[\{a_1, ..., a_{n-1}\}, n-1] \to i^*[a, n]$$

is in M̅. An easy induction on n shows that this is also the case for the morphism

$$[a_0, 1] \cup ... \cup [a_{n-1}, 1] = i^*[a_0, 1] \cup ... \cup i^*[a_{n-1}, 1] \to i^*[a, n].$$

Now remark that i* Spₐ,ₙ is equivalent to

$$[\text{Sp}_{a_0}, 1] \cup ... \cup [\text{Sp}_{a_{n-1}}, 1].$$

As the morphisms [Spᵢ, 1] → [aᵢ, 1] are by definition in M, this concludes the proof.

**Proposition 1.1.3.17.** *There is an inclusion i* W ⊂ M̅.*

*Proof.* For Segal extensions, this is precisely the content of the last lemma. For saturation extensions, remark that i* Wₛₐₜ = Mₛₐₜ.

*Proof of theorem 1.1.3.3.* Let a be a globe. We then have iₜi*a = a. Suppose now that a is any globular sum. We then have a commutative diagram

$$\begin{array}{c} i_t i^* \text{Sp}_a \xlongequal{\quad} \text{Sp}_a \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ i_t i^* a \longrightarrow a \end{array}$$

where the upper horizontal morphism is an identity. The proposition 1.1.3.17 and the fact that iₜ(M) ⊂ W implies that the vertical morphisms of the previous diagram are in W̅. By left cancellation, this implies that iₜi*a → a belongs to W̅ for any globular sum. We proceed analogously to show that for any b ∈ Δ[Θ], b → i*iₜb is in M̅.

24