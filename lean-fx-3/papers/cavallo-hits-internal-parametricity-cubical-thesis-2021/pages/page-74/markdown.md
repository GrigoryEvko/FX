62

Cubical type theory

type, meanwhile, motivates the general form of hcom, as we must to add new entries to the tube for the endpoints whenever we compose in a path type.

We have deliberately omitted the most complex pieces of cubical type theory: the definitions of coercion and composition in the V types and the definition of composition in the universe. While these are of course crucial to cubical type theory, they will not play an explicit role in this thesis. We therefore refer to [AFH18, Figure 4.2, Section 4.4.9, Section 4.4.11] for details.

We now define our first candidate type system. To the constructs of our Martin-Löf type theory, we add path types, V types, and composite types (which implement composition in the universe). We encourage the unfamiliar reader to ignore the specification of V types for now; we will explain them in Section 3.1.6. As we will never need the definition of composite types, we gloss over these entirely. Note that we do not include identity types in our cubical type system; as they are in Chapter 2, these will fail to support the Kan operations. Of course, it has been our intention to replace identity types with path types from the beginning. (We will, however, return to identity types in Part II.)

Example 3.1.32 (Small type system). We define an operator F on candidate type systems as follows: given τ, F(τ) is the union of the following clauses.

- F(τ) ⊨ Ψ ⊨ (a : A) → B ≈ (a : A') → B' ↓ R whenever
  - A ≈ A' ∈ ⋃τ[S] for some Ψ-PER S,
  - Bψ[M/a] ≈ B'ψ[M'/a] ∈ ⋃τ[T_M] for all M ≈ M' ∈ Rψ, for some S-PER T,
  - V ≈ V' ∈ R⟨ψ⟩ holds for Ψ' ⊨ ψ ∈ Ψ exactly when V = λa.N and V' = λa.N' for some N, N' with N[M/a] ≈ N'[M'/a] ∈ ⋃T_Mψ for all ψ and M ≈ M' ∈ ⋃Sψ,
- F(τ) ⊨ Ψ ⊨ Path(x.A, M₀, M₁) ≈ Path(x.A, M₀', M₁') ↓ R whenever
  - A ≈ A' ∈ ⋃τ[S] for some (Ψ, x : 𝕀)-PER S,
  - M_ε ≈ M_ε' ∈ ⋃S[ε/x] for ε ∈ {0, 1},
  - V ≈ V' ∈ R⟨ψ⟩ holds for Ψ' ⊨ ψ ∈ Ψ exactly when V = λ𝕀x.M and V' = λ𝕀x.M' for some M, M' with M ≈ M' ∈ ⋃Sψ and M[ε/x] ≈ M_εψ ∈ ⋃Sψ[ε/x] for ε ∈ {0, 1}.
- F(τ) ⊨ Ψ ⊨ V_r(A, B, I) ≈ V_r(A', B', I') ↓ R whenever
  - Ψ ⊨ r ∈ 𝕀,
  - A ≈ A' ∈ ⋃τ[S] for some (Ψ, r ≡ 0)-PER S,
  - B ≈ B' ∈ ⋃τ[T] for some Ψ-PER T,
  - I ≈ I' ∈ (S ≃ T), where S ≃ T is the (Ψ, r ≡ 0)-PER that relates equal isomorphisms (Definition 1.2.1) between the elements of S and T.