import FX1Poly.Typed.TypedChurchNumeralTyping

/-! # FX1Poly/Typed/TypedChurchNumeralInhabitants — the Church Nat type has infinitely many inhabitants

The Church arc established that every Church numeral is well-typed (`churchNumeralLambda_hasTypeDescPi`, #1007)
and that distinct numerals are non-convertible (`churchNumeralLambda_notConvertible_of_ne`, #1006).  This file
bundles those into an expressiveness capstone:

  **`churchNatType_hasInfinitelyManyDistinctInhabitants` (★)** — the formation-only Π-fragment's Church Nat type
  `Π(A:Type@0). Π(f:A→A). Π(x:A). A` has INFINITELY MANY definitionally-distinct closed inhabitants: there is an
  injective family `ℕ → RawTerm 0` (the Church numerals) every member of which is typed at the Church Nat type
  and which is pairwise non-convertible.  So a single closed type of the Π-fragment carries an injection from ℕ.

Alongside, the reusable structural metatheory of the `iteratedApplication` spine (firing 121's substrate):

  * `subst_iteratedApplication` — substitution distributes over the iterate: `subst σ (iteratedApplication n f x)
    = iteratedApplication n (subst σ f) (subst σ x)` (induction on `n`; `subst` over `appCell` is `rfl`).
  * `rename_iteratedApplication` — the renaming twin.

These commute-with-`iteratedApplication` lemmas are the substitution backbone for any future reasoning about
Church-numeral-style application spines (notably the general iteration computation, CHURCH-NAT-COMPUTE-GENERAL
#1009, whose β-peel substitutes into the iterate body).

Zero-axiom: the distribution lemmas are clean inductions over `rfl`-holding `appCell` substitution/renaming
equations; the capstone bundles `churchNumeralLambda_injective` / `_hasTypeDescPi` / `_notConvertible_of_ne`.  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation StepStar

/-- Substitution distributes over the iterate: `subst σ (f^n x) = (subst σ f)^n (subst σ x)`.  By induction on
`n`; `subst` over `appCell` is `rfl` (no binder to lift through). -/
theorem subst_iteratedApplication {scopeSource scopeTarget : Nat}
    (sigma : RawTermSubst scopeSource scopeTarget) (n : Nat) (stepFn base : RawTerm scopeSource) :
    RawTerm.subst sigma (iteratedApplication n stepFn base)
      = iteratedApplication n (RawTerm.subst sigma stepFn) (RawTerm.subst sigma base) := by
  induction n with
  | zero => rfl
  | succ priorDepth priorIH =>
      show RawTerm.subst sigma (appCell stepFn (iteratedApplication priorDepth stepFn base))
        = appCell (RawTerm.subst sigma stepFn)
            (iteratedApplication priorDepth (RawTerm.subst sigma stepFn) (RawTerm.subst sigma base))
      have distributeEq : RawTerm.subst sigma (appCell stepFn (iteratedApplication priorDepth stepFn base))
          = appCell (RawTerm.subst sigma stepFn)
              (RawTerm.subst sigma (iteratedApplication priorDepth stepFn base)) := rfl
      rw [distributeEq, priorIH]

/-- Renaming distributes over the iterate (the `rename` twin of `subst_iteratedApplication`). -/
theorem rename_iteratedApplication {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) (n : Nat) (stepFn base : RawTerm sourceScope) :
    RawTerm.rename someRenaming (iteratedApplication n stepFn base)
      = iteratedApplication n (RawTerm.rename someRenaming stepFn) (RawTerm.rename someRenaming base) := by
  induction n with
  | zero => rfl
  | succ priorDepth priorIH =>
      show RawTerm.rename someRenaming (appCell stepFn (iteratedApplication priorDepth stepFn base))
        = appCell (RawTerm.rename someRenaming stepFn)
            (iteratedApplication priorDepth (RawTerm.rename someRenaming stepFn)
              (RawTerm.rename someRenaming base))
      have distributeEq : RawTerm.rename someRenaming (appCell stepFn (iteratedApplication priorDepth stepFn base))
          = appCell (RawTerm.rename someRenaming stepFn)
              (RawTerm.rename someRenaming (iteratedApplication priorDepth stepFn base)) := rfl
      rw [distributeEq, priorIH]

/-- ★ **The Church Nat type has infinitely many definitionally-distinct closed inhabitants.**  There is an
injective family `ℕ → RawTerm 0` — the Church numerals — every member of which is typed at the Church Nat type
`Π(A:Type@0). Π(f:A→A). Π(x:A). A` and which is pairwise non-convertible.  So a single closed type of the
formation-only Π-fragment carries an injection from ℕ — an expressiveness capstone of the Church arc, bundling
the general typing (#1007) and the general faithfulness (#1006). -/
theorem churchNatType_hasInfinitelyManyDistinctInhabitants {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ inhabitants : Nat → RawTerm 0,
      (∀ depthLeft depthRight, inhabitants depthLeft = inhabitants depthRight → depthLeft = depthRight)
      ∧ (∀ depth, HasTypeDescPi profile TypingContext.empty (inhabitants depth)
          (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
            (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
              (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))))
      ∧ (∀ depthLeft depthRight, depthLeft ≠ depthRight
          → ¬ Conv (inhabitants depthLeft) (inhabitants depthRight)) :=
  ⟨churchNumeralLambda,
    fun _ _ sameNumeral => churchNumeralLambda_injective sameNumeral,
    fun depth => churchNumeralLambda_hasTypeDescPi flag depth,
    fun _ _ depthsDiffer => churchNumeralLambda_notConvertible_of_ne depthsDiffer⟩

end FX1Poly.Typed
