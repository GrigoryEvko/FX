import LeanFX2.Algo.DecConv

/-! Phase 9.C end-to-end: typed `Term.checkConv` smoke tests.

Demonstrates the full Phase 9 pipeline operating on typed `Term`
values: build typed terms, run the conversion checker, verify
the result by `rfl`, then extract the parStar witness via
`Term.checkConv_sound`.
-/

namespace LeanFX2.SmokePhase9CDecConvTyped

open LeanFX2

/-- The identity function applied to unit is convertible to unit. -/
example :
    Term.checkConv 5
      (Term.app (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩))
                (Term.unit (context := Ctx.empty Mode.software 0)))
      (Term.unit (context := Ctx.empty Mode.software 0))
    = true := rfl

/-- Sound: the same `Term.checkConv = true` witnesses a raw common
parStar reduct of the two terms' raw projections. -/
example :
    ∃ commonRaw,
      RawStep.parStar
        (RawTerm.app (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
                     RawTerm.unit)
        commonRaw ∧
      RawStep.parStar (RawTerm.unit (scope := 0)) commonRaw :=
  Term.checkConv_sound 5
    (Term.app (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩))
              (Term.unit (context := Ctx.empty Mode.software 0)))
    (Term.unit (context := Ctx.empty Mode.software 0))
    rfl

/-- Reflexivity: a term is always conv-equal to itself. -/
example :
    Term.checkConv 3
      (Term.unit (context := Ctx.empty Mode.software 0))
      (Term.unit (context := Ctx.empty Mode.software 0))
    = true := rfl

/-- Out-of-fuel doesn't matter for syntactically equal terms — even
fuel 0 returns `true` since `whnf 0 t = t` and `t = t` is `rfl`. -/
example :
    Term.checkConv 0
      (Term.app (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩))
                (Term.unit (context := Ctx.empty Mode.software 0)))
      (Term.app (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩))
                (Term.unit (context := Ctx.empty Mode.software 0)))
    = true := rfl

#print axioms LeanFX2.Term.checkConv
#print axioms LeanFX2.Term.checkConv_sound
#print axioms LeanFX2.Conv.toRawCheckConvWitness

end LeanFX2.SmokePhase9CDecConvTyped
