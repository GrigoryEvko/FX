import LeanFX2.Algo.RawWHNF

/-! Phase 9.A raw WHNF zero-axiom audit + concrete reduction smoke.

`RawTerm.whnf` is a fuel-bounded weak head normal form reducer.
Verified zero-axiom under strict policy.  Concrete examples
demonstrate β/ι firing on closed terms.
-/

namespace LeanFX2.SmokePhase9A

open LeanFX2

#print axioms LeanFX2.RawTerm.whnf

/-- The identity function applied to unit reduces to unit. -/
example :
    RawTerm.whnf 10
        (.app (.lam (.var ⟨0, by decide⟩)) (.unit (scope := 0)))
      = .unit := rfl

/-- `fst (pair true false)` reduces to `true`. -/
example :
    RawTerm.whnf 10
        (.fst (.pair (.boolTrue (scope := 0)) .boolFalse))
      = .boolTrue := rfl

/-- `snd (pair true false)` reduces to `false`. -/
example :
    RawTerm.whnf 10
        (.snd (.pair (.boolTrue (scope := 0)) .boolFalse))
      = .boolFalse := rfl

/-- `boolElim true (lam unit) (lam refl)` fires the true-branch. -/
example :
    RawTerm.whnf 10
        (.boolElim (.boolTrue (scope := 0))
                   (.lam .unit)
                   (.lam (.refl (.var ⟨0, by decide⟩))))
      = .lam .unit := rfl

/-- `natElim 0 unit (lam (lam unit))` fires zero branch. -/
example :
    RawTerm.whnf 10
        (.natElim (.natZero (scope := 0))
                  .unit
                  (.lam (.lam .unit)))
      = .unit := rfl

/-- Double β: `(λ x. x) ((λ y. y) unit)` reduces twice to unit. -/
example :
    RawTerm.whnf 10
        (.app (.lam (.var ⟨0, by decide⟩))
              (.app (.lam (.var ⟨0, by decide⟩))
                    (.unit (scope := 0))))
      = .unit := rfl

/-- Out-of-fuel: zero fuel returns the input unchanged. -/
example :
    RawTerm.whnf 0
        (.app (.lam (.var ⟨0, by decide⟩)) (.unit (scope := 0)))
      = .app (.lam (.var ⟨0, by decide⟩)) .unit := rfl

end LeanFX2.SmokePhase9A
