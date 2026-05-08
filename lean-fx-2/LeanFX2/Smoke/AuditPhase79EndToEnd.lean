import LeanFX2.Algo.DecConv
import LeanFX2.Algo.Synth
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Reduction.ConvCanonical
import LeanFX2.Term.Inversion

/-! # End-to-end Phase 7 + Phase 9 demonstration smoke

Exercises the full pipeline:

1. **Synthesise** typed Terms via Phase 9.D synth helpers
2. **Reduce** via Phase 9.A `RawTerm.whnf` + `Term.toRaw = rfl`
3. **Check conversion** via Phase 9.A.4 `Term.checkConv`
4. **Extract witness** via Phase 9.A.4 `Term.checkConv_sound`
5. **Lift to typed Conv** via Phase 7.B `Conv.canonical_<ctor>`
   when both sides reach matching canonical heads

All zero-axiom under strict policy.
-/

namespace LeanFX2.SmokePhase79EndToEnd

open LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Step 1 — Synthesis

Build typed Terms via the Synth API.  Each helper has the typing
rule visible in its signature. -/

/-- `unit ()` synthesised at type `Ty.unit`. -/
example : Term context Ty.unit (RawTerm.unit (scope := scope)) :=
  Algo.Term.synthUnit

/-- Boolean true. -/
example : Term context Ty.bool (RawTerm.boolTrue (scope := scope)) :=
  Algo.Term.synthBoolTrue

/-! ## Step 2 — Reduction via raw projection

`Term.toRaw t = raw` is `rfl`, so reducing the typed Term's raw
projection IS reducing the Term. -/

/-- WHNF of a unit term is unit. -/
example :
    RawTerm.whnf 5 (Term.toRaw (Algo.Term.synthUnit (context := context)))
    = RawTerm.unit (scope := scope) := rfl

/-! ## Step 3+4 — Boolean check + soundness

`Term.checkConv` returns `true` when WHNFs match; soundness gives
a `parStar` join. -/

/-- Two synthesised unit terms verify as convertible. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.unit (scope := scope)))
    (term2 : Term context ty2 (RawTerm.unit (scope := scope))) :
    Term.checkConv 1 term1 term2 = true := rfl

/-- The boolean check yields a constructive parStar witness. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.unit (scope := scope)))
    (term2 : Term context ty2 (RawTerm.unit (scope := scope))) :
    ∃ commonRaw,
      RawStep.parStar (RawTerm.unit (scope := scope)) commonRaw ∧
      RawStep.parStar (RawTerm.unit (scope := scope)) commonRaw :=
  Term.checkConv_sound 1 term1 term2 rfl

/-! ## Step 5 — Lift to typed Conv

`Conv.canonical_<ctor>` gives typed Conv directly when both sides
reach matching canonical heads. -/

/-- Two unit terms are convertible. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.unit (scope := scope)))
    (term2 : Term context ty2 (RawTerm.unit (scope := scope))) :
    Conv term1 term2 :=
  Conv.canonical_unit term1 term2

/-- Two boolTrue terms are convertible. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.boolTrue (scope := scope)))
    (term2 : Term context ty2 (RawTerm.boolTrue (scope := scope))) :
    Conv term1 term2 :=
  Conv.canonical_boolTrue term1 term2

/-! ## Step 6 — Phase 3 inversions in action

`RawStep.parStar.<head>_inv` lemmas extracted from
`Confluence/RawParStarCong.lean` constrain the common raw reduct
when one side has a canonical-head raw form.  Demonstrates the
machinery — even though it doesn't fully lift to typed
`Conv.canonicalForm_<head>`, it's directly useful for decidable
conversion. -/

/-- Given a parStar chain from `unit`, the only reachable target
is `unit` itself.  Direct application of `parStar.unit_inv`. -/
example {someTarget : RawTerm scope}
    (chain : RawStep.parStar (RawTerm.unit : RawTerm scope) someTarget) :
    someTarget = RawTerm.unit :=
  RawStep.parStar.unit_inv chain

/-- The raw join of a unit-source Conv must be unit.  Composing
`Conv.canonicalRaw` (which gives the raw join) with
`parStar.unit_inv` produces this constraint. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.unit (scope := scope)))
    (term2 : Term context ty2 (RawTerm.unit (scope := scope)))
    (someConv : Conv term1 term2) :
    ∃ commonRaw,
      commonRaw = (RawTerm.unit (scope := scope)) ∧
      RawStep.parStar (RawTerm.unit (scope := scope)) commonRaw ∧
      RawStep.parStar (RawTerm.unit (scope := scope)) commonRaw := by
  obtain ⟨commonRaw, sourceJoin, targetJoin⟩ := Conv.canonicalRaw someConv
  exact ⟨commonRaw, RawStep.parStar.unit_inv sourceJoin,
         sourceJoin, targetJoin⟩

/-- Same pattern at `boolTrue`. -/
example {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.boolTrue (scope := scope)))
    (term2 : Term context ty2 (RawTerm.boolTrue (scope := scope)))
    (someConv : Conv term1 term2) :
    ∃ commonRaw,
      commonRaw = (RawTerm.boolTrue (scope := scope)) ∧
      RawStep.parStar (RawTerm.boolTrue (scope := scope)) commonRaw ∧
      RawStep.parStar (RawTerm.boolTrue (scope := scope)) commonRaw := by
  obtain ⟨commonRaw, sourceJoin, targetJoin⟩ := Conv.canonicalRaw someConv
  exact ⟨commonRaw, RawStep.parStar.boolTrue_inv sourceJoin,
         sourceJoin, targetJoin⟩

/-! ## Audit

All theorems in this file should be zero-axiom — they delegate
to existing zero-axiom primitives shipped this iteration. -/

#print axioms LeanFX2.Algo.Term.synthUnit
#print axioms LeanFX2.Term.checkConv
#print axioms LeanFX2.Term.checkConv_sound
#print axioms LeanFX2.Conv.canonical_unit
#print axioms LeanFX2.Conv.canonical_boolTrue
#print axioms LeanFX2.RawStep.parStar.unit_inv
#print axioms LeanFX2.RawStep.parStar.boolTrue_inv

end LeanFX2.SmokePhase79EndToEnd
