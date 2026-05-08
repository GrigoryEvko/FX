import LeanFX2.Bridge.BoxObservational

/-! # Smoke/AuditPhase12A9D96BoxObservational

Reviewer-facing `#print axioms` regression log for the rfl-fragment
box-observational bridge shipped under tracker #1390 (D9.6).

Every declaration printed here MUST report "does not depend on any
axioms".  The strict-harness gate in
`Tools/AuditAll/AuditBridge.lean` is the canonical machine-enforced
checker; this file documents the intent for human review.

## What is audited

| Declaration | Role |
|-------------|------|
| `boxObservationalRefl` | LHS → RHS forward bridge |
| `boxObservationalRefl_toRaw` | raw projection of the forward bridge |
| `boxObservationalRefl_onCanonical` | canonical-input simplification |
| `observationalBoxRefl` | RHS → LHS backward bridge |
| `observationalBoxRefl_toRaw` | raw projection of the backward bridge |
| `observationalBoxRefl_onCanonical` | canonical-input simplification |
| `boxObservationalRefl_roundTrip_onRefl` | LHS → RHS → LHS = id |
| `observationalBoxRefl_roundTrip_onRefl` | RHS → LHS → RHS = id |
| `boxObservationalRefl_roundTrip_toRaw` | raw smoke for LHS round trip |
| `observationalBoxRefl_roundTrip_toRaw` | raw smoke for RHS round trip |

## Scope advisory

These are RFL-FRAGMENT bridges only.  The headline `Equiv (□ (Ty.id A x y))
(Ty.id (□ A) (boxIntro x) (boxIntro y))` is gated on Phase 12.A.6+
infrastructure (typed `Term.boxIntro` / `Term.boxElim` ctors that
promote `innerType` to `Ty.modal Modality.box innerType`).  See the
header docstring of `Bridge/BoxObservational.lean` for the detailed
shipping-plan analysis.
-/

namespace LeanFX2.Smoke

#print axioms LeanFX2.Bridge.boxObservationalRefl
#print axioms LeanFX2.Bridge.boxObservationalRefl_toRaw
#print axioms LeanFX2.Bridge.boxObservationalRefl_onCanonical
#print axioms LeanFX2.Bridge.observationalBoxRefl
#print axioms LeanFX2.Bridge.observationalBoxRefl_toRaw
#print axioms LeanFX2.Bridge.observationalBoxRefl_onCanonical
#print axioms LeanFX2.Bridge.boxObservationalRefl_roundTrip_onRefl
#print axioms LeanFX2.Bridge.observationalBoxRefl_roundTrip_onRefl
#print axioms LeanFX2.Bridge.boxObservationalRefl_roundTrip_toRaw
#print axioms LeanFX2.Bridge.observationalBoxRefl_roundTrip_toRaw

end LeanFX2.Smoke
