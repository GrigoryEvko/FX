import LeanFX2.Bridge.BoxCubical

/-! # Smoke/AuditPhase12A9D97BoxCubical

Reviewer-facing `#print axioms` regression log for the rfl-fragment
box-cubical bridge shipped under tracker #1391 (D9.7).

Every declaration printed here MUST report "does not depend on any
axioms".  The strict-harness gate in
`Tools/AuditAll/AuditBridge.lean` is the canonical machine-enforced
checker; this file documents the intent for human review.

## What is audited

| Declaration | Role |
|-------------|------|
| `boxCubicalRefl` | LHS → RHS forward bridge |
| `boxCubicalRefl_toRaw` | raw projection of the forward bridge |
| `boxCubicalRefl_onCanonical` | canonical-input simplification |
| `cubicalBoxRefl` | RHS → LHS backward bridge |
| `cubicalBoxRefl_toRaw` | raw projection of the backward bridge |
| `cubicalBoxRefl_onCanonical` | canonical-input simplification |
| `boxCubicalRefl_roundTrip_onConstantPath` | LHS → RHS → LHS = id |
| `cubicalBoxRefl_roundTrip_onConstantPath` | RHS → LHS → RHS = id |
| `boxCubicalRefl_roundTrip_toRaw` | raw smoke for LHS round trip |
| `cubicalBoxRefl_roundTrip_toRaw` | raw smoke for RHS round trip |

## Scope advisory

These are RFL-FRAGMENT bridges only.  The headline `Equiv (□ (Path A x y))
(Path (□ A) (boxIntro x) (boxIntro y))` is gated on Phase 12.A.6+
infrastructure (typed `Term.boxIntro` / `Term.boxElim` ctors that
promote `innerType` to `Ty.modal Modality.box innerType`) AND a
proper transport-style commutation (D2.5.1 typed `transpBeta`
cascade — strategically deferred).  See the header docstring of
`Bridge/BoxCubical.lean` for the detailed shipping-plan analysis.
-/

namespace LeanFX2.Smoke

#print axioms LeanFX2.Bridge.boxCubicalRefl
#print axioms LeanFX2.Bridge.boxCubicalRefl_toRaw
#print axioms LeanFX2.Bridge.boxCubicalRefl_onCanonical
#print axioms LeanFX2.Bridge.cubicalBoxRefl
#print axioms LeanFX2.Bridge.cubicalBoxRefl_toRaw
#print axioms LeanFX2.Bridge.cubicalBoxRefl_onCanonical
#print axioms LeanFX2.Bridge.boxCubicalRefl_roundTrip_onConstantPath
#print axioms LeanFX2.Bridge.cubicalBoxRefl_roundTrip_onConstantPath
#print axioms LeanFX2.Bridge.boxCubicalRefl_roundTrip_toRaw
#print axioms LeanFX2.Bridge.cubicalBoxRefl_roundTrip_toRaw

end LeanFX2.Smoke
