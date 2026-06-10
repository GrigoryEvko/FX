import FX1Poly.Typed.ClosedNormalForm
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ClosedNonConvertibility
    — the NEGATIVE non-vacuity capstone of the closed decision/extraction lane

`ClosedConvDecision.lean` decides conversion of closed FT-certified terms and `betaRedexConvertsToReduct`
witnessed the POSITIVE direction (a genuinely convertible pair: the β-redex converts to its reduct).  This file
ships the NEGATIVE direction — PROVEN non-convertibilities — so the decidable-`Conv` lane is demonstrably
non-trivial in BOTH directions (it decides genuinely convertible AND genuinely non-convertible closed pairs).

The engine is `Conv.iff_eq_of_noStep` (`FX1Poly/Core/ConvNormalForm.lean`): when neither endpoint can step,
conversion collapses to syntactic equality (rigidity — a `Conv` common reduct reached by no steps must equal
each endpoint).  Specialized to the `isStepNormalForm` predicate it reads: **on closed normal terms,
conversion IS syntactic equality** (`closedNormalConv_iff_syntacticEq`).  Then two closed normal terms with
DIFFERENT head generators cannot be convertible — `Generator.noConfusion` on the head-generator projection of
the forced equality.

These results are UNCONDITIONAL and do NOT use the fundamental theorem or strong normalization at all: the
terms are normal by `rfl` (`isStepNormalForm` computes on a leaf / a redex-free cell), and rigidity needs only
`isStepNormalForm_blocks_step`.  They stand on the raw substrate alone — the cleanest possible non-convertibility
proofs.

## Zero-axiom verification

`Conv.iff_eq_of_noStep` + `isStepNormalForm_blocks_step` + `Generator.noConfusion (congrArg RawTerm.headGenerator …)`.
Normality is `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **On closed normal terms, conversion is syntactic equality.**  The `isStepNormalForm`-stated
specialization of the core rigidity lemma `Conv.iff_eq_of_noStep` (which takes raw "no outgoing step"
functions): two structurally-normal closed terms convert iff they are equal.  The reusable seed for every
closed non-convertibility below — and the honest characterization that, on the normal-form fragment,
conversion carries no information beyond syntactic identity. -/
theorem closedNormalConv_iff_syntacticEq {leftTerm rightTerm : RawTerm 0}
    (leftNormal : RawTerm.isStepNormalForm leftTerm)
    (rightNormal : RawTerm.isStepNormalForm rightTerm) :
    Conv leftTerm rightTerm ↔ leftTerm = rightTerm :=
  Conv.iff_eq_of_noStep
    (fun reduct step => RawTerm.isStepNormalForm_blocks_step leftNormal reduct step)
    (fun reduct step => RawTerm.isStepNormalForm_blocks_step rightNormal reduct step)

/-- **Negative non-vacuity (1/3): a closed universe code is NOT convertible to the identity function.**
Both are normal (`rfl`); their head generators differ (`gen_universeCode` vs `gen_lam`), so by the
normal-form characterization a conversion would force the impossible syntactic equality. -/
theorem closedUniverseCode_not_conv_identity (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (universeCodeCell levelExpr flag : RawTerm 0)
        (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := by
  intro convertibility
  have universeNormal :
      RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm 0) := rfl
  have identityNormal :
      RawTerm.isStepNormalForm
        (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) := rfl
  have termsEqual :=
    (closedNormalConv_iff_syntacticEq universeNormal identityNormal).mp convertibility
  exact Generator.noConfusion (congrArg RawTerm.headGenerator termsEqual)

/-- **Negative non-vacuity (2/3): a closed universe code is NOT convertible to a Π type code.**  Head
generators `gen_universeCode` vs `gen_piTyCode` differ. -/
theorem closedUniverseCode_not_conv_piCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (universeCodeCell levelExpr flag : RawTerm 0)
        (piTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)) := by
  intro convertibility
  have universeNormal :
      RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm 0) := rfl
  have piCodeNormal :
      RawTerm.isStepNormalForm
        (piTyCodeCell (universeCodeCell levelExpr flag)
          (universeCodeCell levelExpr flag) : RawTerm 0) := rfl
  have termsEqual :=
    (closedNormalConv_iff_syntacticEq universeNormal piCodeNormal).mp convertibility
  exact Generator.noConfusion (congrArg RawTerm.headGenerator termsEqual)

/-- **Negative non-vacuity (3/3): the closed identity is NOT convertible to a Π type code.**  Head generators
`gen_lam` vs `gen_piTyCode` differ. -/
theorem closedIdentity_not_conv_piCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0)
        (piTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)) := by
  intro convertibility
  have identityNormal :
      RawTerm.isStepNormalForm
        (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) : RawTerm 0) := rfl
  have piCodeNormal :
      RawTerm.isStepNormalForm
        (piTyCodeCell (universeCodeCell levelExpr flag)
          (universeCodeCell levelExpr flag) : RawTerm 0) := rfl
  have termsEqual :=
    (closedNormalConv_iff_syntacticEq identityNormal piCodeNormal).mp convertibility
  exact Generator.noConfusion (congrArg RawTerm.headGenerator termsEqual)

end FX1Poly.Typed
