import FX1Poly.STC.FxLogicalRelation
import FX1Poly.Typed.TypedNormalizer
/-! # FX1Poly/STC/FxNormalization — normalizationViaSTC (the Axis 12 normalization rung)

The Axis 12 `normalizationTheorem` ledger level, witnessed: every
closed grown-typed FX term GLUES with its normalization evidence —
reaching a `Step`-normal form — in the canonical STC model's
vocabulary.  The third rung of the STC arc, completing the
glue-family trilogy (SN: `fxStcRelationAt`; canonicity:
`fxStcBoolRelation`; normalization: this module).

## Why no vacuity trap here (contrast with the bool canonicity glue)

The bool canonicity glue had to carry the combined 3-engine
disjunction because the GROWN engine types no closed bool.  The
normalization glue quantifies over ALL classifiers, and the grown
engine has plenty of closed inhabitants there (λ-terms, universe
codes, applications) — the relation reuses the generic
`ClosedTypedTerm` syntax side, and non-vacuity is pinned on a closed
β-REDEX (`identityApplicationClosedTyped`), where the normalizer does
real reduction work.

## The bridge

The semantic component is the KERNEL's normalizer triple —
`HasTypeDescPi.normalForm` (the computed normal form, SN-043
discharging termination) with its `normalForm_reducesTo` /
`normalForm_isStepNormalForm` correctness theorems — definitionally
(`normalizationViaSTC_semantic_isKernelWitness`).  BRIDGED, not
independent; independence stays HIT-blocked (see
`FxLogicalRelation.lean`).

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.STC

open FX1Poly.Core FX1Poly.Typed FX1Poly.Universe

/-- The normalization payload: the subject reaches a `Step`-normal
form.  (Weak normalization as the displayed evidence; the kernel
witness routes through strong normalization.) -/
def ReachesNormalForm (subject : RawTerm 0) : Prop :=
  ∃ value : RawTerm 0,
    StepStar subject value ∧ RawTerm.isStepNormalForm value

/-- ★ The FX STC normalization relation at a closed classifier: the
canonical model's `Glue` of closed grown-typed syntax with the
NORMALIZATION payload. -/
def fxStcNormalizationRelation (profile : PolyProfile)
    (classifier : RawTerm 0) : Type :=
  canonicalSTCModel.Glue (ClosedTypedTerm profile classifier)
    (fun typedTerm => PLift (ReachesNormalForm typedTerm.term))

/-- ★★ **normalizationViaSTC**: every closed grown-typed FX term GLUES
with its normalization evidence.  The semantic component is the
kernel's computed normal form (`HasTypeDescPi.normalForm`, typing as
the termination certificate) with its correctness theorems. -/
def normalizationViaSTC {profile : PolyProfile} {classifier : RawTerm 0}
    (typedTerm : ClosedTypedTerm profile classifier) :
    fxStcNormalizationRelation profile classifier :=
  ⟨typedTerm,
    ⟨⟨typedTerm.typed.normalForm,
      typedTerm.typed.normalForm_reducesTo,
      typedTerm.typed.normalForm_isStepNormalForm⟩⟩⟩

/-- The normalization headline, recovered FROM the glue: every closed
grown-typed term reaches a `Step`-normal form. -/
theorem normalizationViaSTC_extracts {profile : PolyProfile}
    {classifier : RawTerm 0}
    (typedTerm : ClosedTypedTerm profile classifier) :
    ReachesNormalForm typedTerm.term :=
  (normalizationViaSTC typedTerm).semantic.down

/-- The bridge pin: the glue's semantic component IS the kernel's
normalizer triple — the computed `normalForm` with its
reaches/is-normal correctness theorems — definitionally. -/
theorem normalizationViaSTC_semantic_isKernelWitness
    {profile : PolyProfile} {classifier : RawTerm 0}
    (typedTerm : ClosedTypedTerm profile classifier) :
    (normalizationViaSTC typedTerm).semantic
      = ⟨⟨typedTerm.typed.normalForm,
          typedTerm.typed.normalForm_reducesTo,
          typedTerm.typed.normalForm_isStepNormalForm⟩⟩ := rfl

/-- Round-trip: the glue carries exactly the input syntax (no
laundering through the relation). -/
theorem normalizationViaSTC_syntactic_eq {profile : PolyProfile}
    {classifier : RawTerm 0}
    (typedTerm : ClosedTypedTerm profile classifier) :
    (normalizationViaSTC typedTerm).syntactic = typedTerm := rfl

/-! ## Non-vacuity: a closed typed β-redex glues -/

/-- The closed β-redex `(λ(x : Type@(e+1)). x) (Type@e)` as a
grown-typed closed term — the normalizer does REAL reduction work on
this subject (it is not already normal). -/
def identityApplicationClosedTyped (profile : PolyProfile)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ClosedTypedTerm profile (universeCodeCell levelExpr.lsucc flag) :=
  ⟨_, identityApplicationOnUniverseCode_hasTypeDescPi levelExpr flag⟩

/-- NON-VACUITY smoke: `normalizationViaSTC` at the closed β-redex is
a genuine glue carrying that redex as its syntax. -/
theorem normalizationViaSTC_betaRedex_nonVacuous (profile : PolyProfile)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    (normalizationViaSTC
        (identityApplicationClosedTyped profile levelExpr flag)).syntactic.term
      = appCell
          (lamCell (universeCodeCell levelExpr.lsucc flag)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag) := rfl

end FX1Poly.STC
