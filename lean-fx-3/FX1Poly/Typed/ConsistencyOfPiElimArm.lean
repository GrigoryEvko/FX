import FX1Poly.Typed.HasTypeDescPiSubjectReductionMutual
import FX1Poly.Typed.ConsistencyConditionalOnSubjectReduction

/-! # FX1Poly/Typed/ConsistencyOfPiElimArm
    — iterated (multi-step) subject reduction + ★ SN-050 consistency, both conditional on EXACTLY the
      single `piElim` crux (SRD-3 `#846`, CON-A5wire `#848` / SN-050 `#553` / `#812`)

This file collapses the grown-engine consistency theorem onto the SAME single residual that the grown master
subject reduction (`HasTypeDescPiSubjectReductionMutual.lean`, SRD-2 `#845`) and the grown context-conversion
(`HasTypeDescPiContextConversionConditional.lean`, GCC-5 `#842`) are conditional on: the lone `piElim`
context-conversion arm (`piElimArm`, the mutual fundamental-metatheory crux = type-correctness + Π-injectivity
+ SR + context-conversion proven together).  After this file, **Milestone-A consistency is one lemma away**:
discharging `piElimArm` discharges the master SR, the iterated SR, AND consistency, all at once.

  * **`HasTypeDescPi.subjectReductionStarOfPiElimArm`** (SRD-3) — iterated subject reduction along a `StepStar`
    chain, conditional on `piElimArm`.  Structural recursion on the `StepStar` chain (`refl` returns the
    subject's typing unchanged; `trans firstStep rest` re-types the one-step reduct via the single-step master
    SR `HasTypeDescPi.subjectReductionOfPiElimArm`, then recurses on the tail under the SAME well-formedness —
    the classifier never changes, so the well-formedness is threaded verbatim).

  * **`HasTypeDescPi.consistencyOfPiElimArm`** (★ SN-050, conditional) — `HasTypeDescPi .empty t EmptyType`
    is uninhabited, conditional on EXACTLY `piElimArm`.  Composes the SR-along-↝* hypothesis of
    `consistencyOfSubjectReductionStarToEmptyType` (which itself bundles OB-5 open-SN `#794` +
    `exists_normalForm_of_isStronglyNormalizing` + `noClosedNormalTermAtEmptyType`) by instantiating the
    iterated SR at the empty context — `WfContextDescPi.emptyIsWellFormed` supplies the well-formedness, and the
    empty context is preserved verbatim through every reduction step.

This is the syntactic consistency route (CON-A6 `#837` shipped the unconditional grown closed-canonical-forms +
the `consistencyOfSubjectReductionStarToEmptyType` skeleton; this file plugs in the iterated SR so the residual
is exactly the one `piElim` arm).  The BFT bounded model CANNOT prove consistency — its `emptyTypeCell`
candidate is the coarse `IsStronglyNormalizing` (the `neutral` candidate arm), so the candidate is inhabited by
any SN term — which is why the syntactic SR-to-normal-form route is the tractable one.

## Zero-axiom verification

Structural recursion on the `StepStar` chain + the single-step master SR `subjectReductionOfPiElimArm` +
`consistencyOfSubjectReductionStarToEmptyType` + `WfContextDescPi.emptyIsWellFormed`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Iterated (multi-step) subject reduction, conditional on the `piElim` arm** (SRD-3).  A grown-typed subject
is preserved along an entire `StepStar` reduction chain, at the SAME classifier, given the lone `piElim`
context-conversion arm (`piElimArm`, the GCC-5 crux).  Structural recursion on the chain: `refl` returns the
typing unchanged; `trans firstStep rest` re-types the single-step reduct via the master SR
`HasTypeDescPi.subjectReductionOfPiElimArm`, then recurses on `rest` under the SAME `wellFormed` (the classifier
and context are invariant under reduction).  Discharging `piElimArm` yields unconditional iterated SR. -/
theorem HasTypeDescPi.subjectReductionStarOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : StepStar subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  match chain with
  | .refl _ => typed
  | .trans firstStep rest =>
      HasTypeDescPi.subjectReductionStarOfPiElimArm piElimArm wellFormed
        (HasTypeDescPi.subjectReductionOfPiElimArm piElimArm typed wellFormed _ firstStep) rest

/-- **★ SN-050 typed consistency, conditional on EXACTLY the single `piElim` crux.**  The empty type has no
closed inhabitant under the grown engine — `HasTypeDescPi .empty subject EmptyType → False` — conditional on the
lone `piElim` context-conversion arm (`piElimArm`, the GCC-5 fundamental-metatheory bundle).  Composes the
SR-along-↝* hypothesis of `consistencyOfSubjectReductionStarToEmptyType` by instantiating the iterated SR
`subjectReductionStarOfPiElimArm` at the empty context (`WfContextDescPi.emptyIsWellFormed`).  Discharging
`piElimArm` (which also discharges the master SR and context-conversion) closes Milestone-A consistency. -/
theorem HasTypeDescPi.consistencyOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType
    (fun startTyped chain =>
      HasTypeDescPi.subjectReductionStarOfPiElimArm piElimArm WfContextDescPi.emptyIsWellFormed
        startTyped chain)
    typed

end FX1Poly.Typed
