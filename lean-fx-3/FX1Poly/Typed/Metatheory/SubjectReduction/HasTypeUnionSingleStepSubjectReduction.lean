import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionSingleStepSubjectReduction
    — the single-step union subject-reduction master, assembled modulo two named closers — TYTAB-2-FT gate 2

This file assembles the **single-step union subject reduction master** (gate 2 of TYTAB-2-FT, #1697) out of
the shipped root-step dispatcher `unionRootStepSubjectReduction`, exposing exactly the two residual closers as
named gate interfaces.  It is the standard-shape (`∃ pinned, … ∧ Conv pinned classifier`) and the
classifier-PRESERVING (`… reduct classifier`) reformulations that the consistency route
(`coreFragmentConsistencyOfSnAndSingleStepSR`) consumes — turning the 3-way disjunction surfaced by the
dispatcher into a drop-in subject-reduction function.

## The dispatcher and the two residual gates

`unionRootStepSubjectReduction typed step` classifies an arbitrary single `Step` of a union-typed term into
exactly three honest outcomes (see its docstring):

  1. the reduct is union-typed at a classifier `Conv`-equal to the original (the seven branch-selection ι,
     PROVEN inside the dispatcher);
  2. the step is a top-level child CONGRUENCE (surfaced as the `.mkGen` cong shape — the conv wall);
  3. the redex is one of the deferred substituting / constructor-elimination shapes
     (`IsDeferredRootRedexShape`: β + the nine remaining ι + endpoint-β).

Outcomes 2 and 3 are the residuals.  This file names them as `UnionCongruenceCloser` and
`UnionDeferredRedexCloser` — Prop-valued gate interfaces over `(profile, context, classifier)` — and the
master discharges outcome 1 inline, leaving the two closers as hypotheses.  Both closers are genuine remaining
work, but of very different character:

  * the **deferred-redex** closer is ASSEMBLY of already-shipped per-shape closers
    (`unionSubjectReductionBetaFromRedex`, `unionSubjectReductionEndpointBetaFromRedex`, the
    `subjectReductionOnIotaRedex` bundle interface) — the pieces exist, the unified wiring across the eleven
    `IsDeferredRootRedexShape` shapes is the follow-up;
  * the **congruence** closer is the genuine native mountain (re-type a parent cell when one child steps,
    absorbing dependent-output drift through `conv` and re-typing the cross-referencing obligations — the
    native analogue of the unconditional grown `HasTypeDescPi.subjectReduction`).

## Zero-axiom verification

Pure assembly: `unionRootStepSubjectReduction` (the dispatcher), `HasTypeUnion.reclassifyToType` (the conv
arm), and `HasTypeUnion.classifierIsType` (the unconditional validity) — every cited carrier is already
zero-axiom.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Gate interface — the deferred-redex closer.**  Every `IsDeferredRootRedexShape` redex (β + the nine
substituting / constructor-elimination ι + endpoint-β) typed at `classifier` subject-reduces to a reduct
union-typed at a `Conv`-equal classifier.  Assembled from the shipped per-shape closers (the redex half of
gate 2). -/
def UnionDeferredRedexCloser (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  ∀ {redexShape reductShape : RawTerm scope},
    HasTypeUnion profile context redexShape classifier →
    IsDeferredRootRedexShape redexShape →
    Step redexShape reductShape →
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context reductShape pinned ∧ Conv pinned classifier

/-- **Gate interface — the congruence closer.**  When one child of a `.mkGen` cell typed at `classifier`
steps, the re-formed cell is union-typed at a `Conv`-equal classifier.  The genuine native mountain (the
conv wall): the native analogue of the unconditional grown `HasTypeDescPi.subjectReduction`'s congruence
dispatch. -/
def UnionCongruenceCloser (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) : Prop :=
  ∀ {generator : Generator} {payload : generator.payload scope}
    {childrenBefore childrenAfter : RawTermChildren generator.binderShifts scope},
    HasTypeUnion profile context (.mkGen generator payload childrenBefore) classifier →
    StepChildren childrenBefore childrenAfter →
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (.mkGen generator payload childrenAfter) pinned ∧
      Conv pinned classifier

/-- **★ The single-step union subject-reduction master (up to `Conv`), modulo the two closers.**  For any
single `Step subject reduct` of a union-typed term, the reduct is union-typed at a classifier `Conv`-equal
to the original.  The dispatcher `unionRootStepSubjectReduction` routes the step into the proven
branch-selection ι (discharged inline), the congruence shape (→ `UnionCongruenceCloser`), or the deferred
substituting / constructor-elimination shapes (→ `UnionDeferredRedexCloser`).  This is the standard-shape
reformulation of gate 2: the 3-way disjunction collapses to the single subject-reduction conclusion once the
two named gates land. -/
theorem HasTypeUnion.singleStepSubjectReductionFromClosers {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (deferredRedexCloser : UnionDeferredRedexCloser profile context classifier)
    (congruenceCloser : UnionCongruenceCloser profile context classifier)
    (step : Step subject reduct) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context reduct pinned ∧ Conv pinned classifier := by
  rcases unionRootStepSubjectReduction typed step with
    typedReduct |
    ⟨generator, payload, childrenBefore, childrenAfter, redexEq, reductEq, childStep⟩ |
    deferredShape
  · exact typedReduct
  · subst redexEq
    subst reductEq
    exact congruenceCloser typed childStep
  · exact deferredRedexCloser typed deferredShape step

/-- **★ The classifier-PRESERVING single-step union subject-reduction master, modulo the two closers.**  Same
as `singleStepSubjectReductionFromClosers` but landing the reduct at the EXACT original classifier (not merely
`Conv`-equal): the up-to-`Conv` reduct is reclassified back via the conv arm `HasTypeUnion.reclassifyToType`,
whose type-of-the-classifier obligation is discharged unconditionally by the validity
`HasTypeUnion.classifierIsType` over `WfContextUnion`.  This is the exact shape the consistency gate
`coreFragmentConsistencyOfSnAndSingleStepSR`'s `singleStepSubjectReduction` hypothesis demands
(`… start C → Step start finish → … finish C`). -/
theorem HasTypeUnion.singleStepSubjectReductionPreservingFromClosers {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (deferredRedexCloser : UnionDeferredRedexCloser profile context classifier)
    (congruenceCloser : UnionCongruenceCloser profile context classifier)
    (step : Step subject reduct) :
    HasTypeUnion profile context reduct classifier := by
  obtain ⟨pinned, reductTyped, convPinnedClassifier⟩ :=
    HasTypeUnion.singleStepSubjectReductionFromClosers typed deferredRedexCloser congruenceCloser step
  exact HasTypeUnion.reclassifyToType reductTyped convPinnedClassifier
    (HasTypeUnion.classifierIsType typed wellFormed)

end FX1Poly.Typed
