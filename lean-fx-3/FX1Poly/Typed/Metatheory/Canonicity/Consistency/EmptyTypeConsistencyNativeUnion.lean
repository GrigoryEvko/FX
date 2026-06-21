import FX1Poly.Typed.Engine.Union.HasTypeUnionEmptyCanonicalForms
import FX1Poly.Core.Metatheory.Normalization.Core.WeakNormalization
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction

/-! # FX1Poly/Typed/Metatheory/Canonicity/Consistency/EmptyTypeConsistencyNativeUnion
    — NATIVE consistency over the union bundle, the assembled route + its three named gates — TYTAB-2-FT

This file pins the **consistency leg of TYTAB-2-FT (#1697)** over the native union judgment and corrects a
strategy mistake worth recording.

## The finding: the union's empty type is SUBSTANTIVE (so the cheap validity route is BLOCKED)

The grown engine proved consistency the easy way (`HasTypeDescPi.emptyTypeConsistency`, the validity route):
`gen_emptyCode` has no grown formation rule (`typingRuleDescOf gen_emptyCode = none`), so `emptyTypeCell` is not
even a type, so nothing is typed AT it.  That route does NOT transfer to the union: the union bundle DOES give
`gen_emptyCode` a base-type formation row — `fxTypingBundle.formationRule gen_emptyCode = some (baseType Type@0)`
(mechanically observed: a `formationRule`-arm derivation types `emptyTypeCell` at `Type@0`).  So in the native
kernel `emptyTypeCell` IS a real, substantive type, and native consistency is the GENUINE statement — the empty
type is real AND uninhabited — which (exactly as the grown `EmptyTypeConsistencyUnconditional` header warned for
the substantive regime) must route through canonicity / SN, NOT validity.

## The assembled route — three named gates

Mirroring the proven grown `HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType`
(`ConsistencyConditionalOnSubjectReduction.lean`): strong-normalize the closed subject to a normal form, carry
the `emptyTypeCell` classifier down the chain (subject reduction), and refute a closed-NORMAL inhabitant.  For
the grown engine SN and canonical-forms were already shipped, so only SR-star was a hypothesis.  For the union
the open FT lane leaves THREE genuine gates — named here as explicit hypotheses (the conditional-package
discipline: assemble the plumbing, expose exactly what remains):

  1. `nativeStronglyNormalizing` — open SN for the union (the FUNDAMENTAL THEOREM, FTGEN-9 / FTGEN-11 data
     intro/elim reducibility assembled over the bundle: the real mountain).
  2. `subjectReductionStar` — the iterated union subject reduction along `↝*` (the single-step bundle SR is
     unconditional post-#1701 SRINV; its `StepStar.rec` closure is mechanical).
  3. `closedNormalCanonicity` — no closed NORMAL term is union-typed at `emptyTypeCell` (the union analogue of
     `closedNormalEmptyTypeUninhabited`: a closed-normal-form inversion that routes a union typing into the
     dataIntroNullary / baseType / grown cases, then applies the shipped `closedNormalEmptyTypeUninhabited`).

When all three land, `consistencyOfNativeSubjectReduction` becomes the UNCONDITIONAL native consistency
`HasTypeUnion .empty t EmptyType → False` — the #1697 headline.  This file ships the assembly + the precise gate
list so the remaining work is exactly three self-contained lemmas, not an implicit route.

## Zero-axiom verification

A `StepStar.rec`-free plumbing: `exists_normalForm_of_isStronglyNormalizing` (weak normalization) composed with
the three hypotheses.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **★ NATIVE consistency, gated on the three FT-lane residuals (TYTAB-2-FT route).**  A closed term typed at
the substantive empty type yields `False`, given (1) native strong normalization, (2) iterated union subject
reduction, and (3) closed-normal canonicity at the empty type.  Strong normalization reaches a normal form;
subject reduction carries the `emptyTypeCell` classifier to it; closed-normal canonicity refutes it.  The native
twin of `HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType`, with SN and canonicity additionally exposed
(the grown engine had them shipped; the union does not yet).  Becomes unconditional once the native FT lands. -/
theorem HasTypeUnion.consistencyOfNativeSubjectReduction {profile : PolyProfile}
    {subject : RawTerm 0}
    (nativeStronglyNormalizing : IsStronglyNormalizing subject)
    (subjectReductionStar : ∀ {start finish : RawTerm 0},
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) start
        (emptyTypeCell (scope := 0)) →
      StepStar start finish →
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) finish
        (emptyTypeCell (scope := 0)))
    (closedNormalCanonicity : ∀ {normalForm : RawTerm 0},
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) normalForm
        (emptyTypeCell (scope := 0)) →
      RawTerm.isStepNormalForm normalForm →
      False)
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing nativeStronglyNormalizing
  exact closedNormalCanonicity (subjectReductionStar typed reachesNormalForm) normalFormIsNormal

/-- **Iterated union subject reduction from the single-step master.**  Lifts a single-step union
subject-reduction `HasTypeUnion … s C → Step s f → HasTypeUnion … f C` to the `StepStar` closure by induction
on the chain (the `refl`/`trans` recursor).  This is the mechanical half of gate 2: once the single-step union
SR master is assembled (the per-row SR is unconditional post-SRINV #1701, this only needs the cross-step-kind
dispatch), `subjectReductionStar` follows with no extra hypothesis.  Generic in context and classifier. -/
theorem HasTypeUnion.subjectReductionStarFromSingleStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (singleStep : ∀ {start finish : RawTerm scope},
      HasTypeUnion profile context start classifier → Step start finish →
      HasTypeUnion profile context finish classifier) :
    ∀ {start finish : RawTerm scope}, StepStar start finish →
      HasTypeUnion profile context start classifier →
      HasTypeUnion profile context finish classifier := by
  intro start finish chain
  induction chain with
  | refl _term => intro typed; exact typed
  | trans step _rest ih => intro typed; exact ih (singleStep typed step)

/-- **★ NATIVE consistency from the SINGLE-STEP union SR master (gate 2 reduced).**  Same as
`consistencyOfNativeSubjectReduction` but consuming the single-step union subject-reduction master instead of
its `StepStar` closure — the lift is supplied internally by `subjectReductionStarFromSingleStep`.  So the three
residuals collapse to: native SN, the single-step union SR master, and closed-normal canonicity. -/
theorem HasTypeUnion.consistencyOfNativeSingleStepSubjectReduction {profile : PolyProfile}
    {subject : RawTerm 0}
    (nativeStronglyNormalizing : IsStronglyNormalizing subject)
    (singleStepSubjectReduction : ∀ {start finish : RawTerm 0},
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) start
        (emptyTypeCell (scope := 0)) →
      Step start finish →
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) finish
        (emptyTypeCell (scope := 0)))
    (closedNormalCanonicity : ∀ {normalForm : RawTerm 0},
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) normalForm
        (emptyTypeCell (scope := 0)) →
      RawTerm.isStepNormalForm normalForm →
      False)
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeUnion.consistencyOfNativeSubjectReduction nativeStronglyNormalizing
    (fun startTyped chain =>
      HasTypeUnion.subjectReductionStarFromSingleStep singleStepSubjectReduction chain startTyped)
    closedNormalCanonicity typed

/-- **★ GATE 3 DISCHARGED — native consistency on the core beta/iota fragment from SN + single-step SR.**  The
closed-normal canonicity gate of `consistencyOfNativeSingleStepSubjectReduction` is no longer a hypothesis: it
is supplied by the shipped `HasTypeUnion.closedNormalEmptyTypeHasNoInhabitant` (gate 3, the empty-type twin of
the lane master `closedNormalLaneCanonicalForms`).  What remains is exactly two residuals plus the fragment
bookkeeping the entire canonicity layer already shares:

  1. `nativeStronglyNormalizing` — native open SN (the FUNDAMENTAL THEOREM, FTGEN data intro/elim over the
     bundle: gate 1, the real mountain).
  2. `singleStepSubjectReduction` — the single-step union SR master (gate 2; its `StepStar` closure is
     supplied internally by `subjectReductionStarFromSingleStep`, and its per-row half is unconditional
     post-#1701 SRINV).
  3. `reductsPathAppFree` / `reductsPathLamFree` — every reduct stays on the core beta/iota fragment (no
     `pathApp` / `pathLam`).  This is the SAME boundary the lane-master canonicity lives on (reduction never
     synthesizes a fresh generator), not a new assumption about consistency — purely the WAVE-2 fragment line.

Strong-normalize to a normal form, carry the `emptyTypeCell` classifier down (gate 2), and refute the
closed-normal inhabitant (gate 3).  When SN and the SR master land, this is unconditional native consistency on
the core fragment — the discharged form of `consistencyOfNativeSubjectReduction`. -/
theorem HasTypeUnion.coreFragmentConsistencyOfSnAndSingleStepSR {profile : PolyProfile}
    {subject : RawTerm 0}
    (nativeStronglyNormalizing : IsStronglyNormalizing subject)
    (singleStepSubjectReduction : ∀ {start finish : RawTerm 0},
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) start
        (emptyTypeCell (scope := 0)) →
      Step start finish →
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) finish
        (emptyTypeCell (scope := 0)))
    (reductsPathAppFree : ∀ {reduct : RawTerm 0}, StepStar subject reduct →
      RawTerm.containsGeneratorBool .gen_pathApp reduct = false)
    (reductsPathLamFree : ∀ {reduct : RawTerm 0}, StepStar subject reduct →
      RawTerm.containsGeneratorBool .gen_pathLam reduct = false)
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing nativeStronglyNormalizing
  have typedNormalForm :
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) normalForm
        (emptyTypeCell (scope := 0)) :=
    HasTypeUnion.subjectReductionStarFromSingleStep singleStepSubjectReduction reachesNormalForm typed
  exact HasTypeUnion.closedNormalEmptyTypeHasNoInhabitant typedNormalForm normalFormIsNormal
    (reductsPathAppFree reachesNormalForm) (reductsPathLamFree reachesNormalForm)

/-- **★ NATIVE consistency reduced to native SN + the two single-step SR closers (gate 2 fully decomposed).**
The classifier-preserving single-step union SR master `singleStepSubjectReductionPreservingFromClosers`
discharges the `singleStepSubjectReduction` gate of `coreFragmentConsistencyOfSnAndSingleStepSR` directly
from the two named closers (`UnionDeferredRedexCloser` / `UnionCongruenceCloser` at the empty context /
empty type) — the empty-context well-formedness obligation is the trivial `WfContextUnion.empty`.  So native
core-fragment consistency now rests on exactly THREE residuals, each a self-contained gate:

  1. `nativeStronglyNormalizing` — native open SN (gate 1, the FUNDAMENTAL THEOREM: FTGEN data intro/elim
     reducibility over the bundle, the real mountain);
  2. `deferredRedexCloser` — the redex half of gate 2 (assembly of the shipped per-shape redex closers:
     `unionSubjectReductionBetaFromRedex`, `unionSubjectReductionEndpointBetaFromRedex`, the
     `subjectReductionOnIotaRedex` bundle interface across the eleven `IsDeferredRootRedexShape` shapes);
  3. `congruenceCloser` — the congruence half of gate 2 (the native mountain: re-type a parent cell when one
     child steps, the native analogue of the unconditional grown `HasTypeDescPi.subjectReduction`).

`reductsPathAppFree` / `reductsPathLamFree` are the shared WAVE-2 core-fragment bookkeeping (reduction never
synthesises a fresh `pathApp`/`pathLam`), not a consistency assumption.  When the three gates land, this is
unconditional native consistency on the core β/ι fragment.  Pure composition — zero-axiom. -/
theorem HasTypeUnion.coreFragmentConsistencyFromClosers {profile : PolyProfile}
    {subject : RawTerm 0}
    (nativeStronglyNormalizing : IsStronglyNormalizing subject)
    (deferredRedexCloser : UnionDeferredRedexCloser profile
      (TypingContext.empty : TypingContext profile 0) (emptyTypeCell (scope := 0)))
    (congruenceCloser : UnionCongruenceCloser profile
      (TypingContext.empty : TypingContext profile 0) (emptyTypeCell (scope := 0)))
    (reductsPathAppFree : ∀ {reduct : RawTerm 0}, StepStar subject reduct →
      RawTerm.containsGeneratorBool .gen_pathApp reduct = false)
    (reductsPathLamFree : ∀ {reduct : RawTerm 0}, StepStar subject reduct →
      RawTerm.containsGeneratorBool .gen_pathLam reduct = false)
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False :=
  HasTypeUnion.coreFragmentConsistencyOfSnAndSingleStepSR nativeStronglyNormalizing
    (fun startTyped step =>
      HasTypeUnion.singleStepSubjectReductionPreservingFromClosers startTyped WfContextUnion.empty
        deferredRedexCloser congruenceCloser step)
    reductsPathAppFree reductsPathLamFree typed

end FX1Poly.Typed
