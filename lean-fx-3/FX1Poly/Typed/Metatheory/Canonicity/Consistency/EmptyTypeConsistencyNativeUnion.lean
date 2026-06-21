import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Core.Metatheory.Normalization.Core.WeakNormalization

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

end FX1Poly.Typed
