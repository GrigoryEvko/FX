import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDrift
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimObligationsDrift
    — SR-DSL-4 driver: fold the per-obligation reclassifier over an eliminator's obligation list

When one child of an eliminator cell steps, the obligation list `rule.obligations … args …` drifts to
`rule.obligations … argsAfter …`.  This file ships the GENERIC driver that re-establishes the whole drifted list:
the relation `ObligationsDrift` packages the positional per-obligation drift (each obligation's subject + classifier
reduce by `StepStar`, the context unchanged), and `premisesHoldUnderObligationsDrift` folds the SR-DSL-4 atom
`obligationReclassifiesUnderDrift` along it.

`ObligationsDrift` is the CONTEXT-FIXED case — it requires `oBefore.context = oAfter.context`.  This covers EVERY
context-fixed obligation position: all of `app` / `pathApp` / `fst` / `snd` (param-only classifiers, no binder-
extended branches), AND every non-motive arg position of every recursor.  The binder-EXTENDED branch obligations
(natElim / natRec step branch at `scope + 2`, listElim cons at `scope + 3`, idJ) carry a context that itself reads
the motive, so when the motive steps THAT context drifts — those positions need the context-conversion extension
(a later increment) and are NOT covered here.

The per-position drift data (`subjectDrift` / `classifierDrift`) is exactly what the directed engine produces: a
single arg step lifts to `StepStarChildren` (`StepChildren.toStepStarChildren`), then `templateStepStarUnderChildStep`
(SR-DSL-2) drives the classifier `StepStar`, and the subject projection drives the subject `StepStar`.  This driver
only CONSUMES the packaged drifts — the reification (SR-DSL-0c per-row) supplies them.

## Zero-axiom

A plain induction on the `ObligationsDrift` relation threading `List.Mem.head` / `List.Mem.tail`, each head case
the SR-DSL-4 atom.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Positional per-obligation drift of an eliminator's obligation list (context-fixed).**  Each corresponding
pair of obligations shares scope + context, and the after-obligation's subject / classifier are `StepStar`-reachable
from the before-obligation's — exactly the drift a single child step induces on the obligations whose context does
not read the stepping child.  Carries the before-classifier's formedness (universe-typedness) so the driver can
hand it to `obligationReclassifiesUnderDrift`. -/
inductive ObligationsDrift (profile : PolyProfile) :
    List (ElimObligation profile) → List (ElimObligation profile) → Prop where
  | nil : ObligationsDrift profile [] []
  | cons {scope : Nat} {context : TypingContext profile scope}
      {subjectBefore subjectAfter classifierBefore classifierAfter : RawTerm scope}
      {restBefore restAfter : List (ElimObligation profile)}
      (subjectDrift : StepStar subjectBefore subjectAfter)
      (classifierDrift : StepStar classifierBefore classifierAfter)
      (classifierFormedBefore : UnionClassifierIsType profile context classifierBefore)
      (restDrift : ObligationsDrift profile restBefore restAfter) :
      ObligationsDrift profile
        ({ scope := scope, context := context, subject := subjectBefore, classifier := classifierBefore }
          :: restBefore)
        ({ scope := scope, context := context, subject := subjectAfter, classifier := classifierAfter }
          :: restAfter)

/-- **★ SR-DSL-4 driver — the obligation list re-holds after the drift.**  Given the obligations held before the
child step and the positional drift (`ObligationsDrift`), every drifted obligation holds: induct on the drift, the
head case is the SR-DSL-4 atom `obligationReclassifiesUnderDrift`, the tail recurses.  This is the context-fixed
core of `premisesHoldAfter` — the generic transform every clean obligation position dispatches to. -/
theorem premisesHoldUnderObligationsDrift {profile : PolyProfile}
    {obligationsBefore obligationsAfter : List (ElimObligation profile)}
    (drift : ObligationsDrift profile obligationsBefore obligationsAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    (∀ obligation ∈ obligationsBefore,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    ∀ obligation ∈ obligationsAfter,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  induction drift with
  | nil => intro _premisesHold obligation obligationMem; cases obligationMem
  | @cons scope context subjectBefore subjectAfter classifierBefore classifierAfter restBefore _restAfter
      subjectDrift classifierDrift classifierFormedBefore _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
          exact obligationReclassifiesUnderDrift
            (premisesHold
              { scope := scope, context := context, subject := subjectBefore, classifier := classifierBefore }
              (List.Mem.head restBefore))
            classifierFormedBefore subjectDrift classifierDrift childSubjectReduction
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem

end FX1Poly.Typed
