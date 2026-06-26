import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDrift
import FX1Poly.Typed.Metatheory.ContextConversion.HasTypeUnionContextConversion
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimObligationsDrift
    — SR-DSL-4 driver: fold the per-obligation reclassifier over an eliminator's obligation list

When one child of an eliminator cell steps, the obligation list `rule.obligations … args …` drifts to
`rule.obligations … argsAfter …`.  This file ships the GENERIC driver that re-establishes the whole drifted list:
the relation `ObligationsDrift` packages the positional per-obligation drift (each obligation's subject + classifier
reduce by `StepStar`, the context unchanged), and `premisesHoldUnderObligationsDrift` folds the SR-DSL-4 atom
`obligationReclassifiesUnderDrift` along it.

`ObligationsDrift` has TWO constructors.  `cons` is the CONTEXT-FIXED case — it requires `oBefore.context =
oAfter.context`.  This covers EVERY context-fixed obligation position: all of `app` / `pathApp` / `fst` / `snd`
(param-only classifiers, no binder-extended branches), `optionMatch` / `eitherMatch` / `boolElim` / `listElim`
(their branch binders live INSIDE the branch TYPE at the ambient scope), AND every non-motive arg position of every
recursor.  `consContextHeadConv` is the BINDER-EXTENDED case — the `natElim` / `natRec` step branch sits at
`scope + 2` in the context `(… cons natType) cons motive`, whose HEAD binding IS the motive, so when the motive
steps that context's head drifts `motive ⟶ motiveAfter`.  This constructor converts the head binding
(`convertHeadBinding`) and reclassifies the (also drifted) classifier (`reclassifyToType`), with the after-classifier
formedness supplied DIRECTLY (it is NOT derivable from the before-formedness by SR — the SR keystone needs a fixed
context).  The subject is FIXED across the conversion (only the motive — a different child — steps).

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
      {modality : ObligationModality}
      {restBefore restAfter : List (ElimObligation profile)}
      (subjectDrift : StepStar subjectBefore subjectAfter)
      (classifierDrift : StepStar classifierBefore classifierAfter)
      (classifierFormedBefore : UnionClassifierIsType profile context classifierBefore)
      (restDrift : ObligationsDrift profile restBefore restAfter) :
      ObligationsDrift profile
        ({ scope := scope, context := context, subject := subjectBefore, classifier := classifierBefore,
            modality := modality } :: restBefore)
        ({ scope := scope, context := context, subject := subjectAfter, classifier := classifierAfter,
            modality := modality } :: restAfter)
  | consContextHeadConv {scope : Nat} {context : TypingContext profile scope}
      {oldBinding newBinding : RawTerm scope}
      {subject : RawTerm (scope + 1)} {classifierBefore classifierAfter : RawTerm (scope + 1)}
      {modality : ObligationModality}
      {restBefore restAfter : List (ElimObligation profile)}
      (bindingConv : Conv oldBinding newBinding)
      (oldBindingFormed : UnionClassifierIsType profile context oldBinding)
      (classifierConv : Conv classifierBefore classifierAfter)
      (classifierFormedAfter : UnionClassifierIsType profile (context.cons newBinding) classifierAfter)
      (restDrift : ObligationsDrift profile restBefore restAfter) :
      ObligationsDrift profile
        ({ scope := scope + 1, context := context.cons oldBinding, subject := subject,
            classifier := classifierBefore, modality := modality } :: restBefore)
        ({ scope := scope + 1, context := context.cons newBinding, subject := subject,
            classifier := classifierAfter, modality := modality } :: restAfter)

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
  | @cons scope context subjectBefore subjectAfter classifierBefore classifierAfter modality restBefore _restAfter
      subjectDrift classifierDrift classifierFormedBefore _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
          exact obligationReclassifiesUnderDrift
            (premisesHold
              { scope := scope, context := context, subject := subjectBefore, classifier := classifierBefore,
                modality := modality }
              (List.Mem.head restBefore))
            classifierFormedBefore subjectDrift classifierDrift childSubjectReduction
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem
  | @consContextHeadConv scope context oldBinding newBinding subject classifierBefore classifierAfter modality
      restBefore _restAfter bindingConv oldBindingFormed classifierConv classifierFormedAfter _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
          -- The before-obligation holds (subject typed over `cons oldBinding` at the before-classifier); convert the
          -- head binding `oldBinding ⟶ newBinding`, then reclassify the classifier along its own drift.
          have subjectTyped := premisesHold
            { scope := scope + 1, context := context.cons oldBinding, subject := subject,
              classifier := classifierBefore, modality := modality }
            (List.Mem.head restBefore)
          have subjectOverNewBinding := HasTypeUnion.convertHeadBinding subjectTyped bindingConv oldBindingFormed
          exact HasTypeUnion.reclassifyToType subjectOverNewBinding classifierConv classifierFormedAfter
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem

end FX1Poly.Typed
