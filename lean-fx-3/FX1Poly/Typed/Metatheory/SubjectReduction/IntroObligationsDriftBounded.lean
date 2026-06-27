import FX1Poly.Typed.Metatheory.SubjectReduction.ObligationReclassifiesUnderDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroObligationsDriftBounded
    — SR-WF-TIEOFF (intro third): the FUEL-BOUNDED obligation-drift driver

`ElimObligationsDrift.lean` ships the universal-child-SR obligation driver `premisesHoldUnderObligationsDrift`,
whose `cons` arm folds the SR-DSL-4 atom `obligationReclassifiesUnderDrift` along the OPAQUE `StepStar` subject and
classifier drifts — consuming the UNIVERSAL `UnionChildSubjectReduction`.  The SR-WF-TIEOFF fuel induction supplies
only the fuel-bounded `UnionChildSubjectReductionBelow profile bound`, which can re-type a stepping subject only when
that subject is STRICTLY SMALLER than the bound.  The universal driver cannot consume it: a generic `StepStar`'s
intermediates can exceed the bound, so the fold's recursion has no size handle.

But the INTRODUCER arm never produces a generic `StepStar`.  Inspecting every introducer branch
(`IntroGateBranches.lean`) shows each `cons` drift is built with EXACTLY:

  * a SUBJECT drift `StepStar.single <argStep>` (length 1 — the one stepping arg) or `StepStar.refl` (length 0 —
    a param or a non-stepping arg); NEVER a genuine multi-step chain, because introducer obligation subjects ARE
    the args / params directly, and one cell-child steps once; AND
  * a CLASSIFIER drift `StepStar.refl` — introducer obligation classifiers are params / universe-codes that do NOT
    read the args, so an arg step leaves them FIXED.

So the bounded driver needs child-SR only for a SINGLE-step subject at a size-bounded arg, with a FIXED classifier.
This file ships exactly that specialization:

  * `SubjectDriftBelow bound` — the introducer subject drift: `fixed` (subject unchanged) or `stepsBelow` (subject
    steps ONCE, with the source below the bound).  The honest length-≤-1 encoding the bounded predicate can consume.
  * `obligationReclassifiesUnderSubjectDriftBelow` — re-establish one obligation at a FIXED classifier under a
    `SubjectDriftBelow` (the `fixed` case is `id`; the `stepsBelow` case is the committed atom
    `subjectReductionAtFixedClassifierStepBelow`).
  * `ObligationsDriftBelow profile bound` — the bounded obligation-list drift: the `cons` arm FIXES the
    classifier (faithful to introducers + the clean eliminators `app`/`pathApp`/`fst`/`snd` — no classifier drift)
    and carries a `SubjectDriftBelow`; the `consClassifierConv` arm is the CONTEXT-FIXED classifier-drift case
    (the dependent recursors' branch obligations when the MOTIVE steps — subject FIXED, classifier drifts via a
    `Conv`, the after-formedness supplied DIRECTLY so NO child-SR folds the multi-step branch-classifier chain);
    the `consContextHeadConv` arm is VERBATIM the universal driver's binder-extended case (the `lam` domain-step
    and `natElim`/`natRec` motive-in-context-head drift, discharged by `convertHeadBinding` + `reclassifyToType`,
    with NO child-SR).
  * `premisesHoldUnderObligationsDriftBelow` — the fuel-bounded analogue of `premisesHoldUnderObligationsDrift`.

This relation now serves BOTH the introducer arm AND the eliminator arm of SR-WF-TIEOFF.  The eliminator's hard
MOTIVE case — where a branch classifier `C[motive]` drifts MULTI-STEP because the branch type reads the motive — is
handled NOT by folding child-SR along the `C[motive] ⟶* C[motiveAfter]` chain (the wall: that branch type can
exceed `memberCell.size` via a large type param, so the fuel-bounded child-SR cannot re-type it), but by the
`consClassifierConv` arm carrying `C[motiveAfter]` formed DIRECTLY — a type-formation-from-the-motive's-formedness
fact (the future `*_formedFromMotive` family), bounded-safe because the motive itself IS a structural cell-child
(`motive.size < memberCell.size`), so the fuel-bounded child-SR re-types the MOTIVE, not the whole branch type.

## Zero-axiom

A plain induction on `ObligationsDriftBelow` threading `List.Mem.head` / `List.Mem.tail`, each head case the
committed bounded atom or the binder-conversion pair.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The introducer SUBJECT drift, fuel-bounded.**  An introducer obligation's subject either stays FIXED (the
param / non-stepping-arg positions) or steps EXACTLY ONCE from a source strictly below the fuel bound (the one
stepping arg, a structural cell-child).  The honest length-≤-1 encoding of the `StepStar` the universal driver
carries — the bounded child-SR can consume each constructor directly. -/
inductive SubjectDriftBelow (bound : Nat) {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  | fixed (subject : RawTerm scope) : SubjectDriftBelow bound subject subject
  | stepsBelow {subjectBefore subjectAfter : RawTerm scope}
      (subjectStep : Step subjectBefore subjectAfter)
      (subjectBelow : subjectBefore.size < bound) :
      SubjectDriftBelow bound subjectBefore subjectAfter

/-- **An obligation re-holds at a FIXED classifier under a bounded subject drift.**  The introducer-arm specialization
of `obligationReclassifiesUnderDrift`: the classifier never moves (introducer classifiers are arg-free), so the only
work is walking the subject.  `fixed` returns the obligation untouched; `stepsBelow` is the committed bounded
single-step atom `subjectReductionAtFixedClassifierStepBelow`. -/
theorem obligationReclassifiesUnderSubjectDriftBelow {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {bound : Nat} {subjectBefore subjectAfter : RawTerm scope}
    (holds : HasTypeUnion profile context subjectBefore classifier)
    (classifierFormed : UnionClassifierIsType profile context classifier)
    (subjectDrift : SubjectDriftBelow bound subjectBefore subjectAfter)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound) :
    HasTypeUnion profile context subjectAfter classifier := by
  cases subjectDrift with
  | fixed => exact holds
  | stepsBelow subjectStep subjectBelow =>
      exact subjectReductionAtFixedClassifierStepBelow classifierFormed subjectStep subjectBelow
        childSubjectReductionBelow holds

/-- **Positional introducer obligation-list drift, fuel-bounded.**  The introducer specialization of
`ObligationsDrift`: the `cons` arm FIXES the classifier (introducer obligations face no classifier drift) and carries
a `SubjectDriftBelow` for the subject; the `consContextHeadConv` arm is VERBATIM the universal driver's
binder-extended case (the `lam` domain-step context-head drift). -/
inductive ObligationsDriftBelow (profile : PolyProfile) (bound : Nat) :
    List (ElimObligation profile) → List (ElimObligation profile) → Prop where
  | nil : ObligationsDriftBelow profile bound [] []
  | cons {scope : Nat} {context : TypingContext profile scope}
      {subjectBefore subjectAfter classifier : RawTerm scope}
      {modality : ObligationModality}
      {restBefore restAfter : List (ElimObligation profile)}
      (subjectDrift : SubjectDriftBelow bound subjectBefore subjectAfter)
      (classifierFormed : UnionClassifierIsType profile context classifier)
      (restDrift : ObligationsDriftBelow profile bound restBefore restAfter) :
      ObligationsDriftBelow profile bound
        ({ scope := scope, context := context, subject := subjectBefore, classifier := classifier,
            modality := modality } :: restBefore)
        ({ scope := scope, context := context, subject := subjectAfter, classifier := classifier,
            modality := modality } :: restAfter)
  | consClassifierConv {scope : Nat} {context : TypingContext profile scope}
      {subject classifierBefore classifierAfter : RawTerm scope}
      {modality : ObligationModality}
      {restBefore restAfter : List (ElimObligation profile)}
      (classifierConv : Conv classifierBefore classifierAfter)
      (classifierFormedAfter : UnionClassifierIsType profile context classifierAfter)
      (restDrift : ObligationsDriftBelow profile bound restBefore restAfter) :
      ObligationsDriftBelow profile bound
        ({ scope := scope, context := context, subject := subject, classifier := classifierBefore,
            modality := modality } :: restBefore)
        ({ scope := scope, context := context, subject := subject, classifier := classifierAfter,
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
      (restDrift : ObligationsDriftBelow profile bound restBefore restAfter) :
      ObligationsDriftBelow profile bound
        ({ scope := scope + 1, context := context.cons oldBinding, subject := subject,
            classifier := classifierBefore, modality := modality } :: restBefore)
        ({ scope := scope + 1, context := context.cons newBinding, subject := subject,
            classifier := classifierAfter, modality := modality } :: restAfter)

/-- **★ The introducer obligation-list re-holds after the drift, from the FUEL-BOUNDED child-SR.**  The bounded
analogue of `premisesHoldUnderObligationsDrift`: induct on `ObligationsDriftBelow`, the `cons` head case the bounded
fixed-classifier atom `obligationReclassifiesUnderSubjectDriftBelow`, the `consContextHeadConv` head case the
binder-conversion pair (`convertHeadBinding` + `reclassifyToType`, no child-SR), the tail recurses.  Consumes
`UnionChildSubjectReductionBelow profile bound` — exactly what the SR-WF-TIEOFF fuel IH supplies. -/
theorem premisesHoldUnderObligationsDriftBelow {profile : PolyProfile} {bound : Nat}
    {obligationsBefore obligationsAfter : List (ElimObligation profile)}
    (drift : ObligationsDriftBelow profile bound obligationsBefore obligationsAfter)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound) :
    (∀ obligation ∈ obligationsBefore,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    ∀ obligation ∈ obligationsAfter,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  induction drift with
  | nil => intro _premisesHold obligation obligationMem; cases obligationMem
  | @cons scope context subjectBefore subjectAfter classifier modality restBefore _restAfter
      subjectDrift classifierFormed _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
          exact obligationReclassifiesUnderSubjectDriftBelow
            (premisesHold
              { scope := scope, context := context, subject := subjectBefore, classifier := classifier,
                modality := modality }
              (List.Mem.head restBefore))
            classifierFormed subjectDrift childSubjectReductionBelow
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem
  | @consClassifierConv scope context subject classifierBefore classifierAfter modality restBefore _restAfter
      classifierConv classifierFormedAfter _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
          exact HasTypeUnion.reclassifyToType
            (premisesHold
              { scope := scope, context := context, subject := subject, classifier := classifierBefore,
                modality := modality }
              (List.Mem.head restBefore))
            classifierConv classifierFormedAfter
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem
  | @consContextHeadConv scope context oldBinding newBinding subject classifierBefore classifierAfter modality
      restBefore _restAfter bindingConv oldBindingFormed classifierConv classifierFormedAfter _restDrift restIH =>
      intro premisesHold obligation obligationMem
      cases obligationMem with
      | head =>
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
