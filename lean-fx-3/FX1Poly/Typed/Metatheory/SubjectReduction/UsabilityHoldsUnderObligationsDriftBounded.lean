import FX1Poly.Typed.Metatheory.SubjectReduction.IntroObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.UsabilityHoldsUnderObligationsDrift

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/UsabilityHoldsUnderObligationsDriftBounded
    — the FUEL-BOUNDED usability companion of `premisesHoldUnderObligationsDriftBelow`

The fuel-bounded twin of `usabilityHoldsUnderObligationsDrift` (`UsabilityHoldsUnderObligationsDrift.lean`).  Where
the universal usability driver folds the SHIPPED unconditional `HasTypeUnion.stepPreservesFibrantSubjectUsability`
along an OPAQUE `StepStar` subject drift (lifted to `stepStarPreservesFibrantSubjectUsability`, threading
`UnionChildSubjectReduction` to re-type each intermediate), the BOUNDED introducer drift `ObligationsDriftBelow`
carries a `SubjectDriftBelow` — a subject drift of length AT MOST ONE (`fixed` | `stepsBelow`).  So the bounded
usability driver needs only the single-step preservation DIRECTLY: NO `StepStar` chain, hence NO intermediate
re-typing, hence NO `childSubjectReductionBelow` — a strictly weaker dependency than the bounded premise driver
`premisesHoldUnderObligationsDriftBelow`.

The three `ObligationsDriftBelow` arms transport usability:

  * `cons` — a `SubjectDriftBelow`: `fixed` keeps the subject (usability transports verbatim); `stepsBelow` steps
    the subject ONCE, transported by `HasTypeUnion.stepPreservesFibrantSubjectUsability` (the obligation is fibrant
    by `allFibrant`, typed by the before-premise).
  * `consClassifierConv` — only the CLASSIFIER drifts; the subject and context are FIXED, and
    `isSubjectUsableAtModality` reads neither classifier, so the before-usability IS the after-usability.
  * `consContextHeadConv` — only the head BINDING type drifts; the subject is FIXED, and usability reads only the
    cons/lockCons SKELETON (`isSubjectUsableAtModality_consHeadIrrelevant`), so usability transports definitionally.

## Zero-axiom verification

The SHIPPED unconditional `HasTypeUnion.stepPreservesFibrantSubjectUsability` + `isSubjectUsableAtModality_consHeadIrrelevant`
+ an `ObligationsDriftBelow` induction mirroring `premisesHoldUnderObligationsDriftBelow`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The A1-CONJUNCT-WIRE usability driver, fuel-bounded.**  The bounded twin of
`usabilityHoldsUnderObligationsDrift`: given the before-step obligation subjects fibrantly usable (the native arm's
`usabilityHolds`) and typed (`premisesHold`), every drifted obligation subject is usable at its modality.  Induct on
`ObligationsDriftBelow`: the `cons` head transports through the single-step `stepPreservesFibrantSubjectUsability`
(the bounded subject drift is length ≤ 1, so NO chain / NO child-SR); `consClassifierConv` keeps the subject and only
drifts the classifier (usability is classifier-blind); `consContextHeadConv` keeps the subject and only drifts the
head binding (usability is binding-type-blind); tails recurse. -/
theorem usabilityHoldsUnderObligationsDriftBelow {profile : PolyProfile} {bound : Nat}
    {obligationsBefore obligationsAfter : List (ElimObligation profile)}
    (drift : ObligationsDriftBelow profile bound obligationsBefore obligationsAfter) :
    (∀ obligation ∈ obligationsBefore, obligation.modality = ObligationModality.fibrant) →
    (∀ obligation ∈ obligationsBefore,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ obligationsBefore,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    ∀ obligation ∈ obligationsAfter,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  induction drift with
  | nil => intro _allFibrant _premisesHold _usabilityHolds obligation obligationMem; cases obligationMem
  | @cons scope context subjectBefore subjectAfter classifier modality restBefore _restAfter
      subjectDrift _classifierFormed _restDrift restIH =>
      intro allFibrant premisesHold usabilityHolds obligation obligationMem
      cases obligationMem with
      | head =>
          have headModalityFibrant : modality = ObligationModality.fibrant :=
            allFibrant _ (List.Mem.head restBefore)
          have beforeTyped := premisesHold
            { scope := scope, context := context, subject := subjectBefore, classifier := classifier,
              modality := modality }
            (List.Mem.head restBefore)
          have beforeUsable := usabilityHolds
            { scope := scope, context := context, subject := subjectBefore, classifier := classifier,
              modality := modality }
            (List.Mem.head restBefore)
          subst headModalityFibrant
          cases subjectDrift with
          | fixed => exact beforeUsable
          | stepsBelow subjectStep _subjectBelow =>
              exact HasTypeUnion.stepPreservesFibrantSubjectUsability beforeTyped subjectStep beforeUsable
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => allFibrant innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => usabilityHolds innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem
  | @consClassifierConv scope context subject classifierBefore _classifierAfter modality restBefore _restAfter
      _classifierConv _classifierFormedAfter _restDrift restIH =>
      intro allFibrant premisesHold usabilityHolds obligation obligationMem
      cases obligationMem with
      | head =>
          -- The subject and context are FIXED; only the classifier drifts, and `isSubjectUsableAtModality` reads
          -- neither classifier, so the before-usability IS the after-usability.
          exact usabilityHolds
            { scope := scope, context := context, subject := subject, classifier := classifierBefore,
              modality := modality }
            (List.Mem.head restBefore)
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => allFibrant innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => usabilityHolds innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem
  | @consContextHeadConv scope context oldBinding newBinding subject classifierBefore _classifierAfter modality
      restBefore _restAfter _bindingConv _oldBindingFormed _classifierConv _classifierFormedAfter _restDrift
      restIH =>
      intro allFibrant premisesHold usabilityHolds obligation obligationMem
      cases obligationMem with
      | head =>
          rw [isSubjectUsableAtModality_consHeadIrrelevant context newBinding oldBinding subject modality]
          exact usabilityHolds
            { scope := scope + 1, context := context.cons oldBinding, subject := subject,
              classifier := classifierBefore, modality := modality }
            (List.Mem.head restBefore)
      | tail _ tailMem =>
          exact restIH
            (fun innerObligation innerMem => allFibrant innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => premisesHold innerObligation (List.Mem.tail _ innerMem))
            (fun innerObligation innerMem => usabilityHolds innerObligation (List.Mem.tail _ innerMem))
            obligation tailMem

end FX1Poly.Typed
