import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.StepPreservesSubjectUsability

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/UsabilityHoldsUnderObligationsDrift
    — the A1-CONJUNCT-WIRE usability companion of `premisesHoldUnderObligationsDrift`

`premisesHoldUnderObligationsDrift` (ElimObligationsDrift.lean) folds typing forward across the obligation drift a
single child step induces.  This file ships its USABILITY twin: the before-step obligation subjects are fibrantly
usable (the `usabilityHolds` field the native `HasTypeUnion.elim` / `.intro` arms carry), and so are the drifted
after-step subjects — each FIBRANT obligation transported by the SHIPPED, unconditional
`HasTypeUnion.stepPreservesFibrantSubjectUsability` lifted to the obligation's `StepStar` subject drift.

The drift's `cons` arm changes the subject by a `StepStar`, so the single-step preservation is first lifted to a
`StepStar` chain (`stepStarPreservesFibrantSubjectUsability`, threading typing across each step through the
`UnionChildSubjectReduction` self-reference).  The `consContextHeadConv` arm leaves the subject FIXED and only drifts
the head BINDING type — to which `isSubjectUsableAtModality` is INVARIANT (it inspects only the cons/lockCons
SKELETON of the context, never a binding's type), so usability transports definitionally.

This companion handles only FIBRANT obligations (`allFibrant`); the single `.dimensional` obligation in the whole
generator table — `pathApp`'s interval argument — is NOT preserved as step-preservation (it is type-derived, and the
unconditional analogue is false; see `StepPreservesDimensionalSubjectUsability`), so the `pathApp` row discharges its
dimensional residual separately via `stepPreservesDimensionalSubjectUsability_ofWfContext`.  Every other eliminator /
introducer obligation is fibrant, so this one companion closes all of their `usabilityAfter` obligations.

## Zero-axiom verification

`HasTypeUnion.stepPreservesFibrantSubjectUsability` (shipped) + a `StepStar` induction threading
`UnionChildSubjectReduction` + an `ObligationsDrift` induction mirroring `premisesHoldUnderObligationsDrift`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Fibrant usability is preserved across a `StepStar` chain.**  The `StepStar` lift of the single-step
`HasTypeUnion.stepPreservesFibrantSubjectUsability`: a union-typed, fibrantly-usable subject stays fibrantly usable
after any finite reduction chain.  Each head step preserves usability directly (the single-step theorem) and the
intermediate is re-typed by the `UnionChildSubjectReduction` self-reference so the tail can recurse; the typing
classifier is existentially carried because every step changes it (only up to `Conv`). -/
theorem HasTypeUnion.stepStarPreservesFibrantSubjectUsability {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct : RawTerm scope}
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (chain : StepStar subject reduct) :
    (∃ subjectType : RawTerm scope, HasTypeUnion profile context subject subjectType) →
    context.isSubjectUsableAtModality subject ObligationModality.fibrant = true →
    context.isSubjectUsableAtModality reduct ObligationModality.fibrant = true := by
  induction chain with
  | refl _ => intro _typedExists usable; exact usable
  | trans headStep _restChain restIH =>
      intro typedExists usable
      obtain ⟨subjectType, typed⟩ := typedExists
      obtain ⟨reductType, reductTyped, _conv⟩ := childSubjectReduction typed headStep
      exact restIH ⟨reductType, reductTyped⟩
        (HasTypeUnion.stepPreservesFibrantSubjectUsability typed headStep usable)

/-- Accessibility at any modality is invariant under the TYPE of the newest `cons` binding: the
`isFibrantlyAccessibleAt` / `isDimensionallyAccessibleAt` recursions read only the cons/lockCons SKELETON of the
telescope, never a binding's term, so swapping the head binding's type leaves every variable's accessibility fixed.
Structural on the index: the newest binder closes by `rfl`, deeper binders recurse into the (shared) prefix. -/
theorem isAccessibleAtModality_consHeadIrrelevant {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (oldBinding newBinding : RawTerm scope)
    (index : Fin (scope + 1)) (modality : ObligationModality) :
    (context.cons oldBinding).isAccessibleAtModality index modality
      = (context.cons newBinding).isAccessibleAtModality index modality := by
  cases modality with
  | fibrant =>
      rw [isAccessibleAtModality_fibrant, isAccessibleAtModality_fibrant]
      obtain ⟨val, isLt⟩ := index
      cases val with
      | zero => rfl
      | succ position => rfl
  | dimensional =>
      rw [isAccessibleAtModality_dimensional, isAccessibleAtModality_dimensional]
      obtain ⟨val, isLt⟩ := index
      cases val with
      | zero => rfl
      | succ position => rfl

/-- Subject usability at any modality is invariant under the TYPE of the newest `cons` binding — the subject-level
lift of `isAccessibleAtModality_consHeadIrrelevant`.  A non-variable subject is usable regardless of context; a bare
variable defers to `isAccessibleAtModality` at its own index, which is binding-type-blind.  The transport the
`consContextHeadConv` drift arm needs: when the head binding drifts but the (fixed) subject does not, usability is
preserved. -/
theorem isSubjectUsableAtModality_consHeadIrrelevant {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (oldBinding newBinding : RawTerm scope)
    (subject : RawTerm (scope + 1)) (modality : ObligationModality) :
    (context.cons oldBinding).isSubjectUsableAtModality subject modality
      = (context.cons newBinding).isSubjectUsableAtModality subject modality := by
  cases subject with
  | mkGen generator payload children =>
      dsimp only [TypingContext.isSubjectUsableAtModality]
      by_cases generatorIsVar : generator = Generator.gen_var
      · rw [dif_pos generatorIsVar, dif_pos generatorIsVar]
        exact isAccessibleAtModality_consHeadIrrelevant context oldBinding newBinding _ modality
      · rw [dif_neg generatorIsVar, dif_neg generatorIsVar]

/-- **★ The A1-CONJUNCT-WIRE usability driver — the obligation subjects stay usable after the drift.**  The usability
twin of `premisesHoldUnderObligationsDrift`: given the before-step obligation subjects fibrantly usable (the native
arm's `usabilityHolds`) and typed (`premisesHold`), every drifted obligation subject is usable at its modality.
Induct on the drift: the `cons` head transports through `stepStarPreservesFibrantSubjectUsability` (the obligation is
fibrant by `allFibrant`, its subject drifts by `StepStar`); the `consContextHeadConv` head keeps the subject and
drifts only the head binding, to which `isSubjectUsableAtModality` is definitionally invariant; tails recurse. -/
theorem usabilityHoldsUnderObligationsDrift {profile : PolyProfile}
    {obligationsBefore obligationsAfter : List (ElimObligation profile)}
    (drift : ObligationsDrift profile obligationsBefore obligationsAfter)
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    (∀ obligation ∈ obligationsBefore, obligation.modality = ObligationModality.fibrant) →
    (∀ obligation ∈ obligationsBefore,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ obligationsBefore,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    ∀ obligation ∈ obligationsAfter,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  induction drift with
  | nil => intro _allFibrant _premisesHold _usabilityHolds obligation obligationMem; cases obligationMem
  | @cons scope context subjectBefore subjectAfter classifierBefore _classifierAfter modality restBefore
      _restAfter subjectDrift _classifierDrift _classifierFormedBefore _restDrift restIH =>
      intro allFibrant premisesHold usabilityHolds obligation obligationMem
      cases obligationMem with
      | head =>
          have headModalityFibrant : modality = ObligationModality.fibrant :=
            allFibrant _ (List.Mem.head restBefore)
          subst headModalityFibrant
          exact HasTypeUnion.stepStarPreservesFibrantSubjectUsability childSubjectReduction subjectDrift
            ⟨classifierBefore, premisesHold _ (List.Mem.head restBefore)⟩
            (usabilityHolds _ (List.Mem.head restBefore))
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
          -- The subject is FIXED; only the head binding drifts `oldBinding ⟶ newBinding`, and
          -- `isSubjectUsableAtModality` reads only the cons-skeleton (never the binding type), so the before-usability
          -- over `cons oldBinding` IS the after-usability over `cons newBinding`.
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
