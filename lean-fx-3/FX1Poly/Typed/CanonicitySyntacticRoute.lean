import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ConvBoolCodeRigidity
import FX1Poly.Typed.ClosedBoolCanonicity

/-! # FX1Poly/Typed/CanonicitySyntacticRoute
    — SN-047/048/049 target signature via the SYNTACTIC route (the candidate-bridge-free twin)

`CanonicityTargetSignature.dataCanonicityFromCandidateBridge` reduces engine canonicity to the §5
data-candidate bridge (the sconing leg: closed engine-typing at a data code ⟹ reducibility-candidate
membership).  That bridge is HIGH-RISK (a §5 `ReducibleTypeStepBounded` edit, #1049) and is now confined to the
sconing cross-check of the "three ways".

This file ships the PARALLEL **syntactic-route** target signature, which BYPASSES the candidate bridge entirely
— exactly as grown consistency (`consistencyOfSubjectReductionStarToEmptyType`) bypassed it.  Its two
ingredients are both already-shipped, unconditional metatheory:

  * **standalone-layer canonicity** — a closed cell typed at the data code by one of the VALUE rows (the union
    `dataIntroNullary` / `baseTypeFormation` arms) already reduces to a canonical value (it IS one);
  * **grown vacuity** — the grown engine `HasTypeDescPi` has NO closed inhabitant of the data code (it types
    only λ / Π / Σ / formation, never data values), proved by grown SN + SR-U4 `subjectReductionStar` +
    closed-normal canonical forms — NO candidate bridge.

`closedBoolCanonicalForms` (this directory) is the first concrete instance; `boolCanonicityViaSyntacticRoute`
below re-derives it THROUGH the generic signature, witnessing the signature's non-vacuity and serving as the
template Nat (SN-048) and the remaining data types (SN-049) instantiate — each a one-liner once its
standalone-engine canonicity + grown vacuity land (the same per-data-type work the candidate route needs, minus
the §5 risk).

## What the signature does NOT yet cover

The disjunction is over the layers whose canonical-forms/vacuity facts are shipped: the nullary-formation
VALUE rows (`dataIntroNullary` data values + `baseTypeFormation` base codes) and the grown engine.  ELIMINATOR
computations (`boolElim …`) are typed by the union's data-eliminator arms, which are NOT in the disjunction —
fully-non-vacuous eliminator-computing canonicity is the follow-on (needs combined SN/SR over eliminator
redexes).  This file is honest about that boundary; it closes the VALUE-layer canonicity, not the eliminator
layer.

## Zero-axiom verification

The generic signature is a two-way `rcases` dispatch (the standalone arm via the standalone-canonicity premise,
the grown arm via the vacuity premise's `False.elim`); the bool instance composes it with the shipped
`standaloneBoolCanonicalForms` (over the union rows) + the generic
`HasTypeDescPi.noClosedGrownTermAtDataClassifier` at the bool rigidities.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **SN-047/048/049 target signature: engine canonicity via the SYNTACTIC route (candidate-bridge-free).**  For
any value predicate `isValue`, any standalone-value predicate `StandaloneTyped`, and any closed data type code
`dataTypeCode`, given (1) the standalone-layer canonicity — every closed term satisfying `StandaloneTyped` reduces
to an `isValue` — and (2) the grown vacuity — nothing closed is grown-typed at `dataTypeCode` — every closed term
typed at `dataTypeCode` by the standalone layer OR the grown engine reduces to a canonical value.  The syntactic
twin of `dataCanonicityFromCandidateBridge`: where that route discharges the data-candidate bridge (§5 sconing
leg), this route discharges only grown SN + SR + closed-normal canonical forms (all shipped, unconditional).  The
standalone layer is now the abstract `StandaloneTyped` — instantiated at the union `dataIntroNullary` /
`baseTypeFormation` rows by the bool witness below. -/
theorem dataCanonicityFromSyntacticRoute {profile : PolyProfile}
    {isValue : RawTerm 0 → Prop} {dataTypeCode : RawTerm 0} {StandaloneTyped : RawTerm 0 → Prop}
    (standaloneCanonicity : ∀ subject : RawTerm 0, StandaloneTyped subject →
        ∃ value : RawTerm 0, StepStar subject value ∧ isValue value)
    (noClosedGrownTermAtDataCode : ∀ subject : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode → False)
    (subject : RawTerm 0)
    (typed : StandaloneTyped subject ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode) :
    ∃ value : RawTerm 0, StepStar subject value ∧ isValue value := by
  rcases typed with standaloneTyped | grownTyped
  · exact standaloneCanonicity subject standaloneTyped
  · exact (noClosedGrownTermAtDataCode subject grownTyped).elim

/-- **Bool canonicity re-derived through the generic syntactic-route signature** — witnesses
`dataCanonicityFromSyntacticRoute` is non-vacuous and shows the instantiation pattern Nat (SN-048) / data
(SN-049) follow.  The two premises are the shipped `standaloneBoolCanonicalForms` (recast into the
`∃ value, StepStar ∧ isValue` shape — the standalone subject already IS its value) and the generic grown vacuity
`HasTypeDescPi.noClosedGrownTermAtDataClassifier` at the bool rigidities.  Same statement as the direct
`closedBoolCanonicalForms`, with the standalone disjuncts taken over the union `dataIntroNullary` /
`baseTypeFormation` rows. -/
theorem boolCanonicityViaSyntacticRoute {profile : PolyProfile} {subject : RawTerm 0}
    (typed : boolStandaloneRowTyped subject ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) :=
  dataCanonicityFromSyntacticRoute
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    (StandaloneTyped := boolStandaloneRowTyped)
    (fun _standaloneSubject standaloneTyped => by
      rcases standaloneTyped with
          ⟨generator, payload, children, rule, subjectEq, isDataIntro, classifierEq⟩
        | ⟨generator, payload, children, rule, subjectEq, isBaseType, classifierEq⟩
      · subst subjectEq
        rcases standaloneBoolCanonicalForms (generator := generator) (payload := payload)
            (children := children) (Or.inl ⟨rule, isDataIntro, classifierEq⟩) with valueEq | valueEq
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
      · subst subjectEq
        rcases standaloneBoolCanonicalForms (generator := generator) (payload := payload)
            (children := children) (Or.inr ⟨rule, isBaseType, classifierEq⟩) with valueEq | valueEq
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
        · rw [valueEq]; exact ⟨_, StepStar.refl _, Or.inr rfl⟩)
    (fun _subject grownTyped =>
      HasTypeDescPi.noClosedGrownTermAtDataClassifier grownTyped
        (fun _domainCode _codomainCode convToPiCode => Conv.boolTypeCell_not_piTyCode convToPiCode)
        (fun _levelExpr _flag convToUniverseCode => Conv.boolTypeCell_not_universeCode convToUniverseCode))
    subject typed

end FX1Poly.Typed
