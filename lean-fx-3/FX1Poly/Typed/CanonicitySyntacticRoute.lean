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

  * **standalone-engine canonicity** — a closed term typed at the data code by one of the VALUE engines
    (`HasTypeDescDataIntro` / `HasTypeDescBaseType`) already reduces to a canonical value (it IS one);
  * **grown vacuity** — the grown engine `HasTypeDescPi` has NO closed inhabitant of the data code (it types
    only λ / Π / Σ / formation, never data values), proved by grown SN + SR-U4 `subjectReductionStar` +
    closed-normal canonical forms — NO candidate bridge.

`closedBoolCanonicalForms` (this directory) is the first concrete instance; `boolCanonicityViaSyntacticRoute`
below re-derives it THROUGH the generic signature, witnessing the signature's non-vacuity and serving as the
template Nat (SN-048) and the remaining data types (SN-049) instantiate — each a one-liner once its
standalone-engine canonicity + grown vacuity land (the same per-data-type work the candidate route needs, minus
the §5 risk).

## What the signature does NOT yet cover

The disjunction is over the three engines whose canonical-forms/vacuity facts are shipped: data-intro VALUES,
base-type CODES, and the grown engine.  ELIMINATOR computations (`boolElim …`) are typed by the fourth engine
`HasTypeDescDataElim`, which is NOT in the disjunction — fully-non-vacuous eliminator-computing canonicity is the
follow-on (needs `HasTypeDescDataElim` folded into the grown table, GTL-18, plus combined SN/SR over eliminator
redexes).  This file is honest about that boundary; it closes the VALUE-layer canonicity, not the eliminator
layer.

## Zero-axiom verification

The generic signature is a three-way `rcases` dispatch (two value arms via the standalone-canonicity premise, the
grown arm via the vacuity premise's `False.elim`); the bool instance composes it with the shipped
`standaloneBoolCanonicalForms` + `HasTypeDescPi.noClosedGrownTermAtBoolType`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **SN-047/048/049 target signature: engine canonicity via the SYNTACTIC route (candidate-bridge-free).**  For
any value predicate `isValue` and any closed data type code `dataTypeCode`, given (1) the standalone-engine
canonicity — every closed term typed at `dataTypeCode` by `HasTypeDescDataIntro`/`HasTypeDescBaseType` reduces to
an `isValue` — and (2) the grown vacuity — nothing closed is grown-typed at `dataTypeCode` — every closed term
typed at `dataTypeCode` by ANY of the three engines reduces to a canonical value.  The syntactic twin of
`dataCanonicityFromCandidateBridge`: where that route discharges the data-candidate bridge (§5 sconing leg), this
route discharges only grown SN + SR + closed-normal canonical forms (all shipped, unconditional). -/
theorem dataCanonicityFromSyntacticRoute {profile : PolyProfile}
    {isValue : RawTerm 0 → Prop} {dataTypeCode : RawTerm 0}
    (standaloneCanonicity : ∀ subject : RawTerm 0,
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode →
        ∃ value : RawTerm 0, StepStar subject value ∧ isValue value)
    (noClosedGrownTermAtDataCode : ∀ subject : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode → False)
    (subject : RawTerm 0)
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject dataTypeCode) :
    ∃ value : RawTerm 0, StepStar subject value ∧ isValue value := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · exact standaloneCanonicity subject (Or.inl dataIntroTyped)
  · exact standaloneCanonicity subject (Or.inr baseTypeTyped)
  · exact (noClosedGrownTermAtDataCode subject grownTyped).elim

/-- **Bool canonicity re-derived through the generic syntactic-route signature** — witnesses
`dataCanonicityFromSyntacticRoute` is non-vacuous and shows the instantiation pattern Nat (SN-048) / data
(SN-049) follow.  The two premises are the shipped `standaloneBoolCanonicalForms` (recast into the
`∃ value, StepStar ∧ isValue` shape — the standalone subject already IS its value) and
`HasTypeDescPi.noClosedGrownTermAtBoolType`.  Same statement as the direct `closedBoolCanonicalForms`. -/
theorem boolCanonicityViaSyntacticRoute {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) :=
  dataCanonicityFromSyntacticRoute
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    (fun subject standaloneTyped => by
      rcases standaloneBoolCanonicalForms standaloneTyped with valueEq | valueEq
      · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
      · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩)
    (fun _subject grownTyped => HasTypeDescPi.noClosedGrownTermAtBoolType grownTyped)
    subject typed

end FX1Poly.Typed
