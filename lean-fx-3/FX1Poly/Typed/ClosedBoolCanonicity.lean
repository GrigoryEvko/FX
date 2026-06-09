import FX1Poly.Typed.CombinedBoolCanonicalForms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization

/-! # FX1Poly/Typed/ClosedBoolCanonicity
    — closed bool canonicity for an ARBITRARY (not-necessarily-normal) subject, via the SYNTACTIC route

`CombinedBoolCanonicalForms.lean` settled the NORMAL case — `closedNormalBoolCanonicalForms` shows a closed
*normal* term typed at `boolTypeCell` by any of the three engines (data-intro values, base-type codes, the grown
`HasTypeDescPi`) is `boolTrueCell`/`boolFalseCell`.  Its docstring named the only residual for FULL canonicity:

> reduce an arbitrary closed `t : boolCode` to its normal form WHILE preserving the `boolTypeCell` classifier —
> i.e. grown SN (SN-043) plus the master subject-reduction dispatcher (SN-055 / GrownCtxConv-5).

Both ingredients now ship: grown SN is `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, and the master
subject-reduction-along-`↝*` dispatcher is the unconditional `HasTypeDescPi.subjectReductionStar` (SR-U4).  So
this file assembles full closed bool canonicity by the SAME template that closed grown consistency
(`consistencyOfSubjectReductionStarToEmptyType`, now unconditional via SR-U4):

  1. the subject strongly normalizes (grown SN, under the benign empty-context wf presupposition);
  2. it reaches a normal form by `↝*` (`exists_normalForm_of_isStronglyNormalizing`);
  3. the normal form is STILL typed at `boolTypeCell` (SR-U4 `subjectReductionStar`);
  4. a closed normal term at `boolTypeCell` is `boolTrue`/`boolFalse` (`closedNormalBoolCanonicalForms`).

This is the **syntactic route to canonicity** — it BYPASSES the §5 reducibility-candidate bridge
(`candidateBridge` / sconing leg) entirely, exactly as consistency did.  The candidate bridge is now confined to
the sconing cross-check (the "three ways"), off the canonicity critical path.

## What this is and is NOT

`HasTypeDescPi.noClosedGrownTermAtBoolType` is the bool twin of consistency's
`noClosedTermAtEmptyType` half: the GROWN engine alone has NO closed inhabitant of `boolTypeCell` (it types only
λ / Π / Σ / formation, never data VALUES — `boolTrue`/`boolFalse` live in the standalone `HasTypeDescDataIntro`
engine).  `closedBoolCanonicalForms` is the 3-engine combined canonicity for arbitrary subjects.

NON-VACUITY is via the data-intro VALUE disjunct (`standaloneBoolCanonicalForms` supplies `boolTrue`/`boolFalse`
without a `normal` hypothesis).  This canonicity does NOT yet cover ELIMINATOR computations (`boolElim …`): those
are typed by the FOURTH engine `HasTypeDescDataElim`, which is NOT in this disjunction.  Fully-non-vacuous
eliminator-computing canonicity is the follow-on — it needs `HasTypeDescDataElim` folded into the grown table
(GTL-18) so the combined SN/SR cover eliminator redexes.

## Zero-axiom verification

Direct assembly: grown SN + `exists_normalForm_of_isStronglyNormalizing` + SR-U4 `subjectReductionStar` +
`noClosedNormalTermAtBoolType` + `standaloneBoolCanonicalForms`; the empty-context wf presuppositions are the
already-shipped `WfContextDesc.emptyIsWellFormed` / `WfContextDescPi.emptyIsWellFormed`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The grown engine has no closed inhabitant of `boolTypeCell`** — the bool twin of consistency's
`noClosedTermAtEmptyType`.  An arbitrary (not-necessarily-normal) closed term typed at `boolTypeCell` by the grown
`HasTypeDescPi` engine is impossible: it strongly normalizes (grown SN), reaches a normal form by `↝*`, that
normal form is still typed at `boolTypeCell` (SR-U4 `subjectReductionStar`), and the grown engine has no closed
NORMAL inhabitant of `boolTypeCell` (`noClosedNormalTermAtBoolType`).  Unconditional modulo the benign empty-context
well-formedness presupposition. -/
theorem HasTypeDescPi.noClosedGrownTermAtBoolType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (boolTypeCell : RawTerm 0)) :
    False := by
  have terminates :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨normalForm, reachesNormalForm, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing terminates
  exact HasTypeDescPi.noClosedNormalTermAtBoolType
    (HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typed reachesNormalForm)
    normalFormIsNormal

/-- **★ Closed bool canonicity for an ARBITRARY subject (the syntactic route).**  A closed term typed at
`boolTypeCell` by ANY of the three engines (data-intro values, base-type codes, the grown `HasTypeDescPi`)
reduces by `↝*` to `boolTrueCell` or `boolFalseCell`.  The two standalone engines settle to a VALUE directly
(`standaloneBoolCanonicalForms`, no reduction, no `normal` hypothesis); the grown disjunct is vacuous
(`noClosedGrownTermAtBoolType`).  This upgrades `closedNormalBoolCanonicalForms` off the `normal` hypothesis using
grown SN + SR-U4, with NO candidate bridge — the bool analogue of unconditional grown consistency. -/
theorem closedBoolCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · rcases standaloneBoolCanonicalForms (Or.inl dataIntroTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · rcases standaloneBoolCanonicalForms (Or.inr baseTypeTyped) with valueEq | valueEq
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inl rfl⟩
    · subst valueEq; exact ⟨_, StepStar.refl _, Or.inr rfl⟩
  · exact (HasTypeDescPi.noClosedGrownTermAtBoolType grownTyped).elim

end FX1Poly.Typed
