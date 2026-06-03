import FX1Poly.Typed.HasTypeDescPiConditionalConfluence

/-! # FX1Poly/Typed/HasTypeDescPiUniqueNormalForm
    — the typed fragment has a UNIQUE normal form per well-typed subject, conditional on typed-SN

`HasTypeDescPiConditionalConfluence.lean` ships, on the single typed-SN hypothesis
`HasTypeDescPiStronglyNormalizes`, the four building blocks: weak normalization (a subject reaches a normal
form), per-term confluence (any two reducts join), decidable conversion, and Conv ↔ normal-form equality.
This file combines the first two into the canonical-forms headline for the typed fragment:

* `HasTypeDescPi.uniqueNormalFormOfStronglyNormalizes` — **every well-typed subject has a UNIQUE normal
  form.**  Existence is weak normalization; uniqueness is confluence plus normal-form rigidity (two normal
  forms reached from the same subject join, and a normal form reached by a reduction chain IS the chain's
  start, so the join apex collapses both onto one term).

This is the milestone statement that the typed fragment is a normalizing rewriting system with canonical
representatives — the foundation under "Conv is decided by normal-form equality" (the Path-A NbE headline).
It is conditional on the one typed-SN hypothesis (= SN-043, gate #672); once #672 lands it becomes
unconditional in a single step, like the rest of the conditional package.

## Zero-axiom verification

`HasTypeDescPi.subjectWeaklyNormalizesOfStronglyNormalizes` (existence) + `HasTypeDescPi.subject-
ConfluenceOfStronglyNormalizes` (the join) + `StepStar.eq_of_noStep` driven by
`RawTerm.isStepNormalForm_blocks_step` (the rigidity).  All shipped zero-axiom.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Every well-typed subject has a unique normal form, conditional on typed-SN.**  Existence is the weak
normalization leg (`subjectWeaklyNormalizesOfStronglyNormalizes`); uniqueness is confluence
(`subjectConfluenceOfStronglyNormalizes`) plus normal-form rigidity: two normal forms reached from the same
subject join (per-term confluence), and a normal form reached by a `StepStar` chain equals the chain's start
(`StepStar.eq_of_noStep` via `RawTerm.isStepNormalForm_blocks_step`), so the join apex collapses both candidate
normal forms onto a single term.  The canonical-forms headline for the typed fragment — it is a normalizing
rewriting system with a unique canonical representative per well-typed subject. -/
theorem HasTypeDescPi.uniqueNormalFormOfStronglyNormalizes {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typedStronglyNormalizes : HasTypeDescPiStronglyNormalizes profile)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
        ∀ otherForm : RawTerm scope,
          (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
            otherForm = normalForm := by
  obtain ⟨canonicalForm, subjectToCanonical, canonicalIsNormal⟩ :=
    HasTypeDescPi.subjectWeaklyNormalizesOfStronglyNormalizes typedStronglyNormalizes typed
  refine ⟨canonicalForm, ⟨subjectToCanonical, canonicalIsNormal⟩, ?_⟩
  rintro otherForm ⟨subjectToOther, otherIsNormal⟩
  obtain ⟨apex, otherToApex, canonicalToApex⟩ :=
    HasTypeDescPi.subjectConfluenceOfStronglyNormalizes typedStronglyNormalizes typed
      subjectToOther subjectToCanonical
  have apexEqualsOther : apex = otherForm :=
    StepStar.eq_of_noStep
      (fun stepReduct stepFromOther =>
        RawTerm.isStepNormalForm_blocks_step otherIsNormal stepReduct stepFromOther)
      otherToApex
  have apexEqualsCanonical : apex = canonicalForm :=
    StepStar.eq_of_noStep
      (fun stepReduct stepFromCanonical =>
        RawTerm.isStepNormalForm_blocks_step canonicalIsNormal stepReduct stepFromCanonical)
      canonicalToApex
  exact apexEqualsOther.symm.trans apexEqualsCanonical

/-- **The typed fragment is a convergent rewriting system with unique normal forms, modulo the single typed-SN
hypothesis.**  This is the release-readiness consolidation (Thrust-C de-risking): it bundles the three
propositional normalization consequences of `HasTypeDescPiStronglyNormalizes` into ONE auditable statement, so a
reviewer can check at a single point what the typed fragment delivers the moment #672 discharges the hypothesis.

Conjunct 1 — **weak normalization** (`subjectWeaklyNormalizesOfStronglyNormalizes`): every well-typed subject
reduces to a normal form.  Conjunct 2 — **per-subject confluence** (`subjectConfluenceOfStronglyNormalizes`, the
typed Newman bridge SN-046): any two reducts of a well-typed subject join.  Conjunct 3 — **unique normal form**
(`uniqueNormalFormOfStronglyNormalizes`): the normal form is unique.  Termination (the hypothesis) + weak
normalization + confluence IS convergence; conjunct 3 is their headline consequence, stated explicitly.

This is consolidation, NOT new metatheory — each conjunct is the corresponding shipped conditional theorem
applied to the one hypothesis.  The two companion results — **decidable typed Conv**
(`Conv.decidableOfHasTypeDescPiStronglyNormalizes`) and **Conv = normal-form equality**
(`Conv.iff_normalize_eq_of_hasTypeDescPiStronglyNormalizes`) — are NOT re-bundled here: their conclusions thread
the SN witness into `RawTerm.normalize`, so they live as standalone gated results in
`HasTypeDescPiConditionalConfluence.lean` rather than as clean `∀`-closed conjuncts.  Together with this bundle
they are the full conditional Milestone-A normalization package. -/
theorem HasTypeDescPi.convergencePackageModuloStronglyNormalizes {profile : PolyProfile}
    (typedStronglyNormalizes : HasTypeDescPiStronglyNormalizes profile) :
    (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
        HasTypeDescPi profile context subject classifier →
          ∃ normalForm : RawTerm scope, StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          HasTypeDescPi profile context subject classifier →
            ∀ {leftReduct rightReduct : RawTerm scope},
              StepStar subject leftReduct → StepStar subject rightReduct →
                StepStar.Join leftReduct rightReduct)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          HasTypeDescPi profile context subject classifier →
            ∃ normalForm : RawTerm scope,
              (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
                ∀ otherForm : RawTerm scope,
                  (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
                    otherForm = normalForm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _scope _context _subject _classifier typed
    exact HasTypeDescPi.subjectWeaklyNormalizesOfStronglyNormalizes typedStronglyNormalizes typed
  · intro _scope _context _subject _classifier typed _leftReduct _rightReduct subjectToLeft subjectToRight
    exact HasTypeDescPi.subjectConfluenceOfStronglyNormalizes typedStronglyNormalizes typed
      subjectToLeft subjectToRight
  · intro _scope _context _subject _classifier typed
    exact HasTypeDescPi.uniqueNormalFormOfStronglyNormalizes typedStronglyNormalizes typed

end FX1Poly.Typed
