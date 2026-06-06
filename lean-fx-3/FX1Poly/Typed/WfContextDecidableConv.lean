import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescPiConditionalConfluence

/-! # FX1Poly/Typed/WfContextDecidableConv
    — UNCONDITIONAL decidable typed Conv + global confluence on the WfContextDesc fragment

The conditional package (`HasTypeDescPiConditionalConfluence.lean`) keys its results — decidable typed Conv,
global confluence — on the UNQUALIFIED typed-SN interface `HasTypeDescPiStronglyNormalizes` (SN for well-typed
terms in EVERY context).  Open strong normalization (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) supplies
SN directly for terms in a WELL-FORMED context — so these results are UNCONDITIONAL with the qualifier
"assume the context is well-formed" (a decidable presupposition, and the honest precondition: the unqualified
interface is unprovable because the var rule types in any context, well-formed or not).  Everything runs through
the `HasTypeDesc`-defined `WfContextDesc`.

  * `Conv.decidableOfWellTypedInWfContextDesc` — two well-typed subjects in a well-formed context have
    DECIDABLE convertibility, with NO typed-SN hypothesis: feed each subject's open-SN witness to the parameter-
    free SN-fragment decider `Conv.decidableOfStronglyNormalizing` (normalize both, compare propext-free).
  * `HasTypeDescPi.subjectConfluenceOfWfContextDesc` (unconditional) — any two reducts of a well-typed
    subject in a well-formed context join, via per-term Newman (`confluence_of_localJoin_and_accessible`) on the
    open-SN witness.  Raw global confluence (false by Ω) is never used.

## Zero-axiom verification

Each is a one-line composition of open SN (`stronglyNormalizingOfWfContextDesc`) with a shipped SN-fragment
result.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Decidable typed Conv on the `WfContextDesc` fragment, UNCONDITIONALLY.**  Two well-typed subjects in
a well-formed context have decidable convertibility — the SN-fragment qualifier is discharged by open strong
normalization: each subject is strongly normalizing (`stronglyNormalizingOfWfContextDesc`), so the parameter-free
decider `Conv.decidableOfStronglyNormalizing` (normalize both, compare normal forms) applies. -/
def Conv.decidableOfWellTypedInWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftSubject leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightSubject rightClassifier) :
    Decidable (Conv leftSubject rightSubject) :=
  Conv.decidableOfStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed leftTyped)
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed rightTyped)

/-- **Global confluence on the `WfContextDesc` fragment (unconditional).**  Any two reducts of a
well-typed subject in a well-formed context join — per-term Newman
(`StepStar.confluence_of_localJoin_and_accessible`, raw local confluence baked in) fed the subject's open-SN
witness (`stronglyNormalizingOfWfContextDesc`); raw global confluence (false by Ω) is never used. -/
theorem HasTypeDescPi.subjectConfluenceOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : StepStar subject leftReduct)
    (subjectToRight : StepStar subject rightReduct) :
    StepStar.Join leftReduct rightReduct :=
  StepStar.confluence_of_localJoin_and_accessible
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)
    subjectToLeft subjectToRight

/-- **Weak normalization on the `WfContextDesc` fragment, UNCONDITIONALLY.**  Every well-typed subject in a
well-formed context reaches a structural normal form — `RawTerm.normalize` driven by the open-SN witness
(`stronglyNormalizingOfWfContextDesc`). -/
theorem HasTypeDescPi.subjectWeaklyNormalizesOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  ⟨RawTerm.normalize subject (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed),
    RawTerm.normalize_reducesTo subject
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed),
    RawTerm.normalize_isStepNormalForm subject
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)⟩

/-- **Unique normal form on the `WfContextDesc` fragment, UNCONDITIONALLY.**  Every well-typed subject in a
well-formed context has a UNIQUE normal form: existence is weak normalization (above), uniqueness is global
confluence (`subjectConfluenceOfWfContextDesc`) plus normal-form rigidity (`StepStar.eq_of_noStep` via
`isStepNormalForm_blocks_step` collapses the join apex onto each candidate).  The typed fragment is a normalizing
rewriting system with a canonical representative per well-typed subject, no SN hypothesis. -/
theorem HasTypeDescPi.uniqueNormalFormOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
        ∀ otherForm : RawTerm scope,
          (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
            otherForm = normalForm := by
  obtain ⟨canonicalForm, subjectToCanonical, canonicalIsNormal⟩ :=
    HasTypeDescPi.subjectWeaklyNormalizesOfWfContextDesc contextWellFormed typed
  refine ⟨canonicalForm, ⟨subjectToCanonical, canonicalIsNormal⟩, ?_⟩
  rintro otherForm ⟨subjectToOther, otherIsNormal⟩
  obtain ⟨apex, otherToApex, canonicalToApex⟩ :=
    HasTypeDescPi.subjectConfluenceOfWfContextDesc contextWellFormed typed subjectToOther subjectToCanonical
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

/-- **The typed fragment is a convergent rewriting system with unique normal forms, UNCONDITIONALLY on the
`WfContextDesc` fragment.**  Bundles weak normalization, per-subject confluence, and unique normal forms
into ONE auditable statement, each conjunct WfContextDesc-hypothesized (the honest precondition), with the typed-SN
hypothesis fully discharged by open strong normalization.  Together with
`Conv.decidableOfWellTypedInWfContextDesc`, this is the normalization package for the typed fragment, no SN
hypothesis, routed entirely through `WfContextDesc`. -/
theorem HasTypeDescPi.convergencePackageOfWfContextDesc {profile : PolyProfile} :
    (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
        WfContextDesc context → HasTypeDescPi profile context subject classifier →
          ∃ normalForm : RawTerm scope, StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContextDesc context → HasTypeDescPi profile context subject classifier →
            ∀ {leftReduct rightReduct : RawTerm scope},
              StepStar subject leftReduct → StepStar subject rightReduct →
                StepStar.Join leftReduct rightReduct)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContextDesc context → HasTypeDescPi profile context subject classifier →
            ∃ normalForm : RawTerm scope,
              (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
                ∀ otherForm : RawTerm scope,
                  (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
                    otherForm = normalForm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _scope _context _subject _classifier contextWellFormed typed
    exact HasTypeDescPi.subjectWeaklyNormalizesOfWfContextDesc contextWellFormed typed
  · intro _scope _context _subject _classifier contextWellFormed typed
      _leftReduct _rightReduct subjectToLeft subjectToRight
    exact HasTypeDescPi.subjectConfluenceOfWfContextDesc contextWellFormed typed subjectToLeft subjectToRight
  · intro _scope _context _subject _classifier contextWellFormed typed
    exact HasTypeDescPi.uniqueNormalFormOfWfContextDesc contextWellFormed typed

end FX1Poly.Typed
