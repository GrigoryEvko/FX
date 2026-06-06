import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescPiConditionalConfluence

/-! # FX1Poly/Typed/WfContextDecidableConv
    — harvesting open SN-043: UNCONDITIONAL decidable typed Conv + global confluence on the WfContext fragment
      (SN-051 / SN-046-unconditional)

The conditional package (`HasTypeDescPiConditionalConfluence.lean`) keyed its results — decidable typed Conv,
global confluence — on the UNQUALIFIED typed-SN interface `HasTypeDescPiStronglyNormalizes` (SN for well-typed
terms in EVERY context).  Open SN-043 (`HasTypeDescPi.stronglyNormalizingOfWfContext`, OB-5) supplies SN directly
for terms in a WELL-FORMED context — so these results become UNCONDITIONAL once the qualifier moves from "assume
typed-SN" to "assume the context is well-formed" (a decidable presupposition, and the honest precondition: the
unqualified interface is unprovable because the var rule types in any context, well-formed or not).

  * `Conv.decidableOfWellTypedInWfContext` (SN-051) — two well-typed subjects in a well-formed context have
    DECIDABLE convertibility, with NO typed-SN hypothesis: feed each subject's OB-5 SN witness to the parameter-
    free SN-fragment decider `Conv.decidableOfStronglyNormalizing` (normalize both, compare propext-free).
  * `HasTypeDescPi.subjectConfluenceOfWfContext` (SN-046, unconditional) — any two reducts of a well-typed
    subject in a well-formed context join, via per-term Newman (`confluence_of_localJoin_and_accessible`) on the
    OB-5 SN witness.  Raw global confluence (false by Ω) is never used.

## Zero-axiom verification

Each is a one-line composition of OB-5 (`stronglyNormalizingOfWfContext`) with a shipped SN-fragment result.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **SN-051: decidable typed Conv on the WfContext fragment, UNCONDITIONALLY.**  Two well-typed subjects in a
well-formed context have decidable convertibility — the SN-fragment qualifier is discharged by open SN-043
(OB-5): each subject is strongly normalizing (`stronglyNormalizingOfWfContext`), so the parameter-free decider
`Conv.decidableOfStronglyNormalizing` (normalize both, compare normal forms) applies.  The unconditional form of
`Conv.decidableOfHasTypeDescPiStronglyNormalizes`. -/
def Conv.decidableOfWellTypedInWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (leftTyped : HasTypeDescPi profile context leftSubject leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightSubject rightClassifier) :
    Decidable (Conv leftSubject rightSubject) :=
  Conv.decidableOfStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed leftTyped)
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed rightTyped)

/-- **SN-046 (unconditional): global confluence on the WfContext fragment.**  Any two reducts of a well-typed
subject in a well-formed context join — per-term Newman (`StepStar.confluence_of_localJoin_and_accessible`, raw
local confluence baked in) fed the subject's OB-5 SN witness.  The unconditional form of
`HasTypeDescPi.subjectConfluenceOfStronglyNormalizes`; raw global confluence (false by Ω) is never used. -/
theorem HasTypeDescPi.subjectConfluenceOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : StepStar subject leftReduct)
    (subjectToRight : StepStar subject rightReduct) :
    StepStar.Join leftReduct rightReduct :=
  StepStar.confluence_of_localJoin_and_accessible
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)
    subjectToLeft subjectToRight

/-- **Weak normalization on the WfContext fragment, UNCONDITIONALLY.**  Every well-typed subject in a well-formed
context reaches a structural normal form — `RawTerm.normalize` driven by the OB-5 SN witness.  The unconditional
form of `HasTypeDescPi.subjectWeaklyNormalizesOfStronglyNormalizes`. -/
theorem HasTypeDescPi.subjectWeaklyNormalizesOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  ⟨RawTerm.normalize subject (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed),
    RawTerm.normalize_reducesTo subject (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed),
    RawTerm.normalize_isStepNormalForm subject
      (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)⟩

/-- **Unique normal form on the WfContext fragment, UNCONDITIONALLY.**  Every well-typed subject in a well-formed
context has a UNIQUE normal form: existence is weak normalization (above), uniqueness is global confluence
(`subjectConfluenceOfWfContext`, SN-046) plus normal-form rigidity (`StepStar.eq_of_noStep` via
`isStepNormalForm_blocks_step` collapses the join apex onto each candidate).  The unconditional form of
`HasTypeDescPi.uniqueNormalFormOfStronglyNormalizes` — the typed fragment is a normalizing rewriting system with
a canonical representative per well-typed subject (the Path-A NbE headline), no SN hypothesis. -/
theorem HasTypeDescPi.uniqueNormalFormOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
        ∀ otherForm : RawTerm scope,
          (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
            otherForm = normalForm := by
  obtain ⟨canonicalForm, subjectToCanonical, canonicalIsNormal⟩ :=
    HasTypeDescPi.subjectWeaklyNormalizesOfWfContext contextWellFormed typed
  refine ⟨canonicalForm, ⟨subjectToCanonical, canonicalIsNormal⟩, ?_⟩
  rintro otherForm ⟨subjectToOther, otherIsNormal⟩
  obtain ⟨apex, otherToApex, canonicalToApex⟩ :=
    HasTypeDescPi.subjectConfluenceOfWfContext contextWellFormed typed subjectToOther subjectToCanonical
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
WfContext fragment.**  The unconditional twin of `convergencePackageModuloStronglyNormalizes`: bundles weak
normalization, per-subject confluence (SN-046), and unique normal forms into ONE auditable statement, each
conjunct WfContext-hypothesized (the honest precondition), with the typed-SN hypothesis fully discharged by open
SN-043 (OB-5).  Together with the standalone `Conv.decidableOfWellTypedInWfContext` (SN-051), this is the
Milestone-A normalization package for the typed fragment, no SN hypothesis. -/
theorem HasTypeDescPi.convergencePackageOfWfContext {profile : PolyProfile} :
    (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
        WfContext context → HasTypeDescPi profile context subject classifier →
          ∃ normalForm : RawTerm scope, StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContext context → HasTypeDescPi profile context subject classifier →
            ∀ {leftReduct rightReduct : RawTerm scope},
              StepStar subject leftReduct → StepStar subject rightReduct →
                StepStar.Join leftReduct rightReduct)
      ∧ (∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContext context → HasTypeDescPi profile context subject classifier →
            ∃ normalForm : RawTerm scope,
              (StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) ∧
                ∀ otherForm : RawTerm scope,
                  (StepStar subject otherForm ∧ RawTerm.isStepNormalForm otherForm) →
                    otherForm = normalForm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _scope _context _subject _classifier contextWellFormed typed
    exact HasTypeDescPi.subjectWeaklyNormalizesOfWfContext contextWellFormed typed
  · intro _scope _context _subject _classifier contextWellFormed typed
      _leftReduct _rightReduct subjectToLeft subjectToRight
    exact HasTypeDescPi.subjectConfluenceOfWfContext contextWellFormed typed subjectToLeft subjectToRight
  · intro _scope _context _subject _classifier contextWellFormed typed
    exact HasTypeDescPi.uniqueNormalFormOfWfContext contextWellFormed typed

/-! ## Bridge-free `WfContextDesc` twins (HT-B spine step 3)

The whole decidable-Conv / convergence leg, ported to the `HasTypeDesc`-defined `WfContextDesc` context
predicate by composing the bridge-free open-SN twin `stronglyNormalizingOfWfContextDesc` (spine step 2) — no
`HasType` dependency anywhere on the path.  Each twin is the verbatim original with `WfContext`→`WfContextDesc`
and the SN witness routed through the `…OfWfContextDesc` form; the rest (the parameter-free SN-fragment decider,
per-term Newman, `RawTerm.normalize`, normal-form rigidity) is context-predicate-agnostic.  These are the
targets the SN-051/052 qualifier-drops migrate onto before HT-C deletes the `HasType` engine. -/

/-- **SN-051 (bridge-free): decidable typed Conv on the `WfContextDesc` fragment.**  The `WfContextDesc` twin of
`Conv.decidableOfWellTypedInWfContext`, off the `HasType` engine via `stronglyNormalizingOfWfContextDesc`. -/
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

/-- **SN-046 (bridge-free): global confluence on the `WfContextDesc` fragment** — the `WfContextDesc` twin of
`subjectConfluenceOfWfContext`, via per-term Newman on the `…OfWfContextDesc` SN witness. -/
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

/-- **Weak normalization on the `WfContextDesc` fragment (bridge-free)** — the `WfContextDesc` twin of
`subjectWeaklyNormalizesOfWfContext`. -/
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

/-- **Unique normal form on the `WfContextDesc` fragment (bridge-free)** — the `WfContextDesc` twin of
`uniqueNormalFormOfWfContext`: existence from the weak-normalization twin, uniqueness from the confluence twin +
normal-form rigidity.  The Path-A NbE headline, off the `HasType` engine. -/
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

/-- **Convergent rewriting package on the `WfContextDesc` fragment (bridge-free)** — the `WfContextDesc` twin of
`convergencePackageOfWfContext`: weak normalization + per-subject confluence + unique normal forms in one
auditable statement, off the `HasType` engine.  With `Conv.decidableOfWellTypedInWfContextDesc` this is the
Milestone-A normalization package routed entirely through `WfContextDesc`. -/
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
