import FX1Poly.Typed.GrownOpenProgress
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.NormalFormUnique

/-! # FX1Poly/Typed/GrownOpenTypeSafety — OPEN type safety + evaluation determinism for the grown engine
    (five-layer-defense L4, §27.3: the open analogues of `GrownTypeSafety`)

`GrownTypeSafety` ships type safety + determinism for CLOSED grown-typed terms, resting on the empty-context
strong normalization.  This file lifts all three statements to an arbitrary well-formed context, resting on
OPEN strong normalization (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, unconditional for any
`WfContextDesc`) and the OPEN progress / canonical-forms lemma (`openNormalSubjectCanonicalOrNeutral`).  In an open context the
canonical-value conclusion gains the neutral disjunct (a variable / stuck application is a perfectly good normal
form), exactly as open progress does.

  * `HasTypeDescPi.openHasUniqueNormalForm` — **OPEN EVALUATION DETERMINISM (unconditional).**  A grown-typed term
    in any well-formed context has a UNIQUE normal form: open SN strong-normalizes it (any context, no hypothesis, `stronglyNormalizingOfWfContextDesc`);
    `exists_unique_normalForm_of_isStronglyNormalizing` (existence by weak normalization, uniqueness by raw
    confluence) delivers both halves.  Evaluation of an open grown-typed term is a well-defined
    single-valued total function — the open generalization of `closedHasUniqueNormalForm`, and the strongest
    unconditional statement here (it needs neither preservation nor closedness).

  * `HasTypeDescPi.openTypeSafetyOfSubjectReductionStar` — **OPEN TYPE SAFETY (conditional on SR-along-`↝*`).**
    Every grown-typed term in any well-formed context evaluates to a normal form that is canonical-or-neutral: open
    SN + weak normalization reach the normal form, the `subjectReductionStar` hypothesis (preservation) carries the
    classifier down the chain, and `openNormalSubjectCanonicalOrNeutral` classifies the normal endpoint.  The open
    generalization of `closedTypeSafetyOfSubjectReductionStar`; the lone hypothesis is exactly preservation.

  * `HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar` — **OPEN TYPE SAFETY + DETERMINISM (conditional on
    SR-along-`↝*`).**  The UNIQUE normal form is moreover canonical-or-neutral: determinism (confluence + open SN)
    pins the value, and the SR hypothesis types it there so `openNormalSubjectCanonicalOrNeutral` classifies it.
    The full "evaluates to THE canonical-or-neutral value" statement in open context — the open generalization of
    `closedTypeSafetyUniqueOfSubjectReductionStar`.

Together with open progress (`openProgress`) and open canonical forms per type
(`openNormalFunctionIsLambdaOrNeutral` / `openNormalTypeIsFormerOrNeutral`), this completes the open metatheory
triple — progress, canonical forms, and safety/evaluation — for the grown engine.  Open SN is unconditional,
with no fuel-stability gate.

## Why `subjectReductionStar` is a hypothesis, not discharged

Identical to `GrownTypeSafety`: preservation for the full grown engine is the master SR dispatcher, whose last
residual is the grown context-conversion `piElim` arm.  β-step preservation and the whole formation family are
already unconditional; only the iterated full-engine `↝*` preservation at an arbitrary classifier is gated.
Exposing it as a hypothesis ships the open safety capstone and names the lone gate precisely.

## Zero-axiom verification

Open SN (`stronglyNormalizingOfWfContextDesc`) + weak/unique normalization + the SR hypothesis + open
canonical forms (`openNormalSubjectCanonicalOrNeutral`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Open evaluation determinism (unconditional).**  A grown-typed term in any well-formed context has a UNIQUE
normal form: it reaches one normal form, and every normal form it reaches equals that one.  Open strong
normalization (`stronglyNormalizingOfWfContextDesc`, any context, no hypothesis) feeds
`exists_unique_normalForm_of_isStronglyNormalizing` (existence by weak normalization, uniqueness by raw
confluence).  No subject reduction, no closedness — evaluation of an open grown-typed term is a well-defined
single-valued total function.  The open generalization of `closedHasUniqueNormalForm`. -/
theorem HasTypeDescPi.openHasUniqueNormalForm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  exists_unique_normalForm_of_isStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed typed)

/-- **Open type safety (conditional on SR-along-`↝*`).**  Every grown-typed term in any well-formed context
evaluates to a normal form that is canonical-or-neutral: open strong normalization terminates the subject,
weak normalization reaches the normal form, the `subjectReductionStar` hypothesis (preservation) carries the
classifier down the chain, and `openNormalSubjectCanonicalOrNeutral` classifies the endpoint.  The open
generalization of `closedTypeSafetyOfSubjectReductionStar`; the lone gate is preservation. -/
theorem HasTypeDescPi.openTypeSafetyOfSubjectReductionStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectReductionStar : ∀ {start finish : RawTerm scope},
      HasTypeDescPi profile context start classifier →
      StepStar start finish →
      HasTypeDescPi profile context finish classifier)
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
      (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value) := by
  have terminates : IsStronglyNormalizing subject :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed typed
  obtain ⟨value, reaches, valueNormal⟩ := exists_normalForm_of_isStronglyNormalizing terminates
  refine ⟨value, reaches, valueNormal, ?_⟩
  exact HasTypeDescPi.openNormalSubjectCanonicalOrNeutral (subjectReductionStar typed reaches)
    wellFormed valueNormal

/-- **Open type safety + determinism (conditional on SR-along-`↝*`).**  The UNIQUE normal form of a grown-typed
term in any well-formed context is moreover canonical-or-neutral: the subject reaches a UNIQUE normal form
(determinism, by confluence + open SN) whose head is canonical or neutral (`openNormalSubjectCanonicalOrNeutral`
applied at the normal form, typed there via the `subjectReductionStar` hypothesis).  The full "evaluates to THE
canonical-or-neutral value" statement in open context — the open generalization of
`closedTypeSafetyUniqueOfSubjectReductionStar`. -/
theorem HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (subjectReductionStar : ∀ {start finish : RawTerm scope},
      HasTypeDescPi profile context start classifier →
      StepStar start finish →
      HasTypeDescPi profile context finish classifier)
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
        (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value)) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value := by
  obtain ⟨value, ⟨reaches, valueNormal⟩, valueUnique⟩ :=
    exists_unique_normalForm_of_isStronglyNormalizing
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed typed)
  refine ⟨value, ⟨reaches, valueNormal, ?_⟩, valueUnique⟩
  exact HasTypeDescPi.openNormalSubjectCanonicalOrNeutral (subjectReductionStar typed reaches)
    wellFormed valueNormal

end FX1Poly.Typed
