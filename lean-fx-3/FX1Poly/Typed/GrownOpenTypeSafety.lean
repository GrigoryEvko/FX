import FX1Poly.Typed.GrownOpenProgress
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.NormalFormUnique

/-! # FX1Poly/Typed/GrownOpenTypeSafety — OPEN type safety + evaluation determinism for the grown engine
    (five-layer-defense L4, §27.3: the open analogues of `GrownTypeSafety`)

`GrownTypeSafety` shipped type safety + determinism for CLOSED grown-typed terms, resting on the empty-context
strong normalization.  This file lifts all three statements to an arbitrary well-formed context, resting on OB-5
OPEN strong normalization (`HasTypeDescPi.stronglyNormalizingOfWfContext`, unconditional for any `WfContext`) and
the OPEN progress / canonical-forms lemma (`openNormalSubjectCanonicalOrNeutral`).  In an open context the
canonical-value conclusion gains the neutral disjunct (a variable / stuck application is a perfectly good normal
form), exactly as open progress does.

  * `HasTypeDescPi.openHasUniqueNormalForm` — **OPEN EVALUATION DETERMINISM (unconditional).**  A grown-typed term
    in any well-formed context has a UNIQUE normal form: OB-5 strong-normalizes it (any context, no hypothesis);
    `exists_unique_normalForm_of_isStronglyNormalizing` (existence by weak normalization, uniqueness by raw
    confluence, the `#420` harvest) delivers both halves.  Evaluation of an open grown-typed term is a well-defined
    single-valued total function — the open generalization of `closedHasUniqueNormalForm`, and the strongest
    unconditional statement here (it needs neither preservation nor closedness).

  * `HasTypeDescPi.openTypeSafetyOfSubjectReductionStar` — **OPEN TYPE SAFETY (conditional on SR-along-`↝*`).**
    Every grown-typed term in any well-formed context evaluates to a normal form that is canonical-or-neutral: OB-5
    SN + weak normalization reach the normal form, the `subjectReductionStar` hypothesis (preservation) carries the
    classifier down the chain, and `openNormalSubjectCanonicalOrNeutral` classifies the normal endpoint.  The open
    generalization of `closedTypeSafetyOfSubjectReductionStar`; the lone hypothesis is exactly preservation,
    mirroring the conditional-package discipline (`UB-SD-conditionalPackage`/`#664`).

  * `HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar` — **OPEN TYPE SAFETY + DETERMINISM (conditional on
    SR-along-`↝*`).**  The UNIQUE normal form is moreover canonical-or-neutral: determinism (confluence + OB-5 SN)
    pins the value, and the SR hypothesis types it there so `openNormalSubjectCanonicalOrNeutral` classifies it.
    The full "evaluates to THE canonical-or-neutral value" statement in open context — the open generalization of
    `closedTypeSafetyUniqueOfSubjectReductionStar`.

Together with open progress (`openProgress`) and open canonical forms per type
(`openNormalFunctionIsLambdaOrNeutral` / `openNormalTypeIsFormerOrNeutral`), this completes the open metatheory
triple — progress, canonical forms, and safety/evaluation — for the grown engine.  `#672`-independent: OB-5 is the
unconditional open SN, no fuel-stability gate.

## Why `subjectReductionStar` is a hypothesis, not discharged

Identical to `GrownTypeSafety`: preservation for the full grown engine is the SN-055 master SR dispatcher
(`SRD-1`/`#844`, `TG-3`/`#853`), whose last residual is the grown context-conversion `piElim` arm
(`GCC-5`/`#842`).  β-step preservation and the whole formation family are already unconditional; only the iterated
full-engine `↝*` preservation at an arbitrary classifier is gated.  Exposing it as a hypothesis ships the open
safety capstone now and names the lone gate precisely.

## Zero-axiom verification

OB-5 open SN (`stronglyNormalizingOfWfContext`) + weak/unique normalization + the SR hypothesis + open canonical
forms (`openNormalSubjectCanonicalOrNeutral`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Open evaluation determinism (unconditional).**  A grown-typed term in any well-formed context has a UNIQUE
normal form: it reaches one normal form, and every normal form it reaches equals that one.  OB-5 open strong
normalization (`stronglyNormalizingOfWfContext`, any context, no hypothesis) feeds
`exists_unique_normalForm_of_isStronglyNormalizing` (existence by weak normalization, uniqueness by raw confluence,
the `#420` harvest).  No subject reduction, no closedness — evaluation of an open grown-typed term is a well-defined
single-valued total function.  The open generalization of `closedHasUniqueNormalForm`. -/
theorem HasTypeDescPi.openHasUniqueNormalForm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContext context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  exists_unique_normalForm_of_isStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContext wellFormed typed)

/-- **Open type safety (conditional on SR-along-`↝*`).**  Every grown-typed term in any well-formed context
evaluates to a normal form that is canonical-or-neutral: OB-5 open strong normalization terminates the subject,
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
    (wellFormed : WfContext context) :
    ∃ value : RawTerm scope,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
      (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value) := by
  have terminates : IsStronglyNormalizing subject :=
    HasTypeDescPi.stronglyNormalizingOfWfContext wellFormed typed
  obtain ⟨value, reaches, valueNormal⟩ := exists_normalForm_of_isStronglyNormalizing terminates
  refine ⟨value, reaches, valueNormal, ?_⟩
  exact HasTypeDescPi.openNormalSubjectCanonicalOrNeutral (subjectReductionStar typed reaches)
    wellFormed valueNormal

/-- **Open type safety + determinism (conditional on SR-along-`↝*`).**  The UNIQUE normal form of a grown-typed
term in any well-formed context is moreover canonical-or-neutral: the subject reaches a UNIQUE normal form
(determinism, by confluence + OB-5 SN) whose head is canonical or neutral (`openNormalSubjectCanonicalOrNeutral`
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
    (wellFormed : WfContext context) :
    ∃ value : RawTerm scope,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧
        (RawTerm.IsGrownCanonicalHead value ∨ IsNeutral value)) ∧
      ∀ otherForm : RawTerm scope,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value := by
  obtain ⟨value, ⟨reaches, valueNormal⟩, valueUnique⟩ :=
    exists_unique_normalForm_of_isStronglyNormalizing
      (HasTypeDescPi.stronglyNormalizingOfWfContext wellFormed typed)
  refine ⟨value, ⟨reaches, valueNormal, ?_⟩, valueUnique⟩
  exact HasTypeDescPi.openNormalSubjectCanonicalOrNeutral (subjectReductionStar typed reaches)
    wellFormed valueNormal

end FX1Poly.Typed
