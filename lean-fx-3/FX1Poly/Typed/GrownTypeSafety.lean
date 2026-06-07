import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.NormalFormUnique

/-! # FX1Poly/Typed/GrownTypeSafety — syntactic type safety for the grown engine `HasTypeDescPi`
    (five-layer-defense L4, §27.3: progress + the SN-conditional safety capstone)

`GrownCanonicalForms.closedNormalSubjectHead` establishes CANONICAL FORMS for the grown engine: a closed NORMAL
grown-typed term has head `gen_lam` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` — a λ value or a
Π / Σ / universe type code.  Canonical forms is the *ingredient*; the §27.3 five-layer-defense L4 deliverable is
the named **preservation/progress** safety statements themselves.  This file ships them.

  * `RawTerm.IsGrownCanonicalHead` — the canonical-value-head predicate: a term whose head is one of the four
    shapes a closed grown-typed normal form can take (λ / Π-code / Σ-code / universe-code).

  * `HasTypeDescPi.closedProgress` — **PROGRESS (unconditional).**  A closed grown-typed term is either a
    canonical value (a canonical head AND a normal form) or it can take a `Step`.  The textbook "value or steps"
    safety statement: there are NO stuck closed grown-typed terms.  Proof dispatches on decidable normality —
    normal ⟹ canonical-head by `closedNormalSubjectHead` (this is where typing is load-bearing: a closed normal
    form that is NOT canonical cannot be typed), non-normal ⟹ steps by `exists_step_of_not_isStepNormalForm`.

  * `HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar` — **TYPE SAFETY (conditional on SR-along-`↝*`).**
    Every closed grown-typed term *evaluates to a canonical value*: there is a reachable normal form that is a
    canonical head.  Assembles strong normalization (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, the
    termination half), weak normalization (`exists_normalForm_of_isStronglyNormalizing`, reaching the normal
    form), the `subjectReductionStar` hypothesis (PRESERVATION — carrying the classifier down the chain), and
    canonical forms (`closedNormalSubjectHead`, the progress half at the normal form).  The lone hypothesis is
    exactly preservation; this mirrors the conditional-package discipline of
    `ConsistencyConditionalOnSubjectReduction`.

## Why `subjectReductionStar` is a hypothesis, not discharged

Preservation for the FULL grown engine (`piElim` included) is the master SR dispatcher, whose last residual is
the grown context-conversion `piElim` arm — the entangled mutual fundamental-metatheory bundle.  β-step
preservation and the whole formation family are already unconditional; only the iterated full-engine
`↝*` preservation at an arbitrary classifier is gated.  Exposing it as a hypothesis ships the safety capstone
and names the lone gate precisely, exactly as the consistency route does for `EmptyType`.

The DETERMINISM layer — evaluation lands at a UNIQUE value, the punchline that makes "the value" well defined:

  * `HasTypeDescPi.closedHasUniqueNormalForm` — **EVALUATION DETERMINISM (unconditional).**  A closed grown-typed
    term has a UNIQUE normal form: it reaches one, and every normal form it reaches is that same one.  Just open
    strong normalization fed to `exists_unique_normalForm_of_isStronglyNormalizing` (existence by weak
    normalization, uniqueness by raw confluence) — NO subject reduction needed.  Evaluation of
    a closed grown-typed term is a well-defined partial function made total by SN.

  * `HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar` — **TYPE SAFETY + DETERMINISM (conditional on
    SR-along-`↝*`).**  The unique normal form of a closed grown-typed term is moreover a canonical VALUE: it
    reaches a unique normal form (determinism) whose head is canonical (`closedNormalSubjectHead` via the SR
    hypothesis).  The full "evaluates to THE canonical value" statement — progress + preservation + confluence
    combined.

## Zero-axiom verification

`Decidable.em`-free dispatch (`by_cases` on the decidable `isStepNormalForm`) + `closedNormalSubjectHead` +
`exists_step_of_not_isStepNormalForm` (progress); open SN + weak normalization + the SR hypothesis + canonical
forms (safety).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The canonical-value-head predicate for the grown engine.**  The five head shapes a closed grown-typed
normal form can take: a λ value (`gen_lam`) or a Π / Σ / universe / list type code.  `closedNormalSubjectHead`
returns exactly this disjunction; this names it for the safety statements.  The `gen_listCode` disjunct is the
forward-compatible slot for the data-type-code formation row (GTL-11): once `gen_listCode` joins
`typingRuleDescOf`, a closed normal grown-typed `List A` head lands here; until then the disjunct is sound but
unreached, so the canonical-forms cascade is widened one commit ahead of the row. -/
abbrev RawTerm.IsGrownCanonicalHead {scope : Nat} (term : RawTerm scope) : Prop :=
  RawTerm.headGenerator term = Generator.gen_lam ∨
  RawTerm.headGenerator term = Generator.gen_piTyCode ∨
  RawTerm.headGenerator term = Generator.gen_sigmaTyCode ∨
  RawTerm.headGenerator term = Generator.gen_universeCode ∨
  RawTerm.headGenerator term = Generator.gen_listCode

/-- **Progress (unconditional).**  A closed grown-typed term is a canonical value (a canonical head AND a normal
form) or it takes a `Step` — there are no stuck closed grown-typed terms.  Dispatches on decidable normality: a
normal subject is canonical by `closedNormalSubjectHead` (typing is load-bearing — a non-canonical closed normal
form has no typing derivation); a non-normal subject steps. -/
theorem HasTypeDescPi.closedProgress {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    (RawTerm.IsGrownCanonicalHead subject ∧ RawTerm.isStepNormalForm subject)
    ∨ (∃ reduct : RawTerm 0, Step subject reduct) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · refine Or.inl ⟨?canonicalHead, isNormal⟩
    exact HasTypeDescPi.closedNormalSubjectHead typed isNormal
      (fun emptyIndex => emptyIndex.elim0)
  · exact Or.inr (exists_step_of_not_isStepNormalForm isNormal)

/-- **Type safety (conditional on SR-along-`↝*`).**  Every closed grown-typed term evaluates to a canonical
value: a reachable normal form whose head is canonical.  Open strong normalization terminates the subject;
weak normalization reaches the normal form; the `subjectReductionStar` hypothesis (preservation) carries the
classifier down the chain so canonical forms applies at the normal form.  The hypothesis is the lone gate — the
iterated master dispatcher — so this is full grown-engine type safety modulo preservation. -/
theorem HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (subjectReductionStar : ∀ {start finish : RawTerm 0},
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) start classifier →
      StepStar start finish →
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) finish classifier)
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value := by
  have terminates : IsStronglyNormalizing subject :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  obtain ⟨value, reaches, valueNormal⟩ := exists_normalForm_of_isStronglyNormalizing terminates
  refine ⟨value, reaches, valueNormal, ?canonicalHead⟩
  exact HasTypeDescPi.closedNormalSubjectHead (subjectReductionStar typed reaches)
    valueNormal (fun emptyIndex => emptyIndex.elim0)

/-- **Evaluation determinism (unconditional).**  A closed grown-typed term has a UNIQUE normal form: it reaches
one normal form, and every normal form it reaches equals that one.  Open strong normalization terminates the
subject; the unique-normal-form package (`exists_unique_normalForm_of_isStronglyNormalizing` — existence by weak
normalization, uniqueness by raw confluence) delivers both halves.  No subject reduction needed: evaluation
of a closed grown-typed term is a well-defined function of the term (total by SN, single-valued by confluence). -/
theorem HasTypeDescPi.closedHasUniqueNormalForm {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value) ∧
      ∀ otherForm : RawTerm 0,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value :=
  exists_unique_normalForm_of_isStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed)

/-- **Type safety + determinism (conditional on SR-along-`↝*`).**  The unique normal form of a closed grown-typed
term is moreover a canonical VALUE: the subject reaches a UNIQUE normal form (determinism, by confluence + SN)
whose head is canonical (`closedNormalSubjectHead` applied at the normal form, typed there via the
`subjectReductionStar` hypothesis).  The full "evaluates to THE canonical value" statement — progress,
preservation, and confluence combined into one. -/
theorem HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (subjectReductionStar : ∀ {start finish : RawTerm 0},
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) start classifier →
      StepStar start finish →
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) finish classifier)
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    ∃ value : RawTerm 0,
      (StepStar subject value ∧ RawTerm.isStepNormalForm value ∧ RawTerm.IsGrownCanonicalHead value) ∧
      ∀ otherForm : RawTerm 0,
        StepStar subject otherForm → RawTerm.isStepNormalForm otherForm → otherForm = value := by
  obtain ⟨value, ⟨reaches, valueNormal⟩, valueUnique⟩ :=
    exists_unique_normalForm_of_isStronglyNormalizing
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed)
  refine ⟨value, ⟨reaches, valueNormal, ?canonicalHead⟩, valueUnique⟩
  exact HasTypeDescPi.closedNormalSubjectHead (subjectReductionStar typed reaches)
    valueNormal (fun emptyIndex => emptyIndex.elim0)

end FX1Poly.Typed
