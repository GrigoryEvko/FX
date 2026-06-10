import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.CombinedBoolCanonicalForms

/-! # FX1Poly/Typed/BoolElimClosedNormalForms
    — the bool ELIMINATOR engine is a VACUOUS disjunct in closed-normal canonical forms (first piece of #1138)

`closedNormalBoolCanonicalForms` (#1064) settled the closed-normal bool canonical forms over THREE engines —
data-intro values, base-type codes, and the grown `HasTypeDescPi`.  But the kernel has a FOURTH engine that can
type a term at a data code: the standalone data ELIMINATORS (`HasTypeDescBoolElim`, DI-5a #1070, and its
siblings).  Full Milestone-A canonicity must cover them — a closed `boolElim (λ_.Bool) t f scrut : Bool` is a
genuine bool-typed term.

This file lands the eliminator engine's contribution to the CLOSED-NORMAL canonical forms — and it is **vacuous**:

  * **`HasTypeDescBoolElim.noClosedNormalBoolElim` (★)** — a closed NORMAL term typed by the bool eliminator
    engine (at ANY classifier) is impossible.  The scrutinee is typed by the data-intro engine at `boolCode`,
    hence is `boolTrue`/`boolFalse` (`standaloneBoolCanonicalForms`), so `boolElim(boolTrue/boolFalse, t, e)` is an
    ι-redex (`Step.iotaBoolTrue`/`iotaBoolFalse`); the structural NF checker computes `false` on that head redex,
    so `cases normal` refutes.  The eliminator analogue of `noClosedNormalTermAtBoolType` — and EVEN SIMPLER:
    no classifier reasoning, just "a closed eliminator on a closed value scrutinee fires, so it is not normal."

  * **`closedNormalBoolCanonicalFormsWithElim` (★)** — the FOUR-engine closed-normal canonical forms: a closed
    NORMAL term typed at `boolCode` by `HasTypeDescDataIntro` ∨ `HasTypeDescBaseType` ∨ `HasTypeDescPi` ∨
    `HasTypeDescBoolElim` is `boolTrue`/`boolFalse`.  Extends `closedNormalBoolCanonicalForms` (#1064) with the
    eliminator as a vacuous fourth disjunct.

## Why this is the right closed-NORMAL piece (and what is deferred)

A CLOSED eliminator term is NEVER normal — its closed scrutinee is a value, so the eliminator always ι-fires.  So
the eliminator engine adds NOTHING to the closed-NORMAL inhabitants; its real canonicity content is the
ARBITRARY-subject case, where the eliminator term SN-reduces to a normal form (a value, by the four-engine forms
here) while preserving the classifier.  That arbitrary-subject four-engine canonicity needs SN + SR over the
combined (grown ∪ eliminator) engine — the value-case ι-SR is shipped (`boolElimTrueIotaComputesTyped` #1070); the
branch-congruence SR is the deferred combined-engine metatheory.  This file ships the closed-normal half (the
vacuity + four-engine forms); the arbitrary-subject upgrade is the #1138 follow-on.

## Zero-axiom verification

`cases derivation` (free-index single-arm, the `subjectIsBoolElim` idiom) + `standaloneBoolCanonicalForms` +
`cases normal` (the NF checker computes `false` on the ι-redex head, as in `not_isStepNormalForm_beta_smoke`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The bool eliminator engine has no closed-normal inhabitant (at any classifier).**  A closed NORMAL term
typed by `HasTypeDescBoolElim` is impossible: the scrutinee is data-intro-typed at `boolCode`, hence
`boolTrue`/`boolFalse` (`standaloneBoolCanonicalForms`), so the `boolElim` is an ι-redex (`Step.iotaBoolTrue` /
`iotaBoolFalse`) — the structural NF checker computes `false` on that head redex, refuting `normal`.  A closed
eliminator on a closed VALUE scrutinee always fires, so it is never normal.  Classifier-agnostic (the result type
is free). -/
theorem HasTypeDescBoolElim.noClosedNormalBoolElim {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0)
      subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  cases derivation with
  | boolElimIntro motive scrutinee thenBranch elseBranch _resultType scrutineeTyped
      _thenTyped _elseTyped =>
      rcases standaloneBoolCanonicalForms (Or.inl scrutineeTyped) with scrutineeEq | scrutineeEq
      · subst scrutineeEq; cases normal
      · subst scrutineeEq; cases normal

/-- **★ Four-engine closed-normal bool canonical forms.**  A closed NORMAL term typed at `boolCode` by ANY of the
four engines — data-intro values, base-type codes, the grown `HasTypeDescPi`, OR the bool eliminator
`HasTypeDescBoolElim` — is `boolTrue`/`boolFalse`.  Extends `closedNormalBoolCanonicalForms` (#1064, three
engines) with the eliminator as a VACUOUS fourth disjunct (`noClosedNormalBoolElim`).  The closed-normal half of
the four-engine bool canonicity; the arbitrary-subject upgrade (via combined SN/SR) is the #1138 follow-on. -/
theorem closedNormalBoolCanonicalFormsWithElim {profile : PolyProfile} {subject : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
      HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped | elimTyped
  · exact standaloneBoolCanonicalForms (Or.inl dataIntroTyped)
  · exact standaloneBoolCanonicalForms (Or.inr baseTypeTyped)
  · exact (HasTypeDescPi.noClosedNormalTermAtBoolType grownTyped normal).elim
  · exact (HasTypeDescBoolElim.noClosedNormalBoolElim elimTyped normal).elim

end FX1Poly.Typed
