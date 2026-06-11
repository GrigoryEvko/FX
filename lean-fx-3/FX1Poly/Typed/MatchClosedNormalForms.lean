import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.HasTypeDescEitherMatch

/-! # FX1Poly/Typed/MatchClosedNormalForms
    — the option/either MATCH eliminator engines are VACUOUS disjuncts in closed-normal canonical forms

`BoolElimClosedNormalForms` established that the bool ELIMINATOR engine (`HasTypeDescBoolElim`) contributes no
closed-normal inhabitant — a closed `boolElim` on a closed value scrutinee always ι-fires, so it is never normal.
The combined closed-normal canonical-forms characterization (the canonicity-specific per-classifier rule-out) must
cover EVERY engine that can type a term at a data code, including the remaining standalone data ELIMINATORS.

This file lands the option/either MATCH eliminators' contribution, both VACUOUS, by the identical structural
argument:

  * **`HasTypeDescOptionMatch.noClosedNormalOptionMatch` (★)** — a closed NORMAL term typed by the option-match
    engine is impossible.  Its scrutinee is option-intro-typed at `option(A)`, hence `optionNone`/`optionSome v`
    (`subjectIsOptionConstructor`), so `optionMatch(m, n, s, optionNone/optionSome v)` is an ι-redex
    (`Step.iotaOptionMatchNone` / `iotaOptionMatchSome` fire on a constructor scrutinee regardless of `v`'s
    normality); the structural NF checker computes `false` on that head redex, so `cases normal` refutes.

  * **`HasTypeDescEitherMatch.noClosedNormalEitherMatch` (★)** — the either-match twin: the scrutinee is
    `eitherInl v`/`eitherInr v` (`subjectIsEitherInjection`), so the `eitherMatch` ι-fires.

A CLOSED eliminator term is never normal: its closed scrutinee is a constructor value, so the eliminator always
fires.  So these engines add NOTHING to the closed-normal inhabitants — exactly as the bool case.  Their real
canonicity content is the ARBITRARY-subject computing layer (the eliminator SN-reduces to a value), shipped
unconditionally as `closedOptionMatchIntoBoolComputes` / `closedOptionMatchComputes` (the general-branch
reduction) and bundled in the eliminator-layer canonicity spine; this file is the closed-NORMAL half — the
per-classifier rule-out the combined-canonicity headline needs.

## Zero-axiom verification

`cases derivation` (free-index single-arm, the `subjectIsOptionMatch`/`subjectIsEitherMatch` idiom) +
`subjectIsOptionConstructor` / `subjectIsEitherInjection` (the scrutinee is a constructor) + `cases normal` (the
NF checker computes `false` on the ι-redex head, exactly as in `noClosedNormalBoolElim`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The option-match engine has no closed-normal inhabitant (at any classifier).**  A closed NORMAL term
typed by `HasTypeDescOptionMatch` is impossible: the scrutinee is option-intro-typed at `option(A)`, hence
`optionNone`/`optionSome v` (`subjectIsOptionConstructor`), so the `optionMatch` is an ι-redex
(`Step.iotaOptionMatchNone` / `iotaOptionMatchSome`) — the structural NF checker computes `false` on that head
redex, refuting `normal`.  A closed eliminator on a closed constructor scrutinee always fires, so it is never
normal.  Classifier-agnostic.  The option twin of `HasTypeDescBoolElim.noClosedNormalBoolElim`. -/
theorem HasTypeDescOptionMatch.noClosedNormalOptionMatch {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescOptionMatch profile (TypingContext.empty : TypingContext profile 0)
      subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  cases derivation with
  | optionMatchIntro _motive scrutinee noneBranch someBranch _elementType _resultType scrutineeTyped
      _noneBranchTyped _someBranchTyped =>
      rcases scrutineeTyped.subjectIsOptionConstructor with scrutineeEq | ⟨value, scrutineeEq⟩
      · subst scrutineeEq; cases normal
      · subst scrutineeEq; cases normal

/-- **★ The either-match engine has no closed-normal inhabitant (at any classifier).**  The either twin of
`noClosedNormalOptionMatch`: the scrutinee is `eitherInl v`/`eitherInr v` (`subjectIsEitherInjection`), so the
`eitherMatch` ι-fires (`Step.iotaEitherMatchInl` / `iotaEitherMatchInr`) — never normal. -/
theorem HasTypeDescEitherMatch.noClosedNormalEitherMatch {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescEitherMatch profile (TypingContext.empty : TypingContext profile 0)
      subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    False := by
  cases derivation with
  | eitherMatchIntro _motive scrutinee leftBranch rightBranch _leftType _rightType _resultType scrutineeTyped
      _leftBranchTyped _rightBranchTyped =>
      rcases scrutineeTyped.subjectIsEitherInjection with ⟨value, scrutineeEq⟩ | ⟨value, scrutineeEq⟩
      · subst scrutineeEq; cases normal
      · subst scrutineeEq; cases normal

end FX1Poly.Typed
