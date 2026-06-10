import FX1Poly.Typed.MatchElimComputingCanonicityTyped

/-! # FX1Poly/Typed/MatchGeneralBranchCanonicity
    — option/either MATCH eliminator-computing canonicity for ARBITRARY branches, abstracting branch canonicity

`MatchElimComputingCanonicityTyped` closed the eliminator-canonicity corner only for CONSTANT bool branches
(`λ_.boolTrue`), where the stored payload obstruction dissolves because the branch ignores its argument.  Its
honest deferral named "the GENERAL (payload-using) branch" — where the eliminator's value depends on the
some/inl/inr payload — as the broader integration.

This file lands the general structural reduction.  The eliminator-computing canonicity has TWO independent parts:

  * the SCRUTINEE part — a closed option/either reduces to a constructor value (`closedOptionCanonicalForms` /
    `closedEitherCanonicalForms`), carried under the match by the scrutinee congruence, then the matching ι rule
    fires to select-and-APPLY the branch to the stored payload;
  * the BRANCH part — the selected branch, applied to the payload, reduces to a value.

`closedOptionMatchComputes` / `closedEitherMatchComputes` discharge the FIRST part unconditionally and take the
SECOND as a hypothesis (`branchComputes : ∀ payload, ∃ out, StepStar (app branch payload) out ∧ isValue out`).
So they reduce eliminator canonicity to branch canonicity for ANY branches — the constant branches of the prior
file become a one-line corollary (`closedOptionMatchIntoBoolFromGeneral`), and genuinely PAYLOAD-USING branches
are now in scope: `closedOptionMatchIdentityIntoBool` feeds the some-payload `boolTrue` straight out through the
IDENTITY branch `λx.x` (the payload is consumed and re-emitted, not discarded), reaching the canonical bool
`boolTrue` — past the constant-branch corner the prior file could not cross.

The branch-canonicity hypothesis is exactly where the eventual recursion lives: for a general branch typed at
`elementType → resultType`, discharging it for the specific (typed) payload is the recursive call of the full
combined canonicity over the type structure.  This file isolates the structural reduction cleanly; the recursive
discharge over arbitrary result types remains the named combined-canonicity follow-on.

## Zero-axiom verification

`closedOptionCanonicalForms` / `closedEitherCanonicalForms` (scrutinee) + `StepStar.optionMatchScrutinee` /
`StepStar.eitherMatchScrutinee` (congruence) + `StepStar.transLast` with `Step.iotaOptionMatch*` /
`Step.iotaEitherMatch*` (ι) + `StepStar.trans_compose` (chain in the branch reduction) + `Step.beta` (the
identity/constant branch β).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Option-match eliminator-computing canonicity for ARBITRARY branches.**  A closed
`optionMatch(scrutinee, noneBranch, someBranch)` whose scrutinee is typed at `option(elementType)` reduces by
`↝*` to an `isValue`, GIVEN that the none-branch reduces to an `isValue` and the some-branch applied to any
payload reduces to an `isValue`.  The scrutinee reduces to `optionNone`/`optionSome inner`
(`closedOptionCanonicalForms`); the congruence carries it under the match; the ι rule selects (and, for `some`,
applies) the branch; the branch-canonicity hypothesis finishes.  Reduces eliminator canonicity to branch
canonicity for ANY branches — including payload-using ones. -/
theorem closedOptionMatchComputes {profile : PolyProfile}
    {scrutinee elementType noneBranch someBranch : RawTerm 0}
    {isValue : RawTerm 0 → Prop}
    (scrutineeTyped :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType))
    (noneBranchComputes : ∃ out : RawTerm 0, StepStar noneBranch out ∧ isValue out)
    (someBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell someBranch payload) out ∧ isValue out) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell scrutinee noneBranch someBranch) out ∧ isValue out := by
  obtain ⟨scrutValue, scrutReduces, scrutIsOption⟩ := closedOptionCanonicalForms scrutineeTyped
  rcases scrutIsOption with noneEq | ⟨inner, someEq⟩
  · subst noneEq
    obtain ⟨out, branchReduces, branchValue⟩ := noneBranchComputes
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) Step.iotaOptionMatchNone)
        branchReduces,
      branchValue⟩
  · subst someEq
    obtain ⟨out, branchReduces, branchValue⟩ := someBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) Step.iotaOptionMatchSome)
        branchReduces,
      branchValue⟩

/-- **★ Either-match eliminator-computing canonicity for ARBITRARY branches.**  A closed
`eitherMatch(scrutinee, leftBranch, rightBranch)` whose scrutinee is typed at `either(leftType, rightType)`
reduces by `↝*` to an `isValue`, GIVEN that each branch applied to any payload reduces to an `isValue`.  The
either twin of `closedOptionMatchComputes`. -/
theorem closedEitherMatchComputes {profile : PolyProfile}
    {scrutinee leftType rightType leftBranch rightBranch : RawTerm 0}
    {isValue : RawTerm 0 → Prop}
    (scrutineeTyped :
      HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType))
    (leftBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell leftBranch payload) out ∧ isValue out)
    (rightBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell rightBranch payload) out ∧ isValue out) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell scrutinee leftBranch rightBranch) out ∧ isValue out := by
  obtain ⟨scrutValue, scrutReduces, scrutIsEither⟩ := closedEitherCanonicalForms scrutineeTyped
  rcases scrutIsEither with ⟨inner, inlEq⟩ | ⟨inner, inrEq⟩
  · subst inlEq
    obtain ⟨out, branchReduces, branchValue⟩ := leftBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) Step.iotaEitherMatchInl)
        branchReduces,
      branchValue⟩
  · subst inrEq
    obtain ⟨out, branchReduces, branchValue⟩ := rightBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) Step.iotaEitherMatchInr)
        branchReduces,
      branchValue⟩

/-- **Constant-branch option canonicity, recovered as a corollary** of the general theorem — the shipped
`closedOptionMatchIntoBoolComputes` (constant `boolTrue` / `λ_.boolTrue` branches) is the general theorem at the
constant branch canonicity (`app (λ_.boolTrue) payload ↝β boolTrue` for any payload).  Witnesses the general
theorem subsumes the constant case. -/
theorem closedOptionMatchIntoBoolFromGeneral {profile : PolyProfile}
    {scrutinee elementType : RawTerm 0}
    (scrutineeTyped :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType)) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell scrutinee boolTrueCell
        (lamCell unitCell (boolTrueCell : RawTerm 1))) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedOptionMatchComputes
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    scrutineeTyped
    ⟨boolTrueCell, StepStar.refl _, Or.inl rfl⟩
    (fun _payload => ⟨boolTrueCell, StepStar.transLast (StepStar.refl _) Step.beta, Or.inl rfl⟩)

/-- **★ Payload-USING option canonicity (identity branch).**  A closed `optionMatch(optionSome boolTrue,
noneBranch, λx.x)` reduces to the canonical bool `boolTrue` — the IDENTITY some-branch CONSUMES the stored
payload `boolTrue` and re-emits it, so the eliminator's output genuinely depends on the payload (unlike the
constant branch).  This crosses the boundary `MatchElimComputingCanonicityTyped` flagged: the some-branch
produces a value FROM the payload. -/
theorem closedOptionMatchIdentityIntoBool {noneBranch : RawTerm 0} :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell (optionSomeCell boolTrueCell) noneBranch
        (lamCell unitCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  ⟨boolTrueCell,
   StepStar.transLast
     (StepStar.transLast (StepStar.refl _) Step.iotaOptionMatchSome)
     Step.beta,
   Or.inl rfl⟩

/-- **★ Payload-USING either canonicity (identity left branch).**  A closed `eitherMatch(eitherInl boolTrue,
λx.x, rightBranch)` reduces to the canonical bool `boolTrue` — the IDENTITY left branch consumes and re-emits the
`inl` payload.  The either twin of `closedOptionMatchIdentityIntoBool`. -/
theorem closedEitherMatchIdentityIntoBool {rightBranch : RawTerm 0} :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell (eitherInlCell boolTrueCell)
        (lamCell unitCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) rightBranch) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  ⟨boolTrueCell,
   StepStar.transLast
     (StepStar.transLast (StepStar.refl _) Step.iotaEitherMatchInl)
     Step.beta,
   Or.inl rfl⟩

end FX1Poly.Typed
