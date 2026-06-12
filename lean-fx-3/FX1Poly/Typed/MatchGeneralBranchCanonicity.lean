import FX1Poly.Typed.MatchElimComputingCanonicityTyped
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Typed/MatchGeneralBranchCanonicity
    — option/either MATCH eliminator-computing canonicity for ARBITRARY branches, abstracting branch canonicity

`MatchElimComputingCanonicityTyped` closed the eliminator-canonicity corner only for CONSTANT bool branches
(`λ_.boolTrue`), where the stored payload obstruction dissolves because the branch ignores its argument.  Its
honest deferral named "the GENERAL (payload-using) branch" — where the eliminator's value depends on the
some/inl/inr payload — as the broader integration.

This file lands the general structural reduction.  The eliminator-computing canonicity has TWO independent parts:

  * the SCRUTINEE part — the scrutinee reduces to a constructor value (taken as the OPERATIONAL
    scrutinee-canonicity hypothesis since the NATIVE-42 re-shape; any typing route that yields it — a
    constructor-headed scrutinee by `refl`, the union arc once its SR/SN lands — discharges it), carried
    under the match by the scrutinee congruence, then the matching ι rule fires to select-and-APPLY the
    branch to the stored payload;
  * the BRANCH part — the selected branch, applied to the payload, reduces to a value.

`closedOptionMatchComputes` / `closedEitherMatchComputes` take BOTH parts as hypotheses
(`branchComputes : ∀ payload, ∃ out, StepStar (app branch payload) out ∧ isValue out`).
So they reduce eliminator canonicity to branch canonicity for ANY branches — the constant branches of the prior
file become a one-line corollary (`closedOptionMatchIntoBoolFromGeneral`), and genuinely PAYLOAD-USING branches
are now in scope (`optionMatch(m, n, branch, scrutinee)`): `closedOptionMatchIdentityIntoBool` feeds the some-payload `boolTrue` straight out through the
IDENTITY branch `λx.x` (the payload is consumed and re-emitted, not discarded), reaching the canonical bool
`boolTrue` — past the constant-branch corner the prior file could not cross.

The branch-canonicity hypothesis is exactly where the eventual recursion lives: for a general branch typed at
`elementType → resultType`, discharging it for the specific (typed) payload is the recursive call of the full
combined canonicity over the type structure.  This file isolates the structural reduction cleanly; the recursive
discharge over arbitrary result types remains the named combined-canonicity follow-on.

## Zero-axiom verification

The scrutinee-canonicity hypothesis (operational) + `StepStar.optionMatchScrutinee` /
`StepStar.eitherMatchScrutinee` (congruence) + `StepStar.transLast` with `IotaHeadStep.iotaOptionMatch*` /
`IotaHeadStep.iotaEitherMatch*` via `toStep` (ι) + `StepStar.trans_compose` (chain in the branch reduction) + `Step.beta` (the
identity/constant branch β).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Option-match eliminator-computing canonicity for ARBITRARY branches.**  A closed
`optionMatch(m, noneBranch, someBranch, scrutinee)` whose scrutinee reduces to an option constructor value
reduces by `↝*` to an `isValue`, GIVEN that the none-branch reduces to an `isValue` and the some-branch
applied to any payload reduces to an `isValue`.  The congruence carries the scrutinee reduction under the
match; the ι rule selects (and, for `some`, applies) the branch; the branch-canonicity hypothesis finishes.
Reduces eliminator canonicity to branch canonicity for ANY branches — including payload-using ones.
(NATIVE-42 re-shape: the scrutinee hypothesis is the OPERATIONAL canonicity the retired zoo statement
used to derive.) -/
theorem closedOptionMatchComputes
    {motive : RawTerm 1}
    {scrutinee noneBranch someBranch : RawTerm 0}
    {isValue : RawTerm 0 → Prop}
    (scrutineeCanonical : ∃ scrutValue : RawTerm 0, StepStar scrutinee scrutValue ∧
      (scrutValue = optionNoneCell ∨ ∃ inner : RawTerm 0, scrutValue = optionSomeCell inner))
    (noneBranchComputes : ∃ out : RawTerm 0, StepStar noneBranch out ∧ isValue out)
    (someBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell someBranch payload) out ∧ isValue out) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell motive noneBranch someBranch scrutinee) out ∧ isValue out := by
  obtain ⟨scrutValue, scrutReduces, scrutIsOption⟩ := scrutineeCanonical
  rcases scrutIsOption with noneEq | ⟨inner, someEq⟩
  · subst noneEq
    obtain ⟨out, branchReduces, branchValue⟩ := noneBranchComputes
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) IotaHeadStep.iotaOptionMatchNone.toStep)
        branchReduces,
      branchValue⟩
  · subst someEq
    obtain ⟨out, branchReduces, branchValue⟩ := someBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) IotaHeadStep.iotaOptionMatchSome.toStep)
        branchReduces,
      branchValue⟩

/-- **★ Either-match eliminator-computing canonicity for ARBITRARY branches.**  A closed
`eitherMatch(m, leftBranch, rightBranch, scrutinee)` whose scrutinee reduces to an either injection value
reduces by `↝*` to an `isValue`, GIVEN that each branch applied to any payload reduces to an `isValue`.  The
either twin of `closedOptionMatchComputes`.  (NATIVE-42 re-shape: operational scrutinee-canonicity
hypothesis.) -/
theorem closedEitherMatchComputes
    {motive : RawTerm 1}
    {scrutinee leftBranch rightBranch : RawTerm 0}
    {isValue : RawTerm 0 → Prop}
    (scrutineeCanonical : ∃ scrutValue : RawTerm 0, StepStar scrutinee scrutValue ∧
      ((∃ inner : RawTerm 0, scrutValue = eitherInlCell inner) ∨
        (∃ inner : RawTerm 0, scrutValue = eitherInrCell inner)))
    (leftBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell leftBranch payload) out ∧ isValue out)
    (rightBranchComputes : ∀ payload : RawTerm 0,
      ∃ out : RawTerm 0, StepStar (appCell rightBranch payload) out ∧ isValue out) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell motive leftBranch rightBranch scrutinee) out ∧ isValue out := by
  obtain ⟨scrutValue, scrutReduces, scrutIsEither⟩ := scrutineeCanonical
  rcases scrutIsEither with ⟨inner, inlEq⟩ | ⟨inner, inrEq⟩
  · subst inlEq
    obtain ⟨out, branchReduces, branchValue⟩ := leftBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) IotaHeadStep.iotaEitherMatchInl.toStep)
        branchReduces,
      branchValue⟩
  · subst inrEq
    obtain ⟨out, branchReduces, branchValue⟩ := rightBranchComputes inner
    exact ⟨out,
      StepStar.trans_compose
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) IotaHeadStep.iotaEitherMatchInr.toStep)
        branchReduces,
      branchValue⟩

/-- **Constant-branch option canonicity, recovered as a corollary** of the general theorem — the shipped
`closedOptionMatchIntoBoolComputes` (constant `boolTrue` / `λ_.boolTrue` branches) is the general theorem at the
constant branch canonicity (`app (λ_.boolTrue) payload ↝β boolTrue` for any payload).  Witnesses the general
theorem subsumes the constant case. -/
theorem closedOptionMatchIntoBoolFromGeneral
    {scrutinee : RawTerm 0}
    (scrutineeCanonical : ∃ scrutValue : RawTerm 0, StepStar scrutinee scrutValue ∧
      (scrutValue = optionNoneCell ∨ ∃ inner : RawTerm 0, scrutValue = optionSomeCell inner)) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) boolTrueCell
        (lamCell unitCell (boolTrueCell : RawTerm 1)) scrutinee) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedOptionMatchComputes
    (isValue := fun value => value = boolTrueCell ∨ value = boolFalseCell)
    scrutineeCanonical
    ⟨boolTrueCell, StepStar.refl _, Or.inl rfl⟩
    (fun _payload => ⟨boolTrueCell, StepStar.transLast (StepStar.refl _) Step.beta, Or.inl rfl⟩)

/-- **★ Payload-USING option canonicity (identity branch).**  A closed `optionMatch(m, noneBranch, λx.x,
optionSome boolTrue)` reduces to the canonical bool `boolTrue` — the IDENTITY some-branch CONSUMES the stored
payload `boolTrue` and re-emits it, so the eliminator's output genuinely depends on the payload (unlike the
constant branch).  This crosses the boundary `MatchElimComputingCanonicityTyped` flagged: the some-branch
produces a value FROM the payload. -/
theorem closedOptionMatchIdentityIntoBool {noneBranch : RawTerm 0} :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) noneBranch
        (lamCell unitCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) (optionSomeCell boolTrueCell)) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  ⟨boolTrueCell,
   StepStar.transLast
     (StepStar.transLast (StepStar.refl _) IotaHeadStep.iotaOptionMatchSome.toStep)
     Step.beta,
   Or.inl rfl⟩

/-- **★ Payload-USING either canonicity (identity left branch).**  A closed `eitherMatch(m, λx.x, rightBranch,
eitherInl boolTrue)` reduces to the canonical bool `boolTrue` — the IDENTITY left branch consumes and re-emits the
`inl` payload.  The either twin of `closedOptionMatchIdentityIntoBool`. -/
theorem closedEitherMatchIdentityIntoBool {rightBranch : RawTerm 0} :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (lamCell unitCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) rightBranch (eitherInlCell boolTrueCell)) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  ⟨boolTrueCell,
   StepStar.transLast
     (StepStar.transLast (StepStar.refl _) IotaHeadStep.iotaEitherMatchInl.toStep)
     Step.beta,
   Or.inl rfl⟩

end FX1Poly.Typed
