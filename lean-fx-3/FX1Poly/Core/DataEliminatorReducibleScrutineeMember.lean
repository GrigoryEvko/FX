import FX1Poly.Core.BoolElimClosedMembership
import FX1Poly.Core.DirectIotaEliminatorNeutralScrutineeMember
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.WeakHeadStepSubsumes

/-! # FX1Poly/Core/DataEliminatorReducibleScrutineeMember
    — the GENERAL-scrutinee regime of the NON-recursive data eliminators (starting with `boolElim`)

`RecursorReducibleScrutineeMember` brought the RECURSIVE eliminators (`natElim` / `natRec` / `listElim`) to
general-scrutinee reducibility: the recursor over an ARBITRARY reducible scrutinee is a member of the result
candidate, by dispatching on the data candidate's built-in value-or-neutral disjunct.  The NON-recursive
eliminators (`boolElim` / `fst` / `snd` / `optionMatch` / `eitherMatch` / `idJ` / `idStrictRec`) had only the
CLOSED membership (scope 0, via `closedReducesToValue`) and the NEUTRAL regime.  This file ships the open-scope
value regime and general-scrutinee dispatch for the non-recursive eliminators,
beginning with `boolElim` (the canonicity poster child).

The dispatch is identical in shape to the recursive case but simpler — no inductive hypothesis, no
successor-branch application — because the ι contractum is just the SELECTED BRANCH, a member by hypothesis:

  * `boolElimValueReducibility` — the OPEN-scope value regime (the genuinely-new piece, the `boolElim` analogue
    of `natElimValueReducibility`): `boolElim value t e` on a boolean VALUE lands in the result candidate, by
    cases on `boolIsValue` — each ι (`iotaBoolTrue` / `iotaBoolFalse`) selects a branch (a member) lifted to the
    cell by the candidate's weak-head expansion.  Conditional on the honest Tait `headExpand` interface, exactly
    as `natElimValueReducibility`.
  * `boolElimReducibleScrutineeMember` — the general-scrutinee dispatch: a `boolElim` whose scrutinee is a member
    of the bool candidate (so strongly normalizing AND neutral-or-reduces-to-`true`/`false`) is a member of the
    result candidate.  NEUTRAL → the cell is neutral and SN, a member by CR3
    (`memberOfStronglyNormalizingNeutral`); VALUE → `boolElimValueReducibility` lands the value cell, which
    reaches a value (its non-neutrality forces the value side via `boolElim_notNeutral_ofBoolValueScrutinee`),
    lifted back through the scrutinee congruence `StepStar.boolElimScrutinee` by `ofStepStarReachingValue`.

The open-scope generalization of `boolElimClosedIsMember` (where the neutral disjunct is vacuous at scope 0).
Fundamental-independent — pure Tait dispatch over the shipped bool candidate regimes.

## Zero-axiom verification

`boolElim_notNeutral_ofBoolValueScrutinee` is `cases` on the (concrete-index) cell neutrality giving scrutinee
neutrality, then the `rootGenerator_ne_boolTrue` / `_ne_boolFalse` discriminators (`Generator.noConfusion`-clean);
the value regime is two `headExpand`s of the bool ι head steps; the dispatch is `rcases` on the candidate
disjunct + `memberOfStronglyNormalizingNeutral` / (`boolElimValueReducibility` + `ofStepStarReachingValue` +
`resolve_left`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(verified by `#print axioms` in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The Phase-Z `boolElim` cell — author order `(motive, scrutinee, thenBranch, elseBranch)`, emitting the
canonical spine `(motive, thenBranch, elseBranch, scrutinee)` with the motive a term under one binder and the
scrutinee LAST.  Spelled exactly as `IsNeutral.boolElim`,
`boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`, and `StepStar.boolElimScrutinee` expect. -/
abbrev boolElimSpine {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_boolElim ()
    (.childCons motive
      (.childCons thenBranch
        (.childCons elseBranch
          (.childCons scrutinee .childNil))))

/-- **A neutral term's head is never `boolTrue`** (the `boolTrue` ι-vacuity discriminator, the `boolElim`
analogue of `IsNeutral.rootGenerator_ne_natZero`). -/
theorem IsNeutral.rootGenerator_ne_boolTrue {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_boolTrue := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never `boolFalse`** (the dual of `rootGenerator_ne_boolTrue`). -/
theorem IsNeutral.rootGenerator_ne_boolFalse {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_boolFalse := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A `boolElim` over a boolean-value scrutinee is never neutral.**  `IsNeutral.boolElim` is the unique
constructor producing a neutral `boolElim` cell and it demands a neutral scrutinee, but a boolean value's head is
`boolTrue` / `boolFalse` (refuted by the `rootGenerator_ne_boolTrue` / `_ne_boolFalse` discriminators).  The fact
the value-case lift consumes to extract "the value cell reaches a value" from the cell's candidate membership. -/
theorem boolElim_notNeutral_ofBoolValueScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)} {value thenBranch elseBranch : RawTerm scope}
    (valueIsBool : boolIsValue value) :
    ¬ IsNeutral (boolElimSpine motive value thenBranch elseBranch) := by
  intro cellNeutral
  cases cellNeutral with
  | boolElim scrutineeNeutral =>
      rcases valueIsBool with valueEq | valueEq
      · rw [valueEq] at scrutineeNeutral; exact scrutineeNeutral.rootGenerator_ne_boolTrue rfl
      · rw [valueEq] at scrutineeNeutral; exact scrutineeNeutral.rootGenerator_ne_boolFalse rfl

/-- **A boolean value is strongly normalizing.**  `true` / `false` are normal-form members of the bool
candidate, so strongly normalizing by CR1. -/
theorem boolValue_isStronglyNormalizing {scope : Nat} {value : RawTerm scope}
    (valueIsBool : boolIsValue value) : IsStronglyNormalizing value := by
  rcases valueIsBool with valueEq | valueEq
  · rw [valueEq]; exact boolTrueCell_isMember.stronglyNormalizing
  · rw [valueEq]; exact boolFalseCell_isMember.stronglyNormalizing

/-- **Value-case reducibility for `boolElim`** (the open-scope value regime — the `boolElim` analogue of
`natElimValueReducibility`).  By cases on the boolean value: the `iotaBoolTrue` ι selects the then-branch (a
member), the `iotaBoolFalse` ι the else-branch — each lifted to the `boolElim` cell by the candidate's
weak-head expansion (`headExpand`).  The non-recursive simplification of the recursor value regime: the ι
contractum is just the selected branch, with no successor application or inductive hypothesis. -/
theorem boolElimValueReducibility {scope : Nat}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (thenBranchMember : resultCandidate thenBranch)
    (elseBranchMember : resultCandidate elseBranch)
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, boolIsValue value →
        IsStronglyNormalizing (boolElimSpine motive value thenBranch elseBranch))
    {value : RawTerm scope} (valueIsBool : boolIsValue value) :
    resultCandidate (boolElimSpine motive value thenBranch elseBranch) := by
  rcases valueIsBool with valueEq | valueEq
  · subst valueEq
    exact headExpand IotaHeadStep.iotaBoolTrue.toWeakHeadStep thenBranchMember
      (redexStronglyNormalizing (Or.inl rfl))
  · subst valueEq
    exact headExpand IotaHeadStep.iotaBoolFalse.toWeakHeadStep elseBranchMember
      (redexStronglyNormalizing (Or.inr rfl))

/-- **`boolElim` reducibility over a general reducible scrutinee.**  Given a scrutinee that is a member of the
bool data candidate (so strongly normalizing AND neutral-or-reduces-to-`true`/`false`), reducible branches, and
the honest Tait `headExpand` interface, the `boolElim` cell is a member of the result candidate.  Dispatches on
the scrutinee's built-in disjunct: NEUTRAL → the cell is neutral and SN, a member by CR3
(`memberOfStronglyNormalizingNeutral`); VALUE → the value cell is a member (`boolElimValueReducibility`) that
reaches a value (its non-neutrality forces the value side of its disjunct), lifted back through the scrutinee
congruence by `ofStepStarReachingValue`.  Completes `boolElim` reducibility to the general-scrutinee standard of
the recursive eliminators; the closed `boolElimClosedIsMember` is the scope-0 special case (neutral disjunct
vacuous). -/
theorem boolElimReducibleScrutineeMember {scope : Nat} {isValue : RawTerm scope → Prop}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → CanonicalFormsPredicate isValue contractum →
        IsStronglyNormalizing redexTerm → CanonicalFormsPredicate isValue redexTerm)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (scrutineeMember : CanonicalFormsPredicate boolIsValue scrutinee)
    (thenBranchMember : CanonicalFormsPredicate isValue thenBranch)
    (elseBranchMember : CanonicalFormsPredicate isValue elseBranch) :
    CanonicalFormsPredicate isValue (boolElimSpine motive scrutinee thenBranch elseBranch) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (boolElimSpine motive scrutinee thenBranch elseBranch) :=
    boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
      scrutineeMember.stronglyNormalizing motiveStronglyNormalizing
      thenBranchMember.stronglyNormalizing elseBranchMember.stronglyNormalizing
  rcases scrutineeMember.2 with scrutineeNeutral | ⟨value, scrutineeToValue, valueIsBool⟩
  · exact CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral cellStronglyNormalizing
      (IsNeutral.boolElim scrutineeNeutral)
  · have redexStronglyNormalizing : ∀ {boolValue : RawTerm scope}, boolIsValue boolValue →
        IsStronglyNormalizing (boolElimSpine motive boolValue thenBranch elseBranch) :=
      fun boolValueIsBool =>
        boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
          (boolValue_isStronglyNormalizing boolValueIsBool) motiveStronglyNormalizing
          thenBranchMember.stronglyNormalizing elseBranchMember.stronglyNormalizing
    have valueMember :
        CanonicalFormsPredicate isValue (boolElimSpine motive value thenBranch elseBranch) :=
      boolElimValueReducibility (CanonicalFormsPredicate isValue)
        headExpand thenBranchMember elseBranchMember redexStronglyNormalizing valueIsBool
    have valueCellReachesValue :
        ∃ reached : RawTerm scope,
          StepStar (boolElimSpine motive value thenBranch elseBranch) reached ∧ isValue reached :=
      valueMember.2.resolve_left (boolElim_notNeutral_ofBoolValueScrutinee valueIsBool)
    exact CanonicalFormsPredicate.ofStepStarReachingValue
      (StepStar.boolElimScrutinee scrutineeToValue) cellStronglyNormalizing valueCellReachesValue

end FX1Poly.Core
