import FX1Poly.Core.NatElimNeutralScrutineeMember

/-! # FX1Poly/Core/MatchEliminatorNeutralScrutineeMember
    — the neutral-scrutinee regime of the APPLICATION-ι match eliminators (optionMatch / eitherMatch)

The last two eliminators reaching neutral-coverage parity, completing the arc: every one of the twelve
`IsNeutral` eliminators (var, app, fst, snd, boolElim, natElim, natRec, listElim, optionMatch, eitherMatch, idJ,
idStrictRec) is now reducible over a neutral principal child.

`optionMatch` / `eitherMatch` are APPLICATION-ι: their firing reduct applies the matched branch to the carried
value (`optionMatch (some v) n s ↝ app s v`, `eitherMatch (inl v) l r ↝ app l v`).  Unlike the direct-ι
eliminators (`DirectIotaEliminatorNeutralScrutineeMember`), their shipped cell-SN-from-children
(`StrongNormalizationMatch.lean`) carries an extra branch-application interface, so the neutral member is NOT a
pure compose.  But the structural fact is the same as for the recursive recursors: a NEUTRAL scrutinee is never a
constructor (`some`/`none`, `inl`/`inr`) and stays neutral under `Step`, so the match NEVER ι-fires — the cell
reduces purely by congruence.  Hence a bespoke triple-accessibility cell-SN (the `natElim` pattern, with the two
ι cases VACUOUS by neutrality), composed with `IsReducibilityCandidate.memberOfStronglyNormalizingNeutral` +
`IsNeutral.optionMatch` / `IsNeutral.eitherMatch`.

Six results:

  * `IsNeutral.rootGenerator_ne_optionNone` / `_optionSome` / `_eitherInl` / `_eitherInr` — a neutral term's head
    is never a match-constructor (the ι-vacuity discriminators), uniform over the neutral family exactly as
    `IsNeutral.rootGenerator_ne_natZero`.
  * `optionMatch_neutralScrutinee_isStronglyNormalizing` / `eitherMatch_…` — the cell at a neutral SN scrutinee
    with SN branches is SN, by a triple accessibility recursion whose two ι-reduct cases are vacuous.
  * `optionMatchNeutralScrutineeMember` / `eitherMatchNeutralScrutineeMember` — the member arms.

`#672`-independent (fixed result candidate, the pure Tait neutral-eliminator argument).

## Zero-axiom verification

The discriminators are `cases neutral <;> Generator.noConfusion`; the cell-SN recursors are a triple `Acc.intro`
over the branch + scrutinee accessibilities with `Step.from_optionMatch` / `from_eitherMatch` dispatch (the
constructor ι cases refuted by `congrArg RawTerm.rootGenerator` against the neutral discriminators); the member
arms compose through `memberOfStronglyNormalizingNeutral`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `optionMatch` cell over its (scrutinee, noneBranch, someBranch) spine, spelled exactly as
`IsNeutral.optionMatch` and `Step.from_optionMatch` expect. -/
abbrev optionMatchCellSpine {scope : Nat} (scrutinee noneBranch someBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))

/-- The `eitherMatch` cell over its (scrutinee, leftBranch, rightBranch) spine. -/
abbrev eitherMatchCellSpine {scope : Nat} (scrutinee leftBranch rightBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))

/-- **A neutral term's head is never the `optionNone` constructor** (an Option ι-vacuity discriminator). -/
theorem IsNeutral.rootGenerator_ne_optionNone {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_optionNone := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `optionSome` constructor** (the dual Option ι-vacuity discriminator). -/
theorem IsNeutral.rootGenerator_ne_optionSome {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_optionSome := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `eitherInl` constructor** (an Either ι-vacuity discriminator). -/
theorem IsNeutral.rootGenerator_ne_eitherInl {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_eitherInl := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `eitherInr` constructor** (the dual Either ι-vacuity discriminator). -/
theorem IsNeutral.rootGenerator_ne_eitherInr {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_eitherInr := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **`optionMatch` over a neutral SN scrutinee with SN branches is strongly normalizing.**  A neutral scrutinee
is never an Option constructor and stays neutral under `Step`, so the match never ι-fires — the cell reduces
purely by congruence in its three children.  A triple accessibility recursion over (scrutinee, noneBranch,
someBranch): `Step.from_optionMatch`'s two ι cases are refuted by the neutrality discriminators, and its three
congruence cases recurse. -/
theorem optionMatch_neutralScrutinee_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope} (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {noneBranch someBranch : RawTerm scope}
    (noneBranchStronglyNormalizing : IsStronglyNormalizing noneBranch)
    (someBranchStronglyNormalizing : IsStronglyNormalizing someBranch) :
    IsStronglyNormalizing (optionMatchCellSpine scrutinee noneBranch someBranch) := by
  suffices aux :
    ∀ scrutinee : RawTerm scope, IsStronglyNormalizing scrutinee → IsNeutral scrutinee →
    ∀ noneBranch : RawTerm scope, IsStronglyNormalizing noneBranch →
    ∀ someBranch : RawTerm scope, IsStronglyNormalizing someBranch →
      IsStronglyNormalizing (optionMatchCellSpine scrutinee noneBranch someBranch) by
    exact aux scrutinee scrutineeStronglyNormalizing scrutineeNeutral noneBranch
      noneBranchStronglyNormalizing someBranch someBranchStronglyNormalizing
  clear scrutineeStronglyNormalizing scrutineeNeutral noneBranchStronglyNormalizing
    someBranchStronglyNormalizing scrutinee noneBranch someBranch
  intro scrutinee scrutineeStronglyNormalizing
  induction scrutineeStronglyNormalizing with
  | intro scrutineeNode _scrutineeAccessible scrutineeInductiveHypothesis =>
    intro scrutineeNeutral noneBranch noneBranchStronglyNormalizing
    induction noneBranchStronglyNormalizing with
    | intro noneNode _noneAccessible noneInductiveHypothesis =>
      intro someBranch someBranchStronglyNormalizing
      induction someBranchStronglyNormalizing with
      | intro someNode someNodeAccessible someInductiveHypothesis =>
        apply Acc.intro
        intro target step
        rcases Step.from_optionMatch step with
          ⟨scrutineeIsNone, _⟩ |
          ⟨_value, scrutineeIsSome, _⟩ |
          ⟨scrutineeAfter, targetEquation, scrutineeStep⟩ |
          ⟨noneAfter, targetEquation, noneStep⟩ |
          ⟨someAfter, targetEquation, someStep⟩
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsNone)
            scrutineeNeutral.rootGenerator_ne_optionNone
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsSome)
            scrutineeNeutral.rootGenerator_ne_optionSome
        · rw [targetEquation]
          exact scrutineeInductiveHypothesis scrutineeAfter scrutineeStep
            (scrutineeNeutral.closedUnderStep scrutineeStep)
            noneNode (Acc.intro noneNode _noneAccessible)
            someNode (Acc.intro someNode someNodeAccessible)
        · rw [targetEquation]
          exact noneInductiveHypothesis noneAfter noneStep someNode
            (Acc.intro someNode someNodeAccessible)
        · rw [targetEquation]
          exact someInductiveHypothesis someAfter someStep

/-- **`eitherMatch` over a neutral SN scrutinee with SN branches is strongly normalizing** — the Either twin of
`optionMatch_neutralScrutinee_isStronglyNormalizing` (both ι cases are existential `inl`/`inr`, both vacuous by
neutrality). -/
theorem eitherMatch_neutralScrutinee_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope} (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {leftBranch rightBranch : RawTerm scope}
    (leftBranchStronglyNormalizing : IsStronglyNormalizing leftBranch)
    (rightBranchStronglyNormalizing : IsStronglyNormalizing rightBranch) :
    IsStronglyNormalizing (eitherMatchCellSpine scrutinee leftBranch rightBranch) := by
  suffices aux :
    ∀ scrutinee : RawTerm scope, IsStronglyNormalizing scrutinee → IsNeutral scrutinee →
    ∀ leftBranch : RawTerm scope, IsStronglyNormalizing leftBranch →
    ∀ rightBranch : RawTerm scope, IsStronglyNormalizing rightBranch →
      IsStronglyNormalizing (eitherMatchCellSpine scrutinee leftBranch rightBranch) by
    exact aux scrutinee scrutineeStronglyNormalizing scrutineeNeutral leftBranch
      leftBranchStronglyNormalizing rightBranch rightBranchStronglyNormalizing
  clear scrutineeStronglyNormalizing scrutineeNeutral leftBranchStronglyNormalizing
    rightBranchStronglyNormalizing scrutinee leftBranch rightBranch
  intro scrutinee scrutineeStronglyNormalizing
  induction scrutineeStronglyNormalizing with
  | intro scrutineeNode _scrutineeAccessible scrutineeInductiveHypothesis =>
    intro scrutineeNeutral leftBranch leftBranchStronglyNormalizing
    induction leftBranchStronglyNormalizing with
    | intro leftNode _leftAccessible leftInductiveHypothesis =>
      intro rightBranch rightBranchStronglyNormalizing
      induction rightBranchStronglyNormalizing with
      | intro rightNode rightNodeAccessible rightInductiveHypothesis =>
        apply Acc.intro
        intro target step
        rcases Step.from_eitherMatch step with
          ⟨_value, scrutineeIsInl, _⟩ |
          ⟨_value, scrutineeIsInr, _⟩ |
          ⟨scrutineeAfter, targetEquation, scrutineeStep⟩ |
          ⟨leftAfter, targetEquation, leftStep⟩ |
          ⟨rightAfter, targetEquation, rightStep⟩
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsInl)
            scrutineeNeutral.rootGenerator_ne_eitherInl
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsInr)
            scrutineeNeutral.rootGenerator_ne_eitherInr
        · rw [targetEquation]
          exact scrutineeInductiveHypothesis scrutineeAfter scrutineeStep
            (scrutineeNeutral.closedUnderStep scrutineeStep)
            leftNode (Acc.intro leftNode _leftAccessible)
            rightNode (Acc.intro rightNode rightNodeAccessible)
        · rw [targetEquation]
          exact leftInductiveHypothesis leftAfter leftStep rightNode
            (Acc.intro rightNode rightNodeAccessible)
        · rw [targetEquation]
          exact rightInductiveHypothesis rightAfter rightStep

/-- **`optionMatch` over a neutral SN scrutinee with reducible branches is a member of the result candidate.**
The cell is neutral (`IsNeutral.optionMatch`) and SN
(`optionMatch_neutralScrutinee_isStronglyNormalizing`, fed the branches' SN by CR1), so it inhabits the candidate
by the abstract neutral bridge. -/
theorem optionMatchNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {noneBranch someBranch : RawTerm scope}
    (noneBranchMember : resultCandidate noneBranch) (someBranchMember : resultCandidate someBranch) :
    resultCandidate (optionMatchCellSpine scrutinee noneBranch someBranch) :=
  candidate.memberOfStronglyNormalizingNeutral
    (optionMatch_neutralScrutinee_isStronglyNormalizing scrutineeStronglyNormalizing scrutineeNeutral
      (candidate.stronglyNormalizing noneBranchMember)
      (candidate.stronglyNormalizing someBranchMember))
    (IsNeutral.optionMatch scrutineeNeutral)

/-- **`eitherMatch` over a neutral SN scrutinee with reducible branches is a member of the result candidate** —
the Either twin of `optionMatchNeutralScrutineeMember`.  Completes the eliminator-neutral-coverage arc (all
twelve `IsNeutral` eliminators reducible over a neutral principal child). -/
theorem eitherMatchNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop) (candidate : IsReducibilityCandidate resultCandidate)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {leftBranch rightBranch : RawTerm scope}
    (leftBranchMember : resultCandidate leftBranch) (rightBranchMember : resultCandidate rightBranch) :
    resultCandidate (eitherMatchCellSpine scrutinee leftBranch rightBranch) :=
  candidate.memberOfStronglyNormalizingNeutral
    (eitherMatch_neutralScrutinee_isStronglyNormalizing scrutineeStronglyNormalizing scrutineeNeutral
      (candidate.stronglyNormalizing leftBranchMember)
      (candidate.stronglyNormalizing rightBranchMember))
    (IsNeutral.eitherMatch scrutineeNeutral)

end FX1Poly.Core
