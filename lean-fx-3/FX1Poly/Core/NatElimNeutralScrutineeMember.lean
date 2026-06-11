import FX1Poly.Core.ReducibilityCandidate
import FX1Poly.Core.NeutralStepClosure
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Core/NatElimNeutralScrutineeMember
    — the NEUTRAL-scrutinee regime of `natElim` / `natRec` recursor reducibility

`NatElimValueMember` discharges the VALUE-scrutinee regime of the Nat recursor: `natElim motive zeroBranch
succBranch numeral` lands in the result candidate.  This file ships the NEUTRAL-scrutinee regime.

The key structural fact: `gen_natElim` ι-fires only on a numeral scrutinee (`natZero` / `natSucc`).  A NEUTRAL
scrutinee is never a numeral and stays neutral under `Step` (`IsNeutral.closedUnderStep`), so the recursor cell
NEVER ι-fires — it reduces purely by congruence in its four children.  Hence `natElim` over a neutral
scrutinee is itself neutral (`IsNeutral.natElim`), and a neutral strongly-normalizing term inhabits EVERY
reducibility candidate by CR3 (`neutralExpansion`).  This is the dual of the value regime: there the recursor
COMPUTES into the SUBSTITUTED succ reduct; here it is STUCK at a neutral head and reducibility flows from the
neutral-closure of the candidate.  Because the cell STAYS neutral, the SUBSTITUTING succ-iota never enters this
regime — the neutral proof is entirely congruence + vacuity, NO substitution machinery.

Five results:

  * `IsReducibilityCandidate.memberOfStronglyNormalizingNeutral` — the abstract reusable bridge: a
    strongly-normalizing neutral term is a member of ANY reducibility candidate.  Well-founded recursion on the
    term's SN accessibility — at each term every reduct stays neutral (`IsNeutral.closedUnderStep`) and is
    SN-smaller, so the IH makes it a member, and CR3 (`neutralExpansion`) lifts membership back.  This
    generalizes `CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral` (which is fixed to the
    canonical-forms candidate) to every candidate; any stuck-eliminator member argument consumes it.
  * `IsNeutral.rootGenerator_ne_natZero` / `IsNeutral.rootGenerator_ne_natSucc` — a neutral term's head is
    never a numeral constructor (the ι-vacuity discriminators), uniform over the neutral family exactly as
    `IsNeutral.rootGenerator_ne_piTyCode`.
  * `natElim_neutralScrutinee_isStronglyNormalizing` / `natRec_…` — the recursor cell at a neutral SN scrutinee
    with SN motive and SN branches is SN: a FOUR-fold accessibility recursion (Phase-Z motive shape adds the
    motive child) over (scrutinee, motive, zeroBranch, succBranch) whose two ι-reduct cases are VACUOUS by
    neutrality (a neutral scrutinee is no numeral) and whose four congruence cases (motive, zero, succ,
    scrutinee) recurse.
  * `natElimNeutralScrutineeMember` / `natRec…` — the neutral arm: `natElim`/`natRec` over a neutral SN
    scrutinee with SN motive and reducible branches is a member of the result candidate, by the abstract neutral
    bridge on the cell SN + `IsNeutral.natElim`.

Fundamental-independent: the result candidate is a fixed candidate, this is the pure Tait neutral-eliminator
argument.  The remaining regime is the scrutinee-reduction outer recursion (a non-value non-neutral
scrutinee threading down to its numeral), shared with the closed-membership track.

## Zero-axiom verification

The abstract bridge is `Acc`-recursion + CR3 + `IsNeutral.closedUnderStep`.  The discriminators are `cases
neutral <;> Generator.noConfusion` (the shipped `rootGenerator_ne_piTyCode` pattern).  The cell-SN recursors are
a FOUR-fold `Acc.intro` over the motive + branch + scrutinee accessibilities with `Step.from_natElim` /
`from_natRec` dispatch; the ι cases are refuted by `congrArg RawTerm.rootGenerator` against the neutral
discriminators.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `natElim` cell — `gen_natElim` in the Phase-Z motive shape (arity 4, `binderShifts = [1, 0, 2, 0]`),
spelled exactly as `IsNeutral.natElim` and `Step.from_natElim` expect (motive FIRST under one binder, the
succ-branch under TWO binders, the scrutinee LAST). -/
abbrev natElimCellSpine {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- The `natRec` cell — `gen_natRec` in the Phase-Z motive shape (motive first, scrutinee last). -/
abbrev natRecCellSpine {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) : RawTerm scope :=
  .mkGen .gen_natRec ()
    (.childCons motive
      (.childCons zeroBranch
        (.childCons succBranch
          (.childCons scrutinee .childNil))))

/-- **A strongly-normalizing neutral term is a member of ANY reducibility candidate.**  Well-founded recursion
on the term's SN accessibility: each one-step reduct stays neutral (`IsNeutral.closedUnderStep`) and is
SN-smaller, so the inductive hypothesis makes it a member, and CR3 (`neutralExpansion`) lifts membership back to
the term.  The abstract generalization of `CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral` to every
candidate — the reusable bridge any stuck-eliminator (`app` / `fst` / `boolElim …` / `natElim …` over a neutral
head) reducibility argument consumes. -/
theorem IsReducibilityCandidate.memberOfStronglyNormalizingNeutral {scope : Nat}
    {predicate : RawTerm scope → Prop} (candidate : IsReducibilityCandidate predicate)
    {term : RawTerm scope} (termStronglyNormalizing : IsStronglyNormalizing term)
    (termNeutral : IsNeutral term) :
    predicate term := by
  revert termNeutral
  induction termStronglyNormalizing with
  | intro node _nodeAccessible inductiveHypothesis =>
      intro nodeNeutral
      exact candidate.neutralExpansion nodeNeutral
        (fun reduct stepToReduct =>
          inductiveHypothesis reduct stepToReduct (nodeNeutral.closedUnderStep stepToReduct))

/-- **A neutral term's head is never the `natZero` constructor.**  Every `IsNeutral` arm fixes the root to an
elimination generator (`gen_var`, `gen_app`, …, `gen_natElim`); casing the neutrality witness sends each arm's
`rootGenerator` to that concrete generator, refuted against `gen_natZero` by `Generator.noConfusion`.  One of
the two ι-vacuity discriminators (a neutral scrutinee is no numeral, so the recursor never fires). -/
theorem IsNeutral.rootGenerator_ne_natZero {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_natZero := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `natSucc` constructor** (the `natSucc` ι-vacuity discriminator, dual of
`rootGenerator_ne_natZero`). -/
theorem IsNeutral.rootGenerator_ne_natSucc {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_natSucc := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **`natElim` over a neutral SN scrutinee with SN motive and SN branches is strongly normalizing.**  A neutral
scrutinee is never a numeral and stays neutral under `Step`, so the recursor never ι-fires — the cell reduces
purely by congruence in its four children.  Phase-Z motive shape: a FOUR-fold accessibility recursion over
(scrutinee, motive, zeroBranch, succBranch): `Step.from_natElim`'s two ι cases are refuted by the neutrality
discriminators, and its four congruence cases recurse (the scrutinee step preserving neutrality via
`IsNeutral.closedUnderStep`). -/
theorem natElim_neutralScrutinee_isStronglyNormalizing {scope : Nat}
    {motive : RawTerm (scope + 1)} (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {scrutinee : RawTerm scope} (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchStronglyNormalizing : IsStronglyNormalizing zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  suffices aux :
    ∀ scrutinee : RawTerm scope, IsStronglyNormalizing scrutinee → IsNeutral scrutinee →
    ∀ motive : RawTerm (scope + 1), IsStronglyNormalizing motive →
    ∀ zeroBranch : RawTerm scope, IsStronglyNormalizing zeroBranch →
    ∀ succBranch : RawTerm (scope + 2), IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natElimCellSpine motive scrutinee zeroBranch succBranch) by
    exact aux scrutinee scrutineeStronglyNormalizing scrutineeNeutral motive
      motiveStronglyNormalizing zeroBranch zeroBranchStronglyNormalizing succBranch
      succBranchStronglyNormalizing
  clear motiveStronglyNormalizing scrutineeStronglyNormalizing scrutineeNeutral
    zeroBranchStronglyNormalizing succBranchStronglyNormalizing motive scrutinee zeroBranch succBranch
  intro scrutinee scrutineeStronglyNormalizing
  induction scrutineeStronglyNormalizing with
  | intro scrutineeNode _scrutineeAccessible scrutineeInductiveHypothesis =>
    intro scrutineeNeutral motive motiveStronglyNormalizing
    induction motiveStronglyNormalizing with
    | intro motiveNode _motiveAccessible motiveInductiveHypothesis =>
      intro zeroBranch zeroBranchStronglyNormalizing
      induction zeroBranchStronglyNormalizing with
      | intro zeroNode _zeroAccessible zeroInductiveHypothesis =>
        intro succBranch succBranchStronglyNormalizing
        induction succBranchStronglyNormalizing with
        | intro succNode succNodeAccessible succInductiveHypothesis =>
          apply Acc.intro
          intro target step
          rcases Step.from_natElim step with
            ⟨scrutineeIsZero, _⟩ |
            ⟨_predecessor, scrutineeIsSucc, _⟩ |
            ⟨motiveAfter, targetEquation, motiveStep⟩ |
            ⟨zeroAfter, targetEquation, zeroStep⟩ |
            ⟨succAfter, targetEquation, succStep⟩ |
            ⟨scrutineeAfter, targetEquation, scrutineeStep⟩
          · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsZero)
              scrutineeNeutral.rootGenerator_ne_natZero
          · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsSucc)
              scrutineeNeutral.rootGenerator_ne_natSucc
          · rw [targetEquation]
            exact motiveInductiveHypothesis motiveAfter motiveStep
              zeroNode (Acc.intro zeroNode _zeroAccessible)
              succNode (Acc.intro succNode succNodeAccessible)
          · rw [targetEquation]
            exact zeroInductiveHypothesis zeroAfter zeroStep succNode
              (Acc.intro succNode succNodeAccessible)
          · rw [targetEquation]
            exact succInductiveHypothesis succAfter succStep
          · rw [targetEquation]
            exact scrutineeInductiveHypothesis scrutineeAfter scrutineeStep
              (scrutineeNeutral.closedUnderStep scrutineeStep)
              motiveNode (Acc.intro motiveNode _motiveAccessible)
              zeroNode (Acc.intro zeroNode _zeroAccessible)
              succNode (Acc.intro succNode succNodeAccessible)

/-- **`natRec` over a neutral SN scrutinee with SN motive and SN branches is strongly normalizing** — the
dependent-recursor twin of `natElim_neutralScrutinee_isStronglyNormalizing` (same `Step.from_natRec` six-way
inversion, same FOUR-fold accessibility, same ι-vacuity by neutrality). -/
theorem natRec_neutralScrutinee_isStronglyNormalizing {scope : Nat}
    {motive : RawTerm (scope + 1)} (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {scrutinee : RawTerm scope} (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchStronglyNormalizing : IsStronglyNormalizing zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  suffices aux :
    ∀ scrutinee : RawTerm scope, IsStronglyNormalizing scrutinee → IsNeutral scrutinee →
    ∀ motive : RawTerm (scope + 1), IsStronglyNormalizing motive →
    ∀ zeroBranch : RawTerm scope, IsStronglyNormalizing zeroBranch →
    ∀ succBranch : RawTerm (scope + 2), IsStronglyNormalizing succBranch →
      IsStronglyNormalizing (natRecCellSpine motive scrutinee zeroBranch succBranch) by
    exact aux scrutinee scrutineeStronglyNormalizing scrutineeNeutral motive
      motiveStronglyNormalizing zeroBranch zeroBranchStronglyNormalizing succBranch
      succBranchStronglyNormalizing
  clear motiveStronglyNormalizing scrutineeStronglyNormalizing scrutineeNeutral
    zeroBranchStronglyNormalizing succBranchStronglyNormalizing motive scrutinee zeroBranch succBranch
  intro scrutinee scrutineeStronglyNormalizing
  induction scrutineeStronglyNormalizing with
  | intro scrutineeNode _scrutineeAccessible scrutineeInductiveHypothesis =>
    intro scrutineeNeutral motive motiveStronglyNormalizing
    induction motiveStronglyNormalizing with
    | intro motiveNode _motiveAccessible motiveInductiveHypothesis =>
      intro zeroBranch zeroBranchStronglyNormalizing
      induction zeroBranchStronglyNormalizing with
      | intro zeroNode _zeroAccessible zeroInductiveHypothesis =>
        intro succBranch succBranchStronglyNormalizing
        induction succBranchStronglyNormalizing with
        | intro succNode succNodeAccessible succInductiveHypothesis =>
          apply Acc.intro
          intro target step
          rcases Step.from_natRec step with
            ⟨scrutineeIsZero, _⟩ |
            ⟨_predecessor, scrutineeIsSucc, _⟩ |
            ⟨motiveAfter, targetEquation, motiveStep⟩ |
            ⟨zeroAfter, targetEquation, zeroStep⟩ |
            ⟨succAfter, targetEquation, succStep⟩ |
            ⟨scrutineeAfter, targetEquation, scrutineeStep⟩
          · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsZero)
              scrutineeNeutral.rootGenerator_ne_natZero
          · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsSucc)
              scrutineeNeutral.rootGenerator_ne_natSucc
          · rw [targetEquation]
            exact motiveInductiveHypothesis motiveAfter motiveStep
              zeroNode (Acc.intro zeroNode _zeroAccessible)
              succNode (Acc.intro succNode succNodeAccessible)
          · rw [targetEquation]
            exact zeroInductiveHypothesis zeroAfter zeroStep succNode
              (Acc.intro succNode succNodeAccessible)
          · rw [targetEquation]
            exact succInductiveHypothesis succAfter succStep
          · rw [targetEquation]
            exact scrutineeInductiveHypothesis scrutineeAfter scrutineeStep
              (scrutineeNeutral.closedUnderStep scrutineeStep)
              motiveNode (Acc.intro motiveNode _motiveAccessible)
              zeroNode (Acc.intro zeroNode _zeroAccessible)
              succNode (Acc.intro succNode succNodeAccessible)

/-- **Neutral regime: `natElim` over a neutral SN scrutinee with SN motive, a reducible zero-branch, and an SN
under-binder succ-branch is a member of the result candidate.**  The cell is neutral (`IsNeutral.natElim`) and
strongly normalizing (`natElim_neutralScrutinee_isStronglyNormalizing`, fed the zero-branch's SN by CR1 and the
succ-branch's SN directly — the succ-branch lives at `scope + 2` so it cannot be a candidate member, only SN), so
it inhabits the candidate by the abstract neutral bridge.  The dual of `natElimValueMember`: there the recursor
COMPUTES into a member; here it is stuck at a neutral head and reducibility is the candidate's neutral closure. -/
theorem natElimNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidate : IsReducibilityCandidate resultCandidate)
    {motive : RawTerm (scope + 1)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch) :
    resultCandidate (natElimCellSpine motive scrutinee zeroBranch succBranch) :=
  candidate.memberOfStronglyNormalizingNeutral
    (natElim_neutralScrutinee_isStronglyNormalizing motiveStronglyNormalizing
      scrutineeStronglyNormalizing scrutineeNeutral
      (candidate.stronglyNormalizing zeroBranchMember)
      succBranchStronglyNormalizing)
    (IsNeutral.natElim scrutineeNeutral)

/-- **Neutral regime for `natRec`** — the dependent-recursor twin of `natElimNeutralScrutineeMember`. -/
theorem natRecNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidate : IsReducibilityCandidate resultCandidate)
    {motive : RawTerm (scope + 1)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch) :
    resultCandidate (natRecCellSpine motive scrutinee zeroBranch succBranch) :=
  candidate.memberOfStronglyNormalizingNeutral
    (natRec_neutralScrutinee_isStronglyNormalizing motiveStronglyNormalizing
      scrutineeStronglyNormalizing scrutineeNeutral
      (candidate.stronglyNormalizing zeroBranchMember)
      succBranchStronglyNormalizing)
    (IsNeutral.natRec scrutineeNeutral)

end FX1Poly.Core
