import FX1Poly.Core.NatElimNeutralScrutineeMember

/-! # FX1Poly/Core/ListElimNeutralScrutineeMember
    — the NEUTRAL-scrutinee regime of `listElim` recursor reducibility (toward SN-064)

The `listElim` mirror of `NatElimNeutralScrutineeMember`.  `ListElimValueReducibility` / `listElimValueMember`
(#733) discharged the VALUE-scrutinee regime of the List recursor (`listElim value nilBranch consBranch` lands
in the result candidate by `IsListValue` structural induction).  This file ships the NEUTRAL-scrutinee regime,
bringing the three RECURSIVE recursors (`natElim`, `natRec`, `listElim`) to neutral-coverage parity.

The structural fact is identical to the Nat recursor's: `gen_listElim` ι-fires only on a constructor scrutinee
(`listNil` / `listCons`).  A NEUTRAL scrutinee is never a constructor and stays neutral under `Step`
(`IsNeutral.closedUnderStep`), so the recursor NEVER ι-fires — it reduces purely by congruence in its three
children.  Hence `listElim` over a neutral scrutinee is neutral (`IsNeutral.listElim`) and a strongly-normalizing
neutral inhabits EVERY reducibility candidate by CR3 (the reusable
`IsReducibilityCandidate.memberOfStronglyNormalizingNeutral`, shipped with the Nat regime).

Four results:

  * `IsNeutral.rootGenerator_ne_listNil` / `IsNeutral.rootGenerator_ne_listCons` — a neutral term's head is never
    a List constructor (the ι-vacuity discriminators), uniform over the neutral family exactly as
    `IsNeutral.rootGenerator_ne_natZero`.
  * `listElim_neutralScrutinee_isStronglyNormalizing` — the recursor cell at a neutral SN scrutinee with SN
    branches is SN, by a triple accessibility recursion whose two ι-reduct cases are VACUOUS by neutrality and
    whose three congruence cases recurse.
  * `listElimNeutralScrutineeMember` — the SN-064 neutral arm: `listElim` over a neutral SN scrutinee with
    reducible branches is a member of the result candidate, via the abstract neutral bridge + `IsNeutral.listElim`.

`#672`-independent (fixed result candidate, the pure Tait neutral-eliminator argument).  The remaining
scrutinee-reduction regime is the shared recursor outer-recursion (a non-value non-neutral scrutinee threading
down to its List value), the List twin of the Nat residual.

## Zero-axiom verification

The discriminators are `cases neutral <;> Generator.noConfusion`; the cell-SN recursor is a triple `Acc.intro`
over the branch + scrutinee accessibilities with `Step.from_listElim` dispatch (its `listNil` / `listCons` ι
cases refuted by `congrArg RawTerm.rootGenerator` against the neutral discriminators); the member arm composes
them through `IsReducibilityCandidate.memberOfStronglyNormalizingNeutral`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The `listElim` cell over its (scrutinee, nilBranch, consBranch) spine, spelled exactly as
`IsNeutral.listElim` and `Step.from_listElim` expect. -/
abbrev listElimCellSpine {scope : Nat} (scrutinee nilBranch consBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_listElim ()
    (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))

/-- **A neutral term's head is never the `listNil` constructor.**  Casing the neutrality witness sends each
arm's `rootGenerator` to its concrete elimination generator, refuted against `gen_listNil` by
`Generator.noConfusion`.  One of the two List ι-vacuity discriminators (a neutral scrutinee is no List
constructor, so the recursor never fires). -/
theorem IsNeutral.rootGenerator_ne_listNil {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_listNil := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **A neutral term's head is never the `listCons` constructor** (the `listCons` ι-vacuity discriminator, dual
of `rootGenerator_ne_listNil`). -/
theorem IsNeutral.rootGenerator_ne_listCons {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_listCons := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **`listElim` over a neutral SN scrutinee with SN branches is strongly normalizing.**  A neutral scrutinee is
never a List constructor and stays neutral under `Step`, so the recursor never ι-fires — the cell reduces purely
by congruence in its three children.  A triple accessibility recursion over (scrutinee, nilBranch, consBranch):
`Step.from_listElim`'s two ι cases are refuted by the neutrality discriminators, and its three congruence cases
recurse (the scrutinee step preserving neutrality via `IsNeutral.closedUnderStep`). -/
theorem listElim_neutralScrutinee_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope} (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {nilBranch consBranch : RawTerm scope}
    (nilBranchStronglyNormalizing : IsStronglyNormalizing nilBranch)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing (listElimCellSpine scrutinee nilBranch consBranch) := by
  suffices aux :
    ∀ scrutinee : RawTerm scope, IsStronglyNormalizing scrutinee → IsNeutral scrutinee →
    ∀ nilBranch : RawTerm scope, IsStronglyNormalizing nilBranch →
    ∀ consBranch : RawTerm scope, IsStronglyNormalizing consBranch →
      IsStronglyNormalizing (listElimCellSpine scrutinee nilBranch consBranch) by
    exact aux scrutinee scrutineeStronglyNormalizing scrutineeNeutral nilBranch
      nilBranchStronglyNormalizing consBranch consBranchStronglyNormalizing
  clear scrutineeStronglyNormalizing scrutineeNeutral nilBranchStronglyNormalizing
    consBranchStronglyNormalizing scrutinee nilBranch consBranch
  intro scrutinee scrutineeStronglyNormalizing
  induction scrutineeStronglyNormalizing with
  | intro scrutineeNode _scrutineeAccessible scrutineeInductiveHypothesis =>
    intro scrutineeNeutral nilBranch nilBranchStronglyNormalizing
    induction nilBranchStronglyNormalizing with
    | intro nilNode _nilAccessible nilInductiveHypothesis =>
      intro consBranch consBranchStronglyNormalizing
      induction consBranchStronglyNormalizing with
      | intro consNode consNodeAccessible consInductiveHypothesis =>
        apply Acc.intro
        intro target step
        rcases Step.from_listElim step with
          ⟨scrutineeIsNil, _⟩ |
          ⟨_headValue, _tailValue, scrutineeIsCons, _⟩ |
          ⟨scrutineeAfter, targetEquation, scrutineeStep⟩ |
          ⟨nilAfter, targetEquation, nilStep⟩ |
          ⟨consAfter, targetEquation, consStep⟩
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsNil)
            scrutineeNeutral.rootGenerator_ne_listNil
        · exact absurd (congrArg RawTerm.rootGenerator scrutineeIsCons)
            scrutineeNeutral.rootGenerator_ne_listCons
        · rw [targetEquation]
          exact scrutineeInductiveHypothesis scrutineeAfter scrutineeStep
            (scrutineeNeutral.closedUnderStep scrutineeStep)
            nilNode (Acc.intro nilNode _nilAccessible)
            consNode (Acc.intro consNode consNodeAccessible)
        · rw [targetEquation]
          exact nilInductiveHypothesis nilAfter nilStep consNode
            (Acc.intro consNode consNodeAccessible)
        · rw [targetEquation]
          exact consInductiveHypothesis consAfter consStep

/-- **SN-064 neutral regime: `listElim` over a neutral SN scrutinee with reducible branches is a member of the
result candidate.**  The cell is neutral (`IsNeutral.listElim`) and strongly normalizing
(`listElim_neutralScrutinee_isStronglyNormalizing`, fed the branches' SN by CR1), so it inhabits the candidate by
the abstract neutral bridge.  The List twin of `natElimNeutralScrutineeMember`. -/
theorem listElimNeutralScrutineeMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidate : IsReducibilityCandidate resultCandidate)
    {scrutinee : RawTerm scope}
    (scrutineeStronglyNormalizing : IsStronglyNormalizing scrutinee)
    (scrutineeNeutral : IsNeutral scrutinee)
    {nilBranch consBranch : RawTerm scope}
    (nilBranchMember : resultCandidate nilBranch) (consBranchMember : resultCandidate consBranch) :
    resultCandidate (listElimCellSpine scrutinee nilBranch consBranch) :=
  candidate.memberOfStronglyNormalizingNeutral
    (listElim_neutralScrutinee_isStronglyNormalizing scrutineeStronglyNormalizing scrutineeNeutral
      (candidate.stronglyNormalizing nilBranchMember)
      (candidate.stronglyNormalizing consBranchMember))
    (IsNeutral.listElim scrutineeNeutral)

end FX1Poly.Core
