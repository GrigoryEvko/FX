import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepCommute

/-! # FX1Poly/Core/NatElimSuccContractumReductionCongruence
    — the branch-side reduction congruences of the `natElim` cell + the succ-iota contractum
      reduction-congruence (the reduct-tracking SN engine's discharge ingredient for FTGEN-13.1)

The recursor-SN keystone (#1754) needs the `natElim` cell-SN engine to discharge its succ-iota firing
obligation WITHOUT the universally-false bare-SN premise (`succBranchSubstClosed` /
`succContractumTerminates`).  The genuine route: the cell-SN engine reaches the firing point with the
branches already STEPPED `(currentMotive, currentZero, currentSucc)` reachable from the originals; the
substituted contractum AT THE STEPPED BRANCHES is a REDUCT of the contractum at the ORIGINAL branches, so its
SN follows from the original contractum's SN (`IsStronglyNormalizing.descendStepStar`) — and that original
contractum SN comes from the genuine Tait MEMBERSHIP obligation the value-reducibility arm already carries
(`natElimValueReducibility.succReductMember`, SN-extracted by CR1), never from a false premise.

This file ships the "stepped contractum is a reduct of the original contractum" half: the reduction
congruence that lifts branch reduction chains through the succ-iota contractum.  It decomposes into:

  * `StepStar.natElimMotiveReduces` / `…ZeroBranchReduces` / `…SuccBranchReduces` — single-child congruences
    lifting a reduction chain in one branch through the whole `natElim` cell (the other three children + the
    scrutinee fixed).  The motive (`scope + 1`) and succ-branch (`scope + 2`) children are under binders, so
    these mirror `StepStar.lamBody`'s `StepChildren.here`/`there` drill rather than `StepStar.congAt` (which is
    same-scope).
  * `StepStar.natElimBranchesReduce` — all three branch chains composed: the cell with the scrutinee fixed
    reduces as its motive/zero/succ branches reduce.
  * `StepStar.natElimSuccContractumReduces` — the headline.  The Phase-Z succ-iota contractum
    `succBranch[var 0 := natElimCellSpine motive predecessor zeroBranch succBranch, var 1 := predecessor]`
    reduces to its branch-stepped image, assembling the cell-substituent chain (via
    `RawTermSubst.natSuccElim_cons_pointwiseStepStar` at a fixed predecessor) with the succ-branch body chain
    (`StepStar.subst`), composed exactly as the `Conv.substPair` recipe.

The `natRec` twin ships alongside (its succ-iota contractum has the identical 2-substituent cons shape, so it
reuses `RawTermSubst.natSuccElim_cons_pointwiseStepStar` verbatim).  The `listElim` twin is the follow-up brick
(its cons-iota contractum is a 3-substituent substitution — head, tail, recursive call — needing its own
pointwise lemma).

## Zero-axiom verification

`StepStar` induction (`refl`/`trans`) lifting each branch step by `Step.cong .gen_natElim …` through the
`StepChildren.here`/`there` spine drill, then `StepStar.trans_compose` / `StepStar.subst` /
`RawTerm.subst_pointwise_stepStar` composition.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

open FX1Poly.Axis.Syntax

/-- **Motive-position chain congruence for `natElim`.**  A reduction chain in the motive (the first,
binder-shifted `scope + 1` child) lifts to the whole `natElim` cell, the zero/succ branches + scrutinee fixed.
Mirrors `StepStar.lamBody`: each `Step.cong .gen_natElim …` fires `StepChildren.here` at the head child. -/
theorem natElimMotiveReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct) :
    StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
      (natElimCellSpine motiveReduct scrutinee zeroBranch succBranch) := by
  induction motiveChain with
  | refl _ => exact StepStar.refl _
  | trans motiveHeadStep _ motiveTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natElim ()
          (StepChildren.here _ motiveHeadStep))
        motiveTailCongruence

/-- **Zero-branch-position chain congruence for `natElim`.**  A reduction chain in the zero branch (the
second, base-scope child) lifts to the whole cell, the motive/succ branch + scrutinee fixed.  The drill walks
past the motive (`there`) then fires `here` at the zero branch. -/
theorem natElimZeroBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct) :
    StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
      (natElimCellSpine motive scrutinee zeroBranchReduct succBranch) := by
  induction zeroBranchChain with
  | refl _ => exact StepStar.refl _
  | trans zeroHeadStep _ zeroTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natElim ()
          (StepChildren.there _
            (StepChildren.here _ zeroHeadStep)))
        zeroTailCongruence

/-- **Succ-branch-position chain congruence for `natElim`.**  A reduction chain in the succ branch (the third,
binder-shifted `scope + 2` child) lifts to the whole cell, the motive/zero branch + scrutinee fixed.  The drill
walks past the motive and zero branch (`there`, `there`) then fires `here` at the succ branch. -/
theorem natElimSuccBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
      (natElimCellSpine motive scrutinee zeroBranch succBranchReduct) := by
  induction succBranchChain with
  | refl _ => exact StepStar.refl _
  | trans succHeadStep _ succTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natElim ()
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ succHeadStep))))
        succTailCongruence

/-- **The `natElim` cell reduces as its branches reduce (scrutinee fixed).**  Composes the three single-branch
congruences in sequence — motive first, then zero branch at the reduced motive, then succ branch at the reduced
motive + zero branch — via `StepStar.trans_compose`.  This is the cell-substituent chain the succ-iota
contractum congruence threads (with the scrutinee instantiated to the firing predecessor). -/
theorem natElimBranchesReduce {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {scrutinee zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct)
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct)
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar (natElimCellSpine motive scrutinee zeroBranch succBranch)
      (natElimCellSpine motiveReduct scrutinee zeroBranchReduct succBranchReduct) :=
  StepStar.trans_compose
    (natElimMotiveReduces motiveChain)
    (StepStar.trans_compose
      (natElimZeroBranchReduces zeroBranchChain)
      (natElimSuccBranchReduces succBranchChain))

/-- **★ The Phase-Z succ-iota contractum reduces as the branches reduce.**  The contractum
`succBranch[var 0 := natElimCellSpine motive predecessor zeroBranch succBranch, var 1 := predecessor]`
reduces to its branch-stepped image when the motive/zero/succ branches reduce (the firing predecessor fixed):
the consed substituent steps pointwise (`RawTermSubst.natSuccElim_cons_pointwiseStepStar` carries the recursive
cell's chain at a `refl` predecessor) and the body succ branch steps (`StepStar.subst`), composed by
`StepStar.trans_compose` — the `Conv.substPair` recipe.  This makes the contractum at any branch-reduced
`(motiveReduct, zeroBranchReduct, succBranchReduct)` a REDUCT of the contractum at the originals, so its SN
follows from the original contractum's SN — the discharge the reduct-tracking cell-SN engine needs to retire the
false `succBranchSubstClosed` / `succContractumTerminates` premise. -/
theorem natElimSuccContractumReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {predecessor zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct)
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct)
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar
      (RawTerm.subst
        (RawTermSubst.cons
          (natElimCellSpine motive predecessor zeroBranch succBranch)
          (RawTermSubst.singleton predecessor))
        succBranch)
      (RawTerm.subst
        (RawTermSubst.cons
          (natElimCellSpine motiveReduct predecessor zeroBranchReduct succBranchReduct)
          (RawTermSubst.singleton predecessor))
        succBranchReduct) :=
  StepStar.trans_compose
    (StepStar.subst
      (RawTermSubst.cons
        (natElimCellSpine motive predecessor zeroBranch succBranch)
        (RawTermSubst.singleton predecessor))
      succBranchChain)
    (RawTerm.subst_pointwise_stepStar
      (RawTermSubst.natSuccElim_cons_pointwiseStepStar
        (natElimBranchesReduce motiveChain zeroBranchChain succBranchChain)
        (StepStar.refl predecessor))
      succBranchReduct)

/-- **Motive-position chain congruence for `natRec`** — the `gen_natRec` twin of `natElimMotiveReduces`. -/
theorem natRecMotiveReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct) :
    StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch)
      (natRecCellSpine motiveReduct scrutinee zeroBranch succBranch) := by
  induction motiveChain with
  | refl _ => exact StepStar.refl _
  | trans motiveHeadStep _ motiveTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natRec ()
          (StepChildren.here _ motiveHeadStep))
        motiveTailCongruence

/-- **Zero-branch-position chain congruence for `natRec`** — the `gen_natRec` twin of
`natElimZeroBranchReduces`. -/
theorem natRecZeroBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct) :
    StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch)
      (natRecCellSpine motive scrutinee zeroBranchReduct succBranch) := by
  induction zeroBranchChain with
  | refl _ => exact StepStar.refl _
  | trans zeroHeadStep _ zeroTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natRec ()
          (StepChildren.there _
            (StepChildren.here _ zeroHeadStep)))
        zeroTailCongruence

/-- **Succ-branch-position chain congruence for `natRec`** — the `gen_natRec` twin of
`natElimSuccBranchReduces`. -/
theorem natRecSuccBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch)
      (natRecCellSpine motive scrutinee zeroBranch succBranchReduct) := by
  induction succBranchChain with
  | refl _ => exact StepStar.refl _
  | trans succHeadStep _ succTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_natRec ()
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ succHeadStep))))
        succTailCongruence

/-- **The `natRec` cell reduces as its branches reduce (scrutinee fixed)** — the `gen_natRec` twin of
`natElimBranchesReduce`. -/
theorem natRecBranchesReduce {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {scrutinee zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct)
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct)
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar (natRecCellSpine motive scrutinee zeroBranch succBranch)
      (natRecCellSpine motiveReduct scrutinee zeroBranchReduct succBranchReduct) :=
  StepStar.trans_compose
    (natRecMotiveReduces motiveChain)
    (StepStar.trans_compose
      (natRecZeroBranchReduces zeroBranchChain)
      (natRecSuccBranchReduces succBranchChain))

/-- **★ The Phase-Z `natRec` succ-iota contractum reduces as the branches reduce** — the `gen_natRec` twin of
`natElimSuccContractumReduces`.  The `natRec` succ-iota contractum has the identical 2-substituent cons shape
(`cons (natRecCellSpine …) (singleton predecessor)`), so the same `RawTermSubst.natSuccElim_cons_pointwiseStepStar`
(generator-agnostic — it threads the recursive cell as the position-0 substituent) assembles the reduction. -/
theorem natRecSuccContractumReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {predecessor zeroBranch zeroBranchReduct : RawTerm scope}
    {succBranch succBranchReduct : RawTerm (scope + 2)}
    (motiveChain : StepStar motive motiveReduct)
    (zeroBranchChain : StepStar zeroBranch zeroBranchReduct)
    (succBranchChain : StepStar succBranch succBranchReduct) :
    StepStar
      (RawTerm.subst
        (RawTermSubst.cons
          (natRecCellSpine motive predecessor zeroBranch succBranch)
          (RawTermSubst.singleton predecessor))
        succBranch)
      (RawTerm.subst
        (RawTermSubst.cons
          (natRecCellSpine motiveReduct predecessor zeroBranchReduct succBranchReduct)
          (RawTermSubst.singleton predecessor))
        succBranchReduct) :=
  StepStar.trans_compose
    (StepStar.subst
      (RawTermSubst.cons
        (natRecCellSpine motive predecessor zeroBranch succBranch)
        (RawTermSubst.singleton predecessor))
      succBranchChain)
    (RawTerm.subst_pointwise_stepStar
      (RawTermSubst.natSuccElim_cons_pointwiseStepStar
        (natRecBranchesReduce motiveChain zeroBranchChain succBranchChain)
        (StepStar.refl predecessor))
      succBranchReduct)

end StepStar
end FX1Poly.Core
