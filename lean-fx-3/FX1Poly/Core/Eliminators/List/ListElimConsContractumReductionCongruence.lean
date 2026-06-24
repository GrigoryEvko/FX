import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember
import FX1Poly.Core.Rewriting.Reduction.Step.StepStar

/-! # FX1Poly/Core/ListElimConsContractumReductionCongruence
    — the branch-side reduction congruences of the `listElim` cell + the cons-iota contractum
      reduction-congruence (the `listElim` twin of the nat recursor congruences)

The recursor strong-normalization keystone needs each recursive eliminator's cell-SN engine to discharge its
iota firing obligation WITHOUT a universally-false bare-SN premise.  The genuine route threads reachability: the
cell-SN engine reaches the firing point with the branches already STEPPED, reachable from the originals; the
firing contractum at the stepped branches is a REDUCT of the contractum at the original branches, so its SN
follows from the original contractum's SN (`IsStronglyNormalizing.descendStepStar`), itself the CR1 shadow of the
Tait membership obligation the value-reducibility arm already carries.

This file ships the "stepped contractum is a reduct of the original contractum" half for `listElim`.  Unlike the
nat recursors — whose succ-iota contractum is a 2-substituent SUBSTITUTION
(`succBranch[var 0 := recursive cell, var 1 := predecessor]`) — the `listElim` cons-iota contractum is an
APP-CHAIN, never a substitution:

  `app (app (app consBranch head) tail) (listElim motive nilBranch consBranch tail)`

so the assembly uses `StepStar.appFunction` / `StepStar.appArgument` over the four positions rather than the
nat `RawTerm.subst_pointwise_stepStar` recipe — no pointwise-substitution lemma is needed.  The decomposition:

  * `StepStar.listElimMotiveReduces` / `…NilBranchReduces` / `…ConsBranchReduces` — single-child congruences
    lifting a reduction chain in one branch through the whole `listElim` cell (the other branches + scrutinee
    fixed).  The motive (`scope + 1`) is under one binder; the two branches and scrutinee are base-scope (the
    cons branch is applied in the contractum, not substituted under binders).  Each fires `Step.cong .gen_listElim`
    over the `StepChildren.here`/`there` spine drill, exactly as the nat congruences do.
  * `StepStar.listElimBranchesReduce` — all three branch chains composed (scrutinee fixed).
  * `StepStar.listElimConsContractumReduces` — the headline.  The cons-iota contractum reduces to its
    branch-stepped image (the firing `head`/`tail` fixed): the cons branch reduces through the three nested
    application function-positions (`appFunction` thrice), and the recursive call reduces through the outer
    application argument-position (`appArgument` over `listElimBranchesReduce`, the recursive scrutinee `tail`
    fixed) — composed by `StepStar.trans_compose`.  This makes the contractum at any branch-reduced
    `(motiveReduct, nilBranchReduct, consBranchReduct)` a REDUCT of the contractum at the originals, the discharge
    the reduct-tracking cell-SN engine needs to retire the false bare-SN firing premise.

## Zero-axiom verification

`StepStar` induction (`refl`/`trans`) lifting each branch step by `Step.cong .gen_listElim …` through the
`StepChildren.here`/`there` spine drill, then `StepStar.trans_compose` / `StepStar.appFunction` /
`StepStar.appArgument` composition.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
namespace StepStar

open FX1Poly.Tier0.Syntax

/-- **Motive-position chain congruence for `listElim`.**  A reduction chain in the motive (the first,
binder-shifted `scope + 1` child) lifts to the whole `listElim` cell, the nil/cons branches + scrutinee fixed.
Each `Step.cong .gen_listElim …` fires `StepChildren.here` at the head child. -/
theorem listElimMotiveReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveChain : StepStar motive motiveReduct) :
    StepStar (listElimCellSpine motive scrutinee nilBranch consBranch)
      (listElimCellSpine motiveReduct scrutinee nilBranch consBranch) := by
  induction motiveChain with
  | refl _ => exact StepStar.refl _
  | trans motiveHeadStep _ motiveTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_listElim ()
          (StepChildren.here _ motiveHeadStep))
        motiveTailCongruence

/-- **Nil-branch-position chain congruence for `listElim`.**  A reduction chain in the nil branch (the second,
base-scope child) lifts to the whole cell, the motive/cons branch + scrutinee fixed.  The drill walks past the
motive (`there`) then fires `here` at the nil branch. -/
theorem listElimNilBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch nilBranchReduct consBranch : RawTerm scope}
    (nilBranchChain : StepStar nilBranch nilBranchReduct) :
    StepStar (listElimCellSpine motive scrutinee nilBranch consBranch)
      (listElimCellSpine motive scrutinee nilBranchReduct consBranch) := by
  induction nilBranchChain with
  | refl _ => exact StepStar.refl _
  | trans nilHeadStep _ nilTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_listElim ()
          (StepChildren.there _
            (StepChildren.here _ nilHeadStep)))
        nilTailCongruence

/-- **Cons-branch-position chain congruence for `listElim`.**  A reduction chain in the cons branch (the third,
base-scope child) lifts to the whole cell, the motive/nil branch + scrutinee fixed.  The drill walks past the
motive and nil branch (`there`, `there`) then fires `here` at the cons branch. -/
theorem listElimConsBranchReduces {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch consBranchReduct : RawTerm scope}
    (consBranchChain : StepStar consBranch consBranchReduct) :
    StepStar (listElimCellSpine motive scrutinee nilBranch consBranch)
      (listElimCellSpine motive scrutinee nilBranch consBranchReduct) := by
  induction consBranchChain with
  | refl _ => exact StepStar.refl _
  | trans consHeadStep _ consTailCongruence =>
      exact StepStar.trans
        (Step.cong .gen_listElim ()
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ consHeadStep))))
        consTailCongruence

/-- **The `listElim` cell reduces as its branches reduce (scrutinee fixed).**  Composes the three single-branch
congruences in sequence — motive first, then nil branch at the reduced motive, then cons branch at the reduced
motive + nil branch — via `StepStar.trans_compose`.  This is the recursive-call chain the cons-iota contractum
congruence threads (with the scrutinee instantiated to the firing tail). -/
theorem listElimBranchesReduce {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {scrutinee nilBranch nilBranchReduct consBranch consBranchReduct : RawTerm scope}
    (motiveChain : StepStar motive motiveReduct)
    (nilBranchChain : StepStar nilBranch nilBranchReduct)
    (consBranchChain : StepStar consBranch consBranchReduct) :
    StepStar (listElimCellSpine motive scrutinee nilBranch consBranch)
      (listElimCellSpine motiveReduct scrutinee nilBranchReduct consBranchReduct) :=
  StepStar.trans_compose
    (listElimMotiveReduces motiveChain)
    (StepStar.trans_compose
      (listElimNilBranchReduces nilBranchChain)
      (listElimConsBranchReduces consBranchChain))

/-- **★ The cons-iota contractum reduces as the branches reduce.**  The cons-iota contractum
`app (app (app consBranch head) tail) (listElim motive nilBranch consBranch tail)` reduces to its branch-stepped
image when the motive/nil/cons branches reduce (the firing `head`/`tail` fixed): the cons branch reduces through
the three nested application function-positions (`StepStar.appFunction` thrice), then the recursive call reduces
through the outer application argument-position (`StepStar.appArgument` over `listElimBranchesReduce`, the
recursive scrutinee `tail` fixed) — composed by `StepStar.trans_compose`.  This makes the contractum at any
branch-reduced `(motiveReduct, nilBranchReduct, consBranchReduct)` a REDUCT of the contractum at the originals,
so its SN follows from the original contractum's SN — the discharge the reduct-tracking cell-SN engine needs to
retire the false bare-SN firing premise. -/
theorem listElimConsContractumReduces {scope : Nat}
    {motive motiveReduct : RawTerm (scope + 1)}
    {head tail nilBranch nilBranchReduct consBranch consBranchReduct : RawTerm scope}
    (motiveChain : StepStar motive motiveReduct)
    (nilBranchChain : StepStar nilBranch nilBranchReduct)
    (consBranchChain : StepStar consBranch consBranchReduct) :
    StepStar
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
              (.childCons tail .childNil)))
          (.childCons (listElimCellSpine motive tail nilBranch consBranch) .childNil)))
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons consBranchReduct (.childCons head .childNil)))
              (.childCons tail .childNil)))
          (.childCons (listElimCellSpine motiveReduct tail nilBranchReduct consBranchReduct) .childNil))) :=
  StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.appFunction consBranchChain)))
    (StepStar.appArgument _
      (listElimBranchesReduce motiveChain nilBranchChain consBranchChain))

end StepStar
end FX1Poly.Core
