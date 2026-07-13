import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapGeneralArms

/-! # MODE-COMMUTE r27 — the whole-cell fold GLUE: sim algebra, cell decomposition, atom dispatch

## What this ships

With all four general atom arms landed (`ArcDisjointAtomSwapGeneralArms` + the r25 cup engine), the
whole-cell disjoint-support commutation (`fxMode_hasDisjointWhiskerSupport`) reduces to the DOUBLE
FOLD `atomPastCell -> cellPastCell`.  This file ships the fold's algebraic glue — every reusable
piece of the induction that is independent of the window/component invariant threading:

  * `arcStepSimCount_refl` / `arcStepSimCount_comp` — the count-field simulation is reflexive (at
    the identity carrier) and composes along composed carriers.  Composition is what chains the
    pairwise atom swaps: `sim sigma1 (A, B')` and `sim sigma2 (B', B)` give
    `sim (sigma2 after sigma1) (A, B)` — the fold's transitivity spine.
  * `runArcCell_vcomp` / `runArcCell_whiskerLeft` / `runArcCell_whiskerRight` / `runArcCell_gen` —
    the cell-shape decomposition of the arc run: a vertical composite runs its two factors in
    sequence (via the shipped `processArcSpine_spineDiff`), a whiskering shifts the accumulator, a
    generator is one `stepArcAtom`.  These are the recursion equations of the cell induction.
  * `stepArcAtom_eq_stepCupArc` / `stepArcAtom_eq_stepCapArc` — the arity dispatch: an atom whose
    generator boundary is `0 => 2` IS a cup step at its left-context length, `2 => 0` a cap step.
    These connect the cell-level `runArcCell` recursion to the four general atom arms.

## The honest residual (named precisely, NOT flipped)

What remains for the whole-cell theorem, exactly: the DOUBLE INDUCTION threading (1) the window
geometry — each fired atom shifts the other cell's window by its arity delta (`+2` cup / `-2` cap),
produced by the whisker accumulators' path lengths; (2) the r27-sharpened component guard for
cap-bearing cells — the two windows' reads must stay component-disjoint through every intermediate
state (a preservation argument over `isSameComponent_twoJoinBlock_untouched`); (3) the base
dispatch of the four arms along `stepArcAtom_eq_step*Arc`.  The pins stay `false`; the fold is the
sole remaining delivery.

Raw Lean 4 + Init; term-mode field assembly and `rfl`-level decomposition equations.
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Map composition (propext-free, hand-rolled) -/

/-- Mapping twice is mapping the composite. -/
theorem mapComposition (sigmaFirst sigmaSecond : Nat → Nat) :
    (wires : List Nat) →
    (wires.map sigmaFirst).map sigmaSecond = wires.map (fun node => sigmaSecond (sigmaFirst node))
  | [] => rfl
  | headWire :: restWires => by
      show sigmaSecond (sigmaFirst headWire) :: (restWires.map sigmaFirst).map sigmaSecond
        = sigmaSecond (sigmaFirst headWire)
          :: restWires.map (fun node => sigmaSecond (sigmaFirst node))
      rw [mapComposition sigmaFirst sigmaSecond restWires]

/-! ## The simulation algebra — reflexivity and composition -/

/-- ★ **The count-field simulation is reflexive at the identity carrier** (over a forest).  The
base case of every fold: zero swaps performed, both orders literally equal. -/
theorem arcStepSimCount_refl (state : ArcWireState) (forest : isUnionFindForest state.links) :
    ArcStepSimCount (fun node => node) state state where
  openMap := (mapFixedOn (fun node => node) state.openWires (fun _ _ => rfl)).symm
  nfEq := rfl
  rootComm := fun _ => rfl
  loopsEq := rfl
  cupCorr := fun _ => rfl
  capCorr := fun _ => rfl
  forestS := forest
  forestT := forest

/-- ★ **The count-field simulation COMPOSES along composed carriers** — the transitivity spine of
the whole-cell fold: the pairwise atom swap gives `sim sigma1` to the once-transposed order, the
inductive hypothesis gives `sim sigma2` onward, and the composite carrier relates the endpoints. -/
theorem arcStepSimCount_comp (sigmaFirst sigmaSecond : Nat → Nat)
    (stateA stateB stateC : ArcWireState)
    (simFirst : ArcStepSimCount sigmaFirst stateA stateB)
    (simSecond : ArcStepSimCount sigmaSecond stateB stateC) :
    ArcStepSimCount (fun node => sigmaSecond (sigmaFirst node)) stateA stateC where
  openMap := by
    rw [simSecond.openMap, simFirst.openMap, mapComposition sigmaFirst sigmaSecond stateA.openWires]
  nfEq := simFirst.nfEq.trans simSecond.nfEq
  rootComm := fun node => by
    show unionFindRootOf stateC.links (sigmaSecond (sigmaFirst node))
      = sigmaSecond (sigmaFirst (unionFindRootOf stateA.links node))
    rw [simSecond.rootComm (sigmaFirst node), simFirst.rootComm node]
  loopsEq := simSecond.loopsEq.trans simFirst.loopsEq
  cupCorr := fun rootHere => by
    show countEventsInRoot stateC.links (sigmaSecond (sigmaFirst rootHere)) stateC.cupEventNodes
      = countEventsInRoot stateA.links rootHere stateA.cupEventNodes
    rw [simSecond.cupCorr (sigmaFirst rootHere), simFirst.cupCorr rootHere]
  capCorr := fun rootHere => by
    show countEventsInRoot stateC.links (sigmaSecond (sigmaFirst rootHere)) stateC.capEventNodes
      = countEventsInRoot stateA.links rootHere stateA.capEventNodes
    rw [simSecond.capCorr (sigmaFirst rootHere), simFirst.capCorr rootHere]
  forestS := simFirst.forestS
  forestT := simSecond.forestT

/-! ## The cell-shape decomposition of the arc run -/

/-- A vertical composite runs its factors in sequence — the vcomp recursion equation of the
whole-cell induction (via the shipped fold decomposition). -/
theorem runArcCell_vcomp {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {pathLow pathMid pathHigh : ModalityPath signature.graph localSource localTarget}
    (cellAlpha : RawTwoCellExpr signature pathLow pathMid)
    (cellBeta : RawTwoCellExpr signature pathMid pathHigh) :
    runArcCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = runArcCell (runArcCell state leftAcc rightAcc cellAlpha) leftAcc rightAcc cellBeta := by
  show processArcSpine state
      (cellAlpha.spineDiff leftAcc rightAcc (cellBeta.spineDiff leftAcc rightAcc []))
    = runArcCell (runArcCell state leftAcc rightAcc cellAlpha) leftAcc rightAcc cellBeta
  rw [processArcSpine_spineDiff leftAcc rightAcc cellAlpha state
    (cellBeta.spineDiff leftAcc rightAcc [])]
  rfl

/-- A left whiskering shifts the left accumulator — definitional. -/
theorem runArcCell_whiskerLeft {signature : ModeSignature}
    {overallSource overallTarget localSource middleMode localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    (oneCell : ModalityPath signature.graph localSource middleMode)
    {pathDom pathCod : ModalityPath signature.graph middleMode localTarget}
    (body : RawTwoCellExpr signature pathDom pathCod) :
    runArcCell state leftAcc rightAcc (RawTwoCellExpr.whiskerLeft oneCell body)
      = runArcCell state (composePath leftAcc oneCell) rightAcc body := rfl

/-- A right whiskering shifts the right accumulator — definitional. -/
theorem runArcCell_whiskerRight {signature : ModeSignature}
    {overallSource overallTarget localSource middleMode localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {pathDom pathCod : ModalityPath signature.graph localSource middleMode}
    (oneCell : ModalityPath signature.graph middleMode localTarget)
    (body : RawTwoCellExpr signature pathDom pathCod) :
    runArcCell state leftAcc rightAcc (RawTwoCellExpr.whiskerRight oneCell body)
      = runArcCell state leftAcc (composePath oneCell rightAcc) body := rfl

/-- A generator runs as ONE spine atom — definitional (the singleton fold). -/
theorem runArcCell_gen {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {pathDom pathCod : ModalityPath signature.graph localSource localTarget}
    (generator : signature.twoCell pathDom pathCod) :
    runArcCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)
      = stepArcAtom state
          (SpineAtom.mk localSource localTarget leftAcc pathDom pathCod generator rightAcc) := rfl

/-! ## The arity dispatch — SHIPPED

The dispatch of `stepArcAtom` onto `stepCupArc` / `stepCapArc` by generator arity is already
shipped (`stepArcAtom_eq_stepCupArc` / `stepArcAtom_eq_stepCapArc`,
`ArcGodementSoundnessPeelEmptyBoundary`); together with `runArcCell_gen` above it connects the
cell recursion to the four general atom arms. -/

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the whole-cell fold GLUE is SHIPPED.**  The simulation algebra
(`arcStepSimCount_refl` / `_comp`), the cell-shape decomposition of `runArcCell`
(vcomp / whiskerings / generator), and the arity dispatch onto the four general atom arms.
Together with the r24 bundle preservation + common-suffix extension and the r27 general arms,
every INGREDIENT of the `atomPastCell -> cellPastCell` double fold is now in place; the fold's
own induction (window geometry + component-guard threading) is the sole remaining delivery.
`= true`. -/
def fxMode_hasArcCellSwapFoldGlue : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN** (the double fold
itself).  `rfl`. -/
theorem arcCellSwapFoldGlue_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  `rfl`. -/
theorem arcCellSwapFoldGlue_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN.**  `rfl`. -/
theorem arcCellSwapFoldGlue_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcCellSwapFoldGlue_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
