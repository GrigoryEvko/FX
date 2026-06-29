import FX1Poly.Tier0.Mode.FreeTwoCellSpineTraceDecision

/-! # mode-3 floor — the Godement arc-extract independence, SHARPENED to the union-find partition core

`FreeTwoCellSpineTraceDecision` ships the full planar-arc invariant `arcStructureOf` and proves its FULL
`TwoCellConvFull` soundness ASSEMBLED modulo one residual: the state-parametric Godement-step invariance
`godementInvariant` — `extractArcAfterProcessing state redex = extractArcAfterProcessing state reduct` for every
`SpineGodementStep`.  That residual is the union-find INDEPENDENCE of two horizontally-disjoint blocks; its
honesty marker there is `fxMode_hasArcGodementIndependenceProof = false`.

This file discharges the FOLD-THREADING boilerplate AND the cup/cap COUNT fields, sharpening that residual to
ONLY the union-find PARTITION independence — exactly the boundary partner matching and the per-port internal
cup/cap arc data:

  ★ `runArcCell` / `processArcSpine_spineDiff` — the **fold-decomposition engine**: running the arc fold over a
    cons-only `spineDiff` difference-list equals running it over the cell alone (`runArcCell`) and then over the
    tail.  Pure structural recursion on the cell, definitional per arm, so it is `propext`/`Quot.sound`-free.
    This is the lemma that lets the fold peel one whiskered block at a time.
  ★ `ArcGodementCommute` + `arcGodementInvariant_of_commute` — the **two-block commutation core** and the
    reduction.  A `SpineGodementStep` transposes exactly two horizontally-disjoint middle blocks
    (`cellAlphaUpper` and `cellBeta`) with a context shift; `processArcSpine_spineDiff` peels the untouched outer
    blocks (`cellAlpha` prefix, `cellBetaUpper`) and the common tail, so the whole `godementInvariant` reduces
    to the bare statement that the two run orders of those two blocks produce an arc-EXTRACT-equal state.
  ★ the cup/cap COUNT fields DISCHARGED — `stepArcAtom_*EventNodes_length`, `processArcSpine_*EventNodes_length`,
    `runArcCell_*EventNodes_length`: the extract's `cupCount` / `capCount` fields are order-independent atom
    counts, so `arcGodementCommute_of_partitionCommute` proves them Godement-invariant unconditionally (the
    αUpper / β counts transpose by `Nat.add_right_comm`).
  ★ `ArcGodementPartitionCommute` + `arcStructureOf_sound_of_arcGodementPartitionCommute` — the residual
    SHARPENED to the three partition-determined fields (`diagram` = partner matching + loops + port counts;
    `internalCupCounts`; `internalCapCounts`), and the full `TwoCellConvFull` soundness of `arcStructureOf`
    re-gated on THAT alone.  Both the fold-threading AND the cup/cap counts are discharged.

## What is honest-DEFERRED (the SHARPENED residual)

`ArcGodementPartitionCommute` — `fxMode_hasArcPartitionCommuteProof = false`.  The union-find PARTITION
independence: transposing the two horizontally-disjoint blocks preserves the connected components the extract
reads off (the boundary partner matching, the loop count, the per-port internal cup/cap counts).  TRUE (disjoint
port-support merge sequences induce the same partition up to the fresh-id renaming) and computationally confirmed
on every obstruction witness; its general zero-axiom proof (a partition-isomorphism simulation between the two
run orders) is the one remaining soundness obligation, shared with the matching route's
`fxMode_hasMatchingGodementIndependenceProof`.  This is exactly the parent's "partner + internalCupCounts"
component — the cup/cap COUNT component is discharged here.

Raw Lean 4 + Init; the fold-decomposition / count lemmas are definitional structural recursion (no `omega` /
`simp`-AC / `WellFounded.fix` / `List.append`; the only arithmetic is `Nat.add_assoc` / `Nat.add_right_comm`),
the reductions are `cases` on the single Godement constructor.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Tier0

/-! ## The fold-decomposition engine -/

/-- Run the arc fold over ONE cell's spine from a given state (the cell's contribution alone, with an empty
tail).  Reading a `spineDiff` block off the fold reduces, via `processArcSpine_spineDiff`, to threading
`runArcCell` for each block. -/
def runArcCell {signature : ModeSignature} {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) : ArcWireState :=
  processArcSpine state (cell.spineDiff leftAcc rightAcc [])

/-- ★ **The fold-decomposition of the arc spine fold over a `spineDiff` difference-list.**  Folding the per-atom
arc step over `cell.spineDiff leftAcc rightAcc rest` equals folding it over the cell alone (`runArcCell`) and
then over `rest`.  By structural recursion on `cell`: a generator / identity reduce definitionally (`foldl` on a
singleton / on `[]`), a vertical composite peels each factor in turn (the inductive hypothesis applied to
`cellLeft` over the tail `cellRight.spineDiff … rest`, then to `cellRight`), and the two whiskerings recurse
under the shifted accumulators.  Cons-only difference lists keep it `List.append`-free, hence propext-free. -/
theorem processArcSpine_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : ArcWireState) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    processArcSpine state (cell.spineDiff leftAcc rightAcc rest)
      = processArcSpine (runArcCell state leftAcc rightAcc cell) rest
  | _, _, _, _, _, _, .gen _, _, _ => rfl
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, state, rest => by
      show processArcSpine state
          (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc rest))
        = processArcSpine (runArcCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)) rest
      rw [processArcSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc rest),
        processArcSpine_spineDiff leftAcc rightAcc cellRight (runArcCell state leftAcc rightAcc cellLeft) rest]
      congr 1
      show runArcCell (runArcCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight
        = processArcSpine state (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc []))
      rw [processArcSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])]
      rfl
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, state, rest =>
      processArcSpine_spineDiff (composePath leftAcc oneCell) rightAcc body state rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, state, rest =>
      processArcSpine_spineDiff leftAcc (composePath oneCell rightAcc) body state rest

/-! ## The two-block commutation core — the residual, SHARPENED -/

/-- ★ **The two-block commutation core** — the Godement arc residual with the fold-threading discharged.  A
`SpineGodementStep` transposes the two horizontally-disjoint middle blocks `cellAlphaUpper` (right context
`gLow → gMid`) and `cellBeta` (left context `fHigh → fMid`); `cellAlpha` (the prefix) and `cellBetaUpper` (the
suffix) are untouched.  `processArcSpine_spineDiff` peels all four blocks, so the entire `godementInvariant`
reduces to THIS: the two run orders of `cellAlphaUpper` and `cellBeta` — run after the common `cellAlpha`
prefix, before the common `cellBetaUpper` suffix and the common `rest` — extract to the SAME `FullArcStructure`
from EVERY starting state.  This is the genuine Mazurkiewicz independence (disjoint-support merge sequences
commute up to the fresh-id renaming the extract reads through); the LHS runs `αUpper` then `β`, the RHS `β`
then `αUpper`, and the four context shifts (`gLow`/`gMid`, `fHigh`/`fMid`) are exactly the constructor's. -/
def ArcGodementCommute (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : ArcWireState),
    extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      = extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-! ## The reduction: the two-block core IMPLIES the parent's full Godement residual -/

/-- ★ **The reduction.**  The two-block commutation core `ArcGodementCommute` implies the parent's full
state-parametric Godement-step invariance (`godementInvariant`'s shape) — with NOTHING else owed.  By `cases` on
the single `SpineGodementStep.godement` constructor (its redex / reduct spines are the four-block nested
`spineDiff` forms) followed by four `processArcSpine_spineDiff` peels on each side, both sides land EXACTLY on
`ArcGodementCommute`'s two run-order states.  The fold-threading and the common prefix/tail are thereby
discharged; the bare αUpper↔β disjoint commutation is all that the core supplies. -/
theorem arcGodementInvariant_of_commute {signature : ModeSignature}
    (commute : ArcGodementCommute signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : ArcWireState)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractArcAfterProcessing bottomCount state firstList
      = extractArcAfterProcessing bottomCount state secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [extractArcAfterProcessing, processArcSpine_spineDiff]
    exact commute cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state

/-- ★ **`arcStructureOf` soundness under the COMPLETE `TwoCellConvFull`, gated on the two-block core alone.**
Composing the reduction `arcGodementInvariant_of_commute` with the parent's
`arcStructureOf_sound_of_godementInvariant`: given only `ArcGodementCommute` (the αUpper↔β disjoint commutation),
`arcStructureOf` is invariant under every structural law, all whisker functoriality, every congruence, and the
interchange step.  The soundness residual is now exactly the two-block commutation core — the fold-threading
that the parent's residual still carried is discharged. -/
theorem arcStructureOf_sound_of_arcGodementCommute {signature : ModeSignature}
    (commute : ArcGodementCommute signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcStructureOf_sound_of_godementInvariant (arcGodementInvariant_of_commute commute) convFull

/-! ## Honesty markers -/

/-- **Honesty marker — the Godement arc residual's fold-threading is DISCHARGED.**  `processArcSpine_spineDiff`
proves the arc fold decomposes over the cons-only `spineDiff` difference-list (`runArcCell` per block), so the
four whiskered blocks of a `SpineGodementStep` peel off unconditionally and `propext`-free.  This is the
structural half of the parent's `godementInvariant`.  `= true`. -/
def fxMode_hasArcGodementFoldDecomposition : Bool := true

/-- **Honesty marker — the Godement arc residual is REDUCED to the two-block commutation core.**
`arcGodementInvariant_of_commute` proves the parent's full state-parametric `godementInvariant` from
`ArcGodementCommute` alone, and `arcStructureOf_sound_of_arcGodementCommute` re-gates the entire
`TwoCellConvFull` soundness of `arcStructureOf` on that single core.  The residual is strictly smaller than the
parent's: the four-fold fold-threading and the common prefix/suffix are discharged; only the bare αUpper↔β
disjoint-support commutation remains.  `= true`. -/
def fxMode_hasArcGodementReducedToBlockCommute : Bool := true

/-- **Honesty marker — the full two-block EXTRACT commutation is not proven directly.**  `ArcGodementCommute`
states that transposing the two horizontally-disjoint middle blocks `cellAlphaUpper` / `cellBeta` (with their
context shifts) preserves the WHOLE arc extract from every state.  It is NOT proven outright here; below it is
FURTHER reduced (`arcGodementCommute_of_partitionCommute`) to the strictly smaller partition core, the cup/cap
count fields discharged — so the genuine standing obligation is `fxMode_hasArcPartitionCommuteProof`, not this.
TRUE (the blocks act on disjoint port-sets) and computationally confirmed on the obstruction witnesses
(`parallelUnits_cupCount_eq` / `parallelCounits_capCount_eq`, the matching route's `parallelUnits_matchingOf_eq`).
`= false`. -/
def fxMode_hasArcBlockCommuteProof : Bool := false

/-! ## The cup / cap COUNT fields are unconditionally Godement-invariant — discharging two of five fields

The extract's `cupCount` / `capCount` fields are `state.cupEventNodes.length` / `state.capEventNodes.length`
after processing — the COUNT of cup / cap atoms, which is order-INDEPENDENT (a Godement step only permutes the
atoms).  So these two fields of `ArcGodementCommute` are discharged unconditionally, leaving only the three
partition-determined fields (`diagram`, `internalCupCounts`, `internalCapCounts`) as the genuine residual. -/

/-- One arc step changes the cup-event-node count by exactly one (for a CUP atom, arity `0 ⇒ 2`) or zero (every
other atom).  By cases on the generator's boundary lengths mirroring `stepArcAtom`'s match; each leaf is `rfl`
(a `0 ⇒ 2` conses one cup event, the cap / box branches leave `cupEventNodes` untouched, and `Nat.add … 0`
reduces definitionally). -/
theorem stepArcAtom_cupEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepArcAtom state atom).cupEventNodes.length
      = state.cupEventNodes.length
        + (if atom.generatorDom.length == 0 && atom.generatorCod.length == 2 then 1 else 0) := by
  unfold stepArcAtom
  generalize atom.generatorDom.length = domLen
  generalize atom.generatorCod.length = codLen
  cases domLen with
  | zero =>
    cases codLen with
    | zero => rfl
    | succ codLenPred =>
      cases codLenPred with
      | zero => rfl
      | succ codLenPredPred =>
        cases codLenPredPred with
        | zero => rfl
        | succ _ => rfl
  | succ domLenPred =>
    cases domLenPred with
    | zero => rfl
    | succ domLenPredPred =>
      cases domLenPredPred with
      | zero =>
        cases codLen with
        | zero => rfl
        | succ _ => rfl
      | succ _ => rfl

/-- One arc step changes the cap-event-node count by exactly one (for a CAP atom, arity `2 ⇒ 0`) or zero.  The
dual of `stepArcAtom_cupEventNodes_length`. -/
theorem stepArcAtom_capEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepArcAtom state atom).capEventNodes.length
      = state.capEventNodes.length
        + (if atom.generatorDom.length == 2 && atom.generatorCod.length == 0 then 1 else 0) := by
  unfold stepArcAtom
  generalize atom.generatorDom.length = domLen
  generalize atom.generatorCod.length = codLen
  cases domLen with
  | zero =>
    cases codLen with
    | zero => rfl
    | succ codLenPred =>
      cases codLenPred with
      | zero => rfl
      | succ codLenPredPred =>
        cases codLenPredPred with
        | zero => rfl
        | succ _ => rfl
  | succ domLenPred =>
    cases domLenPred with
    | zero => rfl
    | succ domLenPredPred =>
      cases domLenPredPred with
      | zero =>
        cases codLen with
        | zero => rfl
        | succ _ => rfl
      | succ _ => rfl

/-- The number of CUP atoms (arity `0 ⇒ 2`) in a spine list — structural on the list, propext-free. -/
def cupAtomCount {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Nat
  | [] => 0
  | atom :: rest =>
      (if atom.generatorDom.length == 0 && atom.generatorCod.length == 2 then 1 else 0) + cupAtomCount rest

/-- The number of CAP atoms (arity `2 ⇒ 0`) in a spine list. -/
def capAtomCount {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Nat
  | [] => 0
  | atom :: rest =>
      (if atom.generatorDom.length == 2 && atom.generatorCod.length == 0 then 1 else 0) + capAtomCount rest

/-- The arc fold accumulates exactly `cupAtomCount` cup-event nodes onto the starting state — by induction on the
list (the `foldl`), the head via `stepArcAtom_cupEventNodes_length`. -/
theorem processArcSpine_cupEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (processArcSpine state atoms).cupEventNodes.length
      = state.cupEventNodes.length + cupAtomCount atoms
  | [], _ => rfl
  | atom :: rest, state => by
      show (processArcSpine (stepArcAtom state atom) rest).cupEventNodes.length = _
      rw [processArcSpine_cupEventNodes_length rest (stepArcAtom state atom),
        stepArcAtom_cupEventNodes_length state atom]
      dsimp only [cupAtomCount]
      rw [Nat.add_assoc]

/-- The arc fold accumulates exactly `capAtomCount` cap-event nodes onto the starting state. -/
theorem processArcSpine_capEventNodes_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    (processArcSpine state atoms).capEventNodes.length
      = state.capEventNodes.length + capAtomCount atoms
  | [], _ => rfl
  | atom :: rest, state => by
      show (processArcSpine (stepArcAtom state atom) rest).capEventNodes.length = _
      rw [processArcSpine_capEventNodes_length rest (stepArcAtom state atom),
        stepArcAtom_capEventNodes_length state atom]
      dsimp only [capAtomCount]
      rw [Nat.add_assoc]

/-- The cup-atom count of a `spineDiff` is CONTEXT-INDEPENDENT: it adds exactly the cell's intrinsic `cupCount`
onto the tail, regardless of the whisker accumulators.  By structural recursion on the cell — at a `gen` leaf the
atom's `generatorDom` / `generatorCod` ARE the cell's boundary paths, so the cup predicate matches `cupCount`'s
`gen` case on the nose; the composites / whiskerings recurse (`Nat`-add rearrangement only). -/
theorem cupAtomCount_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    cupAtomCount (cell.spineDiff leftAcc rightAcc rest) = cell.cupCount + cupAtomCount rest
  | _, _, _, _, _, _, .gen _, _ => rfl
  | _, _, _, _, _, _, .id _, _ => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.cupCount]; rw [Nat.zero_add]
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, rest => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.cupCount]
      rw [cupAtomCount_spineDiff leftAcc rightAcc cellLeft (cellRight.spineDiff leftAcc rightAcc rest),
        cupAtomCount_spineDiff leftAcc rightAcc cellRight rest, Nat.add_assoc]
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, rest =>
      cupAtomCount_spineDiff (composePath leftAcc oneCell) rightAcc body rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, rest =>
      cupAtomCount_spineDiff leftAcc (composePath oneCell rightAcc) body rest

/-- The cap-atom count of a `spineDiff` is CONTEXT-INDEPENDENT — the dual of `cupAtomCount_spineDiff`. -/
theorem capAtomCount_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    capAtomCount (cell.spineDiff leftAcc rightAcc rest) = cell.capCount + capAtomCount rest
  | _, _, _, _, _, _, .gen _, _ => rfl
  | _, _, _, _, _, _, .id _, _ => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.capCount]; rw [Nat.zero_add]
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, rest => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.capCount]
      rw [capAtomCount_spineDiff leftAcc rightAcc cellLeft (cellRight.spineDiff leftAcc rightAcc rest),
        capAtomCount_spineDiff leftAcc rightAcc cellRight rest, Nat.add_assoc]
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, rest =>
      capAtomCount_spineDiff (composePath leftAcc oneCell) rightAcc body rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, rest =>
      capAtomCount_spineDiff leftAcc (composePath oneCell rightAcc) body rest

/-- Running ONE cell from a state adds exactly the cell's intrinsic `cupCount` cup-event nodes. -/
theorem runArcCell_cupEventNodes_length {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    (runArcCell state leftAcc rightAcc cell).cupEventNodes.length
      = state.cupEventNodes.length + cell.cupCount := by
  unfold runArcCell
  rw [processArcSpine_cupEventNodes_length (cell.spineDiff leftAcc rightAcc []) state,
    cupAtomCount_spineDiff leftAcc rightAcc cell []]
  rfl

/-- Running ONE cell from a state adds exactly the cell's intrinsic `capCount` cap-event nodes. -/
theorem runArcCell_capEventNodes_length {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    (runArcCell state leftAcc rightAcc cell).capEventNodes.length
      = state.capEventNodes.length + cell.capCount := by
  unfold runArcCell
  rw [processArcSpine_capEventNodes_length (cell.spineDiff leftAcc rightAcc []) state,
    capAtomCount_spineDiff leftAcc rightAcc cell []]
  rfl

/-! ## The residual SHARPENED to the partition fields — the count fields discharged -/

/-- A `FullArcStructure` is determined by its five fields: equal fields give equal structures.  By `cases` on the
two structures and on each field equality (recursor / `Eq.rec` only), so propext-free. -/
theorem fullArcStructure_eq_of_fields {first second : FullArcStructure}
    (hDiagram : first.diagram = second.diagram)
    (hCupCount : first.cupCount = second.cupCount)
    (hCapCount : first.capCount = second.capCount)
    (hInternalCup : first.internalCupCounts = second.internalCupCounts)
    (hInternalCap : first.internalCapCounts = second.internalCapCounts) : first = second := by
  cases first; cases second
  cases hDiagram; cases hCupCount; cases hCapCount; cases hInternalCup; cases hInternalCap
  rfl

/-- ★ **The two-block commutation core, SHARPENED to the partition fields.**  The cup/cap COUNT fields are
order-independent (discharged below), so a `SpineGodementStep` reduces to the equality of only the three
partition-determined fields: the boundary `diagram` (partner matching + loops + port counts) and the per-port
`internalCupCounts` / `internalCapCounts`.  This is the genuine union-find PARTITION independence — strictly
smaller than `ArcGodementCommute`, which still carried the (now discharged) count fields. -/
def ArcGodementPartitionCommute (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : ArcWireState),
    (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).diagram
      = (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).diagram
    ∧ (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).internalCupCounts
      = (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).internalCupCounts
    ∧ (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).internalCapCounts
      = (extractArc bottomCount (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)).internalCapCounts

/-- ★ **The cup/cap COUNT fields are unconditionally Godement-invariant**, so the partition core implies the full
two-block core.  The count fields are `cupEventNodes.length` / `capEventNodes.length` after processing; by
`processArcSpine_*EventNodes_length` + `runArcCell_*EventNodes_length` each side is
`state.…Count + cellAlpha + cellAlphaUpper + cellBeta + cellBetaUpper + (count in rest)`, and the two run orders
differ only by transposing `cellAlphaUpper`'s and `cellBeta`'s counts — equal by `Nat.add_right_comm`.  The three
partition fields come straight from `ArcGodementPartitionCommute`. -/
theorem arcGodementCommute_of_partitionCommute {signature : ModeSignature}
    (partition : ArcGodementPartitionCommute signature) : ArcGodementCommute signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state
  obtain ⟨hDiagram, hInternalCup, hInternalCap⟩ :=
    partition cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
  refine fullArcStructure_eq_of_fields hDiagram ?_ ?_ hInternalCup hInternalCap
  · show (processArcSpine _ rest).cupEventNodes.length = (processArcSpine _ rest).cupEventNodes.length
    simp only [processArcSpine_cupEventNodes_length, runArcCell_cupEventNodes_length]
    rw [Nat.add_right_comm (state.cupEventNodes.length + cellAlpha.cupCount)
      cellAlphaUpper.cupCount cellBeta.cupCount]
  · show (processArcSpine _ rest).capEventNodes.length = (processArcSpine _ rest).capEventNodes.length
    simp only [processArcSpine_capEventNodes_length, runArcCell_capEventNodes_length]
    rw [Nat.add_right_comm (state.capEventNodes.length + cellAlpha.capCount)
      cellAlphaUpper.capCount cellBeta.capCount]

/-- ★ **`arcStructureOf` soundness under the COMPLETE `TwoCellConvFull`, gated on the PARTITION core alone.**
Composing `arcGodementCommute_of_partitionCommute` (which discharges the count fields) with
`arcStructureOf_sound_of_arcGodementCommute`: given only `ArcGodementPartitionCommute` — the union-find PARTITION
independence of the two disjoint blocks — `arcStructureOf` is invariant under the entire free-strict-2-category
convertibility.  The soundness residual is now exactly the three partition-determined fields; the fold-threading
AND the cup/cap counts are discharged. -/
theorem arcStructureOf_sound_of_arcGodementPartitionCommute {signature : ModeSignature}
    (partition : ArcGodementPartitionCommute signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcStructureOf_sound_of_arcGodementCommute (arcGodementCommute_of_partitionCommute partition) convFull

/-- **Honesty marker — the cup/cap COUNT fields of the Godement arc residual are DISCHARGED.**  The extract's
`cupCount` / `capCount` fields are order-independent atom counts; `arcGodementCommute_of_partitionCommute` proves
them Godement-invariant unconditionally (via `runArcCell_cupEventNodes_length` + `Nat.add_right_comm`), removing
two of the five fields from the residual.  `= true`. -/
def fxMode_hasArcCupCapCountFieldsDischarged : Bool := true

/-- **Honesty marker — the Godement arc residual is SHARPENED to the three partition-determined fields.**
`arcStructureOf_sound_of_arcGodementPartitionCommute` re-gates the entire `TwoCellConvFull` soundness on
`ArcGodementPartitionCommute` — only the boundary `diagram` (partner matching + loops + port counts) and the
per-port `internalCupCounts` / `internalCapCounts` remain.  The fold-threading and the cup/cap counts are
discharged.  `= true`. -/
def fxMode_hasArcGodementReducedToPartitionCommute : Bool := true

/-- **Honesty marker — the union-find PARTITION independence is the standing obligation.**
`ArcGodementPartitionCommute` states that transposing the two horizontally-disjoint middle blocks preserves the
boundary partner matching, the loop count, and the per-port internal cup/cap arc data — i.e. the union-find
PARTITION the extract reads off is unchanged.  TRUE (disjoint port-support merge sequences induce the same
connected components up to the fresh-id renaming) and computationally confirmed on the obstruction witnesses; its
general zero-axiom proof (a partition-isomorphism simulation between the two run orders) is the one remaining
soundness obligation, shared with the matching route's `fxMode_hasMatchingGodementIndependenceProof`.
`= false`. -/
def fxMode_hasArcPartitionCommuteProof : Bool := false

end FX1Poly.Tier0
