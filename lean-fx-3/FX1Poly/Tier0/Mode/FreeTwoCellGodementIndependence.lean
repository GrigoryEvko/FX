import FX1Poly.Tier0.Mode.FreeTwoCellSpineTraceDecision

/-! # mode-3 floor — the Godement arc-extract independence, REDUCED to the two-block commutation core

`FreeTwoCellSpineTraceDecision` ships the full planar-arc invariant `arcStructureOf` and proves its FULL
`TwoCellConvFull` soundness ASSEMBLED modulo one residual: the state-parametric Godement-step invariance
`godementInvariant` — `extractArcAfterProcessing state redex = extractArcAfterProcessing state reduct` for every
`SpineGodementStep`.  That residual is the union-find INDEPENDENCE of two horizontally-disjoint blocks; its
honesty marker there is `fxMode_hasArcGodementIndependenceProof = false`.

This file discharges the STRUCTURAL HALF of that residual — the fold-threading boilerplate — leaving ONLY the
genuine disjoint-support commutation:

  ★ `runArcCell` / `processArcSpine_spineDiff` — the **fold-decomposition engine**: running the arc fold over a
    cons-only `spineDiff` difference-list equals running it over the cell alone (`runArcCell`) and then over the
    tail.  Pure structural recursion on the cell, definitional per arm, so it is `propext`/`Quot.sound`-free.
    This is the lemma that lets the fold peel one whiskered block at a time.
  ★ `ArcGodementCommute` — the **two-block commutation core**, the residual SHARPENED.  A `SpineGodementStep`
    transposes exactly two horizontally-disjoint middle blocks (`cellAlphaUpper` and `cellBeta`) with a
    context shift; `processArcSpine_spineDiff` peels the untouched outer blocks (`cellAlpha` prefix,
    `cellBetaUpper`) and the common tail, reducing the whole `godementInvariant` to the bare statement that the
    two run orders of those two blocks produce an arc-EXTRACT-equal state.  This is the genuine
    Mazurkiewicz-trace independence — two union-find merge sequences with DISJOINT port-support commute — and it
    is the ONE remaining soundness obligation.
  ★ `arcGodementInvariant_of_commute` — the **reduction**: `ArcGodementCommute` IMPLIES the parent's full
    `godementInvariant` (via the fold-decomposition, with nothing else owed).
  ★ `arcStructureOf_sound_of_arcGodementCommute` — composing the reduction with the parent's
    `arcStructureOf_sound_of_godementInvariant`: `arcStructureOf` is invariant under the COMPLETE
    `TwoCellConvFull` GIVEN only `ArcGodementCommute` — the soundness residual is now exactly the two-block
    commutation, the fold-threading discharged.

## What is honest-DEFERRED (the SHARPENED residual)

`ArcGodementCommute` — `fxMode_hasArcBlockCommuteProof = false`.  TRUE (the two blocks act on disjoint
port-sets, so their merge operations commute up to the fresh-id renaming the extract reads through), and it is
strictly smaller than the parent's `godementInvariant`: the four-fold fold-threading and the common
prefix/tail are discharged here unconditionally; only the bare αUpper↔β disjoint-support commutation remains.
The general zero-axiom proof (a state-renaming simulation between the two run orders) is the standing obligation,
shared with the matching route's `fxMode_hasMatchingGodementIndependenceProof`.

Raw Lean 4 + Init; the fold-decomposition is definitional structural recursion (no `omega` / `simp`-AC /
`WellFounded.fix` / `List.append`), the reduction is `cases` on the single Godement constructor plus the
fold-decomposition.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

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

/-- **Honesty marker — the two-block commutation core itself is the standing obligation.**  `ArcGodementCommute`
states that transposing the two horizontally-disjoint middle blocks `cellAlphaUpper` / `cellBeta` (with their
context shifts) preserves the arc EXTRACT from every state.  TRUE (the blocks act on disjoint port-sets, so
their union-find merges commute up to the fresh-id renaming the extract reads through) and computationally
confirmed on the obstruction witnesses (`parallelUnits_cupCount_eq` / `parallelCounits_capCount_eq` and the
matching route's `parallelUnits_matchingOf_eq`).  Its general zero-axiom proof — a state-renaming simulation
between the two run orders — is the one remaining soundness obligation, shared with the matching route's
`fxMode_hasMatchingGodementIndependenceProof`.  `= false`. -/
def fxMode_hasArcBlockCommuteProof : Bool := false

end FX1Poly.Tier0
