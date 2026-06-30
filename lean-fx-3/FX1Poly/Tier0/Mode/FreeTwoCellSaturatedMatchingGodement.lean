import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedMatchingCanonicalization
import FX1Poly.Tier0.Mode.FreeTwoCellArcSamePartitionFresh

/-! # mode-9 keystone — the matching-carrier Godement residual, REDUCED to the two-block commutation core

`FreeTwoCellSaturatedMatchingCanonicalization` proved the saturated soundness `saturatedConv_matchingOf_eq`
(`SaturatedTwoCellConv a b → matchingOf a = matchingOf b`) MODULO two named inputs, the first being the
SPINE-LEVEL state-parametric `godementInvariant` (`extractAfterProcessing state firstList =
extractAfterProcessing state secondList` for every `SpineGodementStep`).  That residual is posited RAW there —
a bare hypothesis quantifying over arbitrary cells.

This file SHARPENS that residual exactly as `FreeTwoCellGodementIndependence` sharpened the arc route's: it ships
the matching-carrier **fold-decomposition engine** and uses it to REDUCE the raw `godementInvariant` to the bare
two-block commutation core `MatchingGodementCommute` — the αUpper↔β disjoint-support commutation, with the
fold-threading and the common prefix / suffix discharged.

  ★ `runMatchingCell` / `processSpine_spineDiff` — the fold-decomposition: folding `stepAtom` over a cons-only
    `spineDiff` difference-list equals running the cell alone (`runMatchingCell`) then the tail.  Structural
    recursion on the cell, definitional per arm — `propext`/`Quot.sound`-free.  The exact `DiagramType`-carrier
    analog of the arc route's `processArcSpine_spineDiff`.
  ★ `MatchingGodementCommute` + `matchingGodementInvariant_of_commute` — the two-block commutation core and the
    reduction.  A `SpineGodementStep` transposes the two horizontally-disjoint middle blocks (`cellAlphaUpper`,
    `cellBeta`) with a context shift; `processSpine_spineDiff` peels the untouched outer blocks (`cellAlpha`
    prefix, `cellBetaUpper` suffix) and the common tail, so the whole `godementInvariant` reduces to the bare
    statement that the two run orders of those two blocks extract to the SAME `DiagramType` from EVERY state.
  ★ `saturatedConv_matchingOf_eq_of_commute` / `saturatedMatchingCanonicalization_ofCommute` — the keystone's
    soundness field and the whole canonicalization, re-gated on `MatchingGodementCommute` (two-block) instead of
    the raw spine-level `godementInvariant`.  The residual is strictly smaller.

## What is honest-DEFERRED (the SHARPENED residual)

`MatchingGodementCommute` — `fxMode_hasMatchingBlockCommuteProof = false`.  The union-find PARTITION
independence for the boundary matching: transposing the two horizontally-disjoint blocks preserves the connected
components the `DiagramType` extract reads off (the boundary `partner` matching and the loop count).  This is a
STRICT SUBSET of the arc route's open `fxMode_hasArcPartitionCommuteProof` (which additionally owes the per-port
internal cup/cap counts the `DiagramType` carrier forgets) — the matching carrier reads ONLY boundary
connectivity, so its Godement residual is the cleanest form of the shared partition-commutation node.  TRUE
(disjoint port-support merge sequences induce the same boundary partition up to the fresh-id renaming the extract
reads through) and computationally confirmed on every obstruction witness (`parallelUnits_matchingOf_eq`,
`parallelCounits_matchingOf_eq`); its general zero-axiom proof (a partition-isomorphism simulation between the
two run orders) is the remaining obligation.

Raw Lean 4 + Init; the fold-decomposition is definitional structural recursion (no `omega` / `simp`-AC /
`WellFounded.fix` / `List.append`), the reduction is `cases` on the single Godement constructor.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The fold-decomposition engine -/

/-- Run the matching fold over ONE cell's spine from a given state (the cell's contribution alone, with an empty
tail).  Reading a `spineDiff` block off the fold reduces, via `processSpine_spineDiff`, to threading
`runMatchingCell` for each block. -/
def runMatchingCell {signature : ModeSignature} {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) : WireState :=
  processSpine state (cell.spineDiff leftAcc rightAcc [])

/-- ★ **The fold-decomposition of the matching spine fold over a `spineDiff` difference-list.**  Folding the
per-atom `stepAtom` over `cell.spineDiff leftAcc rightAcc rest` equals folding it over the cell alone
(`runMatchingCell`) and then over `rest`.  By structural recursion on `cell`: a generator / identity reduce
definitionally (`foldl` on a singleton / on `[]`), a vertical composite peels each factor in turn, and the two
whiskerings recurse under the shifted accumulators.  Cons-only difference lists keep it `List.append`-free,
hence propext-free.  The `DiagramType`-carrier analog of `processArcSpine_spineDiff`. -/
theorem processSpine_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : WireState) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    processSpine state (cell.spineDiff leftAcc rightAcc rest)
      = processSpine (runMatchingCell state leftAcc rightAcc cell) rest
  | _, _, _, _, _, _, .gen _, _, _ => rfl
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, state, rest => by
      show processSpine state
          (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc rest))
        = processSpine (runMatchingCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)) rest
      rw [processSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc rest),
        processSpine_spineDiff leftAcc rightAcc cellRight (runMatchingCell state leftAcc rightAcc cellLeft) rest]
      congr 1
      show runMatchingCell (runMatchingCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight
        = processSpine state (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc []))
      rw [processSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])]
      rfl
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, state, rest =>
      processSpine_spineDiff (composePath leftAcc oneCell) rightAcc body state rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, state, rest =>
      processSpine_spineDiff leftAcc (composePath oneCell rightAcc) body state rest

/-! ## The two-block commutation core — the residual, SHARPENED -/

/-- ★ **The two-block commutation core** — the matching Godement residual with the fold-threading discharged.  A
`SpineGodementStep` transposes the two horizontally-disjoint middle blocks `cellAlphaUpper` (right context
`gLow → gMid`) and `cellBeta` (left context `fHigh → fMid`); `cellAlpha` (the prefix) and `cellBetaUpper` (the
suffix) are untouched.  `processSpine_spineDiff` peels all four blocks, so the entire `godementInvariant` reduces
to THIS: the two run orders of `cellAlphaUpper` and `cellBeta` — run after the common `cellAlpha` prefix, before
the common `cellBetaUpper` suffix and `rest` — extract to the SAME `DiagramType` from EVERY starting state.  The
genuine Mazurkiewicz independence (disjoint-support merge sequences induce the same boundary partition up to the
fresh-id renaming the extract reads through); the LHS runs `αUpper` then `β`, the RHS `β` then `αUpper`, and the
four context shifts (`gLow`/`gMid`, `fHigh`/`fMid`) are exactly the constructor's. -/
def MatchingGodementCommute (signature : ModeSignature) : Prop :=
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
    (bottomCount : Nat) (state : WireState),
    extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      = extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-! ## The reduction: the two-block core IMPLIES the keystone's full Godement residual -/

/-- ★ **The reduction.**  The two-block commutation core `MatchingGodementCommute` implies the keystone's full
state-parametric Godement-step invariance (the raw `godementInvariant` shape) — with NOTHING else owed.  By
`cases` on the single `SpineGodementStep.godement` constructor (its redex / reduct spines are the four-block
nested `spineDiff` forms) followed by four `processSpine_spineDiff` peels on each side, both sides land EXACTLY on
`MatchingGodementCommute`'s two run-order states.  The fold-threading and the common prefix / tail are thereby
discharged; the bare αUpper↔β disjoint commutation is all the core supplies. -/
theorem matchingGodementInvariant_of_commute {signature : ModeSignature}
    (commute : MatchingGodementCommute signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : WireState)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractAfterProcessing bottomCount state firstList
      = extractAfterProcessing bottomCount state secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [extractAfterProcessing, processSpine_spineDiff]
    exact commute cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state

/-- ★ **The keystone soundness field, re-gated on the two-block core.**  Composing the reduction
`matchingGodementInvariant_of_commute` with the keystone's `saturatedConv_matchingOf_eq`: given the two-block
commutation core (`MatchingGodementCommute adjunctionModeSignature`) and the matching's saturated-congruence
compositionality (`MatchingSaturatedCongruence`), `matchingOf` is invariant under the COMPLETE
`SaturatedTwoCellConv` — the triangle cases ON THE NOSE, `whiskerExchange` same-spine, the congruences by
`congruence`, and the `ofFull` interchange step through the two-block core.  The soundness residual is now exactly
the bare disjoint-block commutation, the fold-threading discharged. -/
theorem saturatedConv_matchingOf_eq_of_commute
    (commute : MatchingGodementCommute adjunctionModeSignature)
    (congruence : MatchingSaturatedCongruence)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB :=
  saturatedConv_matchingOf_eq (matchingGodementInvariant_of_commute commute) congruence conv

/-- ★ **Assembling the keystone from the two-block core.**  `saturatedMatchingCanonicalization_of` with the raw
`godementInvariant` discharged by `matchingGodementInvariant_of_commute`: a `SaturatedMatchingCanonicalization`
is determined by the two-block commutation core, the saturated-congruence compositionality, and a `convOfMapEq`
reconstruction.  This pins exactly how the keystone assembles around the SHARPENED Godement residual. -/
def saturatedMatchingCanonicalization_ofCommute
    (commute : MatchingGodementCommute adjunctionModeSignature)
    (congruence : MatchingSaturatedCongruence)
    (convOfMapEq : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
      matchingOf cellA = matchingOf cellB → SaturatedTwoCellConv cellA cellB) :
    SaturatedMatchingCanonicalization :=
  saturatedMatchingCanonicalization_of (matchingGodementInvariant_of_commute commute) congruence convOfMapEq

/-! ## Renaming-invariance of the matching extract — the partition-view half, CLOSED

The two-block core `MatchingGodementCommute` reduces to the boundary-partition commutation.  This section ships
the PARTITION-VIEW half of that node — the matching twin of the arc route's `fxMode_hasArcRenameInvariance` — by
REUSING the shared union-find renaming lemmas (`beq_congr_inj`, `unionFindRootOf_rename`) and the partner read-off
congruence (`findPartnerScan_congr`) the arc route proved over the shared primitives.  The matching carrier reads
ONLY boundary connectivity, so its renaming relation `MatchingRenameRel` is strictly leaner than the arc's
`ArcRenameRel` (no per-root cup/cap event-count fields).

The remaining residual is then EXACTLY the witness construction: exhibiting the node-id renaming between the two
Godement run orders.  That is the shared open frontier `fxMode_hasArcGodementSwapRenameableProof = false`, and the
arc route established that it MUST be conditioned on freshness (`not_arcGodementSamePartition` refutes the
unconditional partition equality).  This section closes the renaming-invariant read-off the witness feeds. -/

/-- The boundary node ids of a matching `WireState`: the bottom ports `0 … bottomCount-1` followed by the open
top wires — exactly the `boundaryNodes` `extractDiagram` reads (definitionally `List.range bottomCount ++
state.openWires`). -/
def matchingBoundaryNodes (bottomCount : Nat) (state : WireState) : List Nat :=
  List.range bottomCount ++ state.openWires

/-- Whether two boundary ports of a matching `WireState` share a union-find component — the same-component
relation `extractDiagram`'s partner matching reads off.  `propext`-free (a `Nat` `BEq` of the two roots). -/
def matchingSameComponent (bottomCount : Nat) (state : WireState) (firstIndex secondIndex : Nat) : Bool :=
  unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
    == unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)

/-- ★ **The matching extract is determined by the boundary-connectivity view.**  Two matching states with equal
open-wire count, equal loop count, and the same boundary same-component relation on the in-range indices extract
to the same `DiagramType`.  The `DiagramType`-carrier analog of the arc route's `extractArc_eq_of_partitionView`
(the `.diagram` field alone — no per-port cup/cap counts): the partner matching closes by `findPartnerScan_congr`
+ `listMapCongr` over the agreeing same-component relation, the open-wire / loop counts are direct.  All indices
sit in `List.range (bottomCount + openWires.length)`, so the in-range hypotheses suffice (`mem_range_imp_lt`). -/
theorem extractDiagram_eq_of_connectivityView (bottomCount : Nat) (firstState secondState : WireState)
    (lengthsAgree : firstState.openWires.length = secondState.openWires.length)
    (loopsAgree : firstState.loops = secondState.loops)
    (relationAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        matchingSameComponent bottomCount firstState firstIndex secondIndex
          = matchingSameComponent bottomCount secondState firstIndex secondIndex) :
    extractDiagram bottomCount firstState = extractDiagram bottomCount secondState := by
  have totalsAgree : bottomCount + firstState.openWires.length = bottomCount + secondState.openWires.length := by
    rw [lengthsAgree]
  apply diagramType_eq_of_fields
  · rfl
  · exact lengthsAgree
  · show (List.range (bottomCount + firstState.openWires.length)).map
            (partnerIndexOf firstState.links (matchingBoundaryNodes bottomCount firstState)
              (bottomCount + firstState.openWires.length))
       = (List.range (bottomCount + secondState.openWires.length)).map
            (partnerIndexOf secondState.links (matchingBoundaryNodes bottomCount secondState)
              (bottomCount + secondState.openWires.length))
    rw [← totalsAgree]
    apply listMapCongr
    intro candidateIndex candidateInRange
    have candidateBelow : candidateIndex < bottomCount + firstState.openWires.length :=
      mem_range_imp_lt candidateInRange
    show findPartnerScan firstState.links (matchingBoundaryNodes bottomCount firstState)
          (unionFindRootOf firstState.links
            (natListGetAt (matchingBoundaryNodes bottomCount firstState) candidateIndex))
          candidateIndex (List.range (bottomCount + firstState.openWires.length))
       = findPartnerScan secondState.links (matchingBoundaryNodes bottomCount secondState)
          (unionFindRootOf secondState.links
            (natListGetAt (matchingBoundaryNodes bottomCount secondState) candidateIndex))
          candidateIndex (List.range (bottomCount + firstState.openWires.length))
    apply findPartnerScan_congr
    intro scanIndex scanInRange
    exact relationAgrees scanIndex candidateIndex (mem_range_imp_lt scanInRange) candidateBelow
  · exact loopsAgree

/-- Two matching states are **renaming-related** at `bottomCount` via `sigma` when `t` is a `sigma`-renaming of
`s` fixing the bottom-boundary ports: equal open-wire / loop counts, `sigma` injective, every in-range boundary
node of `t` is the `sigma`-image of the corresponding boundary node of `s`, and the union-find root
root-commutes.  The leaner `DiagramType`-carrier analog of the arc route's `ArcRenameRel` — the per-root cup/cap
event-count fields are DROPPED (the matching extract never reads them). -/
structure MatchingRenameRel (bottomCount : Nat) (sigma : Nat → Nat) (firstState secondState : WireState) :
    Prop where
  /-- The open-wire counts agree. -/
  lengthEq : secondState.openWires.length = firstState.openWires.length
  /-- The loop counts agree. -/
  loopsEq : secondState.loops = firstState.loops
  /-- The renaming is injective. -/
  inj : ∀ a b, sigma a = sigma b → a = b
  /-- Every in-range boundary node of `secondState` is the `sigma`-image of the corresponding one of `firstState`. -/
  bnodeCorr : ∀ index, index < bottomCount + firstState.openWires.length →
      natListGetAt (matchingBoundaryNodes bottomCount secondState) index
        = sigma (natListGetAt (matchingBoundaryNodes bottomCount firstState) index)
  /-- The union-find root root-commutes with `sigma`. -/
  rootComm : ∀ x, unionFindRootOf secondState.links (sigma x) = sigma (unionFindRootOf firstState.links x)

/-- ★ **Renaming-invariance of the matching extract.**  Renaming-related matching states extract to the SAME
`DiagramType`: the open-wire / loop counts come straight from the relation, and the boundary same-component
booleans agree because the boundary nodes correspond under `sigma` and the root root-commutes (so the `==` is
`beq_congr_inj`-transported).  The fresh node-ids the two Godement run orders allocate in different orders are
exactly the renaming's content — invisible to the matching extract.  The matching twin of
`sameArcPartition_of_renameRel`, reusing the SHARED `beq_congr_inj` over the SHARED `unionFindRootOf`. -/
theorem extractDiagram_of_matchingRenameRel (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState)
    (rel : MatchingRenameRel bottomCount sigma firstState secondState) :
    extractDiagram bottomCount firstState = extractDiagram bottomCount secondState := by
  apply extractDiagram_eq_of_connectivityView bottomCount firstState secondState rel.lengthEq.symm rel.loopsEq.symm
  intro firstIndex secondIndex firstBelow secondBelow
  show (unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        == unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex))
     = (unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        == unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex))
  rw [rel.bnodeCorr firstIndex firstBelow, rel.bnodeCorr secondIndex secondBelow,
    rel.rootComm, rel.rootComm, beq_congr_inj sigma rel.inj]

/-! ## Residual 1, FULLY reduced to the renaming-witness construction -/

/-- ★ **The matching Godement residual at the RENAMING level.**  The two-block run orders — the redex
(`cellAlphaUpper` then `cellBeta`) and the reduct (`cellBeta` then `cellAlphaUpper`), with the common `cellAlpha`
prefix, `cellBetaUpper` suffix and `rest` tail — are related by an injective node renaming fixing the bottom
boundary (`MatchingRenameRel`).  The `DiagramType`-carrier analog of the arc route's `ArcGodementSwapRenameable`:
the Mazurkiewicz independence content (the two horizontally-disjoint blocks act on disjoint wire supports, so
transposing them only permutes the disjoint fresh id ranges).  Stated unconditionally in `state` to match
`MatchingGodementCommute`; the witness is only SATISFIABLE under freshness (see
`fxMode_hasMatchingBlockCommuteProof`). -/
def MatchingGodementSwapRenameable (signature : ModeSignature) : Prop :=
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
    (bottomCount : Nat) (state : WireState),
    ∃ sigma : Nat → Nat, MatchingRenameRel bottomCount sigma
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **The reduction.**  The renaming-level residual `MatchingGodementSwapRenameable` IMPLIES the two-block
commutation core `MatchingGodementCommute` — with NOTHING else owed: the renaming witness between the two run
orders feeds `extractDiagram_of_matchingRenameRel` to give the equal extract the core demands.  The
renaming-invariance of the partition view (everything ABOVE the witness construction) is discharged.  The matching
twin of `arcGodementSamePartitionFresh_of_swapRenameable`.  Chained with `matchingGodementInvariant_of_commute`
and `saturatedConv_matchingOf_eq_of_commute`, the ENTIRE residual-1 chain is reduced to constructing the renaming
`sigma`. -/
theorem matchingGodementCommute_of_swapRenameable {signature : ModeSignature}
    (swapRenameable : MatchingGodementSwapRenameable signature) :
    MatchingGodementCommute signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state
  obtain ⟨sigma, rel⟩ :=
    swapRenameable cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
  exact extractDiagram_of_matchingRenameRel bottomCount sigma _ _ rel

/-- ★ **The whole keystone soundness, reduced to the renaming witness.**  Composing
`matchingGodementCommute_of_swapRenameable` → `matchingGodementInvariant_of_commute` →
`saturatedConv_matchingOf_eq`: given the renaming witness (`MatchingGodementSwapRenameable`) and the saturated
congruence (`MatchingSaturatedCongruence`), `matchingOf` is invariant under the COMPLETE `SaturatedTwoCellConv`.
The Godement soundness residual is now EXACTLY the renaming-witness construction (`sigma` between the two run
orders) — the partition-view read-off, the fold-threading, and the triangle / whisker-exchange cases all
discharged. -/
theorem saturatedConv_matchingOf_eq_of_swapRenameable
    (swapRenameable : MatchingGodementSwapRenameable adjunctionModeSignature)
    (congruence : MatchingSaturatedCongruence)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB :=
  saturatedConv_matchingOf_eq_of_commute
    (matchingGodementCommute_of_swapRenameable swapRenameable) congruence conv

/-! ## Honesty markers -/

/-- **Honesty marker — the matching Godement residual's fold-threading is DISCHARGED.**  `processSpine_spineDiff`
proves the matching fold decomposes over the cons-only `spineDiff` difference-list (`runMatchingCell` per block),
so the four whiskered blocks of a `SpineGodementStep` peel off unconditionally and `propext`-free.  This is the
structural half of the keystone's raw `godementInvariant`.  `= true`. -/
def fxMode_hasMatchingGodementFoldDecomposition : Bool := true

/-- **Honesty marker — the matching Godement residual is REDUCED to the two-block commutation core.**
`matchingGodementInvariant_of_commute` proves the keystone's full state-parametric `godementInvariant` from
`MatchingGodementCommute` alone, and `saturatedConv_matchingOf_eq_of_commute` re-gates the entire saturated
soundness on that single core.  The residual is strictly smaller than the keystone's raw hypothesis: the
four-fold fold-threading and the common prefix / suffix are discharged; only the bare αUpper↔β disjoint-support
commutation remains.  `= true`. -/
def fxMode_hasMatchingGodementReducedToBlockCommute : Bool := true

/-- **Honesty marker — the renaming-invariance of the matching extract is CLOSED.**
`extractDiagram_of_matchingRenameRel` proves that renaming-related matching states (`MatchingRenameRel` — equal
open-wire / loop counts, an injective boundary-fixing node renaming, root-commutation) extract to the SAME
`DiagramType`, via the factoring `extractDiagram_eq_of_connectivityView`.  Both REUSE the SHARED union-find
machinery (`beq_congr_inj`, `findPartnerScan_congr`, `listMapCongr`, `mem_range_imp_lt`, `diagramType_eq_of_fields`)
the arc route proved over the shared primitives.  This is the matching twin of the arc's
`fxMode_hasArcRenameInvariance = true`, and STRICTLY LEANER: `MatchingRenameRel` drops the per-root cup/cap
event-count fields the arc's `ArcRenameRel` carries (the matching extract never reads them).  So the
partition-VIEW half of the matching Godement residual is discharged.  `= true`. -/
def fxMode_hasMatchingExtractRenameInvariance : Bool := true

/-- **Honesty marker — residual 1 is FULLY reduced to the renaming-witness construction.**
`matchingGodementCommute_of_swapRenameable` proves `MatchingGodementCommute` from
`MatchingGodementSwapRenameable` (the two run orders are renaming-related) alone — feeding the closed
`extractDiagram_of_matchingRenameRel`.  Chained through `matchingGodementInvariant_of_commute` and
`saturatedConv_matchingOf_eq_of_swapRenameable`, the ENTIRE matching Godement soundness residual is now exactly
the renaming `sigma` between the two Godement run orders — the SAME open frontier as the arc route's
`fxMode_hasArcGodementSwapRenameableProof`, in the cleaner `DiagramType`-carrier form.  Everything above the
witness (fold-threading, partition-view read-off, triangle / whisker-exchange) is discharged.  `= true`. -/
def fxMode_hasMatchingGodementReducedToSwapRenameable : Bool := true

/-- **Honesty marker — the matching two-block EXTRACT commutation is not proven directly; the live residual is
the freshness-conditioned RENAMING WITNESS.**  `MatchingGodementCommute` (as stated, unconditional in `state`)
mirrors the keystone's raw `godementInvariant` and the arc route's unconditional `ArcGodementCommute`.  The
partition-VIEW half is now CLOSED (`extractDiagram_of_matchingRenameRel`), so the residual reduces to the WITNESS:
exhibiting the node-id renaming `sigma` between the two Godement run orders (`∃ sigma, MatchingRenameRel … redex
reduct`).  That witness construction is the shared open frontier `fxMode_hasArcGodementSwapRenameableProof =
false`.  The arc route established (`not_arcGodementSamePartition`, `fxMode_hasArcSamePartitionRefuted = true`) that
the UNCONDITIONAL partition equality is REFUTED — a non-fresh state lets a cup allocate a colliding id — so the
live witness must be conditioned on freshness (the matching twin of `ArcGodementSamePartitionFresh`).  Hence both
this unconditional core and the keystone's unconditional `godementInvariant` are the too-strong intermediate; the
correct residual is the freshness-conditioned renaming witness, of which only the partition-view read-off is
closed here.  TRUE on every obstruction witness (`parallelUnits_matchingOf_eq`, `parallelCounits_matchingOf_eq`).
`= false`. -/
def fxMode_hasMatchingBlockCommuteProof : Bool := false

end FX1Poly.Tier0
