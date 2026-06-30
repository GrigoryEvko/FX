import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedMatchingCanonicalization

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

/-- **Honesty marker — the matching two-block EXTRACT commutation is not proven directly.**
`MatchingGodementCommute` states that transposing the two horizontally-disjoint middle blocks `cellAlphaUpper` /
`cellBeta` (with their context shifts) preserves the WHOLE `DiagramType` extract — the boundary `partner` matching
and the loop count — from every state.  It is NOT proven outright here.  This is a STRICT SUBSET of the arc
route's open `fxMode_hasArcPartitionCommuteProof` (which additionally owes the per-port internal cup/cap counts
the `DiagramType` carrier forgets): the matching carrier reads ONLY boundary connectivity, so its Godement
residual is the cleanest form of the shared partition-commutation node.  TRUE (the blocks act on disjoint
port-sets; disjoint-support merge sequences induce the same boundary partition up to the fresh-id renaming the
extract reads through) and computationally confirmed on every obstruction witness (`parallelUnits_matchingOf_eq`,
`parallelCounits_matchingOf_eq`); its general zero-axiom proof (a partition-isomorphism simulation between the two
run orders) is the one remaining soundness obligation.  `= false`. -/
def fxMode_hasMatchingBlockCommuteProof : Bool := false

end FX1Poly.Tier0
