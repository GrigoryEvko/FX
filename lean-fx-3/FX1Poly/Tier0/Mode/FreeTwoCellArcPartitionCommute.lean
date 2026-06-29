import FX1Poly.Tier0.Mode.FreeTwoCellGodementIndependence

/-! # mode-3 floor — the Godement arc residual REDUCED to the boundary-connectivity closure

`FreeTwoCellGodementIndependence` sharpened the full `arcStructureOf` soundness residual to
`ArcGodementPartitionCommute` — the union-find PARTITION independence of transposing the two
horizontally-disjoint Godement blocks, stated as agreement of the THREE partition-determined EXTRACT fields
(`diagram` = partner matching + loops + port counts; `internalCupCounts`; `internalCapCounts`).  It left
`fxMode_hasArcPartitionCommuteProof = false`, with the cup/cap COUNT fields already discharged.

This file peels the EXTRACTION PLUMBING off that residual.  The decisive observation (the de-risking insight that
prior node-id-simulation passes missed): the extracted partition data is a FUNCTION of the **boundary-port
connectivity equivalence** — the per-index same-component relation read off the union-find — plus the per-port
turnback counts, the loop count and the open-wire count.  The fresh node-ids the two run orders allocate in
different orders are union-find INTERNALS, invisible to that data.  So `extractArc` is RENAMING-INVARIANT: it
factors through the boundary-connectivity view.  We prove exactly that, zero-axiom:

  ★ `extractArc_eq_of_partitionView` — the **renaming-invariance / factoring theorem**: two arc states that agree
    on the open-wire count, the loop count, the cup/cap event-node counts, the boundary same-component relation
    (`boundarySameComponent`) on the in-range indices, and the per-port internal cup/cap counts
    (`internalEventCountAt`) extract to the SAME `FullArcStructure`.  This discharges the entire `findPartnerScan`
    / `extractDiagram` / `List.map` read-off layer once and for all — the connectivity data determines the
    extract.

  ★ `SameArcPartition` / `ArcGodementSamePartition` — the residual restated at the connectivity level: two states
    are `SameArcPartition` when they share that boundary-connectivity view; the Godement residual
    `ArcGodementSamePartition` asks that the two Godement run orders land `SameArcPartition`.  This is the genuine
    Mazurkiewicz statement — **disjoint-support merge sequences induce the same connected-components closure** —
    with all the extraction machinery removed.

  ★ `arcGodementPartitionCommute_of_sameArcPartition` — the reduction: `ArcGodementSamePartition` implies the
    parent's `ArcGodementPartitionCommute`, the cup/cap event-node COUNT fields discharged unconditionally here
    (order-independent atom counts, exactly as the parent did, transposed by `Nat.add_right_comm`).

  ★ `arcGodementInvariant_of_sameArcPartition` / `arcStructureOf_sound_of_arcGodementSamePartition` — the
    assembly: composing with the parent's shipped reductions, the connectivity residual alone yields the parent's
    full state-parametric `godementInvariant` (the input `decidableTwoCellConvFull_of` consumes) and the complete
    `TwoCellConvFull` soundness of `arcStructureOf`.

## What is honest-DEFERRED (the connectivity-closure residual)

`ArcGodementSamePartition` — `fxMode_hasArcSamePartitionProof = false`.  Transposing the two
horizontally-disjoint Godement blocks preserves the boundary same-component relation, the per-port cup/cap counts,
the loop count and the open-wire count: the pure "disjoint merges commute on the connectivity closure" fact.  It
is the standing soundness obligation, now stripped of the extract read-off — the renaming-invariance half (which
the prior passes drowned in node-id bookkeeping) is PROVED, leaving only the combinatorial closure-commutation.
This file does NOT flip the parent's `fxMode_hasArcPartitionCommuteProof`; it provides the strictly more atomic
route to it.

Raw Lean 4 + Init; the factoring is structural induction on the candidate / map lists (`findPartnerScan_congr`,
`listMapCongr`) plus a manual `propext`-free `mem_range_imp_lt` (Lean core's `List.mem_range` depends on
`propext` / `Quot.sound`); the reduction is the parent's count machinery + `Nat.add_right_comm`.  No `omega`,
no `simp`-AC, no `List.append` lemmas, no `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Tier0

/-! ## `propext`-free list helpers (Lean core's range/membership lemmas leak `propext`) -/

/-- `List.range.loop count acc` lists `0 … count-1` in front of `acc`, so a member is either below `count` or
already in `acc`.  Structural recursion on `count`, casing the cons-membership by its constructors — `propext`-free
(Lean core's `List.mem_range` depends on `propext` / `Quot.sound`). -/
theorem memRangeLoop_imp {target : Nat} :
    (count : Nat) → (acc : List Nat) → target ∈ List.range.loop count acc →
    target < count ∨ target ∈ acc
  | 0, _, membership => Or.inr membership
  | count + 1, acc, membership => by
      have recurse := memRangeLoop_imp count (count :: acc) membership
      cases recurse with
      | inl isBelow => exact Or.inl (Nat.lt_succ_of_lt isBelow)
      | inr consMembership =>
          cases consMembership with
          | head => exact Or.inl (Nat.lt_succ_self _)
          | tail _ tailMembership => exact Or.inr tailMembership

/-- A member of `List.range count` is below `count` — the `propext`-free replacement for `List.mem_range.mp`. -/
theorem mem_range_imp_lt {target count : Nat} (membership : target ∈ List.range count) : target < count := by
  cases memRangeLoop_imp count [] membership with
  | inl isBelow => exact isBelow
  | inr nilMembership => nomatch nilMembership

/-- Pointwise congruence of `List.map` over a `Nat` list: functions agreeing on every member give equal maps.
Structural recursion on the list, head agreement via `List.Mem.head`, tail via `List.Mem.tail` — no `funext`
(which would leak `Quot.sound`), no `propext`. -/
theorem listMapCongr {resultType : Type} (mapFirst mapSecond : Nat → resultType) :
    (cands : List Nat) → (∀ candidate ∈ cands, mapFirst candidate = mapSecond candidate) →
    cands.map mapFirst = cands.map mapSecond
  | [], _ => rfl
  | head :: tail, agree => by
      dsimp only [List.map]
      rw [agree head (List.Mem.head _),
        listMapCongr mapFirst mapSecond tail (fun candidate inTail => agree candidate (List.Mem.tail _ inTail))]

/-! ## The boundary-connectivity view of an arc state -/

/-- The boundary node ids of an arc state: the bottom ports `0 … bottomCount-1` followed by the open top wires —
exactly the `boundaryNodes` `extractArc` reads (definitionally `List.range bottomCount ++ state.openWires`). -/
def boundaryNodesOf (bottomCount : Nat) (state : ArcWireState) : List Nat :=
  List.range bottomCount ++ state.openWires

/-- Whether two boundary ports share a union-find component — the boundary same-component relation `extractArc`'s
partner matching reads off.  `propext`-free (a `Nat` `BEq` of the two roots). -/
def boundarySameComponent (bottomCount : Nat) (state : ArcWireState) (firstIndex secondIndex : Nat) : Bool :=
  unionFindRootOf state.links (natListGetAt (boundaryNodesOf bottomCount state) firstIndex)
    == unionFindRootOf state.links (natListGetAt (boundaryNodesOf bottomCount state) secondIndex)

/-- `findPartnerScan` reads its boundary nodes only through the per-candidate root-equality boolean.  So two scans
whose root-equality booleans agree on every candidate return the same partner index — regardless of the actual
node ids / link lists / root values.  Structural recursion on the candidate list; the cons step rewrites the head
boolean and the recursive tail.  This is the renaming-invariance of the partner read-off. -/
theorem findPartnerScan_congr
    (firstLinks : List (Nat × Nat)) (firstBoundaryNodes : List Nat) (firstRootHere : Nat)
    (secondLinks : List (Nat × Nat)) (secondBoundaryNodes : List Nat) (secondRootHere excludeIndex : Nat) :
    (cands : List Nat) →
    (∀ candidate ∈ cands,
        (unionFindRootOf firstLinks (natListGetAt firstBoundaryNodes candidate) == firstRootHere)
          = (unionFindRootOf secondLinks (natListGetAt secondBoundaryNodes candidate) == secondRootHere)) →
    findPartnerScan firstLinks firstBoundaryNodes firstRootHere excludeIndex cands
      = findPartnerScan secondLinks secondBoundaryNodes secondRootHere excludeIndex cands
  | [], _ => rfl
  | head :: tail, rootEqualityAgrees => by
      show (if head != excludeIndex
              && unionFindRootOf firstLinks (natListGetAt firstBoundaryNodes head) == firstRootHere
              then head else findPartnerScan firstLinks firstBoundaryNodes firstRootHere excludeIndex tail)
         = (if head != excludeIndex
              && unionFindRootOf secondLinks (natListGetAt secondBoundaryNodes head) == secondRootHere
              then head else findPartnerScan secondLinks secondBoundaryNodes secondRootHere excludeIndex tail)
      rw [rootEqualityAgrees head (List.Mem.head _),
        findPartnerScan_congr firstLinks firstBoundaryNodes firstRootHere
          secondLinks secondBoundaryNodes secondRootHere excludeIndex tail
          (fun candidate inTail => rootEqualityAgrees candidate (List.Mem.tail _ inTail))]

/-- A `DiagramType` is determined by its four fields. `cases` on the structures and on each field equality
(recursor / `Eq.rec` only), so `propext`-free. -/
theorem diagramType_eq_of_fields {first second : DiagramType}
    (bottomCountsAgree : first.bottomCount = second.bottomCount)
    (topCountsAgree : first.topCount = second.topCount)
    (partnersAgree : first.partner = second.partner)
    (loopsAgree : first.loops = second.loops) : first = second := by
  cases first; cases second
  cases bottomCountsAgree; cases topCountsAgree; cases partnersAgree; cases loopsAgree
  rfl

/-! ## The factoring theorem — `extractArc` is determined by the boundary-connectivity view

This is the de-risking insight, made rigorous: the extracted `FullArcStructure` is a function of the
RENAMING-INVARIANT boundary-connectivity data (the same-component relation on the in-range boundary indices, the
per-port internal cup/cap counts, the loop count, the open-wire count, the cup/cap event-node counts).  The actual
node ids — the only thing the two Godement run orders disagree on by allocation order — never leak into it.  Every
`findPartnerScan` / `extractDiagram` / `List.map` read-off is discharged here. -/

/-- ★ **Renaming-invariance of `extractArc`.**  Two arc states sharing the boundary-connectivity view extract to
the same `FullArcStructure`.  The partner matching closes by `findPartnerScan_congr` + `listMapCongr` over the
agreeing same-component relation (`relationAgrees`); the internal cup/cap counts by `listMapCongr` over the
agreeing per-port counts; the open-wire / loop / event-node counts are direct.  All indices used sit in
`List.range (bottomCount + openWires.length)`, so the in-range hypotheses suffice (`mem_range_imp_lt`). -/
theorem extractArc_eq_of_partitionView (bottomCount : Nat) (firstState secondState : ArcWireState)
    (lengthsAgree : firstState.openWires.length = secondState.openWires.length)
    (loopsAgree : firstState.loops = secondState.loops)
    (cupEventCountsAgree : firstState.cupEventNodes.length = secondState.cupEventNodes.length)
    (capEventCountsAgree : firstState.capEventNodes.length = secondState.capEventNodes.length)
    (relationAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        boundarySameComponent bottomCount firstState firstIndex secondIndex
          = boundarySameComponent bottomCount secondState firstIndex secondIndex)
    (cupPortCountsAgree : ∀ index, index < bottomCount + firstState.openWires.length →
        internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
            firstState.cupEventNodes index
          = internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
            secondState.cupEventNodes index)
    (capPortCountsAgree : ∀ index, index < bottomCount + firstState.openWires.length →
        internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
            firstState.capEventNodes index
          = internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
            secondState.capEventNodes index) :
    extractArc bottomCount firstState = extractArc bottomCount secondState := by
  have totalsAgree : bottomCount + firstState.openWires.length = bottomCount + secondState.openWires.length := by
    rw [lengthsAgree]
  apply fullArcStructure_eq_of_fields
  · apply diagramType_eq_of_fields
    · rfl
    · exact lengthsAgree
    · show (List.range (bottomCount + firstState.openWires.length)).map
              (partnerIndexOf firstState.links (boundaryNodesOf bottomCount firstState)
                (bottomCount + firstState.openWires.length))
         = (List.range (bottomCount + secondState.openWires.length)).map
              (partnerIndexOf secondState.links (boundaryNodesOf bottomCount secondState)
                (bottomCount + secondState.openWires.length))
      rw [← totalsAgree]
      apply listMapCongr
      intro candidateIndex candidateInRange
      have candidateBelow : candidateIndex < bottomCount + firstState.openWires.length :=
        mem_range_imp_lt candidateInRange
      show findPartnerScan firstState.links (boundaryNodesOf bottomCount firstState)
            (unionFindRootOf firstState.links
              (natListGetAt (boundaryNodesOf bottomCount firstState) candidateIndex))
            candidateIndex (List.range (bottomCount + firstState.openWires.length))
         = findPartnerScan secondState.links (boundaryNodesOf bottomCount secondState)
            (unionFindRootOf secondState.links
              (natListGetAt (boundaryNodesOf bottomCount secondState) candidateIndex))
            candidateIndex (List.range (bottomCount + firstState.openWires.length))
      apply findPartnerScan_congr
      intro scanIndex scanInRange
      exact relationAgrees scanIndex candidateIndex (mem_range_imp_lt scanInRange) candidateBelow
    · exact loopsAgree
  · exact cupEventCountsAgree
  · exact capEventCountsAgree
  · show (List.range (bottomCount + firstState.openWires.length)).map
            (internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
              firstState.cupEventNodes)
       = (List.range (bottomCount + secondState.openWires.length)).map
            (internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
              secondState.cupEventNodes)
    rw [← totalsAgree]
    apply listMapCongr
    intro index indexInRange
    exact cupPortCountsAgree index (mem_range_imp_lt indexInRange)
  · show (List.range (bottomCount + firstState.openWires.length)).map
            (internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
              firstState.capEventNodes)
       = (List.range (bottomCount + secondState.openWires.length)).map
            (internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
              secondState.capEventNodes)
    rw [← totalsAgree]
    apply listMapCongr
    intro index indexInRange
    exact capPortCountsAgree index (mem_range_imp_lt indexInRange)

/-! ## The residual restated at the connectivity level -/

/-- Two arc states share the **boundary-connectivity view** (w.r.t. `bottomCount`): equal open-wire count, equal
loop count, the same boundary same-component relation on the in-range indices, and the same per-port internal
cup/cap counts.  This is the renaming-invariant data `extractArc_eq_of_partitionView` shows determines the
extract — the event-node COUNTS are deliberately NOT bundled here (they are order-independent and discharged in
the reduction), so this predicate is exactly the connectivity content. -/
def SameArcPartition (bottomCount : Nat) (firstState secondState : ArcWireState) : Prop :=
  firstState.openWires.length = secondState.openWires.length
  ∧ firstState.loops = secondState.loops
  ∧ (∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        boundarySameComponent bottomCount firstState firstIndex secondIndex
          = boundarySameComponent bottomCount secondState firstIndex secondIndex)
  ∧ (∀ index, index < bottomCount + firstState.openWires.length →
        internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
            firstState.cupEventNodes index
          = internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
            secondState.cupEventNodes index)
  ∧ (∀ index, index < bottomCount + firstState.openWires.length →
        internalEventCountAt firstState.links (boundaryNodesOf bottomCount firstState)
            firstState.capEventNodes index
          = internalEventCountAt secondState.links (boundaryNodesOf bottomCount secondState)
            secondState.capEventNodes index)

/-- `SameArcPartition` plus the (order-independent, separately-dischargeable) event-node count agreements give
equal extracts — the factoring theorem packaged against the connectivity predicate. -/
theorem extractArc_eq_of_sameArcPartition (bottomCount : Nat) (firstState secondState : ArcWireState)
    (samePartition : SameArcPartition bottomCount firstState secondState)
    (cupEventCountsAgree : firstState.cupEventNodes.length = secondState.cupEventNodes.length)
    (capEventCountsAgree : firstState.capEventNodes.length = secondState.capEventNodes.length) :
    extractArc bottomCount firstState = extractArc bottomCount secondState := by
  obtain ⟨lengthsAgree, loopsAgree, relationAgrees, cupPortCountsAgree, capPortCountsAgree⟩ := samePartition
  exact extractArc_eq_of_partitionView bottomCount firstState secondState lengthsAgree loopsAgree
    cupEventCountsAgree capEventCountsAgree relationAgrees cupPortCountsAgree capPortCountsAgree

/-- ★ **The Godement arc residual, restated at the connectivity level.**  Transposing the two
horizontally-disjoint Godement blocks (`cellAlphaUpper` and `cellBeta`, with their context shifts) leaves the two
run orders `SameArcPartition` from every starting state — i.e. they induce the SAME boundary same-component
relation, per-port cup/cap counts, loop count and open-wire count.  This is the pure "disjoint-support merge
sequences commute on the connectivity closure" statement, with all of `extractArc`'s read-off layer stripped by
`extractArc_eq_of_partitionView`. -/
def ArcGodementSamePartition (signature : ModeSignature) : Prop :=
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
    SameArcPartition bottomCount
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-! ## The reduction and assembly -/

/-- ★ **The connectivity residual implies the parent's `ArcGodementPartitionCommute`.**  The three
partition-determined extract fields come from `extractArc_eq_of_sameArcPartition` applied to the connectivity
residual; the cup/cap event-node COUNTS owed by the factoring are discharged unconditionally here — each run
order accumulates `state.…Count + cellAlpha + cellAlphaUpper + cellBeta + cellBetaUpper + (count in rest)`
(`processArcSpine_*EventNodes_length` + `runArcCell_*EventNodes_length`), equal under transposing
`cellAlphaUpper`/`cellBeta` by `Nat.add_right_comm`. -/
theorem arcGodementPartitionCommute_of_sameArcPartition {signature : ModeSignature}
    (samePartition : ArcGodementSamePartition signature) : ArcGodementPartitionCommute signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state
  have extractsAgree := extractArc_eq_of_sameArcPartition bottomCount _ _
    (samePartition cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state)
    (by simp only [processArcSpine_cupEventNodes_length, runArcCell_cupEventNodes_length]
        rw [Nat.add_right_comm (state.cupEventNodes.length + cellAlpha.cupCount)
          cellAlphaUpper.cupCount cellBeta.cupCount])
    (by simp only [processArcSpine_capEventNodes_length, runArcCell_capEventNodes_length]
        rw [Nat.add_right_comm (state.capEventNodes.length + cellAlpha.capCount)
          cellAlphaUpper.capCount cellBeta.capCount])
  exact ⟨congrArg FullArcStructure.diagram extractsAgree,
         congrArg FullArcStructure.internalCupCounts extractsAgree,
         congrArg FullArcStructure.internalCapCounts extractsAgree⟩

/-- ★ **The connectivity residual yields the parent's full state-parametric `godementInvariant`.**  Composing the
reduction with the parent's `arcGodementCommute_of_partitionCommute` and `arcGodementInvariant_of_commute`: this
is exactly the `godementInvariant` argument `decidableTwoCellConvFull_of` consumes, now gated on the connectivity
residual alone. -/
theorem arcGodementInvariant_of_sameArcPartition {signature : ModeSignature}
    (samePartition : ArcGodementSamePartition signature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) (state : ArcWireState)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    extractArcAfterProcessing bottomCount state firstList
      = extractArcAfterProcessing bottomCount state secondList :=
  arcGodementInvariant_of_commute
    (arcGodementCommute_of_partitionCommute (arcGodementPartitionCommute_of_sameArcPartition samePartition))
    bottomCount state step

/-- ★ **`arcStructureOf` soundness under the COMPLETE `TwoCellConvFull`, gated on the connectivity residual
alone.**  Composing the reduction with the parent's `arcStructureOf_sound_of_arcGodementPartitionCommute`: given
only `ArcGodementSamePartition` — that the two Godement run orders induce the same boundary connectivity closure —
`arcStructureOf` is invariant under every structural law, all whisker functoriality, every congruence, and the
interchange step.  The soundness residual is now the bare disjoint-merge connectivity commutation; the extract
read-off (`findPartnerScan` / `extractDiagram` / `List.map`) and the cup/cap counts are discharged. -/
theorem arcStructureOf_sound_of_arcGodementSamePartition {signature : ModeSignature}
    (samePartition : ArcGodementSamePartition signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell :=
  arcStructureOf_sound_of_arcGodementPartitionCommute
    (arcGodementPartitionCommute_of_sameArcPartition samePartition) convFull

/-! ## Honesty markers -/

/-- **Honesty marker — `extractArc` renaming-invariance is PROVED.**  `extractArc_eq_of_partitionView` shows the
extracted `FullArcStructure` is a function of the boundary-connectivity view alone (the in-range same-component
relation, the per-port cup/cap counts, the loop / open-wire / event-node counts) — the fresh node-ids the two
Godement run orders allocate in different orders are union-find internals invisible to the extract.  This is the
de-risking insight the prior node-id-simulation passes drowned in: the `findPartnerScan` / `extractDiagram` /
`List.map` read-off layer is discharged once and for all.  `= true`. -/
def fxMode_hasArcPartitionViewFactoring : Bool := true

/-- **Honesty marker — the Godement arc residual is REDUCED to the connectivity closure.**
`arcGodementPartitionCommute_of_sameArcPartition` proves the parent's `ArcGodementPartitionCommute` from
`ArcGodementSamePartition` (with the cup/cap event counts discharged), and
`arcStructureOf_sound_of_arcGodementSamePartition` / `arcGodementInvariant_of_sameArcPartition` re-gate the full
`TwoCellConvFull` soundness and the parent's `godementInvariant` on that single connectivity statement.  The
residual is stripped of all extract read-off — only the pure partition data remains.  `= true`. -/
def fxMode_hasArcGodementReducedToSamePartition : Bool := true

/-- **Honesty marker — the boundary-connectivity closure commutation is the standing obligation.**
`ArcGodementSamePartition` states that transposing the two horizontally-disjoint Godement blocks preserves the
boundary same-component relation, the per-port cup/cap counts, the loop count and the open-wire count: the bare
"disjoint-support merge sequences commute on the connected-components closure" fact (Mazurkiewicz independence on
the union-find).  TRUE (the blocks act on disjoint port-supports) and computationally confirmed on the obstruction
witnesses; its general zero-axiom proof is the one remaining soundness obligation, shared with the matching
route's `fxMode_hasMatchingGodementIndependenceProof`.  This does NOT flip the parent's
`fxMode_hasArcPartitionCommuteProof`; it provides the strictly more atomic route to it.  `= false`. -/
def fxMode_hasArcSamePartitionProof : Bool := false

end FX1Poly.Tier0
