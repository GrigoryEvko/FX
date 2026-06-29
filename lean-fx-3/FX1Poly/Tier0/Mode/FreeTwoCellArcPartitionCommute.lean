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

/-! ## ★ The over-quantified residual is FALSE — freshness is a NECESSARY precondition

The decisive correction this pass lands.  `ArcGodementSamePartition` — and, identically shaped, the parent's
`ArcGodementPartitionCommute` / `ArcGodementCommute` and the root `godementInvariant` — quantifies over EVERY
`ArcWireState`, including states whose `links` / `openWires` name node ids `≥ nextFresh`.  At such an adversarial
state the two Godement run orders allocate their fresh cup/cap legs into SWAPPED id ranges (`cellAlphaUpper`'s
range and `cellBeta`'s range trade places between the orders), so a pre-existing `links` edge that names one of
those soon-to-be-allocated ids attaches a boundary node to whichever block allocates it FIRST — `cellAlphaUpper`
(a LEFT-region port) in the redex, `cellBeta` (a RIGHT-region port) in the reduct.  The boundary same-component
relation then DIFFERS between the two orders, so `SameArcPartition` fails.

Concretely (`cellAlpha = id`, `cellAlphaUpper = cellBeta = unit` cups, `cellBetaUpper = id`, all accumulators
trivial) at `state.links = [(100, 0)]`, `state.nextFresh = 100`, `bottomCount = 3`: bottom port `0` shares a
component with top port `3` in the redex order but NOT in the reduct order.  The prior passes' "computationally
confirmed on the obstruction witnesses" only ever checked FRESH witnesses; the unconditional statement is FALSE,
and no zero-axiom proof of it exists — this section EXHIBITS the refutation. -/

/-- `cellAlpha` for the refuting instance: the identity 2-cell on `id_base` (a no-op block). -/
private def arcRefuteIdentityBase : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) := RawTwoCellExpr.id _

/-- `cellBetaUpper` for the refuting instance: the identity 2-cell on `left·right`. -/
private def arcRefuteIdentityLeftRight : RawTwoCellExpr adjunctionModeSignature
    adjunctionLeftThenRight adjunctionLeftThenRight := RawTwoCellExpr.id _

/-- The trivial base accumulator `id_base`, used for every whisker context in the refuting instance. -/
private def arcRefuteNilBase : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- The **adversarial** starting state: a `links` edge `(100, 0)` naming id `100 = nextFresh`, which the FIRST
cup allocates as its left leg — thereby pre-attaching that fresh leg to bottom boundary node `0`. -/
private def arcRefuteAdversarialState : ArcWireState := ArcWireState.mk [] [(100, 0)] 100 0 [] []

/-- The REDEX middle state of the refuting Godement instance: `cellAlpha`, then `cellAlphaUpper` (cup, left
context `id_base`), then `cellBeta` (cup, left context `id_base·(left·right)`), then `cellBetaUpper`. -/
private def arcRefuteRedexState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell arcRefuteAdversarialState arcRefuteNilBase (composePath arcRefuteNilBase arcRefuteNilBase)
        arcRefuteIdentityBase)
      arcRefuteNilBase (composePath arcRefuteNilBase arcRefuteNilBase) adjunctionUnitTwoCell)
    (composePath arcRefuteNilBase adjunctionLeftThenRight) arcRefuteNilBase adjunctionUnitTwoCell)
    (composePath arcRefuteNilBase adjunctionLeftThenRight) arcRefuteNilBase arcRefuteIdentityLeftRight

/-- The REDUCT middle state — `cellBeta` and `cellAlphaUpper` transposed with their context shift. -/
private def arcRefuteReductState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell arcRefuteAdversarialState arcRefuteNilBase (composePath arcRefuteNilBase arcRefuteNilBase)
        arcRefuteIdentityBase)
      (composePath arcRefuteNilBase arcRefuteNilBase) arcRefuteNilBase adjunctionUnitTwoCell)
    arcRefuteNilBase (composePath adjunctionLeftThenRight arcRefuteNilBase) adjunctionUnitTwoCell)
    (composePath arcRefuteNilBase adjunctionLeftThenRight) arcRefuteNilBase arcRefuteIdentityLeftRight

/-- The boundary same-component relation DISAGREES at boundary indices `(0, 3)` — bottom port `0` shares top port
`3`'s component in the redex order but not the reduct order.  Kernel-decided on the two small concrete states
(NOT the large parallel cells the perf rule warns against), so it is `decide`-discharged and zero-axiom. -/
private theorem arcRefute_boundarySameComponent_differs :
    boundarySameComponent 3 arcRefuteRedexState 0 3 ≠ boundarySameComponent 3 arcRefuteReductState 0 3 := by
  decide

/-- ★ **The over-quantified Godement arc residual is FALSE.**  `ArcGodementSamePartition adjunctionModeSignature`
would force the two Godement run orders to agree on the boundary same-component relation from EVERY starting
state; instantiated at the adversarial state above it forces `boundarySameComponent 3 redex 0 3 =
boundarySameComponent 3 reduct 0 3`, contradicting `arcRefute_boundarySameComponent_differs`.  Hence the
unconditional residual is unprovable (it is refuted), and `fxMode_hasArcSamePartitionProof` cannot be flipped: the
statement needs a FRESHNESS precondition (`ArcGodementSamePartitionFresh` below).  Zero-axiom (the only
nontrivial step is `decide` on the two small concrete states). -/
theorem not_arcGodementSamePartition :
    ¬ ArcGodementSamePartition adjunctionModeSignature := by
  intro everyStateAgrees
  have samePartitionAtAdversary := everyStateAgrees arcRefuteIdentityBase adjunctionUnitTwoCell
    adjunctionUnitTwoCell arcRefuteIdentityLeftRight arcRefuteNilBase arcRefuteNilBase [] 3
    arcRefuteAdversarialState
  exact arcRefute_boundarySameComponent_differs
    (samePartitionAtAdversary.2.2.1 0 3 (by decide) (by decide))

/-! ## The corrected residual — `ArcGodementSamePartition` under the FRESHNESS precondition

The refutation pins the exact missing hypothesis: every node id the starting state mentions must lie strictly
below `nextFresh` (so the cups'/caps' fresh allocations are disjoint from the pre-existing connectivity), and the
bottom-boundary ports `0 … bottomCount-1` must likewise lie below `nextFresh`.  Under that precondition — which is
PRECISELY the reachable-state invariant of the actual fold (the initial state `mk (range n) [] n 0 [] []`
satisfies it, and each `stepArcAtom` preserves it) — the disjoint-block commutation holds (computationally
confirmed on fresh, slack-fresh, and even fresh-but-cyclic starting states: both run orders inherit the same
pre-existing part verbatim, only the disjoint fresh ranges are renamed).  This is the genuine, well-formed
residual; it is TRUE but its general zero-axiom proof is the standing combinatorial obligation (a renaming
simulation between the two run orders' disjoint fresh id ranges over the union-find). -/

/-- An arc state is **fresh** when every node id it mentions — open wires, both endpoints of every union-find
edge, and every cup/cap event node — lies strictly below `nextFresh`.  This is the invariant the matching/arc
fold maintains from its initial state; the Godement refutation (`not_arcGodementSamePartition`) shows it is
exactly what `ArcGodementSamePartition` silently assumed. -/
def ArcStateFresh (state : ArcWireState) : Prop :=
  (∀ wire ∈ state.openWires, wire < state.nextFresh)
    ∧ (∀ edge ∈ state.links, edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh)
    ∧ (∀ node ∈ state.cupEventNodes, node < state.nextFresh)
    ∧ (∀ node ∈ state.capEventNodes, node < state.nextFresh)

/-- The canonical INITIAL arc state `mk (range bottomCount) [] bottomCount 0 [] []` is fresh: its open wires are
exactly `0 … bottomCount-1` (all `< bottomCount = nextFresh`, via the propext-free `mem_range_imp_lt`), and its
links / event lists are empty.  So the consumer's starting state already meets the corrected residual's
precondition. -/
theorem arcStateFresh_initial (bottomCount : Nat) :
    ArcStateFresh (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) := by
  refine ⟨fun _ wireInRange => mem_range_imp_lt wireInRange, ?_, ?_, ?_⟩
  · intro _ edgeInNil; cases edgeInNil
  · intro _ nodeInNil; cases nodeInNil
  · intro _ nodeInNil; cases nodeInNil

/-- ★ **The corrected (freshness-conditioned) Godement arc residual.**  Identical to `ArcGodementSamePartition`
except it assumes the starting `state` is `ArcStateFresh` and that the bottom-boundary width does not exceed
`nextFresh` — exactly the reachable-state invariant the refutation shows is required.  Under these hypotheses the
two Godement run orders land `SameArcPartition` (computationally confirmed; the general zero-axiom proof is the
standing obligation).  Discharging THIS — not the unconditional `ArcGodementSamePartition`, which is false
(`not_arcGodementSamePartition`) — together with threading `ArcStateFresh` through the consumer chain (the
read-only `arcTraceInvariant_of_godementInvariant` and the `godementInvariant` shape), closes the keystone's
soundness side. -/
def ArcGodementSamePartitionFresh (signature : ModeSignature) : Prop :=
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
    ArcStateFresh state → bottomCount ≤ state.nextFresh →
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

/-- **Honesty marker — the UNCONDITIONAL boundary-connectivity commutation is FALSE, not merely unproven.**
`ArcGodementSamePartition` quantifies over EVERY `ArcWireState`; `not_arcGodementSamePartition` REFUTES it
zero-axiom at an adversarial state whose `links` names an id `≥ nextFresh` (the two run orders then attach a
boundary node to the differently-positioned block that allocates that id first — bottom port `0` shares top port
`3`'s component in the redex but not the reduct).  The prior "TRUE, computationally confirmed" claim held only for
FRESH witnesses.  So this flag stays `false` — and CANNOT honestly be flipped, because the statement it names is
false; the provable, well-formed replacement is `fxMode_hasArcGodementSamePartitionFreshProof` below.  `= false`. -/
def fxMode_hasArcSamePartitionProof : Bool := false

/-- **Honesty marker — the over-quantified residual is REFUTED (zero-axiom).**  `not_arcGodementSamePartition`
proves `¬ ArcGodementSamePartition adjunctionModeSignature` by exhibiting the adversarial state at which the two
Godement run orders disagree on `boundarySameComponent` (bottom port `0` vs top port `3`).  This overturns the
standing belief that the residual was true-but-unproven: as STATED (over all states) it is false, so the
keystone's soundness residual must be re-stated with a freshness precondition.  The same over-quantification
afflicts the parent's `ArcGodementPartitionCommute` / `ArcGodementCommute` and the root `godementInvariant`
(all `∀ state`).  `= true`. -/
def fxMode_hasArcSamePartitionRefuted : Bool := true

/-- **Honesty marker — the FRESHNESS-conditioned residual is the genuine standing obligation.**
`ArcGodementSamePartitionFresh` re-states the commutation under `ArcStateFresh state` (every mentioned id
`< nextFresh`) and `bottomCount ≤ nextFresh` — the reachable-state invariant the fold maintains
(`arcStateFresh_initial` anchors the canonical initial state).  Under it the disjoint-block commutation is TRUE
(computationally confirmed on fresh, slack-fresh and fresh-but-cyclic starting states).  Its general zero-axiom
proof — a renaming simulation between the two orders' disjoint fresh id ranges over the union-find — is the one
remaining soundness obligation; closing it ALSO requires threading `ArcStateFresh` through the read-only consumer
chain (`arcTraceInvariant_of_godementInvariant` and the `godementInvariant` shape), which the parent must wire.
`= false`. -/
def fxMode_hasArcGodementSamePartitionFreshProof : Bool := false

end FX1Poly.Tier0
