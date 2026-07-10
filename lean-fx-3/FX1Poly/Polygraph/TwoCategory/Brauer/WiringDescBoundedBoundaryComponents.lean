import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable

/-! # BRAUER-MIDDLE r6 B1 (partial) — the T-DISJOINT invariant `boundedBoundaryComponents`, its seed base case,
and non-vacuity (the forest-cardinality "no over-connection" core of R3-A-TAGCORR)

The r5 ledger (`Brauer/WiringDescStandardFoldR5Ledger.lean`) decomposed R3-A-TAGCORR into four sub-legs and
named **T-DISJOINT** (`fxBrauer_hasTagCorrDisjoint`, below) as THE long pole: for every boundary pair NOT matched by
`d` the fold state's `matchingSameComponent` is `false`; equivalently every union-find component of the fold holds
`<= 2` boundary indices — a forest-cardinality invariant with NO Frobenius analog (the Frobenius target is
all-connected, so this direction was vacuous there).

This round ships the invariant as a machine-checked Lean object with its base case and non-vacuity, following the
shipped precedent `ArcOpenEndsDiscipline` (`WalkingAdjunction/ArcOpenEndsDiscipline.lean`), whose own STATEMENT layer
(discipline + seed) shipped while the `stepCupArc` / `stepCapArc` preservation stayed named rungs.  Concretely:

  * **`boundedBoundaryComponents`** — the invariant, in the relational "no three distinct boundary indices share a
    component" form (propext-free: a `Nat` `BEq` of roots under the hood via `matchingSameComponent`).  This is the
    positive, `d`-free statement of the CONVERSE that `Brauer/WiringDescConnectivityMono.lean:104-113` explicitly
    flags as "the freshness-conditioned window-locality half — NOT built here, still the standing brick".

  * **`boundedBoundaryComponents_seed`** — the SEED base case for ARBITRARY `bottomCount`: the fresh seed
    (`brauerSeed bottomCount`, every strand an identity through-strand) satisfies the invariant.  Each component
    `{ k }` holds exactly the two boundary indices `k` (bottom port) and `bottomCount + k` (its top slot) — the
    correct through-strand double-count — so no three distinct indices share.  A finite pigeonhole ("three distinct
    indices cannot all lie in the two-element preimage `{ v, bottomCount + v }`") over the append read-off of
    `List.range bottomCount ++ List.range bottomCount`.

  * **Non-vacuity** — (i) a `decide` REFUTATION `boundedBoundaryComponents_notMonochromatic`: an over-connected
    state (three boundary nodes in one component) genuinely FAILS the invariant, so the predicate constrains; and
    (ii) mixed-diagram computational FIRINGS `boundedBoundaryComponentsCheck_crossing` / `_capThenCup`: the bounded
    triple-check returns `true` on the crossing and the cap-then-cup fold states (diagrams the identity seed does
    not cover).

## Honest scope — what this round does NOT ship (the named residual)

The three per-atom PRESERVATION steps (`boundedBoundaryComponents` survives `stepWiring` at `cupWiring` /
`capWiring` / `crossingWiring`), the `processBrauer` FOLD lift, and the EXTRACTION consequence
(cardinality + T-CONNECT => `partnerIndexOf` reads the `d`-partner) are UNBUILT.  They carry the real per-atom
labor the recon named: general-position `natListInsertAt` / `natListRemoveManyAt` boundary-index arithmetic, a
threaded freshness invariant, and (the novel leg, no Frobenius analog) the crossing case's two-join count
bookkeeping via `isSameComponent_unionFindJoin` (`FreeTwoCell/MatchingComponentAlgebra.lean:86`).  So
`fxBrauer_hasTagCorrDisjoint` STAYS `false`; the roundtrip flags and masters stay `false`; #2013 does NOT close.

Raw Lean 4 + Init; structural recursion + a local `Nat.le.dest`-free `Nat` kit, no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range + append plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLengthBBC : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthBBC count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthBBC (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthBBC count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_pastBBC : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_pastBBC count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_belowBBC : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_belowBBC count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_pastBBC count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_belowBBC (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_belowBBC count [] index indexBelow

private theorem natListGetAt_appendLeftBBC :
    (leftList rightList : List Nat) → (index : Nat) → index < leftList.length →
    natListGetAt (leftList ++ rightList) index = natListGetAt leftList index
  | [], _, _, indexBelow => absurd indexBelow (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, rightList, index + 1, indexBelow =>
      natListGetAt_appendLeftBBC rest rightList index (Nat.lt_of_succ_lt_succ indexBelow)

private theorem natListGetAt_appendAddBBC :
    (leftList rightList : List Nat) → (offset : Nat) →
    natListGetAt (leftList ++ rightList) (leftList.length + offset) = natListGetAt rightList offset
  | [], rightList, offset => by
      show natListGetAt rightList (0 + offset) = natListGetAt rightList offset
      rw [Nat.zero_add]
  | head :: rest, rightList, offset => by
      show natListGetAt (head :: (rest ++ rightList)) ((rest.length + 1) + offset) = natListGetAt rightList offset
      rw [Nat.add_right_comm rest.length 1 offset]
      show natListGetAt (rest ++ rightList) (rest.length + offset) = natListGetAt rightList offset
      exact natListGetAt_appendAddBBC rest rightList offset

/-- With no links, every node is its own root (a per-file copy; the union-find has no parent edges). -/
private theorem unionFindRootOf_nilBBC (node : Nat) : unionFindRootOf [] node = node := rfl

/-! ## The T-DISJOINT invariant -/

/-- ★ **The forest-cardinality invariant (T-DISJOINT), relational "no over-connection" form.**  No three distinct
boundary indices of `state` (indices `< bottomCount + state.openWires.length`, reading the boundary node list
`List.range bottomCount ++ state.openWires` exactly as `extractDiagram` does) all pairwise share a union-find
component — equivalently every component holds at most two boundary indices.  Stated through `matchingSameComponent`
(a `Nat` `BEq` of roots), so `propext`-free.  This is the positive, `d`-free statement of the boundary
window-locality CONVERSE named as the standing brick in `Brauer/WiringDescConnectivityMono.lean`. -/
def boundedBoundaryComponents (bottomCount : Nat) (state : WireState) : Prop :=
  ∀ firstIndex secondIndex thirdIndex,
    firstIndex < bottomCount + state.openWires.length →
    secondIndex < bottomCount + state.openWires.length →
    thirdIndex < bottomCount + state.openWires.length →
    firstIndex ≠ secondIndex → firstIndex ≠ thirdIndex → secondIndex ≠ thirdIndex →
    ¬ (matchingSameComponent bottomCount state firstIndex secondIndex = true
        ∧ matchingSameComponent bottomCount state firstIndex thirdIndex = true)

/-! ## The seed base case -/

/-- The seed boundary same-component relation reduces to a raw `Nat` `BEq` of the append read-offs (the seed has no
links, so every root is the node itself). -/
private theorem seed_matchingSameComponent (bottomCount firstIndex secondIndex : Nat) :
    matchingSameComponent bottomCount (brauerSeed bottomCount) firstIndex secondIndex
      = (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
          == natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex) := by
  show (unionFindRootOf [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex)
        == unionFindRootOf [] (natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex))
      = (natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
          == natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex)
  rw [unionFindRootOf_nilBBC, unionFindRootOf_nilBBC]

/-- Each seed boundary index `< bottomCount + bottomCount` lies in the two-element preimage of its read-off value:
either it IS the value (a bottom port `< bottomCount`) or it is `bottomCount +` the value (its top slot). -/
private theorem seedBoundaryNode_cases (bottomCount index : Nat) (indexBelow : index < bottomCount + bottomCount) :
    index = natListGetAt (List.range bottomCount ++ List.range bottomCount) index
      ∨ index = bottomCount + natListGetAt (List.range bottomCount ++ List.range bottomCount) index := by
  cases Nat.lt_or_ge index bottomCount with
  | inl below =>
      apply Or.inl
      rw [natListGetAt_appendLeftBBC (List.range bottomCount) (List.range bottomCount) index
            (by rw [rangeLengthBBC]; exact below),
        rangeGetAt_belowBBC bottomCount index below]
  | inr atLeast =>
      apply Or.inr
      obtain ⟨gap, gapEq⟩ := Nat.le.dest atLeast
      have gapBelow : gap < bottomCount := by
        have widened : bottomCount + gap < bottomCount + bottomCount := by rw [gapEq]; exact indexBelow
        exact Nat.lt_of_add_lt_add_left widened
      have nodeRead : natListGetAt (List.range bottomCount ++ List.range bottomCount) index = gap := by
        rw [← gapEq,
          show bottomCount + gap = (List.range bottomCount).length + gap from
            congrArg (· + gap) (rangeLengthBBC bottomCount).symm,
          natListGetAt_appendAddBBC (List.range bottomCount) (List.range bottomCount) gap,
          rangeGetAt_belowBBC bottomCount gap gapBelow]
      rw [nodeRead, gapEq]

/-- ★ **The SEED base case of T-DISJOINT.**  The fresh seed `brauerSeed bottomCount` (all strands identity
through-strands) satisfies `boundedBoundaryComponents`: with no links every component is a singleton node read by
exactly the two boundary indices `k` and `bottomCount + k`, so three distinct boundary indices cannot pairwise share
a component.  A finite pigeonhole ("three distinct indices cannot fit the two-element preimage
`{ value, bottomCount + value }`") over the seed read-off; each contradiction is derived from distinctness through
the shared read-off value, so it needs no case on `bottomCount`. -/
theorem boundedBoundaryComponents_seed (bottomCount : Nat) :
    boundedBoundaryComponents bottomCount (brauerSeed bottomCount) := by
  intro firstIndex secondIndex thirdIndex firstBelow secondBelow thirdBelow
    firstNeSecond firstNeThird secondNeThird sameConjunction
  obtain ⟨sameFirstSecond, sameFirstThird⟩ := sameConjunction
  have lengthEq : (brauerSeed bottomCount).openWires.length = bottomCount := rangeLengthBBC bottomCount
  rw [lengthEq] at firstBelow secondBelow thirdBelow
  rw [seed_matchingSameComponent] at sameFirstSecond sameFirstThird
  have readFirstSecond :
      natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
        = natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex :=
    of_decide_eq_true sameFirstSecond
  have readFirstThird :
      natListGetAt (List.range bottomCount ++ List.range bottomCount) firstIndex
        = natListGetAt (List.range bottomCount ++ List.range bottomCount) thirdIndex :=
    of_decide_eq_true sameFirstThird
  have readSecondThird :
      natListGetAt (List.range bottomCount ++ List.range bottomCount) secondIndex
        = natListGetAt (List.range bottomCount ++ List.range bottomCount) thirdIndex :=
    readFirstSecond.symm.trans readFirstThird
  rcases seedBoundaryNode_cases bottomCount firstIndex firstBelow with firstLow | firstHigh
  · rcases seedBoundaryNode_cases bottomCount secondIndex secondBelow with secondLow | secondHigh
    · exact firstNeSecond (firstLow.trans (readFirstSecond.trans secondLow.symm))
    · rcases seedBoundaryNode_cases bottomCount thirdIndex thirdBelow with thirdLow | thirdHigh
      · exact firstNeThird (firstLow.trans (readFirstThird.trans thirdLow.symm))
      · exact secondNeThird
          (secondHigh.trans ((congrArg (bottomCount + ·) readSecondThird).trans thirdHigh.symm))
  · rcases seedBoundaryNode_cases bottomCount secondIndex secondBelow with secondLow | secondHigh
    · rcases seedBoundaryNode_cases bottomCount thirdIndex thirdBelow with thirdLow | thirdHigh
      · exact secondNeThird (secondLow.trans (readSecondThird.trans thirdLow.symm))
      · exact firstNeThird
          (firstHigh.trans ((congrArg (bottomCount + ·) readFirstThird).trans thirdHigh.symm))
    · exact firstNeSecond
        (firstHigh.trans ((congrArg (bottomCount + ·) readFirstSecond).trans secondHigh.symm))

/-! ## Non-vacuity — the refutation -/

/-- A deliberately over-connected state at `bottomCount = 0`: three open wires `0, 1, 2` collapsed into ONE
union-find component. -/
def overConnectedProbeState : WireState :=
  { openWires := [0, 1, 2], links := [(0, 2), (1, 2)], nextFresh := 3, loops := 0 }

/-- ★ **The invariant genuinely constrains (refutation).**  The over-connected state fails
`boundedBoundaryComponents`: its three boundary indices `0, 1, 2` all pairwise share the one component, witnessing a
violating triple.  So the predicate is not vacuously true. -/
theorem boundedBoundaryComponents_notMonochromatic :
    ¬ boundedBoundaryComponents 0 overConnectedProbeState := by
  intro invariantHolds
  exact invariantHolds 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩

/-! ## Non-vacuity — mixed-diagram computational firings

The invariant's body is an unbounded `Nat` `forall`, so it is not itself decidable; the bounded triple-check below
is the decidable proxy that a genuine mixed diagram (not the identity seed) satisfies the `<= 2`-per-component
discipline over its boundary range. -/

/-- The decidable per-triple predicate: distinct indices are NOT all pairwise same-component. -/
def sameComponentTripleFree (bottomCount : Nat) (state : WireState) (firstIndex secondIndex thirdIndex : Nat) :
    Bool :=
  !(!(firstIndex == secondIndex) && !(firstIndex == thirdIndex) && !(secondIndex == thirdIndex)
    && matchingSameComponent bottomCount state firstIndex secondIndex
    && matchingSameComponent bottomCount state firstIndex thirdIndex)

/-- The bounded triple-check: `sameComponentTripleFree` holds for every triple below `bound` — the decidable proxy
for `boundedBoundaryComponents` over the range `[0, bound)`. -/
def boundedBoundaryComponentsCheck (bottomCount : Nat) (state : WireState) (bound : Nat) : Bool :=
  (List.range bound).all fun firstIndex =>
    (List.range bound).all fun secondIndex =>
      (List.range bound).all fun thirdIndex =>
        sameComponentTripleFree bottomCount state firstIndex secondIndex thirdIndex

/-- ★ **Mixed-diagram firing (crossing).**  A single crossing over two bottom strands (partner `[3, 2, 1, 0]`, the
two arcs `0-3` and `1-2`) passes the bounded triple-check over its full boundary range `[0, 4)` — a mixed diagram
the identity seed does not cover. -/
theorem boundedBoundaryComponentsCheck_crossing :
    boundedBoundaryComponentsCheck 2 (processBrauer (brauerSeed 2) [crossingAt 0]) 4 = true := by decide

/-- ★ **Mixed-diagram firing (cap then cup).**  Capping the two bottom strands then cupping a fresh pair (partner
`[1, 0, 3, 2]`, one closed bottom arc and one fresh top arc) passes the bounded triple-check over `[0, 4)`. -/
theorem boundedBoundaryComponentsCheck_capThenCup :
    boundedBoundaryComponentsCheck 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]) 4 = true := by decide

/-! ## B1 — THE CAP preservation: the core pigeonhole over a single boundary join

The crux of T-DISJOINT.  `stepCap` merges the two boundary ports at the window into one component and drops them
from the boundary view; the shipped cap read-kit (`Brauer/`-external `MatchingBoundaryReads.lean`) supplies the
total boundary reindex `capBoundaryReindex`, its range transport, and the join-legs-as-boundary-reads form.  The new
content is the finite pigeonhole: after joining the two ports `leftPort`, `rightPort`, no THREE distinct boundary
indices (each distinct from both ports) can pairwise share a component, because each such index is forced (by the
before-invariant applied through the port) to sit with `leftPort` or `rightPort`, and 3-into-2 forces two into the
same port's class — a forbidden triple `{ port, x, y }` at the BEFORE state. -/

/-- Same-component is symmetric at the matching view (a `dsimp`-thin wrapper of `isSameComponent_symm`). -/
private theorem matchingSameComponent_symmBBC (bottomCount : Nat) (state : WireState)
    (firstIndex secondIndex : Nat) :
    matchingSameComponent bottomCount state firstIndex secondIndex
      = matchingSameComponent bottomCount state secondIndex firstIndex := by
  show (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
        == unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
      = (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)
        == unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
  exact isSameComponent_symm state.links _ _

/-- The flat-disjunction expansion of the after-join same-component view at BOUNDARY reads, restated in
`matchingSameComponent` terms (the port reads are the join legs).  Every disjunct is defeq to a
`matchingSameComponent` at the before state. -/
private theorem matchingSameComponent_afterJoinBBC (bottomCount : Nat) (state : WireState)
    (forest : isUnionFindForest state.links) (leftPort rightPort firstIndex secondIndex : Nat) :
    isSameComponent
        (unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
          (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
        (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)
      = (matchingSameComponent bottomCount state firstIndex secondIndex
          || (matchingSameComponent bottomCount state leftPort firstIndex
              && matchingSameComponent bottomCount state rightPort secondIndex)
          || (matchingSameComponent bottomCount state leftPort secondIndex
              && matchingSameComponent bottomCount state firstIndex rightPort)) :=
  isSameComponent_unionFindJoin state.links forest
    (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
    (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort)
    (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
    (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)

/-- **The port fact.**  Given a star of two after-join same-component links centred at `centerIdx`, that centre is
connected AT THE BEFORE STATE to `leftPort` or `rightPort`.  Proof: if it were connected to neither, both bridging
disjuncts collapse, so the after-links reduce to the before-links on the star, giving a forbidden before-triple
`{ centerIdx, otherA, otherB }`. -/
private theorem portOfStarBBC (bottomCount : Nat) (state : WireState)
    (forest : isUnionFindForest state.links)
    (bounded : boundedBoundaryComponents bottomCount state)
    (leftPort rightPort centerIdx otherA otherB : Nat)
    (centerRange : centerIdx < bottomCount + state.openWires.length)
    (otherARange : otherA < bottomCount + state.openWires.length)
    (otherBRange : otherB < bottomCount + state.openWires.length)
    (centerNeA : centerIdx ≠ otherA) (centerNeB : centerIdx ≠ otherB) (aNeB : otherA ≠ otherB)
    (sameCenterA : isSameComponent
        (unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
          (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
        (natListGetAt (matchingBoundaryNodes bottomCount state) centerIdx)
        (natListGetAt (matchingBoundaryNodes bottomCount state) otherA) = true)
    (sameCenterB : isSameComponent
        (unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
          (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
        (natListGetAt (matchingBoundaryNodes bottomCount state) centerIdx)
        (natListGetAt (matchingBoundaryNodes bottomCount state) otherB) = true) :
    matchingSameComponent bottomCount state leftPort centerIdx = true
      ∨ matchingSameComponent bottomCount state rightPort centerIdx = true := by
  cases hleft : matchingSameComponent bottomCount state leftPort centerIdx with
  | true => exact Or.inl rfl
  | false =>
      cases hright : matchingSameComponent bottomCount state rightPort centerIdx with
      | true => exact Or.inr rfl
      | false =>
          exfalso
          rw [matchingSameComponent_afterJoinBBC bottomCount state forest leftPort rightPort centerIdx otherA,
            hleft, matchingSameComponent_symmBBC bottomCount state centerIdx rightPort, hright,
            Bool.false_and, Bool.and_false, Bool.or_false, Bool.or_false] at sameCenterA
          rw [matchingSameComponent_afterJoinBBC bottomCount state forest leftPort rightPort centerIdx otherB,
            hleft, matchingSameComponent_symmBBC bottomCount state centerIdx rightPort, hright,
            Bool.false_and, Bool.and_false, Bool.or_false, Bool.or_false] at sameCenterB
          exact bounded centerIdx otherA otherB centerRange otherARange otherBRange centerNeA centerNeB aNeB
            ⟨sameCenterA, sameCenterB⟩

/-- ★ **The core pigeonhole.**  After joining `leftPort`/`rightPort`, no three distinct boundary indices (each
distinct from both ports) pairwise share a component.  The star at the first index is completed to a full pairwise
triple; each index's port fact places it with `leftPort` or `rightPort`; 3-into-2 forces two into a shared port,
yielding a forbidden before-triple `{ port, x, y }`.  Generator-independent — the single-join heart the cap consumes
directly. -/
private theorem noThreeSharingAfterJoin (bottomCount : Nat) (state : WireState)
    (forest : isUnionFindForest state.links)
    (bounded : boundedBoundaryComponents bottomCount state)
    (leftPort rightPort firstIndex secondIndex thirdIndex : Nat)
    (leftRange : leftPort < bottomCount + state.openWires.length)
    (rightRange : rightPort < bottomCount + state.openWires.length)
    (firstRange : firstIndex < bottomCount + state.openWires.length)
    (secondRange : secondIndex < bottomCount + state.openWires.length)
    (thirdRange : thirdIndex < bottomCount + state.openWires.length)
    (firstNeLeft : firstIndex ≠ leftPort) (firstNeRight : firstIndex ≠ rightPort)
    (secondNeLeft : secondIndex ≠ leftPort) (secondNeRight : secondIndex ≠ rightPort)
    (thirdNeLeft : thirdIndex ≠ leftPort) (thirdNeRight : thirdIndex ≠ rightPort)
    (firstNeSecond : firstIndex ≠ secondIndex) (firstNeThird : firstIndex ≠ thirdIndex)
    (secondNeThird : secondIndex ≠ thirdIndex)
    (sameFirstSecond : isSameComponent
        (unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
          (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
        (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex) = true)
    (sameFirstThird : isSameComponent
        (unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
          (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
        (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount state) thirdIndex) = true) :
    False := by
  have forestJoin := isUnionFindForest_unionFindJoin state.links
    (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
    (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort) forest
  have sameSecondFirst : isSameComponent
      (unionFindJoin state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
        (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
      (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex) = true := by
    rw [isSameComponent_symm]; exact sameFirstSecond
  have sameThirdFirst : isSameComponent
      (unionFindJoin state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
        (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
      (natListGetAt (matchingBoundaryNodes bottomCount state) thirdIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex) = true := by
    rw [isSameComponent_symm]; exact sameFirstThird
  have sameSecondThird : isSameComponent
      (unionFindJoin state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
        (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
      (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount state) thirdIndex) = true :=
    isSameComponent_trans _ _ _ _ sameSecondFirst sameFirstThird
  have sameThirdSecond : isSameComponent
      (unionFindJoin state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) leftPort)
        (natListGetAt (matchingBoundaryNodes bottomCount state) rightPort))
      (natListGetAt (matchingBoundaryNodes bottomCount state) thirdIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex) = true := by
    rw [isSameComponent_symm]; exact sameSecondThird
  have portFirst := portOfStarBBC bottomCount state forest bounded leftPort rightPort firstIndex secondIndex thirdIndex
    firstRange secondRange thirdRange firstNeSecond firstNeThird secondNeThird sameFirstSecond sameFirstThird
  have portSecond := portOfStarBBC bottomCount state forest bounded leftPort rightPort secondIndex firstIndex thirdIndex
    secondRange firstRange thirdRange (Ne.symm firstNeSecond) secondNeThird firstNeThird sameSecondFirst sameSecondThird
  have portThird := portOfStarBBC bottomCount state forest bounded leftPort rightPort thirdIndex firstIndex secondIndex
    thirdRange firstRange secondRange (Ne.symm firstNeThird) (Ne.symm secondNeThird) firstNeSecond sameThirdFirst sameThirdSecond
  rcases portFirst with aLeft | aRight
  · rcases portSecond with bLeft | bRight
    · exact bounded leftPort firstIndex secondIndex leftRange firstRange secondRange
        (Ne.symm firstNeLeft) (Ne.symm secondNeLeft) firstNeSecond ⟨aLeft, bLeft⟩
    · rcases portThird with cLeft | cRight
      · exact bounded leftPort firstIndex thirdIndex leftRange firstRange thirdRange
          (Ne.symm firstNeLeft) (Ne.symm thirdNeLeft) firstNeThird ⟨aLeft, cLeft⟩
      · exact bounded rightPort secondIndex thirdIndex rightRange secondRange thirdRange
          (Ne.symm secondNeRight) (Ne.symm thirdNeRight) secondNeThird ⟨bRight, cRight⟩
  · rcases portSecond with bLeft | bRight
    · rcases portThird with cLeft | cRight
      · exact bounded leftPort secondIndex thirdIndex leftRange secondRange thirdRange
          (Ne.symm secondNeLeft) (Ne.symm thirdNeLeft) secondNeThird ⟨bLeft, cLeft⟩
      · exact bounded rightPort firstIndex thirdIndex rightRange firstRange thirdRange
          (Ne.symm firstNeRight) (Ne.symm thirdNeRight) firstNeThird ⟨aRight, cRight⟩
    · exact bounded rightPort firstIndex secondIndex rightRange firstRange secondRange
        (Ne.symm firstNeRight) (Ne.symm secondNeRight) firstNeSecond ⟨aRight, bRight⟩

/-! ### The cap boundary-reindex avoids the two ports, and is injective -/

/-- The cap reindex never hits the left port `bottomCount + position` (below the window it is strictly less; at or
above it is at least two more). -/
private theorem capBoundaryReindex_ne_leftPort (bottomCount position index : Nat) :
    capBoundaryReindex bottomCount position index ≠ bottomCount + position := by
  show (if index < bottomCount + position then index else index + 2) ≠ bottomCount + position
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl below => rw [if_pos below]; exact Nat.ne_of_lt below
  | inr atLeast =>
      rw [if_neg (Nat.not_lt.mpr atLeast)]
      exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_lt atLeast (Nat.lt_succ_of_lt (Nat.lt_add_one index))))

/-- The cap reindex never hits the right port `bottomCount + (position + 1)`. -/
private theorem capBoundaryReindex_ne_rightPort (bottomCount position index : Nat) :
    capBoundaryReindex bottomCount position index ≠ bottomCount + (position + 1) := by
  show (if index < bottomCount + position then index else index + 2) ≠ bottomCount + (position + 1)
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl below =>
      rw [if_pos below]
      exact Nat.ne_of_lt (Nat.lt_trans below (Nat.add_lt_add_left (Nat.lt_add_one position) bottomCount))
  | inr atLeast =>
      rw [if_neg (Nat.not_lt.mpr atLeast)]
      have shifted : bottomCount + (position + 1) ≤ index + 1 :=
        (Nat.add_assoc bottomCount position 1) ▸ Nat.add_le_add_right atLeast 1
      exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_lt shifted (Nat.lt_add_one (index + 1))))

/-- The cap reindex is injective (strictly monotone across the window threshold). -/
private theorem capBoundaryReindex_inj (bottomCount position firstIndex secondIndex : Nat)
    (heq : capBoundaryReindex bottomCount position firstIndex
        = capBoundaryReindex bottomCount position secondIndex) :
    firstIndex = secondIndex := by
  show firstIndex = secondIndex
  have heq' : (if firstIndex < bottomCount + position then firstIndex else firstIndex + 2)
      = (if secondIndex < bottomCount + position then secondIndex else secondIndex + 2) := heq
  cases Nat.lt_or_ge firstIndex (bottomCount + position) with
  | inl firstBelow =>
      cases Nat.lt_or_ge secondIndex (bottomCount + position) with
      | inl secondBelow => rw [if_pos firstBelow, if_pos secondBelow] at heq'; exact heq'
      | inr secondAtLeast =>
          rw [if_pos firstBelow, if_neg (Nat.not_lt.mpr secondAtLeast)] at heq'
          exact (Nat.lt_irrefl firstIndex (Nat.lt_of_lt_of_le firstBelow
            (heq'.symm ▸ Nat.le_trans secondAtLeast (Nat.le_add_right secondIndex 2)))).elim
  | inr firstAtLeast =>
      cases Nat.lt_or_ge secondIndex (bottomCount + position) with
      | inl secondBelow =>
          rw [if_neg (Nat.not_lt.mpr firstAtLeast), if_pos secondBelow] at heq'
          exact (Nat.lt_irrefl secondIndex (Nat.lt_of_lt_of_le secondBelow
            (heq' ▸ Nat.le_trans firstAtLeast (Nat.le_add_right firstIndex 2)))).elim
      | inr secondAtLeast =>
          rw [if_neg (Nat.not_lt.mpr firstAtLeast), if_neg (Nat.not_lt.mpr secondAtLeast)] at heq'
          exact Nat.succ.inj (Nat.succ.inj heq')

/-- The cap reindex sends distinct indices to distinct images. -/
private theorem capBoundaryReindex_ne (bottomCount position firstIndex secondIndex : Nat)
    (distinct : firstIndex ≠ secondIndex) :
    capBoundaryReindex bottomCount position firstIndex ≠ capBoundaryReindex bottomCount position secondIndex :=
  fun imagesEq => distinct (capBoundaryReindex_inj bottomCount position firstIndex secondIndex imagesEq)

/-- The post-cap boundary same-component view factors as an after-join view over the reindexed boundary reads (the
join legs are the two ports, the reads reindexed by `capBoundaryReindex`). -/
private theorem matchingSameComponent_stepCap_reindex (bottomCount : Nat) (state : WireState)
    (position firstIndex secondIndex : Nat) (windowInRange : position + 2 ≤ state.openWires.length) :
    matchingSameComponent bottomCount (stepCap state position) firstIndex secondIndex
      = isSameComponent
          (unionFindJoin state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1))))
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (capBoundaryReindex bottomCount position firstIndex))
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (capBoundaryReindex bottomCount position secondIndex)) := by
  show (unionFindRootOf (stepCap state position).links
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) firstIndex)
        == unionFindRootOf (stepCap state position).links
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) secondIndex))
      = (unionFindRootOf
          (unionFindJoin state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1))))
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (capBoundaryReindex bottomCount position firstIndex))
        == unionFindRootOf
          (unionFindJoin state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
            (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1))))
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (capBoundaryReindex bottomCount position secondIndex)))
  rw [stepCap_links_eq_unionFindJoin_boundaryReads bottomCount state position,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount state position firstIndex windowInRange,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount state position secondIndex windowInRange]

/-- ★ **THE CAP preservation.**  `boundedBoundaryComponents` survives an in-range `stepCap`: the post-cap view
factors through the cap reindex over the single boundary join of the two window ports, and the core pigeonhole
(`noThreeSharingAfterJoin`) rejects any three distinct post-cap boundary indices sharing a component.  Requires the
window in range (`position + 2 ≤ openWires.length`, load-bearing per `WiringDescReachable.lean`) and the forest
invariant. -/
theorem boundedBoundaryComponents_stepCap (bottomCount : Nat) (state : WireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state) :
    boundedBoundaryComponents bottomCount (stepCap state position) := by
  intro firstIndex secondIndex thirdIndex firstBelow secondBelow thirdBelow
    firstNeSecond firstNeThird secondNeThird sameConjunction
  obtain ⟨sameFirstSecond, sameFirstThird⟩ := sameConjunction
  rw [matchingSameComponent_stepCap_reindex bottomCount state position firstIndex secondIndex windowInRange]
    at sameFirstSecond
  rw [matchingSameComponent_stepCap_reindex bottomCount state position firstIndex thirdIndex windowInRange]
    at sameFirstThird
  have leftRange : bottomCount + position < bottomCount + state.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_add_one position)) windowInRange) bottomCount
  have rightRange : bottomCount + (position + 1) < bottomCount + state.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_add_one (position + 1)) windowInRange) bottomCount
  exact noThreeSharingAfterJoin bottomCount state forest bounded
    (bottomCount + position) (bottomCount + (position + 1))
    (capBoundaryReindex bottomCount position firstIndex)
    (capBoundaryReindex bottomCount position secondIndex)
    (capBoundaryReindex bottomCount position thirdIndex)
    leftRange rightRange
    (capBoundaryReindex_lt_ofNewRange bottomCount state position firstIndex windowInRange firstBelow)
    (capBoundaryReindex_lt_ofNewRange bottomCount state position secondIndex windowInRange secondBelow)
    (capBoundaryReindex_lt_ofNewRange bottomCount state position thirdIndex windowInRange thirdBelow)
    (capBoundaryReindex_ne_leftPort bottomCount position firstIndex)
    (capBoundaryReindex_ne_rightPort bottomCount position firstIndex)
    (capBoundaryReindex_ne_leftPort bottomCount position secondIndex)
    (capBoundaryReindex_ne_rightPort bottomCount position secondIndex)
    (capBoundaryReindex_ne_leftPort bottomCount position thirdIndex)
    (capBoundaryReindex_ne_rightPort bottomCount position thirdIndex)
    (capBoundaryReindex_ne bottomCount position firstIndex secondIndex firstNeSecond)
    (capBoundaryReindex_ne bottomCount position firstIndex thirdIndex firstNeThird)
    (capBoundaryReindex_ne bottomCount position secondIndex thirdIndex secondNeThird)
    sameFirstSecond sameFirstThird

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the T-DISJOINT invariant, its seed, and non-vacuity are SHIPPED (r6 B1 partial).**
`boundedBoundaryComponents` is the forest-cardinality "no over-connection" invariant (the `d`-free positive
statement of the boundary window-locality converse named as the standing brick in
`Brauer/WiringDescConnectivityMono.lean`); `boundedBoundaryComponents_seed` proves it at the fresh seed for
ARBITRARY `bottomCount` via the through-strand double-count pigeonhole; and non-vacuity is witnessed both ways — the
`decide` refutation `boundedBoundaryComponents_notMonochromatic` (an over-connected state fails it) and the
mixed-diagram firings `boundedBoundaryComponentsCheck_{crossing,capThenCup}` (real diagrams pass the bounded
triple-check).  `= true`. -/
def fxBrauer_hasBoundedBoundaryComponentsSeed : Bool := true

/-- ★ **Honesty marker — THE CAP preservation is SHIPPED (r7 B1, the crux).**
`boundedBoundaryComponents_stepCap`: `boundedBoundaryComponents` survives an in-range `stepCap` — the post-cap
boundary view factors through the shipped total cap reindex `capBoundaryReindex` (its range transport
`capBoundaryReindex_lt_ofNewRange`, the join-legs-as-boundary-reads `stepCap_links_eq_unionFindJoin_boundaryReads`),
and the new single-join pigeonhole `noThreeSharingAfterJoin` rejects any three distinct post-cap boundary indices
sharing a component: each index is forced by the before-invariant (through the merged port) into `leftPort`'s or
`rightPort`'s class, and 3-into-2 produces a forbidden before-triple.  Zero-axiom (the reindex-injectivity uses
`Nat.succ.inj`, NOT the `propext`-leaking `Nat.add_right_cancel`).  Requires the window in range
(`position + 2 <= openWires.length`) + the forest invariant.  `= true`. -/
def fxBrauer_hasCapPreservation : Bool := true

/-- **Honesty marker — the FULL T-DISJOINT leg (`R3-A-TAGCORR` long pole) is NOT closed.**  THE CAP preservation is
now SHIPPED (`boundedBoundaryComponents_stepCap`, see `fxBrauer_hasCapPreservation`).  Still UNBUILT this round: the
CUP + CROSSING per-atom preservation (cup: the confined FRESH join `unionFindJoin links nextFresh (nextFresh+1)`, the
reads reindex UP by two past the window — the natural `index - 2` reindex hits the `propext` subtraction wall
[`Nat.sub_add_cancel` leaks], so an ADDITIVE recover-witness `index = oldIdx + 2` is required; crossing: the novel
two-join transposition with no Frobenius analog), the `stepWiring _ _ capWiring = stepCap` bridge (conditional on the
window in range: `natListRemoveManyAt _ _ 2 = natListRemoveTwoAt` + `natListInsertAt _ _ [] = id` + the single-arc
`stepWiringArcs` fold), the `processBrauer` FOLD lift (ride `brauerStateConditions_processBrauer` +
`processBrauer_wireListDistinct`, dispatching on the generator kind with a per-atom window-in-range predicate), and
the EXTRACTION consequence (cardinality + T-CONNECT => `partnerIndexOf` reads the `d`-partner, a
`findPartnerScan`-uniqueness lemma).  So T-DISJOINT stays open, the roundtrip flags and masters stay `false`, and
#2013 does not close — a ROUTE / totality gap, never a truth gap (Lehrer-Zhang arXiv:1207.5889 Thm 2.6).
`= false`. -/
def fxBrauer_hasTagCorrDisjoint : Bool := false

end FX1Poly.Polygraph
