import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPortReconnection
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderSuffixCongruence

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

/-! ## B2 — THE CUP preservation: the confined FRESH join (no total reindex; a fresh-leg case split)

`stepCup` splices two FRESH legs `nextFresh`, `nextFresh + 1` into the open-wire window and joins them.  Both join
endpoints are fresh (disconnected from every old node), so the join is INVISIBLE to old boundary reads and the fresh
pair forms its own two-element component.  The forward old->new boundary reindex is exactly the cap's
`capBoundaryReindex` (old indices shift UP by two past the window — the two leg slots), so no `index - 2`
subtraction is needed (the propext subtraction wall the r7 marker flagged is avoided by using the shipped ADDITIVE
past-block read).  The preservation is a case split: an index reading a fresh leg forces every co-component index to
read a fresh leg too, and there are only two such indices (a pigeonhole); the all-old case transports to the base
invariant through the fresh-inert join. -/

/-- Every boundary node read is below the fresh counter (range values `< bottomCount <= nextFresh`, open wires
`< nextFresh`, past-the-end default `0 < nextFresh`). -/
private theorem boundaryRead_lt_nextFreshBBC (bottomCount : Nat) (state : WireState)
    (fresh : WiringDescStateFresh state) (bottomLe : bottomCount ≤ state.nextFresh)
    (nfPos : 0 < state.nextFresh) (index : Nat) :
    natListGetAt (matchingBoundaryNodes bottomCount state) index < state.nextFresh := by
  cases Nat.lt_or_ge index bottomCount with
  | inl belowBottom =>
      show natListGetAt (List.range bottomCount ++ state.openWires) index < state.nextFresh
      rw [natListGetAt_appendLeftBBC (List.range bottomCount) state.openWires index
          (by rw [rangeLengthBBC]; exact belowBottom),
        rangeGetAt_belowBBC bottomCount index belowBottom]
      exact Nat.lt_of_lt_of_le belowBottom bottomLe
  | inr atLeastBottom =>
      obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
      rw [matchingBoundaryNodes_getAt_top bottomCount state offset]
      exact natListGetAt_lt state.nextFresh nfPos state.openWires offset fresh.1

/-- A base fresh node (`nextFresh`) is disconnected from every old node (`< nextFresh`): its root is itself, the old
node's root stays below. -/
private theorem sameComponent_nextFresh_old_falseBBC (state : WireState) (fresh : WiringDescStateFresh state)
    (oldNode : Nat) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent state.links state.nextFresh oldNode = false := by
  show (unionFindRootOf state.links state.nextFresh == unionFindRootOf state.links oldNode) = false
  rw [unionFindRootOf_eq_self_ofFresh state.nextFresh state.links
      (fun edge edgeMem => (fresh.2 edge edgeMem).1) state.nextFresh (Nat.le_refl state.nextFresh)]
  exact decide_eq_false (fun rootEq =>
    Nat.ne_of_lt (unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeMem => (fresh.2 edge edgeMem).2) oldNode oldBelow) rootEq.symm)

/-- The base fresh RIGHT leg (`nextFresh + 1`) is likewise disconnected from every old node. -/
private theorem sameComponent_nextFreshSucc_old_falseBBC (state : WireState) (fresh : WiringDescStateFresh state)
    (oldNode : Nat) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent state.links (state.nextFresh + 1) oldNode = false := by
  show (unionFindRootOf state.links (state.nextFresh + 1) == unionFindRootOf state.links oldNode) = false
  rw [unionFindRootOf_eq_self_ofFresh state.nextFresh state.links
      (fun edge edgeMem => (fresh.2 edge edgeMem).1) (state.nextFresh + 1) (Nat.le_succ state.nextFresh)]
  exact decide_eq_false (fun rootEq =>
    Nat.ne_of_lt (Nat.lt_succ_of_lt (unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeMem => (fresh.2 edge edgeMem).2) oldNode oldBelow)) rootEq.symm)

/-- The cup's fresh join is INVISIBLE to two old nodes: joining `nextFresh`/`nextFresh + 1` leaves the
same-component view on old probes equal to the base view (both bridging disjuncts collapse — the fresh legs are
disconnected from either old node). -/
private theorem cupJoin_inert_oldBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (nodeA nodeB : Nat)
    (aBelow : nodeA < state.nextFresh) (bBelow : nodeB < state.nextFresh) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) nodeA nodeB
      = isSameComponent state.links nodeA nodeB := by
  rw [isSameComponent_unionFindJoin state.links forest state.nextFresh (state.nextFresh + 1) nodeA nodeB,
    sameComponent_nextFresh_old_falseBBC state fresh nodeA aBelow,
    sameComponent_nextFresh_old_falseBBC state fresh nodeB bBelow]
  cases isSameComponent state.links nodeA nodeB <;> rfl

/-- The cup's fresh LEFT leg (`nextFresh`) is disconnected, under the join, from every old node. -/
private theorem cupJoin_nextFresh_old_falseBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (oldNode : Nat) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) state.nextFresh oldNode
      = false := by
  rw [isSameComponent_unionFindJoin state.links forest state.nextFresh (state.nextFresh + 1)
      state.nextFresh oldNode,
    sameComponent_nextFresh_old_falseBBC state fresh oldNode oldBelow,
    sameComponent_nextFreshSucc_old_falseBBC state fresh oldNode oldBelow]
  cases isSameComponent state.links state.nextFresh state.nextFresh <;> rfl

/-- The cup's fresh RIGHT leg (`nextFresh + 1`) is disconnected, under the join, from every old node. -/
private theorem cupJoin_nextFreshSucc_old_falseBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (oldNode : Nat) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) (state.nextFresh + 1) oldNode
      = false := by
  rw [isSameComponent_unionFindJoin state.links forest state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 1) oldNode,
    sameComponent_nextFreshSucc_old_falseBBC state fresh oldNode oldBelow,
    sameComponent_nextFresh_old_falseBBC state fresh oldNode oldBelow]
  cases isSameComponent state.links state.nextFresh (state.nextFresh + 1) <;> rfl

/-- ★ **The post-cup boundary read classification.**  Every post-cup boundary index either reads the LEFT fresh leg
(`= bottomCount + position`), the RIGHT fresh leg (`= bottomCount + (position + 1)`), or an OLD node whose pre-cup
index is `capBoundaryReindex bottomCount position pre` (the same additive up-shift the cap uses).  No index-`- 2`
subtraction — the past-block reindex is stated additively through the shipped cup read. -/
private theorem cupReadClassBBC (bottomCount : Nat) (state : WireState) (position : Nat)
    (positionLe : position ≤ state.openWires.length)
    (index : Nat) (indexRange : index < bottomCount + state.openWires.length + 2) :
    (index = bottomCount + position
       ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) index = state.nextFresh)
    ∨ (index = bottomCount + (position + 1)
       ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) index = state.nextFresh + 1)
    ∨ (∃ pre, pre < bottomCount + state.openWires.length
        ∧ index = capBoundaryReindex bottomCount position pre
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) index
            = natListGetAt (matchingBoundaryNodes bottomCount state) pre) := by
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl belowWindow =>
      refine Or.inr (Or.inr ⟨index, ?_, ?_, ?_⟩)
      · exact Nat.lt_of_lt_of_le belowWindow (Nat.add_le_add_left positionLe bottomCount)
      · show index = (if index < bottomCount + position then index else index + 2)
        rw [if_pos belowWindow]
      · cases Nat.lt_or_ge index bottomCount with
        | inl belowBottom =>
            exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount (stepCup state position) state index
              belowBottom
        | inr atLeastBottom =>
            obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
            exact matchingBoundaryNodes_stepCup_getAt_below bottomCount state position offset
              (Nat.lt_of_add_lt_add_left belowWindow)
              (Nat.lt_of_lt_of_le (Nat.lt_of_add_lt_add_left belowWindow) positionLe)
  | inr atWindow =>
      cases Nat.lt_or_ge index (bottomCount + position + 2) with
      | inl belowPlus2 =>
          cases Nat.lt_or_ge index (bottomCount + position + 1) with
          | inl belowPlus1 =>
              have indexEq : index = bottomCount + position :=
                Nat.le_antisymm (Nat.le_of_lt_succ belowPlus1) atWindow
              subst indexEq
              exact Or.inl ⟨rfl,
                matchingBoundaryNodes_stepCup_getAt_leftLeg bottomCount state position positionLe⟩
          | inr atPlus1 =>
              have indexEq : index = bottomCount + position + 1 :=
                Nat.le_antisymm (Nat.le_of_lt_succ belowPlus2) atPlus1
              subst indexEq
              refine Or.inr (Or.inl ⟨?_, ?_⟩)
              · rw [Nat.add_assoc bottomCount position 1]
              · rw [Nat.add_assoc bottomCount position 1]
                exact matchingBoundaryNodes_stepCup_getAt_rightLeg bottomCount state position positionLe
      | inr atPlus2 =>
          obtain ⟨offset, rfl⟩ := Nat.le.dest atPlus2
          have indexAsPast : bottomCount + position + 2 + offset = bottomCount + (position + offset + 2) := by
            rw [Nat.add_assoc bottomCount position 2, Nat.add_assoc bottomCount (position + 2) offset,
              Nat.add_right_comm position 2 offset]
          refine Or.inr (Or.inr ⟨bottomCount + (position + offset), ?_, ?_, ?_⟩)
          · have hlt : bottomCount + (position + offset + 2) < bottomCount + state.openWires.length + 2 :=
              indexAsPast ▸ indexRange
            rw [← Nat.add_assoc bottomCount (position + offset) 2] at hlt
            exact Nat.lt_of_add_lt_add_right hlt
          · rw [indexAsPast]
            show bottomCount + (position + offset + 2)
              = (if bottomCount + (position + offset) < bottomCount + position then bottomCount + (position + offset)
                 else bottomCount + (position + offset) + 2)
            rw [if_neg (Nat.not_lt.mpr (Nat.add_le_add_left (Nat.le_add_right position offset) bottomCount)),
              Nat.add_assoc bottomCount (position + offset) 2]
          · rw [indexAsPast]
            exact matchingBoundaryNodes_stepCup_getAt_pastBlock bottomCount state position offset positionLe

/-- ★ **THE CUP preservation.**  `boundedBoundaryComponents` survives an in-range `stepCup`.  Every post-cup
boundary index reads a fresh leg (`nextFresh` / `nextFresh + 1`) or an old node (`cupReadClassBBC`); the fresh join
is invisible to old nodes (`cupJoin_inert_oldBBC`) and the fresh pair is disconnected from every old node
(`cupJoin_nextFresh{,Succ}_old_falseBBC`).  An index reading a fresh leg forces every co-component index to read a
fresh leg too, and only two indices do (a pigeonhole); the all-old case transports the star to the base invariant
through the fresh-inert join and the injective up-shift `capBoundaryReindex`.  Requires the four reachable-state
conditions (fresh / forest / positive counter / bottom-fits) plus the cup window in range
(`position <= openWires.length`). -/
theorem boundedBoundaryComponents_stepCup (bottomCount : Nat) (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (bottomLe : bottomCount ≤ state.nextFresh)
    (positionLe : position ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state) :
    boundedBoundaryComponents bottomCount (stepCup state position) := by
  intro firstIndex secondIndex thirdIndex firstBelow secondBelow thirdBelow
    firstNeSecond firstNeThird secondNeThird sameConjunction
  obtain ⟨sameFirstSecond, sameFirstThird⟩ := sameConjunction
  rw [stepCup_openWiresLength state position, ← Nat.add_assoc bottomCount state.openWires.length 2]
    at firstBelow secondBelow thirdBelow
  have classFirst := cupReadClassBBC bottomCount state position positionLe firstIndex firstBelow
  have classSecond := cupReadClassBBC bottomCount state position positionLe secondIndex secondBelow
  have classThird := cupReadClassBBC bottomCount state position positionLe thirdIndex thirdBelow
  have sfs : isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) secondIndex) = true :=
    sameFirstSecond
  have sft : isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) thirdIndex) = true :=
    sameFirstThird
  rcases classFirst with ⟨hidxF, hrF⟩ | ⟨hidxF, hrF⟩ | ⟨preF, preFrange, hidxF, hrF⟩
  · -- first reads the LEFT fresh leg
    rw [hrF] at sfs sft
    rcases classSecond with ⟨hidxS, _⟩ | ⟨hidxS, _⟩ | ⟨preS, _, _, hrS⟩
    · exact firstNeSecond (hidxF.trans hidxS.symm)
    · rcases classThird with ⟨hidxT, _⟩ | ⟨hidxT, _⟩ | ⟨preT, _, _, hrT⟩
      · exact firstNeThird (hidxF.trans hidxT.symm)
      · exact secondNeThird (hidxS.trans hidxT.symm)
      · rw [hrT, cupJoin_nextFresh_old_falseBBC state forest fresh _
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preT)] at sft
        exact Bool.noConfusion sft
    · rw [hrS, cupJoin_nextFresh_old_falseBBC state forest fresh _
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preS)] at sfs
      exact Bool.noConfusion sfs
  · -- first reads the RIGHT fresh leg
    rw [hrF] at sfs sft
    rcases classSecond with ⟨hidxS, _⟩ | ⟨hidxS, _⟩ | ⟨preS, _, _, hrS⟩
    · rcases classThird with ⟨hidxT, _⟩ | ⟨hidxT, _⟩ | ⟨preT, _, _, hrT⟩
      · exact secondNeThird (hidxS.trans hidxT.symm)
      · exact firstNeThird (hidxF.trans hidxT.symm)
      · rw [hrT, cupJoin_nextFreshSucc_old_falseBBC state forest fresh _
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preT)] at sft
        exact Bool.noConfusion sft
    · exact firstNeSecond (hidxF.trans hidxS.symm)
    · rw [hrS, cupJoin_nextFreshSucc_old_falseBBC state forest fresh _
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preS)] at sfs
      exact Bool.noConfusion sfs
  · -- first reads an OLD node
    rw [hrF] at sfs sft
    rcases classSecond with ⟨_, hrS⟩ | ⟨_, hrS⟩ | ⟨preS, preSrange, hidxS, hrS⟩
    · rw [hrS, isSameComponent_symm, cupJoin_nextFresh_old_falseBBC state forest fresh _
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)] at sfs
      exact Bool.noConfusion sfs
    · rw [hrS, isSameComponent_symm, cupJoin_nextFreshSucc_old_falseBBC state forest fresh _
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)] at sfs
      exact Bool.noConfusion sfs
    · rw [hrS, cupJoin_inert_oldBBC state forest fresh _ _
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)
        (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preS)] at sfs
      rcases classThird with ⟨_, hrT⟩ | ⟨_, hrT⟩ | ⟨preT, preTrange, hidxT, hrT⟩
      · rw [hrT, isSameComponent_symm, cupJoin_nextFresh_old_falseBBC state forest fresh _
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)] at sft
        exact Bool.noConfusion sft
      · rw [hrT, isSameComponent_symm, cupJoin_nextFreshSucc_old_falseBBC state forest fresh _
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)] at sft
        exact Bool.noConfusion sft
      · rw [hrT, cupJoin_inert_oldBBC state forest fresh _ _
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preF)
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos preT)] at sft
        have preFneS : preF ≠ preS := fun heq => firstNeSecond
          (hidxF.trans ((congrArg (capBoundaryReindex bottomCount position) heq).trans hidxS.symm))
        have preFneT : preF ≠ preT := fun heq => firstNeThird
          (hidxF.trans ((congrArg (capBoundaryReindex bottomCount position) heq).trans hidxT.symm))
        have preSneT : preS ≠ preT := fun heq => secondNeThird
          (hidxS.trans ((congrArg (capBoundaryReindex bottomCount position) heq).trans hidxT.symm))
        exact bounded preF preS preT preFrange preSrange preTrange preFneS preFneT preSneT ⟨sfs, sft⟩

/-! ## B2 — THE CROSSING preservation: the two-join transposition transport

`stepWiring _ _ crossingWiring` fires two joins, `join (join links in0 (nextFresh+1)) in1 nextFresh`, whose SECOND
endpoints (`nextFresh+1`, `nextFresh`) are FRESH.  So the crossing is invisible to two OLD boundary reads, and the
two window slots read the fresh outputs which reconnect (transposed) to the OLD window strands `in0`, `in1`.  The
after-view is the before-view precomposed with the window transposition `tau` — a bijective relabel, not a
cardinality count.  These node-level lemmas compute the crossing's same-component view on every read pair; the
transposition-transport and the preservation ride them. -/

/-- A fresh pair `nextFresh`, `nextFresh + 1` is never already connected (both out of support, distinct). -/
private theorem sameComponent_freshPairBBC (state : WireState) (fresh : WiringDescStateFresh state) :
    isSameComponent state.links state.nextFresh (state.nextFresh + 1) = false :=
  isSameComponent_freshPair_eq_false state.nextFresh state.links
    (fun edge edgeMem => (fresh.2 edge edgeMem).1) state.nextFresh (Nat.le_refl state.nextFresh)

/-- Same-component left congruence: joined heads see the same neighbours. -/
private theorem isSameComponent_congrLeftBBC (links : List (Nat × Nat)) (nodeA nodeB nodeC : Nat)
    (sameAB : isSameComponent links nodeA nodeB = true) :
    isSameComponent links nodeA nodeC = isSameComponent links nodeB nodeC := by
  show (unionFindRootOf links nodeA == unionFindRootOf links nodeC)
    = (unionFindRootOf links nodeB == unionFindRootOf links nodeC)
  rw [of_decide_eq_true sameAB]

/-- Same-component right congruence. -/
private theorem isSameComponent_congrRightBBC (links : List (Nat × Nat)) (nodeA nodeB nodeC : Nat)
    (sameBC : isSameComponent links nodeB nodeC = true) :
    isSameComponent links nodeA nodeB = isSameComponent links nodeA nodeC := by
  show (unionFindRootOf links nodeA == unionFindRootOf links nodeB)
    = (unionFindRootOf links nodeA == unionFindRootOf links nodeC)
  rw [of_decide_eq_true sameBC]

/-- The fresh LEFT input `nextFresh` is disconnected, under the FIRST crossing join `join links in0 (nextFresh+1)`,
from every old node. -/
private theorem crossing_nf_disc_J1_BBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 oldNode : Nat) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent (unionFindJoin state.links in0 (state.nextFresh + 1)) state.nextFresh oldNode = false := by
  rw [isSameComponent_unionFindJoin_eq_ofSecondDisconnected state.links forest in0 (state.nextFresh + 1)
      state.nextFresh oldNode
      ((isSameComponent_symm state.links (state.nextFresh + 1) state.nextFresh).trans
        (sameComponent_freshPairBBC state fresh))
      (sameComponent_nextFreshSucc_old_falseBBC state fresh oldNode oldBelow)]
  exact sameComponent_nextFresh_old_falseBBC state fresh oldNode oldBelow

/-- ★ **The crossing is invisible to two OLD boundary nodes** — both joins' fresh second endpoints are disconnected
from either old probe (two applications of the second-endpoint converse). -/
private theorem crossingJoin_oldOldBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 in1 nodeX nodeY : Nat)
    (xBelow : nodeX < state.nextFresh) (yBelow : nodeY < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        nodeX nodeY
      = isSameComponent state.links nodeX nodeY := by
  rw [isSameComponent_unionFindJoin_eq_ofSecondDisconnected (unionFindJoin state.links in0 (state.nextFresh + 1))
      (isUnionFindForest_unionFindJoin state.links in0 (state.nextFresh + 1) forest) in1 state.nextFresh nodeX nodeY
      (crossing_nf_disc_J1_BBC state forest fresh in0 nodeX xBelow)
      (crossing_nf_disc_J1_BBC state forest fresh in0 nodeY yBelow),
    isSameComponent_unionFindJoin_eq_ofSecondDisconnected state.links forest in0 (state.nextFresh + 1) nodeX nodeY
      (sameComponent_nextFreshSucc_old_falseBBC state fresh nodeX xBelow)
      (sameComponent_nextFreshSucc_old_falseBBC state fresh nodeY yBelow)]

/-- The crossing joins its LEFT fresh output `nextFresh` to the SECOND window strand `in1`. -/
private theorem crossing_nf_join_in1_BBC (state : WireState) (forest : isUnionFindForest state.links)
    (in0 in1 : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        in1 state.nextFresh = true :=
  isSameComponent_unionFindJoin_joined (unionFindJoin state.links in0 (state.nextFresh + 1))
    (isUnionFindForest_unionFindJoin state.links in0 (state.nextFresh + 1) forest) in1 state.nextFresh

/-- The crossing joins its RIGHT fresh output `nextFresh + 1` to the FIRST window strand `in0` (survives the outer
join by monotonicity). -/
private theorem crossing_nfSucc_join_in0_BBC (state : WireState) (forest : isUnionFindForest state.links)
    (in0 in1 : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        in0 (state.nextFresh + 1) = true :=
  isSameComponent_unionFindJoin_ofBase (unionFindJoin state.links in0 (state.nextFresh + 1))
    (isUnionFindForest_unionFindJoin state.links in0 (state.nextFresh + 1) forest) in1 state.nextFresh
    in0 (state.nextFresh + 1)
    (isSameComponent_unionFindJoin_joined state.links forest in0 (state.nextFresh + 1))

/-- ★ The crossing's LEFT window read (`nextFresh`) shares a component with an old node iff the SECOND window
strand `in1` did before — the transposition on window slot 0. -/
private theorem crossingJoin_nf_oldBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 in1 oldNode : Nat)
    (in1Below : in1 < state.nextFresh) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        state.nextFresh oldNode
      = isSameComponent state.links in1 oldNode := by
  rw [isSameComponent_congrLeftBBC (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1
        state.nextFresh) state.nextFresh in1 oldNode
      ((isSameComponent_symm _ state.nextFresh in1).trans (crossing_nf_join_in1_BBC state forest in0 in1))]
  exact crossingJoin_oldOldBBC state forest fresh in0 in1 in1 oldNode in1Below oldBelow

/-- ★ The crossing's RIGHT window read (`nextFresh + 1`) shares a component with an old node iff the FIRST window
strand `in0` did before — the transposition on window slot 1. -/
private theorem crossingJoin_nfSucc_oldBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 in1 oldNode : Nat)
    (in0Below : in0 < state.nextFresh) (oldBelow : oldNode < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        (state.nextFresh + 1) oldNode
      = isSameComponent state.links in0 oldNode := by
  rw [isSameComponent_congrLeftBBC (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1
        state.nextFresh) (state.nextFresh + 1) in0 oldNode
      ((isSameComponent_symm _ (state.nextFresh + 1) in0).trans (crossing_nfSucc_join_in0_BBC state forest in0 in1))]
  exact crossingJoin_oldOldBBC state forest fresh in0 in1 in0 oldNode in0Below oldBelow

/-- ★ The crossing's two window reads (`nextFresh`, `nextFresh + 1`) share a component iff the two window strands
`in1`, `in0` did before. -/
private theorem crossingJoin_nf_nfSuccBBC (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 in1 : Nat)
    (in0Below : in0 < state.nextFresh) (in1Below : in1 < state.nextFresh) :
    isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
        state.nextFresh (state.nextFresh + 1)
      = isSameComponent state.links in1 in0 := by
  rw [isSameComponent_congrLeftBBC (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1
        state.nextFresh) state.nextFresh in1 (state.nextFresh + 1)
      ((isSameComponent_symm _ state.nextFresh in1).trans (crossing_nf_join_in1_BBC state forest in0 in1)),
    isSameComponent_congrRightBBC (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1
        state.nextFresh) in1 (state.nextFresh + 1) in0
      ((isSameComponent_symm _ (state.nextFresh + 1) in0).trans (crossing_nfSucc_join_in0_BBC state forest in0 in1))]
  exact crossingJoin_oldOldBBC state forest fresh in0 in1 in1 in0 in1Below in0Below

/-- ★ **THE CROSSING transposition on the same-component view.**  For the crossing's two-join link update
`unionFindJoin (unionFindJoin links in0 (nextFresh + 1)) in1 nextFresh` (both joins carrying a FRESH second
endpoint), the same-component view is the window transposition of the base view: (1) two OLD nodes are unchanged;
(2) the LEFT fresh output `nextFresh` reads the SECOND window strand `in1`'s class; (3) the RIGHT fresh output
`nextFresh + 1` reads the FIRST window strand `in0`'s class; (4) the two fresh outputs share iff the two window
strands did.  This is the connectivity crux of the crossing's `boundedBoundaryComponents` preservation — a bijective
relabel (no cardinality count, no Frobenius analog).  Zero-axiom (pure union-find; the fresh endpoints make each
join invisible to old nodes via the second-endpoint converse). -/
theorem crossingJoin_transposition_view (state : WireState) (forest : isUnionFindForest state.links)
    (fresh : WiringDescStateFresh state) (in0 in1 : Nat)
    (in0Below : in0 < state.nextFresh) (in1Below : in1 < state.nextFresh) :
    (∀ nodeX nodeY, nodeX < state.nextFresh → nodeY < state.nextFresh →
        isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
            nodeX nodeY
          = isSameComponent state.links nodeX nodeY)
    ∧ (∀ nodeX, nodeX < state.nextFresh →
        isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
            state.nextFresh nodeX
          = isSameComponent state.links in1 nodeX)
    ∧ (∀ nodeX, nodeX < state.nextFresh →
        isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
            (state.nextFresh + 1) nodeX
          = isSameComponent state.links in0 nodeX)
    ∧ isSameComponent (unionFindJoin (unionFindJoin state.links in0 (state.nextFresh + 1)) in1 state.nextFresh)
          state.nextFresh (state.nextFresh + 1)
        = isSameComponent state.links in1 in0 :=
  ⟨fun nodeX nodeY xBelow yBelow => crossingJoin_oldOldBBC state forest fresh in0 in1 nodeX nodeY xBelow yBelow,
   fun nodeX xBelow => crossingJoin_nf_oldBBC state forest fresh in0 in1 nodeX in1Below xBelow,
   fun nodeX xBelow => crossingJoin_nfSucc_oldBBC state forest fresh in0 in1 nodeX in0Below xBelow,
   crossingJoin_nf_nfSuccBBC state forest fresh in0 in1 in0Below in1Below⟩

/-! ## B1 — THE CROSSING preservation: assemble the transposition view over the read classification

The crossing preserves the open-wire length (removes two, inserts two) and its two window slots read the fresh
outputs; every other slot reads the SAME old node at the SAME index.  The connectivity is the shipped window
transposition (`crossingJoin_transposition_view`).  So the crossing's `boundedBoundaryComponents` preservation is a
PULLBACK along the window transposition `crossingReindexBBC` — a bijective relabel that swaps the two window boundary
indices — with the base invariant refuting the pulled-back triple.  No pigeonhole, no cardinality count (the novel
leg with no Frobenius analog: the shipped two-join transposition view did the connectivity work in r8). -/

/-- The **window transposition** on boundary indices: swap the crossing's two window boundary slots `bottomCount +
position` and `bottomCount + (position + 1)`, fixing everything else.  The pullback map along which the crossing's
same-component view is the base view. -/
private def crossingReindexBBC (bottomCount position index : Nat) : Nat :=
  if index = bottomCount + position then bottomCount + (position + 1)
  else if index = bottomCount + (position + 1) then bottomCount + position
  else index

/-- The two window boundary indices are distinct (`bottomCount + (position + 1) ≠ bottomCount + position`). -/
private theorem windowIndex_neBBC (bottomCount position : Nat) :
    bottomCount + (position + 1) ≠ bottomCount + position := by
  intro heq
  exact Nat.succ_ne_self (bottomCount + position) ((Nat.add_assoc bottomCount position 1).trans heq)

/-- The reindex sends the left window index to the right window index. -/
private theorem crossingReindexBBC_leftPort (bottomCount position : Nat) :
    crossingReindexBBC bottomCount position (bottomCount + position) = bottomCount + (position + 1) := by
  show (if bottomCount + position = bottomCount + position then bottomCount + (position + 1)
        else if bottomCount + position = bottomCount + (position + 1) then bottomCount + position
        else bottomCount + position) = bottomCount + (position + 1)
  rw [if_pos rfl]

/-- The reindex sends the right window index to the left window index. -/
private theorem crossingReindexBBC_rightPort (bottomCount position : Nat) :
    crossingReindexBBC bottomCount position (bottomCount + (position + 1)) = bottomCount + position := by
  show (if bottomCount + (position + 1) = bottomCount + position then bottomCount + (position + 1)
        else if bottomCount + (position + 1) = bottomCount + (position + 1) then bottomCount + position
        else bottomCount + (position + 1)) = bottomCount + position
  rw [if_neg (windowIndex_neBBC bottomCount position), if_pos rfl]

/-- The reindex fixes every non-window index. -/
private theorem crossingReindexBBC_other (bottomCount position index : Nat)
    (neLeft : index ≠ bottomCount + position) (neRight : index ≠ bottomCount + (position + 1)) :
    crossingReindexBBC bottomCount position index = index := by
  show (if index = bottomCount + position then bottomCount + (position + 1)
        else if index = bottomCount + (position + 1) then bottomCount + position
        else index) = index
  rw [if_neg neLeft, if_neg neRight]

/-- The reindex is an involution (it swaps the two window indices and fixes the rest). -/
private theorem crossingReindexBBC_involutive (bottomCount position index : Nat) :
    crossingReindexBBC bottomCount position (crossingReindexBBC bottomCount position index) = index := by
  cases Nat.decEq index (bottomCount + position) with
  | isTrue hLeft =>
      rw [hLeft, crossingReindexBBC_leftPort, crossingReindexBBC_rightPort]
  | isFalse hNotLeft =>
      cases Nat.decEq index (bottomCount + (position + 1)) with
      | isTrue hRight => rw [hRight, crossingReindexBBC_rightPort, crossingReindexBBC_leftPort]
      | isFalse hNotRight =>
          rw [crossingReindexBBC_other bottomCount position index hNotLeft hNotRight,
            crossingReindexBBC_other bottomCount position index hNotLeft hNotRight]

/-- The reindex is injective (it is its own inverse). -/
private theorem crossingReindexBBC_inj (bottomCount position firstIndex secondIndex : Nat)
    (imagesEq : crossingReindexBBC bottomCount position firstIndex
        = crossingReindexBBC bottomCount position secondIndex) :
    firstIndex = secondIndex :=
  (crossingReindexBBC_involutive bottomCount position firstIndex).symm.trans
    ((congrArg (crossingReindexBBC bottomCount position) imagesEq).trans
      (crossingReindexBBC_involutive bottomCount position secondIndex))

/-- The reindex sends distinct indices to distinct images. -/
private theorem crossingReindexBBC_ne (bottomCount position firstIndex secondIndex : Nat)
    (distinct : firstIndex ≠ secondIndex) :
    crossingReindexBBC bottomCount position firstIndex ≠ crossingReindexBBC bottomCount position secondIndex :=
  fun imagesEq => distinct (crossingReindexBBC_inj bottomCount position firstIndex secondIndex imagesEq)

/-- The reindex preserves the boundary range (window indices map to window indices, which are in range when the
window is in range; everything else is fixed). -/
private theorem crossingReindexBBC_lt (bottomCount : Nat) (state : WireState) (position index : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (indexRange : index < bottomCount + state.openWires.length) :
    crossingReindexBBC bottomCount position index < bottomCount + state.openWires.length := by
  cases Nat.decEq index (bottomCount + position) with
  | isTrue hLeft =>
      rw [hLeft, crossingReindexBBC_leftPort]
      exact Nat.add_lt_add_left
        (Nat.lt_of_lt_of_le (Nat.lt_add_one (position + 1)) windowInRange) bottomCount
  | isFalse hNotLeft =>
      cases Nat.decEq index (bottomCount + (position + 1)) with
      | isTrue hRight =>
          rw [hRight, crossingReindexBBC_rightPort]
          exact Nat.add_lt_add_left
            (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_add_one position)
              (Nat.le_succ (position + 1))) windowInRange) bottomCount
      | isFalse hNotRight =>
          rw [crossingReindexBBC_other bottomCount position index hNotLeft hNotRight]
          exact indexRange

/-- ★ **The post-crossing boundary read classification.**  Every in-range post-crossing boundary index either reads
the LEFT fresh output (`= bottomCount + position`, value `nextFresh`), the RIGHT fresh output
(`= bottomCount + (position + 1)`, value `nextFresh + 1`), or an OLD node at the SAME index (the crossing preserves
length, so past-window reads are unshifted).  Stated through the shipped four-zone open-wire classifier
`stepWiringOpenRead_below` / `_fresh` / `_past`. -/
private theorem crossingReadClassBBC (bottomCount : Nat) (state : WireState) (position : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (index : Nat) (indexRange : index < bottomCount + state.openWires.length) :
    (index = bottomCount + position
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepWiring state position crossingWiring)) index
            = state.nextFresh)
    ∨ (index = bottomCount + (position + 1)
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepWiring state position crossingWiring)) index
            = state.nextFresh + 1)
    ∨ (index ≠ bottomCount + position ∧ index ≠ bottomCount + (position + 1)
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepWiring state position crossingWiring)) index
            = natListGetAt (matchingBoundaryNodes bottomCount state) index) := by
  obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest windowInRange
  have fitsC : state.openWires.length = position + crossingWiring.inputCount + rightLen := fitsRaw.symm
  cases Nat.lt_or_ge index bottomCount with
  | inl belowBottom =>
      refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le belowBottom (Nat.le_add_right bottomCount position))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le belowBottom (Nat.le_add_right bottomCount (position + 1)))
      · exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount (stepWiring state position crossingWiring)
          state index belowBottom
  | inr atLeastBottom =>
      obtain ⟨wireOffset, rfl⟩ := Nat.le.dest atLeastBottom
      have wireOffsetLt : wireOffset < state.openWires.length := Nat.lt_of_add_lt_add_left indexRange
      cases Nat.lt_or_ge wireOffset position with
      | inl belowWindow =>
          refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · exact Nat.ne_of_lt (Nat.add_lt_add_left belowWindow bottomCount)
          · exact Nat.ne_of_lt (Nat.add_lt_add_left
              (Nat.lt_trans belowWindow (Nat.lt_add_one position)) bottomCount)
          · rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring state position crossingWiring) wireOffset,
              matchingBoundaryNodes_getAt_top bottomCount state wireOffset,
              stepWiringOpenRead_below state position rightLen wireOffset crossingWiring fitsC belowWindow]
      | inr atLeastWindow =>
          cases Nat.lt_or_ge wireOffset (position + 2) with
          | inl belowPlus2 =>
              cases Nat.lt_or_ge wireOffset (position + 1) with
              | inl belowPlus1 =>
                  have wireOffsetEq : wireOffset = position :=
                    Nat.le_antisymm (Nat.le_of_lt_succ belowPlus1) atLeastWindow
                  subst wireOffset
                  refine Or.inl ⟨rfl, ?_⟩
                  rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring state position crossingWiring) position]
                  show natListGetAt (stepWiring state position crossingWiring).openWires (position + 0)
                      = state.nextFresh
                  rw [stepWiringOpenRead_fresh state position rightLen 0 crossingWiring fitsC (by decide),
                    Nat.zero_add]
              | inr atLeastPlus1 =>
                  have wireOffsetEq : wireOffset = position + 1 :=
                    Nat.le_antisymm (Nat.le_of_lt_succ belowPlus2) atLeastPlus1
                  subst wireOffset
                  refine Or.inr (Or.inl ⟨rfl, ?_⟩)
                  rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring state position crossingWiring)
                      (position + 1),
                    stepWiringOpenRead_fresh state position rightLen 1 crossingWiring fitsC (by decide),
                    Nat.add_comm 1 state.nextFresh]
          | inr atLeastPlus2 =>
              obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastPlus2
              have posLtHere : position < position + 2 + offset :=
                Nat.lt_of_lt_of_le (Nat.lt_add_one position)
                  (Nat.le_trans (Nat.le_succ (position + 1)) (Nat.le_add_right (position + 2) offset))
              have posSuccLtHere : position + 1 < position + 2 + offset :=
                Nat.lt_of_lt_of_le (Nat.lt_add_one (position + 1)) (Nat.le_add_right (position + 2) offset)
              have offsetLt : offset < rightLen := by
                have hlt : position + 2 + offset < position + 2 + rightLen := by
                  rw [fitsRaw]; exact wireOffsetLt
                exact Nat.lt_of_add_lt_add_left hlt
              refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
              · exact Ne.symm (Nat.ne_of_lt (Nat.add_lt_add_left posLtHere bottomCount))
              · exact Ne.symm (Nat.ne_of_lt (Nat.add_lt_add_left posSuccLtHere bottomCount))
              · rw [matchingBoundaryNodes_getAt_top bottomCount (stepWiring state position crossingWiring)
                    (position + 2 + offset),
                  matchingBoundaryNodes_getAt_top bottomCount state (position + 2 + offset)]
                exact stepWiringOpenRead_past state position rightLen offset crossingWiring fitsC offsetLt

/-- ★ **The crossing same-component PULLBACK.**  For distinct in-range boundary indices, the post-crossing
same-component view equals the base same-component view of the reindexed pair (`crossingReindexBBC`, the window
transposition).  Every combination of the two indices' read classes (fresh left / fresh right / old) is discharged
by the matching leg of the shipped `crossingJoin_transposition_view`: two OLD reads are unchanged, a LEFT fresh read
transposes to the SECOND window strand, a RIGHT fresh read to the FIRST, and the two fresh reads share iff the two
strands did. -/
private theorem matchingSameComponent_stepCrossing_reindexBBC (bottomCount : Nat) (state : WireState)
    (position : Nat) (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (bottomLe : bottomCount ≤ state.nextFresh)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (firstIndex secondIndex : Nat) (distinct : firstIndex ≠ secondIndex)
    (firstRange : firstIndex < bottomCount + state.openWires.length)
    (secondRange : secondIndex < bottomCount + state.openWires.length) :
    matchingSameComponent bottomCount (stepWiring state position crossingWiring) firstIndex secondIndex
      = matchingSameComponent bottomCount state
          (crossingReindexBBC bottomCount position firstIndex)
          (crossingReindexBBC bottomCount position secondIndex) := by
  have in0Below : natListGetAt state.openWires position < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires position fresh.1
  have in1Below : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    natListGetAt_lt state.nextFresh nfPos state.openWires (position + 1) fresh.1
  obtain ⟨oldOld, nfOld, nfSuccOld, nfNfSucc⟩ :=
    crossingJoin_transposition_view state forest fresh
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) in0Below in1Below
  have topL := matchingBoundaryNodes_getAt_top bottomCount state position
  have topR := matchingBoundaryNodes_getAt_top bottomCount state (position + 1)
  have nfBoundF : natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex < state.nextFresh :=
    boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos firstIndex
  have nfBoundS : natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex < state.nextFresh :=
    boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos secondIndex
  have classFirst := crossingReadClassBBC bottomCount state position windowInRange firstIndex firstRange
  have classSecond := crossingReadClassBBC bottomCount state position windowInRange secondIndex secondRange
  show isSameComponent (stepWiring state position crossingWiring).links
        (natListGetAt (matchingBoundaryNodes bottomCount (stepWiring state position crossingWiring)) firstIndex)
        (natListGetAt (matchingBoundaryNodes bottomCount (stepWiring state position crossingWiring)) secondIndex)
      = isSameComponent state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state)
          (crossingReindexBBC bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount state)
          (crossingReindexBBC bottomCount position secondIndex))
  rw [stepWiring_crossing_links state position fresh nfPos forest windowInRange]
  rcases classFirst with ⟨hiF, hrF⟩ | ⟨hiF, hrF⟩ | ⟨hneLF, hneRF, hrF⟩
  · rcases classSecond with ⟨hiS, _⟩ | ⟨hiS, hrS⟩ | ⟨hneLS, hneRS, hrS⟩
    · exact absurd (hiF.trans hiS.symm) distinct
    · rw [hrF, hrS, hiF, crossingReindexBBC_leftPort, hiS, crossingReindexBBC_rightPort, topR, topL]
      exact nfNfSucc
    · rw [hrF, hrS, hiF, crossingReindexBBC_leftPort, topR,
        crossingReindexBBC_other bottomCount position secondIndex hneLS hneRS]
      exact nfOld _ nfBoundS
  · rcases classSecond with ⟨hiS, hrS⟩ | ⟨hiS, _⟩ | ⟨hneLS, hneRS, hrS⟩
    · rw [hrF, hrS, hiF, crossingReindexBBC_rightPort, hiS, crossingReindexBBC_leftPort, topL, topR,
        isSameComponent_symm _ (state.nextFresh + 1) state.nextFresh, nfNfSucc,
        isSameComponent_symm state.links (natListGetAt state.openWires (position + 1))
          (natListGetAt state.openWires position)]
    · exact absurd (hiF.trans hiS.symm) distinct
    · rw [hrF, hrS, hiF, crossingReindexBBC_rightPort, topL,
        crossingReindexBBC_other bottomCount position secondIndex hneLS hneRS]
      exact nfSuccOld _ nfBoundS
  · rcases classSecond with ⟨hiS, hrS⟩ | ⟨hiS, hrS⟩ | ⟨hneLS, hneRS, hrS⟩
    · rw [hrF, hrS, crossingReindexBBC_other bottomCount position firstIndex hneLF hneRF, hiS,
        crossingReindexBBC_leftPort, topR,
        isSameComponent_symm _ (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
          state.nextFresh,
        nfOld (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex) nfBoundF,
        isSameComponent_symm state.links (natListGetAt state.openWires (position + 1))
          (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)]
    · rw [hrF, hrS, crossingReindexBBC_other bottomCount position firstIndex hneLF hneRF, hiS,
        crossingReindexBBC_rightPort, topL,
        isSameComponent_symm _ (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
          (state.nextFresh + 1),
        nfSuccOld (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex) nfBoundF,
        isSameComponent_symm state.links (natListGetAt state.openWires position)
          (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)]
    · rw [hrF, hrS, crossingReindexBBC_other bottomCount position firstIndex hneLF hneRF,
        crossingReindexBBC_other bottomCount position secondIndex hneLS hneRS]
      exact oldOld _ _ nfBoundF nfBoundS

/-- ★ **THE CROSSING preservation.**  `boundedBoundaryComponents` survives an in-range `stepWiring _ _ crossingWiring`.
The crossing preserves the open-wire length, so its boundary range is unchanged; each post-crossing same-component
view pulls back along the window transposition `crossingReindexBBC` to the base view
(`matchingSameComponent_stepCrossing_reindexBBC`, riding the shipped `crossingJoin_transposition_view`).  A would-be
violating post-crossing triple therefore maps under the injective, range-preserving transposition to a violating
BASE triple, refuted by the base invariant — a pure bijective relabel, no pigeonhole (the connectivity crux was the
shipped transposition view).  Requires the four reachable-state conditions (fresh / forest / positive counter /
bottom-fits) plus the crossing window in range (`position + 2 ≤ openWires.length`). -/
theorem boundedBoundaryComponents_stepCrossing (bottomCount : Nat) (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (bottomLe : bottomCount ≤ state.nextFresh)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state) :
    boundedBoundaryComponents bottomCount (stepWiring state position crossingWiring) := by
  intro firstIndex secondIndex thirdIndex firstBelow secondBelow thirdBelow
    firstNeSecond firstNeThird secondNeThird sameConjunction
  obtain ⟨sameFirstSecond, sameFirstThird⟩ := sameConjunction
  have lenEq : (stepWiring state position crossingWiring).openWires.length = state.openWires.length := by
    obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest windowInRange
    rw [stepWiring_openWires_length_fits state position rightLen crossingWiring fitsRaw.symm]
    exact fitsRaw
  rw [lenEq] at firstBelow secondBelow thirdBelow
  rw [matchingSameComponent_stepCrossing_reindexBBC bottomCount state position fresh forest nfPos bottomLe
      windowInRange firstIndex secondIndex firstNeSecond firstBelow secondBelow] at sameFirstSecond
  rw [matchingSameComponent_stepCrossing_reindexBBC bottomCount state position fresh forest nfPos bottomLe
      windowInRange firstIndex thirdIndex firstNeThird firstBelow thirdBelow] at sameFirstThird
  exact bounded (crossingReindexBBC bottomCount position firstIndex)
    (crossingReindexBBC bottomCount position secondIndex) (crossingReindexBBC bottomCount position thirdIndex)
    (crossingReindexBBC_lt bottomCount state position firstIndex windowInRange firstBelow)
    (crossingReindexBBC_lt bottomCount state position secondIndex windowInRange secondBelow)
    (crossingReindexBBC_lt bottomCount state position thirdIndex windowInRange thirdBelow)
    (crossingReindexBBC_ne bottomCount position firstIndex secondIndex firstNeSecond)
    (crossingReindexBBC_ne bottomCount position firstIndex thirdIndex firstNeThird)
    (crossingReindexBBC_ne bottomCount position secondIndex thirdIndex secondNeThird)
    ⟨sameFirstSecond, sameFirstThird⟩

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

/-- ★ **Honesty marker — THE CUP preservation is SHIPPED (r8 B1).**  `boundedBoundaryComponents_stepCup`:
`boundedBoundaryComponents` survives an in-range `stepCup`.  The cup splices two FRESH legs `nextFresh`,
`nextFresh + 1` and joins them; both endpoints being fresh, the join is invisible to old boundary reads
(`cupJoin_inert_oldBBC`) and the fresh pair forms its own two-element component (`cupJoin_nextFresh{,Succ}_old_falseBBC`).
The read classification `cupReadClassBBC` sends every post-cup boundary index to a fresh leg or an old node reindexed
by the cap's ADDITIVE up-shift `capBoundaryReindex` (NO `index - 2` subtraction — the `propext` wall the r7 marker
flagged is avoided).  An index reading a fresh leg forces every co-component index to read a fresh leg too, and only
two indices do (a pigeonhole); the all-old case transports the star to the base invariant.  Zero-axiom.  Requires
the four reachable-state conditions + the cup window in range (`position <= openWires.length`).  `= true`. -/
def fxBrauer_hasCupPreservation : Bool := true

/-- ★ **Honesty marker — THE CROSSING transposition on the same-component view is SHIPPED (r8 B2, the connectivity
crux).**  `crossingJoin_transposition_view`: for the crossing's two-join link update
`unionFindJoin (unionFindJoin links in0 (nextFresh + 1)) in1 nextFresh` (both joins carrying a FRESH second endpoint),
the same-component view is the window TRANSPOSITION of the base view — two old nodes unchanged
(`crossingJoin_oldOldBBC`, two applications of the second-endpoint converse), the LEFT fresh output reading the SECOND
window strand's class (`crossingJoin_nf_oldBBC`), the RIGHT fresh output the FIRST strand's class
(`crossingJoin_nfSucc_oldBBC`), the two outputs sharing iff the two strands did (`crossingJoin_nf_nfSuccBBC`).  This
is the novel two-join transposition connectivity with no Frobenius analog — a bijective relabel, proved zero-axiom by
pure union-find (fresh-endpoint invisibility + same-component congruence).  `= true`. -/
def fxBrauer_hasCrossingTranspositionView : Bool := true

/-- ★ **Honesty marker — THE CROSSING per-atom preservation is SHIPPED (r9 B1, the headline).**
`boundedBoundaryComponents_stepCrossing`: `boundedBoundaryComponents` survives an in-range
`stepWiring _ _ crossingWiring`.  The crossing preserves the open-wire length (so its boundary range is unchanged),
its two window slots read the fresh outputs and every other slot reads the SAME old node at the SAME index
(`crossingReadClassBBC`, over the un-privated four-zone open-wire classifier `stepWiringOpenRead_below` / `_fresh` /
`_past` and the crossing link update `stepWiring_crossing_links`).  Each post-crossing same-component view therefore
PULLS BACK along the window transposition `crossingReindexBBC` to the base view
(`matchingSameComponent_stepCrossing_reindexBBC`, discharged leg-by-leg from the shipped
`crossingJoin_transposition_view`); a would-be violating post-crossing triple maps under the injective,
range-preserving transposition to a violating BASE triple, refuted by the base invariant.  A pure bijective relabel,
no pigeonhole — the novel leg with no Frobenius analog (the connectivity crux was the shipped transposition view).
Zero-axiom.  Requires the four reachable-state conditions + the crossing window in range
(`position + 2 ≤ openWires.length`).  `= true`. -/
def fxBrauer_hasCrossingPreservation : Bool := true

/-- **Honesty marker — the FULL T-DISJOINT leg (`R3-A-TAGCORR` long pole) is NOT closed.**  SHIPPED: THE CAP
preservation (`boundedBoundaryComponents_stepCap`, `fxBrauer_hasCapPreservation`), THE CUP preservation
(`boundedBoundaryComponents_stepCup`, `fxBrauer_hasCupPreservation`), THE CROSSING transposition on the
same-component view (`crossingJoin_transposition_view`, `fxBrauer_hasCrossingTranspositionView`), and now (r9 B1) THE
CROSSING per-atom preservation (`boundedBoundaryComponents_stepCrossing`, `fxBrauer_hasCrossingPreservation`) — so all
THREE per-atom preservations (cup / cap / crossing) stand.  Still UNBUILT: the `stepWiring _ _ capWiring = stepCap` /
`stepWiring _ _ cupWiring = stepCup` bridges (conditional on the window in range + freshness), the `processBrauer`
FOLD lift (ride `brauerStateConditions_processBrauer`, dispatching on the generator kind with a per-atom
window-in-range predicate `WellFormedBrauerWord`), and the EXTRACTION consequence (cardinality + T-CONNECT =>
`partnerIndexOf` reads the `d`-partner).  So T-DISJOINT stays open, the roundtrip flags and masters stay `false`, and
#2013 does not close — a ROUTE / totality gap, never a truth gap (Lehrer-Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasTagCorrDisjoint : Bool := false

end FX1Poly.Polygraph
