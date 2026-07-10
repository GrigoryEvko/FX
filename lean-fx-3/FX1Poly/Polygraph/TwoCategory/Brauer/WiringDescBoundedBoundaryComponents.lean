import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement

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

/-- **Honesty marker — the FULL T-DISJOINT leg (`R3-A-TAGCORR` long pole) is NOT closed.**  The three per-atom
PRESERVATION steps (`boundedBoundaryComponents` survives `stepWiring` at `cupWiring` / `capWiring` / `crossingWiring`
— the crossing case the novel leg with no Frobenius analog), the `processBrauer` FOLD lift, and the EXTRACTION
consequence (cardinality + T-CONNECT => `partnerIndexOf` reads the `d`-partner) are UNBUILT this round.  They carry
the general-position `natListInsertAt` / `natListRemoveManyAt` boundary-index arithmetic, the threaded freshness
invariant, and the two-join crossing bookkeeping via `isSameComponent_unionFindJoin`.  So T-DISJOINT stays open, the
roundtrip flags and masters stay `false`, and #2013 does not close — a ROUTE / totality gap, never a truth gap
(Lehrer-Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasTagCorrDisjoint : Bool := false

end FX1Poly.Polygraph
