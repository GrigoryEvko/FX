import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFoldInstance

/-! # Polygraph/TwoCategory/Table/FrobeniusFoldLegs — the shift algebra + the connectivity->partition
reduction for the deep `foldEq` residuals (FROB-RESUME r2, #2017)

`Table/FrobeniusFoldInstance.lean` banked the FULL deep `rowConvInvariant_foldEq` instance
(`fxTab_hasDeepDiagramFoldInstance = false`), sharpening the residual to (a) `fullPreserves` (the
`TwoCellConvFull` 13-arm), and (b) the boundary-CHANGING context legs (`vcompCongrRight` /
`whiskerLeftCongr` / `whiskerRightCongr`).  The r2 recon confirmed the SPIDER pad congruences ship
gate-free (`spiderConv_relation_inWiderBoundary` right pad, `spiderConv_relation_inWiderBoundary_leftOffset`
left pad), so the whisker legs route through them — the residual blocker is not a partition gap but
the readback-in-range side condition + the NIL-boundary gate on the `vcomp` legs (`spiderConv_suffixCongruence`
/ `spiderConv_relation_afterPrefix` both demand `0 < bottomCount`, genuinely false at the `η : id ⇒ t` cell).

## What ships here (r2)

  * **The shift algebra** — `shiftBrauerWord_zero` (`shift 0 = id`) and `shiftBrauerWord_add`
    (`shift (a+b) = shift a ∘ shift b`), the two structural word-position lemmas the EASY structural
    arms of `fullPreserves` (`whiskerLeftUnit` = shift-0, `whiskerLeftComp` = shift-add) reduce to.
    These are the `RawTwoCellExpr.whiskerLeft` normalisation atoms on the readback word.
  * **The connectivity->partition reduction** (`spiderPartition_of_allConnected`) — a wire state whose
    boundary ports are ALL pairwise same-component reads back to the fully-connected partition
    `⟨n, openWires.length, replicate (n + openWires.length) 0⟩`.  This is the CLEAN half of the B1
    general-arity spider realization: it reduces the realization theorem
    `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` from a partition
    computation to a pure CONNECTIVITY-of-the-canonical-fold statement (the surviving node banked in
    `FrobeniusFusionNF.lean`, sharpened here from "the whole realization" to "the union-find fold of
    `mergeToOne`/`fanToN` connects every boundary port").

Raw Lean 4 + Init; the shift lemmas are structural cons-recursions, the reduction lemma routes through
the shipped block-label bridge `matchingSameComponent_eq_blockLabelBeq` + the field-determination
`spiderPartitionType_eq_of_fields`.  No `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Additive: nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The shift algebra on Brauer words -/

/-- ★ **Shifting every atom position by `0` is the identity.**  The `whiskerLeft (id_path) body` normalisation
atom: a zero-length prefix pad leaves the readback word unchanged (`RawTwoCellExpr.whiskerLeft` on an empty
prefix 1-cell reads back to the bare body).  Structural cons-recursion; the head reconstructs the atom by
structure eta after `Nat.zero_add`. -/
theorem shiftBrauerWord_zero (word : List BrauerAtom) : shiftBrauerWord 0 word = word := by
  induction word with
  | nil => rfl
  | cons atom rest ih =>
      show { position := 0 + atom.position, wiring := atom.wiring } :: shiftBrauerWord 0 rest = atom :: rest
      rw [Nat.zero_add, ih]

/-- ★ **Shifting by `delta1 + delta2` factors as shifting by `delta2` then by `delta1`.**  The
`whiskerLeft (compose p q) body` normalisation atom: a composite prefix pad decomposes as two nested pads
(`shift (p.length + q.length) = shift p.length ∘ shift q.length`), matching `composePath_length`.  Structural
cons-recursion; the head is `Nat.add_assoc` on the position. -/
theorem shiftBrauerWord_add (delta1 delta2 : Nat) (word : List BrauerAtom) :
    shiftBrauerWord (delta1 + delta2) word = shiftBrauerWord delta1 (shiftBrauerWord delta2 word) := by
  induction word with
  | nil => rfl
  | cons atom rest ih =>
      show { position := delta1 + delta2 + atom.position, wiring := atom.wiring }
            :: shiftBrauerWord (delta1 + delta2) rest
          = { position := delta1 + (delta2 + atom.position), wiring := atom.wiring }
            :: shiftBrauerWord delta1 (shiftBrauerWord delta2 rest)
      rw [Nat.add_assoc, ih]

/-! ## The connectivity -> partition reduction (the clean half of the B1 realization)

Local propext-free `List.range` primitives (the core `List.range` / `mem_range` lemmas leak `propext`,
so `Frobenius/SpiderCompleteness.lean` keeps its own; those are `private`, so we re-derive the two we
need). -/

/-- `(List.range count).length = count` — propext-free, via the loop accumulator. -/
private theorem rangeLoopLengthFold : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthFold count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthFold (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthFold count []]
  exact Nat.add_zero count

/-- `natListGetAt (List.range count) index = index` for `index < count` — propext-free. -/
private theorem rangeLoopGetAtPastFold : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastFold count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowFold : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowFold count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastFold count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowFold (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowFold count [] index indexBelow

/-- The `firstIndexWithRoot` scan over `List.range total`, when the port at candidate `0` matches the
target root, returns `0` — because the scan visits candidates in `natListGetAt`-order and candidate `0`
of `List.range total` reads as `0` (`rangeGetAtBelowFold`), so its own root equality holds and the head
branch fires.  We phrase it on the scan of an arbitrary in-range candidate whose port `0` is connected. -/
private theorem firstIndexWithRoot_range_zero_of_zeroMatches
    (links : List (Nat × Nat)) (boundaryNodes : List Nat) (targetRoot : Nat) (total : Nat)
    (totalPos : 0 < total)
    (zeroMatches : (unionFindRootOf links (natListGetAt boundaryNodes 0) == targetRoot) = true) :
    firstIndexWithRoot links boundaryNodes targetRoot (List.range total) = 0 := by
  -- `firstIndexWithRoot` recurses on the concrete candidate list, so we case on `List.range total`;
  -- its head reads as `natListGetAt (List.range total) 0 = 0` (`rangeGetAtBelowFold`), so the head
  -- if-branch fires under `zeroMatches`.
  cases hrange : List.range total with
  | nil =>
      have hz : total = 0 := by
        have hL := rangeLengthFold total
        rw [hrange] at hL
        exact hL.symm
      subst hz
      exact absurd totalPos (Nat.lt_irrefl 0)
  | cons head restCands =>
      have headZero : head = 0 := by
        have headRead := rangeGetAtBelowFold total 0 totalPos
        rw [hrange] at headRead
        exact headRead
      show (if (unionFindRootOf links (natListGetAt boundaryNodes head) == targetRoot) then head
          else firstIndexWithRoot links boundaryNodes targetRoot restCands) = 0
      rw [headZero, zeroMatches]
      exact if_pos rfl

/-- Mapping the constant-`0` function over a list yields the all-zero list of the same length —
propext-free structural recursion (the block-label list is constantly `0` once every port connects). -/
private theorem mapConstZero : (values : List Nat) →
    values.map (fun _ => (0 : Nat)) = List.replicate values.length 0
  | [] => rfl
  | head :: tail => by
      show (0 : Nat) :: tail.map (fun _ => (0 : Nat)) = (0 : Nat) :: List.replicate tail.length 0
      rw [mapConstZero tail]

/-- ★ **The connectivity -> partition reduction.**  A wire state whose boundary ports are ALL pairwise
same-component (`allConnected`) reads back (`extractSpiderDiagram` + `forgetSpiderClosed`) to the
FULLY-connected corelation partition `⟨bottomCount, openWires.length, replicate (bottomCount + openWires.length) 0⟩`
— one block, every block label `0`.  The block-label map is constantly `0` because `firstIndexWithRoot`
scanning `List.range total` returns candidate `0` (`firstIndexWithRoot_range_zero_of_zeroMatches`) whenever
port `0` shares a component with the scanned index, which `allConnected` supplies.  This is the CLEAN half of
the general-arity spider realization `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩`:
it reduces that realization to a pure CONNECTIVITY statement about the `mergeToOne`/`fanToN` union-find fold
(the surviving node banked in `Table/FrobeniusFusionNF.lean`). -/
theorem spiderPartition_of_allConnected (bottomCount : Nat) (state : WireState)
    (allConnected : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + state.openWires.length →
        secondIndex < bottomCount + state.openWires.length →
        matchingSameComponent bottomCount state firstIndex secondIndex = true) :
    forgetSpiderClosed (extractSpiderDiagram bottomCount state)
      = { bottomCount := bottomCount, topCount := state.openWires.length,
          blockLabels := List.replicate (bottomCount + state.openWires.length) 0 } := by
  apply spiderPartitionType_eq_of_fields
  · rfl
  · rfl
  · show (List.range (bottomCount + state.openWires.length)).map (fun index =>
          firstIndexWithRoot state.links (List.range bottomCount ++ state.openWires)
            (unionFindRootOf state.links
              (natListGetAt (List.range bottomCount ++ state.openWires) index))
            (List.range (bottomCount + state.openWires.length)))
        = List.replicate (bottomCount + state.openWires.length) 0
    rw [listMapCongr _ (fun _ => (0 : Nat)) (List.range (bottomCount + state.openWires.length))
        (fun candidate candidateInRange => by
          have candidateBelow : candidate < bottomCount + state.openWires.length :=
            mem_range_imp_lt candidateInRange
          have totalPos : 0 < bottomCount + state.openWires.length :=
            Nat.lt_of_le_of_lt (Nat.zero_le candidate) candidateBelow
          exact firstIndexWithRoot_range_zero_of_zeroMatches state.links
            (List.range bottomCount ++ state.openWires)
            (unionFindRootOf state.links
              (natListGetAt (List.range bottomCount ++ state.openWires) candidate))
            (bottomCount + state.openWires.length) totalPos
            (allConnected 0 candidate totalPos candidateBelow)),
      mapConstZero, rangeLengthFold]

/-! ## Non-vacuity — the reduction fires on the connected canonical spider -/

/-- The connected `2 ⇒ 2` canonical spider `[μ, δ]` has ALL four boundary ports pairwise same-component —
`decide` on the concrete post-fold state (the `Nat.decidableBallLT`-friendly guard order). -/
theorem canonicalSpider22_allConnected : ∀ firstIndex, firstIndex < 4 → ∀ secondIndex, secondIndex < 4 →
    matchingSameComponent 2 (processBrauer (brauerSeed 2) (canonicalSpiderOf 2 2)) firstIndex secondIndex
      = true := by decide

/-- ★ **The reduction fires: the connected `2 ⇒ 2` canonical spider realizes `⟨2, 2, [0,0,0,0]⟩` VIA the
connectivity reduction** (not per-instance `decide`).  `spiderPartition_of_allConnected` consumes the machine-checked
full connectivity of the `[μ, δ]` fold and produces the fully-connected partition — the reduction path the general
realization would ride once the `mergeToOne`/`fanToN` connectivity induction is built. -/
theorem extraSpider22_via_connectivityReduction :
    extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2)
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 0, 0, 0] } :=
  spiderPartition_of_allConnected 2 (processBrauer (brauerSeed 2) (canonicalSpiderOf 2 2))
    (fun firstIndex secondIndex firstBelow secondBelow =>
      canonicalSpider22_allConnected firstIndex firstBelow secondIndex secondBelow)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the deep-`foldEq` shift algebra + the connectivity->partition reduction SHIP (FROB-RESUME
r2).**  `shiftBrauerWord_zero` (`shift 0 = id`) and `shiftBrauerWord_add` (`shift (a+b) = shift a ∘ shift b`) are
the two `RawTwoCellExpr.whiskerLeft` readback-word normalisation atoms the EASY structural arms of `fullPreserves`
reduce to.  `spiderPartition_of_allConnected` reduces the B1 general-arity spider realization from a partition
computation to a pure CONNECTIVITY statement about the `mergeToOne`/`fanToN` union-find fold.  `= true`. -/
def fxTab_hasFoldLegShiftAlgebra : Bool := true

end FX1Poly.Polygraph
