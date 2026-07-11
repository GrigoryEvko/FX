import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm

/-! # BRAUER r25 GAP β — the base-permute bridge (the MAP-fusion route)

The r23 crossing trackers deliver COMPONENT preservation between the abstract adjacent-swap fold
`positions.foldl applyAdjacentSwap base` and the processed fold state.  The CUP / THROUGH chains additionally need the
POSITIONAL bridge: reading the abstract fold at an index equals reading the ORIGINAL base at the permuted index.  On the
SEED (`base = List.range width`) that bridge is definitional (`permuteOfCrossingWord width positions` IS the fold over
`List.range`), which is why the CAP chain needed nothing.  The CUP `topPerm` phase and the THROUGH `middle` / `topPerm`
phases run on POST-cup / POST-cap NON-seed states, so they need the general base ≠ range read-through — **GAP β**.

The route is MAP-FUSION (cleaner than the foldr composite-index route — boundedness fires exactly once):

  * `applyAdjacentSwap_map` — one swap commutes with a pointwise `map` (naturality; no boundedness).
  * `foldlAdjacentSwap_map` — the whole swap fold commutes with `map` (single induction on the word).
  * `foldlAdjacentSwapBase_eq_mapPermute` — the fusion: the abstract fold over any `base` equals the identity-range
    permutation `permuteOfCrossingWord base.length positions` read THROUGH `base` (via the swap fold applied at
    `List.range base.length`, then the range-map-self collapse `(List.range n).map (natListGetAt base) = base`).
  * `natListGetAt_foldlAdjacentSwapBase` — GAP β itself: reading the abstract fold at `index` (in range) equals reading
    `base` at `natListGetAt (permuteOfCrossingWord base.length positions) index`.

The base-permute width guard `index < base.length` fires at the CUP / THROUGH fire site via
`crossingWordFold_openWires_length` (the post-cup S4 width).  Raw Lean 4 + Init, STRUCTURAL, propext-free — the
internal range / map helpers are private public re-proofs of the `WiringDescArcConjugator`-private conjugator kit
(`getAtMapConj` / `getAtRangeConj` / `listExtGetAtConj`), avoiding a cross-file private reference.  The length lemmas
(`applyAdjacentSwap_length`, `foldlAdjacentSwap_length`, `permuteOfCrossingWord_length`) are the shipped
`WiringDescStandardForm` ones, reused. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The swap fold commutes with a pointwise map (naturality) -/

/-- One adjacent swap commutes with a pointwise `map` — full-enum matches, single induction on the list, no
boundedness. -/
theorem applyAdjacentSwap_map (mapFn : Nat → Nat) :
    (wires : List Nat) → (position : Nat) →
    applyAdjacentSwap (wires.map mapFn) position = (applyAdjacentSwap wires position).map mapFn
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 => by
      show applyAdjacentSwap (mapFn first :: (second :: rest).map mapFn) (position + 1)
          = (first :: applyAdjacentSwap (second :: rest) position).map mapFn
      show mapFn first :: applyAdjacentSwap ((second :: rest).map mapFn) position
          = mapFn first :: (applyAdjacentSwap (second :: rest) position).map mapFn
      rw [applyAdjacentSwap_map mapFn (second :: rest) position]

/-- The whole swap fold commutes with a pointwise `map` — a single induction on the word, one `applyAdjacentSwap_map`
rewrite per step. -/
theorem foldlAdjacentSwap_map (mapFn : Nat → Nat) :
    (positions : List Nat) → (base : List Nat) →
    positions.foldl applyAdjacentSwap (base.map mapFn)
      = (positions.foldl applyAdjacentSwap base).map mapFn
  | [], _ => rfl
  | position :: rest, base => by
      show rest.foldl applyAdjacentSwap (applyAdjacentSwap (base.map mapFn) position)
          = (rest.foldl applyAdjacentSwap (applyAdjacentSwap base position)).map mapFn
      rw [applyAdjacentSwap_map mapFn base position]
      exact foldlAdjacentSwap_map mapFn rest (applyAdjacentSwap base position)

/-! ## Internal range / map kit (private public re-proofs of the conjugator-private conjugator lemmas) -/

/-- Reading a `map` in range commutes with the function. -/
private theorem getAtInMapRange (mapFn : Nat → Nat) :
    (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt (entries.map mapFn) index = mapFn (natListGetAt entries index)
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, indexBelow =>
      getAtInMapRange mapFn rest index (Nat.lt_of_succ_lt_succ indexBelow)

private theorem rangeReadLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = (count + 1) + accumulated.length
      rw [rangeReadLoopLength count (count :: accumulated)]
      show count + (accumulated.length + 1) = (count + 1) + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem rangeReadLength (count : Nat) : (List.range count).length = count :=
  (rangeReadLoopLength count []).trans (Nat.add_zero count)

private theorem getAtRangeLoopPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := getAtRangeLoopPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem getAtRangeLoop : (count : Nat) → (accumulated : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact getAtRangeLoop count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ indexBelow) atLeast
          have pastRead : natListGetAt (List.range.loop count (count :: accumulated)) (0 + count)
              = natListGetAt (count :: accumulated) 0 := getAtRangeLoopPast count (count :: accumulated) 0
          rw [Nat.zero_add] at pastRead
          rw [indexEq]; exact pastRead

private theorem getAtRangeSelf (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  getAtRangeLoop count [] index indexBelow

private theorem natListMapLength (mapFn : Nat → Nat) : (entries : List Nat) →
    (entries.map mapFn).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (natListMapLength mapFn rest)

private theorem listExtByGetAt : (entriesLeft entriesRight : List Nat) →
    entriesLeft.length = entriesRight.length →
    (∀ index, index < entriesLeft.length → natListGetAt entriesLeft index = natListGetAt entriesRight index) →
    entriesLeft = entriesRight
  | [], [], _, _ => rfl
  | [], _ :: _, lengthsEq, _ => Nat.noConfusion lengthsEq
  | _ :: _, [], lengthsEq, _ => Nat.noConfusion lengthsEq
  | headLeft :: tailLeft, headRight :: tailRight, lengthsEq, getAtEq => by
      have headEq : headLeft = headRight := getAtEq 0 (Nat.succ_pos _)
      have tailEq : tailLeft = tailRight :=
        listExtByGetAt tailLeft tailRight (Nat.succ.inj lengthsEq)
          (fun index indexBelow => getAtEq (index + 1) (Nat.succ_lt_succ indexBelow))
      rw [headEq, tailEq]

/-- `(List.range base.length).map (natListGetAt base) = base` — the range-map-self collapse. -/
private theorem mapGetAtRangeSelf (base : List Nat) :
    (List.range base.length).map (natListGetAt base) = base := by
  apply listExtByGetAt
  · rw [natListMapLength, rangeReadLength]
  · intro index indexBelow
    rw [natListMapLength, rangeReadLength] at indexBelow
    rw [getAtInMapRange (natListGetAt base) (List.range base.length) index (by rw [rangeReadLength]; exact indexBelow),
      getAtRangeSelf base.length index indexBelow]

/-! ## The list-level fusion + GAP β -/

/-- ★★ **THE FUSION.**  The abstract adjacent-swap fold over an arbitrary `base` equals the identity-range permutation
`permuteOfCrossingWord base.length positions` read THROUGH `base` — proved by `foldlAdjacentSwap_map` at
`List.range base.length`, then the range-map-self collapse.  `permuteOfCrossingWord base.length positions` is
DEFINITIONALLY `positions.foldl applyAdjacentSwap (List.range base.length)`. -/
theorem foldlAdjacentSwapBase_eq_mapPermute (base positions : List Nat) :
    positions.foldl applyAdjacentSwap base
      = (permuteOfCrossingWord base.length positions).map (natListGetAt base) := by
  have h := foldlAdjacentSwap_map (natListGetAt base) positions (List.range base.length)
  rw [mapGetAtRangeSelf base] at h
  exact h

/-- ★★★ **GAP β — THE BASE-PERMUTE BRIDGE.**  Reading the abstract adjacent-swap fold over `base` at an in-range
`index` equals reading `base` at the permuted index `natListGetAt (permuteOfCrossingWord base.length positions) index`.
The CUP / THROUGH positional bridge the SEED-only CAP chain never needed.  The width guard `index < base.length` fires
at the fire site via `crossingWordFold_openWires_length`.  Machine-checked zero-axiom (`foldlAdjacentSwapBase_eq_mapPermute`
then the map read-through, the read-guard discharged by the shipped `permuteOfCrossingWord_length`). -/
theorem natListGetAt_foldlAdjacentSwapBase (base positions : List Nat) (index : Nat)
    (indexLt : index < base.length) :
    natListGetAt (positions.foldl applyAdjacentSwap base) index
      = natListGetAt base (natListGetAt (permuteOfCrossingWord base.length positions) index) := by
  rw [foldlAdjacentSwapBase_eq_mapPermute base positions,
    getAtInMapRange (natListGetAt base) (permuteOfCrossingWord base.length positions) index
      (by rw [permuteOfCrossingWord_length]; exact indexLt)]

/-- ★★ **Honesty marker — GAP β base-permute bridge SHIPPED (r25).**  `natListGetAt_foldlAdjacentSwapBase` is the
general base ≠ range read-through the CUP `topPerm` and THROUGH `middle` / `topPerm` phases consume.  A NEW ingredient
marker; it flips NO master. `= true`. -/
def fxBrauer_hasBasePermuteBridge : Bool := true

end FX1Poly.Polygraph
