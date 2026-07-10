import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideExtract

/-! # BRAUER-ARC-DESCENT r1 B1 — the distinguished-arc lexicographic descent MEASURE (breaching the pass-5-arc freeze)

The pass-5-arc wall (`Brauer/WiringDescCrossingComplete.lean:24-42`) is a MEASURE gap, not a truth wall: every
shipped cup-sink move fires and `ArcNonCrossing` holds, yet the `WiringDescInsertion` windowPin's `length` /
`inversionCount` monovariant is FROZEN across the cup-past-cap commute (the diagram — hence any diagram-derived
scalar — is invariant under every driver move by soundness).  The bequest was a distinguished-arc lexicographic
descent supplying the `Nat`-fuel the fold lacks.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`cupNonCupInversions`** — the PRIMARY coordinate: the count of ordered (cup-before-non-cup) pairs in a
    generator word.  It is `0` exactly when every cup already sits after every cap/crossing (the cup block is a
    tail block, as in the Graham–Lehrer standard form `capWord ++ crossingWord ++ cupWord`).  A cup sliding RIGHT
    past a cap/crossing drops it by one — the exact quantity the frozen `inversionCount` could not see, because it
    is measured on the WORD (list order to the fixed tail slot), not on the boundary matching.
  * **`cupPositionSum`** — the SECONDARY coordinate: the sum of the cup generators' `position` arguments.  A
    cup-past-cup slide holds the primary constant (both operands are cups) and drops this by two — the
    complementary descent the primary is blind to.
  * **`arcMeasure radix w = cupNonCupInversions w * radix + cupPositionSum w`** — the mixed-radix `Nat` embedding
    of the lex pair (the recon's `Mnat`), with the two combine lemmas turning a lex descent into a strict `Nat`
    fuel decrease.
  * ★ **the per-move STRICT-DESCENT lemmas, whiskered into arbitrary prefix/suffix context** — for the three
    disjoint-support / cup-cup shipped slides: `distantCupCapSlideFree8` (**the cup-past-cap commute, the crux** —
    `cupCap_inversions_lt`), `distantCupCrossingSlideFree8` (`cupCrossing_inversions_lt`), `distantCupCupSlideFree8`
    (primary held, `cupCup_positions_lt`).  Each drops `arcMeasure` strictly.
  * the NON-VACUITY eval (`arcDescent_nonVacuity_cupCap`): on the recon's minimal interleaved instance
    (`[cupAt 0, capAt 2]` conv-to `[capAt 0, cupAt 0]` via the cup-past-cap slide) the pair drops `(1,0) → (0,0)`
    and `arcMeasure` drops `8 → 0` — the exact configuration that froze every diagram-derived monovariant.

## The one RESISTING move — honestly walled (feeds B4)

The lone shipped cup-sink move on which this list-order measure does NOT descend is the ADJACENT-STRADDLE cup
slide `cupSlideRelation` (`BrauerConvFree8.cupSlide`): `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]`.  It
keeps the cup FIRST in list order (so `cupNonCupInversions` is frozen at `1`) and BUMPS the cup's position `0 → 1`
(so `cupPositionSum` ASCENDS by one) — a pure boundary reposition, not a list-order sink.  This is proven as a
theorem (`straddle_resists_arcMeasure`): the measure genuinely ascends there.  Its descent needs the boundary-slot
`legDistance` read off `standardForm(DiagramType)`, i.e. the crossing-only readback residual the recon names — so
the pass-5-arc wall is now pinned to EXACTLY the straddle-reposition move, no longer to the whole interleaved case.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup detector (structural on the wiring's input arity, propext-free) -/

/-- A generator atom is a CUP iff it consumes zero boundary inputs.  Among the Brauer generators only `cupAt`
(`inputCount = 0`) is a cup; `capAt` / `crossingAt` / `identityStrandAt` all consume `≥ 1`.  Structural `Nat`
match, so it reduces by `rfl` on the named atoms. -/
def isCupAtom (atom : BrauerAtom) : Bool :=
  match atom.wiring.inputCount with
  | 0 => true
  | _ + 1 => false

/-- A cup atom is detected as a cup. -/
theorem isCupAtom_cupAt (position : Nat) : isCupAtom (cupAt position) = true := rfl

/-- A cap atom is NOT a cup. -/
theorem isCupAtom_capAt (position : Nat) : isCupAtom (capAt position) = false := rfl

/-- A crossing atom is NOT a cup. -/
theorem isCupAtom_crossingAt (position : Nat) : isCupAtom (crossingAt position) = false := rfl

/-! ## The arc-structure counts of a word -/

/-- The number of NON-cup generators (caps / crossings) in a word. -/
def nonCupCount : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) 0 1 + nonCupCount rest

/-- The number of CUP generators in a word. -/
def cupCount : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) 1 0 + cupCount rest

/-- ★ **The PRIMARY descent coordinate** — the count of ordered (cup-before-non-cup) pairs: for each cup, how many
non-cup generators sit strictly to its right.  Zero exactly when the cups form a tail block (the standard-form cup
block).  A cup sliding right past a cap/crossing drops it by one. -/
def cupNonCupInversions : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) (nonCupCount rest) 0 + cupNonCupInversions rest

/-- ★ **The SECONDARY descent coordinate** — the sum of the cup generators' `position` arguments.  Frozen by a
cup-past-cap/crossing slide (the cup keeps its position), dropped by two by a cup-past-cup slide (the recon's
sibling-cup reorder). -/
def cupPositionSum : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) atom.position 0 + cupPositionSum rest

/-! ## Append laws (purely additive — NO multiplicative cross term, so propext-clean) -/

/-- `nonCupCount` is additive over append. -/
theorem nonCupCount_append : (wordLeft wordRight : List BrauerAtom) →
    nonCupCount (wordLeft ++ wordRight) = nonCupCount wordLeft + nonCupCount wordRight
  | [], wordRight => (Nat.zero_add (nonCupCount wordRight)).symm
  | atom :: rest, wordRight => by
      show cond (isCupAtom atom) 0 1 + nonCupCount (rest ++ wordRight)
         = cond (isCupAtom atom) 0 1 + nonCupCount rest + nonCupCount wordRight
      rw [nonCupCount_append rest wordRight]
      exact (Nat.add_assoc _ _ _).symm

/-- `cupPositionSum` is additive over append. -/
theorem cupPositionSum_append : (wordLeft wordRight : List BrauerAtom) →
    cupPositionSum (wordLeft ++ wordRight) = cupPositionSum wordLeft + cupPositionSum wordRight
  | [], wordRight => (Nat.zero_add (cupPositionSum wordRight)).symm
  | atom :: rest, wordRight => by
      show cond (isCupAtom atom) atom.position 0 + cupPositionSum (rest ++ wordRight)
         = cond (isCupAtom atom) atom.position 0 + cupPositionSum rest + cupPositionSum wordRight
      rw [cupPositionSum_append rest wordRight]
      exact (Nat.add_assoc _ _ _).symm

/-! ## Prefix-whiskering (multiplication-free: the head term is diagram-equal on the two candidate tails)

The general append law for `cupNonCupInversions` carries a `cupCount * nonCupCount` cross term (multiplication,
whose distribution `Nat.add_mul` leaks `propext`).  We sidestep it: to whisker a common PREFIX onto two candidate
words that share their `nonCupCount`, each prefix cup sees the SAME extra non-cup count on either candidate, so the
difference is transported unchanged.  Structural induction on the prefix, additive only. -/

/-- Whisker a common prefix onto a `cupNonCupInversions` difference: if two words agree on `nonCupCount` and differ
by `delta` in `cupNonCupInversions`, the same holds after prepending any prefix. -/
theorem cupNonCupInversions_prefix (prefixWord wordLeft wordRight : List BrauerAtom) (delta : Nat)
    (nonCupEq : nonCupCount wordLeft = nonCupCount wordRight)
    (invEq : cupNonCupInversions wordLeft = cupNonCupInversions wordRight + delta) :
    cupNonCupInversions (prefixWord ++ wordLeft)
      = cupNonCupInversions (prefixWord ++ wordRight) + delta := by
  induction prefixWord with
  | nil => exact invEq
  | cons atom rest ih =>
      show cond (isCupAtom atom) (nonCupCount (rest ++ wordLeft)) 0
             + cupNonCupInversions (rest ++ wordLeft)
         = cond (isCupAtom atom) (nonCupCount (rest ++ wordRight)) 0
             + cupNonCupInversions (rest ++ wordRight) + delta
      rw [nonCupCount_append rest wordLeft, nonCupCount_append rest wordRight, nonCupEq, ih]
      exact (Nat.add_assoc _ _ _).symm

/-- Whisker a common prefix onto a `cupPositionSum` difference. -/
theorem cupPositionSum_prefix (prefixWord wordLeft wordRight : List BrauerAtom) (delta : Nat)
    (posEq : cupPositionSum wordLeft = cupPositionSum wordRight + delta) :
    cupPositionSum (prefixWord ++ wordLeft)
      = cupPositionSum (prefixWord ++ wordRight) + delta := by
  rw [cupPositionSum_append, cupPositionSum_append, posEq]
  exact (Nat.add_assoc _ _ _).symm

/-! ## Per-move suffix cores (the local, whiskered-suffix descent of each shipped slide)

Each shipped cup-sink move is a two-atom rewrite; the `cupNonCupInversions` / `cupPositionSum` change is computed
on the two-atom head against an arbitrary suffix, by definitional reduction of the `cond`s on the concrete atoms
(`isCupAtom (cupAt …) = true`, `isCupAtom (capAt …) = isCupAtom (crossingAt …) = false`). -/

/-- **Cup-past-cap** (`distantCupCapSlideFree8`) drops `cupNonCupInversions` by one against any suffix. -/
theorem cupInv_core_cupCap (cupPos capPos : Nat) (suffix : List BrauerAtom) :
    cupNonCupInversions (cupAt cupPos :: capAt (capPos + 2) :: suffix)
      = cupNonCupInversions (capAt capPos :: cupAt cupPos :: suffix) + 1 := by
  show (1 + nonCupCount suffix) + (0 + cupNonCupInversions suffix)
     = (0 + (nonCupCount suffix + cupNonCupInversions suffix)) + 1
  rw [Nat.zero_add, Nat.zero_add, Nat.add_assoc]
  exact Nat.add_comm 1 _

/-- **Cup-past-crossing** (`distantCupCrossingSlideFree8`) drops `cupNonCupInversions` by one against any suffix. -/
theorem cupInv_core_cupCrossing (cupPos crossPos : Nat) (suffix : List BrauerAtom) :
    cupNonCupInversions (cupAt cupPos :: crossingAt (crossPos + 2) :: suffix)
      = cupNonCupInversions (crossingAt crossPos :: cupAt cupPos :: suffix) + 1 := by
  show (1 + nonCupCount suffix) + (0 + cupNonCupInversions suffix)
     = (0 + (nonCupCount suffix + cupNonCupInversions suffix)) + 1
  rw [Nat.zero_add, Nat.zero_add, Nat.add_assoc]
  exact Nat.add_comm 1 _

/-- **Cup-past-cup** (`distantCupCupSlideFree8`) HOLDS `cupNonCupInversions` (both operands are cups). -/
theorem cupInv_core_cupCup (cupLeft cupRight : Nat) (suffix : List BrauerAtom) :
    cupNonCupInversions (cupAt cupLeft :: cupAt (cupRight + 2) :: suffix)
      = cupNonCupInversions (cupAt cupRight :: cupAt cupLeft :: suffix) := rfl

/-- The `nonCupCount` of the cup-past-cap head is unchanged (the pair swaps one cup and one cap). -/
theorem nonCupCount_core_cupCap (cupPos capPos : Nat) (suffix : List BrauerAtom) :
    nonCupCount (cupAt cupPos :: capAt (capPos + 2) :: suffix)
      = nonCupCount (capAt capPos :: cupAt cupPos :: suffix) := by
  show 0 + (1 + nonCupCount suffix) = 1 + (0 + nonCupCount suffix)
  rw [Nat.zero_add, Nat.zero_add]

/-- The `nonCupCount` of the cup-past-crossing head is unchanged. -/
theorem nonCupCount_core_cupCrossing (cupPos crossPos : Nat) (suffix : List BrauerAtom) :
    nonCupCount (cupAt cupPos :: crossingAt (crossPos + 2) :: suffix)
      = nonCupCount (crossingAt crossPos :: cupAt cupPos :: suffix) := by
  show 0 + (1 + nonCupCount suffix) = 1 + (0 + nonCupCount suffix)
  rw [Nat.zero_add, Nat.zero_add]

/-- The bare `cupPositionSum` of a cup-past-cup head drops by two (`cupRight + 2 ↝ cupRight`). -/
theorem cupPos_core_cupCup (cupLeft cupRight : Nat) :
    cupPositionSum [cupAt cupLeft, cupAt (cupRight + 2)]
      = cupPositionSum [cupAt cupRight, cupAt cupLeft] + 2 := by
  show cupLeft + ((cupRight + 2) + 0) = (cupRight + (cupLeft + 0)) + 2
  rw [Nat.add_zero (cupRight + 2), Nat.add_zero cupLeft, ← Nat.add_assoc, Nat.add_comm cupLeft cupRight]

/-- The suffix-whiskered cup-past-cup `cupPositionSum` drop by two. -/
theorem cupPos_core_cupCup_suffix (cupLeft cupRight : Nat) (suffix : List BrauerAtom) :
    cupPositionSum (cupAt cupLeft :: cupAt (cupRight + 2) :: suffix)
      = cupPositionSum (cupAt cupRight :: cupAt cupLeft :: suffix) + 2 := by
  have hLeft : cupPositionSum (cupAt cupLeft :: cupAt (cupRight + 2) :: suffix)
      = cupPositionSum [cupAt cupLeft, cupAt (cupRight + 2)] + cupPositionSum suffix :=
    cupPositionSum_append [cupAt cupLeft, cupAt (cupRight + 2)] suffix
  have hRight : cupPositionSum (cupAt cupRight :: cupAt cupLeft :: suffix)
      = cupPositionSum [cupAt cupRight, cupAt cupLeft] + cupPositionSum suffix :=
    cupPositionSum_append [cupAt cupRight, cupAt cupLeft] suffix
  rw [hLeft, hRight, cupPos_core_cupCup]
  exact Nat.add_right_comm _ 2 _

/-! ## The whiskered per-move descents (equality forms, then strict `<`) -/

/-- ★ **The cup-past-cap descent, whiskered into arbitrary context.**  The `distantCupCapSlideFree8` slide
`prefix ++ [cupAt cupPos, capAt (capPos+2)] ++ suffix ↝ prefix ++ [capAt capPos, cupAt cupPos] ++ suffix` drops
`cupNonCupInversions` by exactly one — the crux commute the frozen `inversionCount` could not descend. -/
theorem cupCap_inversions_descends (cupPos capPos : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupNonCupInversions (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord))
      = cupNonCupInversions (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord)) + 1 :=
  cupNonCupInversions_prefix prefixWord
    ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)
    ([capAt capPos, cupAt cupPos] ++ suffixWord) 1
    (nonCupCount_core_cupCap cupPos capPos suffixWord)
    (cupInv_core_cupCap cupPos capPos suffixWord)

/-- ★ The strict cup-past-cap descent. -/
theorem cupCap_inversions_lt (cupPos capPos : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupNonCupInversions (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
      < cupNonCupInversions (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)) := by
  rw [cupCap_inversions_descends]
  exact Nat.lt_succ_self _

/-- ★ **The cup-past-crossing descent, whiskered into arbitrary context.** -/
theorem cupCrossing_inversions_descends (cupPos crossPos : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupNonCupInversions (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord))
      = cupNonCupInversions (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord)) + 1 :=
  cupNonCupInversions_prefix prefixWord
    ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)
    ([crossingAt crossPos, cupAt cupPos] ++ suffixWord) 1
    (nonCupCount_core_cupCrossing cupPos crossPos suffixWord)
    (cupInv_core_cupCrossing cupPos crossPos suffixWord)

/-- ★ The strict cup-past-crossing descent. -/
theorem cupCrossing_inversions_lt (cupPos crossPos : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupNonCupInversions (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
      < cupNonCupInversions (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)) := by
  rw [cupCrossing_inversions_descends]
  exact Nat.lt_succ_self _

/-- ★ **The cup-past-cup primary is HELD** (both operands are cups). -/
theorem cupCup_inversions_eq (cupLeft cupRight : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupNonCupInversions (prefixWord ++ ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord))
      = cupNonCupInversions (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord)) := by
  have key := cupNonCupInversions_prefix prefixWord
    ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord)
    ([cupAt cupRight, cupAt cupLeft] ++ suffixWord) 0
    rfl
    ((cupInv_core_cupCup cupLeft cupRight suffixWord).trans (Nat.add_zero _).symm)
  rw [Nat.add_zero] at key
  exact key

/-- ★ **The cup-past-cup SECONDARY descent, whiskered into arbitrary context.** -/
theorem cupCup_positions_descends (cupLeft cupRight : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupPositionSum (prefixWord ++ ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord))
      = cupPositionSum (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord)) + 2 :=
  cupPositionSum_prefix prefixWord
    ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord)
    ([cupAt cupRight, cupAt cupLeft] ++ suffixWord) 2
    (cupPos_core_cupCup_suffix cupLeft cupRight suffixWord)

/-- ★ The strict cup-past-cup secondary descent. -/
theorem cupCup_positions_lt (cupLeft cupRight : Nat) (prefixWord suffixWord : List BrauerAtom) :
    cupPositionSum (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord))
      < cupPositionSum (prefixWord ++ ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord)) := by
  rw [cupCup_positions_descends]
  have step := Nat.add_lt_add_left (show (0 : Nat) < 2 by decide)
    (cupPositionSum (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord)))
  rwa [Nat.add_zero] at step

/-! ## The `Nat`-embedded lex measure (the recon's `Mnat`) + the lex→`Nat` combine lemmas -/

/-- ★ **The mixed-radix `Nat` embedding of the lex pair** — `cupNonCupInversions · radix + cupPositionSum`.  With
`radix` chosen above every reachable `cupPositionSum`, this is a strictly-decreasing `Nat` fuel for the sort. -/
def arcMeasure (radix : Nat) (word : List BrauerAtom) : Nat :=
  cupNonCupInversions word * radix + cupPositionSum word

/-- Multiplication-free `(k+1)·r = k·r + r` (via `Nat.mul_succ` + `Nat.mul_comm`, both propext-clean). -/
private theorem succMulLocal (multiplier radix : Nat) :
    (multiplier + 1) * radix = multiplier * radix + radix := by
  rw [Nat.mul_comm (multiplier + 1) radix, Nat.mul_succ, Nat.mul_comm radix multiplier]

/-- ★ **Primary drop ⟹ `arcMeasure` drop** (given the secondary is below the radix on the after-word). -/
theorem arcMeasure_lt_of_primary (radix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primLt : cupNonCupInversions wordAfter < cupNonCupInversions wordBefore)
    (secBound : cupPositionSum wordAfter < radix) :
    arcMeasure radix wordAfter < arcMeasure radix wordBefore := by
  have blockLe : cupNonCupInversions wordAfter * radix + radix
      ≤ cupNonCupInversions wordBefore * radix := by
    rw [← succMulLocal]
    exact Nat.mul_le_mul_right radix primLt
  have belowBlock : cupNonCupInversions wordAfter * radix + cupPositionSum wordAfter
      < cupNonCupInversions wordAfter * radix + radix :=
    Nat.add_lt_add_left secBound _
  show cupNonCupInversions wordAfter * radix + cupPositionSum wordAfter
     < cupNonCupInversions wordBefore * radix + cupPositionSum wordBefore
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le belowBlock blockLe) (Nat.le_add_right _ _)

/-- ★ **Primary held + secondary drop ⟹ `arcMeasure` drop** (no radix bound needed). -/
theorem arcMeasure_lt_of_secondary (radix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primEq : cupNonCupInversions wordAfter = cupNonCupInversions wordBefore)
    (secLt : cupPositionSum wordAfter < cupPositionSum wordBefore) :
    arcMeasure radix wordAfter < arcMeasure radix wordBefore := by
  show cupNonCupInversions wordAfter * radix + cupPositionSum wordAfter
     < cupNonCupInversions wordBefore * radix + cupPositionSum wordBefore
  rw [primEq]
  exact Nat.add_lt_add_left secLt _

/-! ## Non-vacuity — the recon's minimal interleaved instance -/

/-- ★ **Non-vacuity eval on the minimal interleaved instance.**  The recon's cap/cup interleave, minimally
`[cupAt 0, capAt 2]`, is `BrauerConvFree8` to `[capAt 0, cupAt 0]` by the cup-past-cap slide, and BOTH descent
coordinates confirm the drop the frozen monovariants could not see: the primary drops `1 → 0`, the secondary is
held at `0`, and the `Nat` fuel `arcMeasure 8` drops `8 → 0`.  This is exactly the configuration (a cup forced past
a cap) the pass-5-arc wall named. -/
theorem arcDescent_nonVacuity_cupCap :
    BrauerConvFree8 [cupAt 0, capAt 2] [capAt 0, cupAt 0]
      ∧ cupNonCupInversions [capAt 0, cupAt 0] < cupNonCupInversions [cupAt 0, capAt 2]
      ∧ cupPositionSum [capAt 0, cupAt 0] = cupPositionSum [cupAt 0, capAt 2]
      ∧ arcMeasure 8 [capAt 0, cupAt 0] < arcMeasure 8 [cupAt 0, capAt 2] :=
  ⟨distantCupCapSlideFree8 0 0 (Nat.le_refl 0), by decide, by decide, by decide⟩

/-- ★ **Non-vacuity eval on the cup-past-cup reorder.**  `[cupAt 0, cupAt 2]` is `BrauerConvFree8` to
`[cupAt 0, cupAt 0]` by the cup-past-cup slide; the primary is HELD at `0`, the secondary drops `2 → 0`, and the
fuel `arcMeasure 8` drops `2 → 0` — the complementary descent the primary is blind to. -/
theorem arcDescent_nonVacuity_cupCup :
    BrauerConvFree8 [cupAt 0, cupAt 2] [cupAt 0, cupAt 0]
      ∧ cupNonCupInversions [cupAt 0, cupAt 0] = cupNonCupInversions [cupAt 0, cupAt 2]
      ∧ cupPositionSum [cupAt 0, cupAt 0] < cupPositionSum [cupAt 0, cupAt 2]
      ∧ arcMeasure 8 [cupAt 0, cupAt 0] < arcMeasure 8 [cupAt 0, cupAt 2] :=
  ⟨distantCupCupSlideFree8 0 0 (Nat.le_refl 0), by decide, by decide, by decide⟩

/-! ## The ONE resisting move, proven — the honest pass-5-arc wall, now pinned to the straddle -/

/-- ★★ **The adjacent-straddle cup slide RESISTS the list-order measure — a THEOREM.**  The shipped
`BrauerConvFree8.cupSlide` row `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` keeps the cup FIRST in list
order, so `cupNonCupInversions` is FROZEN (both `1`), and BUMPS the cup's position `0 → 1`, so `cupPositionSum`
strictly ASCENDS (`0 < 1`).  Hence NO list-order lex measure `(cupNonCupInversions, cupPositionSum)` descends on
the straddle: it is a boundary reposition, not a list-order sink.  This pins the pass-5-arc wall to EXACTLY the
straddle-reposition move — its descent needs the boundary-slot `legDistance` read off `standardForm(DiagramType)`
(the crossing-only readback residual, `Brauer/WiringDescBrauerLedger.lean`), which is unbuilt. -/
theorem straddle_resists_arcMeasure :
    cupNonCupInversions [cupAt 1, crossingAt 0] = cupNonCupInversions [cupAt 0, crossingAt 1]
      ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0] :=
  ⟨by decide, by decide⟩

/-- The straddle IS a genuine `BrauerConvFree8` move (non-vacuity of the resister). -/
theorem straddle_isMove : BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] :=
  BrauerConvFree8.cupSlide 0

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the distinguished-arc descent MEASURE is SHIPPED and STRICTLY DESCENDS on the
disjoint-support / cup-cup cup-sink moves (B1).**  The lex pair `(cupNonCupInversions, cupPositionSum)` and its
`Nat` embedding `arcMeasure` are defined and computing; the whiskered per-move strict descents are proven for the
cup-past-cap commute (`cupCap_inversions_lt` — the crux the frozen `inversionCount` could not descend), the
cup-past-crossing slide (`cupCrossing_inversions_lt`), and the cup-past-cup reorder (`cupCup_positions_lt`, primary
held by `cupCup_inversions_eq`); the lex→`Nat` combine lemmas (`arcMeasure_lt_of_primary` /
`arcMeasure_lt_of_secondary`) turn each into a strict fuel decrease.  Non-vacuity: on the recon's minimal
interleaved instance the fuel drops `8 → 0` (`arcDescent_nonVacuity_cupCap`) and on the cup reorder `2 → 0`
(`arcDescent_nonVacuity_cupCup`).  `= true`. -/
def fxBrauer_hasArcDescentMeasure : Bool := true

/-- **Honesty WALL marker — the FULL cup-sink monovariant across ALL shipped moves is NOT achieved (B1 residual =
the straddle).**  The list-order lex measure descends on the three disjoint-support / cup-cup moves but PROVABLY
RESISTS the adjacent-straddle cup slide (`straddle_resists_arcMeasure`: primary frozen, secondary ascends), because
the straddle is a boundary reposition (cup and its straddling crossing keep list order), not a list-order sink.  So
a single `Nat`-fuel monovariant covering EVERY cup-sink move needs the boundary-slot `legDistance` read off the
crossing-only readback `standardForm(DiagramType)` — the residual the recon named and the pass-5-arc wall is now
pinned to.  The full V2 completeness `fxBrauer_hasBrauerV2FullCompleteness` stays `false`; #2013 does not close on
B1 alone.  `= false`. -/
def fxBrauer_hasArcDescentFullMonovariant : Bool := false

end FX1Poly.Polygraph
