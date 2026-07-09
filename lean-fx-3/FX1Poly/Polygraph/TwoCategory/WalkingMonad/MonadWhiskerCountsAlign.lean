import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult

/-! # WalkingMonad — the COUNTS-ALIGNMENT for the two whisker `normalizeCell` cases

`wordMul_whiskerLeft` / `wordMul_whiskerRight` produce the canonical word of the ONES-prefixed / ONES-appended
counts.  To line those words up with `canon (whiskerLeft/Right W body)`, one needs the COUNTS-level identity: the
per-target multiplicity list (`countsOf`) of the ordinal-sum embedding of a body's map is the body's own multiplicity
list with a `1`-run prepended (left whisker) / appended (right whisker).

## What this file ships (each piece zero-axiom)

  * **`countsOf_shiftPrepend`** — `countsOf` is invariant under a uniform value shift (`runLengthAt` / `dropRunAt`
    shift-invariance).
  * **`countsOf_ascendingPrepend`** — reading `countsOf` past a strictly-ascending prefix `[base, …, base+leftLen-1]`
    (whose values never recur in a tail bounded below by `base+leftLen`) yields a `1`-run then the tail's counts.
  * ★ **`countsOf_embedLocalMap_left`** — `countsOf (L+M) 0 (embedLocalMap L M 0 values) = 1^L ++ countsOf M 0 values`
    (unconditional — the left ordinal-sum block is the strictly-ascending identity prefix).
  * **`countsOf_consAppend_split`** — reading `countsOf` off a cons-append splits at the range boundary, for a
    WEAKLY-INCREASING first block bounded into `[base, base+a)` and a second block bounded below by `base+a`.
  * ★ **`countsOf_embedLocalMap_right`** — `countsOf (M+R) 0 (embedLocalMap 0 M R values) =
    countsOf M 0 values ++ 1^R` (needs `values` weakly increasing + `mapsInto M` — the fold invariants).
  * ★ **`canonCounts_whiskerLeft` / `canonCounts_whiskerRight`** — the two headline corollaries: the canonical
    counts of a whiskered cell is the body's canonical counts with a `1`-run prepended (left) / appended (right).
    These reduce the two whisker `normalizeCell` cases to the shipped `wordMul_whisker*` + boundary transport.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`List Nat` / `Nat`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- Left-cancellation of `Nat` addition, propext-clean (the library `Nat.add_left_cancel` pulls `propext`; this
structural induction on the cancelled summand does not). -/
theorem natAddLeftCancel : ∀ (base head offset : Nat), base + head = base + offset → head = offset
  | 0, head, offset, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | base + 1, head, offset, h => by
      rw [Nat.succ_add, Nat.succ_add] at h
      exact natAddLeftCancel base head offset (Nat.succ.inj h)

/-! ## `countsOf` is invariant under a uniform value shift -/

/-- `runLengthAt` is invariant under a uniform `+base` shift of both the values and the target. -/
theorem runLengthAt_shiftPrepend : ∀ (base offset : Nat) (values : List Nat),
    runLengthAt (base + offset) (shiftPrepend base values []) = runLengthAt offset values
  | _, _, [] => rfl
  | base, offset, head :: rest => by
      show runLengthAt (base + offset) ((base + head) :: shiftPrepend base rest [])
        = runLengthAt offset (head :: rest)
      rcases Nat.decEq head offset with h | h
      · rw [runLengthAt_cons_neg (fun heq => h (natAddLeftCancel base head offset heq)), runLengthAt_cons_neg h]
      · rw [runLengthAt_cons_pos (congrArg (base + ·) h),
            runLengthAt_cons_pos h, runLengthAt_shiftPrepend base offset rest]

/-- `dropRunAt` commutes with a uniform `+base` shift. -/
theorem dropRunAt_shiftPrepend : ∀ (base offset : Nat) (values : List Nat),
    dropRunAt (base + offset) (shiftPrepend base values [])
      = shiftPrepend base (dropRunAt offset values) []
  | _, _, [] => rfl
  | base, offset, head :: rest => by
      show dropRunAt (base + offset) ((base + head) :: shiftPrepend base rest [])
        = shiftPrepend base (dropRunAt offset (head :: rest)) []
      rcases Nat.decEq head offset with h | h
      · rw [dropRunAt_cons_neg (fun heq => h (natAddLeftCancel base head offset heq)), dropRunAt_cons_neg h]; rfl
      · rw [dropRunAt_cons_pos (congrArg (base + ·) h),
            dropRunAt_cons_pos h, dropRunAt_shiftPrepend base offset rest]

/-- ★ `countsOf` reads the same multiplicities off a uniformly `+base`-shifted value-list (target shifted by the
same `base`).  Structural on the target count. -/
theorem countsOf_shiftPrepend : ∀ (n offset base : Nat) (values : List Nat),
    countsOf n (base + offset) (shiftPrepend base values []) = countsOf n offset values
  | 0, _, _, _ => rfl
  | n + 1, offset, base, values => by
      show runLengthAt (base + offset) (shiftPrepend base values [])
          :: countsOf n (base + offset + 1) (dropRunAt (base + offset) (shiftPrepend base values []))
        = runLengthAt offset values :: countsOf n (offset + 1) (dropRunAt offset values)
      rw [runLengthAt_shiftPrepend, dropRunAt_shiftPrepend]
      rw [show base + offset + 1 = base + (offset + 1) from Nat.add_assoc base offset 1]
      rw [countsOf_shiftPrepend n (offset + 1) base (dropRunAt offset values)]

/-! ## Peeling `countsOf` past a strictly-ascending identity prefix -/

/-- A value-list whose leading run at `base` is empty is unchanged by `dropRunAt base`. -/
theorem dropRunAt_of_runLengthAt_zero : ∀ (base : Nat) (list : List Nat),
    runLengthAt base list = 0 → dropRunAt base list = list
  | _, [], _ => rfl
  | base, head :: rest, h => by
      rcases Nat.decEq head base with hne | heq
      · exact dropRunAt_cons_neg hne
      · rw [runLengthAt_cons_pos heq] at h; exact Nat.noConfusion h

/-- The leading `base`-run of an ascending prefix `[start, …]` (with `base < start`) into a tail all exceeding
`base` is empty. -/
theorem runLengthAt_ascendingPrepend_zero : ∀ (leftLen start base : Nat) (tail : List Nat),
    base < start → (∀ pos, pos < tail.length → base < monotoneMapGet tail pos) →
    runLengthAt base (ascendingPrepend start leftLen tail) = 0
  | 0, _, base, tail, _, htail => by
      cases tail with
      | nil => rfl
      | cons head rest =>
          exact runLengthAt_cons_neg (fun heq => Nat.lt_irrefl base (heq ▸ htail 0 (Nat.succ_pos _)))
  | leftLen + 1, start, base, tail, hlt, _ => by
      show runLengthAt base (start :: ascendingPrepend (start + 1) leftLen tail) = 0
      exact runLengthAt_cons_neg (fun heq => Nat.lt_irrefl base (heq ▸ hlt))

/-- ★ Reading `countsOf` past a strictly-ascending prefix `[base, …, base+leftLen-1]` (whose values never recur in
`tail`, i.e. every tail value is `≥ base + leftLen`) yields a `1`-run of length `leftLen` then the tail's counts
read from `base + leftLen`.  Structural on `leftLen`. -/
theorem countsOf_ascendingPrepend : ∀ (leftLen n base : Nat) (tail : List Nat),
    (∀ pos, pos < tail.length → base + leftLen ≤ monotoneMapGet tail pos) →
    countsOf (leftLen + n) base (ascendingPrepend base leftLen tail)
      = consReplicate 1 leftLen (countsOf n (base + leftLen) tail)
  | 0, n, base, tail, _ => by
      show countsOf (0 + n) base tail = countsOf n (base + 0) tail
      rw [Nat.zero_add, Nat.add_zero]
  | leftLen + 1, n, base, tail, htail => by
      show countsOf (leftLen + 1 + n) base (base :: ascendingPrepend (base + 1) leftLen tail)
        = 1 :: consReplicate 1 leftLen (countsOf n (base + (leftLen + 1)) tail)
      have hrun0 : runLengthAt base (ascendingPrepend (base + 1) leftLen tail) = 0 :=
        runLengthAt_ascendingPrepend_zero leftLen (base + 1) base tail (Nat.lt_succ_self base)
          (fun pos hpos => Nat.lt_of_lt_of_le (Nat.lt_succ_self base)
            (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right base leftLen))
              (by have := htail pos hpos; rw [Nat.add_succ] at this; exact this)))
      rw [show leftLen + 1 + n = (leftLen + n) + 1 from Nat.succ_add leftLen n]
      show runLengthAt base (base :: ascendingPrepend (base + 1) leftLen tail)
          :: countsOf (leftLen + n) (base + 1)
            (dropRunAt base (base :: ascendingPrepend (base + 1) leftLen tail))
        = 1 :: consReplicate 1 leftLen (countsOf n (base + (leftLen + 1)) tail)
      rw [runLengthAt_cons_pos (rfl : base = base), hrun0,
          dropRunAt_cons_pos (rfl : base = base),
          dropRunAt_of_runLengthAt_zero base (ascendingPrepend (base + 1) leftLen tail) hrun0]
      show 1 :: countsOf (leftLen + n) (base + 1) (ascendingPrepend (base + 1) leftLen tail)
        = 1 :: consReplicate 1 leftLen (countsOf n (base + (leftLen + 1)) tail)
      rw [countsOf_ascendingPrepend leftLen n (base + 1) tail
            (fun pos hpos => by have := htail pos hpos; rw [Nat.add_succ] at this;
                                rw [Nat.succ_add]; exact this)]
      show 1 :: consReplicate 1 leftLen (countsOf n (base + 1 + leftLen) tail)
        = 1 :: consReplicate 1 leftLen (countsOf n (base + (leftLen + 1)) tail)
      rw [show base + 1 + leftLen = base + (leftLen + 1) from by
            rw [Nat.add_assoc, Nat.add_comm 1 leftLen]]

/-! ## The LEFT counts lift -/

/-- ★ **LEFT counts lift.**  The per-target multiplicity list of the LEFT ordinal-sum embedding is the body's
multiplicity list with a `1`-run of length `leftLen` PREPENDED — unconditional, since the left block is the
strictly-ascending identity prefix and the shifted body block sits above it. -/
theorem countsOf_embedLocalMap_left (leftLen midLen : Nat) (values : List Nat) :
    countsOf (leftLen + midLen) 0 (embedLocalMap leftLen midLen 0 values)
      = consReplicate 1 leftLen (countsOf midLen 0 values) := by
  show countsOf (leftLen + midLen) 0
      (ascendingPrepend 0 leftLen (shiftPrepend leftLen values []))
    = consReplicate 1 leftLen (countsOf midLen 0 values)
  rw [countsOf_ascendingPrepend leftLen midLen 0 (shiftPrepend leftLen values [])
        (fun pos hpos => by
          have hlen : pos < values.length := by rw [shiftPrepend_length] at hpos; exact hpos
          rw [shiftPrepend_get_lt leftLen values pos [] hlen, Nat.zero_add]
          exact Nat.le_add_right leftLen _)]
  rw [Nat.zero_add]
  rw [show countsOf midLen leftLen (shiftPrepend leftLen values [])
        = countsOf midLen (leftLen + 0) (shiftPrepend leftLen values []) from by rw [Nat.add_zero]]
  rw [countsOf_shiftPrepend midLen 0 leftLen values]

/-! ## Splitting `countsOf` off a cons-append (the RIGHT lift's workhorse) -/

/-- A value-list bounded strictly below by `base` has an empty leading `base`-run. -/
theorem runLengthAt_zero_of_lowerBound : ∀ (base : Nat) (list : List Nat),
    (∀ pos, pos < list.length → base < monotoneMapGet list pos) → runLengthAt base list = 0
  | _, [], _ => rfl
  | base, head :: _, hlow =>
      runLengthAt_cons_neg (fun heq => Nat.lt_irrefl base (heq ▸ hlow 0 (Nat.succ_pos _)))

/-- The leading `base`-run of a cons-append is that of the first block when the second has no leading `base`. -/
theorem runLengthAt_consAppend : ∀ (base : Nat) (list1 list2 : List Nat),
    runLengthAt base list2 = 0 → runLengthAt base (consAppend list1 list2) = runLengthAt base list1
  | _, [], _, hl2 => hl2
  | base, head :: rest, list2, hl2 => by
      show runLengthAt base (head :: consAppend rest list2) = runLengthAt base (head :: rest)
      rcases Nat.decEq head base with hne | heq
      · rw [runLengthAt_cons_neg hne, runLengthAt_cons_neg hne]
      · rw [runLengthAt_cons_pos heq, runLengthAt_cons_pos heq, runLengthAt_consAppend base rest list2 hl2]

/-- Dropping the leading `base`-run of a cons-append drops it from the first block (second has no leading `base`). -/
theorem dropRunAt_consAppend : ∀ (base : Nat) (list1 list2 : List Nat),
    runLengthAt base list2 = 0 →
    dropRunAt base (consAppend list1 list2) = consAppend (dropRunAt base list1) list2
  | base, [], list2, hl2 => dropRunAt_of_runLengthAt_zero base list2 hl2
  | base, head :: rest, list2, hl2 => by
      show dropRunAt base (head :: consAppend rest list2)
        = consAppend (dropRunAt base (head :: rest)) list2
      rcases Nat.decEq head base with hne | heq
      · rw [dropRunAt_cons_neg hne, dropRunAt_cons_neg hne]; rfl
      · rw [dropRunAt_cons_pos heq, dropRunAt_cons_pos heq, dropRunAt_consAppend base rest list2 hl2]

/-- ★ Reading `countsOf` off a cons-append SPLITS at the range boundary: the first block (weakly increasing, values
in `[base, base+a)`) accounts for the first `a` targets, the second block (values `≥ base+a`) for the rest. -/
theorem countsOf_consAppend_split : ∀ (a b base : Nat) (list1 list2 : List Nat),
    isWeaklyIncreasing list1 →
    (∀ pos, pos < list1.length → base ≤ monotoneMapGet list1 pos) →
    (∀ pos, pos < list1.length → monotoneMapGet list1 pos < base + a) →
    (∀ pos, pos < list2.length → base + a ≤ monotoneMapGet list2 pos) →
    countsOf (a + b) base (consAppend list1 list2)
      = consAppend (countsOf a base list1) (countsOf b (base + a) list2)
  | 0, b, base, list1, list2, _, hlow, hupper, _ => by
      cases list1 with
      | nil =>
          show countsOf (0 + b) base list2 = countsOf b (base + 0) list2
          rw [Nat.zero_add, Nat.add_zero]
      | cons head _ =>
          exact absurd (hlow 0 (Nat.succ_pos _)) (Nat.not_le.mpr (by
            have := hupper 0 (Nat.succ_pos _); rwa [Nat.add_zero] at this))
  | a + 1, b, base, list1, list2, hmono, hlow, hupper, hl2low => by
      have hAddSwap : base + 1 + a = base + (a + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 a]
      have hl2zero : runLengthAt base list2 = 0 :=
        runLengthAt_zero_of_lowerBound base list2 (fun pos hpos =>
          Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right base a)) (hl2low pos hpos))
      rw [show a + 1 + b = (a + b) + 1 from Nat.succ_add a b]
      show runLengthAt base (consAppend list1 list2)
          :: countsOf (a + b) (base + 1) (dropRunAt base (consAppend list1 list2))
        = consAppend (runLengthAt base list1 :: countsOf a (base + 1) (dropRunAt base list1))
            (countsOf b (base + (a + 1)) list2)
      rw [runLengthAt_consAppend base list1 list2 hl2zero,
          dropRunAt_consAppend base list1 list2 hl2zero]
      show runLengthAt base list1
          :: countsOf (a + b) (base + 1) (consAppend (dropRunAt base list1) list2)
        = runLengthAt base list1
          :: consAppend (countsOf a (base + 1) (dropRunAt base list1))
              (countsOf b (base + (a + 1)) list2)
      have hUpperDrop : ∀ pos, pos < (dropRunAt base list1).length →
          monotoneMapGet (dropRunAt base list1) pos < base + 1 + a := by
        have hcap : mapsInto list1 (base + 1 + a) := fun p hp => by rw [hAddSwap]; exact hupper p hp
        intro pos hpos
        exact dropRunAt_mapsInto base list1 (base + 1 + a) hcap pos hpos
      rw [countsOf_consAppend_split a b (base + 1) (dropRunAt base list1) list2
            (dropRunAt_isWeaklyIncreasing base list1 hmono)
            (dropRunAt_lowerBound base list1 hmono hlow)
            hUpperDrop
            (fun pos hpos => by rw [hAddSwap]; exact hl2low pos hpos)]
      rw [hAddSwap]

/-! ## The RIGHT counts lift -/

/-- Shifting a value-list by `0` is the identity (up to `Nat.zero_add`), realised as a cons-append. -/
theorem shiftPrepend_zero : ∀ (values tail : List Nat),
    shiftPrepend 0 values tail = consAppend values tail
  | [], _ => rfl
  | head :: rest, tail => by
      show (0 + head) :: shiftPrepend 0 rest tail = head :: consAppend rest tail
      rw [Nat.zero_add, shiftPrepend_zero rest tail]

/-- ★ **RIGHT counts lift.**  The per-target multiplicity list of the RIGHT ordinal-sum embedding is the body's
multiplicity list with a `1`-run of length `rightLen` APPENDED — given `values` weakly increasing and mapping into
`[midLen]` (the fold invariants), so the split at the range boundary consumes exactly the body block and leaves the
strictly-ascending top identity block. -/
theorem countsOf_embedLocalMap_right (midLen rightLen : Nat) (values : List Nat)
    (hmono : isWeaklyIncreasing values) (hinto : mapsInto values midLen) :
    countsOf (midLen + rightLen) 0 (embedLocalMap 0 midLen rightLen values)
      = consAppend (countsOf midLen 0 values) (monadOnes rightLen) := by
  show countsOf (midLen + rightLen) 0
      (shiftPrepend 0 values (ascendingFrom (0 + midLen) rightLen))
    = consAppend (countsOf midLen 0 values) (monadOnes rightLen)
  rw [shiftPrepend_zero,
      countsOf_consAppend_split midLen rightLen 0 values (ascendingFrom (0 + midLen) rightLen)
        hmono (fun _ _ => Nat.zero_le _)
        (fun pos hpos => by rw [Nat.zero_add]; exact hinto pos hpos)
        (fun pos hpos => by
          rw [ascendingFrom_get (0 + midLen) rightLen pos
                (by rw [ascendingFrom_length] at hpos; exact hpos)]
          exact Nat.le_add_right (0 + midLen) pos),
      countsOf_ascendingFrom_ones rightLen (0 + midLen)]

/-! ## The two headline corollaries: whiskered canonical counts -/

/-- ★ **LEFT whisker canonical counts.**  `canonCounts (whiskerLeft W body) = 1^W.length ++ canonCounts body` — the
LEFT whisker prepends a `1`-run to the body's multiplicity vector.  From the LEFT counts lift + the shipped LEFT
whisker fold embedding (`monadMonotoneMapOf_whiskerLeft`). -/
theorem canonCounts_whiskerLeft {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadModeSignature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    canonCounts (RawTwoCellExpr.whiskerLeft oneCell body)
      = consReplicate 1 oneCell.length (canonCounts body) := by
  show countsOf (composePath oneCell oneCellH).length 0
      (monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body))
    = consReplicate 1 oneCell.length (countsOf oneCellH.length 0 (monadMonotoneMapOf body))
  rw [monadMonotoneMapOf_whiskerLeft, ModalityPath.length_composePath]
  exact countsOf_embedLocalMap_left oneCell.length oneCellH.length (monadMonotoneMapOf body)

/-- ★ **RIGHT whisker canonical counts.**  `canonCounts (whiskerRight W body) = canonCounts body ++ 1^W.length` — the
RIGHT whisker appends a `1`-run at the top of the body's multiplicity vector.  From the RIGHT counts lift (with the
fold's weakly-increasing / in-range invariants) + the shipped RIGHT whisker fold embedding. -/
theorem canonCounts_whiskerRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph sourceMode middleMode}
    (oneCell : ModalityPath monadModeSignature.graph middleMode targetMode)
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG) :
    canonCounts (RawTwoCellExpr.whiskerRight oneCell body)
      = consAppend (canonCounts body) (monadOnes oneCell.length) := by
  show countsOf (composePath oneCellG oneCell).length 0
      (monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body))
    = consAppend (countsOf oneCellG.length 0 (monadMonotoneMapOf body)) (monadOnes oneCell.length)
  rw [monadMonotoneMapOf_whiskerRight, ModalityPath.length_composePath]
  exact countsOf_embedLocalMap_right oneCellG.length oneCell.length (monadMonotoneMapOf body)
    (monadMonotoneMapOf_isWeaklyIncreasing body) (monadMonotoneMapOf_mapsInto body)

/-! ## Honesty marker -/

/-- **ESTABLISHED — the COUNTS-ALIGNMENT for both whisker `normalizeCell` cases is CLOSED, zero-axiom.**  The
per-target multiplicity list of a whiskered cell is the body's own multiplicity list with a `1`-run prepended
(`canonCounts_whiskerLeft`, via `countsOf_embedLocalMap_left`) / appended (`canonCounts_whiskerRight`, via
`countsOf_embedLocalMap_right` under the fold's weakly-increasing + in-range invariants).  Combined with the shipped
`wordMul_whiskerLeft` / `wordMul_whiskerRight` (`t^k ◁/▷ word cc ≈ word (1^k ++ cc / cc ++ 1^k)`) and the boundary
transport `monadPath_normalForm` (`W = t^W.length`), this leaves ONLY the cast-assembly of the two whisker
`normalizeCell` cases (`whiskerLeft/Right W body ≈ canon (whiskerLeft/Right W body)`) and the `vcomp` case's
vertical multiplicativity `wordMul_vcomp` toward inhabiting `normalize`.  `= true`. -/
def fxMonad_hasWhiskerCountsAlignment : Bool := true

end FX1Poly.Polygraph
