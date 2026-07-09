import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerNormalizeCases
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCases
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaDecision
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMapFactorization

/-! # WalkingMonad — the DATA bridge `canonCounts_vcomp` + the `vcomp` normalize case

`WalkingMonad/MonadWordVcomp` closed the 2-cell half of the `vcomp` `normalizeCell` case — the VERTICAL word
multiplicativity `wordMul_vcomp : vcomp (word ccL) (cast (word ccR)) ≈ cast (word (composeCounts ccL ccR))`.  This
file ships the DATA half and assembles the last normalization case `monadNormalize_vcomp`.  The full normalization,
the inhabited canonicalization, the decision, and the completeness-flag flips land in `WalkingMonad/MonadWordProblem`.

## The data bridge (the load-bearing new mathematics)

`canonCounts_vcomp : canonCounts (vcomp cellL cellR) = composeCounts (canonCounts cellL) (canonCounts cellR)` — the
per-target multiplicity list of a vertical composite is the block-sum composition of the two factors' lists.  Its
whole content is the pure `List Nat` fact `countsOf_composeMap` (the FUNCTORIALITY of the fibre-count invariant of
Δ under function composition, Kerodon 0004 / nLab simplex+category / Eilenberg-Zilber factorization):

  countsOf targetLen base (composeMap f g)
    = composeCounts (countsOf g.length 0 f) (countsOf targetLen base g)

proved by base-shifted structural induction on `targetLen`, splitting `f` at the leading-run threshold via the
cons-only `splitLow` / `splitHigh` and reindexing the high suffix down by the run length (`mapSub`).  The head is
the fibre count of the leading composite run; the tail is the induction hypothesis over the run-peeled `g` and the
shifted-restricted `f`.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion on
`List Nat` / `Nat`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## `mapSub` — subtract a constant from each entry (the mid-domain reindex of the high suffix) -/

/-- Subtract `amount` from each entry of a value-list (cons-only; the mid-domain reindex when the leading run of the
codomain map is peeled). -/
def mapSub (amount : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => (head - amount) :: mapSub amount rest

/-- `mapSub` preserves length. -/
theorem mapSub_length : ∀ (amount : Nat) (xs : List Nat), (mapSub amount xs).length = xs.length
  | _, [] => rfl
  | amount, head :: rest => by
      show (mapSub amount rest).length + 1 = rest.length + 1
      rw [mapSub_length amount rest]

/-- The entry of `mapSub amount xs` at an in-range position is the original entry minus `amount`. -/
theorem monotoneMapGet_mapSub : ∀ (amount : Nat) (xs : List Nat) (pos : Nat),
    pos < xs.length →
    monotoneMapGet (mapSub amount xs) pos = monotoneMapGet xs pos - amount
  | _, [], pos, hpos => absurd hpos (Nat.not_lt_zero _)
  | _, _ :: _, 0, _ => rfl
  | amount, _ :: rest, pos + 1, hpos => by
      show monotoneMapGet (mapSub amount rest) pos = monotoneMapGet rest pos - amount
      exact monotoneMapGet_mapSub amount rest pos (Nat.lt_of_succ_lt_succ hpos)

/-- `mapSub` preserves weak monotonicity (subtracting a constant is order-preserving on `Nat`). -/
theorem mapSub_isWeaklyIncreasing (amount : Nat) (xs : List Nat)
    (hmono : isWeaklyIncreasing xs) : isWeaklyIncreasing (mapSub amount xs) := by
  intro lowerPos upperPos hle hupper
  rw [mapSub_length] at hupper
  rw [monotoneMapGet_mapSub amount xs lowerPos (Nat.lt_of_le_of_lt hle hupper),
      monotoneMapGet_mapSub amount xs upperPos hupper]
  exact Nat.sub_le_sub_right (hmono lowerPos upperPos hle hupper) amount

/-- Cancellation `amount + (value - amount) = value` when `amount ≤ value`, propext-clean (structural on
`amount`, dodging the library `Nat.add_sub_cancel'`). -/
theorem natAddSubOfGe : ∀ (amount value : Nat), amount ≤ value → amount + (value - amount) = value
  | 0, value, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | amount + 1, value, hle => by
      cases value with
      | zero => exact absurd hle (Nat.not_succ_le_zero amount)
      | succ predValue =>
          have hav : amount ≤ predValue := Nat.le_of_succ_le_succ hle
          show amount + 1 + (predValue + 1 - (amount + 1)) = predValue + 1
          rw [Nat.succ_sub_succ, Nat.add_right_comm amount 1 (predValue - amount),
              natAddSubOfGe amount predValue hav]

/-- Adding `amount` back to a `mapSub amount`-shifted list recovers it, when every entry was `≥ amount`. -/
theorem shiftPrepend_mapSub : ∀ (amount : Nat) (xs : List Nat),
    (∀ pos, pos < xs.length → amount ≤ monotoneMapGet xs pos) →
    shiftPrepend amount (mapSub amount xs) [] = xs
  | _, [], _ => rfl
  | amount, head :: rest, hge => by
      show (amount + (head - amount)) :: shiftPrepend amount (mapSub amount rest) [] = head :: rest
      rw [natAddSubOfGe amount head (hge 0 (Nat.succ_pos _)),
          shiftPrepend_mapSub amount rest (fun pos hpos => hge (pos + 1) (Nat.succ_lt_succ hpos))]

/-! ## `splitLow` / `splitHigh` — split a weakly-increasing list at a value threshold -/

/-- The leading prefix of a value-list all `< threshold` (cons-only, stopping at the first entry `≥ threshold`). -/
def splitLow (threshold : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => if head < threshold then head :: splitLow threshold rest else []

/-- The suffix of a value-list from the first entry `≥ threshold`. -/
def splitHigh (threshold : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => if head < threshold then splitHigh threshold rest else head :: rest

/-- `splitLow` unfolds keeping the head when it is below the threshold. -/
theorem splitLow_cons_lt {threshold head : Nat} {rest : List Nat} (h : head < threshold) :
    splitLow threshold (head :: rest) = head :: splitLow threshold rest := if_pos h

/-- `splitLow` unfolds to the empty prefix when the head is at/above the threshold. -/
theorem splitLow_cons_ge {threshold head : Nat} {rest : List Nat} (h : ¬ head < threshold) :
    splitLow threshold (head :: rest) = [] := if_neg h

/-- `splitHigh` drops the head when it is below the threshold. -/
theorem splitHigh_cons_lt {threshold head : Nat} {rest : List Nat} (h : head < threshold) :
    splitHigh threshold (head :: rest) = splitHigh threshold rest := if_pos h

/-- `splitHigh` keeps the whole list from the first entry at/above the threshold. -/
theorem splitHigh_cons_ge {threshold head : Nat} {rest : List Nat} (h : ¬ head < threshold) :
    splitHigh threshold (head :: rest) = head :: rest := if_neg h

/-- The low prefix and high suffix reconstruct the whole list — UNCONDITIONAL. -/
theorem consAppend_splitLow_splitHigh : ∀ (threshold : Nat) (f : List Nat),
    consAppend (splitLow threshold f) (splitHigh threshold f) = f
  | _, [] => rfl
  | threshold, head :: rest => by
      rcases Nat.lt_or_ge head threshold with h | h
      · rw [splitLow_cons_lt h, splitHigh_cons_lt h]
        show head :: consAppend (splitLow threshold rest) (splitHigh threshold rest) = head :: rest
        rw [consAppend_splitLow_splitHigh threshold rest]
      · rw [splitLow_cons_ge (Nat.not_lt.mpr h), splitHigh_cons_ge (Nat.not_lt.mpr h)]
        rfl

/-- Every entry of the low prefix is below the threshold. -/
theorem splitLow_lt : ∀ (threshold : Nat) (f : List Nat) (pos : Nat),
    pos < (splitLow threshold f).length → monotoneMapGet (splitLow threshold f) pos < threshold
  | _, [], pos, hpos => absurd hpos (Nat.not_lt_zero _)
  | threshold, head :: rest, pos, hpos => by
      rcases Nat.lt_or_ge head threshold with h | h
      · rw [splitLow_cons_lt h] at hpos ⊢
        cases pos with
        | zero => exact h
        | succ predPos => exact splitLow_lt threshold rest predPos (Nat.lt_of_succ_lt_succ hpos)
      · rw [splitLow_cons_ge (Nat.not_lt.mpr h)] at hpos
        exact absurd hpos (Nat.not_lt_zero _)

/-- Every entry of the high suffix is at/above the threshold, given a weakly-increasing source. -/
theorem splitHigh_ge : ∀ (threshold : Nat) (f : List Nat), isWeaklyIncreasing f →
    ∀ pos, pos < (splitHigh threshold f).length → threshold ≤ monotoneMapGet (splitHigh threshold f) pos
  | _, [], _, pos, hpos => absurd hpos (Nat.not_lt_zero _)
  | threshold, head :: rest, hmono, pos, hpos => by
      rcases Nat.lt_or_ge head threshold with h | h
      · rw [splitHigh_cons_lt h] at hpos ⊢
        exact splitHigh_ge threshold rest (isWeaklyIncreasing_tail hmono) pos hpos
      · rw [splitHigh_cons_ge (Nat.not_lt.mpr h)] at hpos ⊢
        cases pos with
        | zero => exact h
        | succ predPos =>
            have hp : predPos < rest.length := Nat.lt_of_succ_lt_succ hpos
            exact Nat.le_trans h (hmono 0 (predPos + 1) (Nat.zero_le _) (Nat.succ_lt_succ hp))

/-- The high suffix maps into the same codomain as the whole list (it is a suffix). -/
theorem splitHigh_mapsInto : ∀ (threshold : Nat) (f : List Nat) (cap : Nat),
    mapsInto f cap → mapsInto (splitHigh threshold f) cap
  | _, [], _, _ => by intro pos hpos; exact absurd hpos (Nat.not_lt_zero _)
  | threshold, head :: rest, cap, hinto => by
      rcases Nat.lt_or_ge head threshold with h | h
      · rw [splitHigh_cons_lt h]
        exact splitHigh_mapsInto threshold rest cap (mapsInto_tail hinto)
      · rw [splitHigh_cons_ge (Nat.not_lt.mpr h)]; exact hinto

/-! ## Weak monotonicity of prefixes (via cons-append indexing) -/

/-- Indexing a cons-append below the first block reads the first block. -/
theorem monotoneMapGet_consAppend_left : ∀ (a b : List Nat) (pos : Nat),
    pos < a.length → monotoneMapGet (consAppend a b) pos = monotoneMapGet a pos
  | [], _, pos, hpos => absurd hpos (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, b, pos + 1, hpos => by
      show monotoneMapGet (consAppend rest b) pos = monotoneMapGet rest pos
      exact monotoneMapGet_consAppend_left rest b pos (Nat.lt_of_succ_lt_succ hpos)

/-- A prefix of a weakly-increasing cons-append is weakly increasing. -/
theorem isWeaklyIncreasing_consAppend_left (a b : List Nat)
    (hmono : isWeaklyIncreasing (consAppend a b)) : isWeaklyIncreasing a := by
  intro lowerPos upperPos hle hupper
  rw [← monotoneMapGet_consAppend_left a b lowerPos (Nat.lt_of_le_of_lt hle hupper),
      ← monotoneMapGet_consAppend_left a b upperPos hupper]
  exact hmono lowerPos upperPos hle
    (by rw [consAppend_length]; exact Nat.lt_of_lt_of_le hupper (Nat.le_add_right a.length b.length))

/-- The low prefix of a weakly-increasing list is weakly increasing. -/
theorem splitLow_isWeaklyIncreasing (threshold : Nat) (f : List Nat)
    (hmono : isWeaklyIncreasing f) : isWeaklyIncreasing (splitLow threshold f) :=
  isWeaklyIncreasing_consAppend_left (splitLow threshold f) (splitHigh threshold f)
    ((consAppend_splitLow_splitHigh threshold f).symm ▸ hmono)

/-- The high suffix of a weakly-increasing list is weakly increasing. -/
theorem splitHigh_isWeaklyIncreasing : ∀ (threshold : Nat) (f : List Nat),
    isWeaklyIncreasing f → isWeaklyIncreasing (splitHigh threshold f)
  | _, [], _ => by intro _ _ _ hupper; exact absurd hupper (Nat.not_lt_zero _)
  | threshold, head :: rest, hmono => by
      rcases Nat.lt_or_ge head threshold with h | h
      · rw [splitHigh_cons_lt h]
        exact splitHigh_isWeaklyIncreasing threshold rest (isWeaklyIncreasing_tail hmono)
      · rw [splitHigh_cons_ge (Nat.not_lt.mpr h)]; exact hmono

/-! ## `composeMap` distributes over cons-append; run-length / drop-run pointwise facts -/

/-- `composeMap` distributes over a cons-append of the source. -/
theorem composeMap_consAppend : ∀ (a b g : List Nat),
    composeMap (consAppend a b) g = consAppend (composeMap a g) (composeMap b g)
  | [], _, _ => rfl
  | head :: rest, b, g => by
      show monotoneMapGet g head :: composeMap (consAppend rest b) g
        = monotoneMapGet g head :: consAppend (composeMap rest g) (composeMap b g)
      rw [composeMap_consAppend rest b g]

/-- The leading run length never exceeds the list length. -/
theorem runLengthAt_le_length : ∀ (base : Nat) (xs : List Nat), runLengthAt base xs ≤ xs.length
  | _, [] => Nat.le_refl 0
  | base, head :: rest => by
      rcases Nat.decEq head base with h | h
      · rw [runLengthAt_cons_neg h]; exact Nat.zero_le _
      · rw [runLengthAt_cons_pos h]; exact Nat.succ_le_succ (runLengthAt_le_length base rest)

/-- Dropping the base-run of an all-`base` list leaves nothing. -/
theorem dropRunAt_of_all_eq : ∀ (base : Nat) (xs : List Nat),
    (∀ pos, pos < xs.length → monotoneMapGet xs pos = base) → dropRunAt base xs = []
  | _, [], _ => rfl
  | base, head :: rest, hall => by
      have hhead : head = base := hall 0 (Nat.succ_pos _)
      rw [dropRunAt_cons_pos hhead]
      exact dropRunAt_of_all_eq base rest (fun pos hpos => hall (pos + 1) (Nat.succ_lt_succ hpos))

/-- Inside the leading `base`-run every entry equals `base`. -/
theorem monotoneMapGet_lt_runLengthAt : ∀ (base pos : Nat) (g : List Nat),
    pos < runLengthAt base g → monotoneMapGet g pos = base
  | _, _, [], hpos => absurd hpos (Nat.not_lt_zero _)
  | base, pos, head :: rest, hpos => by
      rcases Nat.decEq head base with h | h
      · rw [runLengthAt_cons_neg h] at hpos; exact absurd hpos (Nat.not_lt_zero _)
      · rw [runLengthAt_cons_pos h] at hpos
        cases pos with
        | zero => exact h
        | succ predPos =>
            show monotoneMapGet rest predPos = base
            exact monotoneMapGet_lt_runLengthAt base predPos rest (Nat.lt_of_succ_lt_succ hpos)

/-- Past the leading `base`-run, `g` reads its run-peeled remainder shifted by the run length. -/
theorem monotoneMapGet_dropRunAt_shift : ∀ (base offset : Nat) (g : List Nat),
    monotoneMapGet g (runLengthAt base g + offset) = monotoneMapGet (dropRunAt base g) offset
  | _, _, [] => rfl
  | base, offset, head :: rest => by
      rcases Nat.decEq head base with h | h
      · rw [runLengthAt_cons_neg h, dropRunAt_cons_neg h, Nat.zero_add]
      · rw [runLengthAt_cons_pos h, dropRunAt_cons_pos h,
            Nat.add_right_comm (runLengthAt base rest) 1 offset]
        show monotoneMapGet rest (runLengthAt base rest + offset) = monotoneMapGet (dropRunAt base rest) offset
        exact monotoneMapGet_dropRunAt_shift base offset rest

/-- Past the leading `base`-run of a weakly-increasing lower-bounded `g`, every entry strictly exceeds `base`. -/
theorem monotoneMapGet_ge_runLengthAt_gt (base : Nat) (g : List Nat)
    (hmono : isWeaklyIncreasing g)
    (hlow : ∀ pos, pos < g.length → base ≤ monotoneMapGet g pos)
    (target : Nat) (hge : runLengthAt base g ≤ target) (hlt : target < g.length) :
    base < monotoneMapGet g target := by
  obtain ⟨offset, hoffset⟩ := Nat.le.dest hge
  have hglen : (dropRunAt base g).length + runLengthAt base g = g.length := by
    have hh := congrArg List.length (consReplicate_runLengthAt_dropRunAt base g)
    rw [consReplicate_length] at hh; exact hh
  have hkey : monotoneMapGet g target = monotoneMapGet (dropRunAt base g) offset := by
    rw [← hoffset]; exact monotoneMapGet_dropRunAt_shift base offset g
  rw [hkey]
  have hoff_lt : offset < (dropRunAt base g).length := by
    rw [← hoffset, ← hglen] at hlt
    rw [Nat.add_comm (dropRunAt base g).length (runLengthAt base g)] at hlt
    exact Nat.lt_of_add_lt_add_left hlt
  exact dropRunAt_lowerBound base g hmono hlow offset hoff_lt

/-! ## The mid-domain reindex + the drop-run of a composite map -/

/-- The high suffix composed with `g` equals the shifted-down high suffix composed with the run-peeled `g`. -/
theorem composeMap_reindex_high (base : Nat) (g highList : List Nat)
    (hHighGe : ∀ pos, pos < highList.length → runLengthAt base g ≤ monotoneMapGet highList pos) :
    composeMap highList g
      = composeMap (mapSub (runLengthAt base g) highList) (dropRunAt base g) := by
  apply listExtById
  · rw [composeMap_length, composeMap_length, mapSub_length]
  · intro pos hpos
    rw [composeMap_length] at hpos
    rw [composeMap_get highList g pos hpos,
        composeMap_get (mapSub (runLengthAt base g) highList) (dropRunAt base g) pos
          (by rw [mapSub_length]; exact hpos),
        monotoneMapGet_mapSub (runLengthAt base g) highList pos hpos]
    obtain ⟨offset, hoffset⟩ := Nat.le.dest (hHighGe pos hpos)
    rw [← hoffset, natAddSubCancelLeft]
    exact monotoneMapGet_dropRunAt_shift base offset g

/-- Dropping the leading `base`-run of a composite map peels the whole low block and leaves the high suffix
composed with `g`. -/
theorem dropRunAt_composeMap_eq (base : Nat) (g f : List Nat)
    (hgLow : ∀ pos, pos < runLengthAt base g → monotoneMapGet g pos = base)
    (hgHigh : ∀ pos, runLengthAt base g ≤ pos → pos < g.length → base < monotoneMapGet g pos)
    (hf : mapsInto f g.length) (hfmono : isWeaklyIncreasing f) :
    dropRunAt base (composeMap f g)
      = composeMap (splitHigh (runLengthAt base g) f) g := by
  have hcm : composeMap f g
      = consAppend (composeMap (splitLow (runLengthAt base g) f) g)
          (composeMap (splitHigh (runLengthAt base g) f) g) := by
    rw [← composeMap_consAppend, consAppend_splitLow_splitHigh]
  have hHigh0 : runLengthAt base (composeMap (splitHigh (runLengthAt base g) f) g) = 0 := by
    apply runLengthAt_zero_of_lowerBound
    intro pos hpos
    rw [composeMap_length] at hpos
    rw [composeMap_get (splitHigh (runLengthAt base g) f) g pos hpos]
    exact hgHigh (monotoneMapGet (splitHigh (runLengthAt base g) f) pos)
      (splitHigh_ge (runLengthAt base g) f hfmono pos hpos)
      (splitHigh_mapsInto (runLengthAt base g) f g.length hf pos hpos)
  have hLowNil : dropRunAt base (composeMap (splitLow (runLengthAt base g) f) g) = [] := by
    apply dropRunAt_of_all_eq
    intro pos hpos
    rw [composeMap_length] at hpos
    rw [composeMap_get (splitLow (runLengthAt base g) f) g pos hpos]
    exact hgLow (monotoneMapGet (splitLow (runLengthAt base g) f) pos)
      (splitLow_lt (runLengthAt base g) f pos hpos)
  rw [hcm, dropRunAt_consAppend base (composeMap (splitLow (runLengthAt base g) f) g)
        (composeMap (splitHigh (runLengthAt base g) f) g) hHigh0, hLowNil]
  rfl

/-- The leading run of a composite map is exactly the low block (its length is the low prefix's). -/
theorem runLengthAt_composeMap_eq_splitLow_length (base : Nat) (g : List Nat)
    (hgLow : ∀ pos, pos < runLengthAt base g → monotoneMapGet g pos = base)
    (hgHigh : ∀ pos, runLengthAt base g ≤ pos → pos < g.length → base < monotoneMapGet g pos) :
    ∀ (f : List Nat), mapsInto f g.length →
      runLengthAt base (composeMap f g) = (splitLow (runLengthAt base g) f).length
  | [], _ => rfl
  | head :: rest, hf => by
      rcases Nat.lt_or_ge head (runLengthAt base g) with hlt | hge
      · show runLengthAt base (monotoneMapGet g head :: composeMap rest g)
          = (splitLow (runLengthAt base g) (head :: rest)).length
        rw [runLengthAt_cons_pos (hgLow head hlt), splitLow_cons_lt hlt]
        show runLengthAt base (composeMap rest g) + 1
          = (splitLow (runLengthAt base g) rest).length + 1
        rw [runLengthAt_composeMap_eq_splitLow_length base g hgLow hgHigh rest (mapsInto_tail hf)]
      · show runLengthAt base (monotoneMapGet g head :: composeMap rest g)
          = (splitLow (runLengthAt base g) (head :: rest)).length
        have hhead_lt : head < g.length := hf 0 (Nat.succ_pos _)
        have hne : ¬ (monotoneMapGet g head = base) := by
          intro heq
          have hgt := hgHigh head hge hhead_lt
          rw [heq] at hgt
          exact Nat.lt_irrefl base hgt
        rw [runLengthAt_cons_neg hne, splitLow_cons_ge (Nat.not_lt.mpr hge)]
        rfl

/-! ## `listSum` of a counts list = the source length; the shift lemma -/

/-- The multiplicities of a weakly-increasing in-range list sum to its length. -/
theorem listSum_countsOf : ∀ (targetLen base : Nat) (values : List Nat),
    isWeaklyIncreasing values →
    (∀ pos, pos < values.length → base ≤ monotoneMapGet values pos) →
    mapsInto values (base + targetLen) →
    listSum (countsOf targetLen base values) = values.length
  | 0, base, values, _, hlow, hinto => by
      cases values with
      | nil => rfl
      | cons _ _ =>
          exact absurd (hinto 0 (Nat.succ_pos _)) (Nat.not_lt.mpr (by
            rw [Nat.add_zero]; exact hlow 0 (Nat.succ_pos _)))
  | targetLen + 1, base, values, hmono, hlow, hinto => by
      show runLengthAt base values + listSum (countsOf targetLen (base + 1) (dropRunAt base values))
        = values.length
      have hupperShift : mapsInto (dropRunAt base values) (base + 1 + targetLen) := by
        have hupper : mapsInto (dropRunAt base values) (base + (targetLen + 1)) :=
          dropRunAt_mapsInto base values (base + (targetLen + 1)) hinto
        have heq : base + (targetLen + 1) = base + 1 + targetLen := by
          rw [← Nat.add_assoc]; exact (Nat.add_right_comm base 1 targetLen).symm
        rw [heq] at hupper; exact hupper
      rw [listSum_countsOf targetLen (base + 1) (dropRunAt base values)
            (dropRunAt_isWeaklyIncreasing base values hmono)
            (dropRunAt_lowerBound base values hmono hlow) hupperShift]
      have hh := congrArg List.length (consReplicate_runLengthAt_dropRunAt base values)
      rw [consReplicate_length] at hh
      exact (Nat.add_comm (runLengthAt base values) ((dropRunAt base values).length)).trans hh

/-- Shifting the base of a `countsOf` matches shifting the values down by the same amount. -/
theorem countsOf_mapSub_shift (targetLen amount : Nat) (highList : List Nat)
    (hge : ∀ pos, pos < highList.length → amount ≤ monotoneMapGet highList pos) :
    countsOf targetLen 0 (mapSub amount highList) = countsOf targetLen amount highList := by
  rw [← countsOf_shiftPrepend targetLen 0 amount (mapSub amount highList),
      shiftPrepend_mapSub amount highList hge, Nat.add_zero]

/-! ## `consTake` / `consDrop` off a cons-append of two counts blocks -/

/-- `consTake` at the first block's length recovers the first `countsOf` block. -/
theorem consTake_countsOf_consAppend (a b base1 base2 : Nat) (l1 l2 : List Nat) :
    consTake a (consAppend (countsOf a base1 l1) (countsOf b base2 l2)) = countsOf a base1 l1 := by
  have hstep := consTake_consAppend (countsOf a base1 l1) (countsOf b base2 l2)
  rw [countsOf_length] at hstep
  exact hstep

/-- `consDrop` past the first block's length recovers the second `countsOf` block. -/
theorem consDrop_countsOf_consAppend (a b base1 base2 : Nat) (l1 l2 : List Nat) :
    consDrop a (consAppend (countsOf a base1 l1) (countsOf b base2 l2)) = countsOf b base2 l2 := by
  have hstep := consDrop_consAppend (countsOf a base1 l1) (countsOf b base2 l2)
  rw [countsOf_length] at hstep
  exact hstep

/-! ## ★★ The counts-functoriality bridge `countsOf ∘ composeMap = composeCounts ∘ countsOf` -/

/-- ★★ **The FUNCTORIALITY of the fibre-count invariant of Δ under function composition.**  Reading the per-target
multiplicity list off a COMPOSED monotone map is the block-sum composition of the two factors' multiplicity lists:
`countsOf targetLen base (composeMap f g) = composeCounts (countsOf g.length 0 f) (countsOf targetLen base g)`, for
weakly-increasing in-range `f`, `g`.  Base-shifted structural induction on `targetLen`: the head is the fibre count
of the leading composite run (the low block of `f` under the leading `g`-run, `listSum`-summed via the mid split),
the tail is the induction hypothesis over the run-peeled `g` (`dropRunAt`) and the reindexed high suffix
(`mapSub`).  This is the DATA content of the `vcomp` normalize case (Kerodon 0004; nLab simplex+category;
Eilenberg-Zilber (epi,mono) factorization). -/
theorem countsOf_composeMap : ∀ (targetLen base : Nat) (f g : List Nat),
    isWeaklyIncreasing f → mapsInto f g.length →
    isWeaklyIncreasing g → mapsInto g (base + targetLen) →
    (∀ pos, pos < g.length → base ≤ monotoneMapGet g pos) →
    countsOf targetLen base (composeMap f g)
      = composeCounts (countsOf g.length 0 f) (countsOf targetLen base g)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | targetLen + 1, base, f, g, hfmono, hf, hgmono, hg, hglow => by
      have hgLow : ∀ pos, pos < runLengthAt base g → monotoneMapGet g pos = base :=
        fun pos hpos => monotoneMapGet_lt_runLengthAt base pos g hpos
      have hgHigh : ∀ pos, runLengthAt base g ≤ pos → pos < g.length → base < monotoneMapGet g pos :=
        fun pos hge hlt => monotoneMapGet_ge_runLengthAt_gt base g hgmono hglow pos hge hlt
      have hglen : (dropRunAt base g).length + runLengthAt base g = g.length := by
        have hh := congrArg List.length (consReplicate_runLengthAt_dropRunAt base g)
        rw [consReplicate_length] at hh; exact hh
      have hrdlen : runLengthAt base g + (dropRunAt base g).length = g.length := by
        rw [Nat.add_comm (runLengthAt base g) ((dropRunAt base g).length)]; exact hglen
      have hfHighWI : isWeaklyIncreasing (splitHigh (runLengthAt base g) f) :=
        splitHigh_isWeaklyIncreasing (runLengthAt base g) f hfmono
      have hfHighGe : ∀ pos, pos < (splitHigh (runLengthAt base g) f).length →
          runLengthAt base g ≤ monotoneMapGet (splitHigh (runLengthAt base g) f) pos :=
        fun pos hpos => splitHigh_ge (runLengthAt base g) f hfmono pos hpos
      have hfHighInto : ∀ pos, pos < (splitHigh (runLengthAt base g) f).length →
          monotoneMapGet (splitHigh (runLengthAt base g) f) pos < g.length :=
        fun pos hpos => splitHigh_mapsInto (runLengthAt base g) f g.length hf pos hpos
      -- the mid split of ccL = countsOf g.length 0 f
      have hmidsplit : countsOf g.length 0 f
          = consAppend (countsOf (runLengthAt base g) 0 (splitLow (runLengthAt base g) f))
              (countsOf ((dropRunAt base g).length) (runLengthAt base g)
                (splitHigh (runLengthAt base g) f)) := by
        have hcas := countsOf_consAppend_split (runLengthAt base g) ((dropRunAt base g).length) 0
          (splitLow (runLengthAt base g) f) (splitHigh (runLengthAt base g) f)
          (splitLow_isWeaklyIncreasing (runLengthAt base g) f hfmono)
          (fun _ _ => Nat.zero_le _)
          (fun pos hpos => by rw [Nat.zero_add]; exact splitLow_lt (runLengthAt base g) f pos hpos)
          (fun pos hpos => by rw [Nat.zero_add]; exact splitHigh_ge (runLengthAt base g) f hfmono pos hpos)
        rw [hrdlen, consAppend_splitLow_splitHigh, Nat.zero_add] at hcas
        exact hcas
      have htake : consTake (runLengthAt base g) (countsOf g.length 0 f)
          = countsOf (runLengthAt base g) 0 (splitLow (runLengthAt base g) f) := by
        rw [hmidsplit]; exact consTake_countsOf_consAppend _ _ _ _ _ _
      have hdrop : consDrop (runLengthAt base g) (countsOf g.length 0 f)
          = countsOf ((dropRunAt base g).length) (runLengthAt base g) (splitHigh (runLengthAt base g) f) := by
        rw [hmidsplit]; exact consDrop_countsOf_consAppend _ _ _ _ _ _
      -- head: run length of composite = low block sum
      have hhead : runLengthAt base (composeMap f g)
          = listSum (consTake (runLengthAt base g) (countsOf g.length 0 f)) := by
        rw [htake, runLengthAt_composeMap_eq_splitLow_length base g hgLow hgHigh f hf]
        exact (listSum_countsOf (runLengthAt base g) 0 (splitLow (runLengthAt base g) f)
          (splitLow_isWeaklyIncreasing (runLengthAt base g) f hfmono)
          (fun _ _ => Nat.zero_le _)
          (fun pos hpos => by rw [Nat.zero_add]; exact splitLow_lt (runLengthAt base g) f pos hpos)).symm
      -- the IH side conditions on the run-peeled g / reindexed high f
      have hf'Into : mapsInto (mapSub (runLengthAt base g) (splitHigh (runLengthAt base g) f))
          (dropRunAt base g).length := by
        intro pos hpos
        rw [mapSub_length] at hpos
        have hposlt := hfHighInto pos hpos
        obtain ⟨offset, hoffset⟩ := Nat.le.dest (hfHighGe pos hpos)
        rw [monotoneMapGet_mapSub (runLengthAt base g) (splitHigh (runLengthAt base g) f) pos hpos,
            ← hoffset, natAddSubCancelLeft]
        rw [← hoffset, ← hglen] at hposlt
        rw [Nat.add_comm (dropRunAt base g).length (runLengthAt base g)] at hposlt
        exact Nat.lt_of_add_lt_add_left hposlt
      have hcapEq : base + (targetLen + 1) = base + 1 + targetLen := by
        rw [← Nat.add_assoc]; exact (Nat.add_right_comm base 1 targetLen).symm
      have hg'Into : mapsInto (dropRunAt base g) (base + 1 + targetLen) := by
        rw [← hcapEq]; exact dropRunAt_mapsInto base g (base + (targetLen + 1)) hg
      -- tail: assemble via the reindex + IH + shift
      have htail : countsOf targetLen (base + 1) (dropRunAt base (composeMap f g))
          = composeCounts (consDrop (runLengthAt base g) (countsOf g.length 0 f))
              (countsOf targetLen (base + 1) (dropRunAt base g)) := by
        rw [dropRunAt_composeMap_eq base g f hgLow hgHigh hf hfmono,
            composeMap_reindex_high base g (splitHigh (runLengthAt base g) f) hfHighGe,
            countsOf_composeMap targetLen (base + 1)
              (mapSub (runLengthAt base g) (splitHigh (runLengthAt base g) f)) (dropRunAt base g)
              (mapSub_isWeaklyIncreasing (runLengthAt base g) (splitHigh (runLengthAt base g) f) hfHighWI)
              hf'Into (dropRunAt_isWeaklyIncreasing base g hgmono) hg'Into
              (dropRunAt_lowerBound base g hgmono hglow),
            hdrop,
            countsOf_mapSub_shift (dropRunAt base g).length (runLengthAt base g)
              (splitHigh (runLengthAt base g) f) hfHighGe]
      show runLengthAt base (composeMap f g)
            :: countsOf targetLen (base + 1) (dropRunAt base (composeMap f g))
        = listSum (consTake (runLengthAt base g) (countsOf g.length 0 f))
            :: composeCounts (consDrop (runLengthAt base g) (countsOf g.length 0 f))
                (countsOf targetLen (base + 1) (dropRunAt base g))
      rw [hhead, htail]

/-! ## ★ The canonical-counts bridge -/

/-- ★ **The DATA bridge `canonCounts_vcomp`.**  The per-target multiplicity list of a vertical composite is the
block-sum composition of the two factors' lists — `canonCounts (vcomp cellL cellR) = composeCounts (canonCounts
cellL) (canonCounts cellR)`.  Immediate from the fold homomorphism `monadMonotoneMapOf_vcomp` and the counts
functoriality `countsOf_composeMap`, with the fold invariants (weakly increasing, in-range) discharging its side
conditions. -/
theorem canonCounts_vcomp
    {sourcePath midPath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cellL : RawTwoCellExpr monadModeSignature sourcePath midPath)
    (cellR : RawTwoCellExpr monadModeSignature midPath targetPath) :
    canonCounts (RawTwoCellExpr.vcomp cellL cellR)
      = composeCounts (canonCounts cellL) (canonCounts cellR) := by
  show countsOf targetPath.length 0 (monadMonotoneMapOf (RawTwoCellExpr.vcomp cellL cellR))
    = composeCounts (countsOf midPath.length 0 (monadMonotoneMapOf cellL))
        (countsOf targetPath.length 0 (monadMonotoneMapOf cellR))
  rw [monadMonotoneMapOf_vcomp]
  have hmapRLen : (monadMonotoneMapOf cellR).length = midPath.length :=
    monadMonotoneMapOf_length cellR
  rw [← hmapRLen]
  exact countsOf_composeMap targetPath.length 0 (monadMonotoneMapOf cellL) (monadMonotoneMapOf cellR)
    (monadMonotoneMapOf_isWeaklyIncreasing cellL)
    (by rw [hmapRLen]; exact monadMonotoneMapOf_mapsInto cellL)
    (monadMonotoneMapOf_isWeaklyIncreasing cellR)
    (by rw [Nat.zero_add]; exact monadMonotoneMapOf_mapsInto cellR)
    (fun _ _ => Nat.zero_le _)

/-! ## The `vcomp` normalize case -/

/-- ★ **Case `vcomp cellL cellR` of `normalize`.**  Every vertical composite is `MonadSaturatedTwoCellConv`-
convertible to the canonical word of its own fold, given both factors are.  The induction hypotheses give
`vcomp cellL cellR ≈ vcomp (canon cellL) (canon cellR)`; the two boundary casts extrude out of the vertical
composite (`vcomp_castBoundaryRight` / `vcomp_castBoundaryLeft` + cast fusion), exposing the VERTICAL word
multiplicativity `wordMul_vcomp` under an outer cast; applying it lands `cast (word (composeCounts ccL ccR))`, which
the DATA bridge `canonCounts_vcomp` reconciles with `canon (vcomp cellL cellR)` (the boundary casts proof-
irrelevant).  This is the SOLE `normalizeCell` case that uses the monad LAWS (through `wordMul_vcomp`). -/
theorem monadNormalize_vcomp
    {sourcePath midPath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cellL : RawTwoCellExpr monadModeSignature sourcePath midPath)
    (cellR : RawTwoCellExpr monadModeSignature midPath targetPath)
    (ihL : MonadSaturatedTwoCellConv cellL (canon cellL))
    (ihR : MonadSaturatedTwoCellConv cellR (canon cellR)) :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellL cellR)
      (canon (RawTwoCellExpr.vcomp cellL cellR)) := by
  have hlen : (canonCounts cellL).length = listSum (canonCounts cellR) := by
    rw [canonCounts_length cellL, ← countsDomainPath_length_eq_listSum (canonCounts cellR),
        canonDomain_eq cellR]
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.trans
      (MonadSaturatedTwoCellConv.vcompCongrLeft cellR ihL)
      (MonadSaturatedTwoCellConv.vcompCongrRight (canon cellL) ihR)) ?_
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.castBoundary (canonDomain_eq cellL) (canonCodomain_eq cellL)
          (wordFromCounts (canonCounts cellL)))
        (RawTwoCellExpr.castBoundary (canonDomain_eq cellR) (canonCodomain_eq cellR)
          (wordFromCounts (canonCounts cellR))))
      (canon (RawTwoCellExpr.vcomp cellL cellR))
  rw [RawTwoCellExpr.vcomp_castBoundaryRight, RawTwoCellExpr.castBoundary_castBoundary,
      RawTwoCellExpr.vcomp_castBoundaryLeft, RawTwoCellExpr.castBoundary_castBoundary]
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.castBoundaryCongr _ _
      (wordMul_vcomp (canonCounts cellR) (canonCounts cellL) hlen)) ?_
  refine MonadSaturatedTwoCellConv.ofEq ?_
  rw [RawTwoCellExpr.castBoundary_castBoundary]
  exact RawTwoCellExpr.castBoundary_wordCongr _ _
    (canonDomain_eq (RawTwoCellExpr.vcomp cellL cellR))
    (canonCodomain_eq (RawTwoCellExpr.vcomp cellL cellR))
    (canonCounts_vcomp cellL cellR).symm

/-! ## Honesty marker -/

/-- **ESTABLISHED — the DATA bridge `canonCounts_vcomp` and the assembled `vcomp` normalize case are CLOSED,
zero-axiom.**  The Δ fibre-count functoriality `countsOf_composeMap : countsOf targetLen base (composeMap f g) =
composeCounts (countsOf g.length 0 f) (countsOf targetLen base g)` (base-shifted structural induction on
`targetLen`: leading-run head via `listSum` of the low block, mid-suffix-shift tail via `dropRunAt` + `mapSub`)
lifts to `canonCounts_vcomp : canonCounts (vcomp cellL cellR) = composeCounts (canonCounts cellL) (canonCounts
cellR)` through the fold homomorphism `monadMonotoneMapOf_vcomp`.  Combined with the shipped 2-cell half
`wordMul_vcomp`, the two boundary casts extrude out of the vertical composite (`vcomp_castBoundaryLeft/Right` + cast
fusion) exposing `wordMul_vcomp` under an outer cast, which `canonCounts_vcomp` reconciles with `canon (vcomp)` —
the assembled `vcomp` `normalizeCell` case `monadNormalize_vcomp`, the SOLE case using the monad LAWS.  This closes
the DATA half named by the completeness markers; the full normalization + inhabitation + decision + the flag flips
land in `WalkingMonad/MonadWordProblem`.  `= true`. -/
def fxMonad_hasCanonCountsVcompBridge : Bool := true

end FX1Poly.Polygraph
