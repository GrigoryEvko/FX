import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap

/-! # WalkingMonad/MonadSaturatedSkeletonReps — the bespoke-free SKELETON-REPS bridge (Round C severance)

MONAD-R7 Round C severs the walking-monad SURVIVOR files (the KZ order model, the idempotent reps, the Gen
twins) from the pure-bespoke saturated-Δ chain by relocating the chain's conv-FREE lower stratum into this
bridge.  Everything here is `List Nat`/`Nat` combinatorics over the already-bespoke-free monotone-map base
(`WalkingAdjunction/MonotoneMap`); the bridge imports NO file that carries the bespoke saturated-convertibility
inductive, so a survivor that imports only this bridge is provably conv-decoupled.

## What this file ships (relocated VERBATIM from `MonadWhiskerEmbedding`, names/namespace/meaning preserved)

  * the cons-only prepend primitives `ascendingPrepend` / `shiftPrepend` (no `List.append`, propext-safe) with
    their length + region-wise value characterizations;
  * the ordinal-sum whisker embedding `embedLocalMap` (`id_L ⊕ localMap ⊕ id_R`) with its length + the three
    region-wise value characterizations (`_get_left` / `_get_mid` / `_get_right`);
  * the three-region position split `embedRegionSplit` (the `listExtById` workhorse).

`MonadWhiskerEmbedding` now imports this bridge for exactly these primitives (single home, no duplication); the
KZ hom-order model (`WalkingKZ/KZMonadOrderModel`) imports ONLY this bridge and is thereby bespoke-free.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (cons-only lists,
pointwise `listExtById`, hand arithmetic).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The cons-only prepend primitives (no `++`, propext-safe) -/

/-- Prepend the ascending block `[base, base+1, …, base+count-1]` onto a tail (cons-only, so no `List.append`
propext leak). -/
def ascendingPrepend : Nat → Nat → List Nat → List Nat
  | _, 0, tail => tail
  | base, count + 1, tail => base :: ascendingPrepend (base + 1) count tail

/-- Prepend the shifted value-list `[offset + head₀, offset + head₁, …]` onto a tail (cons-only). -/
def shiftPrepend : Nat → List Nat → List Nat → List Nat
  | _, [], tail => tail
  | offset, head :: rest, tail => (offset + head) :: shiftPrepend offset rest tail

/-- The ordinal-sum embedding `id_{leftLen} ⊕ localMap ⊕ id_{rightLen}` of a local map `[domLen] → [midLen]` into a
`leftLen`-prefixed, `rightLen`-suffixed context — the monotone map `[leftLen + domLen + rightLen] →
[leftLen + midLen + rightLen]` that whiskering realizes.  The left block is the identity `[0, …, leftLen-1]`, the
middle is `localMap` shifted up by `leftLen`, the right block is `[leftLen+midLen, …]`. -/
def embedLocalMap (leftLen midLen rightLen : Nat) (localMap : List Nat) : List Nat :=
  ascendingPrepend 0 leftLen (shiftPrepend leftLen localMap (ascendingFrom (leftLen + midLen) rightLen))

/-! ## Length + region-wise value characterizations of the prepend primitives -/

/-- The ascending prepend adds exactly `count` entries. -/
theorem ascendingPrepend_length : ∀ (base count : Nat) (tail : List Nat),
    (ascendingPrepend base count tail).length = count + tail.length
  | _, 0, tail => by show tail.length = 0 + tail.length; rw [Nat.zero_add]
  | base, count + 1, tail => by
      show (ascendingPrepend (base + 1) count tail).length + 1 = count + 1 + tail.length
      rw [ascendingPrepend_length (base + 1) count tail, Nat.succ_add]

/-- Inside the ascending prefix (`position < count`) the value is `base + position`. -/
theorem ascendingPrepend_get_lt : ∀ (base count position : Nat) (tail : List Nat),
    position < count → monotoneMapGet (ascendingPrepend base count tail) position = base + position
  | _, 0, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | base, _ + 1, 0, _, _ => rfl
  | base, count + 1, position + 1, tail, hlt => by
      have hlt' : position < count := Nat.lt_of_succ_lt_succ hlt
      show monotoneMapGet (ascendingPrepend (base + 1) count tail) position = base + (position + 1)
      rw [ascendingPrepend_get_lt (base + 1) count position tail hlt', Nat.add_assoc, Nat.add_comm 1 position]

/-- Past the ascending prefix (position `count + offset`) the value is read off the tail at `offset`. -/
theorem ascendingPrepend_get_add : ∀ (base count offset : Nat) (tail : List Nat),
    monotoneMapGet (ascendingPrepend base count tail) (count + offset) = monotoneMapGet tail offset
  | _, 0, offset, tail => by show monotoneMapGet tail (0 + offset) = _; rw [Nat.zero_add]
  | base, count + 1, offset, tail => by
      show monotoneMapGet (ascendingPrepend base (count + 1) tail) (count + 1 + offset) = monotoneMapGet tail offset
      show monotoneMapGet (base :: ascendingPrepend (base + 1) count tail) (count + 1 + offset)
        = monotoneMapGet tail offset
      rw [show count + 1 + offset = (count + offset) + 1 from by rw [Nat.succ_add]]
      show monotoneMapGet (ascendingPrepend (base + 1) count tail) (count + offset) = monotoneMapGet tail offset
      exact ascendingPrepend_get_add (base + 1) count offset tail

/-- The shifted prepend adds exactly `values.length` entries. -/
theorem shiftPrepend_length : ∀ (offset : Nat) (values tail : List Nat),
    (shiftPrepend offset values tail).length = values.length + tail.length
  | _, [], tail => by show tail.length = 0 + tail.length; rw [Nat.zero_add]
  | offset, head :: rest, tail => by
      show (shiftPrepend offset rest tail).length + 1 = rest.length + 1 + tail.length
      rw [shiftPrepend_length offset rest tail, Nat.succ_add]

/-- Inside the shifted block (`position < values.length`) the value is `offset + (values at position)`. -/
theorem shiftPrepend_get_lt : ∀ (offset : Nat) (values : List Nat) (position : Nat) (tail : List Nat),
    position < values.length →
    monotoneMapGet (shiftPrepend offset values tail) position = offset + monotoneMapGet values position
  | _, [], _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | offset, head :: rest, 0, tail, _ => rfl
  | offset, head :: rest, position + 1, tail, hlt => by
      have hlt' : position < rest.length := Nat.lt_of_succ_lt_succ hlt
      show monotoneMapGet (shiftPrepend offset rest tail) position = offset + monotoneMapGet rest position
      exact shiftPrepend_get_lt offset rest position tail hlt'

/-- Past the shifted block (position `values.length + offsetPos`) the value is read off the tail. -/
theorem shiftPrepend_get_add : ∀ (offset : Nat) (values : List Nat) (offsetPos : Nat) (tail : List Nat),
    monotoneMapGet (shiftPrepend offset values tail) (values.length + offsetPos) = monotoneMapGet tail offsetPos
  | _, [], offsetPos, tail => by show monotoneMapGet tail (0 + offsetPos) = _; rw [Nat.zero_add]
  | offset, head :: rest, offsetPos, tail => by
      show monotoneMapGet (shiftPrepend offset (head :: rest) tail) (rest.length + 1 + offsetPos)
        = monotoneMapGet tail offsetPos
      show monotoneMapGet ((offset + head) :: shiftPrepend offset rest tail) (rest.length + 1 + offsetPos)
        = monotoneMapGet tail offsetPos
      rw [show rest.length + 1 + offsetPos = (rest.length + offsetPos) + 1 from by rw [Nat.succ_add]]
      show monotoneMapGet (shiftPrepend offset rest tail) (rest.length + offsetPos) = monotoneMapGet tail offsetPos
      exact shiftPrepend_get_add offset rest offsetPos tail

/-! ## `embedLocalMap` length + the three region-wise value characterizations -/

/-- The embedding has domain length `leftLen + localMap.length + rightLen`. -/
theorem embedLocalMap_length (leftLen midLen rightLen : Nat) (localMap : List Nat) :
    (embedLocalMap leftLen midLen rightLen localMap).length = leftLen + localMap.length + rightLen := by
  show (ascendingPrepend 0 leftLen (shiftPrepend leftLen localMap (ascendingFrom (leftLen + midLen) rightLen))).length
    = leftLen + localMap.length + rightLen
  rw [ascendingPrepend_length, shiftPrepend_length, ascendingFrom_length, Nat.add_assoc]

/-- LEFT region: below the prefix the embedding is the identity (`position < leftLen ↦ position`). -/
theorem embedLocalMap_get_left (leftLen midLen rightLen : Nat) (localMap : List Nat)
    (position : Nat) (hpos : position < leftLen) :
    monotoneMapGet (embedLocalMap leftLen midLen rightLen localMap) position = position := by
  show monotoneMapGet (ascendingPrepend 0 leftLen
      (shiftPrepend leftLen localMap (ascendingFrom (leftLen + midLen) rightLen))) position = position
  rw [ascendingPrepend_get_lt 0 leftLen position _ hpos, Nat.zero_add]

/-- MIDDLE region: at `leftLen + offset` (`offset < localMap.length`) the embedding is `localMap` shifted up. -/
theorem embedLocalMap_get_mid (leftLen midLen rightLen : Nat) (localMap : List Nat)
    (offset : Nat) (hoff : offset < localMap.length) :
    monotoneMapGet (embedLocalMap leftLen midLen rightLen localMap) (leftLen + offset)
      = leftLen + monotoneMapGet localMap offset := by
  show monotoneMapGet (ascendingPrepend 0 leftLen
      (shiftPrepend leftLen localMap (ascendingFrom (leftLen + midLen) rightLen))) (leftLen + offset)
    = leftLen + monotoneMapGet localMap offset
  rw [ascendingPrepend_get_add 0 leftLen offset, shiftPrepend_get_lt leftLen localMap offset _ hoff]

/-- RIGHT region: at `leftLen + localMap.length + offset` (`offset < rightLen`) the embedding is the top
identity block `leftLen + midLen + offset`. -/
theorem embedLocalMap_get_right (leftLen midLen rightLen : Nat) (localMap : List Nat)
    (offset : Nat) (hoff : offset < rightLen) :
    monotoneMapGet (embedLocalMap leftLen midLen rightLen localMap) (leftLen + localMap.length + offset)
      = leftLen + midLen + offset := by
  show monotoneMapGet (ascendingPrepend 0 leftLen
      (shiftPrepend leftLen localMap (ascendingFrom (leftLen + midLen) rightLen)))
      (leftLen + localMap.length + offset) = leftLen + midLen + offset
  rw [Nat.add_assoc leftLen localMap.length offset, ascendingPrepend_get_add 0 leftLen (localMap.length + offset),
      shiftPrepend_get_add leftLen localMap offset,
      ascendingFrom_get (leftLen + midLen) rightLen offset hoff, Nat.add_assoc]

/-! ## The three-region position split (the workhorse for the embedding-algebra `listExtById` proofs) -/

/-- Any position below `leftLen + midLen + rightLen` lands in exactly one of the three embedding regions: the
left identity prefix (`< leftLen`), the middle block (`leftLen + offset`, `offset < midLen`), or the right
identity suffix (`leftLen + midLen + offset`, `offset < rightLen`). -/
theorem embedRegionSplit (leftLen midLen rightLen position : Nat)
    (hpos : position < leftLen + midLen + rightLen) :
    position < leftLen
      ∨ (∃ offset, offset < midLen ∧ position = leftLen + offset)
      ∨ (∃ offset, offset < rightLen ∧ position = leftLen + midLen + offset) := by
  rcases Nat.lt_or_ge position leftLen with hleft | hleft
  · exact Or.inl hleft
  · obtain ⟨middleOffset, hmiddle⟩ := Nat.le.dest hleft
    subst hmiddle
    rcases Nat.lt_or_ge middleOffset midLen with hmid | hmid
    · exact Or.inr (Or.inl ⟨middleOffset, hmid, rfl⟩)
    · obtain ⟨rightOffset, hright⟩ := Nat.le.dest hmid
      subst hright
      refine Or.inr (Or.inr ⟨rightOffset, ?_, ?_⟩)
      · have hlt : leftLen + midLen + rightOffset < leftLen + midLen + rightLen := by
          rw [Nat.add_assoc leftLen midLen rightOffset]; exact hpos
        exact Nat.lt_of_add_lt_add_left hlt
      · rw [Nat.add_assoc]

end FX1Poly.Polygraph
