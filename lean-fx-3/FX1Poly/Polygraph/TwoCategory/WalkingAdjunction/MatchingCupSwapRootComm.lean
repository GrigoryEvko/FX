import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation

/-! # Track B FINAL CRUX — the cup-restricted `rootComm` (block-transposition union-find automorphism)

`MatchingSwapObstruction` machine-checked that the GENERAL `MatchingGodementCoreSwapSim.rootComm` is FALSE: the
counit (CAP / MERGE) Godement swap flips the root of a merged pre-existing component depending on the join order
(`not_matchingGodementCoreSwapSimFresh`, the root-flip forest state).  The CUP restriction is different, and TRUE.

## Why the cup restriction survives (the make-or-break)

`stepCup` allocates two FRESH legs `(nextFresh, nextFresh+1)` and joins them.  Because both legs sit strictly
above every pre-existing id, `unionFindJoin` NEVER merges pre-existing components — it deterministically prepends
the edge `(nextFresh, nextFresh+1)`, INDEPENDENT of the fire position.  So running two disjoint-window cups in the
two Godement run orders produces the IDENTICAL link list

  `L = (nf+2, nf+3) :: (nf, nf+1) :: orig`

(the first-fired cup always takes `(nf, nf+1)`, the second `(nf+2, nf+3)`, in either order).  The two orders differ
ONLY in the open-wire arrangement — a block transposition swapping the two fresh cup pairs' positions.  The
`MatchingStepSim.rootComm` field is therefore the pure statement that the block transposition

  `blockSwap nf : nf ↔ nf+2, nf+1 ↔ nf+3, fix else`

is a union-find AUTOMORPHISM of `L`: `unionFindRootOf L (blockSwap nf x) = blockSwap nf (unionFindRootOf L x)`.

## What this file ships (zero-axiom, structural)

  * ★ `blockSwap` — the 4-id transposition, and `blockSwap_involutive` / `blockSwap_injective`.
  * `unionFindRoot_map_of_parentComm` — a root-following commutation from a parent-following commutation (the
    generic automorphism-transports-root fact, fuel induction).
  * ★ `blockSwap_rootComm` — the crux: on the two-fresh-join graph over a fresh forest `orig`, `blockSwap nf` is a
    union-find automorphism.  Proven by the two `unionFindRootOf_consJoin` closed forms + a finite case analysis on
    where `x` sits relative to the four fresh ids, using freshness (`unionFindRootOf_lt_of_fresh`, parentlessness
    `unionFindParent_none_of_lt`).  This is the CUP-restriction of the refuted general swap, TRUE and now proven.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix` / `propext`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Beq / distinctness micro-helpers over `Nat` (propext-free) -/

/-- `a ≠ b` collapses the boolean `a == b` to `false` (the decidable read-off, `propext`-free). -/
theorem natBeqFalseOfNe {firstNode secondNode : Nat} (distinct : firstNode ≠ secondNode) :
    (firstNode == secondNode) = false := by
  cases hbeq : firstNode == secondNode with
  | true => exact absurd (of_decide_eq_true hbeq) distinct
  | false => rfl

/-- `a == a` is `true`. -/
theorem natBeqSelf (node : Nat) : (node == node) = true := decide_eq_true (rfl : node = node)

/-- `a ≠ b` refutes the `Prop` `(a == b) = true` (the `if`-condition form of the boolean). -/
theorem natBeqNeTrue {firstNode secondNode : Nat} (distinct : firstNode ≠ secondNode) :
    ¬ (firstNode == secondNode) = true := fun htrue => distinct (of_decide_eq_true htrue)

/-- The boolean `a == b` being `false` witnesses `a ≠ b`. -/
theorem neOfBeqFalse {firstNode secondNode : Nat} (hfalse : (firstNode == secondNode) = false) :
    firstNode ≠ secondNode := by
  intro hEq; rw [hEq, natBeqSelf] at hfalse; exact Bool.noConfusion hfalse

/-! ## The block transposition -/

/-- ★ **The 4-id block transposition** at fresh base `nf`: swaps `nf ↔ nf+2` and `nf+1 ↔ nf+3`, fixing every other
id.  This is the union-find automorphism the two Godement cup run orders differ by. -/
def blockSwap (nf identifier : Nat) : Nat :=
  if identifier == nf then nf + 2
  else if identifier == nf + 1 then nf + 3
  else if identifier == nf + 2 then nf
  else if identifier == nf + 3 then nf + 1
  else identifier

/-- The four fresh ids are pairwise distinct — the `≠` facts every `blockSwap` guard needs. -/
theorem blockSwap_ne_nf1_nf (nf : Nat) : nf + 1 ≠ nf := Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide))
theorem blockSwap_ne_nf2_nf (nf : Nat) : nf + 2 ≠ nf := Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide))
theorem blockSwap_ne_nf3_nf (nf : Nat) : nf + 3 ≠ nf := Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide))
theorem blockSwap_ne_nf2_nf1 (nf : Nat) : nf + 2 ≠ nf + 1 :=
  Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf)
theorem blockSwap_ne_nf3_nf1 (nf : Nat) : nf + 3 ≠ nf + 1 :=
  Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf)
theorem blockSwap_ne_nf3_nf2 (nf : Nat) : nf + 3 ≠ nf + 2 :=
  Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf)

/-- `blockSwap nf` fixes any id below `nf` (all four guards fail: an id `< nf` is none of `nf … nf+3`). -/
theorem blockSwap_fix_lt (nf identifier : Nat) (below : identifier < nf) :
    blockSwap nf identifier = identifier := by
  have ne0 : identifier ≠ nf := Nat.ne_of_lt below
  have ne1 : identifier ≠ nf + 1 := Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_add_of_pos_right (by decide)))
  have ne2 : identifier ≠ nf + 2 := Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_add_of_pos_right (by decide)))
  have ne3 : identifier ≠ nf + 3 := Nat.ne_of_lt (Nat.lt_trans below (Nat.lt_add_of_pos_right (by decide)))
  show (if identifier == nf then nf + 2 else if identifier == nf + 1 then nf + 3
        else if identifier == nf + 2 then nf else if identifier == nf + 3 then nf + 1 else identifier)
      = identifier
  rw [if_neg (natBeqNeTrue ne0), if_neg (natBeqNeTrue ne1), if_neg (natBeqNeTrue ne2),
    if_neg (natBeqNeTrue ne3)]

/-- `blockSwap nf nf = nf + 2`. -/
theorem blockSwap_nf (nf : Nat) : blockSwap nf nf = nf + 2 := by
  show (if nf == nf then nf + 2 else _) = nf + 2
  rw [if_pos (natBeqSelf nf)]

/-- `blockSwap nf (nf+1) = nf + 3`. -/
theorem blockSwap_nf1 (nf : Nat) : blockSwap nf (nf + 1) = nf + 3 := by
  show (if nf + 1 == nf then nf + 2 else if nf + 1 == nf + 1 then nf + 3 else _) = nf + 3
  rw [if_neg (natBeqNeTrue (blockSwap_ne_nf1_nf nf)), if_pos (natBeqSelf (nf + 1))]

/-- `blockSwap nf (nf+2) = nf`. -/
theorem blockSwap_nf2 (nf : Nat) : blockSwap nf (nf + 2) = nf := by
  show (if nf + 2 == nf then nf + 2 else if nf + 2 == nf + 1 then nf + 3
        else if nf + 2 == nf + 2 then nf else _) = nf
  rw [if_neg (natBeqNeTrue (blockSwap_ne_nf2_nf nf)), if_neg (natBeqNeTrue (blockSwap_ne_nf2_nf1 nf)),
    if_pos (natBeqSelf (nf + 2))]

/-- `blockSwap nf (nf+3) = nf + 1`. -/
theorem blockSwap_nf3 (nf : Nat) : blockSwap nf (nf + 3) = nf + 1 := by
  show (if nf + 3 == nf then nf + 2 else if nf + 3 == nf + 1 then nf + 3
        else if nf + 3 == nf + 2 then nf else if nf + 3 == nf + 3 then nf + 1 else _) = nf + 1
  rw [if_neg (natBeqNeTrue (blockSwap_ne_nf3_nf nf)), if_neg (natBeqNeTrue (blockSwap_ne_nf3_nf1 nf)),
    if_neg (natBeqNeTrue (blockSwap_ne_nf3_nf2 nf)), if_pos (natBeqSelf (nf + 3))]

/-- ★ **`blockSwap nf` is an involution** — swapping twice restores the id (the four swap targets round-trip; every
other id is fixed twice).  Case on where `identifier` sits among the four fresh ids and below/above the window. -/
theorem blockSwap_involutive (nf identifier : Nat) : blockSwap nf (blockSwap nf identifier) = identifier := by
  cases hb0 : identifier == nf with
  | true => rw [of_decide_eq_true hb0, blockSwap_nf, blockSwap_nf2]
  | false =>
    cases hb1 : identifier == nf + 1 with
    | true => rw [of_decide_eq_true hb1, blockSwap_nf1, blockSwap_nf3]
    | false =>
      cases hb2 : identifier == nf + 2 with
      | true => rw [of_decide_eq_true hb2, blockSwap_nf2, blockSwap_nf]
      | false =>
        cases hb3 : identifier == nf + 3 with
        | true => rw [of_decide_eq_true hb3, blockSwap_nf3, blockSwap_nf1]
        | false =>
          have fixed : blockSwap nf identifier = identifier := by
            show (if identifier == nf then nf + 2 else if identifier == nf + 1 then nf + 3
                  else if identifier == nf + 2 then nf else if identifier == nf + 3 then nf + 1
                  else identifier) = identifier
            rw [if_neg (natBeqNeTrue (neOfBeqFalse hb0)), if_neg (natBeqNeTrue (neOfBeqFalse hb1)),
              if_neg (natBeqNeTrue (neOfBeqFalse hb2)), if_neg (natBeqNeTrue (neOfBeqFalse hb3))]
          rw [fixed, fixed]

/-- `blockSwap nf` is injective (an involution is its own inverse). -/
theorem blockSwap_injective (nf : Nat) :
    ∀ firstNode secondNode, blockSwap nf firstNode = blockSwap nf secondNode → firstNode = secondNode :=
  fun firstNode secondNode himg => by
    have hround := congrArg (blockSwap nf) himg
    rw [blockSwap_involutive, blockSwap_involutive] at hround
    exact hround

/-! ## Root-following commutation from parent-following commutation -/

/-- ★ **Automorphism transports root, generically.**  If `sigma` commutes with the parent function
(`unionFindParent linksT (sigma n) = (unionFindParent linksS n).map sigma`), it commutes with root-following at
every fuel.  Fuel induction: base is `rfl`; the step rewrites the head parent lookup by the commutation and recurses
on the parent. -/
theorem unionFindRoot_map_of_parentComm (sigma : Nat → Nat) (linksS linksT : List (Nat × Nat))
    (parentComm : ∀ node, unionFindParent linksT (sigma node) = (unionFindParent linksS node).map sigma) :
    (fuel node : Nat) → unionFindRoot fuel linksT (sigma node) = sigma (unionFindRoot fuel linksS node)
  | 0, _ => rfl
  | fuel + 1, node => by
      show (match unionFindParent linksT (sigma node) with
              | none => sigma node | some parent => unionFindRoot fuel linksT parent)
         = sigma (match unionFindParent linksS node with
              | none => node | some parent => unionFindRoot fuel linksS parent)
      rw [parentComm node]
      cases unionFindParent linksS node with
      | none => rfl
      | some parent => exact unionFindRoot_map_of_parentComm sigma linksS linksT parentComm fuel parent

/-! ## The crux — `blockSwap` is a union-find automorphism of the two-fresh-join graph -/

/-- ★ **The cup-restricted `rootComm` (the make-or-break).**  Over a fresh forest `orig` (every edge endpoint
strictly below `nf`), the block transposition `blockSwap nf` is a union-find automorphism of the two-fresh-join
graph `L = (nf+2, nf+3) :: (nf, nf+1) :: orig`:

  `unionFindRootOf L (blockSwap nf x) = blockSwap nf (unionFindRootOf L x)`.

This is the CUP restriction of the machine-refuted general `MatchingGodementCoreSwapSim.rootComm`: because cups
allocate FRESH legs, both Godement run orders build the IDENTICAL `L`, and the swap acts only on the two disjoint
fresh edges — a genuine root-preserving automorphism (unlike the cap/merge case where the merged root flips with
the join order).  Proven by the two `unionFindRootOf_consJoin` closed forms + a finite case analysis on where `x`
sits relative to `nf … nf+3`, discharging every branch with freshness. -/
theorem blockSwap_rootComm (nf : Nat) (orig : List (Nat × Nat))
    (origBelow : ∀ edge ∈ orig, edge.1 < nf ∧ edge.2 < nf)
    (origForest : isUnionFindForest orig) :
    ∀ x, unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) (blockSwap nf x)
       = blockSwap nf (unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) x) := by
  have childrenBelow : ∀ edge ∈ orig, edge.1 < nf := fun edge he => (origBelow edge he).1
  have parentsBelow : ∀ edge ∈ orig, edge.2 < nf := fun edge he => (origBelow edge he).2
  have plNf : unionFindParent orig nf = none :=
    unionFindParent_none_of_lt nf orig childrenBelow nf (Nat.le_refl _)
  have plNf1 : unionFindParent orig (nf + 1) = none :=
    unionFindParent_none_of_lt nf orig childrenBelow (nf + 1) (Nat.le_add_right _ _)
  have l1ChildrenBelow : ∀ edge ∈ (nf, nf + 1) :: orig, edge.1 < nf + 2 := by
    intro edge he
    cases he with
    | head => exact Nat.lt_add_of_pos_right (by decide)
    | tail _ heRest => exact Nat.lt_trans (childrenBelow edge heRest) (Nat.lt_add_of_pos_right (by decide))
  have plNf2 : unionFindParent ((nf, nf + 1) :: orig) (nf + 2) = none :=
    unionFindParent_none_of_lt (nf + 2) ((nf, nf + 1) :: orig) l1ChildrenBelow (nf + 2) (Nat.le_refl _)
  have plNf3 : unionFindParent ((nf, nf + 1) :: orig) (nf + 3) = none :=
    unionFindParent_none_of_lt (nf + 2) ((nf, nf + 1) :: orig) l1ChildrenBelow (nf + 3)
      (Nat.le_succ_of_le (Nat.le_refl (nf + 2)))
  have distinctNf : ¬ (nf == nf + 1) = true := natBeqNeTrue (fun h => (blockSwap_ne_nf1_nf nf) h.symm)
  have distinctNf2 : ¬ (nf + 2 == nf + 3) = true := natBeqNeTrue (fun h => (blockSwap_ne_nf3_nf2 nf) h.symm)
  have forestL1 : isUnionFindForest ((nf, nf + 1) :: orig) := ⟨plNf, plNf1, distinctNf, origForest⟩
  have rootOrigGe : ∀ node, nf ≤ node → unionFindRootOf orig node = node := fun node hle =>
    unionFindRootOf_of_parentless orig node (unionFindParent_none_of_lt nf orig childrenBelow node hle)
  have rootOrigLt : ∀ node, node < nf → unionFindRootOf orig node < nf := fun node hlt =>
    unionFindRootOf_lt_of_fresh orig nf parentsBelow node hlt
  have rootL1 : ∀ node, unionFindRootOf ((nf, nf + 1) :: orig) node
      = if nf == unionFindRootOf orig node then nf + 1 else unionFindRootOf orig node := fun node =>
    unionFindRootOf_consJoin orig nf (nf + 1) origForest plNf plNf1 distinctNf node
  have rootL : ∀ node, unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) node
      = if nf + 2 == unionFindRootOf ((nf, nf + 1) :: orig) node then nf + 3
        else unionFindRootOf ((nf, nf + 1) :: orig) node := fun node =>
    unionFindRootOf_consJoin ((nf, nf + 1) :: orig) (nf + 2) (nf + 3) forestL1 plNf2 plNf3 distinctNf2 node
  -- The four fresh-id root values, closed.
  have geNf1 : nf ≤ nf + 1 := Nat.le_add_right _ _
  have geNf2 : nf ≤ nf + 2 := Nat.le_add_right _ _
  have geNf3 : nf ≤ nf + 3 := Nat.le_add_right _ _
  have rootL_nf : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) nf = nf + 1 := by
    rw [rootL nf, rootL1 nf, rootOrigGe nf (Nat.le_refl _), if_pos (natBeqSelf nf),
      if_neg (natBeqNeTrue (blockSwap_ne_nf2_nf1 nf))]
  have rootL_nf1 : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) (nf + 1) = nf + 1 := by
    rw [rootL (nf + 1), rootL1 (nf + 1), rootOrigGe (nf + 1) geNf1,
      if_neg (natBeqNeTrue (fun h => (blockSwap_ne_nf1_nf nf) h.symm)),
      if_neg (natBeqNeTrue (blockSwap_ne_nf2_nf1 nf))]
  have rootL_nf2 : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) (nf + 2) = nf + 3 := by
    rw [rootL (nf + 2), rootL1 (nf + 2), rootOrigGe (nf + 2) geNf2,
      if_neg (natBeqNeTrue (fun h => (blockSwap_ne_nf2_nf nf) h.symm)), if_pos (natBeqSelf (nf + 2))]
  have rootL_nf3 : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) (nf + 3) = nf + 3 := by
    rw [rootL (nf + 3), rootL1 (nf + 3), rootOrigGe (nf + 3) geNf3,
      if_neg (natBeqNeTrue (fun h => (blockSwap_ne_nf3_nf nf) h.symm)),
      if_neg (natBeqNeTrue (fun h => (blockSwap_ne_nf3_nf2 nf) h.symm))]
  -- Main case analysis on where `x` sits, mirroring `blockSwap`'s guard structure.
  intro x
  cases hb0 : x == nf with
  | true => rw [of_decide_eq_true hb0, blockSwap_nf, rootL_nf, rootL_nf2, blockSwap_nf1]
  | false =>
    cases hb1 : x == nf + 1 with
    | true => rw [of_decide_eq_true hb1, blockSwap_nf1, rootL_nf1, rootL_nf3, blockSwap_nf1]
    | false =>
      cases hb2 : x == nf + 2 with
      | true => rw [of_decide_eq_true hb2, blockSwap_nf2, rootL_nf2, rootL_nf, blockSwap_nf3]
      | false =>
        cases hb3 : x == nf + 3 with
        | true => rw [of_decide_eq_true hb3, blockSwap_nf3, rootL_nf3, rootL_nf1, blockSwap_nf3]
        | false =>
          have swapFix : blockSwap nf x = x := by
            show (if x == nf then nf + 2 else if x == nf + 1 then nf + 3
                  else if x == nf + 2 then nf else if x == nf + 3 then nf + 1 else x) = x
            rw [if_neg (natBeqNeTrue (neOfBeqFalse hb0)), if_neg (natBeqNeTrue (neOfBeqFalse hb1)),
              if_neg (natBeqNeTrue (neOfBeqFalse hb2)), if_neg (natBeqNeTrue (neOfBeqFalse hb3))]
          rw [swapFix]
          cases Nat.lt_or_ge x nf with
          | inl hlt =>
              have hrx : unionFindRootOf orig x < nf := rootOrigLt x hlt
              have hrootLt : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) x < nf := by
                rw [rootL x, rootL1 x, if_neg (natBeqNeTrue (Nat.ne_of_gt hrx)),
                  if_neg (natBeqNeTrue (Nat.ne_of_gt (Nat.lt_trans hrx (Nat.lt_add_of_pos_right (by decide)))))]
                exact hrx
              exact (blockSwap_fix_lt nf _ hrootLt).symm
          | inr hge =>
              have neNf : x ≠ nf := neOfBeqFalse hb0
              have neNf2 : x ≠ nf + 2 := neOfBeqFalse hb2
              have hrootEq : unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) x = x := by
                rw [rootL x, rootL1 x, rootOrigGe x hge,
                  if_neg (natBeqNeTrue (fun h => neNf h.symm)),
                  if_neg (natBeqNeTrue (fun h => neNf2 h.symm))]
              rw [hrootEq, swapFix]

/-! ## Bridge to the general `blockRotate` keystone permutation

The matching keystone infrastructure (`MatchingSigmaBundle`, `MatchingBlockSwapAssembly`) states every
order-blind field (openMap, nfEq, loopsEq, forests, and the WEAKENED component-level correspondence) with the
general block-rotation permutation `blockRotate lo w1 w2` for arbitrary block widths `w1`, `w2`.  For TWO cups each
allocating exactly `2` fresh legs (`w1 = w2 = 2`), that rotation IS `blockSwap`, so the general legs compose with
the ROOT-level `blockSwap_rootComm` — the field the general keystone could not supply (refuted for caps). -/

/-- ★ **`blockRotate lo 2 2 = blockSwap lo`** (pointwise).  Two width-`2` blocks: the first block `[lo, lo+2)`
shifts up by `2` (`lo ↦ lo+2`, `lo+1 ↦ lo+3`), the second block `[lo+2, lo+4)` shifts down by `2`
(`lo+2 ↦ lo`, `lo+3 ↦ lo+1`) — the 4-id transposition.  Case on where `x` sits among the four window ids. -/
theorem blockRotate_two_two_eq_blockSwap (lo x : Nat) : blockRotate lo 2 2 x = blockSwap lo x := by
  cases hb0 : x == lo with
  | true =>
      rw [of_decide_eq_true hb0, blockSwap_nf,
        blockRotate_firstBlock lo 2 2 lo (Nat.le_refl _) (Nat.lt_add_of_pos_right (by decide))]
  | false =>
    cases hb1 : x == lo + 1 with
    | true =>
        rw [of_decide_eq_true hb1, blockSwap_nf1,
          blockRotate_firstBlock lo 2 2 (lo + 1) (Nat.le_add_right _ _) (Nat.lt_succ_self (lo + 1))]
    | false =>
      cases hb2 : x == lo + 2 with
      | true =>
          rw [of_decide_eq_true hb2, blockSwap_nf2,
            blockRotate_secondBlock lo 2 2 (lo + 2) (Nat.le_refl _)
              (Nat.lt_add_of_pos_right (by decide))]
          exact addSubCancelRight lo 2
      | false =>
        cases hb3 : x == lo + 3 with
        | true =>
            rw [of_decide_eq_true hb3, blockSwap_nf3,
              blockRotate_secondBlock lo 2 2 (lo + 3) (Nat.le_succ (lo + 2)) (Nat.lt_succ_self (lo + 3))]
            exact addSubCancelRight (lo + 1) 2
        | false =>
          have swapFix : blockSwap lo x = x := by
            show (if x == lo then lo + 2 else if x == lo + 1 then lo + 3
                  else if x == lo + 2 then lo else if x == lo + 3 then lo + 1 else x) = x
            rw [if_neg (natBeqNeTrue (neOfBeqFalse hb0)), if_neg (natBeqNeTrue (neOfBeqFalse hb1)),
              if_neg (natBeqNeTrue (neOfBeqFalse hb2)), if_neg (natBeqNeTrue (neOfBeqFalse hb3))]
          cases Nat.lt_or_ge x lo with
          | inl hlt => rw [blockRotate_below lo 2 2 x hlt, swapFix]
          | inr hge =>
              have ge1 : lo + 1 ≤ x := Nat.lt_of_le_of_ne hge ((neOfBeqFalse hb0).symm)
              have ge2 : lo + 2 ≤ x := Nat.lt_of_le_of_ne ge1 ((neOfBeqFalse hb1).symm)
              have ge3 : lo + 3 ≤ x := Nat.lt_of_le_of_ne ge2 ((neOfBeqFalse hb2).symm)
              have ge4 : lo + 2 + 2 ≤ x := Nat.lt_of_le_of_ne ge3 ((neOfBeqFalse hb3).symm)
              rw [blockRotate_above lo 2 2 x ge4, swapFix]

/-- ★ **The cup-restricted `rootComm` in the general `blockRotate` form** — the exact field the matching keystone
bundle (`matchingCoreSwap_componentSim_blockRotate`) supplies only at the WEAKENED component level.  For two cups
(`w1 = w2 = 2`) the block rotation `blockRotate nf 2 2` is a union-find automorphism of the two-fresh-join graph. -/
theorem blockRotate_two_two_rootComm (nf : Nat) (orig : List (Nat × Nat))
    (origBelow : ∀ edge ∈ orig, edge.1 < nf ∧ edge.2 < nf)
    (origForest : isUnionFindForest orig) :
    ∀ x, unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) (blockRotate nf 2 2 x)
       = blockRotate nf 2 2 (unionFindRootOf ((nf + 2, nf + 3) :: (nf, nf + 1) :: orig) x) := by
  intro x
  rw [blockRotate_two_two_eq_blockSwap, blockRotate_two_two_eq_blockSwap]
  exact blockSwap_rootComm nf orig origBelow origForest x

end FX1Poly.Polygraph
