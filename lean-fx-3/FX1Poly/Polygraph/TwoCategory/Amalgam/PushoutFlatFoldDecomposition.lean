import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatVcompZip

/-! # Polygraph/TwoCategory/Amalgam/PushoutFlatFoldDecomposition — the arity fold of a flat layout decomposes
BLOCK-DIAGONALLY, and equal whole-cell folds force equal per-slot payload folds (WP-AMALG r30, Brick C)

The semantic heart of the Nelson-Oppen completeness: the payload-blind arity fold (`arityMonotoneMapOf`, the
Δ₊ monotone map) of a flat wall/gap layout is the BLOCK JOIN of the per-slot payload folds — the walls are
fixed points, the gaps act on disjoint source windows.  Consequently the whole fold DETERMINES the per-slot
folds (given the boundary geometry, which parsing uniqueness already pins):

  * **`arityFold_hcomp_append`** — the closed form: `fold(α ⊠ β) = fold α ++ shift |codα| (fold β)`, computed
    off the shipped generic embedding algebra (`arityMonotoneMapOf_hcomp` + the three `embedLocalMap` region
    characterizations), under the pushout's arity discipline (`pushoutHasFaceDegenArity`).
  * **`SlotPayloadFoldsAligned`** — pointwise payload-fold equality of two slot lists.
  * **`flatFold_slots_aligned`** — ★ THE EXTRACTION: two flat layouts with equal boundary geometry and equal
    whole-cell folds have POINTWISE EQUAL payload folds.  This is the "descent" of the r20 JAM-A ledger in its
    honest semantic form: the whole-cell invariant factors block-diagonally, so per-gap data is recoverable —
    no convex-block projection of derivations is ever needed.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## List plumbing for the block join (propext-free, hand-rolled) -/

/-- Shift every entry of a value-list up by an offset. -/
def shiftMapBy (offset : Nat) : List Nat → List Nat
  | [] => []
  | value :: rest => (offset + value) :: shiftMapBy offset rest

/-- The shift preserves length. -/
theorem shiftMapBy_length (offset : Nat) :
    (values : List Nat) → (shiftMapBy offset values).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (shiftMapBy_length offset rest)

/-- Left-cancellation of `Nat` addition, hand-rolled propext-free (core `Nat.add_left_cancel` leaks
`propext`). -/
theorem natAddLeftCancelClean : (front valueA valueB : Nat) → front + valueA = front + valueB →
    valueA = valueB
  | 0, _, _, h => by
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | front + 1, valueA, valueB, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact natAddLeftCancelClean front valueA valueB (Nat.succ.inj h)

/-- The shift is injective (clean left-cancellation entrywise). -/
theorem shiftMapBy_injective (offset : Nat) :
    (valuesA valuesB : List Nat) → shiftMapBy offset valuesA = shiftMapBy offset valuesB →
    valuesA = valuesB
  | [], [], _ => rfl
  | [], _ :: _, hshift => by
    have hlen := congrArg List.length hshift
    rw [shiftMapBy_length, shiftMapBy_length] at hlen
    exact Nat.noConfusion hlen
  | _ :: _, [], hshift => by
    have hlen := congrArg List.length hshift
    rw [shiftMapBy_length, shiftMapBy_length] at hlen
    exact Nat.noConfusion hlen
  | valueA :: restA, valueB :: restB, hshift => by
    injection hshift with headEq tailEq
    rw [natAddLeftCancelClean offset valueA valueB headEq,
      shiftMapBy_injective offset restA restB tailEq]

/-- `monotoneMapGet` reads the LEFT part of an append below the prefix length. -/
theorem monotoneMapGet_appendLeft :
    (prefixList suffixList : List Nat) → (position : Nat) → position < prefixList.length →
    monotoneMapGet (prefixList ++ suffixList) position = monotoneMapGet prefixList position
  | [], _, _, hpos => absurd hpos (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: prefixRest, suffixList, position + 1, hpos =>
      monotoneMapGet_appendLeft prefixRest suffixList position (Nat.lt_of_succ_lt_succ hpos)

/-- `monotoneMapGet` reads the RIGHT part of an append at prefix-length offsets. -/
theorem monotoneMapGet_appendRight :
    (prefixList suffixList : List Nat) → (offset : Nat) →
    monotoneMapGet (prefixList ++ suffixList) (prefixList.length + offset)
      = monotoneMapGet suffixList offset
  | [], suffixList, offset => by
      show monotoneMapGet suffixList (0 + offset) = monotoneMapGet suffixList offset
      rw [Nat.zero_add]
  | value :: prefixRest, suffixList, offset => by
      have hpos : (value :: prefixRest).length + offset = (prefixRest.length + offset) + 1 :=
        Nat.add_right_comm prefixRest.length 1 offset
      rw [hpos]
      show monotoneMapGet (prefixRest ++ suffixList) (prefixRest.length + offset)
        = monotoneMapGet suffixList offset
      exact monotoneMapGet_appendRight prefixRest suffixList offset

/-- `monotoneMapGet` of a shift is the offset plus the base value (in range). -/
theorem monotoneMapGet_shiftMapBy (offset : Nat) :
    (values : List Nat) → (position : Nat) → position < values.length →
    monotoneMapGet (shiftMapBy offset values) position = offset + monotoneMapGet values position
  | [], _, hpos => absurd hpos (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, position + 1, hpos =>
      monotoneMapGet_shiftMapBy offset rest position (Nat.lt_of_succ_lt_succ hpos)

/-- Append length, restated locally off the shipped propext-free `lengthAppend`. -/
theorem appendLengthNat (prefixList suffixList : List Nat) :
    (prefixList ++ suffixList).length = prefixList.length + suffixList.length :=
  lengthAppend prefixList suffixList

/-- Appends with equal-length prefixes split (`prefix` and `suffix` each equal). -/
theorem append_split_of_prefixLength :
    (prefixA prefixB suffixA suffixB : List Nat) → prefixA.length = prefixB.length →
    prefixA ++ suffixA = prefixB ++ suffixB → prefixA = prefixB ∧ suffixA = suffixB
  | [], [], _, _, _, happend => ⟨rfl, happend⟩
  | [], _ :: _, _, _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], _, _, hlen, _ => Nat.noConfusion hlen
  | headA :: prefixA, headB :: prefixB, suffixA, suffixB, hlen, happend => by
    injection happend with headEq tailEq
    obtain ⟨prefixEq, suffixEq⟩ :=
      append_split_of_prefixLength prefixA prefixB suffixA suffixB (Nat.succ.inj hlen) tailEq
    exact ⟨by rw [headEq, prefixEq], suffixEq⟩

/-! ## The closed form of the horizontal composite's fold -/

/-- ★★★ **THE BLOCK-JOIN CLOSED FORM** — under the arity discipline, the fold of a horizontal composite is the
APPEND of the head fold with the shifted tail fold: `fold(α ⊠ β) = fold α ++ shift |codα| (fold β)`.  Pointwise
off the shipped embedding algebra: below the head's source width the composite reads the head fold (middle
region into the left identity region); above it, the right identity region into the shifted middle region. -/
theorem arityFold_hcomp_append {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    arityMonotoneMapOf (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = arityMonotoneMapOf cellAlpha
          ++ shiftMapBy oneCellFCod.length (arityMonotoneMapOf cellBeta) := by
  rw [arityMonotoneMapOf_hcomp disc]
  apply listExtById
  · rw [composeMap_length, embedLocalMap_length, appendLengthNat, shiftMapBy_length,
      arityMonotoneMapOf_length disc cellAlpha, arityMonotoneMapOf_length disc cellBeta,
      Nat.zero_add]
  · intro position hpos
    rw [composeMap_length, embedLocalMap_length, Nat.zero_add,
      arityMonotoneMapOf_length disc cellAlpha] at hpos
    have hcompGet := composeMap_get
      (embedLocalMap 0 oneCellFCod.length oneCellGDom.length (arityMonotoneMapOf cellAlpha))
      (embedLocalMap oneCellFCod.length oneCellGCod.length 0 (arityMonotoneMapOf cellBeta))
      position
      (by rw [embedLocalMap_length, Nat.zero_add, arityMonotoneMapOf_length disc cellAlpha]
          exact hpos)
    rw [hcompGet]
    rcases Nat.lt_or_ge position (arityMonotoneMapOf cellAlpha).length with hleft | hright
    · -- head region
      have hmid := embedLocalMap_get_mid 0 oneCellFCod.length oneCellGDom.length
        (arityMonotoneMapOf cellAlpha) position hleft
      rw [Nat.zero_add, Nat.zero_add] at hmid
      rw [hmid]
      have hinto : monotoneMapGet (arityMonotoneMapOf cellAlpha) position < oneCellFCod.length :=
        arityMonotoneMapOf_mapsInto disc cellAlpha position hleft
      rw [embedLocalMap_get_left oneCellFCod.length oneCellGCod.length 0
          (arityMonotoneMapOf cellBeta) _ hinto,
        monotoneMapGet_appendLeft (arityMonotoneMapOf cellAlpha)
          (shiftMapBy oneCellFCod.length (arityMonotoneMapOf cellBeta)) position hleft]
    · -- tail region
      obtain ⟨offset, rfl⟩ : ∃ offset, position = (arityMonotoneMapOf cellAlpha).length + offset :=
        ⟨position - (arityMonotoneMapOf cellAlpha).length, (addSubCancel hright).symm⟩
      have hoffLt : offset < oneCellGDom.length := by
        have := Nat.lt_of_add_lt_add_left
          (by rw [arityMonotoneMapOf_length disc cellAlpha] at hpos ⊢; exact hpos :
            (arityMonotoneMapOf cellAlpha).length + offset
              < (arityMonotoneMapOf cellAlpha).length + oneCellGDom.length)
        exact this
      have hrightGet := embedLocalMap_get_right 0 oneCellFCod.length oneCellGDom.length
        (arityMonotoneMapOf cellAlpha) offset hoffLt
      rw [Nat.zero_add, Nat.zero_add] at hrightGet
      rw [hrightGet]
      have hbetaLen : offset < (arityMonotoneMapOf cellBeta).length := by
        rw [arityMonotoneMapOf_length disc cellBeta]
        exact hoffLt
      rw [embedLocalMap_get_mid oneCellFCod.length oneCellGCod.length 0
          (arityMonotoneMapOf cellBeta) offset hbetaLen,
        monotoneMapGet_appendRight (arityMonotoneMapOf cellAlpha)
          (shiftMapBy oneCellFCod.length (arityMonotoneMapOf cellBeta)) offset,
        monotoneMapGet_shiftMapBy oneCellFCod.length (arityMonotoneMapOf cellBeta) offset hbetaLen]

/-- The fold of an identity 2-cell is the identity map (`rfl`: the spine is empty). -/
theorem arityFold_id {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (path : ModalityPath signature.graph sourceMode targetMode) :
    arityMonotoneMapOf (RawTwoCellExpr.id (signature := signature) path) = idMap path.length := rfl

/-! ## The per-slot extraction -/

/-- Pointwise payload-fold equality of two slot lists. -/
inductive SlotPayloadFoldsAligned : List GapSlot → List GapSlot → Prop where
  | nil : SlotPayloadFoldsAligned [] []
  | cons (slotA slotB : GapSlot) (restA restB : List GapSlot) :
      arityMonotoneMapOf slotA.payload = arityMonotoneMapOf slotB.payload →
      SlotPayloadFoldsAligned restA restB →
      SlotPayloadFoldsAligned (slotA :: restA) (slotB :: restB)

/-- The fold of a flat layout, one peel: head payload fold appended with the wall fixed point and the shifted
rest fold. -/
theorem flatFold_peel (headSlot nextSlot : GapSlot) (restSlots : List GapSlot) :
    arityMonotoneMapOf (flatSlotsCell headSlot (nextSlot :: restSlots))
      = arityMonotoneMapOf headSlot.payload
          ++ shiftMapBy headSlot.gapCod.length
              (idMap 1 ++ shiftMapBy 1 (arityMonotoneMapOf (flatSlotsCell nextSlot restSlots))) := by
  show arityMonotoneMapOf
      (RawTwoCellExpr.hcomp headSlot.payload
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
          (flatSlotsCell nextSlot restSlots)))
    = _
  rw [arityFold_hcomp_append pushoutHasFaceDegenArity headSlot.payload
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (flatSlotsCell nextSlot restSlots)),
    arityFold_hcomp_append pushoutHasFaceDegenArity
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (flatSlotsCell nextSlot restSlots)]
  rfl

/-- ★★★ **THE PER-SLOT EXTRACTION** — two flat layouts with equal boundary geometry (pointwise equal gap
boundaries) and equal whole-cell folds have POINTWISE EQUAL payload folds.  Structural recursion peeling one
block at a time: the block-join closed form splits the append (`append_split_of_prefixLength`, prefix lengths
pinned by the geometry), the wall fixed point drops (`List` cons injection), and the shift cancels
(`shiftMapBy_injective`). -/
theorem flatFold_slots_aligned :
    (headA headB : GapSlot) → (tailA tailB : List GapSlot) →
    headA.gapDom = headB.gapDom → headA.gapCod = headB.gapCod →
    tailA.map GapSlot.gapDom = tailB.map GapSlot.gapDom →
    tailA.map GapSlot.gapCod = tailB.map GapSlot.gapCod →
    arityMonotoneMapOf (flatSlotsCell headA tailA) = arityMonotoneMapOf (flatSlotsCell headB tailB) →
    SlotPayloadFoldsAligned (headA :: tailA) (headB :: tailB)
  | headA, headB, [], [], _, _, _, _, hfold =>
      SlotPayloadFoldsAligned.cons headA headB [] [] hfold SlotPayloadFoldsAligned.nil
  | _, _, [], _ :: _, _, _, hmapDom, _, _ =>
      Nat.noConfusion (congrArg List.length hmapDom)
  | _, _, _ :: _, [], _, _, hmapDom, _, _ =>
      Nat.noConfusion (congrArg List.length hmapDom)
  | headA, headB, nextA :: restA, nextB :: restB, hDomHead, hCodHead, hmapDom, hmapCod, hfold => by
    have nextDomEq : nextA.gapDom = nextB.gapDom := by injection hmapDom
    have restDomEq : restA.map GapSlot.gapDom = restB.map GapSlot.gapDom := by injection hmapDom
    have nextCodEq : nextA.gapCod = nextB.gapCod := by injection hmapCod
    have restCodEq : restA.map GapSlot.gapCod = restB.map GapSlot.gapCod := by injection hmapCod
    rw [flatFold_peel headA nextA restA, flatFold_peel headB nextB restB] at hfold
    have prefixLenEq : (arityMonotoneMapOf headA.payload).length
        = (arityMonotoneMapOf headB.payload).length := by
      rw [arityMonotoneMapOf_length pushoutHasFaceDegenArity headA.payload,
        arityMonotoneMapOf_length pushoutHasFaceDegenArity headB.payload, hDomHead]
    obtain ⟨headFoldEq, suffixEq⟩ :=
      append_split_of_prefixLength _ _ _ _ prefixLenEq hfold
    rw [hCodHead] at suffixEq
    have shiftedEq := shiftMapBy_injective headB.gapCod.length _ _ suffixEq
    have shiftedConsEq : (0 : Nat) :: shiftMapBy 1 (arityMonotoneMapOf (flatSlotsCell nextA restA))
        = (0 : Nat) :: shiftMapBy 1 (arityMonotoneMapOf (flatSlotsCell nextB restB)) := shiftedEq
    have consEq : shiftMapBy 1 (arityMonotoneMapOf (flatSlotsCell nextA restA))
        = shiftMapBy 1 (arityMonotoneMapOf (flatSlotsCell nextB restB)) := by
      injection shiftedConsEq
    exact SlotPayloadFoldsAligned.cons headA headB (nextA :: restA) (nextB :: restB) headFoldEq
      (flatFold_slots_aligned nextA nextB restA restB nextDomEq nextCodEq restDomEq restCodEq
        (shiftMapBy_injective 1 _ _ consEq))

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the flat layout's fold decomposes BLOCK-DIAGONALLY (WP-AMALG r30, Brick C).**
`= true`.  The block-join closed form (`arityFold_hcomp_append`, off the shipped generic embedding algebra
under the pushout's arity discipline) and THE PER-SLOT EXTRACTION (`flatFold_slots_aligned`): equal whole-cell
folds + equal boundary geometry force pointwise equal payload folds.  This is the honest semantic form of the
r20 JAM-A "per-gap descent": the whole-cell Δ₊ invariant factors block-diagonally over the wall/gap layout, so
per-gap data is RECOVERED from the whole — no convex-block projection of derivations, no wire-creation
obstruction (the wire-creating `eta`/`mu` change only the TARGET widths, which the shared codomain geometry
pins).  The decider and the dispatch are the successor brick; NO master flips here.  `= true`. -/
def fxAmalg_hasFlatFoldDecomposition : Bool := true

end FX1Poly.Polygraph.Amalgam
