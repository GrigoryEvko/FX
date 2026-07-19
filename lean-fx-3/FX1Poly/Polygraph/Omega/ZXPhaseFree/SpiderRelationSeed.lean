/-! # Polygraph/Omega/ZXPhaseFree/SpiderRelationSeed — the WP-ZX seed

Phase-free ZX diagrams (no Hadamard, no phases) with the F2 linear-relations semantics
(IB = IH_Z2 = LinRel_F2; Kissinger arXiv:2204.14038, Bonchi-Sobocinski-Zanasi
arXiv:1403.7048).  The full binding presentation-diff table lives on the
`zxpCompletenessStatement` docstring at the bottom of this file.

Contents: (0) fresh Bool-xor and structural-Nat kits; (1) the F2 row kit (dense
`List Bool` rows, cons-only, width-external); (2) inductive spans (`ZxpMemSpan`) with the
xor-closure algebra; (3) echelonization by sorted insertion + reduction + THE SPAN
DECISION `zxpSpanEqB` (mutual reduction) with BOTH soundness and completeness against
`ZxpMemSpan`, plus `zxpRref` (back-substituted echelon) with `zxpRrefSpansSame`
row-space preservation — the canonical-representative fallback documented by the
commission: span equality is DECIDED by mutual reduction rather than by syntactic RREF
uniqueness, which serves every decision need and keeps the kit lean; (2b) relations as
generator matrices with external arities, relational composition (middle block LEFTMOST,
echelonize, keep zero-middle rows, project) with the full pullback characterization
`zxpComposeSpec`, the interleaved tensor with `zxpTensorSpec`, identity/swap, and the
categorical laws up to span equality (compose/tensor congruence, associativity, units,
`zxpTensorComposeInterchange`); (3) the strict-layer diagram carrier (fresh re-derivation
of the `LafontProp.StrictLayerDiagram` layer-list idiom — DECISION: re-derived, not
imported, so the F2 lane stays self-contained and drags no Mat(N) semantics in);
(4) THE PUBLISHED ROW SET (33 tags: IH A1-A10 + mirrors, Hopf with trivial antipode,
bones, both Frobenius orientations, special laws, Z2 cup/cap coincidence, Kissinger (sp)
identity rows) as one-step window rewrites through the pad combinator, the
boundary-indexed groupoid congruence `ZxpConv` with layer-split moves (exchange DERIVED
in `zxpSplitLayerBundle`), and SOUNDNESS `zxpConvSound`: convertible diagrams denote the
same F2 linear relation — with the refutation bridge `zxpConvSpanEqB` giving the negative
direction (distinct spans => not convertible); (5) fires: Hopf (THE phase-free
signature), bialgebra square, spider fusion both colours, FALSE cases (Z-unit vs X-unit,
crossing vs wires), the 0-arity scalar collapse; (6) honesty markers — completeness is
OWNER FALSE with the invariant-first gate requirement.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`, no
`Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the Bool xor and the structural Nat comparison kit

`Bool.xor` from Init is avoided in favour of a four-case fresh definition so every algebraic
fact is a per-constructor `rfl`; Nat order is handled by a fresh three-way structural
comparator plus a structural Bool `<=`, so no `Nat.le`/`Nat.lt` lemma from Init is ever
touched (the propext-dirty corners of that family stay out of reach by construction). -/

/-- Exclusive or on `Bool`, fresh four-case definition (F2 addition). -/
def zxpXorB : Bool -> Bool -> Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

theorem zxpXorBComm : (leftBit rightBit : Bool) ->
    zxpXorB leftBit rightBit = zxpXorB rightBit leftBit
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

theorem zxpXorBAssoc : (firstBit secondBit thirdBit : Bool) ->
    zxpXorB (zxpXorB firstBit secondBit) thirdBit
      = zxpXorB firstBit (zxpXorB secondBit thirdBit)
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

theorem zxpXorBFalseLeft : (anyBit : Bool) -> zxpXorB false anyBit = anyBit
  | false => rfl
  | true => rfl

theorem zxpXorBFalseRight : (anyBit : Bool) -> zxpXorB anyBit false = anyBit
  | false => rfl
  | true => rfl

theorem zxpXorBSelf : (anyBit : Bool) -> zxpXorB anyBit anyBit = false
  | false => rfl
  | true => rfl

/-- Three-way order witness for the structural Nat comparator. -/
inductive ZxpOrder : Type where
  | isLt : ZxpOrder
  | isEq : ZxpOrder
  | isGt : ZxpOrder

/-- Structural three-way comparison on `Nat` (no `Nat.lt`/`Nat.ble` from Init). -/
def zxpNatCompare : Nat -> Nat -> ZxpOrder
  | 0, 0 => ZxpOrder.isEq
  | 0, _secondPred + 1 => ZxpOrder.isLt
  | _firstPred + 1, 0 => ZxpOrder.isGt
  | firstPred + 1, secondPred + 1 => zxpNatCompare firstPred secondPred

/-- Structural Bool `<=` on `Nat`. -/
def zxpNatLe : Nat -> Nat -> Bool
  | 0, _anyBound => true
  | _firstPred + 1, 0 => false
  | firstPred + 1, secondPred + 1 => zxpNatLe firstPred secondPred

theorem zxpNatCompareRefl : (value : Nat) -> zxpNatCompare value value = ZxpOrder.isEq
  | 0 => rfl
  | valuePred + 1 => zxpNatCompareRefl valuePred

theorem zxpNatCompareEqImpliesEq : (firstValue secondValue : Nat) ->
    zxpNatCompare firstValue secondValue = ZxpOrder.isEq -> firstValue = secondValue
  | 0, 0, _hEq => rfl
  | 0, _secondPred + 1, hEq => ZxpOrder.noConfusion hEq
  | _firstPred + 1, 0, hEq => ZxpOrder.noConfusion hEq
  | firstPred + 1, secondPred + 1, hEq =>
      congrArg (fun innerValue => innerValue + 1)
        (zxpNatCompareEqImpliesEq firstPred secondPred hEq)

theorem zxpNatLeRefl : (value : Nat) -> zxpNatLe value value = true
  | 0 => rfl
  | valuePred + 1 => zxpNatLeRefl valuePred

theorem zxpNatLeZeroLeft : (value : Nat) -> zxpNatLe 0 value = true
  | 0 => rfl
  | _valuePred + 1 => rfl

theorem zxpNatLeTrans : (firstValue secondValue thirdValue : Nat) ->
    zxpNatLe firstValue secondValue = true -> zxpNatLe secondValue thirdValue = true ->
    zxpNatLe firstValue thirdValue = true
  | 0, _secondValue, thirdValue, _hFirst, _hSecond => zxpNatLeZeroLeft thirdValue
  | _firstPred + 1, 0, _thirdValue, hFirst, _hSecond => Bool.noConfusion hFirst
  | _firstPred + 1, _secondPred + 1, 0, _hFirst, hSecond => Bool.noConfusion hSecond
  | firstPred + 1, secondPred + 1, thirdPred + 1, hFirst, hSecond =>
      zxpNatLeTrans firstPred secondPred thirdPred hFirst hSecond

theorem zxpNatLeSuccRight : (firstValue secondValue : Nat) ->
    zxpNatLe firstValue secondValue = true -> zxpNatLe firstValue (secondValue + 1) = true
  | 0, _secondValue, _hLe => rfl
  | _firstPred + 1, 0, hLe => Bool.noConfusion hLe
  | firstPred + 1, secondPred + 1, hLe => zxpNatLeSuccRight firstPred secondPred hLe

/-- `a < b` (as the comparator) gives `a + 1 <= b`. -/
theorem zxpNatLeSuccOfCompareLt : (firstValue secondValue : Nat) ->
    zxpNatCompare firstValue secondValue = ZxpOrder.isLt ->
    zxpNatLe (firstValue + 1) secondValue = true
  | 0, 0, hLt => ZxpOrder.noConfusion hLt
  | 0, secondPred + 1, _hLt => zxpNatLeZeroLeft secondPred
  | _firstPred + 1, 0, hLt => ZxpOrder.noConfusion hLt
  | firstPred + 1, secondPred + 1, hLt => zxpNatLeSuccOfCompareLt firstPred secondPred hLt

/-- `a + 1 <= b` gives `a < b` (as the comparator). -/
theorem zxpNatCompareLtOfLeSucc : (firstValue secondValue : Nat) ->
    zxpNatLe (firstValue + 1) secondValue = true ->
    zxpNatCompare firstValue secondValue = ZxpOrder.isLt
  | _firstValue, 0, hLe => Bool.noConfusion hLe
  | 0, _secondPred + 1, _hLe => rfl
  | firstPred + 1, secondPred + 1, hLe => zxpNatCompareLtOfLeSucc firstPred secondPred hLe

/-- `a <= b` (Bool) from `a < b` (comparator). -/
theorem zxpNatLeOfCompareLt (firstValue secondValue : Nat)
    (hLt : zxpNatCompare firstValue secondValue = ZxpOrder.isLt) :
    zxpNatLe firstValue secondValue = true :=
  zxpNatLeTrans firstValue (firstValue + 1) secondValue
    (zxpNatLeSuccRight firstValue firstValue (zxpNatLeRefl firstValue))
    (zxpNatLeSuccOfCompareLt firstValue secondValue hLt)

/-! ## Stage 1 — the F2 row kit: dense Bool rows, xor, concatenation, take/drop, leads

Rows are dense `List Bool` of a fixed width (the width lives OUTSIDE the row, in the
`ZxpAllWidth` hypotheses and the relation arities — pitfall 1 of the commission brief: the
zero subspace is the EMPTY ROW LIST, never a nonexistent morphism, so arities must be carried
externally).  All list plumbing is fresh and cons-only: no `List.append`, no `List.find?`,
no Init lemma with a propext-dirty simp set behind it. -/

/-- The all-false row of the given width. -/
def zxpZeroRow : Nat -> List Bool
  | 0 => []
  | widthPred + 1 => false :: zxpZeroRow widthPred

/-- The all-true row of the given width (the Z/copy spider generator row). -/
def zxpAllOnesRow : Nat -> List Bool
  | 0 => []
  | widthPred + 1 => true :: zxpAllOnesRow widthPred

/-- Pointwise xor of two rows, truncating to the shorter (width discipline keeps all
operands the same length, so truncation never fires in anger). -/
def zxpRowXor : List Bool -> List Bool -> List Bool
  | [], _secondRow => []
  | _firstBit :: _firstRest, [] => []
  | firstBit :: firstRest, secondBit :: secondRest =>
      zxpXorB firstBit secondBit :: zxpRowXor firstRest secondRest

/-- Cons-only concatenation of two rows. -/
def zxpCat : List Bool -> List Bool -> List Bool
  | [], secondRow => secondRow
  | firstBit :: firstRest, secondRow => firstBit :: zxpCat firstRest secondRow

/-- First `count` bits of a row (shorter row: whatever is there). -/
def zxpTakeN : Nat -> List Bool -> List Bool
  | 0, _row => []
  | _countPred + 1, [] => []
  | countPred + 1, headBit :: restBits => headBit :: zxpTakeN countPred restBits

/-- Row without its first `count` bits. -/
def zxpDropN : Nat -> List Bool -> List Bool
  | 0, row => row
  | _countPred + 1, [] => []
  | countPred + 1, _headBit :: restBits => zxpDropN countPred restBits

/-- Bit at a position (false beyond the end). -/
def zxpGetBit : List Bool -> Nat -> Bool
  | [], _position => false
  | headBit :: _restBits, 0 => headBit
  | _headBit :: restBits, position + 1 => zxpGetBit restBits position

/-- Is every bit false? -/
def zxpAllFalse : List Bool -> Bool
  | [] => true
  | true :: _restBits => false
  | false :: restBits => zxpAllFalse restBits

/-- Position of the first true bit (the leading position), if any. -/
def zxpLead : List Bool -> Option Nat
  | [] => none
  | true :: _restBits => some 0
  | false :: restBits =>
      match zxpLead restBits with
      | none => none
      | some leadPred => some (leadPred + 1)

/-! ### Lengths -/

theorem zxpZeroRowLength : (width : Nat) -> (zxpZeroRow width).length = width
  | 0 => rfl
  | widthPred + 1 => congrArg (fun innerValue => innerValue + 1) (zxpZeroRowLength widthPred)

theorem zxpAllOnesRowLength : (width : Nat) -> (zxpAllOnesRow width).length = width
  | 0 => rfl
  | widthPred + 1 => congrArg (fun innerValue => innerValue + 1) (zxpAllOnesRowLength widthPred)

theorem zxpCatLength : (firstRow secondRow : List Bool) ->
    (zxpCat firstRow secondRow).length = firstRow.length + secondRow.length
  | [], secondRow => (Nat.zero_add secondRow.length).symm
  | firstBit :: firstRest, secondRow => by
      show (zxpCat firstRest secondRow).length + 1
        = (firstRest.length + 1) + secondRow.length
      rw [zxpCatLength firstRest secondRow, Nat.succ_add firstRest.length secondRow.length]

theorem zxpRowXorLength : (firstRow secondRow : List Bool) -> (width : Nat) ->
    firstRow.length = width -> secondRow.length = width ->
    (zxpRowXor firstRow secondRow).length = width
  | [], [], _width, hFirst, _hSecond => hFirst
  | [], secondBit :: secondRest, _width, hFirst, hSecond => by
      rw [<- hFirst] at hSecond
      exact nomatch hSecond
  | firstBit :: firstRest, [], _width, hFirst, hSecond => by
      rw [<- hSecond] at hFirst
      exact nomatch hFirst
  | firstBit :: firstRest, secondBit :: secondRest, 0, hFirst, _hSecond =>
      nomatch hFirst
  | firstBit :: firstRest, secondBit :: secondRest, widthPred + 1, hFirst, hSecond =>
      congrArg (fun innerValue => innerValue + 1)
        (zxpRowXorLength firstRest secondRest widthPred
          (Nat.succ.inj hFirst) (Nat.succ.inj hSecond))

/-! ### Take/drop exact-split algebra -/

theorem zxpTakeNCatExact : (frontRow backRow : List Bool) -> (frontWidth : Nat) ->
    frontRow.length = frontWidth -> zxpTakeN frontWidth (zxpCat frontRow backRow) = frontRow
  | [], _backRow, 0, _hLen => rfl
  | [], _backRow, _frontPred + 1, hLen => nomatch hLen
  | _frontBit :: _frontRest, _backRow, 0, hLen =>
      nomatch hLen
  | frontBit :: frontRest, backRow, frontPred + 1, hLen =>
      congrArg (fun innerRow => frontBit :: innerRow)
        (zxpTakeNCatExact frontRest backRow frontPred (Nat.succ.inj hLen))

theorem zxpDropNCatExact : (frontRow backRow : List Bool) -> (frontWidth : Nat) ->
    frontRow.length = frontWidth -> zxpDropN frontWidth (zxpCat frontRow backRow) = backRow
  | [], _backRow, 0, _hLen => rfl
  | [], _backRow, _frontPred + 1, hLen => nomatch hLen
  | _frontBit :: _frontRest, _backRow, 0, hLen =>
      nomatch hLen
  | _frontBit :: frontRest, backRow, frontPred + 1, hLen =>
      zxpDropNCatExact frontRest backRow frontPred (Nat.succ.inj hLen)

theorem zxpCatTakeDrop : (row : List Bool) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth ->
    zxpCat (zxpTakeN frontWidth row) (zxpDropN frontWidth row) = row
  | row, 0, _backWidth, _hLen => rfl
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | headBit :: restBits, frontPred + 1, backWidth, hLen => by
      show headBit :: zxpCat (zxpTakeN frontPred restBits) (zxpDropN frontPred restBits)
        = headBit :: restBits
      rw [Nat.succ_add frontPred backWidth] at hLen
      rw [zxpCatTakeDrop restBits frontPred backWidth (Nat.succ.inj hLen)]

theorem zxpTakeNLength : (row : List Bool) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth -> (zxpTakeN frontWidth row).length = frontWidth
  | _row, 0, _backWidth, _hLen => rfl
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | headBit :: restBits, frontPred + 1, backWidth, hLen => by
      show (zxpTakeN frontPred restBits).length + 1 = frontPred + 1
      rw [Nat.succ_add frontPred backWidth] at hLen
      rw [zxpTakeNLength restBits frontPred backWidth (Nat.succ.inj hLen)]

theorem zxpDropNLength : (row : List Bool) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth -> (zxpDropN frontWidth row).length = backWidth
  | _row, 0, _backWidth, hLen => by
      rw [Nat.zero_add] at hLen
      exact hLen
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | _headBit :: restBits, frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact zxpDropNLength restBits frontPred backWidth (Nat.succ.inj hLen)

/-! ### Xor algebra -/

theorem zxpRowXorComm : (firstRow secondRow : List Bool) ->
    zxpRowXor firstRow secondRow = zxpRowXor secondRow firstRow
  | [], [] => rfl
  | [], _secondBit :: _secondRest => rfl
  | _firstBit :: _firstRest, [] => rfl
  | firstBit :: firstRest, secondBit :: secondRest => by
      show zxpXorB firstBit secondBit :: zxpRowXor firstRest secondRest
        = zxpXorB secondBit firstBit :: zxpRowXor secondRest firstRest
      rw [zxpXorBComm firstBit secondBit, zxpRowXorComm firstRest secondRest]

theorem zxpRowXorAssoc : (firstRow secondRow thirdRow : List Bool) ->
    zxpRowXor (zxpRowXor firstRow secondRow) thirdRow
      = zxpRowXor firstRow (zxpRowXor secondRow thirdRow)
  | [], _secondRow, _thirdRow => rfl
  | _firstBit :: _firstRest, [], _thirdRow => rfl
  | _firstBit :: _firstRest, _secondBit :: _secondRest, [] => rfl
  | firstBit :: firstRest, secondBit :: secondRest, thirdBit :: thirdRest => by
      show zxpXorB (zxpXorB firstBit secondBit) thirdBit
          :: zxpRowXor (zxpRowXor firstRest secondRest) thirdRest
        = zxpXorB firstBit (zxpXorB secondBit thirdBit)
          :: zxpRowXor firstRest (zxpRowXor secondRest thirdRest)
      rw [zxpXorBAssoc firstBit secondBit thirdBit,
        zxpRowXorAssoc firstRest secondRest thirdRest]

theorem zxpRowXorSelf : (row : List Bool) -> zxpRowXor row row = zxpZeroRow row.length
  | [] => rfl
  | headBit :: restBits => by
      show zxpXorB headBit headBit :: zxpRowXor restBits restBits
        = false :: zxpZeroRow restBits.length
      rw [zxpXorBSelf headBit, zxpRowXorSelf restBits]

theorem zxpRowXorZeroLeft : (row : List Bool) -> (width : Nat) -> row.length = width ->
    zxpRowXor (zxpZeroRow width) row = row
  | [], 0, _hLen => rfl
  | [], _widthPred + 1, hLen => nomatch hLen
  | headBit :: restBits, 0, hLen => nomatch hLen
  | headBit :: restBits, widthPred + 1, hLen => by
      show zxpXorB false headBit :: zxpRowXor (zxpZeroRow widthPred) restBits
        = headBit :: restBits
      rw [zxpXorBFalseLeft headBit,
        zxpRowXorZeroLeft restBits widthPred (Nat.succ.inj hLen)]

theorem zxpRowXorZeroRight : (row : List Bool) -> (width : Nat) -> row.length = width ->
    zxpRowXor row (zxpZeroRow width) = row := by
  intro row width hLen
  rw [zxpRowXorComm row (zxpZeroRow width)]
  exact zxpRowXorZeroLeft row width hLen

/-- Left cancellation: `a xor (a xor b) = b` at a common width. -/
theorem zxpRowXorCancelLeft (firstRow secondRow : List Bool) (width : Nat)
    (hFirst : firstRow.length = width) (hSecond : secondRow.length = width) :
    zxpRowXor firstRow (zxpRowXor firstRow secondRow) = secondRow := by
  rw [<- zxpRowXorAssoc firstRow firstRow secondRow, zxpRowXorSelf firstRow, hFirst]
  exact zxpRowXorZeroLeft secondRow width hSecond

/-! ### Bits, all-false, and their interaction with xor / take / drop / cat -/

theorem zxpGetBitZeroRow : (width position : Nat) -> zxpGetBit (zxpZeroRow width) position = false
  | 0, 0 => rfl
  | 0, _positionPred + 1 => rfl
  | _widthPred + 1, 0 => rfl
  | widthPred + 1, positionPred + 1 => zxpGetBitZeroRow widthPred positionPred

theorem zxpGetBitXor : (firstRow secondRow : List Bool) ->
    firstRow.length = secondRow.length -> (position : Nat) ->
    zxpGetBit (zxpRowXor firstRow secondRow) position
      = zxpXorB (zxpGetBit firstRow position) (zxpGetBit secondRow position)
  | [], [], _hLen, 0 => rfl
  | [], [], _hLen, _positionPred + 1 => rfl
  | [], _secondBit :: _secondRest, hLen, _position => nomatch hLen
  | _firstBit :: _firstRest, [], hLen, _position => nomatch hLen
  | _firstBit :: _firstRest, _secondBit :: _secondRest, _hLen, 0 => rfl
  | _firstBit :: firstRest, _secondBit :: secondRest, hLen, positionPred + 1 =>
      zxpGetBitXor firstRest secondRest (Nat.succ.inj hLen) positionPred

theorem zxpAllFalseZeroRow : (width : Nat) -> zxpAllFalse (zxpZeroRow width) = true
  | 0 => rfl
  | widthPred + 1 => zxpAllFalseZeroRow widthPred

theorem zxpAllFalseToZeroRow : (row : List Bool) -> zxpAllFalse row = true ->
    row = zxpZeroRow row.length
  | [], _hAll => rfl
  | true :: _restBits, hAll => Bool.noConfusion hAll
  | false :: restBits, hAll =>
      congrArg (fun innerRow => false :: innerRow) (zxpAllFalseToZeroRow restBits hAll)

theorem zxpAllFalseXor : (firstRow secondRow : List Bool) ->
    zxpAllFalse firstRow = true -> zxpAllFalse secondRow = true ->
    zxpAllFalse (zxpRowXor firstRow secondRow) = true
  | [], _secondRow, _hFirst, _hSecond => rfl
  | _firstBit :: _firstRest, [], _hFirst, _hSecond => rfl
  | true :: _firstRest, _secondBit :: _secondRest, hFirst, _hSecond =>
      Bool.noConfusion hFirst
  | false :: _firstRest, true :: _secondRest, _hFirst, hSecond =>
      Bool.noConfusion hSecond
  | false :: firstRest, false :: secondRest, hFirst, hSecond =>
      zxpAllFalseXor firstRest secondRest hFirst hSecond

theorem zxpAllFalseGetBit : (row : List Bool) -> zxpAllFalse row = true ->
    (position : Nat) -> zxpGetBit row position = false
  | [], _hAll, 0 => rfl
  | [], _hAll, _positionPred + 1 => rfl
  | true :: _restBits, hAll, _position => Bool.noConfusion hAll
  | false :: _restBits, _hAll, 0 => rfl
  | false :: restBits, hAll, positionPred + 1 => zxpAllFalseGetBit restBits hAll positionPred

theorem zxpAllFalseTakeN : (row : List Bool) -> zxpAllFalse row = true -> (count : Nat) ->
    zxpAllFalse (zxpTakeN count row) = true
  | [], _hAll, 0 => rfl
  | [], _hAll, _countPred + 1 => rfl
  | _headBit :: _restBits, _hAll, 0 => rfl
  | true :: _restBits, hAll, _countPred + 1 => Bool.noConfusion hAll
  | false :: restBits, hAll, countPred + 1 => zxpAllFalseTakeN restBits hAll countPred

/-! ### Cat algebra -/

theorem zxpCatNilRight : (row : List Bool) -> zxpCat row [] = row
  | [] => rfl
  | headBit :: restBits =>
      congrArg (fun innerRow => headBit :: innerRow) (zxpCatNilRight restBits)

theorem zxpCatAssoc : (firstRow secondRow thirdRow : List Bool) ->
    zxpCat (zxpCat firstRow secondRow) thirdRow
      = zxpCat firstRow (zxpCat secondRow thirdRow)
  | [], _secondRow, _thirdRow => rfl
  | headBit :: restBits, secondRow, thirdRow =>
      congrArg (fun innerRow => headBit :: innerRow)
        (zxpCatAssoc restBits secondRow thirdRow)

theorem zxpCatZeroZero : (frontWidth backWidth : Nat) ->
    zxpCat (zxpZeroRow frontWidth) (zxpZeroRow backWidth)
      = zxpZeroRow (frontWidth + backWidth)
  | 0, backWidth => by rw [Nat.zero_add]; rfl
  | frontPred + 1, backWidth => by
      show false :: zxpCat (zxpZeroRow frontPred) (zxpZeroRow backWidth)
        = zxpZeroRow (frontPred + 1 + backWidth)
      rw [Nat.succ_add frontPred backWidth]
      show false :: zxpCat (zxpZeroRow frontPred) (zxpZeroRow backWidth)
        = false :: zxpZeroRow (frontPred + backWidth)
      rw [zxpCatZeroZero frontPred backWidth]

/-- Cat is injective once the first block's length is pinned. -/
theorem zxpCatInj : (firstRow secondRow thirdRow fourthRow : List Bool) ->
    firstRow.length = thirdRow.length ->
    zxpCat firstRow secondRow = zxpCat thirdRow fourthRow ->
    firstRow = thirdRow /\ secondRow = fourthRow
  | [], _secondRow, [], _fourthRow, _hLen, hCat => And.intro rfl hCat
  | [], _secondRow, _thirdBit :: _thirdRest, _fourthRow, hLen, _hCat => nomatch hLen
  | _firstBit :: _firstRest, _secondRow, [], _fourthRow, hLen, _hCat => nomatch hLen
  | firstBit :: firstRest, secondRow, thirdBit :: thirdRest, fourthRow, hLen, hCat => by
      have hHead : firstBit = thirdBit := by
        have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hCat
        exact hHeads
      have hTail : zxpCat firstRest secondRow = zxpCat thirdRest fourthRow := by
        have hTails := congrArg (fun fullRow =>
          match fullRow with
          | [] => ([] : List Bool)
          | _headBit :: tailBits => tailBits) hCat
        exact hTails
      have hRest := zxpCatInj firstRest secondRow thirdRest fourthRow
        (Nat.succ.inj hLen) hTail
      exact And.intro (by rw [hHead, hRest.left]) hRest.right

/-- Xor distributes over cat blockwise once the first blocks share a length. -/
theorem zxpRowXorCat : (firstRow secondRow thirdRow fourthRow : List Bool) ->
    firstRow.length = thirdRow.length ->
    zxpRowXor (zxpCat firstRow secondRow) (zxpCat thirdRow fourthRow)
      = zxpCat (zxpRowXor firstRow thirdRow) (zxpRowXor secondRow fourthRow)
  | [], _secondRow, [], _fourthRow, _hLen => rfl
  | [], _secondRow, _thirdBit :: _thirdRest, _fourthRow, hLen => nomatch hLen
  | _firstBit :: _firstRest, _secondRow, [], _fourthRow, hLen => nomatch hLen
  | firstBit :: firstRest, secondRow, thirdBit :: thirdRest, fourthRow, hLen => by
      show zxpXorB firstBit thirdBit
          :: zxpRowXor (zxpCat firstRest secondRow) (zxpCat thirdRest fourthRow)
        = zxpXorB firstBit thirdBit
          :: zxpCat (zxpRowXor firstRest thirdRest) (zxpRowXor secondRow fourthRow)
      rw [zxpRowXorCat firstRest secondRow thirdRest fourthRow (Nat.succ.inj hLen)]

theorem zxpTakeNXor : (count : Nat) -> (firstRow secondRow : List Bool) ->
    zxpTakeN count (zxpRowXor firstRow secondRow)
      = zxpRowXor (zxpTakeN count firstRow) (zxpTakeN count secondRow)
  | 0, _firstRow, _secondRow => rfl
  | _countPred + 1, [], _secondRow => rfl
  | _countPred + 1, _firstBit :: _firstRest, [] => rfl
  | countPred + 1, firstBit :: firstRest, secondBit :: secondRest =>
      congrArg (fun innerRow => zxpXorB firstBit secondBit :: innerRow)
        (zxpTakeNXor countPred firstRest secondRest)

theorem zxpDropNXor : (count : Nat) -> (firstRow secondRow : List Bool) ->
    zxpDropN count (zxpRowXor firstRow secondRow)
      = zxpRowXor (zxpDropN count firstRow) (zxpDropN count secondRow)
  | 0, _firstRow, _secondRow => rfl
  | countPred + 1, [], [] => rfl
  | countPred + 1, [], _secondBit :: secondRest => by
      show ([] : List Bool) = zxpRowXor [] (zxpDropN countPred secondRest)
      rfl
  | countPred + 1, _firstBit :: firstRest, [] => by
      show ([] : List Bool) = zxpRowXor (zxpDropN countPred firstRest) []
      rw [zxpRowXorComm]
      rfl
  | countPred + 1, _firstBit :: firstRest, _secondBit :: secondRest =>
      zxpDropNXor countPred firstRest secondRest

theorem zxpTakeNZeroRowExact : (frontWidth backWidth : Nat) ->
    zxpTakeN frontWidth (zxpZeroRow (frontWidth + backWidth)) = zxpZeroRow frontWidth := by
  intro frontWidth backWidth
  have hSplit : zxpZeroRow (frontWidth + backWidth)
      = zxpCat (zxpZeroRow frontWidth) (zxpZeroRow backWidth) :=
    (zxpCatZeroZero frontWidth backWidth).symm
  rw [hSplit]
  exact zxpTakeNCatExact (zxpZeroRow frontWidth) (zxpZeroRow backWidth) frontWidth
    (zxpZeroRowLength frontWidth)

theorem zxpDropNZeroRowExact : (frontWidth backWidth : Nat) ->
    zxpDropN frontWidth (zxpZeroRow (frontWidth + backWidth)) = zxpZeroRow backWidth := by
  intro frontWidth backWidth
  have hSplit : zxpZeroRow (frontWidth + backWidth)
      = zxpCat (zxpZeroRow frontWidth) (zxpZeroRow backWidth) :=
    (zxpCatZeroZero frontWidth backWidth).symm
  rw [hSplit]
  exact zxpDropNCatExact (zxpZeroRow frontWidth) (zxpZeroRow backWidth) frontWidth
    (zxpZeroRowLength frontWidth)

/-! ### Leads: the first true bit -/

/-- Inversion of `zxpLead` on a false-headed row: the tail leads, shifted by one. -/
theorem zxpLeadFalseConsSome : (restBits : List Bool) -> (leadPosition : Nat) ->
    zxpLead (false :: restBits) = some leadPosition ->
    Exists fun restLead =>
      zxpLead restBits = some restLead /\ leadPosition = restLead + 1 := by
  intro restBits leadPosition hLead
  cases hInner : zxpLead restBits with
  | none =>
      rw [show zxpLead (false :: restBits)
          = match zxpLead restBits with
            | none => none
            | some leadPred => some (leadPred + 1) from rfl, hInner] at hLead
      exact nomatch hLead
  | some innerLead =>
      rw [show zxpLead (false :: restBits)
          = match zxpLead restBits with
            | none => none
            | some leadPred => some (leadPred + 1) from rfl, hInner] at hLead
      have hReduced : some (innerLead + 1) = some leadPosition := hLead
      exact Exists.intro innerLead (And.intro rfl (Option.some.inj hReduced).symm)

/-- A false-headed row with a leading tail cannot have lead `none`. -/
theorem zxpLeadFalseConsNone : (restBits : List Bool) ->
    zxpLead (false :: restBits) = none -> zxpLead restBits = none := by
  intro restBits hLead
  cases hInner : zxpLead restBits with
  | none => rfl
  | some innerLead =>
      rw [show zxpLead (false :: restBits)
          = match zxpLead restBits with
            | none => none
            | some leadPred => some (leadPred + 1) from rfl, hInner] at hLead
      exact nomatch hLead

theorem zxpLeadBitTrue : (row : List Bool) -> (leadPosition : Nat) ->
    zxpLead row = some leadPosition -> zxpGetBit row leadPosition = true
  | [], _leadPosition, hLead => nomatch hLead
  | true :: _restBits, 0, _hLead => rfl
  | true :: _restBits, leadPred + 1, hLead => by
      have hReduced : some 0 = some (leadPred + 1) := hLead
      exact nomatch Option.some.inj hReduced
  | false :: restBits, leadPosition, hLead => by
      have hSplit := zxpLeadFalseConsSome restBits leadPosition hLead
      cases hSplit with
      | intro restLead hBoth =>
          rw [hBoth.right]
          exact zxpLeadBitTrue restBits restLead hBoth.left

theorem zxpLeadBitBelowFalse : (row : List Bool) -> (leadPosition position : Nat) ->
    zxpLead row = some leadPosition ->
    zxpNatCompare position leadPosition = ZxpOrder.isLt ->
    zxpGetBit row position = false
  | [], _leadPosition, _position, hLead, _hLt => nomatch hLead
  | true :: _restBits, leadPosition, position, hLead, hLt => by
      have hReduced : some 0 = some leadPosition := hLead
      have hZero : leadPosition = 0 := (Option.some.inj hReduced).symm
      rw [hZero] at hLt
      cases position with
      | zero => exact nomatch hLt
      | succ positionPred => exact nomatch hLt
  | false :: restBits, leadPosition, position, hLead, hLt => by
      have hSplit := zxpLeadFalseConsSome restBits leadPosition hLead
      cases hSplit with
      | intro restLead hBoth =>
          cases position with
          | zero => rfl
          | succ positionPred =>
              rw [hBoth.right] at hLt
              exact zxpLeadBitBelowFalse restBits restLead positionPred hBoth.left hLt

theorem zxpLeadNoneAllFalse : (row : List Bool) -> zxpLead row = none ->
    zxpAllFalse row = true
  | [], _hLead => rfl
  | true :: _restBits, hLead => nomatch hLead
  | false :: restBits, hLead =>
      zxpLeadNoneAllFalse restBits (zxpLeadFalseConsNone restBits hLead)

/-- Xoring two rows with the SAME lead strictly raises the lead (or kills the row). -/
theorem zxpLeadXorRaises : (firstRow secondRow : List Bool) -> (commonLead : Nat) ->
    zxpLead firstRow = some commonLead -> zxpLead secondRow = some commonLead ->
    (resultLead : Nat) -> zxpLead (zxpRowXor firstRow secondRow) = some resultLead ->
    zxpNatLe (commonLead + 1) resultLead = true
  | [], _secondRow, _commonLead, hFirst, _hSecond, _resultLead, _hResult =>
      nomatch hFirst
  | _firstBit :: _firstRest, [], _commonLead, _hFirst, hSecond, _resultLead, _hResult =>
      nomatch hSecond
  | true :: firstRest, true :: secondRest, commonLead, hFirst, _hSecond,
      resultLead, hResult => by
      have hReduced : some 0 = some commonLead := hFirst
      have hZero : commonLead = 0 := (Option.some.inj hReduced).symm
      rw [hZero]
      -- the xor has head bit false, so its lead comes from the tail shifted by one
      have hShape : zxpRowXor (true :: firstRest) (true :: secondRest)
          = false :: zxpRowXor firstRest secondRest := rfl
      rw [hShape] at hResult
      have hSplit := zxpLeadFalseConsSome (zxpRowXor firstRest secondRest) resultLead hResult
      cases hSplit with
      | intro innerLead hBoth =>
          rw [hBoth.right]
          exact zxpNatLeZeroLeft innerLead
  | true :: _firstRest, false :: secondRest, commonLead, hFirst, hSecond,
      _resultLead, _hResult => by
      have hReduced : some 0 = some commonLead := hFirst
      have hZero : commonLead = 0 := (Option.some.inj hReduced).symm
      rw [hZero] at hSecond
      have hSplit := zxpLeadFalseConsSome secondRest 0 hSecond
      cases hSplit with
      | intro restLead hBoth => exact nomatch hBoth.right
  | false :: firstRest, true :: _secondRest, commonLead, hFirst, hSecond,
      _resultLead, _hResult => by
      have hReduced : some 0 = some commonLead := hSecond
      have hZero : commonLead = 0 := (Option.some.inj hReduced).symm
      rw [hZero] at hFirst
      have hSplit := zxpLeadFalseConsSome firstRest 0 hFirst
      cases hSplit with
      | intro restLead hBoth => exact nomatch hBoth.right
  | false :: firstRest, false :: secondRest, commonLead, hFirst, hSecond,
      resultLead, hResult => by
      have hFirstSplit := zxpLeadFalseConsSome firstRest commonLead hFirst
      have hSecondSplit := zxpLeadFalseConsSome secondRest commonLead hSecond
      have hShape : zxpRowXor (false :: firstRest) (false :: secondRest)
          = false :: zxpRowXor firstRest secondRest := rfl
      rw [hShape] at hResult
      have hResultSplit :=
        zxpLeadFalseConsSome (zxpRowXor firstRest secondRest) resultLead hResult
      cases hFirstSplit with
      | intro firstInner hFirstBoth =>
          cases hSecondSplit with
          | intro secondInner hSecondBoth =>
              cases hResultSplit with
              | intro resultInner hResultBoth =>
                  have hSameInner : secondInner = firstInner := by
                    have hChain : firstInner + 1 = secondInner + 1 := by
                      rw [<- hFirstBoth.right, <- hSecondBoth.right]
                    exact (Nat.succ.inj hChain).symm
                  rw [hFirstBoth.right, hResultBoth.right]
                  show zxpNatLe (firstInner + 1) resultInner = true
                  refine zxpLeadXorRaises firstRest secondRest firstInner
                    hFirstBoth.left ?_ resultInner hResultBoth.left
                  rw [<- hSameInner]
                  exact hSecondBoth.left

/-- A row whose first `count` bits are not all false has its lead strictly below `count`. -/
theorem zxpTakeNotAllFalseLead : (row : List Bool) -> (count : Nat) ->
    zxpAllFalse (zxpTakeN count row) = false ->
    (Exists fun leadPosition =>
      zxpLead row = some leadPosition
        /\ zxpNatCompare leadPosition count = ZxpOrder.isLt)
  | _row, 0, hFalse => Bool.noConfusion hFalse
  | [], _countPred + 1, hFalse => Bool.noConfusion hFalse
  | true :: _restBits, countPred + 1, _hFalse =>
      Exists.intro 0 (And.intro rfl rfl)
  | false :: restBits, countPred + 1, hFalse => by
      have hRest := zxpTakeNotAllFalseLead restBits countPred hFalse
      cases hRest with
      | intro restLead hRestBoth =>
          refine Exists.intro (restLead + 1) (And.intro ?_ hRestBoth.right)
          show (match zxpLead restBits with
            | none => none
            | some leadPred => some (leadPred + 1)) = some (restLead + 1)
          rw [hRestBoth.left]

/-- If the first `count` bits are all false, every bit strictly below `count` is false. -/
theorem zxpAllFalseTakeGetBit : (row : List Bool) -> (count position : Nat) ->
    zxpAllFalse (zxpTakeN count row) = true ->
    zxpNatCompare position count = ZxpOrder.isLt ->
    zxpGetBit row position = false
  | _row, 0, 0, _hAll, hLt => ZxpOrder.noConfusion hLt
  | _row, 0, _positionPred + 1, _hAll, hLt => ZxpOrder.noConfusion hLt
  | [], _countPred + 1, 0, _hAll, _hLt => rfl
  | [], _countPred + 1, _positionPred + 1, _hAll, _hLt => rfl
  | true :: _restBits, _countPred + 1, _position, hAll, _hLt => Bool.noConfusion hAll
  | false :: _restBits, _countPred + 1, 0, _hAll, _hLt => rfl
  | false :: restBits, countPred + 1, positionPred + 1, hAll, hLt =>
      zxpAllFalseTakeGetBit restBits countPred positionPred hAll hLt

/-- Two rows xoring to zero at a shared width are equal. -/
theorem zxpRowXorEqZeroImpliesEq (firstRow secondRow : List Bool) (width : Nat)
    (hFirst : firstRow.length = width) (hSecond : secondRow.length = width)
    (hZero : zxpRowXor firstRow secondRow = zxpZeroRow width) : firstRow = secondRow := by
  have hStep : zxpRowXor secondRow (zxpRowXor firstRow secondRow) = firstRow := by
    rw [zxpRowXorComm firstRow secondRow]
    exact zxpRowXorCancelLeft secondRow firstRow width hSecond hFirst
  rw [hZero] at hStep
  rw [zxpRowXorZeroRight secondRow width hSecond] at hStep
  exact hStep.symm

/-! ## Stage 2 — spans: membership in the xor-closure of a generator list

`ZxpMemSpan width rows` is the inductive xor-closure of the rows (the F2 span).  The width
index pins the zero vector; `ZxpAllWidth` hypotheses keep every operand at the shared width
so the truncating xor never bites. -/

/-- Cons-only list membership for rows (fresh, monomorphic). -/
inductive ZxpRowMem : List Bool -> List (List Bool) -> Prop where
  | head (row : List Bool) (restRows : List (List Bool)) : ZxpRowMem row (row :: restRows)
  | tail {row otherRow : List Bool} {restRows : List (List Bool)}
      (hRest : ZxpRowMem row restRows) : ZxpRowMem row (otherRow :: restRows)

/-- Every row of the list has the given width. -/
inductive ZxpAllWidth (width : Nat) : List (List Bool) -> Prop where
  | nil : ZxpAllWidth width []
  | cons {headRow : List Bool} {restRows : List (List Bool)}
      (hHead : headRow.length = width) (hRest : ZxpAllWidth width restRows) :
      ZxpAllWidth width (headRow :: restRows)

/-- Membership in the F2 span of a generator list: the zero row, closed under xor with
generators. -/
inductive ZxpMemSpan (width : Nat) (rows : List (List Bool)) : List Bool -> Prop where
  | zero : ZxpMemSpan width rows (zxpZeroRow width)
  | pick {vector : List Bool} (row : List Bool) (hRow : ZxpRowMem row rows)
      (hVec : ZxpMemSpan width rows vector) : ZxpMemSpan width rows (zxpRowXor row vector)

theorem zxpAllWidthRow {width : Nat} {rows : List (List Bool)} {row : List Bool}
    (hAll : ZxpAllWidth width rows) (hRow : ZxpRowMem row rows) : row.length = width := by
  revert hRow
  induction hAll with
  | nil =>
      intro hRow
      exact nomatch hRow
  | cons hHead _hRest innerCovers =>
      intro hRow
      cases hRow with
      | head => exact hHead
      | tail hMemRest => exact innerCovers hMemRest

theorem zxpMemSpanWidth {width : Nat} {rows : List (List Bool)} {vector : List Bool}
    (hAll : ZxpAllWidth width rows) (hMem : ZxpMemSpan width rows vector) :
    vector.length = width := by
  induction hMem with
  | zero => exact zxpZeroRowLength width
  | pick row hRow _hVec innerWidth =>
      exact zxpRowXorLength row _ width (zxpAllWidthRow hAll hRow) innerWidth

theorem zxpMemSpanWeaken {width : Nat} {rows : List (List Bool)} {vector : List Bool}
    (extraRow : List Bool) (hMem : ZxpMemSpan width rows vector) :
    ZxpMemSpan width (extraRow :: rows) vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact ZxpMemSpan.pick row (ZxpRowMem.tail hRow) innerMem

/-- Every generator row belongs to its own span. -/
theorem zxpMemSpanElem {width : Nat} {rows : List (List Bool)} {row : List Bool}
    (hAll : ZxpAllWidth width rows) (hRow : ZxpRowMem row rows) :
    ZxpMemSpan width rows row := by
  have hPicked := ZxpMemSpan.pick row hRow (ZxpMemSpan.zero (width := width) (rows := rows))
  rw [zxpRowXorZeroRight row width (zxpAllWidthRow hAll hRow)] at hPicked
  exact hPicked

/-- Spans are closed under xor. -/
theorem zxpMemSpanXorClosed {width : Nat} {rows : List (List Bool)}
    {firstVec secondVec : List Bool} (hAll : ZxpAllWidth width rows)
    (hFirst : ZxpMemSpan width rows firstVec) (hSecond : ZxpMemSpan width rows secondVec) :
    ZxpMemSpan width rows (zxpRowXor firstVec secondVec) := by
  induction hFirst with
  | zero =>
      rw [zxpRowXorZeroLeft secondVec width (zxpMemSpanWidth hAll hSecond)]
      exact hSecond
  | pick row hRow _hVec innerMem =>
      rw [zxpRowXorAssoc]
      exact ZxpMemSpan.pick row hRow innerMem

/-- Substitution: if every generator of the source lies in the target span, the whole
source span does. -/
theorem zxpMemSpanSub {width : Nat} {sourceRows targetRows : List (List Bool)}
    (hTargetAll : ZxpAllWidth width targetRows)
    (hCover : (row : List Bool) -> ZxpRowMem row sourceRows ->
      ZxpMemSpan width targetRows row)
    {vector : List Bool} (hMem : ZxpMemSpan width sourceRows vector) :
    ZxpMemSpan width targetRows vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact zxpMemSpanXorClosed hTargetAll (hCover row hRow) innerMem

/-- The span of no generators is exactly the zero row. -/
theorem zxpMemSpanNilInv {width : Nat} {vector : List Bool}
    (hMem : ZxpMemSpan width [] vector) : vector = zxpZeroRow width := by
  induction hMem with
  | zero => rfl
  | pick row hRow _hVec _innerEq => exact nomatch hRow

/-- Inversion at a cons: a span member either avoids the head generator or splits off one
copy of it. -/
theorem zxpMemSpanConsInv {width : Nat} {headRow : List Bool} {restRows : List (List Bool)}
    (hAll : ZxpAllWidth width (headRow :: restRows)) {vector : List Bool}
    (hMem : ZxpMemSpan width (headRow :: restRows) vector) :
    ZxpMemSpan width restRows vector \/
      Exists fun partner =>
        ZxpMemSpan width restRows partner /\ vector = zxpRowXor headRow partner := by
  have hHeadLen : headRow.length = width := by
    cases hAll with
    | cons hHead _hRest => exact hHead
  have hRestAll : ZxpAllWidth width restRows := by
    cases hAll with
    | cons _hHead hRest => exact hRest
  induction hMem with
  | zero => exact Or.inl ZxpMemSpan.zero
  | pick row hRow hVec innerSplit =>
      cases hRow with
      | head =>
          cases innerSplit with
          | inl hInRest =>
              exact Or.inr (Exists.intro _ (And.intro hInRest rfl))
          | inr hSplit =>
              cases hSplit with
              | intro partner hBoth =>
                  refine Or.inl ?_
                  rw [hBoth.right, zxpRowXorCancelLeft headRow partner width hHeadLen
                    (zxpMemSpanWidth hRestAll hBoth.left)]
                  exact hBoth.left
      | tail hRowRest =>
          cases innerSplit with
          | inl hInRest =>
              exact Or.inl (ZxpMemSpan.pick row hRowRest hInRest)
          | inr hSplit =>
              cases hSplit with
              | intro partner hBoth =>
                  refine Or.inr (Exists.intro (zxpRowXor row partner) (And.intro
                    (ZxpMemSpan.pick row hRowRest hBoth.left) ?_))
                  rw [hBoth.right, <- zxpRowXorAssoc row headRow partner,
                    zxpRowXorComm row headRow, zxpRowXorAssoc headRow row partner]

/-- A bit position at which every generator vanishes also vanishes on the span. -/
theorem zxpMemSpanBitFalse {width : Nat} {rows : List (List Bool)} (position : Nat)
    (hAll : ZxpAllWidth width rows)
    (hRowsBit : (row : List Bool) -> ZxpRowMem row rows -> zxpGetBit row position = false)
    {vector : List Bool} (hMem : ZxpMemSpan width rows vector) :
    zxpGetBit vector position = false := by
  induction hMem with
  | zero => exact zxpGetBitZeroRow width position
  | pick row hRow hVec innerBit =>
      rw [zxpGetBitXor row _ (by
        rw [zxpAllWidthRow hAll hRow, zxpMemSpanWidth hAll hVec]) position,
        hRowsBit row hRow, innerBit]
      rfl

/-- An all-false leading block on every generator survives onto the span. -/
theorem zxpMemSpanTakeAllFalse {width : Nat} {rows : List (List Bool)} (blockWidth : Nat)
    (hRowsTake : (row : List Bool) -> ZxpRowMem row rows ->
      zxpAllFalse (zxpTakeN blockWidth row) = true)
    {vector : List Bool} (hMem : ZxpMemSpan width rows vector) :
    zxpAllFalse (zxpTakeN blockWidth vector) = true := by
  induction hMem with
  | zero => exact zxpAllFalseTakeN (zxpZeroRow width) (zxpAllFalseZeroRow width) blockWidth
  | pick row hRow _hVec innerTake =>
      rw [zxpTakeNXor blockWidth row _]
      exact zxpAllFalseXor _ _ (hRowsTake row hRow) innerTake

/-! ## Stage 3 — echelonization by sorted insertion, reduction, and THE SPAN DECISION

Design decision (documented per the commission's fallback clause): the CANONICAL span
decision is MUTUAL REDUCTION (`zxpSpanLeB` twice), whose soundness/completeness need only
the row-ECHELON invariant (strictly increasing leads), not full reducedness.  `zxpRref`
(echelonize + back-substitution) is still provided with its row-space preservation theorem
`zxpRrefSpansSame`; the syntactic-uniqueness theorem for RREF is NOT shipped — the
statement is recorded owner-false as `zxpRrefUniquenessStatement` below. -/

/-- The rows are in echelon form with all leads at or above the bound: strictly increasing
leads, no zero rows. -/
inductive ZxpEchelonFrom : Nat -> List (List Bool) -> Prop where
  | nil (lowerBound : Nat) : ZxpEchelonFrom lowerBound []
  | cons {lowerBound : Nat} {headRow : List Bool} {restRows : List (List Bool)}
      (headLead : Nat) (hLead : zxpLead headRow = some headLead)
      (hBound : zxpNatLe lowerBound headLead = true)
      (hRest : ZxpEchelonFrom (headLead + 1) restRows) :
      ZxpEchelonFrom lowerBound (headRow :: restRows)

theorem zxpEchelonFromMono {tightBound : Nat} {rows : List (List Bool)} (looseBound : Nat)
    (hLe : zxpNatLe looseBound tightBound = true) (hEch : ZxpEchelonFrom tightBound rows) :
    ZxpEchelonFrom looseBound rows := by
  cases hEch with
  | nil => exact ZxpEchelonFrom.nil looseBound
  | cons headLead hLead hBound hRest =>
      exact ZxpEchelonFrom.cons headLead hLead
        (zxpNatLeTrans looseBound tightBound headLead hLe hBound) hRest

theorem zxpEchelonFromRowLead : (rows : List (List Bool)) -> (lowerBound : Nat) ->
    (row : List Bool) -> ZxpEchelonFrom lowerBound rows -> ZxpRowMem row rows ->
    Exists fun rowLead =>
      zxpLead row = some rowLead /\ zxpNatLe lowerBound rowLead = true
  | [], _lowerBound, _row, _hEch, hRow => nomatch hRow
  | _headRow :: restRows, lowerBound, row, hEch, hRow => by
      cases hEch with
      | cons headLead hLead hBound hRest =>
          cases hRow with
          | head => exact Exists.intro headLead (And.intro hLead hBound)
          | tail hRowRest =>
              have hFromRest :=
                zxpEchelonFromRowLead restRows (headLead + 1) row hRest hRowRest
              cases hFromRest with
              | intro rowLead hBoth =>
                  refine Exists.intro rowLead (And.intro hBoth.left ?_)
                  exact zxpNatLeTrans lowerBound (headLead + 1) rowLead
                    (zxpNatLeTrans lowerBound headLead (headLead + 1) hBound
                      (zxpNatLeSuccRight headLead headLead (zxpNatLeRefl headLead)))
                    hBoth.right

/-- Rows in echelon form strictly above a bound all vanish at the bound position. -/
theorem zxpEchelonRowsBitFalse {boundPosition : Nat} {rows : List (List Bool)}
    (hEch : ZxpEchelonFrom (boundPosition + 1) rows) (row : List Bool)
    (hRow : ZxpRowMem row rows) : zxpGetBit row boundPosition = false := by
  have hLeadInfo := zxpEchelonFromRowLead rows (boundPosition + 1) row hEch hRow
  cases hLeadInfo with
  | intro rowLead hBoth =>
      exact zxpLeadBitBelowFalse row rowLead boundPosition hBoth.left
        (zxpNatCompareLtOfLeSucc boundPosition rowLead hBoth.right)


/-- One xor-basis insertion step: the vector walks down the echelon list; equal leads xor
and re-insert (the xor's lead is recomputed by the recursive call itself, so a dead xor is
silently dropped), keeping the list echelon and the span extended by exactly the inserted
vector.  All-false vectors are no-ops. -/
def zxpInsertRow : List Bool -> List (List Bool) -> List (List Bool)
  | vectorToInsert, [] =>
      match zxpLead vectorToInsert with
      | none => []
      | some _insertLead => vectorToInsert :: []
  | vectorToInsert, headRow :: restRows =>
      match zxpLead vectorToInsert, zxpLead headRow with
      | none, _headLeadOpt => headRow :: restRows
      | some _insertLead, none => vectorToInsert :: headRow :: restRows
      | some insertLead, some headLead =>
          match zxpNatCompare insertLead headLead with
          | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
          | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
          | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows

/-! Unfolding equations for `zxpInsertRow` (proved once by scrutinee rewriting, consumed by
`rw` everywhere else — the nested-match reduction dance is quarantined here). -/

theorem zxpInsertRowNilNone (vectorToInsert : List Bool)
    (hLeadV : zxpLead vectorToInsert = none) : zxpInsertRow vectorToInsert [] = [] := by
  show (match zxpLead vectorToInsert with
    | none => []
    | some _insertLead => vectorToInsert :: []) = []
  rw [hLeadV]

theorem zxpInsertRowNilSome (vectorToInsert : List Bool) (insertLead : Nat)
    (hLeadV : zxpLead vectorToInsert = some insertLead) :
    zxpInsertRow vectorToInsert [] = vectorToInsert :: [] := by
  show (match zxpLead vectorToInsert with
    | none => []
    | some _insertLead => vectorToInsert :: []) = vectorToInsert :: []
  rw [hLeadV]

theorem zxpInsertRowConsVecNone (vectorToInsert headRow : List Bool)
    (restRows : List (List Bool)) (hLeadV : zxpLead vectorToInsert = none) :
    zxpInsertRow vectorToInsert (headRow :: restRows) = headRow :: restRows := by
  show (match zxpLead vectorToInsert, zxpLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLead, some headLead =>
        match zxpNatCompare insertLead headLead with
        | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
        | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
        | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = headRow :: restRows
  rw [hLeadV]

theorem zxpInsertRowConsHeadNone (vectorToInsert headRow : List Bool)
    (restRows : List (List Bool)) (insertLead : Nat)
    (hLeadV : zxpLead vectorToInsert = some insertLead) (hLeadH : zxpLead headRow = none) :
    zxpInsertRow vectorToInsert (headRow :: restRows)
      = vectorToInsert :: headRow :: restRows := by
  show (match zxpLead vectorToInsert, zxpLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLead, some headLead =>
        match zxpNatCompare insertLead headLead with
        | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
        | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
        | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hLeadV, hLeadH]

theorem zxpInsertRowConsLt (vectorToInsert headRow : List Bool)
    (restRows : List (List Bool)) (insertLead headLead : Nat)
    (hLeadV : zxpLead vectorToInsert = some insertLead)
    (hLeadH : zxpLead headRow = some headLead)
    (hCompare : zxpNatCompare insertLead headLead = ZxpOrder.isLt) :
    zxpInsertRow vectorToInsert (headRow :: restRows)
      = vectorToInsert :: headRow :: restRows := by
  show (match zxpLead vectorToInsert, zxpLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match zxpNatCompare insertLeadInner headLeadInner with
        | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
        | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
        | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hLeadV, hLeadH]
  show (match zxpNatCompare insertLead headLead with
    | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
    | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
    | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hCompare]

theorem zxpInsertRowConsEq (vectorToInsert headRow : List Bool)
    (restRows : List (List Bool)) (insertLead headLead : Nat)
    (hLeadV : zxpLead vectorToInsert = some insertLead)
    (hLeadH : zxpLead headRow = some headLead)
    (hCompare : zxpNatCompare insertLead headLead = ZxpOrder.isEq) :
    zxpInsertRow vectorToInsert (headRow :: restRows)
      = headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows := by
  show (match zxpLead vectorToInsert, zxpLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match zxpNatCompare insertLeadInner headLeadInner with
        | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
        | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
        | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
  rw [hLeadV, hLeadH]
  show (match zxpNatCompare insertLead headLead with
    | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
    | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
    | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
  rw [hCompare]

theorem zxpInsertRowConsGt (vectorToInsert headRow : List Bool)
    (restRows : List (List Bool)) (insertLead headLead : Nat)
    (hLeadV : zxpLead vectorToInsert = some insertLead)
    (hLeadH : zxpLead headRow = some headLead)
    (hCompare : zxpNatCompare insertLead headLead = ZxpOrder.isGt) :
    zxpInsertRow vectorToInsert (headRow :: restRows)
      = headRow :: zxpInsertRow vectorToInsert restRows := by
  show (match zxpLead vectorToInsert, zxpLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match zxpNatCompare insertLeadInner headLeadInner with
        | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
        | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
        | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = headRow :: zxpInsertRow vectorToInsert restRows
  rw [hLeadV, hLeadH]
  show (match zxpNatCompare insertLead headLead with
    | ZxpOrder.isLt => vectorToInsert :: headRow :: restRows
    | ZxpOrder.isEq => headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows
    | ZxpOrder.isGt => headRow :: zxpInsertRow vectorToInsert restRows)
    = headRow :: zxpInsertRow vectorToInsert restRows
  rw [hCompare]

/-- Gaussian echelonization over F2 by repeated insertion. -/
def zxpEchelonize : List (List Bool) -> List (List Bool)
  | [] => []
  | headRow :: restRows => zxpInsertRow headRow (zxpEchelonize restRows)

/-- An all-false vector of a pinned width IS the zero row. -/
theorem zxpLeadNoneToZeroRow {width : Nat} (vector : List Bool)
    (hLen : vector.length = width) (hLead : zxpLead vector = none) :
    vector = zxpZeroRow width := by
  have hToZero := zxpAllFalseToZeroRow vector (zxpLeadNoneAllFalse vector hLead)
  rw [hLen] at hToZero
  exact hToZero

theorem zxpInsertRowWidth {width : Nat} : (rows : List (List Bool)) ->
    (vectorToInsert : List Bool) -> vectorToInsert.length = width ->
    ZxpAllWidth width rows -> ZxpAllWidth width (zxpInsertRow vectorToInsert rows)
  | [], vectorToInsert, hVecLen, _hAll => by
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowNilNone vectorToInsert hLeadV]
          exact ZxpAllWidth.nil
      | some insertLead =>
          rw [zxpInsertRowNilSome vectorToInsert insertLead hLeadV]
          exact ZxpAllWidth.cons hVecLen ZxpAllWidth.nil
  | headRow :: restRows, vectorToInsert, hVecLen, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
          exact hAll
      | some insertLead =>
          cases hLeadH : zxpLead headRow with
          | none =>
              rw [zxpInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH]
              exact ZxpAllWidth.cons hVecLen hAll
          | some headLead =>
              cases hCompare : zxpNatCompare insertLead headLead with
              | isLt =>
                  rw [zxpInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact ZxpAllWidth.cons hVecLen hAll
              | isEq =>
                  rw [zxpInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact ZxpAllWidth.cons hHead
                    (zxpInsertRowWidth restRows (zxpRowXor vectorToInsert headRow)
                      (zxpRowXorLength vectorToInsert headRow width hVecLen hHead) hRestAll)
              | isGt =>
                  rw [zxpInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact ZxpAllWidth.cons hHead
                    (zxpInsertRowWidth restRows vectorToInsert hVecLen hRestAll)

theorem zxpEchelonizeWidth {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> ZxpAllWidth width (zxpEchelonize rows)
  | [], _hAll => ZxpAllWidth.nil
  | headRow :: restRows, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      exact zxpInsertRowWidth (zxpEchelonize restRows) headRow hHead
        (zxpEchelonizeWidth restRows hRestAll)

/-- Comparator flip: `a > b` means `b < a`. -/
theorem zxpNatCompareGtFlip : (firstValue secondValue : Nat) ->
    zxpNatCompare firstValue secondValue = ZxpOrder.isGt ->
    zxpNatCompare secondValue firstValue = ZxpOrder.isLt
  | 0, 0, hGt => ZxpOrder.noConfusion hGt
  | 0, _secondPred + 1, hGt => ZxpOrder.noConfusion hGt
  | _firstPred + 1, 0, _hGt => rfl
  | firstPred + 1, secondPred + 1, hGt => zxpNatCompareGtFlip firstPred secondPred hGt

/-- Insertion preserves the echelon invariant (any lead of the vector honours the bound). -/
theorem zxpInsertRowEchelonFrom : (rows : List (List Bool)) ->
    (vectorToInsert : List Bool) -> (lowerBound : Nat) ->
    ((insertLead : Nat) -> zxpLead vectorToInsert = some insertLead ->
      zxpNatLe lowerBound insertLead = true) ->
    ZxpEchelonFrom lowerBound rows ->
    ZxpEchelonFrom lowerBound (zxpInsertRow vectorToInsert rows)
  | [], vectorToInsert, lowerBound, hBoundOf, _hEch => by
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowNilNone vectorToInsert hLeadV]
          exact ZxpEchelonFrom.nil lowerBound
      | some insertLead =>
          rw [zxpInsertRowNilSome vectorToInsert insertLead hLeadV]
          exact ZxpEchelonFrom.cons insertLead hLeadV (hBoundOf insertLead hLeadV)
            (ZxpEchelonFrom.nil (insertLead + 1))
  | headRow :: restRows, vectorToInsert, lowerBound, hBoundOf, hEch => by
      cases hEch with
      | cons headLead hLeadH hHeadBound hRest =>
          cases hLeadV : zxpLead vectorToInsert with
          | none =>
              rw [zxpInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
              exact ZxpEchelonFrom.cons headLead hLeadH hHeadBound hRest
          | some insertLead =>
              cases hCompare : zxpNatCompare insertLead headLead with
              | isLt =>
                  rw [zxpInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact ZxpEchelonFrom.cons insertLead hLeadV (hBoundOf insertLead hLeadV)
                    (ZxpEchelonFrom.cons headLead hLeadH
                      (zxpNatLeSuccOfCompareLt insertLead headLead hCompare) hRest)
              | isEq =>
                  rw [zxpInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hSameLead : insertLead = headLead :=
                    zxpNatCompareEqImpliesEq insertLead headLead hCompare
                  refine ZxpEchelonFrom.cons headLead hLeadH hHeadBound ?_
                  refine zxpInsertRowEchelonFrom restRows (zxpRowXor vectorToInsert headRow)
                    (headLead + 1) ?_ hRest
                  intro nextLead hNextLead
                  have hRaise := zxpLeadXorRaises vectorToInsert headRow insertLead hLeadV
                    (by rw [hSameLead]; exact hLeadH) nextLead hNextLead
                  rw [<- hSameLead]
                  exact hRaise
              | isGt =>
                  rw [zxpInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  refine ZxpEchelonFrom.cons headLead hLeadH hHeadBound ?_
                  refine zxpInsertRowEchelonFrom restRows vectorToInsert (headLead + 1)
                    ?_ hRest
                  intro otherLead hOtherLead
                  have hSame : otherLead = insertLead := by
                    rw [hLeadV] at hOtherLead
                    exact (Option.some.inj hOtherLead).symm
                  rw [hSame]
                  exact zxpNatLeSuccOfCompareLt headLead insertLead
                    (zxpNatCompareGtFlip insertLead headLead hCompare)

theorem zxpEchelonizeEchelon : (rows : List (List Bool)) ->
    ZxpEchelonFrom 0 (zxpEchelonize rows)
  | [] => ZxpEchelonFrom.nil 0
  | headRow :: restRows =>
      zxpInsertRowEchelonFrom (zxpEchelonize restRows) headRow 0
        (fun insertLead _hLead => zxpNatLeZeroLeft insertLead)
        (zxpEchelonizeEchelon restRows)

/-- Every row of the inserted list lies in the span of the vector plus the old rows. -/
theorem zxpInsertRowRowsCovered {width : Nat} : (rows : List (List Bool)) ->
    (vectorToInsert : List Bool) -> vectorToInsert.length = width ->
    ZxpAllWidth width rows ->
    (row : List Bool) -> ZxpRowMem row (zxpInsertRow vectorToInsert rows) ->
    ZxpMemSpan width (vectorToInsert :: rows) row
  | [], vectorToInsert, hVecLen, _hAll, row, hRow => by
      have hFullAll : ZxpAllWidth width (vectorToInsert :: ([] : List (List Bool))) :=
        ZxpAllWidth.cons hVecLen ZxpAllWidth.nil
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowNilNone vectorToInsert hLeadV] at hRow
          exact nomatch hRow
      | some insertLead =>
          rw [zxpInsertRowNilSome vectorToInsert insertLead hLeadV] at hRow
          cases hRow with
          | head => exact zxpMemSpanElem hFullAll (ZxpRowMem.head vectorToInsert [])
          | tail hRowRest => exact nomatch hRowRest
  | headRow :: restRows, vectorToInsert, hVecLen, hAll, row, hRow => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hFullAll : ZxpAllWidth width (vectorToInsert :: headRow :: restRows) :=
        ZxpAllWidth.cons hVecLen hAll
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowConsVecNone vectorToInsert headRow restRows hLeadV] at hRow
          exact zxpMemSpanElem hFullAll (ZxpRowMem.tail hRow)
      | some insertLead =>
          cases hLeadH : zxpLead headRow with
          | none =>
              rw [zxpInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH] at hRow
              exact zxpMemSpanElem hFullAll hRow
          | some headLead =>
              cases hCompare : zxpNatCompare insertLead headLead with
              | isLt =>
                  rw [zxpInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  exact zxpMemSpanElem hFullAll hRow
              | isEq =>
                  rw [zxpInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  cases hRow with
                  | head =>
                      exact zxpMemSpanElem hFullAll
                        (ZxpRowMem.tail (ZxpRowMem.head headRow restRows))
                  | tail hInserted =>
                      have hInner := zxpInsertRowRowsCovered restRows
                        (zxpRowXor vectorToInsert headRow)
                        (zxpRowXorLength vectorToInsert headRow width hVecLen hHead)
                        hRestAll row hInserted
                      refine zxpMemSpanSub hFullAll ?_ hInner
                      intro generatorRow hGen
                      cases hGen with
                      | head =>
                          exact zxpMemSpanXorClosed hFullAll
                            (zxpMemSpanElem hFullAll (ZxpRowMem.head _ _))
                            (zxpMemSpanElem hFullAll
                              (ZxpRowMem.tail (ZxpRowMem.head _ _)))
                      | tail hGenRest =>
                          exact zxpMemSpanElem hFullAll
                            (ZxpRowMem.tail (ZxpRowMem.tail hGenRest))
              | isGt =>
                  rw [zxpInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  cases hRow with
                  | head =>
                      exact zxpMemSpanElem hFullAll
                        (ZxpRowMem.tail (ZxpRowMem.head headRow restRows))
                  | tail hInserted =>
                      have hInner := zxpInsertRowRowsCovered restRows vectorToInsert
                        hVecLen hRestAll row hInserted
                      refine zxpMemSpanSub hFullAll ?_ hInner
                      intro generatorRow hGen
                      cases hGen with
                      | head => exact zxpMemSpanElem hFullAll (ZxpRowMem.head _ _)
                      | tail hGenRest =>
                          exact zxpMemSpanElem hFullAll
                            (ZxpRowMem.tail (ZxpRowMem.tail hGenRest))

/-- The inserted list's span covers the vector and every old row. -/
theorem zxpInsertRowSpanCovers {width : Nat} : (rows : List (List Bool)) ->
    (vectorToInsert : List Bool) -> vectorToInsert.length = width ->
    ZxpAllWidth width rows ->
    ZxpMemSpan width (zxpInsertRow vectorToInsert rows) vectorToInsert
      /\ ((row : List Bool) -> ZxpRowMem row rows ->
        ZxpMemSpan width (zxpInsertRow vectorToInsert rows) row)
  | [], vectorToInsert, hVecLen, _hAll => by
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowNilNone vectorToInsert hLeadV]
          refine And.intro ?_ ?_
          · rw [zxpLeadNoneToZeroRow vectorToInsert hVecLen hLeadV]
            exact ZxpMemSpan.zero
          · intro row hRow
            exact nomatch hRow
      | some insertLead =>
          rw [zxpInsertRowNilSome vectorToInsert insertLead hLeadV]
          refine And.intro ?_ ?_
          · exact zxpMemSpanElem (ZxpAllWidth.cons hVecLen ZxpAllWidth.nil)
              (ZxpRowMem.head _ _)
          · intro row hRow
            exact nomatch hRow
  | headRow :: restRows, vectorToInsert, hVecLen, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadV : zxpLead vectorToInsert with
      | none =>
          rw [zxpInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
          refine And.intro ?_ ?_
          · rw [zxpLeadNoneToZeroRow vectorToInsert hVecLen hLeadV]
            exact ZxpMemSpan.zero
          · intro row hRow
            exact zxpMemSpanElem hAll hRow
      | some insertLead =>
          cases hLeadH : zxpLead headRow with
          | none =>
              rw [zxpInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH]
              have hFullAll : ZxpAllWidth width (vectorToInsert :: headRow :: restRows) :=
                ZxpAllWidth.cons hVecLen hAll
              refine And.intro (zxpMemSpanElem hFullAll (ZxpRowMem.head _ _)) ?_
              intro row hRow
              exact zxpMemSpanElem hFullAll (ZxpRowMem.tail hRow)
          | some headLead =>
              cases hCompare : zxpNatCompare insertLead headLead with
              | isLt =>
                  rw [zxpInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hFullAll : ZxpAllWidth width
                      (vectorToInsert :: headRow :: restRows) :=
                    ZxpAllWidth.cons hVecLen hAll
                  refine And.intro (zxpMemSpanElem hFullAll (ZxpRowMem.head _ _)) ?_
                  intro row hRow
                  exact zxpMemSpanElem hFullAll (ZxpRowMem.tail hRow)
              | isEq =>
                  rw [zxpInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hXorLen : (zxpRowXor vectorToInsert headRow).length = width :=
                    zxpRowXorLength vectorToInsert headRow width hVecLen hHead
                  have hInner := zxpInsertRowSpanCovers restRows
                    (zxpRowXor vectorToInsert headRow) hXorLen hRestAll
                  have hResultAll : ZxpAllWidth width
                      (headRow :: zxpInsertRow (zxpRowXor vectorToInsert headRow) restRows) :=
                    ZxpAllWidth.cons hHead
                      (zxpInsertRowWidth restRows _ hXorLen hRestAll)
                  refine And.intro ?_ ?_
                  · have hVecEq : zxpRowXor headRow (zxpRowXor vectorToInsert headRow)
                        = vectorToInsert := by
                      rw [zxpRowXorComm vectorToInsert headRow]
                      exact zxpRowXorCancelLeft headRow vectorToInsert width hHead hVecLen
                    have hXorMem := zxpMemSpanWeaken headRow hInner.left
                    have hCombined := zxpMemSpanXorClosed hResultAll
                      (zxpMemSpanElem hResultAll (ZxpRowMem.head _ _)) hXorMem
                    rw [hVecEq] at hCombined
                    exact hCombined
                  · intro row hRow
                    cases hRow with
                    | head => exact zxpMemSpanElem hResultAll (ZxpRowMem.head _ _)
                    | tail hRowRest =>
                        exact zxpMemSpanWeaken headRow (hInner.right row hRowRest)
              | isGt =>
                  rw [zxpInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hInner := zxpInsertRowSpanCovers restRows vectorToInsert hVecLen
                    hRestAll
                  have hResultAll : ZxpAllWidth width
                      (headRow :: zxpInsertRow vectorToInsert restRows) :=
                    ZxpAllWidth.cons hHead
                      (zxpInsertRowWidth restRows vectorToInsert hVecLen hRestAll)
                  refine And.intro (zxpMemSpanWeaken headRow hInner.left) ?_
                  intro row hRow
                  cases hRow with
                  | head => exact zxpMemSpanElem hResultAll (ZxpRowMem.head _ _)
                  | tail hRowRest =>
                      exact zxpMemSpanWeaken headRow (hInner.right row hRowRest)

/-- Echelonization does not grow the span. -/
theorem zxpEchelonizeSpanSub1 {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> {vector : List Bool} ->
    ZxpMemSpan width (zxpEchelonize rows) vector -> ZxpMemSpan width rows vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      refine zxpMemSpanSub hAll ?_ hMem
      intro row hRow
      have hViaInsert := zxpInsertRowRowsCovered (zxpEchelonize restRows) headRow hHead
        (zxpEchelonizeWidth restRows hRestAll) row hRow
      refine zxpMemSpanSub hAll ?_ hViaInsert
      intro generatorRow hGen
      cases hGen with
      | head => exact zxpMemSpanElem hAll (ZxpRowMem.head _ _)
      | tail hGenEch =>
          have hInRest := zxpEchelonizeSpanSub1 restRows hRestAll
            (zxpMemSpanElem (zxpEchelonizeWidth restRows hRestAll) hGenEch)
          exact zxpMemSpanWeaken headRow hInRest

/-- Echelonization does not shrink the span. -/
theorem zxpEchelonizeSpanSub2 {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> {vector : List Bool} ->
    ZxpMemSpan width rows vector -> ZxpMemSpan width (zxpEchelonize rows) vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hEchRestAll := zxpEchelonizeWidth restRows hRestAll
      have hCovers := zxpInsertRowSpanCovers (zxpEchelonize restRows) headRow hHead hEchRestAll
      have hResultAll := zxpInsertRowWidth (zxpEchelonize restRows) headRow hHead hEchRestAll
      refine zxpMemSpanSub hResultAll ?_ hMem
      intro row hRow
      cases hRow with
      | head => exact hCovers.left
      | tail hRowRest =>
          have hInEchRest := zxpEchelonizeSpanSub2 restRows hRestAll
            (zxpMemSpanElem hRestAll hRowRest)
          refine zxpMemSpanSub hResultAll ?_ hInEchRest
          intro generatorRow hGen
          exact hCovers.right generatorRow hGen

/-! ### Reduction against an echelon list -/

/-- Reduce a vector against a row list: xor in every row whose lead position is set in the
running vector (zero-lead rows are skipped). -/
def zxpReduceAgainst : List (List Bool) -> List Bool -> List Bool
  | [], vector => vector
  | headRow :: restRows, vector =>
      match zxpLead headRow with
      | none => zxpReduceAgainst restRows vector
      | some headLead =>
          match zxpGetBit vector headLead with
          | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
          | false => zxpReduceAgainst restRows vector

theorem zxpReduceAgainstConsNone (restRows : List (List Bool)) (headRow vector : List Bool)
    (hLeadH : zxpLead headRow = none) :
    zxpReduceAgainst (headRow :: restRows) vector = zxpReduceAgainst restRows vector := by
  show (match zxpLead headRow with
    | none => zxpReduceAgainst restRows vector
    | some headLead =>
        match zxpGetBit vector headLead with
        | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
        | false => zxpReduceAgainst restRows vector) = zxpReduceAgainst restRows vector
  rw [hLeadH]

theorem zxpReduceAgainstConsTrue (restRows : List (List Bool)) (headRow vector : List Bool)
    (headLead : Nat) (hLeadH : zxpLead headRow = some headLead)
    (hBit : zxpGetBit vector headLead = true) :
    zxpReduceAgainst (headRow :: restRows) vector
      = zxpReduceAgainst restRows (zxpRowXor vector headRow) := by
  show (match zxpLead headRow with
    | none => zxpReduceAgainst restRows vector
    | some headLeadInner =>
        match zxpGetBit vector headLeadInner with
        | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
        | false => zxpReduceAgainst restRows vector)
    = zxpReduceAgainst restRows (zxpRowXor vector headRow)
  rw [hLeadH]
  show (match zxpGetBit vector headLead with
    | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
    | false => zxpReduceAgainst restRows vector)
    = zxpReduceAgainst restRows (zxpRowXor vector headRow)
  rw [hBit]

theorem zxpReduceAgainstConsFalse (restRows : List (List Bool)) (headRow vector : List Bool)
    (headLead : Nat) (hLeadH : zxpLead headRow = some headLead)
    (hBit : zxpGetBit vector headLead = false) :
    zxpReduceAgainst (headRow :: restRows) vector = zxpReduceAgainst restRows vector := by
  show (match zxpLead headRow with
    | none => zxpReduceAgainst restRows vector
    | some headLeadInner =>
        match zxpGetBit vector headLeadInner with
        | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
        | false => zxpReduceAgainst restRows vector) = zxpReduceAgainst restRows vector
  rw [hLeadH]
  show (match zxpGetBit vector headLead with
    | true => zxpReduceAgainst restRows (zxpRowXor vector headRow)
    | false => zxpReduceAgainst restRows vector) = zxpReduceAgainst restRows vector
  rw [hBit]

theorem zxpReduceAgainstWidth {width : Nat} : (rows : List (List Bool)) ->
    (vector : List Bool) -> ZxpAllWidth width rows -> vector.length = width ->
    (zxpReduceAgainst rows vector).length = width
  | [], _vector, _hAll, hVecLen => hVecLen
  | headRow :: restRows, vector, hAll, hVecLen => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadH : zxpLead headRow with
      | none =>
          rw [zxpReduceAgainstConsNone restRows headRow vector hLeadH]
          exact zxpReduceAgainstWidth restRows vector hRestAll hVecLen
      | some headLead =>
          cases hBit : zxpGetBit vector headLead with
          | true =>
              rw [zxpReduceAgainstConsTrue restRows headRow vector headLead hLeadH hBit]
              exact zxpReduceAgainstWidth restRows (zxpRowXor vector headRow) hRestAll
                (zxpRowXorLength vector headRow width hVecLen hHead)
          | false =>
              rw [zxpReduceAgainstConsFalse restRows headRow vector headLead hLeadH hBit]
              exact zxpReduceAgainstWidth restRows vector hRestAll hVecLen

/-- Reduction soundness: the vector and its reduction differ by a span member. -/
theorem zxpReduceAgainstSound {width : Nat} : (rows : List (List Bool)) ->
    (vector : List Bool) -> ZxpAllWidth width rows -> vector.length = width ->
    ZxpMemSpan width rows (zxpRowXor vector (zxpReduceAgainst rows vector))
  | [], vector, _hAll, hVecLen => by
      show ZxpMemSpan width [] (zxpRowXor vector vector)
      rw [zxpRowXorSelf vector, hVecLen]
      exact ZxpMemSpan.zero
  | headRow :: restRows, vector, hAll, hVecLen => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadH : zxpLead headRow with
      | none =>
          rw [zxpReduceAgainstConsNone restRows headRow vector hLeadH]
          exact zxpMemSpanWeaken headRow
            (zxpReduceAgainstSound restRows vector hRestAll hVecLen)
      | some headLead =>
          cases hBit : zxpGetBit vector headLead with
          | true =>
              rw [zxpReduceAgainstConsTrue restRows headRow vector headLead hLeadH hBit]
              have hXorLen : (zxpRowXor vector headRow).length = width :=
                zxpRowXorLength vector headRow width hVecLen hHead
              have hHeadCollapse : zxpRowXor headRow (zxpRowXor vector headRow)
                  = vector := by
                rw [zxpRowXorComm vector headRow]
                exact zxpRowXorCancelLeft headRow vector width hHead hVecLen
              have hInner := zxpMemSpanWeaken headRow
                (zxpReduceAgainstSound restRows (zxpRowXor vector headRow) hRestAll hXorLen)
              have hPicked := ZxpMemSpan.pick headRow
                (ZxpRowMem.head headRow restRows) hInner
              rw [<- zxpRowXorAssoc headRow (zxpRowXor vector headRow) _] at hPicked
              rw [hHeadCollapse] at hPicked
              exact hPicked
          | false =>
              rw [zxpReduceAgainstConsFalse restRows headRow vector headLead hLeadH hBit]
              exact zxpMemSpanWeaken headRow
                (zxpReduceAgainstSound restRows vector hRestAll hVecLen)

/-- A vector whose reduction is all-false lies in the span. -/
theorem zxpReduceAgainstMember {width : Nat} (rows : List (List Bool)) (vector : List Bool)
    (hAll : ZxpAllWidth width rows) (hVecLen : vector.length = width)
    (hZero : zxpAllFalse (zxpReduceAgainst rows vector) = true) :
    ZxpMemSpan width rows vector := by
  have hReducedZero : zxpReduceAgainst rows vector = zxpZeroRow width := by
    have hToZero := zxpAllFalseToZeroRow _ hZero
    rw [zxpReduceAgainstWidth rows vector hAll hVecLen] at hToZero
    exact hToZero
  have hSound := zxpReduceAgainstSound rows vector hAll hVecLen
  rw [hReducedZero, zxpRowXorZeroRight vector width hVecLen] at hSound
  exact hSound

/-- Reduction completeness against an echelon list: every span member reduces to all-false. -/
theorem zxpReduceAgainstComplete {width : Nat} : {lowerBound : Nat} ->
    (rows : List (List Bool)) -> (vector : List Bool) ->
    ZxpAllWidth width rows -> ZxpEchelonFrom lowerBound rows ->
    ZxpMemSpan width rows vector ->
    zxpAllFalse (zxpReduceAgainst rows vector) = true
  | _lowerBound, [], vector, _hAll, _hEch, hMem => by
      show zxpAllFalse vector = true
      rw [zxpMemSpanNilInv hMem]
      exact zxpAllFalseZeroRow width
  | _lowerBound, headRow :: restRows, vector, hAll, hEch, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH _hBound hRest =>
          have hRestBitsFalse : (row : List Bool) -> ZxpRowMem row restRows ->
              zxpGetBit row headLead = false := fun row hRow =>
            zxpEchelonRowsBitFalse hRest row hRow
          have hSplit := zxpMemSpanConsInv hAll hMem
          cases hSplit with
          | inl hInRest =>
              have hBitFalse : zxpGetBit vector headLead = false :=
                zxpMemSpanBitFalse headLead hRestAll hRestBitsFalse hInRest
              rw [zxpReduceAgainstConsFalse restRows headRow vector headLead hLeadH hBitFalse]
              exact zxpReduceAgainstComplete restRows vector hRestAll hRest hInRest
          | inr hSplitPair =>
              cases hSplitPair with
              | intro partner hBoth =>
                  have hPartnerLen : partner.length = width :=
                    zxpMemSpanWidth hRestAll hBoth.left
                  have hPartnerBit : zxpGetBit partner headLead = false :=
                    zxpMemSpanBitFalse headLead hRestAll hRestBitsFalse hBoth.left
                  have hBitTrue : zxpGetBit vector headLead = true := by
                    rw [hBoth.right,
                      zxpGetBitXor headRow partner (by rw [hHead, hPartnerLen]) headLead,
                      zxpLeadBitTrue headRow headLead hLeadH, hPartnerBit]
                    rfl
                  rw [zxpReduceAgainstConsTrue restRows headRow vector headLead hLeadH
                    hBitTrue]
                  have hVectorXor : zxpRowXor vector headRow = partner := by
                    rw [hBoth.right, zxpRowXorComm headRow partner,
                      zxpRowXorAssoc partner headRow headRow, zxpRowXorSelf headRow, hHead,
                      zxpRowXorZeroRight partner width hPartnerLen]
                  rw [hVectorXor]
                  exact zxpReduceAgainstComplete restRows partner hRestAll hRest hBoth.left

/-! ### The Bool span decision: mutual reduction -/

/-- Does every row of the list reduce to all-false against the echelon rows? -/
def zxpAllRowsReduceToZero (echelonRows : List (List Bool)) :
    List (List Bool) -> Bool
  | [] => true
  | headRow :: restRows =>
      match zxpAllFalse (zxpReduceAgainst echelonRows headRow) with
      | true => zxpAllRowsReduceToZero echelonRows restRows
      | false => false

theorem zxpAllRowsReduceToZeroConsTrue (echelonRows : List (List Bool))
    (headRow : List Bool) (restRows : List (List Bool))
    (hCheck : zxpAllFalse (zxpReduceAgainst echelonRows headRow) = true) :
    zxpAllRowsReduceToZero echelonRows (headRow :: restRows)
      = zxpAllRowsReduceToZero echelonRows restRows := by
  show (match zxpAllFalse (zxpReduceAgainst echelonRows headRow) with
    | true => zxpAllRowsReduceToZero echelonRows restRows
    | false => false) = zxpAllRowsReduceToZero echelonRows restRows
  rw [hCheck]

theorem zxpAllRowsReduceToZeroConsFalse (echelonRows : List (List Bool))
    (headRow : List Bool) (restRows : List (List Bool))
    (hCheck : zxpAllFalse (zxpReduceAgainst echelonRows headRow) = false) :
    zxpAllRowsReduceToZero echelonRows (headRow :: restRows) = false := by
  show (match zxpAllFalse (zxpReduceAgainst echelonRows headRow) with
    | true => zxpAllRowsReduceToZero echelonRows restRows
    | false => false) = false
  rw [hCheck]

theorem zxpAllRowsReduceToZeroSpec1 (echelonRows : List (List Bool)) :
    (rows : List (List Bool)) -> zxpAllRowsReduceToZero echelonRows rows = true ->
    (row : List Bool) -> ZxpRowMem row rows ->
    zxpAllFalse (zxpReduceAgainst echelonRows row) = true
  | [], _hAllTrue, _row, hRow => nomatch hRow
  | headRow :: restRows, hAllTrue, row, hRow => by
      cases hCheck : zxpAllFalse (zxpReduceAgainst echelonRows headRow) with
      | true =>
          rw [zxpAllRowsReduceToZeroConsTrue echelonRows headRow restRows hCheck] at hAllTrue
          cases hRow with
          | head => exact hCheck
          | tail hRowRest =>
              exact zxpAllRowsReduceToZeroSpec1 echelonRows restRows hAllTrue row hRowRest
      | false =>
          rw [zxpAllRowsReduceToZeroConsFalse echelonRows headRow restRows hCheck] at hAllTrue
          exact Bool.noConfusion hAllTrue

theorem zxpAllRowsReduceToZeroSpec2 (echelonRows : List (List Bool)) :
    (rows : List (List Bool)) ->
    ((row : List Bool) -> ZxpRowMem row rows ->
      zxpAllFalse (zxpReduceAgainst echelonRows row) = true) ->
    zxpAllRowsReduceToZero echelonRows rows = true
  | [], _hEach => rfl
  | headRow :: restRows, hEach => by
      rw [zxpAllRowsReduceToZeroConsTrue echelonRows headRow restRows
        (hEach headRow (ZxpRowMem.head headRow restRows))]
      exact zxpAllRowsReduceToZeroSpec2 echelonRows restRows
        (fun row hRow => hEach row (ZxpRowMem.tail hRow))

/-- Bool span inclusion: every generator of the first list reduces to zero against the
echelonization of the second. -/
def zxpSpanLeB (firstRows secondRows : List (List Bool)) : Bool :=
  zxpAllRowsReduceToZero (zxpEchelonize secondRows) firstRows

/-- Bool span equality: mutual inclusion. -/
def zxpSpanEqB (firstRows secondRows : List (List Bool)) : Bool :=
  match zxpSpanLeB firstRows secondRows with
  | true => zxpSpanLeB secondRows firstRows
  | false => false

theorem zxpSpanEqBOfLe (firstRows secondRows : List (List Bool))
    (hForward : zxpSpanLeB firstRows secondRows = true) :
    zxpSpanEqB firstRows secondRows = zxpSpanLeB secondRows firstRows := by
  show (match zxpSpanLeB firstRows secondRows with
    | true => zxpSpanLeB secondRows firstRows
    | false => false) = zxpSpanLeB secondRows firstRows
  rw [hForward]

theorem zxpSpanEqBOfNotLe (firstRows secondRows : List (List Bool))
    (hForward : zxpSpanLeB firstRows secondRows = false) :
    zxpSpanEqB firstRows secondRows = false := by
  show (match zxpSpanLeB firstRows secondRows with
    | true => zxpSpanLeB secondRows firstRows
    | false => false) = false
  rw [hForward]

theorem zxpSpanLeBSound {width : Nat} {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth width firstRows) (hSecondAll : ZxpAllWidth width secondRows)
    (hLe : zxpSpanLeB firstRows secondRows = true) {vector : List Bool}
    (hMem : ZxpMemSpan width firstRows vector) : ZxpMemSpan width secondRows vector := by
  refine zxpMemSpanSub hSecondAll ?_ hMem
  intro row hRow
  have hRowReduces := zxpAllRowsReduceToZeroSpec1 (zxpEchelonize secondRows) firstRows
    hLe row hRow
  have hInEch := zxpReduceAgainstMember (zxpEchelonize secondRows) row
    (zxpEchelonizeWidth secondRows hSecondAll) (zxpAllWidthRow hFirstAll hRow) hRowReduces
  exact zxpEchelonizeSpanSub1 secondRows hSecondAll hInEch

theorem zxpSpanLeBComplete {width : Nat} {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth width firstRows) (hSecondAll : ZxpAllWidth width secondRows)
    (hSub : (vector : List Bool) -> ZxpMemSpan width firstRows vector ->
      ZxpMemSpan width secondRows vector) :
    zxpSpanLeB firstRows secondRows = true := by
  refine zxpAllRowsReduceToZeroSpec2 (zxpEchelonize secondRows) firstRows ?_
  intro row hRow
  have hInSecond := hSub row (zxpMemSpanElem hFirstAll hRow)
  have hInEch := zxpEchelonizeSpanSub2 secondRows hSecondAll hInSecond
  exact zxpReduceAgainstComplete (zxpEchelonize secondRows) row
    (zxpEchelonizeWidth secondRows hSecondAll) (zxpEchelonizeEchelon secondRows) hInEch

/-- SOUNDNESS of the span-equality decision: `true` means the two spans have the same
members. -/
theorem zxpSpanEqBSound {width : Nat} {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth width firstRows) (hSecondAll : ZxpAllWidth width secondRows)
    (hEq : zxpSpanEqB firstRows secondRows = true) (vector : List Bool) :
    ZxpMemSpan width firstRows vector <-> ZxpMemSpan width secondRows vector := by
  cases hForward : zxpSpanLeB firstRows secondRows with
  | true =>
      rw [zxpSpanEqBOfLe firstRows secondRows hForward] at hEq
      exact Iff.intro
        (fun hMem => zxpSpanLeBSound hFirstAll hSecondAll hForward hMem)
        (fun hMem => zxpSpanLeBSound hSecondAll hFirstAll hEq hMem)
  | false =>
      rw [zxpSpanEqBOfNotLe firstRows secondRows hForward] at hEq
      exact Bool.noConfusion hEq

/-- COMPLETENESS of the span-equality decision: same members means the decision fires. -/
theorem zxpSpanEqBComplete {width : Nat} {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth width firstRows) (hSecondAll : ZxpAllWidth width secondRows)
    (hSame : (vector : List Bool) ->
      (ZxpMemSpan width firstRows vector <-> ZxpMemSpan width secondRows vector)) :
    zxpSpanEqB firstRows secondRows = true := by
  rw [zxpSpanEqBOfLe firstRows secondRows
    (zxpSpanLeBComplete hFirstAll hSecondAll (fun vector hMem => (hSame vector).mp hMem))]
  exact zxpSpanLeBComplete hSecondAll hFirstAll (fun vector hMem => (hSame vector).mpr hMem)

/-! ### RREF: back-substitution over the echelon list, with row-space preservation -/

/-- Back-substitution: reduce each row against the (already back-reduced) rows below it. -/
def zxpBackReduce : List (List Bool) -> List (List Bool)
  | [] => []
  | headRow :: restRows =>
      zxpReduceAgainst (zxpBackReduce restRows) headRow :: zxpBackReduce restRows

theorem zxpBackReduceWidth {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> ZxpAllWidth width (zxpBackReduce rows)
  | [], _hAll => ZxpAllWidth.nil
  | headRow :: restRows, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInner := zxpBackReduceWidth restRows hRestAll
      exact ZxpAllWidth.cons
        (zxpReduceAgainstWidth (zxpBackReduce restRows) headRow hInner hHead) hInner

theorem zxpBackReduceSpanSub1 {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> {vector : List Bool} ->
    ZxpMemSpan width (zxpBackReduce rows) vector -> ZxpMemSpan width rows vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInnerAll := zxpBackReduceWidth restRows hRestAll
      refine zxpMemSpanSub hAll ?_ hMem
      intro row hRow
      cases hRow with
      | head =>
          have hDelta := zxpReduceAgainstSound (zxpBackReduce restRows) headRow hInnerAll hHead
          have hDeltaInRest : ZxpMemSpan width restRows
              (zxpRowXor headRow (zxpReduceAgainst (zxpBackReduce restRows) headRow)) :=
            zxpBackReduceSpanSub1 restRows hRestAll hDelta
          have hCombined := zxpMemSpanXorClosed hAll
            (zxpMemSpanElem hAll (ZxpRowMem.head headRow restRows))
            (zxpMemSpanWeaken headRow hDeltaInRest)
          rw [zxpRowXorCancelLeft headRow _ width hHead
            (zxpReduceAgainstWidth (zxpBackReduce restRows) headRow hInnerAll hHead)]
            at hCombined
          exact hCombined
      | tail hRowRest =>
          have hInRest := zxpBackReduceSpanSub1 restRows hRestAll
            (zxpMemSpanElem hInnerAll hRowRest)
          exact zxpMemSpanWeaken headRow hInRest

theorem zxpBackReduceSpanSub2 {width : Nat} : (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> {vector : List Bool} ->
    ZxpMemSpan width rows vector -> ZxpMemSpan width (zxpBackReduce rows) vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInnerAll := zxpBackReduceWidth restRows hRestAll
      have hResultAll : ZxpAllWidth width (zxpBackReduce (headRow :: restRows)) :=
        zxpBackReduceWidth (headRow :: restRows) hAll
      refine zxpMemSpanSub hResultAll ?_ hMem
      intro row hRow
      cases hRow with
      | head =>
          have hDelta := zxpReduceAgainstSound (zxpBackReduce restRows) headRow hInnerAll hHead
          have hReducedHead : ZxpMemSpan width (zxpBackReduce (headRow :: restRows))
              (zxpReduceAgainst (zxpBackReduce restRows) headRow) :=
            zxpMemSpanElem hResultAll (ZxpRowMem.head _ _)
          have hDeltaWeakened : ZxpMemSpan width (zxpBackReduce (headRow :: restRows))
              (zxpRowXor headRow (zxpReduceAgainst (zxpBackReduce restRows) headRow)) :=
            zxpMemSpanWeaken _ hDelta
          have hCombined := zxpMemSpanXorClosed hResultAll hReducedHead hDeltaWeakened
          rw [zxpRowXorComm headRow _] at hCombined
          rw [zxpRowXorCancelLeft _ headRow width
            (zxpReduceAgainstWidth (zxpBackReduce restRows) headRow hInnerAll hHead) hHead]
            at hCombined
          exact hCombined
      | tail hRowRest =>
          have hInRest := zxpBackReduceSpanSub2 restRows hRestAll
            (zxpMemSpanElem hRestAll hRowRest)
          exact zxpMemSpanWeaken _ hInRest

/-- Gaussian elimination to (reduced) row echelon form: echelonize, then back-substitute.
The REDUCEDNESS of the output (pivot columns elementary) is not separately certified —
see `zxpRrefUniquenessStatement` for the honest owner-false record. -/
def zxpRref (rows : List (List Bool)) : List (List Bool) :=
  zxpBackReduce (zxpEchelonize rows)

/-- CANONICITY THEOREM (a): `zxpRref` preserves the row space. -/
theorem zxpRrefSpansSame {width : Nat} (rows : List (List Bool))
    (hAll : ZxpAllWidth width rows) (vector : List Bool) :
    ZxpMemSpan width (zxpRref rows) vector <-> ZxpMemSpan width rows vector := by
  have hEchAll := zxpEchelonizeWidth rows hAll
  exact Iff.intro
    (fun hMem => zxpEchelonizeSpanSub1 rows hAll
      (zxpBackReduceSpanSub1 (zxpEchelonize rows) hEchAll hMem))
    (fun hMem => zxpBackReduceSpanSub2 (zxpEchelonize rows) hEchAll
      (zxpEchelonizeSpanSub2 rows hAll hMem))

theorem zxpRrefWidth {width : Nat} (rows : List (List Bool))
    (hAll : ZxpAllWidth width rows) : ZxpAllWidth width (zxpRref rows) :=
  zxpBackReduceWidth (zxpEchelonize rows) (zxpEchelonizeWidth rows hAll)

/-- CANONICITY STATEMENT (b), owner FALSE: syntactic uniqueness of the reduced row echelon
form (span-equal inputs give LITERALLY equal `zxpRref` outputs; Yuster 1984 / Hoffman-Kunze
2.5).  NOT PROVEN HERE — the commissioned fallback was taken instead: the span-equality
DECISION goes through mutual reduction (`zxpSpanEqB`), whose soundness/completeness
(`zxpSpanEqBSound`/`zxpSpanEqBComplete`) serve every decision use of uniqueness.  A future
push at this statement should follow the pivot-column dimension-profile induction. -/
def zxpRrefUniquenessStatement : Prop :=
  (width : Nat) -> (firstRows secondRows : List (List Bool)) ->
  ZxpAllWidth width firstRows -> ZxpAllWidth width secondRows ->
  ((vector : List Bool) ->
    (ZxpMemSpan width firstRows vector <-> ZxpMemSpan width secondRows vector)) ->
  zxpRref firstRows = zxpRref secondRows

/-- Owner flag for the unproven RREF-uniqueness statement. -/
def zxpRrefUniquenessIsProven : Bool := false

/-! ## Stage 2b — relations: generator matrices with external arities

A morphism `n -> m` is (the span of) a generator matrix of width `n + m`, domain block
first.  The BRIEF's pitfalls are baked in: arities live OUTSIDE the rows (pitfall 1); the
composition stack puts the shared middle block LEFTMOST so the zero-middle extraction is
the leftmost-pivot argument (pitfall 4). -/

/-- Cons-only concatenation of row lists (fresh, monomorphic). -/
def zxpCatRows : List (List Bool) -> List (List Bool) -> List (List Bool)
  | [], secondRows => secondRows
  | headRow :: restRows, secondRows => headRow :: zxpCatRows restRows secondRows

/-- Cons-only map over row lists (fresh, monomorphic). -/
def zxpMapRows (transform : List Bool -> List Bool) : List (List Bool) -> List (List Bool)
  | [] => []
  | headRow :: restRows => transform headRow :: zxpMapRows transform restRows

theorem zxpCatRowsMemSplit : {row : List Bool} -> (leftRows rightRows : List (List Bool)) ->
    ZxpRowMem row (zxpCatRows leftRows rightRows) ->
    ZxpRowMem row leftRows \/ ZxpRowMem row rightRows
  | _row, [], _rightRows, hRow => Or.inr hRow
  | _row, headRow :: restRows, rightRows, hRow => by
      cases hRow with
      | head => exact Or.inl (ZxpRowMem.head _ _)
      | tail hRowRest =>
          cases zxpCatRowsMemSplit restRows rightRows hRowRest with
          | inl hInLeft => exact Or.inl (ZxpRowMem.tail hInLeft)
          | inr hInRight => exact Or.inr hInRight

theorem zxpCatRowsMemLeft {row : List Bool} : (leftRows rightRows : List (List Bool)) ->
    ZxpRowMem row leftRows -> ZxpRowMem row (zxpCatRows leftRows rightRows)
  | [], _rightRows, hRow => nomatch hRow
  | _headRow :: restRows, rightRows, hRow => by
      cases hRow with
      | head => exact ZxpRowMem.head _ _
      | tail hRowRest =>
          exact ZxpRowMem.tail (zxpCatRowsMemLeft restRows rightRows hRowRest)

theorem zxpCatRowsMemRight : {row : List Bool} -> (leftRows rightRows : List (List Bool)) ->
    ZxpRowMem row rightRows -> ZxpRowMem row (zxpCatRows leftRows rightRows)
  | _row, [], _rightRows, hRow => hRow
  | _row, _headRow :: restRows, rightRows, hRow =>
      ZxpRowMem.tail (zxpCatRowsMemRight restRows rightRows hRow)

theorem zxpCatRowsWidth {width : Nat} : (leftRows rightRows : List (List Bool)) ->
    ZxpAllWidth width leftRows -> ZxpAllWidth width rightRows ->
    ZxpAllWidth width (zxpCatRows leftRows rightRows)
  | [], _rightRows, _hLeft, hRight => hRight
  | _headRow :: restRows, rightRows, hLeft, hRight => by
      cases hLeft with
      | cons hHead hRest =>
          exact ZxpAllWidth.cons hHead (zxpCatRowsWidth restRows rightRows hRest hRight)

theorem zxpCatRowsSpanLeft {width : Nat} {leftRows rightRows : List (List Bool)}
    {vector : List Bool} (hMem : ZxpMemSpan width leftRows vector) :
    ZxpMemSpan width (zxpCatRows leftRows rightRows) vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact ZxpMemSpan.pick row (zxpCatRowsMemLeft leftRows rightRows hRow) innerMem

theorem zxpCatRowsSpanRight {width : Nat} {leftRows rightRows : List (List Bool)}
    {vector : List Bool} (hMem : ZxpMemSpan width rightRows vector) :
    ZxpMemSpan width (zxpCatRows leftRows rightRows) vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact ZxpMemSpan.pick row (zxpCatRowsMemRight leftRows rightRows hRow) innerMem

/-- A member of the concatenated span splits as an xor of one member from each side. -/
theorem zxpCatRowsSpanSplitFwd {width : Nat} {leftRows rightRows : List (List Bool)}
    (hLeftAll : ZxpAllWidth width leftRows) (hRightAll : ZxpAllWidth width rightRows)
    {vector : List Bool} (hMem : ZxpMemSpan width (zxpCatRows leftRows rightRows) vector) :
    Exists fun leftPart => Exists fun rightPart =>
      ZxpMemSpan width leftRows leftPart /\ ZxpMemSpan width rightRows rightPart
        /\ vector = zxpRowXor leftPart rightPart := by
  induction hMem with
  | zero =>
      refine Exists.intro (zxpZeroRow width) (Exists.intro (zxpZeroRow width)
        (And.intro ZxpMemSpan.zero (And.intro ZxpMemSpan.zero ?_)))
      rw [zxpRowXorSelf (zxpZeroRow width), zxpZeroRowLength width]
  | pick row hRow _hVec innerSplit =>
      cases innerSplit with
      | intro leftPart hRightPack =>
          cases hRightPack with
          | intro rightPart hParts =>
              cases zxpCatRowsMemSplit leftRows rightRows hRow with
              | inl hInLeft =>
                  refine Exists.intro (zxpRowXor row leftPart) (Exists.intro rightPart
                    (And.intro (ZxpMemSpan.pick row hInLeft hParts.left)
                      (And.intro hParts.right.left ?_)))
                  rw [hParts.right.right, <- zxpRowXorAssoc row leftPart rightPart]
              | inr hInRight =>
                  refine Exists.intro leftPart (Exists.intro (zxpRowXor row rightPart)
                    (And.intro hParts.left
                      (And.intro (ZxpMemSpan.pick row hInRight hParts.right.left) ?_)))
                  rw [hParts.right.right, <- zxpRowXorAssoc row leftPart rightPart,
                    zxpRowXorComm row leftPart, zxpRowXorAssoc leftPart row rightPart]

theorem zxpMapRowsMemInv (transform : List Bool -> List Bool) :
    {mappedRow : List Bool} -> (rows : List (List Bool)) ->
    ZxpRowMem mappedRow (zxpMapRows transform rows) ->
    Exists fun sourceRow => ZxpRowMem sourceRow rows /\ mappedRow = transform sourceRow
  | _mappedRow, [], hRow => nomatch hRow
  | _mappedRow, headRow :: restRows, hRow => by
      cases hRow with
      | head =>
          exact Exists.intro headRow
            (And.intro (ZxpRowMem.head headRow restRows) rfl)
      | tail hRowRest =>
          have hInner := zxpMapRowsMemInv transform restRows hRowRest
          cases hInner with
          | intro sourceRow hBoth =>
              exact Exists.intro sourceRow (And.intro (ZxpRowMem.tail hBoth.left) hBoth.right)

theorem zxpMapRowsMemIntro (transform : List Bool -> List Bool) {sourceRow : List Bool} :
    (rows : List (List Bool)) -> ZxpRowMem sourceRow rows ->
    ZxpRowMem (transform sourceRow) (zxpMapRows transform rows)
  | [], hRow => nomatch hRow
  | _headRow :: restRows, hRow => by
      cases hRow with
      | head => exact ZxpRowMem.head _ _
      | tail hRowRest =>
          exact ZxpRowMem.tail (zxpMapRowsMemIntro transform restRows hRowRest)

theorem zxpMapRowsWidth {sourceWidth targetWidth : Nat}
    (transform : List Bool -> List Bool)
    (hTransformLen : (row : List Bool) -> row.length = sourceWidth ->
      (transform row).length = targetWidth) :
    (rows : List (List Bool)) -> ZxpAllWidth sourceWidth rows ->
    ZxpAllWidth targetWidth (zxpMapRows transform rows)
  | [], _hAll => ZxpAllWidth.nil
  | headRow :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          exact ZxpAllWidth.cons (hTransformLen headRow hHead)
            (zxpMapRowsWidth transform hTransformLen restRows hRest)

/-- Span of a linearly-mapped generator list, forward: every member is the image of a
member. -/
theorem zxpMapRowsSpanFwd {sourceWidth targetWidth : Nat}
    (transform : List Bool -> List Bool)
    (hTransformZero : transform (zxpZeroRow sourceWidth) = zxpZeroRow targetWidth)
    (hTransformXor : (firstRow secondRow : List Bool) -> firstRow.length = sourceWidth ->
      secondRow.length = sourceWidth ->
      transform (zxpRowXor firstRow secondRow)
        = zxpRowXor (transform firstRow) (transform secondRow))
    {rows : List (List Bool)} (hAll : ZxpAllWidth sourceWidth rows)
    {mappedVector : List Bool}
    (hMem : ZxpMemSpan targetWidth (zxpMapRows transform rows) mappedVector) :
    Exists fun sourceVector =>
      ZxpMemSpan sourceWidth rows sourceVector /\ mappedVector = transform sourceVector := by
  induction hMem with
  | zero =>
      exact Exists.intro (zxpZeroRow sourceWidth)
        (And.intro ZxpMemSpan.zero hTransformZero.symm)
  | pick row hRow hVec innerSplit =>
      cases innerSplit with
      | intro sourceVector hBoth =>
          have hRowInv := zxpMapRowsMemInv transform rows hRow
          cases hRowInv with
          | intro sourceRow hRowBoth =>
              refine Exists.intro (zxpRowXor sourceRow sourceVector)
                (And.intro (ZxpMemSpan.pick sourceRow hRowBoth.left hBoth.left) ?_)
              rw [hTransformXor sourceRow sourceVector (zxpAllWidthRow hAll hRowBoth.left)
                (zxpMemSpanWidth hAll hBoth.left), <- hRowBoth.right, <- hBoth.right]

/-- Span of a linearly-mapped generator list, backward: images of members are members. -/
theorem zxpMapRowsSpanBwd {sourceWidth targetWidth : Nat}
    (transform : List Bool -> List Bool)
    (hTransformZero : transform (zxpZeroRow sourceWidth) = zxpZeroRow targetWidth)
    (hTransformXor : (firstRow secondRow : List Bool) -> firstRow.length = sourceWidth ->
      secondRow.length = sourceWidth ->
      transform (zxpRowXor firstRow secondRow)
        = zxpRowXor (transform firstRow) (transform secondRow))
    {rows : List (List Bool)} (hAll : ZxpAllWidth sourceWidth rows)
    {sourceVector : List Bool} (hMem : ZxpMemSpan sourceWidth rows sourceVector) :
    ZxpMemSpan targetWidth (zxpMapRows transform rows) (transform sourceVector) := by
  induction hMem with
  | zero =>
      rw [hTransformZero]
      exact ZxpMemSpan.zero
  | pick row hRow hVec innerMem =>
      rw [hTransformXor row _ (zxpAllWidthRow hAll hRow) (zxpMemSpanWidth hAll hVec)]
      exact ZxpMemSpan.pick (transform row) (zxpMapRowsMemIntro transform rows hRow) innerMem

/-- Pair membership: the relation (given by generator rows of width `dom + cod`) holds of
the two boundary vectors. -/
def ZxpPairMem (domWidth codWidth : Nat) (relationRows : List (List Bool))
    (domVec codVec : List Bool) : Prop :=
  domVec.length = domWidth /\ codVec.length = codWidth
    /\ ZxpMemSpan (domWidth + codWidth) relationRows (zxpCat domVec codVec)

theorem zxpMemSpanCast {firstWidth secondWidth : Nat} {rows : List (List Bool)}
    {vector : List Bool} (hWidthEq : firstWidth = secondWidth)
    (hMem : ZxpMemSpan firstWidth rows vector) : ZxpMemSpan secondWidth rows vector :=
  hWidthEq ▸ hMem

theorem zxpAllWidthCast {firstWidth secondWidth : Nat} {rows : List (List Bool)}
    (hWidthEq : firstWidth = secondWidth) (hAll : ZxpAllWidth firstWidth rows) :
    ZxpAllWidth secondWidth rows :=
  hWidthEq ▸ hAll

/-! ### Relational composition: stack with the shared middle LEFTMOST, echelonize, keep the
zero-middle rows, project the middle away -/

/-- Embed a first-factor row `(x | y)` as `(y, x, 0)` — middle block leftmost. -/
def zxpComposeEmbedFirst (domWidth codWidth : Nat) (rowPair : List Bool) : List Bool :=
  zxpCat (zxpDropN domWidth rowPair)
    (zxpCat (zxpTakeN domWidth rowPair) (zxpZeroRow codWidth))

/-- Embed a second-factor row `(y | z)` as `(y, 0, z)` — middle block leftmost. -/
def zxpComposeEmbedSecond (midWidth domWidth : Nat) (rowPair : List Bool) : List Bool :=
  zxpCat (zxpTakeN midWidth rowPair)
    (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth rowPair))

/-- Keep only the rows whose first `blockWidth` bits are all false. -/
def zxpFilterHeadFalse (blockWidth : Nat) : List (List Bool) -> List (List Bool)
  | [] => []
  | headRow :: restRows =>
      match zxpAllFalse (zxpTakeN blockWidth headRow) with
      | true => headRow :: zxpFilterHeadFalse blockWidth restRows
      | false => zxpFilterHeadFalse blockWidth restRows

theorem zxpFilterHeadFalseConsTrue (blockWidth : Nat) (headRow : List Bool)
    (restRows : List (List Bool))
    (hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) = true) :
    zxpFilterHeadFalse blockWidth (headRow :: restRows)
      = headRow :: zxpFilterHeadFalse blockWidth restRows := by
  show (match zxpAllFalse (zxpTakeN blockWidth headRow) with
    | true => headRow :: zxpFilterHeadFalse blockWidth restRows
    | false => zxpFilterHeadFalse blockWidth restRows)
    = headRow :: zxpFilterHeadFalse blockWidth restRows
  rw [hCheck]

theorem zxpFilterHeadFalseConsFalse (blockWidth : Nat) (headRow : List Bool)
    (restRows : List (List Bool))
    (hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) = false) :
    zxpFilterHeadFalse blockWidth (headRow :: restRows)
      = zxpFilterHeadFalse blockWidth restRows := by
  show (match zxpAllFalse (zxpTakeN blockWidth headRow) with
    | true => headRow :: zxpFilterHeadFalse blockWidth restRows
    | false => zxpFilterHeadFalse blockWidth restRows)
    = zxpFilterHeadFalse blockWidth restRows
  rw [hCheck]

theorem zxpFilterHeadFalseMemSub (blockWidth : Nat) : {row : List Bool} ->
    (rows : List (List Bool)) -> ZxpRowMem row (zxpFilterHeadFalse blockWidth rows) ->
    ZxpRowMem row rows
  | _row, [], hRow => nomatch hRow
  | row, headRow :: restRows, hRow => by
      cases hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) with
      | true =>
          rw [zxpFilterHeadFalseConsTrue blockWidth headRow restRows hCheck] at hRow
          cases hRow with
          | head => exact ZxpRowMem.head _ _
          | tail hRowRest =>
              exact ZxpRowMem.tail (zxpFilterHeadFalseMemSub blockWidth restRows hRowRest)
      | false =>
          rw [zxpFilterHeadFalseConsFalse blockWidth headRow restRows hCheck] at hRow
          exact ZxpRowMem.tail (zxpFilterHeadFalseMemSub blockWidth restRows hRow)

theorem zxpFilterHeadFalseMemTake (blockWidth : Nat) : {row : List Bool} ->
    (rows : List (List Bool)) -> ZxpRowMem row (zxpFilterHeadFalse blockWidth rows) ->
    zxpAllFalse (zxpTakeN blockWidth row) = true
  | _row, [], hRow => nomatch hRow
  | row, headRow :: restRows, hRow => by
      cases hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) with
      | true =>
          rw [zxpFilterHeadFalseConsTrue blockWidth headRow restRows hCheck] at hRow
          cases hRow with
          | head => exact hCheck
          | tail hRowRest => exact zxpFilterHeadFalseMemTake blockWidth restRows hRowRest
      | false =>
          rw [zxpFilterHeadFalseConsFalse blockWidth headRow restRows hCheck] at hRow
          exact zxpFilterHeadFalseMemTake blockWidth restRows hRow

theorem zxpFilterHeadFalseWidth {width : Nat} (blockWidth : Nat) :
    (rows : List (List Bool)) -> ZxpAllWidth width rows ->
    ZxpAllWidth width (zxpFilterHeadFalse blockWidth rows)
  | [], _hAll => ZxpAllWidth.nil
  | headRow :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          cases hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) with
          | true =>
              rw [zxpFilterHeadFalseConsTrue blockWidth headRow restRows hCheck]
              exact ZxpAllWidth.cons hHead (zxpFilterHeadFalseWidth blockWidth restRows hRest)
          | false =>
              rw [zxpFilterHeadFalseConsFalse blockWidth headRow restRows hCheck]
              exact zxpFilterHeadFalseWidth blockWidth restRows hRest

/-- Filtering does not grow the span. -/
theorem zxpFilterHeadFalseSpanSub {width : Nat} (blockWidth : Nat)
    {rows : List (List Bool)} (hAll : ZxpAllWidth width rows) {vector : List Bool}
    (hMem : ZxpMemSpan width (zxpFilterHeadFalse blockWidth rows) vector) :
    ZxpMemSpan width rows vector := by
  refine zxpMemSpanSub hAll ?_ hMem
  intro row hRow
  exact zxpMemSpanElem hAll (zxpFilterHeadFalseMemSub blockWidth rows hRow)

/-- Members of the filtered span have an all-false leading block. -/
theorem zxpFilterHeadFalseSpanTake {width : Nat} (blockWidth : Nat)
    {rows : List (List Bool)} {vector : List Bool}
    (hMem : ZxpMemSpan width (zxpFilterHeadFalse blockWidth rows) vector) :
    zxpAllFalse (zxpTakeN blockWidth vector) = true :=
  zxpMemSpanTakeAllFalse blockWidth
    (fun row hRow => zxpFilterHeadFalseMemTake blockWidth rows hRow) hMem

/-- THE LEFTMOST-PIVOT EXTRACTION (pitfall 4 of the brief, done right): over an ECHELON
list, a span member with an all-false leading block already lies in the span of the
filtered rows. -/
theorem zxpFilterHeadFalseSpanComplete {width : Nat} (blockWidth : Nat) :
    {lowerBound : Nat} -> (rows : List (List Bool)) ->
    ZxpAllWidth width rows -> ZxpEchelonFrom lowerBound rows ->
    {vector : List Bool} -> ZxpMemSpan width rows vector ->
    zxpAllFalse (zxpTakeN blockWidth vector) = true ->
    ZxpMemSpan width (zxpFilterHeadFalse blockWidth rows) vector
  | _lowerBound, [], _hAll, _hEch, vector, hMem, _hTake => by
      show ZxpMemSpan width [] vector
      exact hMem
  | _lowerBound, headRow :: restRows, hAll, hEch, vector, hMem, hTake => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH _hBound hRest =>
          have hSplit := zxpMemSpanConsInv hAll hMem
          cases hSplit with
          | inl hInRest =>
              have hInner := zxpFilterHeadFalseSpanComplete blockWidth restRows hRestAll
                hRest hInRest hTake
              cases hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) with
              | true =>
                  rw [zxpFilterHeadFalseConsTrue blockWidth headRow restRows hCheck]
                  exact zxpMemSpanWeaken headRow hInner
              | false =>
                  rw [zxpFilterHeadFalseConsFalse blockWidth headRow restRows hCheck]
                  exact hInner
          | inr hSplitPair =>
              cases hSplitPair with
              | intro partner hBoth =>
                  have hPartnerLen : partner.length = width :=
                    zxpMemSpanWidth hRestAll hBoth.left
                  cases hCheck : zxpAllFalse (zxpTakeN blockWidth headRow) with
                  | true =>
                      -- the head passes the filter; reduce to the partner
                      have hPartnerEq : partner = zxpRowXor headRow vector := by
                        rw [hBoth.right]
                        exact (zxpRowXorCancelLeft headRow partner width hHead
                          hPartnerLen).symm
                      have hPartnerTake :
                          zxpAllFalse (zxpTakeN blockWidth partner) = true := by
                        rw [hPartnerEq, zxpTakeNXor blockWidth headRow vector]
                        exact zxpAllFalseXor _ _ hCheck hTake
                      have hInner := zxpFilterHeadFalseSpanComplete blockWidth restRows
                        hRestAll hRest hBoth.left hPartnerTake
                      rw [zxpFilterHeadFalseConsTrue blockWidth headRow restRows hCheck]
                      rw [hBoth.right]
                      exact ZxpMemSpan.pick headRow
                        (ZxpRowMem.head headRow (zxpFilterHeadFalse blockWidth restRows))
                        (zxpMemSpanWeaken headRow hInner)
                  | false =>
                      -- dead branch: the head's lead sits inside the block, but the vector
                      -- is all-false there while the split forces a true bit
                      have hLeadInfo := zxpTakeNotAllFalseLead headRow blockWidth hCheck
                      cases hLeadInfo with
                      | intro leadPos hLeadBoth =>
                          have hLeadEq : leadPos = headLead := by
                            have hChain : some leadPos = some headLead := by
                              rw [<- hLeadBoth.left, hLeadH]
                            exact Option.some.inj hChain
                          have hPartnerBit : zxpGetBit partner headLead = false :=
                            zxpMemSpanBitFalse headLead hRestAll
                              (fun row hRow => zxpEchelonRowsBitFalse hRest row hRow)
                              hBoth.left
                          have hVectorBitTrue : zxpGetBit vector headLead = true := by
                            rw [hBoth.right,
                              zxpGetBitXor headRow partner
                                (by rw [hHead, hPartnerLen]) headLead,
                              zxpLeadBitTrue headRow headLead hLeadH, hPartnerBit]
                            rfl
                          have hVectorBitFalse : zxpGetBit vector headLead = false := by
                            refine zxpAllFalseTakeGetBit vector blockWidth headLead hTake ?_
                            rw [<- hLeadEq]
                            exact hLeadBoth.right
                          rw [hVectorBitTrue] at hVectorBitFalse
                          exact Bool.noConfusion hVectorBitFalse

/-- Relational composition of generator matrices: stack with middle leftmost, echelonize,
keep zero-middle rows, drop the middle block (IH Lemma 5.10 over F2: the pullback is the
kernel computation). -/
def zxpComposeRows (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool)) : List (List Bool) :=
  zxpMapRows (zxpDropN midWidth)
    (zxpFilterHeadFalse midWidth
      (zxpEchelonize
        (zxpCatRows
          (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows)
          (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows))))

theorem zxpComposeEmbedFirstLength (domWidth midWidth codWidth : Nat) (rowPair : List Bool)
    (hLen : rowPair.length = domWidth + midWidth) :
    (zxpComposeEmbedFirst domWidth codWidth rowPair).length
      = midWidth + (domWidth + codWidth) := by
  show (zxpCat (zxpDropN domWidth rowPair)
      (zxpCat (zxpTakeN domWidth rowPair) (zxpZeroRow codWidth))).length
    = midWidth + (domWidth + codWidth)
  rw [zxpCatLength, zxpCatLength, zxpDropNLength rowPair domWidth midWidth hLen,
    zxpTakeNLength rowPair domWidth midWidth hLen, zxpZeroRowLength]

theorem zxpComposeEmbedFirstZero (domWidth midWidth codWidth : Nat) :
    zxpComposeEmbedFirst domWidth codWidth (zxpZeroRow (domWidth + midWidth))
      = zxpZeroRow (midWidth + (domWidth + codWidth)) := by
  show zxpCat (zxpDropN domWidth (zxpZeroRow (domWidth + midWidth)))
      (zxpCat (zxpTakeN domWidth (zxpZeroRow (domWidth + midWidth))) (zxpZeroRow codWidth))
    = zxpZeroRow (midWidth + (domWidth + codWidth))
  rw [zxpDropNZeroRowExact domWidth midWidth, zxpTakeNZeroRowExact domWidth midWidth,
    zxpCatZeroZero domWidth codWidth, zxpCatZeroZero midWidth (domWidth + codWidth)]

theorem zxpComposeEmbedFirstXor (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List Bool) (hFirstLen : firstPair.length = domWidth + midWidth)
    (hSecondLen : secondPair.length = domWidth + midWidth) :
    zxpComposeEmbedFirst domWidth codWidth (zxpRowXor firstPair secondPair)
      = zxpRowXor (zxpComposeEmbedFirst domWidth codWidth firstPair)
          (zxpComposeEmbedFirst domWidth codWidth secondPair) := by
  have hDropLens : (zxpDropN domWidth firstPair).length
      = (zxpDropN domWidth secondPair).length := by
    rw [zxpDropNLength firstPair domWidth midWidth hFirstLen,
      zxpDropNLength secondPair domWidth midWidth hSecondLen]
  have hTakeLens : (zxpTakeN domWidth firstPair).length
      = (zxpTakeN domWidth secondPair).length := by
    rw [zxpTakeNLength firstPair domWidth midWidth hFirstLen,
      zxpTakeNLength secondPair domWidth midWidth hSecondLen]
  show zxpCat (zxpDropN domWidth (zxpRowXor firstPair secondPair))
      (zxpCat (zxpTakeN domWidth (zxpRowXor firstPair secondPair)) (zxpZeroRow codWidth))
    = zxpRowXor
        (zxpCat (zxpDropN domWidth firstPair)
          (zxpCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth)))
        (zxpCat (zxpDropN domWidth secondPair)
          (zxpCat (zxpTakeN domWidth secondPair) (zxpZeroRow codWidth)))
  rw [zxpDropNXor domWidth firstPair secondPair, zxpTakeNXor domWidth firstPair secondPair,
    zxpRowXorCat (zxpDropN domWidth firstPair)
      (zxpCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth))
      (zxpDropN domWidth secondPair)
      (zxpCat (zxpTakeN domWidth secondPair) (zxpZeroRow codWidth)) hDropLens,
    zxpRowXorCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth)
      (zxpTakeN domWidth secondPair) (zxpZeroRow codWidth) hTakeLens,
    zxpRowXorSelf (zxpZeroRow codWidth), zxpZeroRowLength]

theorem zxpComposeEmbedSecondLength (domWidth midWidth codWidth : Nat) (rowPair : List Bool)
    (hLen : rowPair.length = midWidth + codWidth) :
    (zxpComposeEmbedSecond midWidth domWidth rowPair).length
      = midWidth + (domWidth + codWidth) := by
  show (zxpCat (zxpTakeN midWidth rowPair)
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth rowPair))).length
    = midWidth + (domWidth + codWidth)
  rw [zxpCatLength, zxpCatLength, zxpTakeNLength rowPair midWidth codWidth hLen,
    zxpDropNLength rowPair midWidth codWidth hLen, zxpZeroRowLength]

theorem zxpComposeEmbedSecondZero (domWidth midWidth codWidth : Nat) :
    zxpComposeEmbedSecond midWidth domWidth (zxpZeroRow (midWidth + codWidth))
      = zxpZeroRow (midWidth + (domWidth + codWidth)) := by
  show zxpCat (zxpTakeN midWidth (zxpZeroRow (midWidth + codWidth)))
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth (zxpZeroRow (midWidth + codWidth))))
    = zxpZeroRow (midWidth + (domWidth + codWidth))
  rw [zxpTakeNZeroRowExact midWidth codWidth, zxpDropNZeroRowExact midWidth codWidth,
    zxpCatZeroZero domWidth codWidth, zxpCatZeroZero midWidth (domWidth + codWidth)]

theorem zxpComposeEmbedSecondXor (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List Bool) (hFirstLen : firstPair.length = midWidth + codWidth)
    (hSecondLen : secondPair.length = midWidth + codWidth) :
    zxpComposeEmbedSecond midWidth domWidth (zxpRowXor firstPair secondPair)
      = zxpRowXor (zxpComposeEmbedSecond midWidth domWidth firstPair)
          (zxpComposeEmbedSecond midWidth domWidth secondPair) := by
  have hTakeLens : (zxpTakeN midWidth firstPair).length
      = (zxpTakeN midWidth secondPair).length := by
    rw [zxpTakeNLength firstPair midWidth codWidth hFirstLen,
      zxpTakeNLength secondPair midWidth codWidth hSecondLen]
  have hZeroLens : (zxpZeroRow domWidth).length = (zxpZeroRow domWidth).length := rfl
  show zxpCat (zxpTakeN midWidth (zxpRowXor firstPair secondPair))
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth (zxpRowXor firstPair secondPair)))
    = zxpRowXor
        (zxpCat (zxpTakeN midWidth firstPair)
          (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth firstPair)))
        (zxpCat (zxpTakeN midWidth secondPair)
          (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth secondPair)))
  rw [zxpTakeNXor midWidth firstPair secondPair, zxpDropNXor midWidth firstPair secondPair,
    zxpRowXorCat (zxpTakeN midWidth firstPair)
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth firstPair))
      (zxpTakeN midWidth secondPair)
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth secondPair)) hTakeLens,
    zxpRowXorCat (zxpZeroRow domWidth) (zxpDropN midWidth firstPair)
      (zxpZeroRow domWidth) (zxpDropN midWidth secondPair) hZeroLens,
    zxpRowXorSelf (zxpZeroRow domWidth), zxpZeroRowLength]

theorem zxpComposeRowsWidth (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : ZxpAllWidth (midWidth + codWidth) secondRows) :
    ZxpAllWidth (domWidth + codWidth)
      (zxpComposeRows domWidth midWidth codWidth firstRows secondRows) := by
  have hStackAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpCatRows
        (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows)
        (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows)) :=
    zxpCatRowsWidth _ _
      (zxpMapRowsWidth _ (fun row hRowLen =>
        zxpComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
        firstRows hFirstAll)
      (zxpMapRowsWidth _ (fun row hRowLen =>
        zxpComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
        secondRows hSecondAll)
  exact zxpMapRowsWidth (zxpDropN midWidth)
    (fun row hRowLen => zxpDropNLength row midWidth (domWidth + codWidth) hRowLen)
    _ (zxpFilterHeadFalseWidth midWidth _ (zxpEchelonizeWidth _ hStackAll))

/-- The xor of the two composition embeddings in blocks: middle block first, then the
outer pair. -/
theorem zxpComposeEmbedXorBlocks (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List Bool) (hFirstLen : firstPair.length = domWidth + midWidth)
    (hSecondLen : secondPair.length = midWidth + codWidth) :
    zxpRowXor (zxpComposeEmbedFirst domWidth codWidth firstPair)
        (zxpComposeEmbedSecond midWidth domWidth secondPair)
      = zxpCat (zxpRowXor (zxpDropN domWidth firstPair) (zxpTakeN midWidth secondPair))
          (zxpCat (zxpTakeN domWidth firstPair) (zxpDropN midWidth secondPair)) := by
  show zxpRowXor
      (zxpCat (zxpDropN domWidth firstPair)
        (zxpCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth)))
      (zxpCat (zxpTakeN midWidth secondPair)
        (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth secondPair)))
    = zxpCat (zxpRowXor (zxpDropN domWidth firstPair) (zxpTakeN midWidth secondPair))
        (zxpCat (zxpTakeN domWidth firstPair) (zxpDropN midWidth secondPair))
  have hMidLens : (zxpDropN domWidth firstPair).length
      = (zxpTakeN midWidth secondPair).length := by
    rw [zxpDropNLength firstPair domWidth midWidth hFirstLen,
      zxpTakeNLength secondPair midWidth codWidth hSecondLen]
  have hDomLens : (zxpTakeN domWidth firstPair).length = (zxpZeroRow domWidth).length := by
    rw [zxpTakeNLength firstPair domWidth midWidth hFirstLen, zxpZeroRowLength]
  rw [zxpRowXorCat (zxpDropN domWidth firstPair)
      (zxpCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth))
      (zxpTakeN midWidth secondPair)
      (zxpCat (zxpZeroRow domWidth) (zxpDropN midWidth secondPair)) hMidLens,
    zxpRowXorCat (zxpTakeN domWidth firstPair) (zxpZeroRow codWidth)
      (zxpZeroRow domWidth) (zxpDropN midWidth secondPair) hDomLens,
    zxpRowXorZeroRight (zxpTakeN domWidth firstPair) domWidth
      (zxpTakeNLength firstPair domWidth midWidth hFirstLen),
    zxpRowXorZeroLeft (zxpDropN midWidth secondPair) codWidth
      (zxpDropNLength secondPair midWidth codWidth hSecondLen)]

/-- Stack decomposition, forward: a member of the composition stack is the xor of one
embedded member from each factor. -/
theorem zxpComposeStackFwd (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : ZxpAllWidth (midWidth + codWidth) secondRows)
    {stackVec : List Bool}
    (hMem : ZxpMemSpan (midWidth + (domWidth + codWidth))
      (zxpCatRows
        (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows)
        (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows)) stackVec) :
    Exists fun firstPair => Exists fun secondPair =>
      ZxpMemSpan (domWidth + midWidth) firstRows firstPair
        /\ ZxpMemSpan (midWidth + codWidth) secondRows secondPair
        /\ stackVec = zxpRowXor (zxpComposeEmbedFirst domWidth codWidth firstPair)
            (zxpComposeEmbedSecond midWidth domWidth secondPair) := by
  have hLeftAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows) :=
    zxpMapRowsWidth _ (fun row hRowLen =>
      zxpComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen) firstRows hFirstAll
  have hRightAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows) :=
    zxpMapRowsWidth _ (fun row hRowLen =>
      zxpComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
      secondRows hSecondAll
  have hSplit := zxpCatRowsSpanSplitFwd hLeftAll hRightAll hMem
  cases hSplit with
  | intro leftPart hRightPack =>
      cases hRightPack with
      | intro rightPart hParts =>
          have hLeftInv := zxpMapRowsSpanFwd (zxpComposeEmbedFirst domWidth codWidth)
            (zxpComposeEmbedFirstZero domWidth midWidth codWidth)
            (fun firstRow secondRow hFirstLen hSecondLen =>
              zxpComposeEmbedFirstXor domWidth midWidth codWidth firstRow secondRow
                hFirstLen hSecondLen)
            hFirstAll hParts.left
          have hRightInv := zxpMapRowsSpanFwd (zxpComposeEmbedSecond midWidth domWidth)
            (zxpComposeEmbedSecondZero domWidth midWidth codWidth)
            (fun firstRow secondRow hFirstLen hSecondLen =>
              zxpComposeEmbedSecondXor domWidth midWidth codWidth firstRow secondRow
                hFirstLen hSecondLen)
            hSecondAll hParts.right.left
          cases hLeftInv with
          | intro firstPair hFirstBoth =>
              cases hRightInv with
              | intro secondPair hSecondBoth =>
                  refine Exists.intro firstPair (Exists.intro secondPair
                    (And.intro hFirstBoth.left (And.intro hSecondBoth.left ?_)))
                  rw [hParts.right.right, hFirstBoth.right, hSecondBoth.right]

/-- Stack decomposition, backward. -/
theorem zxpComposeStackBwd (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : ZxpAllWidth (midWidth + codWidth) secondRows)
    {firstPair secondPair : List Bool}
    (hFirstMem : ZxpMemSpan (domWidth + midWidth) firstRows firstPair)
    (hSecondMem : ZxpMemSpan (midWidth + codWidth) secondRows secondPair) :
    ZxpMemSpan (midWidth + (domWidth + codWidth))
      (zxpCatRows
        (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows)
        (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows))
      (zxpRowXor (zxpComposeEmbedFirst domWidth codWidth firstPair)
        (zxpComposeEmbedSecond midWidth domWidth secondPair)) := by
  have hLeftAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows) :=
    zxpMapRowsWidth _ (fun row hRowLen =>
      zxpComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen) firstRows hFirstAll
  have hRightAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows) :=
    zxpMapRowsWidth _ (fun row hRowLen =>
      zxpComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
      secondRows hSecondAll
  have hStackAll := zxpCatRowsWidth _ _ hLeftAll hRightAll
  refine zxpMemSpanXorClosed hStackAll ?_ ?_
  · exact zxpCatRowsSpanLeft
      (zxpMapRowsSpanBwd (zxpComposeEmbedFirst domWidth codWidth)
        (zxpComposeEmbedFirstZero domWidth midWidth codWidth)
        (fun firstRow secondRow hFirstLen hSecondLen =>
          zxpComposeEmbedFirstXor domWidth midWidth codWidth firstRow secondRow
            hFirstLen hSecondLen)
        hFirstAll hFirstMem)
  · exact zxpCatRowsSpanRight
      (zxpMapRowsSpanBwd (zxpComposeEmbedSecond midWidth domWidth)
        (zxpComposeEmbedSecondZero domWidth midWidth codWidth)
        (fun firstRow secondRow hFirstLen hSecondLen =>
          zxpComposeEmbedSecondXor domWidth midWidth codWidth firstRow secondRow
            hFirstLen hSecondLen)
        hSecondAll hSecondMem)

/-- THE COMPOSITION SPEC: the computed composite relates exactly the pairs joined by some
middle vector (IH's pullback/kernel computation, specialized to F2). -/
theorem zxpComposeSpec (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : ZxpAllWidth (midWidth + codWidth) secondRows)
    (domVec codVec : List Bool) :
    ZxpPairMem domWidth codWidth
      (zxpComposeRows domWidth midWidth codWidth firstRows secondRows) domVec codVec
    <-> Exists fun midVec =>
        ZxpPairMem domWidth midWidth firstRows domVec midVec
          /\ ZxpPairMem midWidth codWidth secondRows midVec codVec := by
  have hStackAll : ZxpAllWidth (midWidth + (domWidth + codWidth))
      (zxpCatRows
        (zxpMapRows (zxpComposeEmbedFirst domWidth codWidth) firstRows)
        (zxpMapRows (zxpComposeEmbedSecond midWidth domWidth) secondRows)) :=
    zxpCatRowsWidth _ _
      (zxpMapRowsWidth _ (fun row hRowLen =>
        zxpComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
        firstRows hFirstAll)
      (zxpMapRowsWidth _ (fun row hRowLen =>
        zxpComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
        secondRows hSecondAll)
  have hEchAll := zxpEchelonizeWidth _ hStackAll
  have hFilterAll := zxpFilterHeadFalseWidth midWidth _ hEchAll
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomLen : domVec.length = domWidth := hPair.left
    have hCodLen : codVec.length = codWidth := hPair.right.left
    have hMapMem := hPair.right.right
    have hMapInv := zxpMapRowsSpanFwd (zxpDropN midWidth)
      (zxpDropNZeroRowExact midWidth (domWidth + codWidth))
      (fun firstRow secondRow _hFirstLen _hSecondLen =>
        zxpDropNXor midWidth firstRow secondRow)
      hFilterAll hMapMem
    cases hMapInv with
    | intro stackVec hStackBoth =>
        have hInFilter := hStackBoth.left
        have hTakeFalse := zxpFilterHeadFalseSpanTake midWidth hInFilter
        have hInEch : ZxpMemSpan (midWidth + (domWidth + codWidth))
            (zxpEchelonize _) stackVec :=
          zxpFilterHeadFalseSpanSub midWidth hEchAll hInFilter
        have hInStack := zxpEchelonizeSpanSub1 _ hStackAll hInEch
        have hDecomp := zxpComposeStackFwd domWidth midWidth codWidth firstRows secondRows
          hFirstAll hSecondAll hInStack
        cases hDecomp with
        | intro firstPair hSecondPack =>
            cases hSecondPack with
            | intro secondPair hParts =>
                have hFirstPairLen : firstPair.length = domWidth + midWidth :=
                  zxpMemSpanWidth hFirstAll hParts.left
                have hSecondPairLen : secondPair.length = midWidth + codWidth :=
                  zxpMemSpanWidth hSecondAll hParts.right.left
                have hBlocks : stackVec
                    = zxpCat (zxpRowXor (zxpDropN domWidth firstPair)
                        (zxpTakeN midWidth secondPair))
                      (zxpCat (zxpTakeN domWidth firstPair)
                        (zxpDropN midWidth secondPair)) := by
                  rw [hParts.right.right]
                  exact zxpComposeEmbedXorBlocks domWidth midWidth codWidth firstPair
                    secondPair hFirstPairLen hSecondPairLen
                have hMidBlockLen : (zxpRowXor (zxpDropN domWidth firstPair)
                    (zxpTakeN midWidth secondPair)).length = midWidth :=
                  zxpRowXorLength _ _ midWidth
                    (zxpDropNLength firstPair domWidth midWidth hFirstPairLen)
                    (zxpTakeNLength secondPair midWidth codWidth hSecondPairLen)
                have hMidZero : zxpRowXor (zxpDropN domWidth firstPair)
                    (zxpTakeN midWidth secondPair) = zxpZeroRow midWidth := by
                  have hTakeStack : zxpTakeN midWidth stackVec
                      = zxpRowXor (zxpDropN domWidth firstPair)
                          (zxpTakeN midWidth secondPair) := by
                    rw [hBlocks]
                    exact zxpTakeNCatExact _ _ midWidth hMidBlockLen
                  have hAllFalseMid : zxpAllFalse (zxpRowXor (zxpDropN domWidth firstPair)
                      (zxpTakeN midWidth secondPair)) = true := by
                    rw [<- hTakeStack]
                    exact hTakeFalse
                  have hToZero := zxpAllFalseToZeroRow _ hAllFalseMid
                  rw [hMidBlockLen] at hToZero
                  exact hToZero
                have hMidEq : zxpDropN domWidth firstPair
                    = zxpTakeN midWidth secondPair :=
                  zxpRowXorEqZeroImpliesEq _ _ midWidth
                    (zxpDropNLength firstPair domWidth midWidth hFirstPairLen)
                    (zxpTakeNLength secondPair midWidth codWidth hSecondPairLen) hMidZero
                have hDropStack : zxpCat domVec codVec
                    = zxpCat (zxpTakeN domWidth firstPair)
                        (zxpDropN midWidth secondPair) := by
                  rw [hStackBoth.right, hBlocks]
                  exact zxpDropNCatExact _ _ midWidth hMidBlockLen
                have hOuterSplit := zxpCatInj domVec codVec
                  (zxpTakeN domWidth firstPair) (zxpDropN midWidth secondPair)
                  (by rw [hDomLen,
                    zxpTakeNLength firstPair domWidth midWidth hFirstPairLen])
                  hDropStack
                refine Exists.intro (zxpDropN domWidth firstPair)
                  (And.intro (And.intro hDomLen (And.intro
                    (zxpDropNLength firstPair domWidth midWidth hFirstPairLen) ?_))
                    (And.intro
                      (zxpDropNLength firstPair domWidth midWidth hFirstPairLen)
                      (And.intro hCodLen ?_)))
                · have hReassemble : zxpCat domVec (zxpDropN domWidth firstPair)
                      = firstPair := by
                    rw [hOuterSplit.left]
                    exact zxpCatTakeDrop firstPair domWidth midWidth hFirstPairLen
                  rw [hReassemble]
                  exact hParts.left
                · have hReassemble : zxpCat (zxpDropN domWidth firstPair) codVec
                      = secondPair := by
                    rw [hMidEq, hOuterSplit.right]
                    exact zxpCatTakeDrop secondPair midWidth codWidth hSecondPairLen
                  rw [hReassemble]
                  exact hParts.right.left
  · intro hExists
    cases hExists with
    | intro midVec hBothPairs =>
        have hDomLen : domVec.length = domWidth := hBothPairs.left.left
        have hMidLen : midVec.length = midWidth := hBothPairs.left.right.left
        have hCodLen : codVec.length = codWidth := hBothPairs.right.right.left
        have hFirstCatLen : (zxpCat domVec midVec).length = domWidth + midWidth := by
          rw [zxpCatLength, hDomLen, hMidLen]
        have hSecondCatLen : (zxpCat midVec codVec).length = midWidth + codWidth := by
          rw [zxpCatLength, hMidLen, hCodLen]
        have hStackVecEq : zxpRowXor
            (zxpComposeEmbedFirst domWidth codWidth (zxpCat domVec midVec))
            (zxpComposeEmbedSecond midWidth domWidth (zxpCat midVec codVec))
          = zxpCat (zxpZeroRow midWidth) (zxpCat domVec codVec) := by
          rw [zxpComposeEmbedXorBlocks domWidth midWidth codWidth _ _ hFirstCatLen
            hSecondCatLen,
            zxpDropNCatExact domVec midVec domWidth hDomLen,
            zxpTakeNCatExact midVec codVec midWidth hMidLen,
            zxpTakeNCatExact domVec midVec domWidth hDomLen,
            zxpDropNCatExact midVec codVec midWidth hMidLen,
            zxpRowXorSelf midVec, hMidLen]
        have hInStack := zxpComposeStackBwd domWidth midWidth codWidth firstRows secondRows
          hFirstAll hSecondAll hBothPairs.left.right.right hBothPairs.right.right.right
        rw [hStackVecEq] at hInStack
        have hInEch := zxpEchelonizeSpanSub2 _ hStackAll hInStack
        have hTakeFalse : zxpAllFalse (zxpTakeN midWidth
            (zxpCat (zxpZeroRow midWidth) (zxpCat domVec codVec))) = true := by
          rw [zxpTakeNCatExact (zxpZeroRow midWidth) _ midWidth (zxpZeroRowLength midWidth)]
          exact zxpAllFalseZeroRow midWidth
        have hInFilter := zxpFilterHeadFalseSpanComplete midWidth _ hEchAll
          (zxpEchelonizeEchelon _) hInEch hTakeFalse
        have hMapped := zxpMapRowsSpanBwd (zxpDropN midWidth)
          (zxpDropNZeroRowExact midWidth (domWidth + codWidth))
          (fun firstRow secondRow _hFirstLen _hSecondLen =>
            zxpDropNXor midWidth firstRow secondRow)
          hFilterAll hInFilter
        have hDropEq : zxpDropN midWidth
            (zxpCat (zxpZeroRow midWidth) (zxpCat domVec codVec))
          = zxpCat domVec codVec :=
          zxpDropNCatExact (zxpZeroRow midWidth) _ midWidth (zxpZeroRowLength midWidth)
        rw [hDropEq] at hMapped
        exact And.intro hDomLen (And.intro hCodLen hMapped)

/-! ### Parallel tensor: interleaved direct sum (domain blocks together, then codomain
blocks — NOT plain matrix concatenation; the brief's tensor pitfall) -/

/-- Embed a first-factor row `(x1 | y1)` as `(x1, 0, y1, 0)` in the interleaved layout. -/
def zxpTensorEmbedFirst (firstDomWidth secondDomWidth secondCodWidth : Nat)
    (rowPair : List Bool) : List Bool :=
  zxpCat (zxpTakeN firstDomWidth rowPair)
    (zxpCat (zxpZeroRow secondDomWidth)
      (zxpCat (zxpDropN firstDomWidth rowPair) (zxpZeroRow secondCodWidth)))

/-- Embed a second-factor row `(x2 | y2)` as `(0, x2, 0, y2)` in the interleaved layout. -/
def zxpTensorEmbedSecond (firstDomWidth secondDomWidth firstCodWidth : Nat)
    (rowPair : List Bool) : List Bool :=
  zxpCat (zxpZeroRow firstDomWidth)
    (zxpCat (zxpTakeN secondDomWidth rowPair)
      (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth rowPair)))

/-- Tensor (direct sum) of generator matrices in the interleaved boundary layout. -/
def zxpTensorRows (firstDomWidth firstCodWidth secondDomWidth secondCodWidth : Nat)
    (firstRows secondRows : List (List Bool)) : List (List Bool) :=
  zxpCatRows
    (zxpMapRows (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth) firstRows)
    (zxpMapRows (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth) secondRows)

theorem zxpTensorEmbedFirstLength (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (rowPair : List Bool)
    (hLen : rowPair.length = firstDomWidth + firstCodWidth) :
    (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth rowPair).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) := by
  show (zxpCat (zxpTakeN firstDomWidth rowPair)
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth rowPair) (zxpZeroRow secondCodWidth)))).length
    = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
  rw [zxpCatLength, zxpCatLength, zxpCatLength,
    zxpTakeNLength rowPair firstDomWidth firstCodWidth hLen,
    zxpDropNLength rowPair firstDomWidth firstCodWidth hLen,
    zxpZeroRowLength, zxpZeroRowLength]

theorem zxpTensorEmbedFirstZero (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) :
    zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
        (zxpZeroRow (firstDomWidth + firstCodWidth))
      = zxpZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))) := by
  show zxpCat (zxpTakeN firstDomWidth (zxpZeroRow (firstDomWidth + firstCodWidth)))
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth (zxpZeroRow (firstDomWidth + firstCodWidth)))
          (zxpZeroRow secondCodWidth)))
    = zxpZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
  rw [zxpTakeNZeroRowExact firstDomWidth firstCodWidth,
    zxpDropNZeroRowExact firstDomWidth firstCodWidth,
    zxpCatZeroZero firstCodWidth secondCodWidth,
    zxpCatZeroZero secondDomWidth (firstCodWidth + secondCodWidth),
    zxpCatZeroZero firstDomWidth (secondDomWidth + (firstCodWidth + secondCodWidth))]

theorem zxpTensorEmbedFirstXor (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List Bool)
    (hFirstLen : firstPair.length = firstDomWidth + firstCodWidth)
    (hSecondLen : secondPair.length = firstDomWidth + firstCodWidth) :
    zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
        (zxpRowXor firstPair secondPair)
      = zxpRowXor
          (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth firstPair)
          (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth secondPair) := by
  have hTakeLens : (zxpTakeN firstDomWidth firstPair).length
      = (zxpTakeN firstDomWidth secondPair).length := by
    rw [zxpTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen,
      zxpTakeNLength secondPair firstDomWidth firstCodWidth hSecondLen]
  have hDropLens : (zxpDropN firstDomWidth firstPair).length
      = (zxpDropN firstDomWidth secondPair).length := by
    rw [zxpDropNLength firstPair firstDomWidth firstCodWidth hFirstLen,
      zxpDropNLength secondPair firstDomWidth firstCodWidth hSecondLen]
  show zxpCat (zxpTakeN firstDomWidth (zxpRowXor firstPair secondPair))
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth (zxpRowXor firstPair secondPair))
          (zxpZeroRow secondCodWidth)))
    = zxpRowXor
        (zxpCat (zxpTakeN firstDomWidth firstPair)
          (zxpCat (zxpZeroRow secondDomWidth)
            (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth))))
        (zxpCat (zxpTakeN firstDomWidth secondPair)
          (zxpCat (zxpZeroRow secondDomWidth)
            (zxpCat (zxpDropN firstDomWidth secondPair) (zxpZeroRow secondCodWidth))))
  rw [zxpTakeNXor firstDomWidth firstPair secondPair,
    zxpDropNXor firstDomWidth firstPair secondPair,
    zxpRowXorCat (zxpTakeN firstDomWidth firstPair)
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth)))
      (zxpTakeN firstDomWidth secondPair)
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth secondPair) (zxpZeroRow secondCodWidth)))
      hTakeLens,
    zxpRowXorCat (zxpZeroRow secondDomWidth)
      (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth))
      (zxpZeroRow secondDomWidth)
      (zxpCat (zxpDropN firstDomWidth secondPair) (zxpZeroRow secondCodWidth)) rfl,
    zxpRowXorCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth)
      (zxpDropN firstDomWidth secondPair) (zxpZeroRow secondCodWidth) hDropLens,
    zxpRowXorSelf (zxpZeroRow secondDomWidth), zxpZeroRowLength,
    zxpRowXorSelf (zxpZeroRow secondCodWidth), zxpZeroRowLength]

theorem zxpTensorEmbedSecondLength (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (rowPair : List Bool)
    (hLen : rowPair.length = secondDomWidth + secondCodWidth) :
    (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth rowPair).length
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) := by
  show (zxpCat (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth rowPair)
        (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth rowPair)))).length
    = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))
  rw [zxpCatLength, zxpCatLength, zxpCatLength,
    zxpTakeNLength rowPair secondDomWidth secondCodWidth hLen,
    zxpDropNLength rowPair secondDomWidth secondCodWidth hLen,
    zxpZeroRowLength, zxpZeroRowLength]

theorem zxpTensorEmbedSecondZero (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) :
    zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
        (zxpZeroRow (secondDomWidth + secondCodWidth))
      = zxpZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth))) := by
  show zxpCat (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth (zxpZeroRow (secondDomWidth + secondCodWidth)))
        (zxpCat (zxpZeroRow firstCodWidth)
          (zxpDropN secondDomWidth (zxpZeroRow (secondDomWidth + secondCodWidth)))))
    = zxpZeroRow (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
  rw [zxpTakeNZeroRowExact secondDomWidth secondCodWidth,
    zxpDropNZeroRowExact secondDomWidth secondCodWidth,
    zxpCatZeroZero firstCodWidth secondCodWidth,
    zxpCatZeroZero secondDomWidth (firstCodWidth + secondCodWidth),
    zxpCatZeroZero firstDomWidth (secondDomWidth + (firstCodWidth + secondCodWidth))]

theorem zxpTensorEmbedSecondXor (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List Bool)
    (hFirstLen : firstPair.length = secondDomWidth + secondCodWidth)
    (hSecondLen : secondPair.length = secondDomWidth + secondCodWidth) :
    zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
        (zxpRowXor firstPair secondPair)
      = zxpRowXor
          (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth firstPair)
          (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth secondPair) := by
  have hTakeLens : (zxpTakeN secondDomWidth firstPair).length
      = (zxpTakeN secondDomWidth secondPair).length := by
    rw [zxpTakeNLength firstPair secondDomWidth secondCodWidth hFirstLen,
      zxpTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen]
  show zxpCat (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth (zxpRowXor firstPair secondPair))
        (zxpCat (zxpZeroRow firstCodWidth)
          (zxpDropN secondDomWidth (zxpRowXor firstPair secondPair))))
    = zxpRowXor
        (zxpCat (zxpZeroRow firstDomWidth)
          (zxpCat (zxpTakeN secondDomWidth firstPair)
            (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth firstPair))))
        (zxpCat (zxpZeroRow firstDomWidth)
          (zxpCat (zxpTakeN secondDomWidth secondPair)
            (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair))))
  rw [zxpTakeNXor secondDomWidth firstPair secondPair,
    zxpDropNXor secondDomWidth firstPair secondPair,
    zxpRowXorCat (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth firstPair)
        (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth firstPair)))
      (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth secondPair)
        (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair))) rfl,
    zxpRowXorCat (zxpTakeN secondDomWidth firstPair)
      (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth firstPair))
      (zxpTakeN secondDomWidth secondPair)
      (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair)) hTakeLens,
    zxpRowXorCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth firstPair)
      (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair) rfl,
    zxpRowXorSelf (zxpZeroRow firstDomWidth), zxpZeroRowLength,
    zxpRowXorSelf (zxpZeroRow firstCodWidth), zxpZeroRowLength]

/-- Tensor rows at the OUTER boundary bracketing. -/
theorem zxpTensorRowsWidth (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : ZxpAllWidth (secondDomWidth + secondCodWidth) secondRows) :
    ZxpAllWidth ((firstDomWidth + secondDomWidth) + (firstCodWidth + secondCodWidth))
      (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows) := by
  refine zxpAllWidthCast
    (Nat.add_assoc firstDomWidth secondDomWidth (firstCodWidth + secondCodWidth)).symm ?_
  exact zxpCatRowsWidth _ _
    (zxpMapRowsWidth _ (fun row hRowLen => zxpTensorEmbedFirstLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth row hRowLen) firstRows hFirstAll)
    (zxpMapRowsWidth _ (fun row hRowLen => zxpTensorEmbedSecondLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth row hRowLen) secondRows hSecondAll)

/-- The xor of the two tensor embeddings in interleaved blocks. -/
theorem zxpTensorEmbedXorBlocks (firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth : Nat) (firstPair secondPair : List Bool)
    (hFirstLen : firstPair.length = firstDomWidth + firstCodWidth)
    (hSecondLen : secondPair.length = secondDomWidth + secondCodWidth) :
    zxpRowXor (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth firstPair)
        (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth secondPair)
      = zxpCat (zxpTakeN firstDomWidth firstPair)
          (zxpCat (zxpTakeN secondDomWidth secondPair)
            (zxpCat (zxpDropN firstDomWidth firstPair)
              (zxpDropN secondDomWidth secondPair))) := by
  show zxpRowXor
      (zxpCat (zxpTakeN firstDomWidth firstPair)
        (zxpCat (zxpZeroRow secondDomWidth)
          (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth))))
      (zxpCat (zxpZeroRow firstDomWidth)
        (zxpCat (zxpTakeN secondDomWidth secondPair)
          (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair))))
    = zxpCat (zxpTakeN firstDomWidth firstPair)
        (zxpCat (zxpTakeN secondDomWidth secondPair)
          (zxpCat (zxpDropN firstDomWidth firstPair) (zxpDropN secondDomWidth secondPair)))
  have hOuterLens : (zxpTakeN firstDomWidth firstPair).length
      = (zxpZeroRow firstDomWidth).length := by
    rw [zxpTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen, zxpZeroRowLength]
  have hMidLens : (zxpZeroRow secondDomWidth).length
      = (zxpTakeN secondDomWidth secondPair).length := by
    rw [zxpTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen,
      zxpZeroRowLength]
  have hInnerLens : (zxpDropN firstDomWidth firstPair).length
      = (zxpZeroRow firstCodWidth).length := by
    rw [zxpDropNLength firstPair firstDomWidth firstCodWidth hFirstLen, zxpZeroRowLength]
  rw [zxpRowXorCat (zxpTakeN firstDomWidth firstPair)
      (zxpCat (zxpZeroRow secondDomWidth)
        (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth)))
      (zxpZeroRow firstDomWidth)
      (zxpCat (zxpTakeN secondDomWidth secondPair)
        (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair)))
      hOuterLens,
    zxpRowXorCat (zxpZeroRow secondDomWidth)
      (zxpCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth))
      (zxpTakeN secondDomWidth secondPair)
      (zxpCat (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair)) hMidLens,
    zxpRowXorCat (zxpDropN firstDomWidth firstPair) (zxpZeroRow secondCodWidth)
      (zxpZeroRow firstCodWidth) (zxpDropN secondDomWidth secondPair) hInnerLens,
    zxpRowXorZeroRight (zxpTakeN firstDomWidth firstPair) firstDomWidth
      (zxpTakeNLength firstPair firstDomWidth firstCodWidth hFirstLen),
    zxpRowXorZeroLeft (zxpTakeN secondDomWidth secondPair) secondDomWidth
      (zxpTakeNLength secondPair secondDomWidth secondCodWidth hSecondLen),
    zxpRowXorZeroRight (zxpDropN firstDomWidth firstPair) firstCodWidth
      (zxpDropNLength firstPair firstDomWidth firstCodWidth hFirstLen),
    zxpRowXorZeroLeft (zxpDropN secondDomWidth secondPair) secondCodWidth
      (zxpDropNLength secondPair secondDomWidth secondCodWidth hSecondLen)]

/-- THE TENSOR SPEC: the interleaved direct sum relates exactly blockwise. -/
theorem zxpTensorSpec (firstDomWidth firstCodWidth secondDomWidth secondCodWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : ZxpAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (domVec codVec : List Bool) :
    ZxpPairMem (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows) domVec codVec
    <-> Exists fun firstDomVec => Exists fun secondDomVec =>
        Exists fun firstCodVec => Exists fun secondCodVec =>
          domVec = zxpCat firstDomVec secondDomVec
            /\ codVec = zxpCat firstCodVec secondCodVec
            /\ ZxpPairMem firstDomWidth firstCodWidth firstRows firstDomVec firstCodVec
            /\ ZxpPairMem secondDomWidth secondCodWidth secondRows
                secondDomVec secondCodVec := by
  have hLeftAll : ZxpAllWidth
      (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
      (zxpMapRows (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth)
        firstRows) :=
    zxpMapRowsWidth _ (fun row hRowLen => zxpTensorEmbedFirstLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth row hRowLen) firstRows hFirstAll
  have hRightAll : ZxpAllWidth
      (firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)))
      (zxpMapRows (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth)
        secondRows) :=
    zxpMapRowsWidth _ (fun row hRowLen => zxpTensorEmbedSecondLength firstDomWidth
      firstCodWidth secondDomWidth secondCodWidth row hRowLen) secondRows hSecondAll
  have hBracket : (firstDomWidth + secondDomWidth) + (firstCodWidth + secondCodWidth)
      = firstDomWidth + (secondDomWidth + (firstCodWidth + secondCodWidth)) :=
    Nat.add_assoc firstDomWidth secondDomWidth (firstCodWidth + secondCodWidth)
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomLen : domVec.length = firstDomWidth + secondDomWidth := hPair.left
    have hCodLen : codVec.length = firstCodWidth + secondCodWidth := hPair.right.left
    have hMem := zxpMemSpanCast hBracket hPair.right.right
    have hSplit := zxpCatRowsSpanSplitFwd hLeftAll hRightAll hMem
    cases hSplit with
    | intro leftPart hRightPack =>
        cases hRightPack with
        | intro rightPart hParts =>
            have hLeftInv := zxpMapRowsSpanFwd
              (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth)
              (zxpTensorEmbedFirstZero firstDomWidth firstCodWidth secondDomWidth
                secondCodWidth)
              (fun firstRow secondRow hFirstLen hSecondLen =>
                zxpTensorEmbedFirstXor firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth firstRow secondRow hFirstLen hSecondLen)
              hFirstAll hParts.left
            have hRightInv := zxpMapRowsSpanFwd
              (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth)
              (zxpTensorEmbedSecondZero firstDomWidth firstCodWidth secondDomWidth
                secondCodWidth)
              (fun firstRow secondRow hFirstLen hSecondLen =>
                zxpTensorEmbedSecondXor firstDomWidth firstCodWidth secondDomWidth
                  secondCodWidth firstRow secondRow hFirstLen hSecondLen)
              hSecondAll hParts.right.left
            cases hLeftInv with
            | intro firstPair hFirstBoth =>
                cases hRightInv with
                | intro secondPair hSecondBoth =>
                    have hFirstPairLen : firstPair.length
                        = firstDomWidth + firstCodWidth :=
                      zxpMemSpanWidth hFirstAll hFirstBoth.left
                    have hSecondPairLen : secondPair.length
                        = secondDomWidth + secondCodWidth :=
                      zxpMemSpanWidth hSecondAll hSecondBoth.left
                    have hBlocks : zxpCat domVec codVec
                        = zxpCat (zxpTakeN firstDomWidth firstPair)
                            (zxpCat (zxpTakeN secondDomWidth secondPair)
                              (zxpCat (zxpDropN firstDomWidth firstPair)
                                (zxpDropN secondDomWidth secondPair))) := by
                      rw [hParts.right.right, hFirstBoth.right, hSecondBoth.right]
                      exact zxpTensorEmbedXorBlocks firstDomWidth firstCodWidth
                        secondDomWidth secondCodWidth firstPair secondPair
                        hFirstPairLen hSecondPairLen
                    -- split domVec into its two blocks and align
                    have hDomSplit : zxpCat (zxpTakeN firstDomWidth domVec)
                        (zxpDropN firstDomWidth domVec) = domVec :=
                      zxpCatTakeDrop domVec firstDomWidth secondDomWidth hDomLen
                    have hFlat : zxpCat (zxpTakeN firstDomWidth domVec)
                        (zxpCat (zxpDropN firstDomWidth domVec) codVec)
                        = zxpCat (zxpTakeN firstDomWidth firstPair)
                            (zxpCat (zxpTakeN secondDomWidth secondPair)
                              (zxpCat (zxpDropN firstDomWidth firstPair)
                                (zxpDropN secondDomWidth secondPair))) := by
                      rw [<- zxpCatAssoc (zxpTakeN firstDomWidth domVec)
                        (zxpDropN firstDomWidth domVec) codVec, hDomSplit]
                      exact hBlocks
                    have hFirstSplit := zxpCatInj (zxpTakeN firstDomWidth domVec)
                      (zxpCat (zxpDropN firstDomWidth domVec) codVec)
                      (zxpTakeN firstDomWidth firstPair)
                      (zxpCat (zxpTakeN secondDomWidth secondPair)
                        (zxpCat (zxpDropN firstDomWidth firstPair)
                          (zxpDropN secondDomWidth secondPair)))
                      (by rw [zxpTakeNLength domVec firstDomWidth secondDomWidth hDomLen,
                        zxpTakeNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen])
                      hFlat
                    have hSecondSplit := zxpCatInj (zxpDropN firstDomWidth domVec) codVec
                      (zxpTakeN secondDomWidth secondPair)
                      (zxpCat (zxpDropN firstDomWidth firstPair)
                        (zxpDropN secondDomWidth secondPair))
                      (by rw [zxpDropNLength domVec firstDomWidth secondDomWidth hDomLen,
                        zxpTakeNLength secondPair secondDomWidth secondCodWidth
                          hSecondPairLen])
                      hFirstSplit.right
                    refine Exists.intro (zxpTakeN firstDomWidth firstPair)
                      (Exists.intro (zxpTakeN secondDomWidth secondPair)
                        (Exists.intro (zxpDropN firstDomWidth firstPair)
                          (Exists.intro (zxpDropN secondDomWidth secondPair)
                            (And.intro ?_ (And.intro hSecondSplit.right
                              (And.intro ?_ ?_))))))
                    · rw [<- hFirstSplit.left, <- hSecondSplit.left]
                      exact hDomSplit.symm
                    · refine And.intro
                        (zxpTakeNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen)
                        (And.intro (zxpDropNLength firstPair firstDomWidth firstCodWidth
                          hFirstPairLen) ?_)
                      rw [zxpCatTakeDrop firstPair firstDomWidth firstCodWidth
                        hFirstPairLen]
                      exact hFirstBoth.left
                    · refine And.intro
                        (zxpTakeNLength secondPair secondDomWidth secondCodWidth
                          hSecondPairLen)
                        (And.intro (zxpDropNLength secondPair secondDomWidth
                          secondCodWidth hSecondPairLen) ?_)
                      rw [zxpCatTakeDrop secondPair secondDomWidth secondCodWidth
                        hSecondPairLen]
                      exact hSecondBoth.left
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hAll =>
                    have hDomEq := hAll.left
                    have hCodEq := hAll.right.left
                    have hFirstPair := hAll.right.right.left
                    have hSecondPair := hAll.right.right.right
                    have hFd : firstDomVec.length = firstDomWidth := hFirstPair.left
                    have hFc : firstCodVec.length = firstCodWidth :=
                      hFirstPair.right.left
                    have hSd : secondDomVec.length = secondDomWidth := hSecondPair.left
                    have hSc : secondCodVec.length = secondCodWidth :=
                      hSecondPair.right.left
                    have hFirstCatLen : (zxpCat firstDomVec firstCodVec).length
                        = firstDomWidth + firstCodWidth := by
                      rw [zxpCatLength, hFd, hFc]
                    have hSecondCatLen : (zxpCat secondDomVec secondCodVec).length
                        = secondDomWidth + secondCodWidth := by
                      rw [zxpCatLength, hSd, hSc]
                    have hStackVecEq : zxpRowXor
                        (zxpTensorEmbedFirst firstDomWidth secondDomWidth secondCodWidth
                          (zxpCat firstDomVec firstCodVec))
                        (zxpTensorEmbedSecond firstDomWidth secondDomWidth firstCodWidth
                          (zxpCat secondDomVec secondCodVec))
                      = zxpCat firstDomVec (zxpCat secondDomVec
                          (zxpCat firstCodVec secondCodVec)) := by
                      rw [zxpTensorEmbedXorBlocks firstDomWidth firstCodWidth
                          secondDomWidth secondCodWidth _ _ hFirstCatLen hSecondCatLen,
                        zxpTakeNCatExact firstDomVec firstCodVec firstDomWidth hFd,
                        zxpDropNCatExact firstDomVec firstCodVec firstDomWidth hFd,
                        zxpTakeNCatExact secondDomVec secondCodVec secondDomWidth hSd,
                        zxpDropNCatExact secondDomVec secondCodVec secondDomWidth hSd]
                    have hInStack : ZxpMemSpan
                        (firstDomWidth + (secondDomWidth
                          + (firstCodWidth + secondCodWidth)))
                        (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth
                          secondCodWidth firstRows secondRows)
                        (zxpCat firstDomVec (zxpCat secondDomVec
                          (zxpCat firstCodVec secondCodVec))) := by
                      rw [<- hStackVecEq]
                      refine zxpMemSpanXorClosed (zxpCatRowsWidth _ _ hLeftAll hRightAll)
                        ?_ ?_
                      · exact zxpCatRowsSpanLeft
                          (zxpMapRowsSpanBwd _
                            (zxpTensorEmbedFirstZero firstDomWidth firstCodWidth
                              secondDomWidth secondCodWidth)
                            (fun firstRow secondRow hFirstLen hSecondLen =>
                              zxpTensorEmbedFirstXor firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth firstRow secondRow
                                hFirstLen hSecondLen)
                            hFirstAll hFirstPair.right.right)
                      · exact zxpCatRowsSpanRight
                          (zxpMapRowsSpanBwd _
                            (zxpTensorEmbedSecondZero firstDomWidth firstCodWidth
                              secondDomWidth secondCodWidth)
                            (fun firstRow secondRow hFirstLen hSecondLen =>
                              zxpTensorEmbedSecondXor firstDomWidth firstCodWidth
                                secondDomWidth secondCodWidth firstRow secondRow
                                hFirstLen hSecondLen)
                            hSecondAll hSecondPair.right.right)
                    refine And.intro ?_ (And.intro ?_ ?_)
                    · rw [hDomEq, zxpCatLength, hFd, hSd]
                    · rw [hCodEq, zxpCatLength, hFc, hSc]
                    · refine zxpMemSpanCast hBracket.symm ?_
                      rw [hDomEq, hCodEq,
                        zxpCatAssoc firstDomVec secondDomVec
                          (zxpCat firstCodVec secondCodVec)]
                      exact hInStack

/-! ### The identity relation (the diagonal) and the symmetry generator matrix -/

/-- A row of length zero IS the empty row. -/
theorem zxpLengthZeroNil : (row : List Bool) -> row.length = 0 -> row = []
  | [], _hLen => rfl
  | _headBit :: _restBits, hLen => nomatch hLen

/-- Pad an identity-relation row `(u | u)` to `(0u | 0u)`. -/
def zxpPadPairRow (halfWidth : Nat) (rowPair : List Bool) : List Bool :=
  zxpCat (false :: zxpTakeN halfWidth rowPair) (false :: zxpDropN halfWidth rowPair)

/-- Generator matrix of the identity relation (the diagonal subspace). -/
def zxpIdRows : Nat -> List (List Bool)
  | 0 => []
  | widthPred + 1 =>
      zxpCat (true :: zxpZeroRow widthPred) (true :: zxpZeroRow widthPred)
        :: zxpMapRows (zxpPadPairRow widthPred) (zxpIdRows widthPred)

theorem zxpPadPairRowLength (halfWidth : Nat) (rowPair : List Bool)
    (hLen : rowPair.length = halfWidth + halfWidth) :
    (zxpPadPairRow halfWidth rowPair).length = (halfWidth + 1) + (halfWidth + 1) := by
  show (zxpCat (false :: zxpTakeN halfWidth rowPair)
      (false :: zxpDropN halfWidth rowPair)).length = (halfWidth + 1) + (halfWidth + 1)
  rw [zxpCatLength]
  show ((zxpTakeN halfWidth rowPair).length + 1)
      + ((zxpDropN halfWidth rowPair).length + 1) = (halfWidth + 1) + (halfWidth + 1)
  rw [zxpTakeNLength rowPair halfWidth halfWidth hLen,
    zxpDropNLength rowPair halfWidth halfWidth hLen]

theorem zxpPadPairRowZero (halfWidth : Nat) :
    zxpPadPairRow halfWidth (zxpZeroRow (halfWidth + halfWidth))
      = zxpZeroRow ((halfWidth + 1) + (halfWidth + 1)) := by
  show zxpCat (false :: zxpTakeN halfWidth (zxpZeroRow (halfWidth + halfWidth)))
      (false :: zxpDropN halfWidth (zxpZeroRow (halfWidth + halfWidth)))
    = zxpZeroRow ((halfWidth + 1) + (halfWidth + 1))
  rw [zxpTakeNZeroRowExact halfWidth halfWidth, zxpDropNZeroRowExact halfWidth halfWidth]
  exact zxpCatZeroZero (halfWidth + 1) (halfWidth + 1)

theorem zxpPadPairRowXor (halfWidth : Nat) (firstPair secondPair : List Bool)
    (hFirstLen : firstPair.length = halfWidth + halfWidth)
    (hSecondLen : secondPair.length = halfWidth + halfWidth) :
    zxpPadPairRow halfWidth (zxpRowXor firstPair secondPair)
      = zxpRowXor (zxpPadPairRow halfWidth firstPair)
          (zxpPadPairRow halfWidth secondPair) := by
  have hHeadLens : (false :: zxpTakeN halfWidth firstPair).length
      = (false :: zxpTakeN halfWidth secondPair).length := by
    show (zxpTakeN halfWidth firstPair).length + 1
      = (zxpTakeN halfWidth secondPair).length + 1
    rw [zxpTakeNLength firstPair halfWidth halfWidth hFirstLen,
      zxpTakeNLength secondPair halfWidth halfWidth hSecondLen]
  show zxpCat (false :: zxpTakeN halfWidth (zxpRowXor firstPair secondPair))
      (false :: zxpDropN halfWidth (zxpRowXor firstPair secondPair))
    = zxpRowXor
        (zxpCat (false :: zxpTakeN halfWidth firstPair)
          (false :: zxpDropN halfWidth firstPair))
        (zxpCat (false :: zxpTakeN halfWidth secondPair)
          (false :: zxpDropN halfWidth secondPair))
  rw [zxpTakeNXor halfWidth firstPair secondPair, zxpDropNXor halfWidth firstPair secondPair,
    zxpRowXorCat (false :: zxpTakeN halfWidth firstPair)
      (false :: zxpDropN halfWidth firstPair)
      (false :: zxpTakeN halfWidth secondPair)
      (false :: zxpDropN halfWidth secondPair) hHeadLens]
  exact rfl

theorem zxpIdRowsWidth : (identityWidth : Nat) ->
    ZxpAllWidth (identityWidth + identityWidth) (zxpIdRows identityWidth)
  | 0 => ZxpAllWidth.nil
  | widthPred + 1 => by
      refine ZxpAllWidth.cons ?_ ?_
      · show (zxpCat (true :: zxpZeroRow widthPred) (true :: zxpZeroRow widthPred)).length
          = (widthPred + 1) + (widthPred + 1)
        rw [zxpCatLength]
        show ((zxpZeroRow widthPred).length + 1) + ((zxpZeroRow widthPred).length + 1)
          = (widthPred + 1) + (widthPred + 1)
        rw [zxpZeroRowLength]
      · exact zxpMapRowsWidth (zxpPadPairRow widthPred)
          (fun row hRowLen => zxpPadPairRowLength widthPred row hRowLen)
          (zxpIdRows widthPred) (zxpIdRowsWidth widthPred)

/-- THE IDENTITY SPEC: the diagonal subspace relates exactly equal vectors. -/
theorem zxpIdSpec : (identityWidth : Nat) -> (domVec codVec : List Bool) ->
    (ZxpPairMem identityWidth identityWidth (zxpIdRows identityWidth) domVec codVec
      <-> (domVec = codVec /\ domVec.length = identityWidth))
  | 0, domVec, codVec => by
      refine Iff.intro ?_ ?_
      · intro hPair
        have hDomNil := zxpLengthZeroNil domVec hPair.left
        have hCodNil := zxpLengthZeroNil codVec hPair.right.left
        rw [hDomNil, hCodNil]
        exact And.intro rfl rfl
      · intro hSame
        have hDomNil := zxpLengthZeroNil domVec hSame.right
        rw [<- hSame.left, hDomNil]
        exact And.intro rfl (And.intro rfl ZxpMemSpan.zero)
  | widthPred + 1, domVec, codVec => by
      have hIdAllPred := zxpIdRowsWidth widthPred
      have hIdAllFull := zxpIdRowsWidth (widthPred + 1)
      refine Iff.intro ?_ ?_
      · intro hPair
        have hDomLen : domVec.length = widthPred + 1 := hPair.left
        have hCodLen : codVec.length = widthPred + 1 := hPair.right.left
        have hSplit := zxpMemSpanConsInv hIdAllFull hPair.right.right
        cases hSplit with
        | inl hInMapped =>
            have hMapInv := zxpMapRowsSpanFwd (zxpPadPairRow widthPred)
              (zxpPadPairRowZero widthPred)
              (fun firstRow secondRow hFirstLen hSecondLen =>
                zxpPadPairRowXor widthPred firstRow secondRow hFirstLen hSecondLen)
              hIdAllPred hInMapped
            cases hMapInv with
            | intro innerPair hBoth =>
                have hInnerLen : innerPair.length = widthPred + widthPred :=
                  zxpMemSpanWidth hIdAllPred hBoth.left
                have hPadShape : zxpPadPairRow widthPred innerPair
                    = zxpCat (false :: zxpTakeN widthPred innerPair)
                        (false :: zxpDropN widthPred innerPair) := rfl
                rw [hPadShape] at hBoth
                have hOuterSplit := zxpCatInj domVec codVec
                  (false :: zxpTakeN widthPred innerPair)
                  (false :: zxpDropN widthPred innerPair)
                  (by
                    show domVec.length = (zxpTakeN widthPred innerPair).length + 1
                    rw [hDomLen,
                      zxpTakeNLength innerPair widthPred widthPred hInnerLen])
                  hBoth.right
                have hInnerPairMem : ZxpPairMem widthPred widthPred
                    (zxpIdRows widthPred) (zxpTakeN widthPred innerPair)
                    (zxpDropN widthPred innerPair) := by
                  refine And.intro
                    (zxpTakeNLength innerPair widthPred widthPred hInnerLen)
                    (And.intro (zxpDropNLength innerPair widthPred widthPred hInnerLen)
                      ?_)
                  rw [zxpCatTakeDrop innerPair widthPred widthPred hInnerLen]
                  exact hBoth.left
                have hInnerSame :=
                  (zxpIdSpec widthPred (zxpTakeN widthPred innerPair)
                    (zxpDropN widthPred innerPair)).mp hInnerPairMem
                refine And.intro ?_ hDomLen
                rw [hOuterSplit.left, hOuterSplit.right, hInnerSame.left]
        | inr hSplitPair =>
            cases hSplitPair with
            | intro partner hBoth =>
                have hMapInv := zxpMapRowsSpanFwd (zxpPadPairRow widthPred)
                  (zxpPadPairRowZero widthPred)
                  (fun firstRow secondRow hFirstLen hSecondLen =>
                    zxpPadPairRowXor widthPred firstRow secondRow hFirstLen hSecondLen)
                  hIdAllPred hBoth.left
                cases hMapInv with
                | intro innerPair hInnerBoth =>
                    have hInnerLen : innerPair.length = widthPred + widthPred :=
                      zxpMemSpanWidth hIdAllPred hInnerBoth.left
                    have hHeadLens : (true :: zxpZeroRow widthPred).length
                        = (false :: zxpTakeN widthPred innerPair).length := by
                      show (zxpZeroRow widthPred).length + 1
                        = (zxpTakeN widthPred innerPair).length + 1
                      rw [zxpZeroRowLength,
                        zxpTakeNLength innerPair widthPred widthPred hInnerLen]
                    have hXorHead : zxpRowXor
                        (zxpCat (true :: zxpZeroRow widthPred)
                          (true :: zxpZeroRow widthPred))
                        (zxpPadPairRow widthPred innerPair)
                      = zxpCat (true :: zxpTakeN widthPred innerPair)
                          (true :: zxpDropN widthPred innerPair) := by
                      show zxpRowXor
                          (zxpCat (true :: zxpZeroRow widthPred)
                            (true :: zxpZeroRow widthPred))
                          (zxpCat (false :: zxpTakeN widthPred innerPair)
                            (false :: zxpDropN widthPred innerPair))
                        = zxpCat (true :: zxpTakeN widthPred innerPair)
                            (true :: zxpDropN widthPred innerPair)
                      rw [zxpRowXorCat (true :: zxpZeroRow widthPred)
                        (true :: zxpZeroRow widthPred)
                        (false :: zxpTakeN widthPred innerPair)
                        (false :: zxpDropN widthPred innerPair) hHeadLens]
                      show zxpCat
                          (true :: zxpRowXor (zxpZeroRow widthPred)
                            (zxpTakeN widthPred innerPair))
                          (true :: zxpRowXor (zxpZeroRow widthPred)
                            (zxpDropN widthPred innerPair))
                        = zxpCat (true :: zxpTakeN widthPred innerPair)
                            (true :: zxpDropN widthPred innerPair)
                      rw [zxpRowXorZeroLeft (zxpTakeN widthPred innerPair) widthPred
                          (zxpTakeNLength innerPair widthPred widthPred hInnerLen),
                        zxpRowXorZeroLeft (zxpDropN widthPred innerPair) widthPred
                          (zxpDropNLength innerPair widthPred widthPred hInnerLen)]
                    have hCatEq : zxpCat domVec codVec
                        = zxpCat (true :: zxpTakeN widthPred innerPair)
                            (true :: zxpDropN widthPred innerPair) := by
                      rw [hBoth.right, hInnerBoth.right, hXorHead]
                    have hOuterSplit := zxpCatInj domVec codVec
                      (true :: zxpTakeN widthPred innerPair)
                      (true :: zxpDropN widthPred innerPair)
                      (by
                        show domVec.length = (zxpTakeN widthPred innerPair).length + 1
                        rw [hDomLen,
                          zxpTakeNLength innerPair widthPred widthPred hInnerLen])
                      hCatEq
                    have hInnerPairMem : ZxpPairMem widthPred widthPred
                        (zxpIdRows widthPred) (zxpTakeN widthPred innerPair)
                        (zxpDropN widthPred innerPair) := by
                      refine And.intro
                        (zxpTakeNLength innerPair widthPred widthPred hInnerLen)
                        (And.intro
                          (zxpDropNLength innerPair widthPred widthPred hInnerLen) ?_)
                      rw [zxpCatTakeDrop innerPair widthPred widthPred hInnerLen]
                      exact hInnerBoth.left
                    have hInnerSame :=
                      (zxpIdSpec widthPred (zxpTakeN widthPred innerPair)
                        (zxpDropN widthPred innerPair)).mp hInnerPairMem
                    refine And.intro ?_ hDomLen
                    rw [hOuterSplit.left, hOuterSplit.right, hInnerSame.left]
      · intro hSame
        cases hSame with
        | intro hEqVecs hDomLen =>
            rw [<- hEqVecs]
            cases hDom : domVec with
            | nil =>
                rw [hDom] at hDomLen
                exact nomatch hDomLen
            | cons headBit restVec =>
                rw [hDom] at hDomLen
                have hRestLen : restVec.length = widthPred := Nat.succ.inj hDomLen
                have hInnerPairMem :=
                  (zxpIdSpec widthPred restVec restVec).mpr (And.intro rfl hRestLen)
                have hInnerMem := hInnerPairMem.right.right
                have hMapped := zxpMapRowsSpanBwd (zxpPadPairRow widthPred)
                  (zxpPadPairRowZero widthPred)
                  (fun firstRow secondRow hFirstLen hSecondLen =>
                    zxpPadPairRowXor widthPred firstRow secondRow hFirstLen hSecondLen)
                  hIdAllPred hInnerMem
                have hPadEq : zxpPadPairRow widthPred (zxpCat restVec restVec)
                    = zxpCat (false :: restVec) (false :: restVec) := by
                  show zxpCat (false :: zxpTakeN widthPred (zxpCat restVec restVec))
                      (false :: zxpDropN widthPred (zxpCat restVec restVec))
                    = zxpCat (false :: restVec) (false :: restVec)
                  rw [zxpTakeNCatExact restVec restVec widthPred hRestLen,
                    zxpDropNCatExact restVec restVec widthPred hRestLen]
                rw [hPadEq] at hMapped
                have hWeakened := zxpMemSpanWeaken
                  (zxpCat (true :: zxpZeroRow widthPred) (true :: zxpZeroRow widthPred))
                  hMapped
                refine And.intro hDomLen (And.intro hDomLen ?_)
                cases headBit with
                | false => exact hWeakened
                | true =>
                    have hHeadLens : (true :: zxpZeroRow widthPred).length
                        = (false :: restVec).length := by
                      show (zxpZeroRow widthPred).length + 1 = restVec.length + 1
                      rw [zxpZeroRowLength, hRestLen]
                    have hXorTrue : zxpRowXor
                        (zxpCat (true :: zxpZeroRow widthPred)
                          (true :: zxpZeroRow widthPred))
                        (zxpCat (false :: restVec) (false :: restVec))
                      = zxpCat (true :: restVec) (true :: restVec) := by
                      rw [zxpRowXorCat (true :: zxpZeroRow widthPred)
                        (true :: zxpZeroRow widthPred) (false :: restVec)
                        (false :: restVec) hHeadLens]
                      show zxpCat (true :: zxpRowXor (zxpZeroRow widthPred) restVec)
                          (true :: zxpRowXor (zxpZeroRow widthPred) restVec)
                        = zxpCat (true :: restVec) (true :: restVec)
                      rw [zxpRowXorZeroLeft restVec widthPred hRestLen]
                    have hPicked := ZxpMemSpan.pick
                      (zxpCat (true :: zxpZeroRow widthPred)
                        (true :: zxpZeroRow widthPred))
                      (ZxpRowMem.head _ _) hWeakened
                    rw [hXorTrue] at hPicked
                    exact hPicked

/-- Generator matrix of the block symmetry `sigma_{a,b}`: relates `(x ++ y)` to
`(y ++ x)`.  Shipped as the stage-2 symmetry object with width lemma and small kernel
fires; the general blockwise SPEC is not needed by any shipped theorem (the diagram layer
uses the 1-1 crossing cell, whose denotation is `zxpSwapRows 1 1`). -/
def zxpSwapRows (firstWidth secondWidth : Nat) : List (List Bool) :=
  zxpCatRows
    (zxpMapRows (fun rowPair =>
      zxpCat (zxpTakeN firstWidth rowPair)
        (zxpCat (zxpZeroRow secondWidth)
          (zxpCat (zxpZeroRow secondWidth) (zxpDropN firstWidth rowPair))))
      (zxpIdRows firstWidth))
    (zxpMapRows (fun rowPair =>
      zxpCat (zxpZeroRow firstWidth)
        (zxpCat (zxpTakeN secondWidth rowPair)
          (zxpCat (zxpDropN secondWidth rowPair) (zxpZeroRow firstWidth))))
      (zxpIdRows secondWidth))

theorem zxpSwapRowsWidth (firstWidth secondWidth : Nat) :
    ZxpAllWidth ((firstWidth + secondWidth) + (secondWidth + firstWidth))
      (zxpSwapRows firstWidth secondWidth) := by
  refine zxpAllWidthCast
    (Nat.add_assoc firstWidth secondWidth (secondWidth + firstWidth)).symm ?_
  refine zxpCatRowsWidth _ _ ?_ ?_
  · refine zxpMapRowsWidth _ ?_ (zxpIdRows firstWidth) (zxpIdRowsWidth firstWidth)
    intro row hRowLen
    show (zxpCat (zxpTakeN firstWidth row)
        (zxpCat (zxpZeroRow secondWidth)
          (zxpCat (zxpZeroRow secondWidth) (zxpDropN firstWidth row)))).length
      = firstWidth + (secondWidth + (secondWidth + firstWidth))
    rw [zxpCatLength, zxpCatLength, zxpCatLength,
      zxpTakeNLength row firstWidth firstWidth hRowLen,
      zxpDropNLength row firstWidth firstWidth hRowLen, zxpZeroRowLength]
  · refine zxpMapRowsWidth _ ?_ (zxpIdRows secondWidth) (zxpIdRowsWidth secondWidth)
    intro row hRowLen
    show (zxpCat (zxpZeroRow firstWidth)
        (zxpCat (zxpTakeN secondWidth row)
          (zxpCat (zxpDropN secondWidth row) (zxpZeroRow firstWidth)))).length
      = firstWidth + (secondWidth + (secondWidth + firstWidth))
    rw [zxpCatLength, zxpCatLength, zxpCatLength,
      zxpTakeNLength row secondWidth secondWidth hRowLen,
      zxpDropNLength row secondWidth secondWidth hRowLen, zxpZeroRowLength]

/-! ### Relation equivalence (equality up to span) and the categorical laws -/

/-- Two generator matrices present the SAME relation at the given boundary. -/
def ZxpRelEquiv (domWidth codWidth : Nat) (firstRows secondRows : List (List Bool)) : Prop :=
  (domVec codVec : List Bool) ->
    (ZxpPairMem domWidth codWidth firstRows domVec codVec
      <-> ZxpPairMem domWidth codWidth secondRows domVec codVec)

theorem zxpRelEquivRefl (domWidth codWidth : Nat) (rows : List (List Bool)) :
    ZxpRelEquiv domWidth codWidth rows rows :=
  fun _domVec _codVec => Iff.rfl

theorem zxpRelEquivSymm {domWidth codWidth : Nat} {firstRows secondRows : List (List Bool)}
    (hEquiv : ZxpRelEquiv domWidth codWidth firstRows secondRows) :
    ZxpRelEquiv domWidth codWidth secondRows firstRows :=
  fun domVec codVec => (hEquiv domVec codVec).symm

theorem zxpRelEquivTrans {domWidth codWidth : Nat}
    {firstRows secondRows thirdRows : List (List Bool)}
    (hFirst : ZxpRelEquiv domWidth codWidth firstRows secondRows)
    (hSecond : ZxpRelEquiv domWidth codWidth secondRows thirdRows) :
    ZxpRelEquiv domWidth codWidth firstRows thirdRows :=
  fun domVec codVec => Iff.trans (hFirst domVec codVec) (hSecond domVec codVec)

theorem zxpRelEquivOfSpanIff {domWidth codWidth : Nat}
    {firstRows secondRows : List (List Bool)}
    (hIff : (vector : List Bool) ->
      (ZxpMemSpan (domWidth + codWidth) firstRows vector
        <-> ZxpMemSpan (domWidth + codWidth) secondRows vector)) :
    ZxpRelEquiv domWidth codWidth firstRows secondRows := by
  intro domVec codVec
  refine Iff.intro ?_ ?_
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      ((hIff (zxpCat domVec codVec)).mp hPair.right.right))
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      ((hIff (zxpCat domVec codVec)).mpr hPair.right.right))

theorem zxpSpanIffOfRelEquiv {domWidth codWidth : Nat}
    {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : ZxpAllWidth (domWidth + codWidth) secondRows)
    (hEquiv : ZxpRelEquiv domWidth codWidth firstRows secondRows) (vector : List Bool) :
    ZxpMemSpan (domWidth + codWidth) firstRows vector
      <-> ZxpMemSpan (domWidth + codWidth) secondRows vector := by
  refine Iff.intro ?_ ?_
  · intro hMem
    have hVecLen := zxpMemSpanWidth hFirstAll hMem
    have hSplitBack := zxpCatTakeDrop vector domWidth codWidth hVecLen
    have hPair : ZxpPairMem domWidth codWidth firstRows (zxpTakeN domWidth vector)
        (zxpDropN domWidth vector) := by
      refine And.intro (zxpTakeNLength vector domWidth codWidth hVecLen)
        (And.intro (zxpDropNLength vector domWidth codWidth hVecLen) ?_)
      rw [hSplitBack]
      exact hMem
    have hOther := (hEquiv (zxpTakeN domWidth vector) (zxpDropN domWidth vector)).mp hPair
    have hOtherMem := hOther.right.right
    rw [hSplitBack] at hOtherMem
    exact hOtherMem
  · intro hMem
    have hVecLen := zxpMemSpanWidth hSecondAll hMem
    have hSplitBack := zxpCatTakeDrop vector domWidth codWidth hVecLen
    have hPair : ZxpPairMem domWidth codWidth secondRows (zxpTakeN domWidth vector)
        (zxpDropN domWidth vector) := by
      refine And.intro (zxpTakeNLength vector domWidth codWidth hVecLen)
        (And.intro (zxpDropNLength vector domWidth codWidth hVecLen) ?_)
      rw [hSplitBack]
      exact hMem
    have hOther := (hEquiv (zxpTakeN domWidth vector) (zxpDropN domWidth vector)).mpr hPair
    have hOtherMem := hOther.right.right
    rw [hSplitBack] at hOtherMem
    exact hOtherMem

/-- Bool decision -> relation equivalence (the working direction of every row fire). -/
theorem zxpRelEquivOfSpanEqB {domWidth codWidth : Nat}
    {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : ZxpAllWidth (domWidth + codWidth) secondRows)
    (hEq : zxpSpanEqB firstRows secondRows = true) :
    ZxpRelEquiv domWidth codWidth firstRows secondRows :=
  zxpRelEquivOfSpanIff (fun vector => zxpSpanEqBSound hFirstAll hSecondAll hEq vector)

/-- Relation equivalence -> Bool decision (the refutation direction). -/
theorem zxpSpanEqBOfRelEquiv {domWidth codWidth : Nat}
    {firstRows secondRows : List (List Bool)}
    (hFirstAll : ZxpAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : ZxpAllWidth (domWidth + codWidth) secondRows)
    (hEquiv : ZxpRelEquiv domWidth codWidth firstRows secondRows) :
    zxpSpanEqB firstRows secondRows = true :=
  zxpSpanEqBComplete hFirstAll hSecondAll
    (fun vector => zxpSpanIffOfRelEquiv hFirstAll hSecondAll hEquiv vector)

/-- Composition respects span equality on both sides. -/
theorem zxpComposeRowsCong (domWidth midWidth codWidth : Nat)
    {firstRows firstRows2 secondRows secondRows2 : List (List Bool)}
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hFirstAll2 : ZxpAllWidth (domWidth + midWidth) firstRows2)
    (hSecondAll : ZxpAllWidth (midWidth + codWidth) secondRows)
    (hSecondAll2 : ZxpAllWidth (midWidth + codWidth) secondRows2)
    (hLeft : ZxpRelEquiv domWidth midWidth firstRows firstRows2)
    (hRight : ZxpRelEquiv midWidth codWidth secondRows secondRows2) :
    ZxpRelEquiv domWidth codWidth
      (zxpComposeRows domWidth midWidth codWidth firstRows secondRows)
      (zxpComposeRows domWidth midWidth codWidth firstRows2 secondRows2) := by
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec domWidth midWidth codWidth firstRows secondRows
    hFirstAll hSecondAll domVec codVec)
    (Iff.trans ?_ (zxpComposeSpec domWidth midWidth codWidth firstRows2 secondRows2
      hFirstAll2 hSecondAll2 domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        exact Exists.intro midVec (And.intro ((hLeft domVec midVec).mp hBoth.left)
          ((hRight midVec codVec).mp hBoth.right))
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        exact Exists.intro midVec (And.intro ((hLeft domVec midVec).mpr hBoth.left)
          ((hRight midVec codVec).mpr hBoth.right))

/-- Composition is associative up to span equality. -/
theorem zxpComposeRowsAssoc (domWidth midWidth secondMidWidth codWidth : Nat)
    (firstRows secondRows thirdRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : ZxpAllWidth (midWidth + secondMidWidth) secondRows)
    (hThirdAll : ZxpAllWidth (secondMidWidth + codWidth) thirdRows) :
    ZxpRelEquiv domWidth codWidth
      (zxpComposeRows domWidth secondMidWidth codWidth
        (zxpComposeRows domWidth midWidth secondMidWidth firstRows secondRows) thirdRows)
      (zxpComposeRows domWidth midWidth codWidth firstRows
        (zxpComposeRows midWidth secondMidWidth codWidth secondRows thirdRows)) := by
  have hInnerLeftAll := zxpComposeRowsWidth domWidth midWidth secondMidWidth
    firstRows secondRows hFirstAll hSecondAll
  have hInnerRightAll := zxpComposeRowsWidth midWidth secondMidWidth codWidth
    secondRows thirdRows hSecondAll hThirdAll
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec domWidth secondMidWidth codWidth _ thirdRows
    hInnerLeftAll hThirdAll domVec codVec)
    (Iff.trans ?_ (zxpComposeSpec domWidth midWidth codWidth firstRows _
      hFirstAll hInnerRightAll domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro secondMidVec hBoth =>
        have hInner := (zxpComposeSpec domWidth midWidth secondMidWidth firstRows
          secondRows hFirstAll hSecondAll domVec secondMidVec).mp hBoth.left
        cases hInner with
        | intro midVec hInnerBoth =>
            refine Exists.intro midVec (And.intro hInnerBoth.left ?_)
            refine (zxpComposeSpec midWidth secondMidWidth codWidth secondRows thirdRows
              hSecondAll hThirdAll midVec codVec).mpr ?_
            exact Exists.intro secondMidVec (And.intro hInnerBoth.right hBoth.right)
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        have hInner := (zxpComposeSpec midWidth secondMidWidth codWidth secondRows
          thirdRows hSecondAll hThirdAll midVec codVec).mp hBoth.right
        cases hInner with
        | intro secondMidVec hInnerBoth =>
            refine Exists.intro secondMidVec (And.intro ?_ hInnerBoth.right)
            refine (zxpComposeSpec domWidth midWidth secondMidWidth firstRows secondRows
              hFirstAll hSecondAll domVec secondMidVec).mpr ?_
            exact Exists.intro midVec (And.intro hBoth.left hInnerBoth.left)

/-- Left unit law. -/
theorem zxpComposeIdLeft (domWidth codWidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) rows) :
    ZxpRelEquiv domWidth codWidth
      (zxpComposeRows domWidth domWidth codWidth (zxpIdRows domWidth) rows) rows := by
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec domWidth domWidth codWidth (zxpIdRows domWidth) rows
    (zxpIdRowsWidth domWidth) hAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        have hSame := (zxpIdSpec domWidth domVec midVec).mp hBoth.left
        rw [hSame.left]
        exact hBoth.right
  · intro hPair
    refine Exists.intro domVec (And.intro ?_ hPair)
    exact (zxpIdSpec domWidth domVec domVec).mpr (And.intro rfl hPair.left)

/-- Right unit law. -/
theorem zxpComposeIdRight (domWidth codWidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) rows) :
    ZxpRelEquiv domWidth codWidth
      (zxpComposeRows domWidth codWidth codWidth rows (zxpIdRows codWidth)) rows := by
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec domWidth codWidth codWidth rows (zxpIdRows codWidth)
    hAll (zxpIdRowsWidth codWidth) domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        have hSame := (zxpIdSpec codWidth midVec codVec).mp hBoth.right
        rw [<- hSame.left]
        exact hBoth.left
  · intro hPair
    refine Exists.intro codVec (And.intro hPair ?_)
    exact (zxpIdSpec codWidth codVec codVec).mpr (And.intro rfl hPair.right.left)

theorem zxpPairMemCast {domWidth domWidth2 codWidth codWidth2 : Nat}
    {rows : List (List Bool)} {domVec codVec : List Bool}
    (hDomEq : domWidth = domWidth2) (hCodEq : codWidth = codWidth2) :
    ZxpPairMem domWidth codWidth rows domVec codVec
      <-> ZxpPairMem domWidth2 codWidth2 rows domVec codVec := by
  rw [hDomEq, hCodEq]

/-- Tensor respects span equality on both sides. -/
theorem zxpTensorRowsCong (firstDomWidth firstCodWidth secondDomWidth secondCodWidth : Nat)
    {firstRows firstRows2 secondRows secondRows2 : List (List Bool)}
    (hFirstAll : ZxpAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hFirstAll2 : ZxpAllWidth (firstDomWidth + firstCodWidth) firstRows2)
    (hSecondAll : ZxpAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (hSecondAll2 : ZxpAllWidth (secondDomWidth + secondCodWidth) secondRows2)
    (hLeft : ZxpRelEquiv firstDomWidth firstCodWidth firstRows firstRows2)
    (hRight : ZxpRelEquiv secondDomWidth secondCodWidth secondRows secondRows2) :
    ZxpRelEquiv (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows secondRows)
      (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        firstRows2 secondRows2) := by
  intro domVec codVec
  refine Iff.trans (zxpTensorSpec firstDomWidth firstCodWidth secondDomWidth secondCodWidth
    firstRows secondRows hFirstAll hSecondAll domVec codVec)
    (Iff.trans ?_ (zxpTensorSpec firstDomWidth firstCodWidth secondDomWidth secondCodWidth
      firstRows2 secondRows2 hFirstAll2 hSecondAll2 domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    exact Exists.intro firstDomVec (Exists.intro secondDomVec
                      (Exists.intro firstCodVec (Exists.intro secondCodVec
                        (And.intro hFacts.left (And.intro hFacts.right.left
                          (And.intro
                            ((hLeft firstDomVec firstCodVec).mp hFacts.right.right.left)
                            ((hRight secondDomVec secondCodVec).mp
                              hFacts.right.right.right)))))))
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    exact Exists.intro firstDomVec (Exists.intro secondDomVec
                      (Exists.intro firstCodVec (Exists.intro secondCodVec
                        (And.intro hFacts.left (And.intro hFacts.right.left
                          (And.intro
                            ((hLeft firstDomVec firstCodVec).mpr hFacts.right.right.left)
                            ((hRight secondDomVec secondCodVec).mpr
                              hFacts.right.right.right)))))))

/-- Tensoring two identities is the identity of the sum boundary. -/
theorem zxpTensorIdSum (firstWidth secondWidth : Nat) :
    ZxpRelEquiv (firstWidth + secondWidth) (firstWidth + secondWidth)
      (zxpTensorRows firstWidth firstWidth secondWidth secondWidth
        (zxpIdRows firstWidth) (zxpIdRows secondWidth))
      (zxpIdRows (firstWidth + secondWidth)) := by
  intro domVec codVec
  refine Iff.trans (zxpTensorSpec firstWidth firstWidth secondWidth secondWidth
    (zxpIdRows firstWidth) (zxpIdRows secondWidth)
    (zxpIdRowsWidth firstWidth) (zxpIdRowsWidth secondWidth) domVec codVec)
    (Iff.trans ?_ (zxpIdSpec (firstWidth + secondWidth) domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFirstSame := (zxpIdSpec firstWidth firstDomVec firstCodVec).mp
                      hFacts.right.right.left
                    have hSecondSame := (zxpIdSpec secondWidth secondDomVec
                      secondCodVec).mp hFacts.right.right.right
                    refine And.intro ?_ ?_
                    · rw [hFacts.left, hFacts.right.left, hFirstSame.left,
                        hSecondSame.left]
                    · rw [hFacts.left, zxpCatLength, hFirstSame.right,
                        (zxpIdSpec secondWidth secondDomVec secondCodVec).mp
                          hFacts.right.right.right |> And.right]
  · intro hSame
    cases hSame with
    | intro hEqVecs hDomLen =>
        refine Exists.intro (zxpTakeN firstWidth domVec)
          (Exists.intro (zxpDropN firstWidth domVec)
            (Exists.intro (zxpTakeN firstWidth domVec)
              (Exists.intro (zxpDropN firstWidth domVec)
                (And.intro (zxpCatTakeDrop domVec firstWidth secondWidth hDomLen).symm
                  (And.intro ?_ (And.intro ?_ ?_))))))
        · rw [<- hEqVecs]
          exact (zxpCatTakeDrop domVec firstWidth secondWidth hDomLen).symm
        · exact (zxpIdSpec firstWidth (zxpTakeN firstWidth domVec)
            (zxpTakeN firstWidth domVec)).mpr
            (And.intro rfl (zxpTakeNLength domVec firstWidth secondWidth hDomLen))
        · exact (zxpIdSpec secondWidth (zxpDropN firstWidth domVec)
            (zxpDropN firstWidth domVec)).mpr
            (And.intro rfl (zxpDropNLength domVec firstWidth secondWidth hDomLen))

/-- Tensor with the empty boundary on the left is the identity operation. -/
theorem zxpTensorUnitLeft (domWidth codWidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) rows) :
    ZxpRelEquiv domWidth codWidth
      (zxpTensorRows 0 0 domWidth codWidth [] rows) rows := by
  intro domVec codVec
  refine Iff.trans (zxpPairMemCast (Nat.zero_add domWidth).symm
    (Nat.zero_add codWidth).symm) ?_
  refine Iff.trans (zxpTensorSpec 0 0 domWidth codWidth [] rows
    ZxpAllWidth.nil hAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFdNil := zxpLengthZeroNil firstDomVec
                      hFacts.right.right.left.left
                    have hFcNil := zxpLengthZeroNil firstCodVec
                      hFacts.right.right.left.right.left
                    have hDomIs : domVec = secondDomVec := by
                      rw [hFacts.left, hFdNil]
                      rfl
                    have hCodIs : codVec = secondCodVec := by
                      rw [hFacts.right.left, hFcNil]
                      rfl
                    rw [hDomIs, hCodIs]
                    exact hFacts.right.right.right
  · intro hPair
    refine Exists.intro [] (Exists.intro domVec (Exists.intro [] (Exists.intro codVec
      (And.intro rfl (And.intro rfl (And.intro ?_ hPair))))))
    exact And.intro rfl (And.intro rfl ZxpMemSpan.zero)

/-- Tensor with the empty boundary on the right is the identity operation. -/
theorem zxpTensorUnitRight (domWidth codWidth : Nat) (rows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) rows) :
    ZxpRelEquiv domWidth codWidth
      (zxpTensorRows domWidth codWidth 0 0 rows []) rows := by
  intro domVec codVec
  refine Iff.trans (zxpTensorSpec domWidth codWidth 0 0 rows []
    hAll ZxpAllWidth.nil domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hSdNil := zxpLengthZeroNil secondDomVec
                      hFacts.right.right.right.left
                    have hScNil := zxpLengthZeroNil secondCodVec
                      hFacts.right.right.right.right.left
                    have hDomIs : domVec = firstDomVec := by
                      rw [hFacts.left, hSdNil]
                      exact zxpCatNilRight firstDomVec
                    have hCodIs : codVec = firstCodVec := by
                      rw [hFacts.right.left, hScNil]
                      exact zxpCatNilRight firstCodVec
                    rw [hDomIs, hCodIs]
                    exact hFacts.right.right.left
  · intro hPair
    refine Exists.intro domVec (Exists.intro [] (Exists.intro codVec (Exists.intro []
      (And.intro (zxpCatNilRight domVec).symm
        (And.intro (zxpCatNilRight codVec).symm (And.intro hPair ?_))))))
    exact And.intro rfl (And.intro rfl ZxpMemSpan.zero)

/-- Tensor is associative up to span equality (stated at the left-nested boundary). -/
theorem zxpTensorRowsAssoc (firstDomWidth firstCodWidth secondDomWidth secondCodWidth
    thirdDomWidth thirdCodWidth : Nat)
    (firstRows secondRows thirdRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (firstDomWidth + firstCodWidth) firstRows)
    (hSecondAll : ZxpAllWidth (secondDomWidth + secondCodWidth) secondRows)
    (hThirdAll : ZxpAllWidth (thirdDomWidth + thirdCodWidth) thirdRows) :
    ZxpRelEquiv ((firstDomWidth + secondDomWidth) + thirdDomWidth)
      ((firstCodWidth + secondCodWidth) + thirdCodWidth)
      (zxpTensorRows (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
        thirdDomWidth thirdCodWidth
        (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
          firstRows secondRows) thirdRows)
      (zxpTensorRows firstDomWidth firstCodWidth (secondDomWidth + thirdDomWidth)
        (secondCodWidth + thirdCodWidth) firstRows
        (zxpTensorRows secondDomWidth secondCodWidth thirdDomWidth thirdCodWidth
          secondRows thirdRows)) := by
  have hLeftPairAll := zxpTensorRowsWidth firstDomWidth firstCodWidth secondDomWidth
    secondCodWidth firstRows secondRows hFirstAll hSecondAll
  have hRightPairAll := zxpTensorRowsWidth secondDomWidth secondCodWidth thirdDomWidth
    thirdCodWidth secondRows thirdRows hSecondAll hThirdAll
  intro domVec codVec
  refine Iff.trans (zxpTensorSpec (firstDomWidth + secondDomWidth)
    (firstCodWidth + secondCodWidth) thirdDomWidth thirdCodWidth _ thirdRows
    hLeftPairAll hThirdAll domVec codVec) ?_
  refine Iff.trans ?_ (Iff.trans (zxpTensorSpec firstDomWidth firstCodWidth
    (secondDomWidth + thirdDomWidth) (secondCodWidth + thirdCodWidth) firstRows _
    hFirstAll hRightPairAll domVec codVec).symm
    (zxpPairMemCast (Nat.add_assoc firstDomWidth secondDomWidth thirdDomWidth).symm
      (Nat.add_assoc firstCodWidth secondCodWidth thirdCodWidth).symm))
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro pairDomVec hPack1 =>
        cases hPack1 with
        | intro thirdDomVec hPack2 =>
            cases hPack2 with
            | intro pairCodVec hPack3 =>
                cases hPack3 with
                | intro thirdCodVec hFacts =>
                    have hPairSplit := (zxpTensorSpec firstDomWidth firstCodWidth
                      secondDomWidth secondCodWidth firstRows secondRows hFirstAll
                      hSecondAll pairDomVec pairCodVec).mp hFacts.right.right.left
                    cases hPairSplit with
                    | intro firstDomVec hInner1 =>
                        cases hInner1 with
                        | intro secondDomVec hInner2 =>
                            cases hInner2 with
                            | intro firstCodVec hInner3 =>
                                cases hInner3 with
                                | intro secondCodVec hInnerFacts =>
                                    refine Exists.intro firstDomVec
                                      (Exists.intro (zxpCat secondDomVec thirdDomVec)
                                        (Exists.intro firstCodVec
                                          (Exists.intro
                                            (zxpCat secondCodVec thirdCodVec)
                                            (And.intro ?_ (And.intro ?_ (And.intro
                                              hInnerFacts.right.right.left ?_))))))
                                    · rw [hFacts.left, hInnerFacts.left]
                                      exact zxpCatAssoc firstDomVec secondDomVec
                                        thirdDomVec
                                    · rw [hFacts.right.left, hInnerFacts.right.left]
                                      exact zxpCatAssoc firstCodVec secondCodVec
                                        thirdCodVec
                                    · refine (zxpTensorSpec secondDomWidth secondCodWidth
                                        thirdDomWidth thirdCodWidth secondRows thirdRows
                                        hSecondAll hThirdAll _ _).mpr ?_
                                      exact Exists.intro secondDomVec
                                        (Exists.intro thirdDomVec
                                          (Exists.intro secondCodVec
                                            (Exists.intro thirdCodVec
                                              (And.intro rfl (And.intro rfl (And.intro
                                                hInnerFacts.right.right.right
                                                hFacts.right.right.right))))))
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro restDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro restCodVec hFacts =>
                    have hRestSplit := (zxpTensorSpec secondDomWidth secondCodWidth
                      thirdDomWidth thirdCodWidth secondRows thirdRows hSecondAll
                      hThirdAll restDomVec restCodVec).mp hFacts.right.right.right
                    cases hRestSplit with
                    | intro secondDomVec hInner1 =>
                        cases hInner1 with
                        | intro thirdDomVec hInner2 =>
                            cases hInner2 with
                            | intro secondCodVec hInner3 =>
                                cases hInner3 with
                                | intro thirdCodVec hInnerFacts =>
                                    refine Exists.intro
                                      (zxpCat firstDomVec secondDomVec)
                                      (Exists.intro thirdDomVec
                                        (Exists.intro
                                          (zxpCat firstCodVec secondCodVec)
                                          (Exists.intro thirdCodVec
                                            (And.intro ?_ (And.intro ?_ (And.intro
                                              ?_ hInnerFacts.right.right.right))))))
                                    · rw [hFacts.left, hInnerFacts.left,
                                        <- zxpCatAssoc firstDomVec secondDomVec
                                          thirdDomVec]
                                    · rw [hFacts.right.left, hInnerFacts.right.left,
                                        <- zxpCatAssoc firstCodVec secondCodVec
                                          thirdCodVec]
                                    · refine (zxpTensorSpec firstDomWidth firstCodWidth
                                        secondDomWidth secondCodWidth firstRows
                                        secondRows hFirstAll hSecondAll _ _).mpr ?_
                                      exact Exists.intro firstDomVec
                                        (Exists.intro secondDomVec
                                          (Exists.intro firstCodVec
                                            (Exists.intro secondCodVec
                                              (And.intro rfl (And.intro rfl (And.intro
                                                hFacts.right.right.left
                                                hInnerFacts.right.right.left))))))

/-- THE INTERCHANGE LAW: composing tensors is tensoring composites (up to span). -/
theorem zxpTensorComposeInterchange (firstDomWidth firstMidWidth firstCodWidth
    secondDomWidth secondMidWidth secondCodWidth : Nat)
    (firstRows firstRows2 secondRows secondRows2 : List (List Bool))
    (hFirstAll : ZxpAllWidth (firstDomWidth + firstMidWidth) firstRows)
    (hFirstAll2 : ZxpAllWidth (firstMidWidth + firstCodWidth) firstRows2)
    (hSecondAll : ZxpAllWidth (secondDomWidth + secondMidWidth) secondRows)
    (hSecondAll2 : ZxpAllWidth (secondMidWidth + secondCodWidth) secondRows2) :
    ZxpRelEquiv (firstDomWidth + secondDomWidth) (firstCodWidth + secondCodWidth)
      (zxpComposeRows (firstDomWidth + secondDomWidth)
        (firstMidWidth + secondMidWidth) (firstCodWidth + secondCodWidth)
        (zxpTensorRows firstDomWidth firstMidWidth secondDomWidth secondMidWidth
          firstRows secondRows)
        (zxpTensorRows firstMidWidth firstCodWidth secondMidWidth secondCodWidth
          firstRows2 secondRows2))
      (zxpTensorRows firstDomWidth firstCodWidth secondDomWidth secondCodWidth
        (zxpComposeRows firstDomWidth firstMidWidth firstCodWidth firstRows firstRows2)
        (zxpComposeRows secondDomWidth secondMidWidth secondCodWidth secondRows
          secondRows2)) := by
  have hTensorInAll := zxpTensorRowsWidth firstDomWidth firstMidWidth secondDomWidth
    secondMidWidth firstRows secondRows hFirstAll hSecondAll
  have hTensorOutAll := zxpTensorRowsWidth firstMidWidth firstCodWidth secondMidWidth
    secondCodWidth firstRows2 secondRows2 hFirstAll2 hSecondAll2
  have hComposeFirstAll := zxpComposeRowsWidth firstDomWidth firstMidWidth firstCodWidth
    firstRows firstRows2 hFirstAll hFirstAll2
  have hComposeSecondAll := zxpComposeRowsWidth secondDomWidth secondMidWidth
    secondCodWidth secondRows secondRows2 hSecondAll hSecondAll2
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec (firstDomWidth + secondDomWidth)
    (firstMidWidth + secondMidWidth) (firstCodWidth + secondCodWidth) _ _
    hTensorInAll hTensorOutAll domVec codVec)
    (Iff.trans ?_ (zxpTensorSpec firstDomWidth firstCodWidth secondDomWidth
      secondCodWidth _ _ hComposeFirstAll hComposeSecondAll domVec codVec).symm)
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        have hInSplit := (zxpTensorSpec firstDomWidth firstMidWidth secondDomWidth
          secondMidWidth firstRows secondRows hFirstAll hSecondAll domVec midVec).mp
          hBoth.left
        cases hInSplit with
        | intro firstDomVec hPack1 =>
            cases hPack1 with
            | intro secondDomVec hPack2 =>
                cases hPack2 with
                | intro firstMidVec hPack3 =>
                    cases hPack3 with
                    | intro secondMidVec hInFacts =>
                        have hOutSplit := (zxpTensorSpec firstMidWidth firstCodWidth
                          secondMidWidth secondCodWidth firstRows2 secondRows2
                          hFirstAll2 hSecondAll2 midVec codVec).mp hBoth.right
                        cases hOutSplit with
                        | intro firstMidVec2 hQack1 =>
                            cases hQack1 with
                            | intro secondMidVec2 hQack2 =>
                                cases hQack2 with
                                | intro firstCodVec hQack3 =>
                                    cases hQack3 with
                                    | intro secondCodVec hOutFacts =>
                                        have hMidAligned : firstMidVec = firstMidVec2
                                            /\ secondMidVec = secondMidVec2 := by
                                          have hMidChain : zxpCat firstMidVec
                                              secondMidVec
                                            = zxpCat firstMidVec2 secondMidVec2 := by
                                            rw [<- hInFacts.right.left,
                                              <- hOutFacts.left]
                                          exact zxpCatInj firstMidVec secondMidVec
                                            firstMidVec2 secondMidVec2
                                            (by rw [hInFacts.right.right.left.right.left,
                                              hOutFacts.right.right.left.left])
                                            hMidChain
                                        refine Exists.intro firstDomVec
                                          (Exists.intro secondDomVec
                                            (Exists.intro firstCodVec
                                              (Exists.intro secondCodVec
                                                (And.intro hInFacts.left
                                                  (And.intro hOutFacts.right.left
                                                    (And.intro ?_ ?_))))))
                                        · refine (zxpComposeSpec firstDomWidth
                                            firstMidWidth firstCodWidth firstRows
                                            firstRows2 hFirstAll hFirstAll2 _ _).mpr ?_
                                          refine Exists.intro firstMidVec
                                            (And.intro hInFacts.right.right.left ?_)
                                          rw [hMidAligned.left]
                                          exact hOutFacts.right.right.left
                                        · refine (zxpComposeSpec secondDomWidth
                                            secondMidWidth secondCodWidth secondRows
                                            secondRows2 hSecondAll hSecondAll2 _ _).mpr
                                            ?_
                                          refine Exists.intro secondMidVec
                                            (And.intro hInFacts.right.right.right ?_)
                                          rw [hMidAligned.right]
                                          exact hOutFacts.right.right.right
  · intro hExists
    cases hExists with
    | intro firstDomVec hPack1 =>
        cases hPack1 with
        | intro secondDomVec hPack2 =>
            cases hPack2 with
            | intro firstCodVec hPack3 =>
                cases hPack3 with
                | intro secondCodVec hFacts =>
                    have hFirstCompose := (zxpComposeSpec firstDomWidth firstMidWidth
                      firstCodWidth firstRows firstRows2 hFirstAll hFirstAll2
                      firstDomVec firstCodVec).mp hFacts.right.right.left
                    have hSecondCompose := (zxpComposeSpec secondDomWidth secondMidWidth
                      secondCodWidth secondRows secondRows2 hSecondAll hSecondAll2
                      secondDomVec secondCodVec).mp hFacts.right.right.right
                    cases hFirstCompose with
                    | intro firstMidVec hFirstBoth =>
                        cases hSecondCompose with
                        | intro secondMidVec hSecondBoth =>
                            refine Exists.intro (zxpCat firstMidVec secondMidVec)
                              (And.intro ?_ ?_)
                            · refine (zxpTensorSpec firstDomWidth firstMidWidth
                                secondDomWidth secondMidWidth firstRows secondRows
                                hFirstAll hSecondAll _ _).mpr ?_
                              exact Exists.intro firstDomVec (Exists.intro secondDomVec
                                (Exists.intro firstMidVec (Exists.intro secondMidVec
                                  (And.intro hFacts.left (And.intro rfl (And.intro
                                    hFirstBoth.left hSecondBoth.left))))))
                            · refine (zxpTensorSpec firstMidWidth firstCodWidth
                                secondMidWidth secondCodWidth firstRows2 secondRows2
                                hFirstAll2 hSecondAll2 _ _).mpr ?_
                              exact Exists.intro firstMidVec (Exists.intro secondMidVec
                                (Exists.intro firstCodVec (Exists.intro secondCodVec
                                  (And.intro rfl (And.intro hFacts.right.left
                                    (And.intro hFirstBoth.right
                                      hSecondBoth.right))))))

/-! ## Stage 3 — the strict-layer diagram carrier (fresh re-derivation of the
`StrictLayerDiagram` idiom: a diagram is a source arity plus a list of layers; each layer a
list of cells; sequential composition is layer-list concatenation) -/

/-- Phase-free ZX cells: Z (copy) spiders, X (parity) spiders, the identity wire, and the
adjacent crossing.  NO Hadamard — its absence is exactly what pins the fragment to
LinRel_F2 (Kissinger 2204.14038; IB = IH_Z2). -/
inductive ZxpCell : Type where
  | zSpider : Nat -> Nat -> ZxpCell
  | xSpider : Nat -> Nat -> ZxpCell
  | wire : ZxpCell
  | crossing : ZxpCell

def zxpCellDomArity : ZxpCell -> Nat
  | ZxpCell.zSpider domArity _codArity => domArity
  | ZxpCell.xSpider domArity _codArity => domArity
  | ZxpCell.wire => 1
  | ZxpCell.crossing => 2

def zxpCellCodArity : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity codArity => codArity
  | ZxpCell.xSpider _domArity codArity => codArity
  | ZxpCell.wire => 1
  | ZxpCell.crossing => 2

/-- Z/copy spider subspace: the all-ones row (the diagonal), with the degenerate 0-legged
spider guarded to the empty row list (pitfall 5 of the brief). -/
def zxpSpiderCopyRows : Nat -> List (List Bool)
  | 0 => []
  | totalPred + 1 => zxpAllOnesRow (totalPred + 1) :: []

/-- X/parity spider subspace: consecutive-pair generator rows (dimension `legs - 1`). -/
def zxpParityRows : Nat -> List (List Bool)
  | 0 => []
  | 1 => []
  | widthPred + 2 =>
      (true :: true :: zxpZeroRow widthPred)
        :: zxpMapRows (fun row => false :: row) (zxpParityRows (widthPred + 1))

theorem zxpSpiderCopyRowsWidth : (totalArity : Nat) ->
    ZxpAllWidth totalArity (zxpSpiderCopyRows totalArity)
  | 0 => ZxpAllWidth.nil
  | totalPred + 1 =>
      ZxpAllWidth.cons (zxpAllOnesRowLength (totalPred + 1)) ZxpAllWidth.nil

theorem zxpParityRowsWidth : (totalArity : Nat) ->
    ZxpAllWidth totalArity (zxpParityRows totalArity)
  | 0 => ZxpAllWidth.nil
  | 1 => ZxpAllWidth.nil
  | widthPred + 2 => by
      refine ZxpAllWidth.cons ?_ ?_
      · show (zxpZeroRow widthPred).length + 1 + 1 = widthPred + 2
        rw [zxpZeroRowLength]
      · refine zxpMapRowsWidth (fun row => false :: row) ?_ (zxpParityRows (widthPred + 1))
          (zxpParityRowsWidth (widthPred + 1))
        intro row hRowLen
        show row.length + 1 = widthPred + 2
        rw [hRowLen]

/-- Denotation of one cell as a generator matrix at width `dom + cod`. -/
def zxpCellRows : ZxpCell -> List (List Bool)
  | ZxpCell.zSpider domArity codArity => zxpSpiderCopyRows (domArity + codArity)
  | ZxpCell.xSpider domArity codArity => zxpParityRows (domArity + codArity)
  | ZxpCell.wire => zxpIdRows 1
  | ZxpCell.crossing => zxpSwapRows 1 1

theorem zxpCellRowsWidth : (cell : ZxpCell) ->
    ZxpAllWidth (zxpCellDomArity cell + zxpCellCodArity cell) (zxpCellRows cell)
  | ZxpCell.zSpider domArity codArity => zxpSpiderCopyRowsWidth (domArity + codArity)
  | ZxpCell.xSpider domArity codArity => zxpParityRowsWidth (domArity + codArity)
  | ZxpCell.wire => zxpIdRowsWidth 1
  | ZxpCell.crossing => zxpSwapRowsWidth 1 1

/-- Cons-only concatenation of cell lists. -/
def zxpCatCells : List ZxpCell -> List ZxpCell -> List ZxpCell
  | [], secondCells => secondCells
  | headCell :: restCells, secondCells => headCell :: zxpCatCells restCells secondCells

def zxpLayerDomArity : List ZxpCell -> Nat
  | [] => 0
  | headCell :: restCells => zxpCellDomArity headCell + zxpLayerDomArity restCells

def zxpLayerCodArity : List ZxpCell -> Nat
  | [] => 0
  | headCell :: restCells => zxpCellCodArity headCell + zxpLayerCodArity restCells

/-- Layer denotation: iterated interleaved direct sum, head cell first. -/
def zxpLayerDenote : List ZxpCell -> List (List Bool)
  | [] => []
  | headCell :: restCells =>
      zxpTensorRows (zxpCellDomArity headCell) (zxpCellCodArity headCell)
        (zxpLayerDomArity restCells) (zxpLayerCodArity restCells)
        (zxpCellRows headCell) (zxpLayerDenote restCells)

theorem zxpLayerDenoteWidth : (layer : List ZxpCell) ->
    ZxpAllWidth (zxpLayerDomArity layer + zxpLayerCodArity layer) (zxpLayerDenote layer)
  | [] => ZxpAllWidth.nil
  | headCell :: restCells =>
      zxpTensorRowsWidth (zxpCellDomArity headCell) (zxpCellCodArity headCell)
        (zxpLayerDomArity restCells) (zxpLayerCodArity restCells)
        (zxpCellRows headCell) (zxpLayerDenote restCells)
        (zxpCellRowsWidth headCell) (zxpLayerDenoteWidth restCells)

theorem zxpCatCellsDomArity : (firstCells secondCells : List ZxpCell) ->
    zxpLayerDomArity (zxpCatCells firstCells secondCells)
      = zxpLayerDomArity firstCells + zxpLayerDomArity secondCells
  | [], secondCells => (Nat.zero_add (zxpLayerDomArity secondCells)).symm
  | headCell :: restCells, secondCells => by
      show zxpCellDomArity headCell
          + zxpLayerDomArity (zxpCatCells restCells secondCells)
        = (zxpCellDomArity headCell + zxpLayerDomArity restCells)
          + zxpLayerDomArity secondCells
      rw [zxpCatCellsDomArity restCells secondCells]
      exact (Nat.add_assoc (zxpCellDomArity headCell) (zxpLayerDomArity restCells)
        (zxpLayerDomArity secondCells)).symm

theorem zxpCatCellsCodArity : (firstCells secondCells : List ZxpCell) ->
    zxpLayerCodArity (zxpCatCells firstCells secondCells)
      = zxpLayerCodArity firstCells + zxpLayerCodArity secondCells
  | [], secondCells => (Nat.zero_add (zxpLayerCodArity secondCells)).symm
  | headCell :: restCells, secondCells => by
      show zxpCellCodArity headCell
          + zxpLayerCodArity (zxpCatCells restCells secondCells)
        = (zxpCellCodArity headCell + zxpLayerCodArity restCells)
          + zxpLayerCodArity secondCells
      rw [zxpCatCellsCodArity restCells secondCells]
      exact (Nat.add_assoc (zxpCellCodArity headCell) (zxpLayerCodArity restCells)
        (zxpLayerCodArity secondCells)).symm

/-- The wire layer of a given strand count. -/
def zxpWireCells : Nat -> List ZxpCell
  | 0 => []
  | strandPred + 1 => ZxpCell.wire :: zxpWireCells strandPred

theorem zxpWireCellsDomArity : (strandCount : Nat) ->
    zxpLayerDomArity (zxpWireCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + zxpLayerDomArity (zxpWireCells strandPred) = strandPred + 1
      rw [zxpWireCellsDomArity strandPred]
      exact Nat.add_comm 1 strandPred

theorem zxpWireCellsCodArity : (strandCount : Nat) ->
    zxpLayerCodArity (zxpWireCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + zxpLayerCodArity (zxpWireCells strandPred) = strandPred + 1
      rw [zxpWireCellsCodArity strandPred]
      exact Nat.add_comm 1 strandPred

/-- Relation-equivalence transport along boundary equalities. -/
theorem zxpRelEquivCast {domWidth domWidth2 codWidth codWidth2 : Nat}
    {firstRows secondRows : List (List Bool)} (hDomEq : domWidth = domWidth2)
    (hCodEq : codWidth = codWidth2)
    (hEquiv : ZxpRelEquiv domWidth codWidth firstRows secondRows) :
    ZxpRelEquiv domWidth2 codWidth2 firstRows secondRows := by
  rw [<- hDomEq, <- hCodEq]
  exact hEquiv

/-- The wire layer denotes the identity relation. -/
theorem zxpWireCellsDenoteId : (strandCount : Nat) ->
    ZxpRelEquiv strandCount strandCount (zxpLayerDenote (zxpWireCells strandCount))
      (zxpIdRows strandCount)
  | 0 => zxpRelEquivRefl 0 0 []
  | strandPred + 1 => by
      have hInner := zxpWireCellsDenoteId strandPred
      have hStep1 : ZxpRelEquiv (1 + strandPred) (1 + strandPred)
          (zxpLayerDenote (zxpWireCells (strandPred + 1)))
          (zxpTensorRows 1 1 strandPred strandPred (zxpIdRows 1) (zxpIdRows strandPred)) := by
        show ZxpRelEquiv (1 + strandPred) (1 + strandPred)
          (zxpTensorRows 1 1 (zxpLayerDomArity (zxpWireCells strandPred))
            (zxpLayerCodArity (zxpWireCells strandPred)) (zxpIdRows 1)
            (zxpLayerDenote (zxpWireCells strandPred)))
          (zxpTensorRows 1 1 strandPred strandPred (zxpIdRows 1) (zxpIdRows strandPred))
        rw [zxpWireCellsDomArity strandPred, zxpWireCellsCodArity strandPred]
        exact zxpTensorRowsCong 1 1 strandPred strandPred (zxpIdRowsWidth 1)
          (zxpIdRowsWidth 1)
          (zxpAllWidthCast (by rw [zxpWireCellsDomArity strandPred,
            zxpWireCellsCodArity strandPred])
            (zxpLayerDenoteWidth (zxpWireCells strandPred)))
          (zxpIdRowsWidth strandPred) (zxpRelEquivRefl 1 1 (zxpIdRows 1)) hInner
      have hStep2 := zxpTensorIdSum 1 strandPred
      rw [Nat.add_comm 1 strandPred] at hStep1 hStep2
      exact zxpRelEquivTrans hStep1 hStep2

/-- Splitting a layer built by cell concatenation into a tensor of the parts. -/
theorem zxpLayerDenoteCatSplit : (firstCells secondCells : List ZxpCell) ->
    ZxpRelEquiv (zxpLayerDomArity firstCells + zxpLayerDomArity secondCells)
      (zxpLayerCodArity firstCells + zxpLayerCodArity secondCells)
      (zxpLayerDenote (zxpCatCells firstCells secondCells))
      (zxpTensorRows (zxpLayerDomArity firstCells) (zxpLayerCodArity firstCells)
        (zxpLayerDomArity secondCells) (zxpLayerCodArity secondCells)
        (zxpLayerDenote firstCells) (zxpLayerDenote secondCells))
  | [], secondCells => by
      refine zxpRelEquivCast (Nat.zero_add (zxpLayerDomArity secondCells)).symm
        (Nat.zero_add (zxpLayerCodArity secondCells)).symm ?_
      exact zxpRelEquivSymm (zxpTensorUnitLeft (zxpLayerDomArity secondCells)
        (zxpLayerCodArity secondCells) (zxpLayerDenote secondCells)
        (zxpLayerDenoteWidth secondCells))
  | headCell :: restCells, secondCells => by
      have hInner := zxpLayerDenoteCatSplit restCells secondCells
      -- rewrite the arities of the concatenated tail inside the head tensor
      have hStep1 : ZxpRelEquiv
          (zxpCellDomArity headCell
            + (zxpLayerDomArity restCells + zxpLayerDomArity secondCells))
          (zxpCellCodArity headCell
            + (zxpLayerCodArity restCells + zxpLayerCodArity secondCells))
          (zxpLayerDenote (zxpCatCells (headCell :: restCells) secondCells))
          (zxpTensorRows (zxpCellDomArity headCell) (zxpCellCodArity headCell)
            (zxpLayerDomArity restCells + zxpLayerDomArity secondCells)
            (zxpLayerCodArity restCells + zxpLayerCodArity secondCells)
            (zxpCellRows headCell)
            (zxpTensorRows (zxpLayerDomArity restCells) (zxpLayerCodArity restCells)
              (zxpLayerDomArity secondCells) (zxpLayerCodArity secondCells)
              (zxpLayerDenote restCells) (zxpLayerDenote secondCells))) := by
        show ZxpRelEquiv _ _
          (zxpTensorRows (zxpCellDomArity headCell) (zxpCellCodArity headCell)
            (zxpLayerDomArity (zxpCatCells restCells secondCells))
            (zxpLayerCodArity (zxpCatCells restCells secondCells))
            (zxpCellRows headCell) (zxpLayerDenote (zxpCatCells restCells secondCells)))
          _
        rw [zxpCatCellsDomArity restCells secondCells,
          zxpCatCellsCodArity restCells secondCells]
        refine zxpTensorRowsCong (zxpCellDomArity headCell) (zxpCellCodArity headCell)
          (zxpLayerDomArity restCells + zxpLayerDomArity secondCells)
          (zxpLayerCodArity restCells + zxpLayerCodArity secondCells)
          (zxpCellRowsWidth headCell) (zxpCellRowsWidth headCell)
          (zxpAllWidthCast (by rw [zxpCatCellsDomArity restCells secondCells,
            zxpCatCellsCodArity restCells secondCells])
            (zxpLayerDenoteWidth (zxpCatCells restCells secondCells)))
          (zxpTensorRowsWidth (zxpLayerDomArity restCells) (zxpLayerCodArity restCells)
            (zxpLayerDomArity secondCells) (zxpLayerCodArity secondCells)
            (zxpLayerDenote restCells) (zxpLayerDenote secondCells)
            (zxpLayerDenoteWidth restCells) (zxpLayerDenoteWidth secondCells))
          (zxpRelEquivRefl _ _ (zxpCellRows headCell)) hInner
      have hStep2 := zxpRelEquivSymm (zxpTensorRowsAssoc (zxpCellDomArity headCell)
        (zxpCellCodArity headCell) (zxpLayerDomArity restCells)
        (zxpLayerCodArity restCells) (zxpLayerDomArity secondCells)
        (zxpLayerCodArity secondCells) (zxpCellRows headCell) (zxpLayerDenote restCells)
        (zxpLayerDenote secondCells) (zxpCellRowsWidth headCell)
        (zxpLayerDenoteWidth restCells) (zxpLayerDenoteWidth secondCells))
      have hStep1Casted := zxpRelEquivCast
        (Nat.add_assoc (zxpCellDomArity headCell) (zxpLayerDomArity restCells)
          (zxpLayerDomArity secondCells)).symm
        (Nat.add_assoc (zxpCellCodArity headCell) (zxpLayerCodArity restCells)
          (zxpLayerCodArity secondCells)).symm hStep1
      exact zxpRelEquivTrans hStep1Casted hStep2

/-! ### Layer lists: sequential plumbing, well-formedness, denotation -/

/-- Cons-only concatenation of layer lists. -/
def zxpCatLayers : List (List ZxpCell) -> List (List ZxpCell) -> List (List ZxpCell)
  | [], secondLayers => secondLayers
  | headLayer :: restLayers, secondLayers => headLayer :: zxpCatLayers restLayers secondLayers

/-- Output arity after running the layer list from the given input arity. -/
def zxpLayersCodArity : Nat -> List (List ZxpCell) -> Nat
  | currentArity, [] => currentArity
  | _currentArity, layer :: restLayers => zxpLayersCodArity (zxpLayerCodArity layer) restLayers

/-- Well-formedness of a layer list against a running arity: every layer's domain arity
meets the arity produced so far. -/
inductive ZxpLayersWF : Nat -> List (List ZxpCell) -> Prop where
  | nil (currentArity : Nat) : ZxpLayersWF currentArity []
  | cons {currentArity : Nat} {layer : List ZxpCell} {restLayers : List (List ZxpCell)}
      (hDom : zxpLayerDomArity layer = currentArity)
      (hRest : ZxpLayersWF (zxpLayerCodArity layer) restLayers) :
      ZxpLayersWF currentArity (layer :: restLayers)

/-- Denotation of a layer list: iterated relational composition (identity for no layers). -/
def zxpLayersDenote : Nat -> List (List ZxpCell) -> List (List Bool)
  | currentArity, [] => zxpIdRows currentArity
  | currentArity, layer :: restLayers =>
      zxpComposeRows currentArity (zxpLayerCodArity layer)
        (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
        (zxpLayerDenote layer)
        (zxpLayersDenote (zxpLayerCodArity layer) restLayers)

theorem zxpLayersDenoteWidth : {currentArity : Nat} -> (layers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity layers ->
    ZxpAllWidth (currentArity + zxpLayersCodArity currentArity layers)
      (zxpLayersDenote currentArity layers)
  | currentArity, [], _hWF => zxpIdRowsWidth currentArity
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          exact zxpComposeRowsWidth currentArity (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            (zxpLayerDenote layer) (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            (zxpAllWidthCast (by rw [hDom]) (zxpLayerDenoteWidth layer))
            (zxpLayersDenoteWidth restLayers hRest)

theorem zxpLayersCodArityCat : (currentArity : Nat) ->
    (firstLayers secondLayers : List (List ZxpCell)) ->
    zxpLayersCodArity currentArity (zxpCatLayers firstLayers secondLayers)
      = zxpLayersCodArity (zxpLayersCodArity currentArity firstLayers) secondLayers
  | _currentArity, [], _secondLayers => rfl
  | currentArity, layer :: restLayers, secondLayers =>
      zxpLayersCodArityCat (zxpLayerCodArity layer) restLayers secondLayers

theorem zxpLayersWFCat : {currentArity : Nat} ->
    (firstLayers secondLayers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity firstLayers ->
    ZxpLayersWF (zxpLayersCodArity currentArity firstLayers) secondLayers ->
    ZxpLayersWF currentArity (zxpCatLayers firstLayers secondLayers)
  | _currentArity, [], _secondLayers, _hFirst, hSecond => hSecond
  | _currentArity, layer :: restLayers, secondLayers, hFirst, hSecond => by
      cases hFirst with
      | cons hDom hRest =>
          exact ZxpLayersWF.cons hDom
            (zxpLayersWFCat restLayers secondLayers hRest hSecond)

/-- Sequential decomposition: the denotation of a concatenated layer list is the relational
composition of the two parts' denotations. -/
theorem zxpLayersDenoteCat : {currentArity : Nat} ->
    (firstLayers secondLayers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity firstLayers ->
    ZxpLayersWF (zxpLayersCodArity currentArity firstLayers) secondLayers ->
    ZxpRelEquiv currentArity
      (zxpLayersCodArity (zxpLayersCodArity currentArity firstLayers) secondLayers)
      (zxpLayersDenote currentArity (zxpCatLayers firstLayers secondLayers))
      (zxpComposeRows currentArity (zxpLayersCodArity currentArity firstLayers)
        (zxpLayersCodArity (zxpLayersCodArity currentArity firstLayers) secondLayers)
        (zxpLayersDenote currentArity firstLayers)
        (zxpLayersDenote (zxpLayersCodArity currentArity firstLayers) secondLayers))
  | currentArity, [], secondLayers, _hFirst, hSecond =>
      zxpRelEquivSymm (zxpComposeIdLeft currentArity
        (zxpLayersCodArity currentArity secondLayers)
        (zxpLayersDenote currentArity secondLayers)
        (zxpLayersDenoteWidth secondLayers hSecond))
  | currentArity, layer :: restLayers, secondLayers, hFirst, hSecond => by
      cases hFirst with
      | cons hDom hRest =>
          show ZxpRelEquiv currentArity
            (zxpLayersCodArity
              (zxpLayersCodArity (zxpLayerCodArity layer) restLayers) secondLayers)
            (zxpComposeRows currentArity (zxpLayerCodArity layer)
              (zxpLayersCodArity (zxpLayerCodArity layer)
                (zxpCatLayers restLayers secondLayers))
              (zxpLayerDenote layer)
              (zxpLayersDenote (zxpLayerCodArity layer)
                (zxpCatLayers restLayers secondLayers)))
            _
          rw [zxpLayersCodArityCat (zxpLayerCodArity layer) restLayers secondLayers]
          have hLayerAll : ZxpAllWidth (currentArity + zxpLayerCodArity layer)
              (zxpLayerDenote layer) :=
            zxpAllWidthCast (by rw [hDom]) (zxpLayerDenoteWidth layer)
          have hRestAll := zxpLayersDenoteWidth restLayers hRest
          have hSecondAll := zxpLayersDenoteWidth secondLayers hSecond
          have hCatAll : ZxpAllWidth (zxpLayerCodArity layer
              + zxpLayersCodArity (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
                  secondLayers)
              (zxpLayersDenote (zxpLayerCodArity layer)
                (zxpCatLayers restLayers secondLayers)) :=
            zxpAllWidthCast
              (by rw [zxpLayersCodArityCat (zxpLayerCodArity layer) restLayers secondLayers])
              (zxpLayersDenoteWidth (zxpCatLayers restLayers secondLayers)
                (zxpLayersWFCat restLayers secondLayers hRest hSecond))
          have hComposeRestAll := zxpComposeRowsWidth (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            (zxpLayersCodArity (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              secondLayers)
            (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            (zxpLayersDenote (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              secondLayers)
            hRestAll hSecondAll
          have hStep1 := zxpComposeRowsCong currentArity (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              secondLayers)
            hLayerAll hLayerAll hCatAll hComposeRestAll
            (zxpRelEquivRefl currentArity (zxpLayerCodArity layer) (zxpLayerDenote layer))
            (zxpLayersDenoteCat restLayers secondLayers hRest hSecond)
          have hStep2 := zxpRelEquivSymm (zxpComposeRowsAssoc currentArity
            (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            (zxpLayersCodArity (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              secondLayers)
            (zxpLayerDenote layer)
            (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            (zxpLayersDenote (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              secondLayers)
            hLayerAll hRestAll hSecondAll)
          exact zxpRelEquivTrans hStep1 hStep2

/-! ### Whiskering: identity wires left and right of every layer of a window -/

/-- Whisker one layer with wire cells on both sides. -/
def zxpWhiskerLayer (leftWires rightWires : Nat) (layer : List ZxpCell) : List ZxpCell :=
  zxpCatCells (zxpWireCells leftWires) (zxpCatCells layer (zxpWireCells rightWires))

/-- Whisker every layer of a window. -/
def zxpWhiskerLayers (leftWires rightWires : Nat) : List (List ZxpCell) -> List (List ZxpCell)
  | [] => []
  | layer :: restLayers =>
      zxpWhiskerLayer leftWires rightWires layer
        :: zxpWhiskerLayers leftWires rightWires restLayers

theorem zxpWhiskerLayerDomArity (leftWires rightWires : Nat) (layer : List ZxpCell) :
    zxpLayerDomArity (zxpWhiskerLayer leftWires rightWires layer)
      = leftWires + (zxpLayerDomArity layer + rightWires) := by
  show zxpLayerDomArity (zxpCatCells (zxpWireCells leftWires)
      (zxpCatCells layer (zxpWireCells rightWires)))
    = leftWires + (zxpLayerDomArity layer + rightWires)
  rw [zxpCatCellsDomArity, zxpCatCellsDomArity, zxpWireCellsDomArity, zxpWireCellsDomArity]

theorem zxpWhiskerLayerCodArity (leftWires rightWires : Nat) (layer : List ZxpCell) :
    zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires layer)
      = leftWires + (zxpLayerCodArity layer + rightWires) := by
  show zxpLayerCodArity (zxpCatCells (zxpWireCells leftWires)
      (zxpCatCells layer (zxpWireCells rightWires)))
    = leftWires + (zxpLayerCodArity layer + rightWires)
  rw [zxpCatCellsCodArity, zxpCatCellsCodArity, zxpWireCellsCodArity, zxpWireCellsCodArity]

theorem zxpWhiskerLayersCodArity (leftWires rightWires : Nat) :
    (layers : List (List ZxpCell)) -> (currentArity : Nat) ->
    zxpLayersCodArity (leftWires + (currentArity + rightWires))
      (zxpWhiskerLayers leftWires rightWires layers)
      = leftWires + (zxpLayersCodArity currentArity layers + rightWires)
  | [], _currentArity => rfl
  | layer :: restLayers, currentArity => by
      show zxpLayersCodArity
          (zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires layer))
          (zxpWhiskerLayers leftWires rightWires restLayers)
        = leftWires + (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires)
      rw [zxpWhiskerLayerCodArity]
      exact zxpWhiskerLayersCodArity leftWires rightWires restLayers (zxpLayerCodArity layer)

theorem zxpWhiskerLayersWF (leftWires rightWires : Nat) :
    {currentArity : Nat} -> (layers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity layers ->
    ZxpLayersWF (leftWires + (currentArity + rightWires))
      (zxpWhiskerLayers leftWires rightWires layers)
  | currentArity, [], _hWF => ZxpLayersWF.nil (leftWires + (currentArity + rightWires))
  | _currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          refine ZxpLayersWF.cons ?_ ?_
          · rw [zxpWhiskerLayerDomArity, hDom]
          · rw [zxpWhiskerLayerCodArity]
            exact zxpWhiskerLayersWF leftWires rightWires restLayers hRest

/-- One whiskered layer denotes the tensor `id_left (x) (layer (x) id_right)`. -/
theorem zxpWhiskerLayerDenote (leftWires rightWires : Nat) (layer : List ZxpCell) :
    ZxpRelEquiv (leftWires + (zxpLayerDomArity layer + rightWires))
      (leftWires + (zxpLayerCodArity layer + rightWires))
      (zxpLayerDenote (zxpWhiskerLayer leftWires rightWires layer))
      (zxpTensorRows leftWires leftWires
        (zxpLayerDomArity layer + rightWires) (zxpLayerCodArity layer + rightWires)
        (zxpIdRows leftWires)
        (zxpTensorRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
          rightWires rightWires (zxpLayerDenote layer) (zxpIdRows rightWires))) := by
  have hSplitOuter := zxpLayerDenoteCatSplit (zxpWireCells leftWires)
    (zxpCatCells layer (zxpWireCells rightWires))
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity, zxpCatCellsDomArity, zxpCatCellsCodArity,
    zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplitOuter
  have hSplitInner := zxpLayerDenoteCatSplit layer (zxpWireCells rightWires)
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplitInner
  have hWireLeftAll : ZxpAllWidth (leftWires + leftWires)
      (zxpLayerDenote (zxpWireCells leftWires)) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells leftWires))
  have hWireRightAll : ZxpAllWidth (rightWires + rightWires)
      (zxpLayerDenote (zxpWireCells rightWires)) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells rightWires))
  have hInnerCatAll : ZxpAllWidth ((zxpLayerDomArity layer + rightWires)
      + (zxpLayerCodArity layer + rightWires))
      (zxpLayerDenote (zxpCatCells layer (zxpWireCells rightWires))) :=
    zxpAllWidthCast (by rw [zxpCatCellsDomArity, zxpCatCellsCodArity, zxpWireCellsDomArity,
      zxpWireCellsCodArity]) (zxpLayerDenoteWidth (zxpCatCells layer (zxpWireCells rightWires)))
  have hInnerTensorAll := zxpTensorRowsWidth (zxpLayerDomArity layer)
    (zxpLayerCodArity layer) rightWires rightWires (zxpLayerDenote layer)
    (zxpIdRows rightWires) (zxpLayerDenoteWidth layer) (zxpIdRowsWidth rightWires)
  have hInnerChain : ZxpRelEquiv (zxpLayerDomArity layer + rightWires)
      (zxpLayerCodArity layer + rightWires)
      (zxpLayerDenote (zxpCatCells layer (zxpWireCells rightWires)))
      (zxpTensorRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
        rightWires rightWires (zxpLayerDenote layer) (zxpIdRows rightWires)) :=
    zxpRelEquivTrans hSplitInner
      (zxpTensorRowsCong (zxpLayerDomArity layer) (zxpLayerCodArity layer)
        rightWires rightWires (zxpLayerDenoteWidth layer) (zxpLayerDenoteWidth layer)
        hWireRightAll (zxpIdRowsWidth rightWires)
        (zxpRelEquivRefl (zxpLayerDomArity layer) (zxpLayerCodArity layer)
          (zxpLayerDenote layer))
        (zxpWireCellsDenoteId rightWires))
  refine zxpRelEquivTrans hSplitOuter ?_
  exact zxpTensorRowsCong leftWires leftWires (zxpLayerDomArity layer + rightWires)
    (zxpLayerCodArity layer + rightWires)
    hWireLeftAll (zxpIdRowsWidth leftWires) hInnerCatAll hInnerTensorAll
    (zxpWireCellsDenoteId leftWires) hInnerChain

/-- The whiskered window denotes `id_left (x) (window (x) id_right)` — the whisker
functoriality chain, by interchange down the layer list. -/
theorem zxpWhiskerLayersDenote (leftWires rightWires : Nat) :
    {currentArity : Nat} -> (layers : List (List ZxpCell)) ->
    ZxpLayersWF currentArity layers ->
    ZxpRelEquiv (leftWires + (currentArity + rightWires))
      (leftWires + (zxpLayersCodArity currentArity layers + rightWires))
      (zxpLayersDenote (leftWires + (currentArity + rightWires))
        (zxpWhiskerLayers leftWires rightWires layers))
      (zxpTensorRows leftWires leftWires (currentArity + rightWires)
        (zxpLayersCodArity currentArity layers + rightWires)
        (zxpIdRows leftWires)
        (zxpTensorRows currentArity (zxpLayersCodArity currentArity layers)
          rightWires rightWires
          (zxpLayersDenote currentArity layers) (zxpIdRows rightWires)))
  | currentArity, [], _hWF => by
      refine zxpRelEquivSymm ?_
      refine zxpRelEquivTrans (zxpTensorRowsCong leftWires leftWires
        (currentArity + rightWires) (currentArity + rightWires)
        (zxpIdRowsWidth leftWires) (zxpIdRowsWidth leftWires)
        (zxpTensorRowsWidth currentArity currentArity rightWires rightWires
          (zxpIdRows currentArity) (zxpIdRows rightWires)
          (zxpIdRowsWidth currentArity) (zxpIdRowsWidth rightWires))
        (zxpIdRowsWidth (currentArity + rightWires))
        (zxpRelEquivRefl leftWires leftWires (zxpIdRows leftWires))
        (zxpTensorIdSum currentArity rightWires)) ?_
      exact zxpTensorIdSum leftWires (currentArity + rightWires)
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          subst hDom
          show ZxpRelEquiv
            (leftWires + (zxpLayerDomArity layer + rightWires))
            (leftWires
              + (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires))
            (zxpComposeRows (leftWires + (zxpLayerDomArity layer + rightWires))
              (zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires layer))
              (zxpLayersCodArity
                (zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires layer))
                (zxpWhiskerLayers leftWires rightWires restLayers))
              (zxpLayerDenote (zxpWhiskerLayer leftWires rightWires layer))
              (zxpLayersDenote
                (zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires layer))
                (zxpWhiskerLayers leftWires rightWires restLayers)))
            _
          rw [zxpWhiskerLayerCodArity leftWires rightWires layer,
            zxpWhiskerLayersCodArity leftWires rightWires restLayers (zxpLayerCodArity layer)]
          have hLayerAll := zxpLayerDenoteWidth layer
          have hRestAll := zxpLayersDenoteWidth restLayers hRest
          have hIdLeftAll := zxpIdRowsWidth leftWires
          have hIdRightAll := zxpIdRowsWidth rightWires
          have hWhiskLayerAll : ZxpAllWidth
              ((leftWires + (zxpLayerDomArity layer + rightWires))
                + (leftWires + (zxpLayerCodArity layer + rightWires)))
              (zxpLayerDenote (zxpWhiskerLayer leftWires rightWires layer)) :=
            zxpAllWidthCast (by rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity])
              (zxpLayerDenoteWidth (zxpWhiskerLayer leftWires rightWires layer))
          have hWhiskRestAll : ZxpAllWidth
              ((leftWires + (zxpLayerCodArity layer + rightWires))
                + (leftWires + (zxpLayersCodArity (zxpLayerCodArity layer) restLayers
                    + rightWires)))
              (zxpLayersDenote (leftWires + (zxpLayerCodArity layer + rightWires))
                (zxpWhiskerLayers leftWires rightWires restLayers)) :=
            zxpAllWidthCast (by rw [zxpWhiskerLayersCodArity leftWires rightWires restLayers
              (zxpLayerCodArity layer)])
              (zxpLayersDenoteWidth (zxpWhiskerLayers leftWires rightWires restLayers)
                (zxpWhiskerLayersWF leftWires rightWires restLayers hRest))
          have hInnerTensorInAll := zxpTensorRowsWidth (zxpLayerDomArity layer)
            (zxpLayerCodArity layer) rightWires rightWires (zxpLayerDenote layer)
            (zxpIdRows rightWires) hLayerAll hIdRightAll
          have hInnerTensorOutAll := zxpTensorRowsWidth (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers) rightWires rightWires
            (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            (zxpIdRows rightWires) hRestAll hIdRightAll
          have hT1All := zxpTensorRowsWidth leftWires leftWires
            (zxpLayerDomArity layer + rightWires) (zxpLayerCodArity layer + rightWires)
            (zxpIdRows leftWires) _ hIdLeftAll hInnerTensorInAll
          have hT2All := zxpTensorRowsWidth leftWires leftWires
            (zxpLayerCodArity layer + rightWires)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires)
            (zxpIdRows leftWires) _ hIdLeftAll hInnerTensorOutAll
          have hStep1 := zxpComposeRowsCong
            (leftWires + (zxpLayerDomArity layer + rightWires))
            (leftWires + (zxpLayerCodArity layer + rightWires))
            (leftWires + (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires))
            hWhiskLayerAll hT1All hWhiskRestAll hT2All
            (zxpWhiskerLayerDenote leftWires rightWires layer)
            (zxpWhiskerLayersDenote leftWires rightWires restLayers hRest)
          have hStep2 := zxpTensorComposeInterchange leftWires leftWires leftWires
            (zxpLayerDomArity layer + rightWires) (zxpLayerCodArity layer + rightWires)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires)
            (zxpIdRows leftWires) (zxpIdRows leftWires)
            (zxpTensorRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
              rightWires rightWires (zxpLayerDenote layer) (zxpIdRows rightWires))
            (zxpTensorRows (zxpLayerCodArity layer)
              (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              rightWires rightWires
              (zxpLayersDenote (zxpLayerCodArity layer) restLayers) (zxpIdRows rightWires))
            hIdLeftAll hIdLeftAll hInnerTensorInAll hInnerTensorOutAll
          have hInnerInter := zxpTensorComposeInterchange (zxpLayerDomArity layer)
            (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            rightWires rightWires rightWires
            (zxpLayerDenote layer) (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            (zxpIdRows rightWires) (zxpIdRows rightWires)
            hLayerAll hRestAll hIdRightAll hIdRightAll
          have hComposeLayerRestAll := zxpComposeRowsWidth (zxpLayerDomArity layer)
            (zxpLayerCodArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            (zxpLayerDenote layer) (zxpLayersDenote (zxpLayerCodArity layer) restLayers)
            hLayerAll hRestAll
          have hComposeIdRightAll := zxpComposeRowsWidth rightWires rightWires rightWires
            (zxpIdRows rightWires) (zxpIdRows rightWires) hIdRightAll hIdRightAll
          have hInnerFix := zxpRelEquivTrans hInnerInter
            (zxpTensorRowsCong (zxpLayerDomArity layer)
              (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              rightWires rightWires
              hComposeLayerRestAll hComposeLayerRestAll hComposeIdRightAll hIdRightAll
              (zxpRelEquivRefl (zxpLayerDomArity layer)
                (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
                (zxpComposeRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
                  (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
                  (zxpLayerDenote layer)
                  (zxpLayersDenote (zxpLayerCodArity layer) restLayers)))
              (zxpComposeIdLeft rightWires rightWires (zxpIdRows rightWires) hIdRightAll))
          have hComposeIdLeftAll := zxpComposeRowsWidth leftWires leftWires leftWires
            (zxpIdRows leftWires) (zxpIdRows leftWires) hIdLeftAll hIdLeftAll
          have hInnerComposeAll := zxpComposeRowsWidth
            (zxpLayerDomArity layer + rightWires) (zxpLayerCodArity layer + rightWires)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires)
            (zxpTensorRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
              rightWires rightWires (zxpLayerDenote layer) (zxpIdRows rightWires))
            (zxpTensorRows (zxpLayerCodArity layer)
              (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              rightWires rightWires
              (zxpLayersDenote (zxpLayerCodArity layer) restLayers) (zxpIdRows rightWires))
            hInnerTensorInAll hInnerTensorOutAll
          have hFinalTensorAll := zxpTensorRowsWidth (zxpLayerDomArity layer)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
            rightWires rightWires
            (zxpComposeRows (zxpLayerDomArity layer) (zxpLayerCodArity layer)
              (zxpLayersCodArity (zxpLayerCodArity layer) restLayers)
              (zxpLayerDenote layer)
              (zxpLayersDenote (zxpLayerCodArity layer) restLayers))
            (zxpIdRows rightWires) hComposeLayerRestAll hIdRightAll
          have hStep3 := zxpTensorRowsCong leftWires leftWires
            (zxpLayerDomArity layer + rightWires)
            (zxpLayersCodArity (zxpLayerCodArity layer) restLayers + rightWires)
            hComposeIdLeftAll hIdLeftAll hInnerComposeAll hFinalTensorAll
            (zxpComposeIdLeft leftWires leftWires (zxpIdRows leftWires) hIdLeftAll)
            hInnerFix
          exact zxpRelEquivTrans hStep1 (zxpRelEquivTrans hStep2 hStep3)

/-! ### The diagram carrier: source arity plus layer list -/

/-- A phase-free ZX diagram: a source arity and a list of layers (the strict-layer idiom). -/
structure ZxpDiagram where
  sourceArity : Nat
  layers : List (List ZxpCell)

/-- Target arity of a diagram. -/
def zxpDiagramCodArity (diagram : ZxpDiagram) : Nat :=
  zxpLayersCodArity diagram.sourceArity diagram.layers

/-- Well-formedness of a diagram. -/
def ZxpDiagramWF (diagram : ZxpDiagram) : Prop :=
  ZxpLayersWF diagram.sourceArity diagram.layers

/-- Denotation of a diagram: the generator matrix of its F2 linear relation. -/
def zxpDiagramDenote (diagram : ZxpDiagram) : List (List Bool) :=
  zxpLayersDenote diagram.sourceArity diagram.layers

theorem zxpDiagramDenoteWidth (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) :
    ZxpAllWidth (diagram.sourceArity + zxpDiagramCodArity diagram)
      (zxpDiagramDenote diagram) :=
  zxpLayersDenoteWidth diagram.layers hWF

/-- Structural Bool equality on `Nat` (fresh, for the executable well-formedness gate). -/
def zxpNatEqB : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, _secondPred + 1 => false
  | _firstPred + 1, 0 => false
  | firstPred + 1, secondPred + 1 => zxpNatEqB firstPred secondPred

theorem zxpNatEqBSound : (firstValue secondValue : Nat) ->
    zxpNatEqB firstValue secondValue = true -> firstValue = secondValue
  | 0, 0, _hEq => rfl
  | 0, _secondPred + 1, hEq => Bool.noConfusion hEq
  | _firstPred + 1, 0, hEq => Bool.noConfusion hEq
  | firstPred + 1, secondPred + 1, hEq =>
      congrArg (fun innerValue => innerValue + 1) (zxpNatEqBSound firstPred secondPred hEq)

/-- Executable well-formedness check for a layer list. -/
def zxpLayersWFB : Nat -> List (List ZxpCell) -> Bool
  | _currentArity, [] => true
  | currentArity, layer :: restLayers =>
      cond (zxpNatEqB (zxpLayerDomArity layer) currentArity)
        (zxpLayersWFB (zxpLayerCodArity layer) restLayers) false

theorem zxpLayersWFOfB : (currentArity : Nat) -> (layers : List (List ZxpCell)) ->
    zxpLayersWFB currentArity layers = true -> ZxpLayersWF currentArity layers
  | currentArity, [], _hCheck => ZxpLayersWF.nil currentArity
  | currentArity, layer :: restLayers, hCheck => by
      have hCond : cond (zxpNatEqB (zxpLayerDomArity layer) currentArity)
          (zxpLayersWFB (zxpLayerCodArity layer) restLayers) false = true := hCheck
      cases hEq : zxpNatEqB (zxpLayerDomArity layer) currentArity with
      | false =>
          rw [hEq] at hCond
          exact Bool.noConfusion hCond
      | true =>
          rw [hEq] at hCond
          exact ZxpLayersWF.cons (zxpNatEqBSound (zxpLayerDomArity layer) currentArity hEq)
            (zxpLayersWFOfB (zxpLayerCodArity layer) restLayers hCond)

/-- Executable well-formedness check for a diagram. -/
def zxpDiagramWFB (diagram : ZxpDiagram) : Bool :=
  zxpLayersWFB diagram.sourceArity diagram.layers

theorem zxpDiagramWFOfB (diagram : ZxpDiagram) (hCheck : zxpDiagramWFB diagram = true) :
    ZxpDiagramWF diagram :=
  zxpLayersWFOfB diagram.sourceArity diagram.layers hCheck

/-! ### The pad combinator: a window whiskered by wires and framed by context layers -/

/-- Pad a window diagram: whisker every window layer by `leftWires`/`rightWires` wires and
frame the result with context layers before and after. -/
def zxpPadDiagram (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram) : ZxpDiagram :=
  { sourceArity := contextSource
    layers := zxpCatLayers beforeLayers
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers) }

theorem zxpPadDiagramWF (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires))
    (hWindowWF : ZxpDiagramWF window)
    (hAfterWF : ZxpLayersWF (leftWires + (zxpDiagramCodArity window + rightWires))
      afterLayers) :
    ZxpDiagramWF (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
      window) := by
  show ZxpLayersWF contextSource (zxpCatLayers beforeLayers
    (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers))
  refine zxpLayersWFCat beforeLayers
    (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers)
    hBeforeWF ?_
  rw [hBeforeCod]
  refine zxpLayersWFCat (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers
    (zxpWhiskerLayersWF leftWires rightWires window.layers hWindowWF) ?_
  rw [zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
  exact hAfterWF

theorem zxpPadDiagramCodArity (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires)) :
    zxpDiagramCodArity (zxpPadDiagram contextSource leftWires rightWires beforeLayers
        afterLayers window)
      = zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires))
          afterLayers := by
  show zxpLayersCodArity contextSource (zxpCatLayers beforeLayers
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers))
    = zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers
  rw [zxpLayersCodArityCat, zxpLayersCodArityCat, hBeforeCod,
    zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
  rfl

/-- The padded diagram denotes `before ; (id_left (x) (window (x) id_right)) ; after`. -/
theorem zxpPadDiagramDenoteDecomp (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (window.sourceArity + rightWires))
    (hWindowWF : ZxpDiagramWF window)
    (hAfterWF : ZxpLayersWF (leftWires + (zxpDiagramCodArity window + rightWires))
      afterLayers) :
    ZxpRelEquiv contextSource
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
      (zxpDiagramDenote (zxpPadDiagram contextSource leftWires rightWires beforeLayers
        afterLayers window))
      (zxpComposeRows contextSource (leftWires + (window.sourceArity + rightWires))
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires))
          afterLayers)
        (zxpLayersDenote contextSource beforeLayers)
        (zxpComposeRows (leftWires + (window.sourceArity + rightWires))
          (leftWires + (zxpDiagramCodArity window + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires))
            afterLayers)
          (zxpTensorRows leftWires leftWires
            (window.sourceArity + rightWires) (zxpDiagramCodArity window + rightWires)
            (zxpIdRows leftWires)
            (zxpTensorRows window.sourceArity (zxpDiagramCodArity window)
              rightWires rightWires (zxpDiagramDenote window) (zxpIdRows rightWires)))
          (zxpLayersDenote (leftWires + (zxpDiagramCodArity window + rightWires))
            afterLayers))) := by
  have hWhiskerWF := zxpWhiskerLayersWF leftWires rightWires window.layers hWindowWF
  have hMidWF : ZxpLayersWF (zxpLayersCodArity contextSource beforeLayers)
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers) := by
    rw [hBeforeCod]
    refine zxpLayersWFCat (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers
      hWhiskerWF ?_
    rw [zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    exact hAfterWF
  have hOuterCat := zxpLayersDenoteCat beforeLayers
    (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers)
    hBeforeWF hMidWF
  -- normalize the boundary indices of the outer decomposition
  rw [zxpLayersCodArityCat, hBeforeCod,
    zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    at hOuterCat
  have hAfterWFCast : ZxpLayersWF
      (zxpLayersCodArity (leftWires + (window.sourceArity + rightWires))
        (zxpWhiskerLayers leftWires rightWires window.layers)) afterLayers := by
    rw [zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    exact hAfterWF
  have hInnerCat := zxpLayersDenoteCat
    (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers hWhiskerWF hAfterWFCast
  rw [zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    at hInnerCat
  have hBeforeAll : ZxpAllWidth
      (contextSource + (leftWires + (window.sourceArity + rightWires)))
      (zxpLayersDenote contextSource beforeLayers) :=
    zxpAllWidthCast (by rw [hBeforeCod]) (zxpLayersDenoteWidth beforeLayers hBeforeWF)
  have hWhiskerAll : ZxpAllWidth
      ((leftWires + (window.sourceArity + rightWires))
        + (leftWires + (zxpDiagramCodArity window + rightWires)))
      (zxpLayersDenote (leftWires + (window.sourceArity + rightWires))
        (zxpWhiskerLayers leftWires rightWires window.layers)) :=
    zxpAllWidthCast (by
      rw [zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
      rfl)
      (zxpLayersDenoteWidth (zxpWhiskerLayers leftWires rightWires window.layers) hWhiskerWF)
  have hAfterAll := zxpLayersDenoteWidth afterLayers hAfterWF
  have hWindowAll := zxpDiagramDenoteWidth window hWindowWF
  have hInnerTensorAll := zxpTensorRowsWidth window.sourceArity
    (zxpDiagramCodArity window) rightWires rightWires (zxpDiagramDenote window)
    (zxpIdRows rightWires) hWindowAll (zxpIdRowsWidth rightWires)
  have hTensorAll := zxpTensorRowsWidth leftWires leftWires
    (window.sourceArity + rightWires) (zxpDiagramCodArity window + rightWires)
    (zxpIdRows leftWires) _ (zxpIdRowsWidth leftWires) hInnerTensorAll
  have hCatWhiskAfterAll : ZxpAllWidth
      ((leftWires + (window.sourceArity + rightWires))
        + zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires))
            afterLayers)
      (zxpLayersDenote (leftWires + (window.sourceArity + rightWires))
        (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers)) := by
    have hRaw := zxpLayersDenoteWidth
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers)
      (zxpLayersWFCat (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers
        hWhiskerWF hAfterWFCast)
    refine zxpAllWidthCast ?_ hRaw
    rw [zxpLayersCodArityCat,
      zxpWhiskerLayersCodArity leftWires rightWires window.layers window.sourceArity]
    rfl
  have hComposeInnerAll := zxpComposeRowsWidth
    (leftWires + (window.sourceArity + rightWires))
    (leftWires + (zxpDiagramCodArity window + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    (zxpLayersDenote (leftWires + (window.sourceArity + rightWires))
      (zxpWhiskerLayers leftWires rightWires window.layers))
    (zxpLayersDenote (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    hWhiskerAll hAfterAll
  have hComposeInner2All := zxpComposeRowsWidth
    (leftWires + (window.sourceArity + rightWires))
    (leftWires + (zxpDiagramCodArity window + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    (zxpTensorRows leftWires leftWires
      (window.sourceArity + rightWires) (zxpDiagramCodArity window + rightWires)
      (zxpIdRows leftWires)
      (zxpTensorRows window.sourceArity (zxpDiagramCodArity window)
        rightWires rightWires (zxpDiagramDenote window) (zxpIdRows rightWires)))
    (zxpLayersDenote (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    hTensorAll hAfterAll
  refine zxpRelEquivTrans hOuterCat ?_
  refine zxpComposeRowsCong contextSource (leftWires + (window.sourceArity + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    hBeforeAll hBeforeAll hCatWhiskAfterAll hComposeInner2All
    (zxpRelEquivRefl contextSource (leftWires + (window.sourceArity + rightWires))
      (zxpLayersDenote contextSource beforeLayers)) ?_
  refine zxpRelEquivTrans hInnerCat ?_
  exact zxpComposeRowsCong (leftWires + (window.sourceArity + rightWires))
    (leftWires + (zxpDiagramCodArity window + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
    hWhiskerAll hTensorAll hAfterAll hAfterAll
    (zxpWhiskerLayersDenote leftWires rightWires window.layers hWindowWF)
    (zxpRelEquivRefl (leftWires + (zxpDiagramCodArity window + rightWires))
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers)
      (zxpLayersDenote (leftWires + (zxpDiagramCodArity window + rightWires)) afterLayers))

/-! ### The convertibility bundle: boundary agreement + well-formedness + span equality -/

/-- Everything soundness delivers for one convertibility edge: equal boundaries, both sides
well-formed, and denotational span equality. -/
def ZxpConvBundle (firstDiagram secondDiagram : ZxpDiagram) : Prop :=
  firstDiagram.sourceArity = secondDiagram.sourceArity
    /\ zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram
    /\ ZxpDiagramWF firstDiagram /\ ZxpDiagramWF secondDiagram
    /\ ZxpRelEquiv firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
        (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)

theorem zxpConvBundleSymm {firstDiagram secondDiagram : ZxpDiagram}
    (hBundle : ZxpConvBundle firstDiagram secondDiagram) :
    ZxpConvBundle secondDiagram firstDiagram :=
  And.intro hBundle.left.symm
    (And.intro hBundle.right.left.symm
      (And.intro hBundle.right.right.right.left
        (And.intro hBundle.right.right.left
          (zxpRelEquivCast hBundle.left hBundle.right.left
            (zxpRelEquivSymm hBundle.right.right.right.right)))))

theorem zxpConvBundleTrans {firstDiagram secondDiagram thirdDiagram : ZxpDiagram}
    (hFirst : ZxpConvBundle firstDiagram secondDiagram)
    (hSecond : ZxpConvBundle secondDiagram thirdDiagram) :
    ZxpConvBundle firstDiagram thirdDiagram :=
  And.intro (hFirst.left.trans hSecond.left)
    (And.intro (hFirst.right.left.trans hSecond.right.left)
      (And.intro hFirst.right.right.left
        (And.intro hSecond.right.right.right.left
          (zxpRelEquivTrans hFirst.right.right.right.right
            (zxpRelEquivCast hFirst.left.symm hFirst.right.left.symm
              hSecond.right.right.right.right)))))

/-- Kernel-checkable bundle introduction: two executable well-formedness passes, two
boundary equalities, one span-decision pass — everything `rfl` on closed diagrams. -/
theorem zxpConvBundleOfChecks (firstDiagram secondDiagram : ZxpDiagram)
    (hFirstWFB : zxpDiagramWFB firstDiagram = true)
    (hSecondWFB : zxpDiagramWFB secondDiagram = true)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram)
    (hSpan : zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
      = true) :
    ZxpConvBundle firstDiagram secondDiagram :=
  And.intro hSourceEq
    (And.intro hCodEq
      (And.intro (zxpDiagramWFOfB firstDiagram hFirstWFB)
        (And.intro (zxpDiagramWFOfB secondDiagram hSecondWFB)
          (zxpRelEquivOfSpanEqB
            (zxpDiagramDenoteWidth firstDiagram (zxpDiagramWFOfB firstDiagram hFirstWFB))
            (zxpAllWidthCast (by rw [hSourceEq, hCodEq])
              (zxpDiagramDenoteWidth secondDiagram
                (zxpDiagramWFOfB secondDiagram hSecondWFB)))
            hSpan))))

/-! ### THE PUBLISHED ROW SET (Z2-specialized, scalar-free)

Colour dictionary (IB Def 3.6 / Kissinger eq. (2)): ZX-Z = IH-black = COPY, ZX-X = IH-white
= ADD/parity.  Cells: `mu_X = xSpider 2 1`, `eta_X = xSpider 0 1`, `delta_Z = zSpider 1 2`,
`eps_Z = zSpider 1 0`, and the colour mirrors.  Each tag names one published equation; the
lhs/rhs diagrams are CLOSED, so every soundness obligation is one kernel decision. -/

/-- The shipped rewrite rows: one constructor per published equation (see the
presentation-diff table on `zxpCompletenessStatement`). -/
inductive ZxpRowTag : Type where
  | xMonoidAssoc : ZxpRowTag
  | xMonoidComm : ZxpRowTag
  | xMonoidUnit : ZxpRowTag
  | zComonoidCoassoc : ZxpRowTag
  | zComonoidCocomm : ZxpRowTag
  | zComonoidCounit : ZxpRowTag
  | zMonoidAssoc : ZxpRowTag
  | zMonoidComm : ZxpRowTag
  | zMonoidUnit : ZxpRowTag
  | xComonoidCoassoc : ZxpRowTag
  | xComonoidCocomm : ZxpRowTag
  | xComonoidCounit : ZxpRowTag
  | bialgCopyMult : ZxpRowTag
  | bialgSquare : ZxpRowTag
  | bialgUnitCopy : ZxpRowTag
  | bialgBone : ZxpRowTag
  | bialgCopyMultDual : ZxpRowTag
  | bialgSquareDual : ZxpRowTag
  | bialgUnitCopyDual : ZxpRowTag
  | bialgBoneDual : ZxpRowTag
  | hopf : ZxpRowTag
  | boneX : ZxpRowTag
  | boneZ : ZxpRowTag
  | frobeniusXLeft : ZxpRowTag
  | frobeniusXRight : ZxpRowTag
  | frobeniusZLeft : ZxpRowTag
  | frobeniusZRight : ZxpRowTag
  | specialZ : ZxpRowTag
  | specialX : ZxpRowTag
  | cupCoincide : ZxpRowTag
  | capCoincide : ZxpRowTag
  | zIdentitySpider : ZxpRowTag
  | xIdentitySpider : ZxpRowTag

/-- Left-hand side of each published row. -/
def zxpRowLhs : ZxpRowTag -> ZxpDiagram
  | ZxpRowTag.xMonoidAssoc =>
      { sourceArity := 3
        layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.xMonoidComm =>
      { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.xMonoidUnit =>
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 0 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.zComonoidCoassoc =>
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 1 2, ZxpCell.wire]] }
  | ZxpRowTag.zComonoidCocomm =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.crossing]] }
  | ZxpRowTag.zComonoidCounit =>
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 1 0, ZxpCell.wire]] }
  | ZxpRowTag.zMonoidAssoc =>
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.zMonoidComm =>
      { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.zMonoidUnit =>
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 0 1, ZxpCell.wire], [ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.xComonoidCoassoc =>
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 2], [ZxpCell.xSpider 1 2, ZxpCell.wire]] }
  | ZxpRowTag.xComonoidCocomm =>
      { sourceArity := 1, layers := [[ZxpCell.xSpider 1 2], [ZxpCell.crossing]] }
  | ZxpRowTag.xComonoidCounit =>
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 2], [ZxpCell.xSpider 1 0, ZxpCell.wire]] }
  | ZxpRowTag.bialgCopyMult =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 0]] }
  | ZxpRowTag.bialgSquare =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.bialgUnitCopy =>
      { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.bialgBone =>
      { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] }
  | ZxpRowTag.bialgCopyMultDual =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.xSpider 1 0]] }
  | ZxpRowTag.bialgSquareDual =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.bialgUnitCopyDual =>
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.bialgBoneDual =>
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.xSpider 1 0]] }
  | ZxpRowTag.hopf =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.boneX =>
      { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 1 0]] }
  | ZxpRowTag.boneZ =>
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 0]] }
  | ZxpRowTag.frobeniusXLeft =>
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.frobeniusXRight =>
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
  | ZxpRowTag.frobeniusZLeft =>
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.frobeniusZRight =>
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 1, ZxpCell.wire]] }
  | ZxpRowTag.specialZ =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.specialX =>
      { sourceArity := 1, layers := [[ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.cupCoincide =>
      { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.capCoincide =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 0]] }
  | ZxpRowTag.zIdentitySpider =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 1]] }
  | ZxpRowTag.xIdentitySpider =>
      { sourceArity := 1, layers := [[ZxpCell.xSpider 1 1]] }

/-- Right-hand side of each published row. -/
def zxpRowRhs : ZxpRowTag -> ZxpDiagram
  | ZxpRowTag.xMonoidAssoc =>
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.xSpider 2 1], [ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.xMonoidComm =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.xMonoidUnit =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.zComonoidCoassoc =>
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.zComonoidCocomm =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.zComonoidCounit =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.zMonoidAssoc =>
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 2 1], [ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.zMonoidComm =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.zMonoidUnit =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.xComonoidCoassoc =>
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 2], [ZxpCell.wire, ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.xComonoidCocomm =>
      { sourceArity := 1, layers := [[ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.xComonoidCounit =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.bialgCopyMult =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 1 0, ZxpCell.zSpider 1 0]] }
  | ZxpRowTag.bialgSquare =>
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1]] }
  | ZxpRowTag.bialgUnitCopy =>
      { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] }
  | ZxpRowTag.bialgBone =>
      { sourceArity := 0, layers := [] }
  | ZxpRowTag.bialgCopyMultDual =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] }
  | ZxpRowTag.bialgSquareDual =>
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 1 2, ZxpCell.xSpider 1 2],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 2 1, ZxpCell.zSpider 2 1]] }
  | ZxpRowTag.bialgUnitCopyDual =>
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1]] }
  | ZxpRowTag.bialgBoneDual =>
      { sourceArity := 0, layers := [] }
  | ZxpRowTag.hopf =>
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 0], [ZxpCell.xSpider 0 1]] }
  | ZxpRowTag.boneX =>
      { sourceArity := 0, layers := [] }
  | ZxpRowTag.boneZ =>
      { sourceArity := 0, layers := [] }
  | ZxpRowTag.frobeniusXLeft =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.frobeniusXRight =>
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] }
  | ZxpRowTag.frobeniusZLeft =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.frobeniusZRight =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.specialZ =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.specialX =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.cupCoincide =>
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] }
  | ZxpRowTag.capCoincide =>
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 0]] }
  | ZxpRowTag.zIdentitySpider =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }
  | ZxpRowTag.xIdentitySpider =>
      { sourceArity := 1, layers := [[ZxpCell.wire]] }

/-- SOUNDNESS OF EVERY SHIPPED ROW, kernel-decided: for each tag, both sides are executably
well-formed, share boundaries, and pass the mutual-reduction span decision — all by `rfl`. -/
theorem zxpRowBundle : (tag : ZxpRowTag) ->
    ZxpConvBundle (zxpRowLhs tag) (zxpRowRhs tag)
  | ZxpRowTag.xMonoidAssoc => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xMonoidComm => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xMonoidUnit => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zComonoidCoassoc => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zComonoidCocomm => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zComonoidCounit => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zMonoidAssoc => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zMonoidComm => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zMonoidUnit => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xComonoidCoassoc => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xComonoidCocomm => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xComonoidCounit => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgCopyMult => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgSquare => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgUnitCopy => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgBone => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgCopyMultDual => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgSquareDual => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgUnitCopyDual => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.bialgBoneDual => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.hopf => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.boneX => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.boneZ => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.frobeniusXLeft => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.frobeniusXRight => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.frobeniusZLeft => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.frobeniusZRight => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.specialZ => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.specialX => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.cupCoincide => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.capCoincide => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.zIdentitySpider => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl
  | ZxpRowTag.xIdentitySpider => zxpConvBundleOfChecks _ _ rfl rfl rfl rfl rfl

/-! ### Degenerate-pad identities (empty context dissolves) -/

theorem zxpCatCellsNilRight : (cells : List ZxpCell) -> zxpCatCells cells [] = cells
  | [] => rfl
  | headCell :: restCells =>
      congrArg (fun tailCells => headCell :: tailCells) (zxpCatCellsNilRight restCells)

theorem zxpCatLayersNilRight : (layers : List (List ZxpCell)) -> zxpCatLayers layers [] = layers
  | [] => rfl
  | headLayer :: restLayers =>
      congrArg (fun tailLayers => headLayer :: tailLayers) (zxpCatLayersNilRight restLayers)

theorem zxpWhiskerLayersZero : (layers : List (List ZxpCell)) ->
    zxpWhiskerLayers 0 0 layers = layers
  | [] => rfl
  | layer :: restLayers => by
      show zxpWhiskerLayer 0 0 layer :: zxpWhiskerLayers 0 0 restLayers = layer :: restLayers
      have hLayer : zxpWhiskerLayer 0 0 layer = layer := zxpCatCellsNilRight layer
      rw [hLayer, zxpWhiskerLayersZero restLayers]

theorem zxpPadDiagramIdentityAt (contextSource : Nat) (window : ZxpDiagram)
    (hSource : window.sourceArity = contextSource) :
    zxpPadDiagram contextSource 0 0 [] [] window = window := by
  show ZxpDiagram.mk contextSource (zxpCatLayers (zxpWhiskerLayers 0 0 window.layers) [])
    = window
  rw [zxpWhiskerLayersZero window.layers, zxpCatLayersNilRight window.layers, <- hSource]

/-! ### Window moves: a published row, or a layer split (exchange derived from splits) -/

/-- A window move: either one published row, or splitting one layer into two sequential
whisker-padded halves (from which the exchange law is derived). -/
inductive ZxpWindowMove : ZxpDiagram -> ZxpDiagram -> Prop where
  | row (tag : ZxpRowTag) : ZxpWindowMove (zxpRowLhs tag) (zxpRowRhs tag)
  | splitLayer (leftCells rightCells : List ZxpCell) :
      ZxpWindowMove
        { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
          layers := [zxpCatCells leftCells rightCells] }
        { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
          layers := [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
            zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] }

/-- Soundness of the layer-split move: the merged layer and its two sequential halves
denote the same relation (THE EXCHANGE DERIVATION, by interchange + unit collapses). -/
theorem zxpSplitLayerBundle (leftCells rightCells : List ZxpCell) :
    ZxpConvBundle
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells rightCells] }
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] } := by
  have hDenLAll := zxpLayerDenoteWidth leftCells
  have hDenRAll := zxpLayerDenoteWidth rightCells
  have hL1DomEq : zxpLayerDomArity
      (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)))
      = zxpLayerDomArity leftCells + zxpLayerDomArity rightCells := by
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  have hL1CodEq : zxpLayerCodArity
      (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)))
      = zxpLayerCodArity leftCells + zxpLayerDomArity rightCells := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  have hL2DomEq : zxpLayerDomArity
      (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells)
      = zxpLayerCodArity leftCells + zxpLayerDomArity rightCells := by
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  have hL2CodEq : zxpLayerCodArity
      (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells)
      = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  have hMergedAll : ZxpAllWidth
      ((zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        + zxpLayerCodArity (zxpCatCells leftCells rightCells))
      (zxpLayerDenote (zxpCatCells leftCells rightCells)) :=
    zxpAllWidthCast (by rw [zxpCatCellsDomArity])
      (zxpLayerDenoteWidth (zxpCatCells leftCells rightCells))
  have hL1All : ZxpAllWidth
      ((zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        + (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells))
      (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)))) :=
    zxpAllWidthCast (by rw [hL1DomEq, hL1CodEq])
      (zxpLayerDenoteWidth (zxpCatCells leftCells (zxpWireCells
        (zxpLayerDomArity rightCells))))
  have hL2All : ZxpAllWidth
      ((zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
        + (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
      (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells)) :=
    zxpAllWidthCast (by rw [hL2DomEq, hL2CodEq])
      (zxpLayerDenoteWidth (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
        rightCells))
  -- the merged side collapses to the tensor of the two cell lists
  have hA : ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity (zxpCatCells leftCells rightCells))
      (zxpLayersDenote (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        [zxpCatCells leftCells rightCells])
      (zxpLayerDenote (zxpCatCells leftCells rightCells)) :=
    zxpComposeIdRight (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity (zxpCatCells leftCells rightCells))
      (zxpLayerDenote (zxpCatCells leftCells rightCells)) hMergedAll
  have hW1 : ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayersDenote (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        [zxpCatCells leftCells rightCells])
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote leftCells) (zxpLayerDenote rightCells)) :=
    zxpRelEquivTrans
      (zxpRelEquivCast rfl (zxpCatCellsCodArity leftCells rightCells) hA)
      (zxpLayerDenoteCatSplit leftCells rightCells)
  -- the split side: strip the trailing identity, split both layers, interchange
  have hCEq : zxpLayersDenote (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
        zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells]
      = zxpComposeRows (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
          (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
          (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
          (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells
            (zxpLayerDomArity rightCells))))
          (zxpComposeRows (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
            (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
            (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
            (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
              rightCells))
            (zxpIdRows (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))) := by
    show zxpComposeRows (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerCodArity (zxpCatCells leftCells (zxpWireCells
          (zxpLayerDomArity rightCells))))
        (zxpLayerCodArity (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
          rightCells))
        (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells))))
        (zxpComposeRows
          (zxpLayerCodArity (zxpCatCells leftCells (zxpWireCells
            (zxpLayerDomArity rightCells))))
          (zxpLayerCodArity (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
            rightCells))
          (zxpLayerCodArity (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
            rightCells))
          (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
            rightCells))
          (zxpIdRows (zxpLayerCodArity (zxpCatCells (zxpWireCells
            (zxpLayerCodArity leftCells)) rightCells))))
      = _
    rw [hL1CodEq, hL2CodEq]
  have hSubA : ZxpRelEquiv (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpComposeRows (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
          rightCells))
        (zxpIdRows (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)))
      (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
        rightCells)) :=
    zxpComposeIdRight (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells))
      hL2All
  have hCompInnerAll := zxpComposeRowsWidth
    (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells))
    (zxpIdRows (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
    hL2All (zxpIdRowsWidth (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
  have hSubB : ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayersDenote (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells])
      (zxpComposeRows (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells
          (zxpLayerDomArity rightCells))))
        (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
          rightCells))) := by
    rw [hCEq]
    exact zxpComposeRowsCong (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      hL1All hL1All hCompInnerAll hL2All
      (zxpRelEquivRefl (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
        (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells
          (zxpLayerDomArity rightCells)))))
      hSubA
  have hSplitL1 := zxpLayerDenoteCatSplit leftCells
    (zxpWireCells (zxpLayerDomArity rightCells))
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplitL1
  have hSplitL2 := zxpLayerDenoteCatSplit (zxpWireCells (zxpLayerCodArity leftCells))
    rightCells
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplitL2
  have hWireDrAll : ZxpAllWidth
      (zxpLayerDomArity rightCells + zxpLayerDomArity rightCells)
      (zxpLayerDenote (zxpWireCells (zxpLayerDomArity rightCells))) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells (zxpLayerDomArity rightCells)))
  have hWireClAll : ZxpAllWidth
      (zxpLayerCodArity leftCells + zxpLayerCodArity leftCells)
      (zxpLayerDenote (zxpWireCells (zxpLayerCodArity leftCells))) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells (zxpLayerCodArity leftCells)))
  have hFullL1 : ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerDenote (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells))))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerDomArity rightCells)
        (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerDomArity rightCells))) :=
    zxpRelEquivTrans hSplitL1
      (zxpTensorRowsCong (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerDomArity rightCells)
        hDenLAll hDenLAll hWireDrAll (zxpIdRowsWidth (zxpLayerDomArity rightCells))
        (zxpRelEquivRefl (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
          (zxpLayerDenote leftCells))
        (zxpWireCellsDenoteId (zxpLayerDomArity rightCells)))
  have hFullL2 : ZxpRelEquiv (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerDenote (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells))
      (zxpTensorRows (zxpLayerCodArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpIdRows (zxpLayerCodArity leftCells)) (zxpLayerDenote rightCells)) :=
    zxpRelEquivTrans hSplitL2
      (zxpTensorRowsCong (zxpLayerCodArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        hWireClAll (zxpIdRowsWidth (zxpLayerCodArity leftCells)) hDenRAll hDenRAll
        (zxpWireCellsDenoteId (zxpLayerCodArity leftCells))
        (zxpRelEquivRefl (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
          (zxpLayerDenote rightCells)))
  have hT1All := zxpTensorRowsWidth (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerDomArity rightCells)
    (zxpLayerDomArity rightCells) (zxpLayerDenote leftCells)
    (zxpIdRows (zxpLayerDomArity rightCells)) hDenLAll
    (zxpIdRowsWidth (zxpLayerDomArity rightCells))
  have hT2All := zxpTensorRowsWidth (zxpLayerCodArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerDomArity rightCells)
    (zxpLayerCodArity rightCells) (zxpIdRows (zxpLayerCodArity leftCells))
    (zxpLayerDenote rightCells) (zxpIdRowsWidth (zxpLayerCodArity leftCells)) hDenRAll
  have hSubC := zxpComposeRowsCong
    (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    hL1All hT1All hL2All hT2All hFullL1 hFullL2
  have hSubD := zxpTensorComposeInterchange (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerCodArity leftCells)
    (zxpLayerDomArity rightCells) (zxpLayerDomArity rightCells)
    (zxpLayerCodArity rightCells)
    (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerCodArity leftCells))
    (zxpIdRows (zxpLayerDomArity rightCells)) (zxpLayerDenote rightCells)
    hDenLAll (zxpIdRowsWidth (zxpLayerCodArity leftCells))
    (zxpIdRowsWidth (zxpLayerDomArity rightCells)) hDenRAll
  have hComposeLIdAll := zxpComposeRowsWidth (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerCodArity leftCells)
    (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerCodArity leftCells))
    hDenLAll (zxpIdRowsWidth (zxpLayerCodArity leftCells))
  have hComposeIdRAll := zxpComposeRowsWidth (zxpLayerDomArity rightCells)
    (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
    (zxpIdRows (zxpLayerDomArity rightCells)) (zxpLayerDenote rightCells)
    (zxpIdRowsWidth (zxpLayerDomArity rightCells)) hDenRAll
  have hSubE := zxpTensorRowsCong (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerDomArity rightCells)
    (zxpLayerCodArity rightCells)
    hComposeLIdAll hDenLAll hComposeIdRAll hDenRAll
    (zxpComposeIdRight (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
      (zxpLayerDenote leftCells) hDenLAll)
    (zxpComposeIdLeft (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerDenote rightCells) hDenRAll)
  have hW2 := zxpRelEquivTrans hSubB
    (zxpRelEquivTrans hSubC (zxpRelEquivTrans hSubD hSubE))
  refine And.intro rfl (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  · show zxpLayerCodArity (zxpCatCells leftCells rightCells)
      = zxpLayersCodArity (zxpLayerCodArity (zxpCatCells leftCells
          (zxpWireCells (zxpLayerDomArity rightCells))))
        [zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells]
    show zxpLayerCodArity (zxpCatCells leftCells rightCells)
      = zxpLayerCodArity (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells))
          rightCells)
    rw [zxpCatCellsCodArity, hL2CodEq]
  · exact ZxpLayersWF.cons (zxpCatCellsDomArity leftCells rightCells)
      (ZxpLayersWF.nil (zxpLayerCodArity (zxpCatCells leftCells rightCells)))
  · refine ZxpLayersWF.cons hL1DomEq (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
    rw [hL2DomEq, hL1CodEq]
  · exact zxpRelEquivCast rfl (zxpCatCellsCodArity leftCells rightCells).symm
      (zxpRelEquivTrans hW1 (zxpRelEquivSymm hW2))

/-- Every window move is sound (bundle form). -/
theorem zxpWindowMoveBundle {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxpWindowMove firstWindow secondWindow) :
    ZxpConvBundle firstWindow secondWindow := by
  cases hMove with
  | row tag => exact zxpRowBundle tag
  | splitLayer leftCells rightCells => exact zxpSplitLayerBundle leftCells rightCells

/-! ### The rewriting step and the boundary-indexed congruence -/

/-- One rewriting step: a window move fired inside a padding context (wire whiskering plus
before/after context layers, with the boundary-fit hypotheses carried by the constructor). -/
inductive ZxpStep : ZxpDiagram -> ZxpDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List ZxpCell))
      {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxpWindowMove firstWindow secondWindow)
      (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
      (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : ZxpLayersWF
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
      ZxpStep
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Soundness of one padded step. -/
theorem zxpStepBundle {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxpStep firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
    rename_i firstWindow secondWindow
    have hWindowBundle := zxpWindowMoveBundle hMove
    have hSourceEq : firstWindow.sourceArity = secondWindow.sourceArity :=
      hWindowBundle.left
    have hCodEq : zxpDiagramCodArity firstWindow = zxpDiagramCodArity secondWindow :=
      hWindowBundle.right.left
    have hFirstWF : ZxpDiagramWF firstWindow := hWindowBundle.right.right.left
    have hSecondWF : ZxpDiagramWF secondWindow := hWindowBundle.right.right.right.left
    have hEquiv := hWindowBundle.right.right.right.right
    have hBeforeCod2 : zxpLayersCodArity contextSource beforeLayers
        = leftWires + (secondWindow.sourceArity + rightWires) := by
      rw [hBeforeCod, hSourceEq]
    have hAfterWF2 : ZxpLayersWF
        (leftWires + (zxpDiagramCodArity secondWindow + rightWires)) afterLayers := by
      rw [<- hCodEq]
      exact hAfterWF
    have hPadWF1 := zxpPadDiagramWF contextSource leftWires rightWires beforeLayers
      afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
    have hPadWF2 := zxpPadDiagramWF contextSource leftWires rightWires beforeLayers
      afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
    have hDecomp1 := zxpPadDiagramDenoteDecomp contextSource leftWires rightWires
      beforeLayers afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
    have hDecomp2 := zxpPadDiagramDenoteDecomp contextSource leftWires rightWires
      beforeLayers afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
    rw [<- hSourceEq, <- hCodEq] at hDecomp2
    -- the middle congruence: swap the window denotation inside the decomposed form
    have hBeforeAll : ZxpAllWidth
        (contextSource + (leftWires + (firstWindow.sourceArity + rightWires)))
        (zxpLayersDenote contextSource beforeLayers) :=
      zxpAllWidthCast (by rw [hBeforeCod]) (zxpLayersDenoteWidth beforeLayers hBeforeWF)
    have hAfterAll := zxpLayersDenoteWidth afterLayers hAfterWF
    have hFirstDenAll := zxpDiagramDenoteWidth firstWindow hFirstWF
    have hSecondDenAll : ZxpAllWidth
        (firstWindow.sourceArity + zxpDiagramCodArity firstWindow)
        (zxpDiagramDenote secondWindow) :=
      zxpAllWidthCast (by rw [hSourceEq, hCodEq])
        (zxpDiagramDenoteWidth secondWindow hSecondWF)
    have hIdLeftAll := zxpIdRowsWidth leftWires
    have hIdRightAll := zxpIdRowsWidth rightWires
    have hInner1All := zxpTensorRowsWidth firstWindow.sourceArity
      (zxpDiagramCodArity firstWindow) rightWires rightWires
      (zxpDiagramDenote firstWindow) (zxpIdRows rightWires) hFirstDenAll hIdRightAll
    have hInner2All := zxpTensorRowsWidth firstWindow.sourceArity
      (zxpDiagramCodArity firstWindow) rightWires rightWires
      (zxpDiagramDenote secondWindow) (zxpIdRows rightWires) hSecondDenAll hIdRightAll
    have hTensor1All := zxpTensorRowsWidth leftWires leftWires
      (firstWindow.sourceArity + rightWires)
      (zxpDiagramCodArity firstWindow + rightWires) (zxpIdRows leftWires) _
      hIdLeftAll hInner1All
    have hTensor2All := zxpTensorRowsWidth leftWires leftWires
      (firstWindow.sourceArity + rightWires)
      (zxpDiagramCodArity firstWindow + rightWires) (zxpIdRows leftWires) _
      hIdLeftAll hInner2All
    have hMiddle : ZxpRelEquiv (leftWires + (firstWindow.sourceArity + rightWires))
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        (zxpTensorRows leftWires leftWires
          (firstWindow.sourceArity + rightWires)
          (zxpDiagramCodArity firstWindow + rightWires)
          (zxpIdRows leftWires)
          (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
            rightWires rightWires (zxpDiagramDenote firstWindow) (zxpIdRows rightWires)))
        (zxpTensorRows leftWires leftWires
          (firstWindow.sourceArity + rightWires)
          (zxpDiagramCodArity firstWindow + rightWires)
          (zxpIdRows leftWires)
          (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
            rightWires rightWires (zxpDiagramDenote secondWindow)
            (zxpIdRows rightWires))) :=
      zxpTensorRowsCong leftWires leftWires (firstWindow.sourceArity + rightWires)
        (zxpDiagramCodArity firstWindow + rightWires)
        hIdLeftAll hIdLeftAll hInner1All hInner2All
        (zxpRelEquivRefl leftWires leftWires (zxpIdRows leftWires))
        (zxpTensorRowsCong firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
          rightWires rightWires hFirstDenAll hSecondDenAll hIdRightAll hIdRightAll
          hEquiv
          (zxpRelEquivRefl rightWires rightWires (zxpIdRows rightWires)))
    have hCompose1All := zxpComposeRowsWidth
      (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers) _
      (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hTensor1All hAfterAll
    have hCompose2All := zxpComposeRowsWidth
      (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers) _
      (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hTensor2All hAfterAll
    have hMidCong : ZxpRelEquiv contextSource
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          afterLayers)
        (zxpComposeRows contextSource (leftWires + (firstWindow.sourceArity + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          (zxpLayersDenote contextSource beforeLayers)
          (zxpComposeRows (leftWires + (firstWindow.sourceArity + rightWires))
            (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers)
            (zxpTensorRows leftWires leftWires
              (firstWindow.sourceArity + rightWires)
              (zxpDiagramCodArity firstWindow + rightWires)
              (zxpIdRows leftWires)
              (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
                rightWires rightWires (zxpDiagramDenote firstWindow)
                (zxpIdRows rightWires)))
            (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers)))
        (zxpComposeRows contextSource (leftWires + (firstWindow.sourceArity + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          (zxpLayersDenote contextSource beforeLayers)
          (zxpComposeRows (leftWires + (firstWindow.sourceArity + rightWires))
            (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers)
            (zxpTensorRows leftWires leftWires
              (firstWindow.sourceArity + rightWires)
              (zxpDiagramCodArity firstWindow + rightWires)
              (zxpIdRows leftWires)
              (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
                rightWires rightWires (zxpDiagramDenote secondWindow)
                (zxpIdRows rightWires)))
            (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers))) :=
      zxpComposeRowsCong contextSource (leftWires + (firstWindow.sourceArity + rightWires))
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          afterLayers)
        hBeforeAll hBeforeAll hCompose1All hCompose2All
        (zxpRelEquivRefl contextSource
          (leftWires + (firstWindow.sourceArity + rightWires))
          (zxpLayersDenote contextSource beforeLayers))
        (zxpComposeRowsCong (leftWires + (firstWindow.sourceArity + rightWires))
          (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          hTensor1All hTensor2All hAfterAll hAfterAll hMiddle
          (zxpRelEquivRefl (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers)
            (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
              afterLayers)))
    refine And.intro rfl (And.intro ?_ (And.intro hPadWF1 (And.intro hPadWF2 ?_)))
    · rw [zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow hBeforeCod,
        zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow hBeforeCod2, hCodEq]
    · refine zxpRelEquivCast rfl
        (zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow hBeforeCod).symm ?_
      exact zxpRelEquivTrans hDecomp1
        (zxpRelEquivTrans hMidCong (zxpRelEquivSymm hDecomp2))

/-- The boundary-indexed congruence: steps, reflexivity on well-formed diagrams, symmetry,
transitivity (the groupoid moves). -/
inductive ZxpConv : ZxpDiagram -> ZxpDiagram -> Prop where
  | step {firstDiagram secondDiagram : ZxpDiagram}
      (hStep : ZxpStep firstDiagram secondDiagram) : ZxpConv firstDiagram secondDiagram
  | refl (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) : ZxpConv diagram diagram
  | symm {firstDiagram secondDiagram : ZxpDiagram}
      (hConv : ZxpConv firstDiagram secondDiagram) : ZxpConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : ZxpDiagram}
      (hFirst : ZxpConv firstDiagram secondDiagram)
      (hSecond : ZxpConv secondDiagram thirdDiagram) : ZxpConv firstDiagram thirdDiagram

/-- SOUNDNESS of the congruence: convertible diagrams share boundaries, are well-formed,
and denote the same F2 linear relation. -/
theorem zxpConvSound {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact zxpStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (zxpRelEquivRefl diagram.sourceArity (zxpDiagramCodArity diagram)
          (zxpDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact zxpConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact zxpConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE: convertibility forces the executable span decision to fire
`true` — so a kernel-computed `false` refutes convertibility outright. -/
theorem zxpConvSpanEqB {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
      = true := by
  have hBundle := zxpConvSound hConv
  exact zxpSpanEqBOfRelEquiv
    (zxpDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (zxpAllWidthCast (by rw [hBundle.left, hBundle.right.left])
      (zxpDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-- Every published row is one `ZxpConv` step on the nose (empty context dissolves). -/
theorem zxpRowConv (tag : ZxpRowTag) : ZxpConv (zxpRowLhs tag) (zxpRowRhs tag) := by
  have hStep := ZxpStep.pad (zxpRowLhs tag).sourceArity 0 0 [] []
    (ZxpWindowMove.row tag) (ZxpLayersWF.nil (zxpRowLhs tag).sourceArity)
    (Nat.zero_add ((zxpRowLhs tag).sourceArity + 0)).symm
    (ZxpLayersWF.nil (0 + (zxpDiagramCodArity (zxpRowLhs tag) + 0)))
  rw [zxpPadDiagramIdentityAt (zxpRowLhs tag).sourceArity (zxpRowLhs tag) rfl,
    zxpPadDiagramIdentityAt (zxpRowLhs tag).sourceArity (zxpRowRhs tag)
      (zxpRowBundle tag).left.symm] at hStep
  exact ZxpConv.step hStep

/-! ### Fires: the signature facts, kernel-decided, with FALSE cases -/

/-- THE HOPF FIRE (row 11): copy-then-add equals delete-then-zero — the signature
phase-free fact, kernel-decided on the denotations. -/
theorem zxpHopfFire :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.hopf))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.hopf)) = true := rfl

/-- The Hopf law as a one-step derivation in the congruence. -/
theorem zxpHopfConv : ZxpConv (zxpRowLhs ZxpRowTag.hopf) (zxpRowRhs ZxpRowTag.hopf) :=
  zxpRowConv ZxpRowTag.hopf

/-- The bialgebra square (A8) fire, kernel-decided. -/
theorem zxpBialgebraSquareFire :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.bialgSquare))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.bialgSquare)) = true := rfl

/-- Two chained Z multiplication spiders (a fusable cluster). -/
def zxpZChainedPairDiagram : ZxpDiagram :=
  { sourceArity := 3
    layers := [[ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 1]] }

/-- The fused 3->1 Z spider. -/
def zxpZFusedTripleDiagram : ZxpDiagram :=
  { sourceArity := 3, layers := [[ZxpCell.zSpider 3 1]] }

/-- Two chained X multiplication spiders (a fusable cluster). -/
def zxpXChainedPairDiagram : ZxpDiagram :=
  { sourceArity := 3
    layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }

/-- The fused 3->1 X spider. -/
def zxpXFusedTripleDiagram : ZxpDiagram :=
  { sourceArity := 3, layers := [[ZxpCell.xSpider 3 1]] }

/-- Z-spider fusion (derived family, Kissinger (sp)): two chained copy spiders denote the
one fused spider — semantic fire at the 3->1 instance. -/
theorem zxpZFusionFire :
    zxpSpanEqB (zxpDiagramDenote zxpZChainedPairDiagram)
      (zxpDiagramDenote zxpZFusedTripleDiagram) = true := rfl

/-- X-spider fusion (derived family, Kissinger (sp)): two chained parity spiders denote
the one fused spider — semantic fire at the 3->1 instance. -/
theorem zxpXFusionFire :
    zxpSpanEqB (zxpDiagramDenote zxpXChainedPairDiagram)
      (zxpDiagramDenote zxpXFusedTripleDiagram) = true := rfl

/-- The Z unit state (the full line, |0>+|1>). -/
def zxpZUnitDiagram : ZxpDiagram :=
  { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] }

/-- The X unit state (the zero subspace, |0>). -/
def zxpXUnitDiagram : ZxpDiagram :=
  { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1]] }

/-- FALSE CASE: the Z and X units denote DIFFERENT subspaces of F2^1 — the kernel decision
fires `false`. -/
theorem zxpZUnitXUnitSpanDistinct :
    zxpSpanEqB (zxpDiagramDenote zxpZUnitDiagram) (zxpDiagramDenote zxpXUnitDiagram)
      = false := rfl

/-- NEGATIVE DIRECTION: distinct spans refute convertibility (via the refutation bridge). -/
theorem zxpZUnitXUnitNotConv : Not (ZxpConv zxpZUnitDiagram zxpXUnitDiagram) :=
  fun hConv =>
    Bool.noConfusion ((zxpConvSpanEqB hConv).symm.trans zxpZUnitXUnitSpanDistinct)

/-- The adjacent crossing as a diagram. -/
def zxpCrossingDiagram : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.crossing]] }

/-- Two parallel wires as a diagram. -/
def zxpParallelWiresDiagram : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.wire]] }

/-- FALSE CASE: the crossing is NOT the identity — the kernel decision separates them. -/
theorem zxpCrossingWiresSpanDistinct :
    zxpSpanEqB (zxpDiagramDenote zxpCrossingDiagram)
      (zxpDiagramDenote zxpParallelWiresDiagram) = false := rfl

/-- NEGATIVE DIRECTION: the crossing is not convertible to the parallel wires. -/
theorem zxpCrossingWiresNotConv :
    Not (ZxpConv zxpCrossingDiagram zxpParallelWiresDiagram) :=
  fun hConv =>
    Bool.noConfusion ((zxpConvSpanEqB hConv).symm.trans zxpCrossingWiresSpanDistinct)

/-- SCALAR COLLAPSE (pitfall 2 of the brief): F2^0 has exactly one subspace, so ALL
closed (0 -> 0) relations are equal — the semantics validates the scalar-erased calculus
only, exactly the IB "up to scalar" reading. -/
theorem zxpScalarCollapse (firstRows secondRows : List (List Bool))
    (_hFirstAll : ZxpAllWidth 0 firstRows) (_hSecondAll : ZxpAllWidth 0 secondRows) :
    ZxpRelEquiv 0 0 firstRows secondRows := by
  intro domVec codVec
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomNil := zxpLengthZeroNil domVec hPair.left
    have hCodNil := zxpLengthZeroNil codVec hPair.right.left
    subst hDomNil
    subst hCodNil
    exact And.intro rfl (And.intro rfl ZxpMemSpan.zero)
  · intro hPair
    have hDomNil := zxpLengthZeroNil domVec hPair.left
    have hCodNil := zxpLengthZeroNil codVec hPair.right.left
    subst hDomNil
    subst hCodNil
    exact And.intro rfl (And.intro rfl ZxpMemSpan.zero)

/-- Scalar-collapse instance fire: the two closed bones (X-eta;Z-eps and X-eta;X-eps)
denote the same (unique) 0 -> 0 relation, kernel-decided. -/
theorem zxpScalarCollapseFire :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.bialgBone))
      (zxpDiagramDenote (zxpRowLhs ZxpRowTag.boneX)) = true := rfl

/-- The two closed bones are also CONVERTIBLE (both fire to the empty diagram), so the
scalar equation holds in the calculus, not only in the semantics. -/
theorem zxpClosedBonesConv :
    ZxpConv (zxpRowLhs ZxpRowTag.bialgBone) (zxpRowLhs ZxpRowTag.boneX) :=
  ZxpConv.trans (zxpRowConv ZxpRowTag.bialgBone)
    (ZxpConv.symm (zxpRowConv ZxpRowTag.boneX))

/-- Honesty pin: the executable well-formedness gate rejects a mis-plumbed diagram. -/
theorem zxpIllFormedDetected :
    zxpDiagramWFB { sourceArity := 1, layers := [[ZxpCell.zSpider 2 1]] } = false := rfl

#eval zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.hopf))
  (zxpDiagramDenote (zxpRowRhs ZxpRowTag.hopf))
#eval zxpSpanEqB (zxpDiagramDenote zxpZUnitDiagram) (zxpDiagramDenote zxpXUnitDiagram)
#eval zxpSpanEqB (zxpDiagramDenote zxpCrossingDiagram)
  (zxpDiagramDenote zxpParallelWiresDiagram)
#eval zxpDiagramDenote (zxpRowLhs ZxpRowTag.hopf)
#eval zxpDiagramDenote (zxpRowRhs ZxpRowTag.hopf)
#eval zxpDiagramDenote zxpZUnitDiagram
#eval zxpDiagramDenote zxpXUnitDiagram

/-! ### Honesty: what is DECIDED and what is NOT -/

/-- Stage 1-3 marker: the F2 subspace kit, the relation category with its categorical laws,
and the diagram semantics are shipped zero-axiom. -/
def fxWpZx_hasRelationSemantics : Bool := true

/-- Stage 4 marker: every shipped row preserves the denotation up to span equality
(kernel-decided per row), the padded congruence is sound, and distinct spans refute
convertibility. -/
def fxWpZx_hasRowSoundness : Bool := true

/-- COMPLETENESS statement (Kissinger 2204.14038 Thm 3.4 direction, scalar-erased):
span-equal well-formed diagrams on matching boundaries are convertible.

OWNER FALSE — NOT PROVEN, NOT COMMISSIONED.  The arc law applies: five prior missing-row
defects in this workstream were caught by invariant-first refutation, so a completeness
push REQUIRES the invariant-first gate (a normal-form census against the published normal
form of Kissinger eq. (5)/(6) — the Z-X normal form spanning S with pivot structure —
BEFORE any completeness induction is attempted).  A completeness attempt without that gate
is forbidden by the workstream discipline.

PRESENTATION-DIFF TABLE (binding, against the literature brief):

Rows SHIPPED (tag = published source, all Z2-specialized, scalar-free):
| xMonoidAssoc/Comm/Unit          = IH A1-A3 (white monoid; X = add)            |
| zComonoidCoassoc/Cocomm/Counit  = IH A4-A6 (black comonoid; Z = copy)         |
| zMonoidAssoc/Comm/Unit          = IH A1'-A3' (HA^op mirror: black monoid)     |
| xComonoidCoassoc/Cocomm/Counit  = IH A4'-A6' (HA^op mirror: white comonoid)   |
| bialgCopyMult                   = IH A7  (mu_X ; eps_Z = eps_Z (x) eps_Z)     |
| bialgSquare                     = IH A8  (THE bialgebra square)               |
| bialgUnitCopy                   = IH A9  (eta_X ; delta_Z = eta_X (x) eta_X)  |
| bialgBone                       = IH A10 (eta_X ; eps_Z = id_0)               |
| bialgCopyMultDual/SquareDual/UnitCopyDual/BoneDual = IH A7'-A10' (mirror)     |
| hopf                            = IH Rem 3.4, antipode trivial over Z2 (D3)   |
| boneX / boneZ                   = IH W2 / B2 (white/black bones)              |
| frobeniusXLeft/Right            = IH W3 (white Frobenius, both orientations)  |
| frobeniusZLeft/Right            = IH W4/B4 (black Frobenius, both)            |
| specialZ / specialX             = IH W4 span side / B-side special laws       |
| cupCoincide / capCoincide       = IH W5-W6/B5-B6 Z2-collapsed (antipode = id) |
| zIdentitySpider / xIdentitySpider = Kissinger Fig. 1 (sp) identity component  |

Rows OMITTED (with reason):
| IH A11-A18, W1, W7, W8 (scalar laws)  : trivial over Z2 — LinRel_F2(0,0) is a  |
|   singleton; shipped instead as the PROVED zxpScalarCollapse + the derived     |
|   zxpClosedBonesConv; matches the IB "up to scalar" reading (Kissinger p. 6).  |
| Kissinger (sp) n-ary fusion family    : derived, not primitive, in IH; shipped |
|   as kernel fires zxpZFusionFire/zxpXFusionFire at the 3->1 instances.         |
| Kissinger (sc) general strong compl.  : arity-indexed derived family; its      |
|   generating instance IS the shipped bialgSquare (A8).                         |
| Kissinger (c) complementarity scalar (1/2) : the Z2 Hopf row shipped carries no |
|   scalar (collapse); the quantum-exact scalar has no LinRel_F2 content.        |
| Backens stabilizer rows, Duncan-Perdrix pivoting, anything with H or pi/2      |
|   phases : OUT OF FRAGMENT (no Hadamard cell exists in the syntax; the         |
|   colour-swap exists only as the meta-duality S <-> S-perp, brief pitfall 3).  |

Sources: Kissinger arXiv:2204.14038 Thm 3.4 + Fig. 1; Bonchi-Sobocinski-Zanasi
IH (JPAA 2017, arXiv:1403.7048) A1-A18/W1-W8/B1-B8, Rem 3.4, Def 5.11, Lemma 5.10,
pushout Sect. 6; IB FoSSaCS'14; Yuster 1984 (RREF uniqueness). -/
def zxpCompletenessStatement : Prop :=
  (firstDiagram secondDiagram : ZxpDiagram) ->
    ZxpDiagramWF firstDiagram -> ZxpDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram ->
    ZxpRelEquiv firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
      (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram) ->
    ZxpConv firstDiagram secondDiagram

/-- Stage 6 marker: completeness is OWNER FALSE (see `zxpCompletenessStatement`). -/
def fxWpZx_hasCompleteness : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
