import FX1Poly.ComputerAlgebra.Decision.GroebnerRationalMembership

/-! # LinearAlgebra/RationalLinearRelations — the ℚ span/relations kit (IH_Q substrate)

Port of the F2 subspace/relations kit (`Polygraph/Omega/ZXPhaseFree/SpiderRelationSeed`,
prefix `zxp`) to `QnfRat` coefficients: the semantic substrate for the
interacting-Hopf-over-ℚ word problem (IH_Q = LinRel_Q, Bonchi–Sobociński–Zanasi
arXiv:1403.7048 Theorem 6.4).  The STRUCTURE is the port; the carrier changes
everything the field structure touches:

  * rows are dense `List QnfRat` (width external, exactly the F2 discipline);
  * the span inductive `IhqMemSpan` is LINEAR-COMBINATION closure
    (`pick scalar row`: add `scalar • row`), not xor closure;
  * elimination is EXACT PIVOTING: `ihqElimStep` subtracts
    `(targetCoeff · pivotCoeff⁻¹) • pivotRow` via `qnfInv` — the step F2's
    `{0,1}` scalars could not express;
  * the F2 "xor with equal leads raises the lead" becomes a field-cancellation
    trichotomy (`ihqElimStepLeadRaises`), and every place the F2 proofs used
    "the head scalar is 1" grows a genuinely-ℚ zero-scalar side case discharged
    by the integral-domain consequence of `qnfMulInvCancels`
    (`ihqQnfFactorZeroOfMulPivotZero`);
  * relational composition embeds the SECOND factor with a NEGATED middle block
    (`ihqComposeEmbedSecond`), so "middle sum is zero" literally reads
    "the two middle vectors are EQUAL" (`ihqRowsEqOfAddNegEqZero`) — over F2
    negation was the identity and this was invisible.

Placement: `LinearAlgebra/` (the content is linear algebra), importing the
Decision-lane grq brick ONLY for its derived `QnfRat` telescopes
(`grqQnfMulZeroRight`/`grqQnfMulNegLeft`/`grqQnfNegAddDistrib`/... — reused, never
re-derived, per the commissioning brief).  The Nat comparator kit is re-derived
fresh (`ihqNatCompare`/`ihqNatLe`) following the F2 file's own self-containment
precedent, so no Polygraph import is dragged into the ComputerAlgebra lane.

Contents: (0) fresh structural Nat comparison kit; (1) the QnfRat row kit
(add/neg/scale/cat/take/drop/coefficient/lead) with the row-level AC + block
algebra; (2) inductive spans `IhqMemSpan` (linear-combination membership) with
add/scale/neg closure, substitution, cons inversion with SCALAR witness;
(3) exact-pivot echelonization by sorted insertion (`ihqInsertRow` /
`ihqEchelonize`), reduction (`ihqReduceAgainst`), and THE SPAN DECISION
`ihqSpanEqB` (mutual reduction) with BOTH `ihqSpanEqBSound` and
`ihqSpanEqBComplete` against `IhqMemSpan`; (4) relations as generator matrices
over width `dom + cod` (`IhqPairMem`), relational composition by middle-block
elimination (`ihqComposeRows`) with the full pullback characterization
`ihqComposeSpec` (iff, both directions — BSZ Lemma 5.10/6.6 specialized to ℚ),
converse, identity generators; (5) RREF via back-substitution with row-space
preservation, and `ihqRrefUniquenessStatement` (syntactic un-normalized RREF
uniqueness), which is false and refuted downstream (`rfcIhqRrefUniquenessRefuted`);
the canonical normalized `rreRref` uniqueness is proven (`rfcRreRrefUnique`);
(6) kernel-`rfl` fires with the ℚ-content pins (scalar-2 span collapse,
char-0 basis exchange, rational compose arithmetic) and a false control.

Raw Lean 4 + Init + the two ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no `List.append`, no `Nat.sub/div/mod/min/max` order lemmas, no
wildcard match arms over inductive scrutinees.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalLinearRelations.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the structural Nat comparison kit (fresh, per the F2 precedent) -/

/-- Three-way order witness for the structural Nat comparator. -/
inductive IhqOrder : Type where
  | isLt : IhqOrder
  | isEq : IhqOrder
  | isGt : IhqOrder

/-- Structural three-way comparison on `Nat`. -/
def ihqNatCompare : Nat -> Nat -> IhqOrder
  | 0, 0 => IhqOrder.isEq
  | 0, _secondPred + 1 => IhqOrder.isLt
  | _firstPred + 1, 0 => IhqOrder.isGt
  | firstPred + 1, secondPred + 1 => ihqNatCompare firstPred secondPred

/-- Structural Bool `<=` on `Nat`. -/
def ihqNatLe : Nat -> Nat -> Bool
  | 0, _anyBound => true
  | _firstPred + 1, 0 => false
  | firstPred + 1, secondPred + 1 => ihqNatLe firstPred secondPred

theorem ihqNatCompareEqImpliesEq : (firstValue secondValue : Nat) ->
    ihqNatCompare firstValue secondValue = IhqOrder.isEq -> firstValue = secondValue
  | 0, 0, _hEq => rfl
  | 0, _secondPred + 1, hEq => IhqOrder.noConfusion hEq
  | _firstPred + 1, 0, hEq => IhqOrder.noConfusion hEq
  | firstPred + 1, secondPred + 1, hEq =>
      congrArg (fun innerValue => innerValue + 1)
        (ihqNatCompareEqImpliesEq firstPred secondPred hEq)

theorem ihqNatLeRefl : (value : Nat) -> ihqNatLe value value = true
  | 0 => rfl
  | valuePred + 1 => ihqNatLeRefl valuePred

theorem ihqNatLeZeroLeft : (value : Nat) -> ihqNatLe 0 value = true
  | 0 => rfl
  | _valuePred + 1 => rfl

theorem ihqNatLeTrans : (firstValue secondValue thirdValue : Nat) ->
    ihqNatLe firstValue secondValue = true -> ihqNatLe secondValue thirdValue = true ->
    ihqNatLe firstValue thirdValue = true
  | 0, _secondValue, thirdValue, _hFirst, _hSecond => ihqNatLeZeroLeft thirdValue
  | _firstPred + 1, 0, _thirdValue, hFirst, _hSecond => Bool.noConfusion hFirst
  | _firstPred + 1, _secondPred + 1, 0, _hFirst, hSecond => Bool.noConfusion hSecond
  | firstPred + 1, secondPred + 1, thirdPred + 1, hFirst, hSecond =>
      ihqNatLeTrans firstPred secondPred thirdPred hFirst hSecond

theorem ihqNatLeSuccRight : (firstValue secondValue : Nat) ->
    ihqNatLe firstValue secondValue = true -> ihqNatLe firstValue (secondValue + 1) = true
  | 0, _secondValue, _hLe => rfl
  | _firstPred + 1, 0, hLe => Bool.noConfusion hLe
  | firstPred + 1, secondPred + 1, hLe => ihqNatLeSuccRight firstPred secondPred hLe

/-- `a < b` (as the comparator) gives `a + 1 <= b`. -/
theorem ihqNatLeSuccOfCompareLt : (firstValue secondValue : Nat) ->
    ihqNatCompare firstValue secondValue = IhqOrder.isLt ->
    ihqNatLe (firstValue + 1) secondValue = true
  | 0, 0, hLt => IhqOrder.noConfusion hLt
  | 0, secondPred + 1, _hLt => ihqNatLeZeroLeft secondPred
  | _firstPred + 1, 0, hLt => IhqOrder.noConfusion hLt
  | firstPred + 1, secondPred + 1, hLt => ihqNatLeSuccOfCompareLt firstPred secondPred hLt

/-- `a + 1 <= b` gives `a < b` (as the comparator). -/
theorem ihqNatCompareLtOfLeSucc : (firstValue secondValue : Nat) ->
    ihqNatLe (firstValue + 1) secondValue = true ->
    ihqNatCompare firstValue secondValue = IhqOrder.isLt
  | _firstValue, 0, hLe => Bool.noConfusion hLe
  | 0, _secondPred + 1, _hLe => rfl
  | firstPred + 1, secondPred + 1, hLe => ihqNatCompareLtOfLeSucc firstPred secondPred hLe

/-- Comparator flip: `a > b` means `b < a`. -/
theorem ihqNatCompareGtFlip : (firstValue secondValue : Nat) ->
    ihqNatCompare firstValue secondValue = IhqOrder.isGt ->
    ihqNatCompare secondValue firstValue = IhqOrder.isLt
  | 0, 0, hGt => IhqOrder.noConfusion hGt
  | 0, _secondPred + 1, hGt => IhqOrder.noConfusion hGt
  | _firstPred + 1, 0, _hGt => rfl
  | firstPred + 1, secondPred + 1, hGt => ihqNatCompareGtFlip firstPred secondPred hGt

/-! ## Stage 0b — derived QnfRat scalar laws (telescoped; the grq kit is imported) -/

/-- Negating the right factor negates the product — commuted `grqQnfMulNegLeft`. -/
theorem ihqQnfMulNegRight (factor otherValue : QnfRat) :
    qnfMul factor (qnfNeg otherValue) = qnfNeg (qnfMul factor otherValue) :=
  ((qnfMulComm factor (qnfNeg otherValue)).trans
      (grqQnfMulNegLeft otherValue factor)).trans
    (congrArg qnfNeg (qnfMulComm otherValue factor))

/-- Double negation is the identity — inverse uniqueness on `-a + a = 0`. -/
theorem ihqQnfNegNeg (value : QnfRat) : qnfNeg (qnfNeg value) = value :=
  grqQnfNegEqOfAddEqZero (qnfAddNegLeft value)

/-- A structurally-false zero comparison IS a disequality with zero. -/
theorem ihqQnfNeZeroOfBeqZeroFalse {value : QnfRat}
    (isBeqFalse : qnfBeq value qnfZero = false) : value ≠ qnfZero := by
  intro isEqZero
  rw [isEqZero, qnfBeqSelfIsTrue] at isBeqFalse
  exact Bool.noConfusion isBeqFalse

/-- A structurally-true zero comparison IS equality with zero. -/
theorem ihqQnfEqZeroOfBeqZeroTrue {value : QnfRat}
    (isBeqTrue : qnfBeq value qnfZero = true) : value = qnfZero :=
  (qnfBeqIffEq value qnfZero).mp isBeqTrue

/-- Equality with zero gives the structurally-true comparison. -/
theorem ihqQnfBeqZeroTrueOfEqZero {value : QnfRat}
    (isEqZero : value = qnfZero) : qnfBeq value qnfZero = true :=
  (qnfBeqIffEq value qnfZero).mpr isEqZero

/-- THE FIELD STEP: the exact-pivot elimination scalar cancels the pivot —
`(-(v · p⁻¹)) · p + v = 0` whenever `p ≠ 0`. -/
theorem ihqQnfElimScalarCancels (targetCoeff pivotCoeff : QnfRat)
    (isPivotNonzero : pivotCoeff ≠ qnfZero) :
    qnfAdd (qnfMul (qnfNeg (qnfMul targetCoeff (qnfInv pivotCoeff))) pivotCoeff)
        targetCoeff
      = qnfZero := by
  rw [grqQnfMulNegLeft (qnfMul targetCoeff (qnfInv pivotCoeff)) pivotCoeff,
    qnfMulAssoc targetCoeff (qnfInv pivotCoeff) pivotCoeff,
    qnfInvMulCancels isPivotNonzero, qnfMulOneRight targetCoeff]
  exact qnfAddNegLeft targetCoeff

/-- THE INTEGRAL-DOMAIN STEP (field consequence): a product with a nonzero
pivot vanishes only when the other factor does. -/
theorem ihqQnfFactorZeroOfMulPivotZero {factor pivotCoeff : QnfRat}
    (isPivotNonzero : pivotCoeff ≠ qnfZero)
    (isProductZero : qnfMul factor pivotCoeff = qnfZero) : factor = qnfZero := by
  have hExpand : factor = qnfMul (qnfMul factor pivotCoeff) (qnfInv pivotCoeff) := by
    rw [qnfMulAssoc factor pivotCoeff (qnfInv pivotCoeff),
      qnfMulInvCancels isPivotNonzero, qnfMulOneRight factor]
  rw [hExpand, isProductZero]
  exact grqQnfMulZeroLeft (qnfInv pivotCoeff)

/-! ## Stage 1 — the QnfRat row kit: dense rows, add/neg/scale, blocks, leads

Rows are dense `List QnfRat` of a fixed width; the width lives OUTSIDE the row
(`IhqAllWidth` hypotheses and relation arities).  All list plumbing is fresh and
cons-only. -/

/-- The all-zero row of the given width. -/
def ihqZeroRow : Nat -> List QnfRat
  | 0 => []
  | widthPred + 1 => qnfZero :: ihqZeroRow widthPred

/-- Pointwise addition of two rows, truncating to the shorter (width discipline
keeps all operands the same length, so truncation never fires in anger). -/
def ihqRowAdd : List QnfRat -> List QnfRat -> List QnfRat
  | [], _secondRow => []
  | _firstCoeff :: _firstRest, [] => []
  | firstCoeff :: firstRest, secondCoeff :: secondRest =>
      qnfAdd firstCoeff secondCoeff :: ihqRowAdd firstRest secondRest

/-- Pointwise negation of a row. -/
def ihqRowNeg : List QnfRat -> List QnfRat
  | [] => []
  | headCoeff :: restCoeffs => qnfNeg headCoeff :: ihqRowNeg restCoeffs

/-- Scale a row by a rational scalar. -/
def ihqRowScale (scalar : QnfRat) : List QnfRat -> List QnfRat
  | [] => []
  | headCoeff :: restCoeffs => qnfMul scalar headCoeff :: ihqRowScale scalar restCoeffs

/-- Cons-only concatenation of two rows. -/
def ihqCat : List QnfRat -> List QnfRat -> List QnfRat
  | [], secondRow => secondRow
  | firstCoeff :: firstRest, secondRow => firstCoeff :: ihqCat firstRest secondRow

/-- First `count` coefficients of a row (shorter row: whatever is there). -/
def ihqTakeN : Nat -> List QnfRat -> List QnfRat
  | 0, _row => []
  | _countPred + 1, [] => []
  | countPred + 1, headCoeff :: restCoeffs => headCoeff :: ihqTakeN countPred restCoeffs

/-- Row without its first `count` coefficients. -/
def ihqDropN : Nat -> List QnfRat -> List QnfRat
  | 0, row => row
  | _countPred + 1, [] => []
  | countPred + 1, _headCoeff :: restCoeffs => ihqDropN countPred restCoeffs

/-- Coefficient at a position (the canonical zero beyond the end). -/
def ihqGetCoeff : List QnfRat -> Nat -> QnfRat
  | [], _position => qnfZero
  | headCoeff :: _restCoeffs, 0 => headCoeff
  | _headCoeff :: restCoeffs, position + 1 => ihqGetCoeff restCoeffs position

/-- Is every coefficient (structurally) the canonical zero? -/
def ihqAreAllCoeffsZero : List QnfRat -> Bool
  | [] => true
  | headCoeff :: restCoeffs =>
      match qnfBeq headCoeff qnfZero with
      | false => false
      | true => ihqAreAllCoeffsZero restCoeffs

/-- Position of the first nonzero coefficient (the leading position), if any. -/
def ihqLead : List QnfRat -> Option Nat
  | [] => none
  | headCoeff :: restCoeffs =>
      match qnfBeq headCoeff qnfZero with
      | false => some 0
      | true =>
          match ihqLead restCoeffs with
          | none => none
          | some leadPred => some (leadPred + 1)

/-! ### Unfolding shapes (proved once, consumed by `rw`) -/

theorem ihqAreAllCoeffsZeroConsShape (headCoeff : QnfRat) (restCoeffs : List QnfRat) :
    ihqAreAllCoeffsZero (headCoeff :: restCoeffs)
      = match qnfBeq headCoeff qnfZero with
        | false => false
        | true => ihqAreAllCoeffsZero restCoeffs := rfl

theorem ihqLeadConsShape (headCoeff : QnfRat) (restCoeffs : List QnfRat) :
    ihqLead (headCoeff :: restCoeffs)
      = match qnfBeq headCoeff qnfZero with
        | false => some 0
        | true =>
            match ihqLead restCoeffs with
            | none => none
            | some leadPred => some (leadPred + 1) := rfl

/-! ### Lengths -/

theorem ihqZeroRowLength : (width : Nat) -> (ihqZeroRow width).length = width
  | 0 => rfl
  | widthPred + 1 => congrArg (fun innerValue => innerValue + 1) (ihqZeroRowLength widthPred)

theorem ihqCatLength : (firstRow secondRow : List QnfRat) ->
    (ihqCat firstRow secondRow).length = firstRow.length + secondRow.length
  | [], secondRow => (Nat.zero_add secondRow.length).symm
  | firstCoeff :: firstRest, secondRow => by
      show (ihqCat firstRest secondRow).length + 1
        = (firstRest.length + 1) + secondRow.length
      rw [ihqCatLength firstRest secondRow, Nat.succ_add firstRest.length secondRow.length]

theorem ihqRowAddLength : (firstRow secondRow : List QnfRat) -> (width : Nat) ->
    firstRow.length = width -> secondRow.length = width ->
    (ihqRowAdd firstRow secondRow).length = width
  | [], [], _width, hFirst, _hSecond => hFirst
  | [], secondCoeff :: secondRest, _width, hFirst, hSecond => by
      rw [<- hFirst] at hSecond
      exact nomatch hSecond
  | firstCoeff :: firstRest, [], _width, hFirst, hSecond => by
      rw [<- hSecond] at hFirst
      exact nomatch hFirst
  | firstCoeff :: firstRest, secondCoeff :: secondRest, 0, hFirst, _hSecond =>
      nomatch hFirst
  | firstCoeff :: firstRest, secondCoeff :: secondRest, widthPred + 1, hFirst, hSecond =>
      congrArg (fun innerValue => innerValue + 1)
        (ihqRowAddLength firstRest secondRest widthPred
          (Nat.succ.inj hFirst) (Nat.succ.inj hSecond))

theorem ihqRowNegLength : (row : List QnfRat) -> (ihqRowNeg row).length = row.length
  | [] => rfl
  | _headCoeff :: restCoeffs =>
      congrArg (fun innerValue => innerValue + 1) (ihqRowNegLength restCoeffs)

theorem ihqRowScaleLength (scalar : QnfRat) :
    (row : List QnfRat) -> (ihqRowScale scalar row).length = row.length
  | [] => rfl
  | _headCoeff :: restCoeffs =>
      congrArg (fun innerValue => innerValue + 1) (ihqRowScaleLength scalar restCoeffs)

/-! ### Take/drop exact-split algebra -/

theorem ihqTakeNCatExact : (frontRow backRow : List QnfRat) -> (frontWidth : Nat) ->
    frontRow.length = frontWidth -> ihqTakeN frontWidth (ihqCat frontRow backRow) = frontRow
  | [], _backRow, 0, _hLen => rfl
  | [], _backRow, _frontPred + 1, hLen => nomatch hLen
  | _frontCoeff :: _frontRest, _backRow, 0, hLen => nomatch hLen
  | frontCoeff :: frontRest, backRow, frontPred + 1, hLen =>
      congrArg (fun innerRow => frontCoeff :: innerRow)
        (ihqTakeNCatExact frontRest backRow frontPred (Nat.succ.inj hLen))

theorem ihqDropNCatExact : (frontRow backRow : List QnfRat) -> (frontWidth : Nat) ->
    frontRow.length = frontWidth -> ihqDropN frontWidth (ihqCat frontRow backRow) = backRow
  | [], _backRow, 0, _hLen => rfl
  | [], _backRow, _frontPred + 1, hLen => nomatch hLen
  | _frontCoeff :: _frontRest, _backRow, 0, hLen => nomatch hLen
  | _frontCoeff :: frontRest, backRow, frontPred + 1, hLen =>
      ihqDropNCatExact frontRest backRow frontPred (Nat.succ.inj hLen)

theorem ihqCatTakeDrop : (row : List QnfRat) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth ->
    ihqCat (ihqTakeN frontWidth row) (ihqDropN frontWidth row) = row
  | _row, 0, _backWidth, _hLen => rfl
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | headCoeff :: restCoeffs, frontPred + 1, backWidth, hLen => by
      show headCoeff :: ihqCat (ihqTakeN frontPred restCoeffs) (ihqDropN frontPred restCoeffs)
        = headCoeff :: restCoeffs
      rw [Nat.succ_add frontPred backWidth] at hLen
      rw [ihqCatTakeDrop restCoeffs frontPred backWidth (Nat.succ.inj hLen)]

theorem ihqTakeNLength : (row : List QnfRat) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth -> (ihqTakeN frontWidth row).length = frontWidth
  | _row, 0, _backWidth, _hLen => rfl
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | headCoeff :: restCoeffs, frontPred + 1, backWidth, hLen => by
      show (ihqTakeN frontPred restCoeffs).length + 1 = frontPred + 1
      rw [Nat.succ_add frontPred backWidth] at hLen
      rw [ihqTakeNLength restCoeffs frontPred backWidth (Nat.succ.inj hLen)]

theorem ihqDropNLength : (row : List QnfRat) -> (frontWidth backWidth : Nat) ->
    row.length = frontWidth + backWidth -> (ihqDropN frontWidth row).length = backWidth
  | _row, 0, _backWidth, hLen => by
      rw [Nat.zero_add] at hLen
      exact hLen
  | [], frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact nomatch hLen
  | _headCoeff :: restCoeffs, frontPred + 1, backWidth, hLen => by
      rw [Nat.succ_add frontPred backWidth] at hLen
      exact ihqDropNLength restCoeffs frontPred backWidth (Nat.succ.inj hLen)

/-! ### Row addition algebra -/

theorem ihqRowAddComm : (firstRow secondRow : List QnfRat) ->
    ihqRowAdd firstRow secondRow = ihqRowAdd secondRow firstRow
  | [], [] => rfl
  | [], _secondCoeff :: _secondRest => rfl
  | _firstCoeff :: _firstRest, [] => rfl
  | firstCoeff :: firstRest, secondCoeff :: secondRest => by
      show qnfAdd firstCoeff secondCoeff :: ihqRowAdd firstRest secondRest
        = qnfAdd secondCoeff firstCoeff :: ihqRowAdd secondRest firstRest
      rw [qnfAddComm firstCoeff secondCoeff, ihqRowAddComm firstRest secondRest]

theorem ihqRowAddAssoc : (firstRow secondRow thirdRow : List QnfRat) ->
    ihqRowAdd (ihqRowAdd firstRow secondRow) thirdRow
      = ihqRowAdd firstRow (ihqRowAdd secondRow thirdRow)
  | [], _secondRow, _thirdRow => rfl
  | _firstCoeff :: _firstRest, [], _thirdRow => rfl
  | _firstCoeff :: _firstRest, _secondCoeff :: _secondRest, [] => rfl
  | firstCoeff :: firstRest, secondCoeff :: secondRest, thirdCoeff :: thirdRest => by
      show qnfAdd (qnfAdd firstCoeff secondCoeff) thirdCoeff
          :: ihqRowAdd (ihqRowAdd firstRest secondRest) thirdRest
        = qnfAdd firstCoeff (qnfAdd secondCoeff thirdCoeff)
          :: ihqRowAdd firstRest (ihqRowAdd secondRest thirdRest)
      rw [qnfAddAssoc firstCoeff secondCoeff thirdCoeff,
        ihqRowAddAssoc firstRest secondRest thirdRest]

/-- Left-swap for row addition: `a + (b + c) = b + (a + c)`. -/
theorem ihqRowAddSwapLeft (firstRow secondRow thirdRow : List QnfRat) :
    ihqRowAdd firstRow (ihqRowAdd secondRow thirdRow)
      = ihqRowAdd secondRow (ihqRowAdd firstRow thirdRow) := by
  rw [<- ihqRowAddAssoc firstRow secondRow thirdRow, ihqRowAddComm firstRow secondRow,
    ihqRowAddAssoc secondRow firstRow thirdRow]

theorem ihqRowAddZeroLeft : (row : List QnfRat) -> (width : Nat) -> row.length = width ->
    ihqRowAdd (ihqZeroRow width) row = row
  | [], 0, _hLen => rfl
  | [], _widthPred + 1, hLen => nomatch hLen
  | _headCoeff :: _restCoeffs, 0, hLen => nomatch hLen
  | headCoeff :: restCoeffs, widthPred + 1, hLen => by
      show qnfAdd qnfZero headCoeff :: ihqRowAdd (ihqZeroRow widthPred) restCoeffs
        = headCoeff :: restCoeffs
      rw [qnfAddZeroLeft headCoeff,
        ihqRowAddZeroLeft restCoeffs widthPred (Nat.succ.inj hLen)]

theorem ihqRowAddZeroRight (row : List QnfRat) (width : Nat) (hLen : row.length = width) :
    ihqRowAdd row (ihqZeroRow width) = row := by
  rw [ihqRowAddComm row (ihqZeroRow width)]
  exact ihqRowAddZeroLeft row width hLen

theorem ihqRowAddNegRight : (row : List QnfRat) ->
    ihqRowAdd row (ihqRowNeg row) = ihqZeroRow row.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfAdd headCoeff (qnfNeg headCoeff) :: ihqRowAdd restCoeffs (ihqRowNeg restCoeffs)
        = qnfZero :: ihqZeroRow restCoeffs.length
      rw [qnfAddNegRight headCoeff, ihqRowAddNegRight restCoeffs]

theorem ihqRowAddNegLeft (row : List QnfRat) :
    ihqRowAdd (ihqRowNeg row) row = ihqZeroRow row.length := by
  rw [ihqRowAddComm (ihqRowNeg row) row]
  exact ihqRowAddNegRight row

/-! ### Scale and negation algebra -/

theorem ihqRowScaleAddDistrib (scalar : QnfRat) : (firstRow secondRow : List QnfRat) ->
    ihqRowScale scalar (ihqRowAdd firstRow secondRow)
      = ihqRowAdd (ihqRowScale scalar firstRow) (ihqRowScale scalar secondRow)
  | [], _secondRow => rfl
  | _firstCoeff :: _firstRest, [] => rfl
  | firstCoeff :: firstRest, secondCoeff :: secondRest => by
      show qnfMul scalar (qnfAdd firstCoeff secondCoeff)
          :: ihqRowScale scalar (ihqRowAdd firstRest secondRest)
        = qnfAdd (qnfMul scalar firstCoeff) (qnfMul scalar secondCoeff)
          :: ihqRowAdd (ihqRowScale scalar firstRest) (ihqRowScale scalar secondRest)
      rw [qnfMulLeftDistrib scalar firstCoeff secondCoeff,
        ihqRowScaleAddDistrib scalar firstRest secondRest]

theorem ihqRowScaleScale (firstScalar secondScalar : QnfRat) : (row : List QnfRat) ->
    ihqRowScale firstScalar (ihqRowScale secondScalar row)
      = ihqRowScale (qnfMul firstScalar secondScalar) row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfMul firstScalar (qnfMul secondScalar headCoeff)
          :: ihqRowScale firstScalar (ihqRowScale secondScalar restCoeffs)
        = qnfMul (qnfMul firstScalar secondScalar) headCoeff
          :: ihqRowScale (qnfMul firstScalar secondScalar) restCoeffs
      rw [<- qnfMulAssoc firstScalar secondScalar headCoeff,
        ihqRowScaleScale firstScalar secondScalar restCoeffs]

theorem ihqRowScaleOne : (row : List QnfRat) -> ihqRowScale qnfOne row = row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfMul qnfOne headCoeff :: ihqRowScale qnfOne restCoeffs
        = headCoeff :: restCoeffs
      rw [qnfMulOneLeft headCoeff, ihqRowScaleOne restCoeffs]

theorem ihqRowScaleZeroScalar : (row : List QnfRat) ->
    ihqRowScale qnfZero row = ihqZeroRow row.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfMul qnfZero headCoeff :: ihqRowScale qnfZero restCoeffs
        = qnfZero :: ihqZeroRow restCoeffs.length
      rw [grqQnfMulZeroLeft headCoeff, ihqRowScaleZeroScalar restCoeffs]

theorem ihqRowScaleZeroRow (scalar : QnfRat) : (width : Nat) ->
    ihqRowScale scalar (ihqZeroRow width) = ihqZeroRow width
  | 0 => rfl
  | widthPred + 1 => by
      show qnfMul scalar qnfZero :: ihqRowScale scalar (ihqZeroRow widthPred)
        = qnfZero :: ihqZeroRow widthPred
      rw [grqQnfMulZeroRight scalar, ihqRowScaleZeroRow scalar widthPred]

/-- Merging two scalings of the SAME row: `c • h + d • h = (c + d) • h`. -/
theorem ihqRowScaleMerge (firstScalar secondScalar : QnfRat) : (row : List QnfRat) ->
    ihqRowAdd (ihqRowScale firstScalar row) (ihqRowScale secondScalar row)
      = ihqRowScale (qnfAdd firstScalar secondScalar) row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfAdd (qnfMul firstScalar headCoeff) (qnfMul secondScalar headCoeff)
          :: ihqRowAdd (ihqRowScale firstScalar restCoeffs)
            (ihqRowScale secondScalar restCoeffs)
        = qnfMul (qnfAdd firstScalar secondScalar) headCoeff
          :: ihqRowScale (qnfAdd firstScalar secondScalar) restCoeffs
      rw [<- qnfMulRightDistrib firstScalar secondScalar headCoeff,
        ihqRowScaleMerge firstScalar secondScalar restCoeffs]

/-- The reassociation workhorse: `c • h + (d • h + p) = (c + d) • h + p`. -/
theorem ihqRowScaleMergeOnHead (firstScalar secondScalar : QnfRat)
    (sharedRow partnerRow : List QnfRat) :
    ihqRowAdd (ihqRowScale firstScalar sharedRow)
        (ihqRowAdd (ihqRowScale secondScalar sharedRow) partnerRow)
      = ihqRowAdd (ihqRowScale (qnfAdd firstScalar secondScalar) sharedRow) partnerRow := by
  rw [<- ihqRowAddAssoc (ihqRowScale firstScalar sharedRow)
      (ihqRowScale secondScalar sharedRow) partnerRow,
    ihqRowScaleMerge firstScalar secondScalar sharedRow]

theorem ihqRowNegAddDistrib : (firstRow secondRow : List QnfRat) ->
    ihqRowNeg (ihqRowAdd firstRow secondRow)
      = ihqRowAdd (ihqRowNeg firstRow) (ihqRowNeg secondRow)
  | [], _secondRow => rfl
  | _firstCoeff :: _firstRest, [] => rfl
  | firstCoeff :: firstRest, secondCoeff :: secondRest => by
      show qnfNeg (qnfAdd firstCoeff secondCoeff)
          :: ihqRowNeg (ihqRowAdd firstRest secondRest)
        = qnfAdd (qnfNeg firstCoeff) (qnfNeg secondCoeff)
          :: ihqRowAdd (ihqRowNeg firstRest) (ihqRowNeg secondRest)
      rw [grqQnfNegAddDistrib firstCoeff secondCoeff,
        ihqRowNegAddDistrib firstRest secondRest]

theorem ihqRowNegZeroRow : (width : Nat) -> ihqRowNeg (ihqZeroRow width) = ihqZeroRow width
  | 0 => rfl
  | widthPred + 1 => by
      show qnfNeg qnfZero :: ihqRowNeg (ihqZeroRow widthPred)
        = qnfZero :: ihqZeroRow widthPred
      rw [grqQnfNegZeroIsZero, ihqRowNegZeroRow widthPred]

theorem ihqRowNegNeg : (row : List QnfRat) -> ihqRowNeg (ihqRowNeg row) = row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfNeg (qnfNeg headCoeff) :: ihqRowNeg (ihqRowNeg restCoeffs)
        = headCoeff :: restCoeffs
      rw [ihqQnfNegNeg headCoeff, ihqRowNegNeg restCoeffs]

/-- Negation IS scaling by `-1`. -/
theorem ihqRowNegAsScale : (row : List QnfRat) ->
    ihqRowNeg row = ihqRowScale (qnfNeg qnfOne) row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfNeg headCoeff :: ihqRowNeg restCoeffs
        = qnfMul (qnfNeg qnfOne) headCoeff :: ihqRowScale (qnfNeg qnfOne) restCoeffs
      rw [grqQnfMulNegLeft qnfOne headCoeff, qnfMulOneLeft headCoeff,
        ihqRowNegAsScale restCoeffs]

/-- Scaling commutes with negation. -/
theorem ihqRowScaleNegComm (scalar : QnfRat) : (row : List QnfRat) ->
    ihqRowScale scalar (ihqRowNeg row) = ihqRowNeg (ihqRowScale scalar row)
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show qnfMul scalar (qnfNeg headCoeff) :: ihqRowScale scalar (ihqRowNeg restCoeffs)
        = qnfNeg (qnfMul scalar headCoeff) :: ihqRowNeg (ihqRowScale scalar restCoeffs)
      rw [ihqQnfMulNegRight scalar headCoeff, ihqRowScaleNegComm scalar restCoeffs]

/-- Two rows whose difference vanishes at a shared width are equal. -/
theorem ihqRowsEqOfAddNegEqZero (firstRow secondRow : List QnfRat) (width : Nat)
    (hFirst : firstRow.length = width) (hSecond : secondRow.length = width)
    (hZero : ihqRowAdd firstRow (ihqRowNeg secondRow) = ihqZeroRow width) :
    firstRow = secondRow := by
  have hChain : ihqRowAdd (ihqRowAdd firstRow (ihqRowNeg secondRow)) secondRow
      = firstRow := by
    rw [ihqRowAddAssoc firstRow (ihqRowNeg secondRow) secondRow,
      ihqRowAddNegLeft secondRow, hSecond,
      ihqRowAddZeroRight firstRow width hFirst]
  rw [hZero, ihqRowAddZeroLeft secondRow width hSecond] at hChain
  exact hChain.symm

/-! ### Coefficients, all-zero, blocks -/

theorem ihqGetCoeffZeroRow : (width position : Nat) ->
    ihqGetCoeff (ihqZeroRow width) position = qnfZero
  | 0, 0 => rfl
  | 0, _positionPred + 1 => rfl
  | _widthPred + 1, 0 => rfl
  | widthPred + 1, positionPred + 1 => ihqGetCoeffZeroRow widthPred positionPred

theorem ihqGetCoeffAdd : (firstRow secondRow : List QnfRat) ->
    firstRow.length = secondRow.length -> (position : Nat) ->
    ihqGetCoeff (ihqRowAdd firstRow secondRow) position
      = qnfAdd (ihqGetCoeff firstRow position) (ihqGetCoeff secondRow position)
  | [], [], _hLen, 0 => (qnfAddZeroLeft qnfZero).symm
  | [], [], _hLen, _positionPred + 1 => (qnfAddZeroLeft qnfZero).symm
  | [], _secondCoeff :: _secondRest, hLen, _position => nomatch hLen
  | _firstCoeff :: _firstRest, [], hLen, _position => nomatch hLen
  | _firstCoeff :: _firstRest, _secondCoeff :: _secondRest, _hLen, 0 => rfl
  | _firstCoeff :: firstRest, _secondCoeff :: secondRest, hLen, positionPred + 1 =>
      ihqGetCoeffAdd firstRest secondRest (Nat.succ.inj hLen) positionPred

theorem ihqGetCoeffScale (scalar : QnfRat) : (row : List QnfRat) -> (position : Nat) ->
    ihqGetCoeff (ihqRowScale scalar row) position
      = qnfMul scalar (ihqGetCoeff row position)
  | [], 0 => (grqQnfMulZeroRight scalar).symm
  | [], _positionPred + 1 => (grqQnfMulZeroRight scalar).symm
  | _headCoeff :: _restCoeffs, 0 => rfl
  | _headCoeff :: restCoeffs, positionPred + 1 =>
      ihqGetCoeffScale scalar restCoeffs positionPred

theorem ihqAreAllCoeffsZeroZeroRow : (width : Nat) ->
    ihqAreAllCoeffsZero (ihqZeroRow width) = true
  | 0 => rfl
  | widthPred + 1 => by
      rw [show ihqZeroRow (widthPred + 1) = qnfZero :: ihqZeroRow widthPred from rfl,
        ihqAreAllCoeffsZeroConsShape, qnfBeqSelfIsTrue qnfZero]
      exact ihqAreAllCoeffsZeroZeroRow widthPred

theorem ihqZeroRowOfAllCoeffsZero : (row : List QnfRat) ->
    ihqAreAllCoeffsZero row = true -> row = ihqZeroRow row.length
  | [], _hAll => rfl
  | headCoeff :: restCoeffs, hAll => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          exact Bool.noConfusion hAll
      | true =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          show headCoeff :: restCoeffs = qnfZero :: ihqZeroRow restCoeffs.length
          rw [ihqQnfEqZeroOfBeqZeroTrue hBeq,
            <- ihqZeroRowOfAllCoeffsZero restCoeffs hAll]

theorem ihqAreAllCoeffsZeroAdd : (firstRow secondRow : List QnfRat) ->
    ihqAreAllCoeffsZero firstRow = true -> ihqAreAllCoeffsZero secondRow = true ->
    ihqAreAllCoeffsZero (ihqRowAdd firstRow secondRow) = true
  | [], _secondRow, _hFirst, _hSecond => rfl
  | _firstCoeff :: _firstRest, [], _hFirst, _hSecond => rfl
  | firstCoeff :: firstRest, secondCoeff :: secondRest, hFirst, hSecond => by
      cases hBeqFirst : qnfBeq firstCoeff qnfZero with
      | false =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeqFirst] at hFirst
          exact Bool.noConfusion hFirst
      | true =>
          cases hBeqSecond : qnfBeq secondCoeff qnfZero with
          | false =>
              rw [ihqAreAllCoeffsZeroConsShape, hBeqSecond] at hSecond
              exact Bool.noConfusion hSecond
          | true =>
              rw [ihqAreAllCoeffsZeroConsShape, hBeqFirst] at hFirst
              rw [ihqAreAllCoeffsZeroConsShape, hBeqSecond] at hSecond
              show ihqAreAllCoeffsZero
                (qnfAdd firstCoeff secondCoeff :: ihqRowAdd firstRest secondRest) = true
              rw [ihqAreAllCoeffsZeroConsShape,
                ihqQnfEqZeroOfBeqZeroTrue hBeqFirst,
                ihqQnfEqZeroOfBeqZeroTrue hBeqSecond,
                qnfAddZeroLeft qnfZero, qnfBeqSelfIsTrue qnfZero]
              exact ihqAreAllCoeffsZeroAdd firstRest secondRest hFirst hSecond

theorem ihqAreAllCoeffsZeroScale (scalar : QnfRat) : (row : List QnfRat) ->
    ihqAreAllCoeffsZero row = true ->
    ihqAreAllCoeffsZero (ihqRowScale scalar row) = true
  | [], _hAll => rfl
  | headCoeff :: restCoeffs, hAll => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          exact Bool.noConfusion hAll
      | true =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          show ihqAreAllCoeffsZero
            (qnfMul scalar headCoeff :: ihqRowScale scalar restCoeffs) = true
          rw [ihqAreAllCoeffsZeroConsShape, ihqQnfEqZeroOfBeqZeroTrue hBeq,
            grqQnfMulZeroRight scalar, qnfBeqSelfIsTrue qnfZero]
          exact ihqAreAllCoeffsZeroScale scalar restCoeffs hAll

theorem ihqAreAllCoeffsZeroGetCoeff : (row : List QnfRat) ->
    ihqAreAllCoeffsZero row = true -> (position : Nat) ->
    ihqGetCoeff row position = qnfZero
  | [], _hAll, 0 => rfl
  | [], _hAll, _positionPred + 1 => rfl
  | headCoeff :: restCoeffs, hAll, position => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          exact Bool.noConfusion hAll
      | true =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          cases position with
          | zero => exact ihqQnfEqZeroOfBeqZeroTrue hBeq
          | succ positionPred =>
              exact ihqAreAllCoeffsZeroGetCoeff restCoeffs hAll positionPred

theorem ihqAreAllCoeffsZeroTakeN : (row : List QnfRat) ->
    ihqAreAllCoeffsZero row = true -> (count : Nat) ->
    ihqAreAllCoeffsZero (ihqTakeN count row) = true
  | [], _hAll, 0 => rfl
  | [], _hAll, _countPred + 1 => rfl
  | _headCoeff :: _restCoeffs, _hAll, 0 => rfl
  | headCoeff :: restCoeffs, hAll, countPred + 1 => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          exact Bool.noConfusion hAll
      | true =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq] at hAll
          show ihqAreAllCoeffsZero (headCoeff :: ihqTakeN countPred restCoeffs) = true
          rw [ihqAreAllCoeffsZeroConsShape, hBeq]
          exact ihqAreAllCoeffsZeroTakeN restCoeffs hAll countPred

/-! ### Cat algebra -/

theorem ihqCatZeroZero : (frontWidth backWidth : Nat) ->
    ihqCat (ihqZeroRow frontWidth) (ihqZeroRow backWidth)
      = ihqZeroRow (frontWidth + backWidth)
  | 0, backWidth => by rw [Nat.zero_add]; rfl
  | frontPred + 1, backWidth => by
      show qnfZero :: ihqCat (ihqZeroRow frontPred) (ihqZeroRow backWidth)
        = ihqZeroRow (frontPred + 1 + backWidth)
      rw [Nat.succ_add frontPred backWidth]
      show qnfZero :: ihqCat (ihqZeroRow frontPred) (ihqZeroRow backWidth)
        = qnfZero :: ihqZeroRow (frontPred + backWidth)
      rw [ihqCatZeroZero frontPred backWidth]

/-- Cat is injective once the first block's length is pinned. -/
theorem ihqCatInj : (firstRow secondRow thirdRow fourthRow : List QnfRat) ->
    firstRow.length = thirdRow.length ->
    ihqCat firstRow secondRow = ihqCat thirdRow fourthRow ->
    firstRow = thirdRow /\ secondRow = fourthRow
  | [], _secondRow, [], _fourthRow, _hLen, hCat => And.intro rfl hCat
  | [], _secondRow, _thirdCoeff :: _thirdRest, _fourthRow, hLen, _hCat => nomatch hLen
  | _firstCoeff :: _firstRest, _secondRow, [], _fourthRow, hLen, _hCat => nomatch hLen
  | firstCoeff :: firstRest, secondRow, thirdCoeff :: thirdRest, fourthRow, hLen, hCat => by
      have hHead : firstCoeff = thirdCoeff := by
        have hHeads := congrArg (fun fullRow => ihqGetCoeff fullRow 0) hCat
        exact hHeads
      have hTail : ihqCat firstRest secondRow = ihqCat thirdRest fourthRow := by
        have hTails := congrArg (fun fullRow =>
          match fullRow with
          | [] => ([] : List QnfRat)
          | _headCoeff :: tailCoeffs => tailCoeffs) hCat
        exact hTails
      have hRest := ihqCatInj firstRest secondRow thirdRest fourthRow
        (Nat.succ.inj hLen) hTail
      exact And.intro (by rw [hHead, hRest.left]) hRest.right

/-- Addition distributes over cat blockwise once the first blocks share a length. -/
theorem ihqRowAddCat : (firstRow secondRow thirdRow fourthRow : List QnfRat) ->
    firstRow.length = thirdRow.length ->
    ihqRowAdd (ihqCat firstRow secondRow) (ihqCat thirdRow fourthRow)
      = ihqCat (ihqRowAdd firstRow thirdRow) (ihqRowAdd secondRow fourthRow)
  | [], _secondRow, [], _fourthRow, _hLen => rfl
  | [], _secondRow, _thirdCoeff :: _thirdRest, _fourthRow, hLen => nomatch hLen
  | _firstCoeff :: _firstRest, _secondRow, [], _fourthRow, hLen => nomatch hLen
  | firstCoeff :: firstRest, secondRow, thirdCoeff :: thirdRest, fourthRow, hLen => by
      show qnfAdd firstCoeff thirdCoeff
          :: ihqRowAdd (ihqCat firstRest secondRow) (ihqCat thirdRest fourthRow)
        = qnfAdd firstCoeff thirdCoeff
          :: ihqCat (ihqRowAdd firstRest thirdRest) (ihqRowAdd secondRow fourthRow)
      rw [ihqRowAddCat firstRest secondRow thirdRest fourthRow (Nat.succ.inj hLen)]

theorem ihqRowScaleCat (scalar : QnfRat) : (firstRow secondRow : List QnfRat) ->
    ihqRowScale scalar (ihqCat firstRow secondRow)
      = ihqCat (ihqRowScale scalar firstRow) (ihqRowScale scalar secondRow)
  | [], _secondRow => rfl
  | firstCoeff :: firstRest, secondRow =>
      congrArg (fun innerRow => qnfMul scalar firstCoeff :: innerRow)
        (ihqRowScaleCat scalar firstRest secondRow)

theorem ihqTakeNAdd : (count : Nat) -> (firstRow secondRow : List QnfRat) ->
    ihqTakeN count (ihqRowAdd firstRow secondRow)
      = ihqRowAdd (ihqTakeN count firstRow) (ihqTakeN count secondRow)
  | 0, _firstRow, _secondRow => rfl
  | _countPred + 1, [], _secondRow => rfl
  | _countPred + 1, _firstCoeff :: _firstRest, [] => rfl
  | countPred + 1, firstCoeff :: firstRest, secondCoeff :: secondRest =>
      congrArg (fun innerRow => qnfAdd firstCoeff secondCoeff :: innerRow)
        (ihqTakeNAdd countPred firstRest secondRest)

theorem ihqDropNAdd : (count : Nat) -> (firstRow secondRow : List QnfRat) ->
    ihqDropN count (ihqRowAdd firstRow secondRow)
      = ihqRowAdd (ihqDropN count firstRow) (ihqDropN count secondRow)
  | 0, _firstRow, _secondRow => rfl
  | _countPred + 1, [], [] => rfl
  | countPred + 1, [], _secondCoeff :: secondRest => by
      show ([] : List QnfRat) = ihqRowAdd [] (ihqDropN countPred secondRest)
      rfl
  | countPred + 1, _firstCoeff :: firstRest, [] => by
      show ([] : List QnfRat) = ihqRowAdd (ihqDropN countPred firstRest) []
      rw [ihqRowAddComm]
      rfl
  | countPred + 1, _firstCoeff :: firstRest, _secondCoeff :: secondRest =>
      ihqDropNAdd countPred firstRest secondRest

theorem ihqTakeNScale (scalar : QnfRat) : (count : Nat) -> (row : List QnfRat) ->
    ihqTakeN count (ihqRowScale scalar row) = ihqRowScale scalar (ihqTakeN count row)
  | 0, _row => rfl
  | _countPred + 1, [] => rfl
  | countPred + 1, headCoeff :: restCoeffs =>
      congrArg (fun innerRow => qnfMul scalar headCoeff :: innerRow)
        (ihqTakeNScale scalar countPred restCoeffs)

theorem ihqDropNScale (scalar : QnfRat) : (count : Nat) -> (row : List QnfRat) ->
    ihqDropN count (ihqRowScale scalar row) = ihqRowScale scalar (ihqDropN count row)
  | 0, _row => rfl
  | _countPred + 1, [] => rfl
  | countPred + 1, _headCoeff :: restCoeffs => ihqDropNScale scalar countPred restCoeffs

theorem ihqTakeNZeroRowExact : (frontWidth backWidth : Nat) ->
    ihqTakeN frontWidth (ihqZeroRow (frontWidth + backWidth)) = ihqZeroRow frontWidth := by
  intro frontWidth backWidth
  have hSplit : ihqZeroRow (frontWidth + backWidth)
      = ihqCat (ihqZeroRow frontWidth) (ihqZeroRow backWidth) :=
    (ihqCatZeroZero frontWidth backWidth).symm
  rw [hSplit]
  exact ihqTakeNCatExact (ihqZeroRow frontWidth) (ihqZeroRow backWidth) frontWidth
    (ihqZeroRowLength frontWidth)

theorem ihqDropNZeroRowExact : (frontWidth backWidth : Nat) ->
    ihqDropN frontWidth (ihqZeroRow (frontWidth + backWidth)) = ihqZeroRow backWidth := by
  intro frontWidth backWidth
  have hSplit : ihqZeroRow (frontWidth + backWidth)
      = ihqCat (ihqZeroRow frontWidth) (ihqZeroRow backWidth) :=
    (ihqCatZeroZero frontWidth backWidth).symm
  rw [hSplit]
  exact ihqDropNCatExact (ihqZeroRow frontWidth) (ihqZeroRow backWidth) frontWidth
    (ihqZeroRowLength frontWidth)

/-! ### Leads: the first nonzero coefficient -/

/-- Inversion of `ihqLead` on a zero-headed row: the tail leads, shifted by one. -/
theorem ihqLeadZeroConsSome (headCoeff : QnfRat) (restCoeffs : List QnfRat)
    (hBeq : qnfBeq headCoeff qnfZero = true) (leadPosition : Nat)
    (hLead : ihqLead (headCoeff :: restCoeffs) = some leadPosition) :
    Exists fun restLead =>
      ihqLead restCoeffs = some restLead /\ leadPosition = restLead + 1 := by
  rw [ihqLeadConsShape, hBeq] at hLead
  cases hInner : ihqLead restCoeffs with
  | none =>
      rw [hInner] at hLead
      exact nomatch hLead
  | some innerLead =>
      rw [hInner] at hLead
      have hReduced : some (innerLead + 1) = some leadPosition := hLead
      exact Exists.intro innerLead (And.intro rfl (Option.some.inj hReduced).symm)

/-- A zero-headed row with lead `none` has a tail with lead `none`. -/
theorem ihqLeadZeroConsNone (headCoeff : QnfRat) (restCoeffs : List QnfRat)
    (hBeq : qnfBeq headCoeff qnfZero = true)
    (hLead : ihqLead (headCoeff :: restCoeffs) = none) : ihqLead restCoeffs = none := by
  rw [ihqLeadConsShape, hBeq] at hLead
  cases hInner : ihqLead restCoeffs with
  | none => rfl
  | some innerLead =>
      rw [hInner] at hLead
      exact nomatch hLead

/-- The coefficient at the leading position is structurally nonzero. -/
theorem ihqLeadCoeffBeqFalse : (row : List QnfRat) -> (leadPosition : Nat) ->
    ihqLead row = some leadPosition ->
    qnfBeq (ihqGetCoeff row leadPosition) qnfZero = false
  | [], _leadPosition, hLead => nomatch hLead
  | headCoeff :: restCoeffs, leadPosition, hLead => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqLeadConsShape, hBeq] at hLead
          have hReduced : some 0 = some leadPosition := hLead
          rw [<- Option.some.inj hReduced]
          exact hBeq
      | true =>
          have hSplit := ihqLeadZeroConsSome headCoeff restCoeffs hBeq leadPosition hLead
          cases hSplit with
          | intro restLead hBoth =>
              rw [hBoth.right]
              exact ihqLeadCoeffBeqFalse restCoeffs restLead hBoth.left

/-- Every coefficient strictly below the lead is the canonical zero. -/
theorem ihqLeadCoeffBelowZero : (row : List QnfRat) -> (leadPosition position : Nat) ->
    ihqLead row = some leadPosition ->
    ihqNatCompare position leadPosition = IhqOrder.isLt ->
    ihqGetCoeff row position = qnfZero
  | [], _leadPosition, _position, hLead, _hLt => nomatch hLead
  | headCoeff :: restCoeffs, leadPosition, position, hLead, hLt => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqLeadConsShape, hBeq] at hLead
          have hReduced : some 0 = some leadPosition := hLead
          have hZero : leadPosition = 0 := (Option.some.inj hReduced).symm
          rw [hZero] at hLt
          cases position with
          | zero => exact nomatch hLt
          | succ positionPred => exact nomatch hLt
      | true =>
          have hSplit := ihqLeadZeroConsSome headCoeff restCoeffs hBeq leadPosition hLead
          cases hSplit with
          | intro restLead hBoth =>
              cases position with
              | zero => exact ihqQnfEqZeroOfBeqZeroTrue hBeq
              | succ positionPred =>
                  rw [hBoth.right] at hLt
                  exact ihqLeadCoeffBelowZero restCoeffs restLead positionPred
                    hBoth.left hLt

theorem ihqLeadNoneAllZero : (row : List QnfRat) -> ihqLead row = none ->
    ihqAreAllCoeffsZero row = true
  | [], _hLead => rfl
  | headCoeff :: restCoeffs, hLead => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqLeadConsShape, hBeq] at hLead
          exact nomatch hLead
      | true =>
          rw [ihqAreAllCoeffsZeroConsShape, hBeq]
          exact ihqLeadNoneAllZero restCoeffs
            (ihqLeadZeroConsNone headCoeff restCoeffs hBeq hLead)

/-- An all-zero row of a pinned width IS the zero row. -/
theorem ihqLeadNoneToZeroRow {width : Nat} (vector : List QnfRat)
    (hLen : vector.length = width) (hLead : ihqLead vector = none) :
    vector = ihqZeroRow width := by
  have hToZero := ihqZeroRowOfAllCoeffsZero vector (ihqLeadNoneAllZero vector hLead)
  rw [hLen] at hToZero
  exact hToZero

/-- A row whose first `count` coefficients are not all zero leads strictly below
`count`. -/
theorem ihqTakeNotAllZeroLead : (row : List QnfRat) -> (count : Nat) ->
    ihqAreAllCoeffsZero (ihqTakeN count row) = false ->
    (Exists fun leadPosition =>
      ihqLead row = some leadPosition
        /\ ihqNatCompare leadPosition count = IhqOrder.isLt)
  | _row, 0, hFalse => Bool.noConfusion hFalse
  | [], _countPred + 1, hFalse => Bool.noConfusion hFalse
  | headCoeff :: restCoeffs, countPred + 1, hFalse => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          refine Exists.intro 0 (And.intro ?_ rfl)
          rw [ihqLeadConsShape, hBeq]
      | true =>
          rw [show ihqTakeN (countPred + 1) (headCoeff :: restCoeffs)
              = headCoeff :: ihqTakeN countPred restCoeffs from rfl,
            ihqAreAllCoeffsZeroConsShape, hBeq] at hFalse
          have hRest := ihqTakeNotAllZeroLead restCoeffs countPred hFalse
          cases hRest with
          | intro restLead hRestBoth =>
              refine Exists.intro (restLead + 1) (And.intro ?_ hRestBoth.right)
              rw [ihqLeadConsShape, hBeq, hRestBoth.left]

/-- If the first `count` coefficients are all zero, every coefficient strictly
below `count` is zero. -/
theorem ihqAllZeroTakeGetCoeff : (row : List QnfRat) -> (count position : Nat) ->
    ihqAreAllCoeffsZero (ihqTakeN count row) = true ->
    ihqNatCompare position count = IhqOrder.isLt ->
    ihqGetCoeff row position = qnfZero
  | _row, 0, 0, _hAll, hLt => IhqOrder.noConfusion hLt
  | _row, 0, _positionPred + 1, _hAll, hLt => IhqOrder.noConfusion hLt
  | [], _countPred + 1, 0, _hAll, _hLt => rfl
  | [], _countPred + 1, _positionPred + 1, _hAll, _hLt => rfl
  | headCoeff :: restCoeffs, countPred + 1, position, hAll, hLt => by
      rw [show ihqTakeN (countPred + 1) (headCoeff :: restCoeffs)
          = headCoeff :: ihqTakeN countPred restCoeffs from rfl,
        ihqAreAllCoeffsZeroConsShape] at hAll
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [hBeq] at hAll
          exact Bool.noConfusion hAll
      | true =>
          rw [hBeq] at hAll
          cases position with
          | zero => exact ihqQnfEqZeroOfBeqZeroTrue hBeq
          | succ positionPred =>
              exact ihqAllZeroTakeGetCoeff restCoeffs countPred positionPred hAll hLt

/-! ## Stage 1b — the exact-pivot elimination step

`ihqElimStep target pivot pos` subtracts `(targetCoeff · pivotCoeff⁻¹) • pivotRow`
from the target: the position-`pos` coefficient of the result is EXACTLY zero
(`ihqElimStepCancelsPivot`), the operation is a span `pick`, and it is undone by
adding the negated scalar back (`ihqElimStepRecovers`). -/

/-- The exact-pivot elimination scalar. -/
def ihqElimCoeff (targetVector pivotRow : List QnfRat) (pivotPosition : Nat) : QnfRat :=
  qnfNeg (qnfMul (ihqGetCoeff targetVector pivotPosition)
    (qnfInv (ihqGetCoeff pivotRow pivotPosition)))

/-- One exact-pivot elimination: `target + elimCoeff • pivotRow`. -/
def ihqElimStep (targetVector pivotRow : List QnfRat) (pivotPosition : Nat) :
    List QnfRat :=
  ihqRowAdd (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
    targetVector

theorem ihqElimStepLength {width : Nat} (targetVector pivotRow : List QnfRat)
    (pivotPosition : Nat) (hTargetLen : targetVector.length = width)
    (hPivotLen : pivotRow.length = width) :
    (ihqElimStep targetVector pivotRow pivotPosition).length = width :=
  ihqRowAddLength
    (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
    targetVector width
    ((ihqRowScaleLength (ihqElimCoeff targetVector pivotRow pivotPosition)
      pivotRow).trans hPivotLen)
    hTargetLen

/-- THE CANCELLATION: elimination zeroes the pivot-position coefficient. -/
theorem ihqElimStepCancelsPivot {width : Nat} (targetVector pivotRow : List QnfRat)
    (pivotPosition : Nat) (hTargetLen : targetVector.length = width)
    (hPivotLen : pivotRow.length = width)
    (hPivotNonzero : qnfBeq (ihqGetCoeff pivotRow pivotPosition) qnfZero = false) :
    ihqGetCoeff (ihqElimStep targetVector pivotRow pivotPosition) pivotPosition
      = qnfZero := by
  show ihqGetCoeff
    (ihqRowAdd (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
      targetVector) pivotPosition = qnfZero
  rw [ihqGetCoeffAdd
      (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
      targetVector
      (by rw [ihqRowScaleLength, hPivotLen, hTargetLen])
      pivotPosition,
    ihqGetCoeffScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow
      pivotPosition]
  exact ihqQnfElimScalarCancels (ihqGetCoeff targetVector pivotPosition)
    (ihqGetCoeff pivotRow pivotPosition) (ihqQnfNeZeroOfBeqZeroFalse hPivotNonzero)

/-- Positions where both operands vanish stay zero under elimination. -/
theorem ihqElimStepKeepsZero {width : Nat} (targetVector pivotRow : List QnfRat)
    (pivotPosition position : Nat) (hTargetLen : targetVector.length = width)
    (hPivotLen : pivotRow.length = width)
    (hTargetZero : ihqGetCoeff targetVector position = qnfZero)
    (hPivotZero : ihqGetCoeff pivotRow position = qnfZero) :
    ihqGetCoeff (ihqElimStep targetVector pivotRow pivotPosition) position = qnfZero := by
  show ihqGetCoeff
    (ihqRowAdd (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
      targetVector) position = qnfZero
  rw [ihqGetCoeffAdd
      (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
      targetVector
      (by rw [ihqRowScaleLength, hPivotLen, hTargetLen])
      position,
    ihqGetCoeffScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow position,
    hTargetZero, hPivotZero, grqQnfMulZeroRight, qnfAddZeroLeft]

/-- THE RECOVERY: adding the negated elimination scalar back restores the target. -/
theorem ihqElimStepRecovers {width : Nat} (targetVector pivotRow : List QnfRat)
    (pivotPosition : Nat) (hTargetLen : targetVector.length = width)
    (hPivotLen : pivotRow.length = width) :
    ihqRowAdd
        (ihqRowScale (qnfNeg (ihqElimCoeff targetVector pivotRow pivotPosition)) pivotRow)
        (ihqElimStep targetVector pivotRow pivotPosition)
      = targetVector := by
  show ihqRowAdd
      (ihqRowScale (qnfNeg (ihqElimCoeff targetVector pivotRow pivotPosition)) pivotRow)
      (ihqRowAdd (ihqRowScale (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow)
        targetVector)
    = targetVector
  rw [ihqRowScaleMergeOnHead (qnfNeg (ihqElimCoeff targetVector pivotRow pivotPosition))
      (ihqElimCoeff targetVector pivotRow pivotPosition) pivotRow targetVector,
    qnfAddNegLeft (ihqElimCoeff targetVector pivotRow pivotPosition),
    ihqRowScaleZeroScalar pivotRow, hPivotLen]
  exact ihqRowAddZeroLeft targetVector width hTargetLen

/-- THE LEAD RAISE (F2's xor-raises-the-lead, rebuilt on field cancellation):
eliminating a vector against a pivot row sharing its lead strictly raises any
surviving lead. -/
theorem ihqElimStepLeadRaises {width : Nat} (targetVector pivotRow : List QnfRat)
    (pivotPosition : Nat) (hTargetLen : targetVector.length = width)
    (hPivotLen : pivotRow.length = width)
    (hTargetLead : ihqLead targetVector = some pivotPosition)
    (hPivotLead : ihqLead pivotRow = some pivotPosition) :
    (resultLead : Nat) ->
    ihqLead (ihqElimStep targetVector pivotRow pivotPosition) = some resultLead ->
    ihqNatLe (pivotPosition + 1) resultLead = true := by
  intro resultLead hResultLead
  have hResultCoeff := ihqLeadCoeffBeqFalse
    (ihqElimStep targetVector pivotRow pivotPosition) resultLead hResultLead
  cases hCompare : ihqNatCompare resultLead pivotPosition with
  | isLt =>
      have hZeroCoeff : ihqGetCoeff (ihqElimStep targetVector pivotRow pivotPosition)
          resultLead = qnfZero :=
        ihqElimStepKeepsZero targetVector pivotRow pivotPosition resultLead
          hTargetLen hPivotLen
          (ihqLeadCoeffBelowZero targetVector pivotPosition resultLead
            hTargetLead hCompare)
          (ihqLeadCoeffBelowZero pivotRow pivotPosition resultLead hPivotLead hCompare)
      rw [ihqQnfBeqZeroTrueOfEqZero hZeroCoeff] at hResultCoeff
      exact Bool.noConfusion hResultCoeff
  | isEq =>
      have hSame : resultLead = pivotPosition :=
        ihqNatCompareEqImpliesEq resultLead pivotPosition hCompare
      have hZeroCoeff : ihqGetCoeff (ihqElimStep targetVector pivotRow pivotPosition)
          resultLead = qnfZero := by
        rw [hSame]
        exact ihqElimStepCancelsPivot targetVector pivotRow pivotPosition
          hTargetLen hPivotLen
          (ihqLeadCoeffBeqFalse pivotRow pivotPosition hPivotLead)
      rw [ihqQnfBeqZeroTrueOfEqZero hZeroCoeff] at hResultCoeff
      exact Bool.noConfusion hResultCoeff
  | isGt =>
      exact ihqNatLeSuccOfCompareLt pivotPosition resultLead
        (ihqNatCompareGtFlip resultLead pivotPosition hCompare)

/-! ## Stage 2 — spans: linear-combination membership -/

/-- Cons-only list membership for rows (fresh, monomorphic). -/
inductive IhqRowMem : List QnfRat -> List (List QnfRat) -> Prop where
  | head (row : List QnfRat) (restRows : List (List QnfRat)) : IhqRowMem row (row :: restRows)
  | tail {row otherRow : List QnfRat} {restRows : List (List QnfRat)}
      (hRest : IhqRowMem row restRows) : IhqRowMem row (otherRow :: restRows)

/-- Every row of the list has the given width. -/
inductive IhqAllWidth (width : Nat) : List (List QnfRat) -> Prop where
  | nil : IhqAllWidth width []
  | cons {headRow : List QnfRat} {restRows : List (List QnfRat)}
      (hHead : headRow.length = width) (hRest : IhqAllWidth width restRows) :
      IhqAllWidth width (headRow :: restRows)

/-- Membership in the ℚ span of a generator list: the zero row, closed under
adding a scalar multiple of a generator — linear-combination membership with
`QnfRat` scalars. -/
inductive IhqMemSpan (width : Nat) (rows : List (List QnfRat)) : List QnfRat -> Prop where
  | zero : IhqMemSpan width rows (ihqZeroRow width)
  | pick {vector : List QnfRat} (scalar : QnfRat) (row : List QnfRat)
      (hRow : IhqRowMem row rows) (hVec : IhqMemSpan width rows vector) :
      IhqMemSpan width rows (ihqRowAdd (ihqRowScale scalar row) vector)

theorem ihqAllWidthRow {width : Nat} {rows : List (List QnfRat)} {row : List QnfRat}
    (hAll : IhqAllWidth width rows) (hRow : IhqRowMem row rows) : row.length = width := by
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

theorem ihqMemSpanWidth {width : Nat} {rows : List (List QnfRat)} {vector : List QnfRat}
    (hAll : IhqAllWidth width rows) (hMem : IhqMemSpan width rows vector) :
    vector.length = width := by
  induction hMem with
  | zero => exact ihqZeroRowLength width
  | pick scalar row hRow _hVec innerWidth =>
      exact ihqRowAddLength (ihqRowScale scalar row) _ width
        ((ihqRowScaleLength scalar row).trans (ihqAllWidthRow hAll hRow)) innerWidth

theorem ihqMemSpanWeaken {width : Nat} {rows : List (List QnfRat)} {vector : List QnfRat}
    (extraRow : List QnfRat) (hMem : IhqMemSpan width rows vector) :
    IhqMemSpan width (extraRow :: rows) vector := by
  induction hMem with
  | zero => exact IhqMemSpan.zero
  | pick scalar row hRow _hVec innerMem =>
      exact IhqMemSpan.pick scalar row (IhqRowMem.tail hRow) innerMem

/-- Every generator row belongs to its own span (scalar one). -/
theorem ihqMemSpanElem {width : Nat} {rows : List (List QnfRat)} {row : List QnfRat}
    (hAll : IhqAllWidth width rows) (hRow : IhqRowMem row rows) :
    IhqMemSpan width rows row := by
  have hPicked := IhqMemSpan.pick qnfOne row hRow
    (IhqMemSpan.zero (width := width) (rows := rows))
  rw [ihqRowScaleOne row, ihqRowAddZeroRight row width (ihqAllWidthRow hAll hRow)]
    at hPicked
  exact hPicked

/-- Spans are closed under addition. -/
theorem ihqMemSpanAddClosed {width : Nat} {rows : List (List QnfRat)}
    {firstVec secondVec : List QnfRat} (hAll : IhqAllWidth width rows)
    (hFirst : IhqMemSpan width rows firstVec) (hSecond : IhqMemSpan width rows secondVec) :
    IhqMemSpan width rows (ihqRowAdd firstVec secondVec) := by
  induction hFirst with
  | zero =>
      rw [ihqRowAddZeroLeft secondVec width (ihqMemSpanWidth hAll hSecond)]
      exact hSecond
  | pick scalar row hRow _hVec innerMem =>
      rw [ihqRowAddAssoc]
      exact IhqMemSpan.pick scalar row hRow innerMem

/-- Spans are closed under scaling. -/
theorem ihqMemSpanScaleClosed {width : Nat} {rows : List (List QnfRat)}
    {vector : List QnfRat} (outerScalar : QnfRat)
    (hMem : IhqMemSpan width rows vector) :
    IhqMemSpan width rows (ihqRowScale outerScalar vector) := by
  induction hMem with
  | zero =>
      rw [ihqRowScaleZeroRow outerScalar width]
      exact IhqMemSpan.zero
  | pick scalar row hRow _hVec innerMem =>
      rw [ihqRowScaleAddDistrib outerScalar (ihqRowScale scalar row) _,
        ihqRowScaleScale outerScalar scalar row]
      exact IhqMemSpan.pick (qnfMul outerScalar scalar) row hRow innerMem

/-- Spans are closed under negation. -/
theorem ihqMemSpanNegClosed {width : Nat} {rows : List (List QnfRat)}
    {vector : List QnfRat} (hMem : IhqMemSpan width rows vector) :
    IhqMemSpan width rows (ihqRowNeg vector) := by
  rw [ihqRowNegAsScale vector]
  exact ihqMemSpanScaleClosed (qnfNeg qnfOne) hMem

/-- Substitution: if every generator of the source lies in the target span, the
whole source span does. -/
theorem ihqMemSpanSub {width : Nat} {sourceRows targetRows : List (List QnfRat)}
    (hTargetAll : IhqAllWidth width targetRows)
    (hCover : (row : List QnfRat) -> IhqRowMem row sourceRows ->
      IhqMemSpan width targetRows row)
    {vector : List QnfRat} (hMem : IhqMemSpan width sourceRows vector) :
    IhqMemSpan width targetRows vector := by
  induction hMem with
  | zero => exact IhqMemSpan.zero
  | pick scalar row hRow _hVec innerMem =>
      exact ihqMemSpanAddClosed hTargetAll
        (ihqMemSpanScaleClosed scalar (hCover row hRow)) innerMem

/-- The span of no generators is exactly the zero row. -/
theorem ihqMemSpanNilInv {width : Nat} {vector : List QnfRat}
    (hMem : IhqMemSpan width [] vector) : vector = ihqZeroRow width := by
  induction hMem with
  | zero => rfl
  | pick scalar row hRow _hVec _innerEq => exact nomatch hRow

/-- Inversion at a cons: a span member either avoids the head generator or splits
off ONE scalar multiple of it. -/
theorem ihqMemSpanConsInv {width : Nat} {headRow : List QnfRat}
    {restRows : List (List QnfRat)} {vector : List QnfRat}
    (hMem : IhqMemSpan width (headRow :: restRows) vector) :
    IhqMemSpan width restRows vector \/
      Exists fun headScalar => Exists fun partner =>
        IhqMemSpan width restRows partner
          /\ vector = ihqRowAdd (ihqRowScale headScalar headRow) partner := by
  induction hMem with
  | zero => exact Or.inl IhqMemSpan.zero
  | pick scalar row hRow hVec innerSplit =>
      cases hRow with
      | head =>
          cases innerSplit with
          | inl hInRest =>
              exact Or.inr (Exists.intro scalar (Exists.intro _
                (And.intro hInRest rfl)))
          | inr hSplit =>
              cases hSplit with
              | intro innerScalar hPack =>
                  cases hPack with
                  | intro partner hBoth =>
                      refine Or.inr (Exists.intro (qnfAdd scalar innerScalar)
                        (Exists.intro partner (And.intro hBoth.left ?_)))
                      rw [hBoth.right,
                        ihqRowScaleMergeOnHead scalar innerScalar headRow partner]
      | tail hRowRest =>
          cases innerSplit with
          | inl hInRest =>
              exact Or.inl (IhqMemSpan.pick scalar row hRowRest hInRest)
          | inr hSplit =>
              cases hSplit with
              | intro innerScalar hPack =>
                  cases hPack with
                  | intro partner hBoth =>
                      refine Or.inr (Exists.intro innerScalar
                        (Exists.intro (ihqRowAdd (ihqRowScale scalar row) partner)
                          (And.intro (IhqMemSpan.pick scalar row hRowRest hBoth.left) ?_)))
                      rw [hBoth.right]
                      exact ihqRowAddSwapLeft (ihqRowScale scalar row)
                        (ihqRowScale innerScalar headRow) partner

/-- A position at which every generator vanishes also vanishes on the span. -/
theorem ihqMemSpanCoeffZero {width : Nat} {rows : List (List QnfRat)} (position : Nat)
    (hAll : IhqAllWidth width rows)
    (hRowsCoeff : (row : List QnfRat) -> IhqRowMem row rows ->
      ihqGetCoeff row position = qnfZero)
    {vector : List QnfRat} (hMem : IhqMemSpan width rows vector) :
    ihqGetCoeff vector position = qnfZero := by
  induction hMem with
  | zero => exact ihqGetCoeffZeroRow width position
  | pick scalar row hRow hVec innerCoeff =>
      rw [ihqGetCoeffAdd (ihqRowScale scalar row) _ (by
          rw [ihqRowScaleLength scalar row, ihqAllWidthRow hAll hRow,
            ihqMemSpanWidth hAll hVec]) position,
        ihqGetCoeffScale scalar row position, hRowsCoeff row hRow, innerCoeff,
        grqQnfMulZeroRight scalar, qnfAddZeroLeft]

/-- An all-zero leading block on every generator survives onto the span. -/
theorem ihqMemSpanTakeAllZero {width : Nat} {rows : List (List QnfRat)} (blockWidth : Nat)
    (hRowsTake : (row : List QnfRat) -> IhqRowMem row rows ->
      ihqAreAllCoeffsZero (ihqTakeN blockWidth row) = true)
    {vector : List QnfRat} (hMem : IhqMemSpan width rows vector) :
    ihqAreAllCoeffsZero (ihqTakeN blockWidth vector) = true := by
  induction hMem with
  | zero =>
      exact ihqAreAllCoeffsZeroTakeN (ihqZeroRow width)
        (ihqAreAllCoeffsZeroZeroRow width) blockWidth
  | pick scalar row hRow _hVec innerTake =>
      rw [ihqTakeNAdd blockWidth (ihqRowScale scalar row) _,
        ihqTakeNScale scalar blockWidth row]
      exact ihqAreAllCoeffsZeroAdd _ _
        (ihqAreAllCoeffsZeroScale scalar _ (hRowsTake row hRow)) innerTake

/-! ## Stage 3 — echelonization by sorted insertion with exact pivoting

Design decision (the F2 commission's fallback, kept): the CANONICAL span decision
is MUTUAL REDUCTION, whose soundness/completeness need only the row-ECHELON
invariant (strictly increasing leads), not full reducedness. -/

/-- The rows are in echelon form with all leads at or above the bound. -/
inductive IhqEchelonFrom : Nat -> List (List QnfRat) -> Prop where
  | nil (lowerBound : Nat) : IhqEchelonFrom lowerBound []
  | cons {lowerBound : Nat} {headRow : List QnfRat} {restRows : List (List QnfRat)}
      (headLead : Nat) (hLead : ihqLead headRow = some headLead)
      (hBound : ihqNatLe lowerBound headLead = true)
      (hRest : IhqEchelonFrom (headLead + 1) restRows) :
      IhqEchelonFrom lowerBound (headRow :: restRows)

theorem ihqEchelonFromRowLead : (rows : List (List QnfRat)) -> (lowerBound : Nat) ->
    (row : List QnfRat) -> IhqEchelonFrom lowerBound rows -> IhqRowMem row rows ->
    Exists fun rowLead =>
      ihqLead row = some rowLead /\ ihqNatLe lowerBound rowLead = true
  | [], _lowerBound, _row, _hEch, hRow => nomatch hRow
  | _headRow :: restRows, lowerBound, row, hEch, hRow => by
      cases hEch with
      | cons headLead hLead hBound hRest =>
          cases hRow with
          | head => exact Exists.intro headLead (And.intro hLead hBound)
          | tail hRowRest =>
              have hFromRest :=
                ihqEchelonFromRowLead restRows (headLead + 1) row hRest hRowRest
              cases hFromRest with
              | intro rowLead hBoth =>
                  refine Exists.intro rowLead (And.intro hBoth.left ?_)
                  exact ihqNatLeTrans lowerBound (headLead + 1) rowLead
                    (ihqNatLeTrans lowerBound headLead (headLead + 1) hBound
                      (ihqNatLeSuccRight headLead headLead (ihqNatLeRefl headLead)))
                    hBoth.right

/-- Rows in echelon form strictly above a bound all vanish at the bound position. -/
theorem ihqEchelonRowsCoeffZero {boundPosition : Nat} {rows : List (List QnfRat)}
    (hEch : IhqEchelonFrom (boundPosition + 1) rows) (row : List QnfRat)
    (hRow : IhqRowMem row rows) : ihqGetCoeff row boundPosition = qnfZero := by
  have hLeadInfo := ihqEchelonFromRowLead rows (boundPosition + 1) row hEch hRow
  cases hLeadInfo with
  | intro rowLead hBoth =>
      exact ihqLeadCoeffBelowZero row rowLead boundPosition hBoth.left
        (ihqNatCompareLtOfLeSucc boundPosition rowLead hBoth.right)

/-- One exact-pivot insertion step: the vector walks down the echelon list; equal
leads ELIMINATE (subtract the pivot-normalized multiple) and re-insert — the
eliminated vector's lead strictly rises or dies.  All-zero vectors are no-ops. -/
def ihqInsertRow : List QnfRat -> List (List QnfRat) -> List (List QnfRat)
  | vectorToInsert, [] =>
      match ihqLead vectorToInsert with
      | none => []
      | some _insertLead => vectorToInsert :: []
  | vectorToInsert, headRow :: restRows =>
      match ihqLead vectorToInsert, ihqLead headRow with
      | none, _headLeadOpt => headRow :: restRows
      | some _insertLead, none => vectorToInsert :: headRow :: restRows
      | some insertLead, some headLead =>
          match ihqNatCompare insertLead headLead with
          | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
          | IhqOrder.isEq =>
              headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
          | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows

/-! Unfolding equations for `ihqInsertRow`. -/

theorem ihqInsertRowNilNone (vectorToInsert : List QnfRat)
    (hLeadV : ihqLead vectorToInsert = none) : ihqInsertRow vectorToInsert [] = [] := by
  show (match ihqLead vectorToInsert with
    | none => []
    | some _insertLead => vectorToInsert :: []) = []
  rw [hLeadV]

theorem ihqInsertRowNilSome (vectorToInsert : List QnfRat) (insertLead : Nat)
    (hLeadV : ihqLead vectorToInsert = some insertLead) :
    ihqInsertRow vectorToInsert [] = vectorToInsert :: [] := by
  show (match ihqLead vectorToInsert with
    | none => []
    | some _insertLead => vectorToInsert :: []) = vectorToInsert :: []
  rw [hLeadV]

theorem ihqInsertRowConsVecNone (vectorToInsert headRow : List QnfRat)
    (restRows : List (List QnfRat)) (hLeadV : ihqLead vectorToInsert = none) :
    ihqInsertRow vectorToInsert (headRow :: restRows) = headRow :: restRows := by
  show (match ihqLead vectorToInsert, ihqLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLead, some headLead =>
        match ihqNatCompare insertLead headLead with
        | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
        | IhqOrder.isEq =>
            headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
        | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = headRow :: restRows
  rw [hLeadV]

theorem ihqInsertRowConsHeadNone (vectorToInsert headRow : List QnfRat)
    (restRows : List (List QnfRat)) (insertLead : Nat)
    (hLeadV : ihqLead vectorToInsert = some insertLead)
    (hLeadH : ihqLead headRow = none) :
    ihqInsertRow vectorToInsert (headRow :: restRows)
      = vectorToInsert :: headRow :: restRows := by
  show (match ihqLead vectorToInsert, ihqLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLead, some headLead =>
        match ihqNatCompare insertLead headLead with
        | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
        | IhqOrder.isEq =>
            headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
        | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hLeadV, hLeadH]

theorem ihqInsertRowConsLt (vectorToInsert headRow : List QnfRat)
    (restRows : List (List QnfRat)) (insertLead headLead : Nat)
    (hLeadV : ihqLead vectorToInsert = some insertLead)
    (hLeadH : ihqLead headRow = some headLead)
    (hCompare : ihqNatCompare insertLead headLead = IhqOrder.isLt) :
    ihqInsertRow vectorToInsert (headRow :: restRows)
      = vectorToInsert :: headRow :: restRows := by
  show (match ihqLead vectorToInsert, ihqLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match ihqNatCompare insertLeadInner headLeadInner with
        | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
        | IhqOrder.isEq =>
            headRow
              :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLeadInner) restRows
        | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hLeadV, hLeadH]
  show (match ihqNatCompare insertLead headLead with
    | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
    | IhqOrder.isEq =>
        headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
    | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = vectorToInsert :: headRow :: restRows
  rw [hCompare]

theorem ihqInsertRowConsEq (vectorToInsert headRow : List QnfRat)
    (restRows : List (List QnfRat)) (insertLead headLead : Nat)
    (hLeadV : ihqLead vectorToInsert = some insertLead)
    (hLeadH : ihqLead headRow = some headLead)
    (hCompare : ihqNatCompare insertLead headLead = IhqOrder.isEq) :
    ihqInsertRow vectorToInsert (headRow :: restRows)
      = headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows := by
  show (match ihqLead vectorToInsert, ihqLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match ihqNatCompare insertLeadInner headLeadInner with
        | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
        | IhqOrder.isEq =>
            headRow
              :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLeadInner) restRows
        | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
  rw [hLeadV, hLeadH]
  show (match ihqNatCompare insertLead headLead with
    | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
    | IhqOrder.isEq =>
        headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
    | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
  rw [hCompare]

theorem ihqInsertRowConsGt (vectorToInsert headRow : List QnfRat)
    (restRows : List (List QnfRat)) (insertLead headLead : Nat)
    (hLeadV : ihqLead vectorToInsert = some insertLead)
    (hLeadH : ihqLead headRow = some headLead)
    (hCompare : ihqNatCompare insertLead headLead = IhqOrder.isGt) :
    ihqInsertRow vectorToInsert (headRow :: restRows)
      = headRow :: ihqInsertRow vectorToInsert restRows := by
  show (match ihqLead vectorToInsert, ihqLead headRow with
    | none, _headLeadOpt => headRow :: restRows
    | some _insertLead, none => vectorToInsert :: headRow :: restRows
    | some insertLeadInner, some headLeadInner =>
        match ihqNatCompare insertLeadInner headLeadInner with
        | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
        | IhqOrder.isEq =>
            headRow
              :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLeadInner) restRows
        | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = headRow :: ihqInsertRow vectorToInsert restRows
  rw [hLeadV, hLeadH]
  show (match ihqNatCompare insertLead headLead with
    | IhqOrder.isLt => vectorToInsert :: headRow :: restRows
    | IhqOrder.isEq =>
        headRow :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead) restRows
    | IhqOrder.isGt => headRow :: ihqInsertRow vectorToInsert restRows)
    = headRow :: ihqInsertRow vectorToInsert restRows
  rw [hCompare]

/-- Gaussian echelonization over ℚ by repeated insertion. -/
def ihqEchelonize : List (List QnfRat) -> List (List QnfRat)
  | [] => []
  | headRow :: restRows => ihqInsertRow headRow (ihqEchelonize restRows)

theorem ihqInsertRowWidth {width : Nat} : (rows : List (List QnfRat)) ->
    (vectorToInsert : List QnfRat) -> vectorToInsert.length = width ->
    IhqAllWidth width rows -> IhqAllWidth width (ihqInsertRow vectorToInsert rows)
  | [], vectorToInsert, hVecLen, _hAll => by
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowNilNone vectorToInsert hLeadV]
          exact IhqAllWidth.nil
      | some insertLead =>
          rw [ihqInsertRowNilSome vectorToInsert insertLead hLeadV]
          exact IhqAllWidth.cons hVecLen IhqAllWidth.nil
  | headRow :: restRows, vectorToInsert, hVecLen, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
          exact hAll
      | some insertLead =>
          cases hLeadH : ihqLead headRow with
          | none =>
              rw [ihqInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH]
              exact IhqAllWidth.cons hVecLen hAll
          | some headLead =>
              cases hCompare : ihqNatCompare insertLead headLead with
              | isLt =>
                  rw [ihqInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact IhqAllWidth.cons hVecLen hAll
              | isEq =>
                  rw [ihqInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact IhqAllWidth.cons hHead
                    (ihqInsertRowWidth restRows (ihqElimStep vectorToInsert headRow headLead)
                      (ihqElimStepLength vectorToInsert headRow headLead hVecLen hHead)
                      hRestAll)
              | isGt =>
                  rw [ihqInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact IhqAllWidth.cons hHead
                    (ihqInsertRowWidth restRows vectorToInsert hVecLen hRestAll)

theorem ihqEchelonizeWidth {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> IhqAllWidth width (ihqEchelonize rows)
  | [], _hAll => IhqAllWidth.nil
  | headRow :: restRows, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      exact ihqInsertRowWidth (ihqEchelonize restRows) headRow hHead
        (ihqEchelonizeWidth restRows hRestAll)

/-- Insertion preserves the echelon invariant. -/
theorem ihqInsertRowEchelonFrom {width : Nat} : (rows : List (List QnfRat)) ->
    (vectorToInsert : List QnfRat) -> (lowerBound : Nat) ->
    vectorToInsert.length = width -> IhqAllWidth width rows ->
    ((insertLead : Nat) -> ihqLead vectorToInsert = some insertLead ->
      ihqNatLe lowerBound insertLead = true) ->
    IhqEchelonFrom lowerBound rows ->
    IhqEchelonFrom lowerBound (ihqInsertRow vectorToInsert rows)
  | [], vectorToInsert, lowerBound, _hVecLen, _hAll, hBoundOf, _hEch => by
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowNilNone vectorToInsert hLeadV]
          exact IhqEchelonFrom.nil lowerBound
      | some insertLead =>
          rw [ihqInsertRowNilSome vectorToInsert insertLead hLeadV]
          exact IhqEchelonFrom.cons insertLead hLeadV (hBoundOf insertLead hLeadV)
            (IhqEchelonFrom.nil (insertLead + 1))
  | headRow :: restRows, vectorToInsert, lowerBound, hVecLen, hAll, hBoundOf, hEch => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH hHeadBound hRest =>
          cases hLeadV : ihqLead vectorToInsert with
          | none =>
              rw [ihqInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
              exact IhqEchelonFrom.cons headLead hLeadH hHeadBound hRest
          | some insertLead =>
              cases hCompare : ihqNatCompare insertLead headLead with
              | isLt =>
                  rw [ihqInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  exact IhqEchelonFrom.cons insertLead hLeadV (hBoundOf insertLead hLeadV)
                    (IhqEchelonFrom.cons headLead hLeadH
                      (ihqNatLeSuccOfCompareLt insertLead headLead hCompare) hRest)
              | isEq =>
                  rw [ihqInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hSameLead : insertLead = headLead :=
                    ihqNatCompareEqImpliesEq insertLead headLead hCompare
                  refine IhqEchelonFrom.cons headLead hLeadH hHeadBound ?_
                  refine ihqInsertRowEchelonFrom restRows
                    (ihqElimStep vectorToInsert headRow headLead) (headLead + 1)
                    (ihqElimStepLength vectorToInsert headRow headLead hVecLen hHead)
                    hRestAll ?_ hRest
                  intro nextLead hNextLead
                  refine ihqElimStepLeadRaises vectorToInsert headRow headLead
                    hVecLen hHead ?_ hLeadH nextLead hNextLead
                  rw [<- hSameLead]
                  exact hLeadV
              | isGt =>
                  rw [ihqInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  refine IhqEchelonFrom.cons headLead hLeadH hHeadBound ?_
                  refine ihqInsertRowEchelonFrom restRows vectorToInsert (headLead + 1)
                    hVecLen hRestAll ?_ hRest
                  intro otherLead hOtherLead
                  have hSame : otherLead = insertLead := by
                    rw [hLeadV] at hOtherLead
                    exact (Option.some.inj hOtherLead).symm
                  rw [hSame]
                  exact ihqNatLeSuccOfCompareLt headLead insertLead
                    (ihqNatCompareGtFlip insertLead headLead hCompare)

theorem ihqEchelonizeEchelon {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> IhqEchelonFrom 0 (ihqEchelonize rows)
  | [], _hAll => IhqEchelonFrom.nil 0
  | headRow :: restRows, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      exact ihqInsertRowEchelonFrom (ihqEchelonize restRows) headRow 0 hHead
        (ihqEchelonizeWidth restRows hRestAll)
        (fun insertLead _hLead => ihqNatLeZeroLeft insertLead)
        (ihqEchelonizeEchelon restRows hRestAll)

/-- Every row of the inserted list lies in the span of the vector plus the old
rows. -/
theorem ihqInsertRowRowsCovered {width : Nat} : (rows : List (List QnfRat)) ->
    (vectorToInsert : List QnfRat) -> vectorToInsert.length = width ->
    IhqAllWidth width rows ->
    (row : List QnfRat) -> IhqRowMem row (ihqInsertRow vectorToInsert rows) ->
    IhqMemSpan width (vectorToInsert :: rows) row
  | [], vectorToInsert, hVecLen, _hAll, row, hRow => by
      have hFullAll : IhqAllWidth width (vectorToInsert :: ([] : List (List QnfRat))) :=
        IhqAllWidth.cons hVecLen IhqAllWidth.nil
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowNilNone vectorToInsert hLeadV] at hRow
          exact nomatch hRow
      | some insertLead =>
          rw [ihqInsertRowNilSome vectorToInsert insertLead hLeadV] at hRow
          cases hRow with
          | head => exact ihqMemSpanElem hFullAll (IhqRowMem.head vectorToInsert [])
          | tail hRowRest => exact nomatch hRowRest
  | headRow :: restRows, vectorToInsert, hVecLen, hAll, row, hRow => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hFullAll : IhqAllWidth width (vectorToInsert :: headRow :: restRows) :=
        IhqAllWidth.cons hVecLen hAll
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowConsVecNone vectorToInsert headRow restRows hLeadV] at hRow
          exact ihqMemSpanElem hFullAll (IhqRowMem.tail hRow)
      | some insertLead =>
          cases hLeadH : ihqLead headRow with
          | none =>
              rw [ihqInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH] at hRow
              exact ihqMemSpanElem hFullAll hRow
          | some headLead =>
              cases hCompare : ihqNatCompare insertLead headLead with
              | isLt =>
                  rw [ihqInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  exact ihqMemSpanElem hFullAll hRow
              | isEq =>
                  rw [ihqInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  cases hRow with
                  | head =>
                      exact ihqMemSpanElem hFullAll
                        (IhqRowMem.tail (IhqRowMem.head headRow restRows))
                  | tail hInserted =>
                      have hInner := ihqInsertRowRowsCovered restRows
                        (ihqElimStep vectorToInsert headRow headLead)
                        (ihqElimStepLength vectorToInsert headRow headLead hVecLen hHead)
                        hRestAll row hInserted
                      refine ihqMemSpanSub hFullAll ?_ hInner
                      intro generatorRow hGen
                      cases hGen with
                      | head =>
                          show IhqMemSpan width (vectorToInsert :: headRow :: restRows)
                            (ihqElimStep vectorToInsert headRow headLead)
                          exact IhqMemSpan.pick
                            (ihqElimCoeff vectorToInsert headRow headLead) headRow
                            (IhqRowMem.tail (IhqRowMem.head headRow restRows))
                            (ihqMemSpanElem hFullAll (IhqRowMem.head _ _))
                      | tail hGenRest =>
                          exact ihqMemSpanElem hFullAll
                            (IhqRowMem.tail (IhqRowMem.tail hGenRest))
              | isGt =>
                  rw [ihqInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare] at hRow
                  cases hRow with
                  | head =>
                      exact ihqMemSpanElem hFullAll
                        (IhqRowMem.tail (IhqRowMem.head headRow restRows))
                  | tail hInserted =>
                      have hInner := ihqInsertRowRowsCovered restRows vectorToInsert
                        hVecLen hRestAll row hInserted
                      refine ihqMemSpanSub hFullAll ?_ hInner
                      intro generatorRow hGen
                      cases hGen with
                      | head => exact ihqMemSpanElem hFullAll (IhqRowMem.head _ _)
                      | tail hGenRest =>
                          exact ihqMemSpanElem hFullAll
                            (IhqRowMem.tail (IhqRowMem.tail hGenRest))

/-- The inserted list's span covers the vector and every old row. -/
theorem ihqInsertRowSpanCovers {width : Nat} : (rows : List (List QnfRat)) ->
    (vectorToInsert : List QnfRat) -> vectorToInsert.length = width ->
    IhqAllWidth width rows ->
    IhqMemSpan width (ihqInsertRow vectorToInsert rows) vectorToInsert
      /\ ((row : List QnfRat) -> IhqRowMem row rows ->
        IhqMemSpan width (ihqInsertRow vectorToInsert rows) row)
  | [], vectorToInsert, hVecLen, _hAll => by
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowNilNone vectorToInsert hLeadV]
          refine And.intro ?_ ?_
          · rw [ihqLeadNoneToZeroRow vectorToInsert hVecLen hLeadV]
            exact IhqMemSpan.zero
          · intro row hRow
            exact nomatch hRow
      | some insertLead =>
          rw [ihqInsertRowNilSome vectorToInsert insertLead hLeadV]
          refine And.intro ?_ ?_
          · exact ihqMemSpanElem (IhqAllWidth.cons hVecLen IhqAllWidth.nil)
              (IhqRowMem.head _ _)
          · intro row hRow
            exact nomatch hRow
  | headRow :: restRows, vectorToInsert, hVecLen, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadV : ihqLead vectorToInsert with
      | none =>
          rw [ihqInsertRowConsVecNone vectorToInsert headRow restRows hLeadV]
          refine And.intro ?_ ?_
          · rw [ihqLeadNoneToZeroRow vectorToInsert hVecLen hLeadV]
            exact IhqMemSpan.zero
          · intro row hRow
            exact ihqMemSpanElem hAll hRow
      | some insertLead =>
          cases hLeadH : ihqLead headRow with
          | none =>
              rw [ihqInsertRowConsHeadNone vectorToInsert headRow restRows insertLead
                hLeadV hLeadH]
              have hFullAll : IhqAllWidth width (vectorToInsert :: headRow :: restRows) :=
                IhqAllWidth.cons hVecLen hAll
              refine And.intro (ihqMemSpanElem hFullAll (IhqRowMem.head _ _)) ?_
              intro row hRow
              exact ihqMemSpanElem hFullAll (IhqRowMem.tail hRow)
          | some headLead =>
              cases hCompare : ihqNatCompare insertLead headLead with
              | isLt =>
                  rw [ihqInsertRowConsLt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hFullAll : IhqAllWidth width
                      (vectorToInsert :: headRow :: restRows) :=
                    IhqAllWidth.cons hVecLen hAll
                  refine And.intro (ihqMemSpanElem hFullAll (IhqRowMem.head _ _)) ?_
                  intro row hRow
                  exact ihqMemSpanElem hFullAll (IhqRowMem.tail hRow)
              | isEq =>
                  rw [ihqInsertRowConsEq vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hElimLen : (ihqElimStep vectorToInsert headRow headLead).length
                      = width :=
                    ihqElimStepLength vectorToInsert headRow headLead hVecLen hHead
                  have hInner := ihqInsertRowSpanCovers restRows
                    (ihqElimStep vectorToInsert headRow headLead) hElimLen hRestAll
                  have hResultAll : IhqAllWidth width
                      (headRow
                        :: ihqInsertRow (ihqElimStep vectorToInsert headRow headLead)
                          restRows) :=
                    IhqAllWidth.cons hHead
                      (ihqInsertRowWidth restRows _ hElimLen hRestAll)
                  refine And.intro ?_ ?_
                  · have hElimMem := ihqMemSpanWeaken headRow hInner.left
                    have hPicked := IhqMemSpan.pick
                      (qnfNeg (ihqElimCoeff vectorToInsert headRow headLead)) headRow
                      (IhqRowMem.head headRow _) hElimMem
                    rw [ihqElimStepRecovers vectorToInsert headRow headLead hVecLen hHead]
                      at hPicked
                    exact hPicked
                  · intro row hRow
                    cases hRow with
                    | head => exact ihqMemSpanElem hResultAll (IhqRowMem.head _ _)
                    | tail hRowRest =>
                        exact ihqMemSpanWeaken headRow (hInner.right row hRowRest)
              | isGt =>
                  rw [ihqInsertRowConsGt vectorToInsert headRow restRows insertLead headLead
                    hLeadV hLeadH hCompare]
                  have hInner := ihqInsertRowSpanCovers restRows vectorToInsert hVecLen
                    hRestAll
                  have hResultAll : IhqAllWidth width
                      (headRow :: ihqInsertRow vectorToInsert restRows) :=
                    IhqAllWidth.cons hHead
                      (ihqInsertRowWidth restRows vectorToInsert hVecLen hRestAll)
                  refine And.intro (ihqMemSpanWeaken headRow hInner.left) ?_
                  intro row hRow
                  cases hRow with
                  | head => exact ihqMemSpanElem hResultAll (IhqRowMem.head _ _)
                  | tail hRowRest =>
                      exact ihqMemSpanWeaken headRow (hInner.right row hRowRest)

/-- Echelonization does not grow the span. -/
theorem ihqEchelonizeSpanSub1 {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> {vector : List QnfRat} ->
    IhqMemSpan width (ihqEchelonize rows) vector -> IhqMemSpan width rows vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      refine ihqMemSpanSub hAll ?_ hMem
      intro row hRow
      have hViaInsert := ihqInsertRowRowsCovered (ihqEchelonize restRows) headRow hHead
        (ihqEchelonizeWidth restRows hRestAll) row hRow
      refine ihqMemSpanSub hAll ?_ hViaInsert
      intro generatorRow hGen
      cases hGen with
      | head => exact ihqMemSpanElem hAll (IhqRowMem.head _ _)
      | tail hGenEch =>
          have hInRest := ihqEchelonizeSpanSub1 restRows hRestAll
            (ihqMemSpanElem (ihqEchelonizeWidth restRows hRestAll) hGenEch)
          exact ihqMemSpanWeaken headRow hInRest

/-- Echelonization does not shrink the span. -/
theorem ihqEchelonizeSpanSub2 {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> {vector : List QnfRat} ->
    IhqMemSpan width rows vector -> IhqMemSpan width (ihqEchelonize rows) vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hEchRestAll := ihqEchelonizeWidth restRows hRestAll
      have hCovers := ihqInsertRowSpanCovers (ihqEchelonize restRows) headRow hHead
        hEchRestAll
      have hResultAll := ihqInsertRowWidth (ihqEchelonize restRows) headRow hHead
        hEchRestAll
      refine ihqMemSpanSub hResultAll ?_ hMem
      intro row hRow
      cases hRow with
      | head => exact hCovers.left
      | tail hRowRest =>
          have hInEchRest := ihqEchelonizeSpanSub2 restRows hRestAll
            (ihqMemSpanElem hRestAll hRowRest)
          refine ihqMemSpanSub hResultAll ?_ hInEchRest
          intro generatorRow hGen
          exact hCovers.right generatorRow hGen

/-! ### Reduction against an echelon list -/

/-- Reduce a vector against a row list: for every row with a lead, eliminate the
vector's coefficient at that lead by exact pivoting (zero coefficients skip). -/
def ihqReduceAgainst : List (List QnfRat) -> List QnfRat -> List QnfRat
  | [], vector => vector
  | headRow :: restRows, vector =>
      match ihqLead headRow with
      | none => ihqReduceAgainst restRows vector
      | some headLead =>
          match qnfBeq (ihqGetCoeff vector headLead) qnfZero with
          | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
          | true => ihqReduceAgainst restRows vector

theorem ihqReduceAgainstConsNone (restRows : List (List QnfRat))
    (headRow vector : List QnfRat) (hLeadH : ihqLead headRow = none) :
    ihqReduceAgainst (headRow :: restRows) vector = ihqReduceAgainst restRows vector := by
  show (match ihqLead headRow with
    | none => ihqReduceAgainst restRows vector
    | some headLead =>
        match qnfBeq (ihqGetCoeff vector headLead) qnfZero with
        | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
        | true => ihqReduceAgainst restRows vector) = ihqReduceAgainst restRows vector
  rw [hLeadH]

theorem ihqReduceAgainstConsElim (restRows : List (List QnfRat))
    (headRow vector : List QnfRat) (headLead : Nat)
    (hLeadH : ihqLead headRow = some headLead)
    (hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero = false) :
    ihqReduceAgainst (headRow :: restRows) vector
      = ihqReduceAgainst restRows (ihqElimStep vector headRow headLead) := by
  show (match ihqLead headRow with
    | none => ihqReduceAgainst restRows vector
    | some headLeadInner =>
        match qnfBeq (ihqGetCoeff vector headLeadInner) qnfZero with
        | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLeadInner)
        | true => ihqReduceAgainst restRows vector)
    = ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
  rw [hLeadH]
  show (match qnfBeq (ihqGetCoeff vector headLead) qnfZero with
    | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
    | true => ihqReduceAgainst restRows vector)
    = ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
  rw [hCoeff]

theorem ihqReduceAgainstConsSkip (restRows : List (List QnfRat))
    (headRow vector : List QnfRat) (headLead : Nat)
    (hLeadH : ihqLead headRow = some headLead)
    (hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero = true) :
    ihqReduceAgainst (headRow :: restRows) vector = ihqReduceAgainst restRows vector := by
  show (match ihqLead headRow with
    | none => ihqReduceAgainst restRows vector
    | some headLeadInner =>
        match qnfBeq (ihqGetCoeff vector headLeadInner) qnfZero with
        | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLeadInner)
        | true => ihqReduceAgainst restRows vector) = ihqReduceAgainst restRows vector
  rw [hLeadH]
  show (match qnfBeq (ihqGetCoeff vector headLead) qnfZero with
    | false => ihqReduceAgainst restRows (ihqElimStep vector headRow headLead)
    | true => ihqReduceAgainst restRows vector) = ihqReduceAgainst restRows vector
  rw [hCoeff]

theorem ihqReduceAgainstWidth {width : Nat} : (rows : List (List QnfRat)) ->
    (vector : List QnfRat) -> IhqAllWidth width rows -> vector.length = width ->
    (ihqReduceAgainst rows vector).length = width
  | [], _vector, _hAll, hVecLen => hVecLen
  | headRow :: restRows, vector, hAll, hVecLen => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [ihqReduceAgainstConsNone restRows headRow vector hLeadH]
          exact ihqReduceAgainstWidth restRows vector hRestAll hVecLen
      | some headLead =>
          cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
          | false =>
              rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
              exact ihqReduceAgainstWidth restRows (ihqElimStep vector headRow headLead)
                hRestAll (ihqElimStepLength vector headRow headLead hVecLen hHead)
          | true =>
              rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff]
              exact ihqReduceAgainstWidth restRows vector hRestAll hVecLen

/-- Reduction soundness: the vector and its reduction differ by a span member. -/
theorem ihqReduceAgainstSound {width : Nat} : (rows : List (List QnfRat)) ->
    (vector : List QnfRat) -> IhqAllWidth width rows -> vector.length = width ->
    IhqMemSpan width rows
      (ihqRowAdd vector (ihqRowNeg (ihqReduceAgainst rows vector)))
  | [], vector, _hAll, hVecLen => by
      show IhqMemSpan width [] (ihqRowAdd vector (ihqRowNeg vector))
      rw [ihqRowAddNegRight vector, hVecLen]
      exact IhqMemSpan.zero
  | headRow :: restRows, vector, hAll, hVecLen => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [ihqReduceAgainstConsNone restRows headRow vector hLeadH]
          exact ihqMemSpanWeaken headRow
            (ihqReduceAgainstSound restRows vector hRestAll hVecLen)
      | some headLead =>
          cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
          | false =>
              rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
              have hElimLen : (ihqElimStep vector headRow headLead).length = width :=
                ihqElimStepLength vector headRow headLead hVecLen hHead
              have hInner := ihqMemSpanWeaken headRow
                (ihqReduceAgainstSound restRows (ihqElimStep vector headRow headLead)
                  hRestAll hElimLen)
              have hPicked := IhqMemSpan.pick
                (qnfNeg (ihqElimCoeff vector headRow headLead)) headRow
                (IhqRowMem.head headRow restRows) hInner
              rw [<- ihqRowAddAssoc
                  (ihqRowScale (qnfNeg (ihqElimCoeff vector headRow headLead)) headRow)
                  (ihqElimStep vector headRow headLead)
                  (ihqRowNeg (ihqReduceAgainst restRows
                    (ihqElimStep vector headRow headLead))),
                ihqElimStepRecovers vector headRow headLead hVecLen hHead] at hPicked
              exact hPicked
          | true =>
              rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff]
              exact ihqMemSpanWeaken headRow
                (ihqReduceAgainstSound restRows vector hRestAll hVecLen)

/-- A vector whose reduction is all-zero lies in the span. -/
theorem ihqReduceAgainstMember {width : Nat} (rows : List (List QnfRat))
    (vector : List QnfRat) (hAll : IhqAllWidth width rows)
    (hVecLen : vector.length = width)
    (hZero : ihqAreAllCoeffsZero (ihqReduceAgainst rows vector) = true) :
    IhqMemSpan width rows vector := by
  have hReducedZero : ihqReduceAgainst rows vector = ihqZeroRow width := by
    have hToZero := ihqZeroRowOfAllCoeffsZero _ hZero
    rw [ihqReduceAgainstWidth rows vector hAll hVecLen] at hToZero
    exact hToZero
  have hSound := ihqReduceAgainstSound rows vector hAll hVecLen
  rw [hReducedZero, ihqRowNegZeroRow width,
    ihqRowAddZeroRight vector width hVecLen] at hSound
  exact hSound

/-- Reduction completeness against an echelon list: every span member reduces to
all-zero.  The two genuinely-ℚ side conditions (the split scalar may be ZERO; the
elimination may collapse the whole head contribution) are discharged by the
integral-domain step. -/
theorem ihqReduceAgainstComplete {width : Nat} : {lowerBound : Nat} ->
    (rows : List (List QnfRat)) -> (vector : List QnfRat) ->
    IhqAllWidth width rows -> IhqEchelonFrom lowerBound rows ->
    IhqMemSpan width rows vector ->
    ihqAreAllCoeffsZero (ihqReduceAgainst rows vector) = true
  | _lowerBound, [], vector, _hAll, _hEch, hMem => by
      show ihqAreAllCoeffsZero vector = true
      rw [ihqMemSpanNilInv hMem]
      exact ihqAreAllCoeffsZeroZeroRow width
  | _lowerBound, headRow :: restRows, vector, hAll, hEch, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hVecLen : vector.length = width := ihqMemSpanWidth hAll hMem
      cases hEch with
      | cons headLead hLeadH _hBound hRest =>
          have hRestCoeffsZero : (row : List QnfRat) -> IhqRowMem row restRows ->
              ihqGetCoeff row headLead = qnfZero := fun row hRow =>
            ihqEchelonRowsCoeffZero hRest row hRow
          have hPivotBeq := ihqLeadCoeffBeqFalse headRow headLead hLeadH
          have hPivotNe := ihqQnfNeZeroOfBeqZeroFalse hPivotBeq
          have hSplit := ihqMemSpanConsInv hMem
          cases hSplit with
          | inl hInRest =>
              have hCoeffZero : ihqGetCoeff vector headLead = qnfZero :=
                ihqMemSpanCoeffZero headLead hRestAll hRestCoeffsZero hInRest
              rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH
                (ihqQnfBeqZeroTrueOfEqZero hCoeffZero)]
              exact ihqReduceAgainstComplete restRows vector hRestAll hRest hInRest
          | inr hSplitPack =>
              cases hSplitPack with
              | intro headScalar hPartnerPack =>
                  cases hPartnerPack with
                  | intro partner hBoth =>
                      have hPartnerLen : partner.length = width :=
                        ihqMemSpanWidth hRestAll hBoth.left
                      have hPartnerCoeff : ihqGetCoeff partner headLead = qnfZero :=
                        ihqMemSpanCoeffZero headLead hRestAll hRestCoeffsZero hBoth.left
                      have hVecCoeff : ihqGetCoeff vector headLead
                          = qnfMul headScalar (ihqGetCoeff headRow headLead) := by
                        rw [hBoth.right,
                          ihqGetCoeffAdd (ihqRowScale headScalar headRow) partner
                            (by rw [ihqRowScaleLength, hHead, hPartnerLen]) headLead,
                          ihqGetCoeffScale headScalar headRow headLead, hPartnerCoeff,
                          qnfAddZeroRight]
                      cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
                      | true =>
                          have hScalarZero : headScalar = qnfZero :=
                            ihqQnfFactorZeroOfMulPivotZero hPivotNe
                              (hVecCoeff.symm.trans (ihqQnfEqZeroOfBeqZeroTrue hCoeff))
                          have hVecIsPartner : vector = partner := by
                            rw [hBoth.right, hScalarZero, ihqRowScaleZeroScalar headRow,
                              hHead]
                            exact ihqRowAddZeroLeft partner width hPartnerLen
                          rw [ihqReduceAgainstConsSkip restRows headRow vector headLead
                            hLeadH hCoeff, hVecIsPartner]
                          exact ihqReduceAgainstComplete restRows partner hRestAll hRest
                            hBoth.left
                      | false =>
                          rw [ihqReduceAgainstConsElim restRows headRow vector headLead
                            hLeadH hCoeff]
                          -- the eliminated vector IS the partner: the head
                          -- contribution collapses through the field cancellation
                          have hElimLen : (ihqElimStep vector headRow headLead).length
                              = width :=
                            ihqElimStepLength vector headRow headLead hVecLen hHead
                          have hMergeGeneric : (anyScalar : QnfRat) ->
                              ihqRowAdd (ihqRowScale anyScalar headRow) vector
                                = ihqRowAdd
                                    (ihqRowScale (qnfAdd anyScalar headScalar) headRow)
                                    partner := by
                            intro anyScalar
                            rw [hBoth.right, ihqRowScaleMergeOnHead anyScalar headScalar
                              headRow partner]
                          have hElimAsMerge : ihqElimStep vector headRow headLead
                              = ihqRowAdd
                                  (ihqRowScale
                                    (qnfAdd (ihqElimCoeff vector headRow headLead)
                                      headScalar) headRow) partner :=
                            hMergeGeneric (ihqElimCoeff vector headRow headLead)
                          have hElimCoeffZero : ihqGetCoeff
                              (ihqElimStep vector headRow headLead) headLead = qnfZero :=
                            ihqElimStepCancelsPivot vector headRow headLead hVecLen hHead
                              hPivotBeq
                          have hMergedCoeff : ihqGetCoeff
                              (ihqElimStep vector headRow headLead) headLead
                              = qnfMul (qnfAdd (ihqElimCoeff vector headRow headLead)
                                  headScalar) (ihqGetCoeff headRow headLead) := by
                            rw [hElimAsMerge,
                              ihqGetCoeffAdd
                                (ihqRowScale (qnfAdd (ihqElimCoeff vector headRow headLead)
                                  headScalar) headRow) partner
                                (by rw [ihqRowScaleLength, hHead, hPartnerLen]) headLead,
                              ihqGetCoeffScale _ headRow headLead, hPartnerCoeff,
                              qnfAddZeroRight]
                          have hMergedScalarZero : qnfAdd
                              (ihqElimCoeff vector headRow headLead) headScalar
                              = qnfZero :=
                            ihqQnfFactorZeroOfMulPivotZero hPivotNe
                              (hMergedCoeff.symm.trans hElimCoeffZero)
                          have hElimIsPartner : ihqElimStep vector headRow headLead
                              = partner := by
                            rw [hElimAsMerge, hMergedScalarZero,
                              ihqRowScaleZeroScalar headRow, hHead]
                            exact ihqRowAddZeroLeft partner width hPartnerLen
                          rw [hElimIsPartner]
                          exact ihqReduceAgainstComplete restRows partner hRestAll hRest
                            hBoth.left

/-! ### THE SPAN DECISION: mutual reduction -/

/-- Does every row of the list reduce to all-zero against the echelon rows? -/
def ihqAllRowsReduceToZero (echelonRows : List (List QnfRat)) :
    List (List QnfRat) -> Bool
  | [] => true
  | headRow :: restRows =>
      match ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) with
      | true => ihqAllRowsReduceToZero echelonRows restRows
      | false => false

theorem ihqAllRowsReduceToZeroConsTrue (echelonRows : List (List QnfRat))
    (headRow : List QnfRat) (restRows : List (List QnfRat))
    (hCheck : ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) = true) :
    ihqAllRowsReduceToZero echelonRows (headRow :: restRows)
      = ihqAllRowsReduceToZero echelonRows restRows := by
  show (match ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) with
    | true => ihqAllRowsReduceToZero echelonRows restRows
    | false => false) = ihqAllRowsReduceToZero echelonRows restRows
  rw [hCheck]

theorem ihqAllRowsReduceToZeroConsFalse (echelonRows : List (List QnfRat))
    (headRow : List QnfRat) (restRows : List (List QnfRat))
    (hCheck : ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) = false) :
    ihqAllRowsReduceToZero echelonRows (headRow :: restRows) = false := by
  show (match ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) with
    | true => ihqAllRowsReduceToZero echelonRows restRows
    | false => false) = false
  rw [hCheck]

theorem ihqAllRowsReduceToZeroSpec1 (echelonRows : List (List QnfRat)) :
    (rows : List (List QnfRat)) -> ihqAllRowsReduceToZero echelonRows rows = true ->
    (row : List QnfRat) -> IhqRowMem row rows ->
    ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows row) = true
  | [], _hAllTrue, _row, hRow => nomatch hRow
  | headRow :: restRows, hAllTrue, row, hRow => by
      cases hCheck : ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows headRow) with
      | true =>
          rw [ihqAllRowsReduceToZeroConsTrue echelonRows headRow restRows hCheck] at hAllTrue
          cases hRow with
          | head => exact hCheck
          | tail hRowRest =>
              exact ihqAllRowsReduceToZeroSpec1 echelonRows restRows hAllTrue row hRowRest
      | false =>
          rw [ihqAllRowsReduceToZeroConsFalse echelonRows headRow restRows hCheck]
            at hAllTrue
          exact Bool.noConfusion hAllTrue

theorem ihqAllRowsReduceToZeroSpec2 (echelonRows : List (List QnfRat)) :
    (rows : List (List QnfRat)) ->
    ((row : List QnfRat) -> IhqRowMem row rows ->
      ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows row) = true) ->
    ihqAllRowsReduceToZero echelonRows rows = true
  | [], _hEach => rfl
  | headRow :: restRows, hEach => by
      rw [ihqAllRowsReduceToZeroConsTrue echelonRows headRow restRows
        (hEach headRow (IhqRowMem.head headRow restRows))]
      exact ihqAllRowsReduceToZeroSpec2 echelonRows restRows
        (fun row hRow => hEach row (IhqRowMem.tail hRow))

/-- Bool span inclusion: every generator of the first list reduces to zero
against the echelonization of the second. -/
def ihqSpanLeB (firstRows secondRows : List (List QnfRat)) : Bool :=
  ihqAllRowsReduceToZero (ihqEchelonize secondRows) firstRows

/-- **THE SPAN DECISION** — Bool span equality by mutual inclusion. -/
def ihqSpanEqB (firstRows secondRows : List (List QnfRat)) : Bool :=
  match ihqSpanLeB firstRows secondRows with
  | true => ihqSpanLeB secondRows firstRows
  | false => false

theorem ihqSpanEqBOfLe (firstRows secondRows : List (List QnfRat))
    (hForward : ihqSpanLeB firstRows secondRows = true) :
    ihqSpanEqB firstRows secondRows = ihqSpanLeB secondRows firstRows := by
  show (match ihqSpanLeB firstRows secondRows with
    | true => ihqSpanLeB secondRows firstRows
    | false => false) = ihqSpanLeB secondRows firstRows
  rw [hForward]

theorem ihqSpanEqBOfNotLe (firstRows secondRows : List (List QnfRat))
    (hForward : ihqSpanLeB firstRows secondRows = false) :
    ihqSpanEqB firstRows secondRows = false := by
  show (match ihqSpanLeB firstRows secondRows with
    | true => ihqSpanLeB secondRows firstRows
    | false => false) = false
  rw [hForward]

theorem ihqSpanLeBSound {width : Nat} {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth width firstRows) (hSecondAll : IhqAllWidth width secondRows)
    (hLe : ihqSpanLeB firstRows secondRows = true) {vector : List QnfRat}
    (hMem : IhqMemSpan width firstRows vector) : IhqMemSpan width secondRows vector := by
  refine ihqMemSpanSub hSecondAll ?_ hMem
  intro row hRow
  have hRowReduces := ihqAllRowsReduceToZeroSpec1 (ihqEchelonize secondRows) firstRows
    hLe row hRow
  have hInEch := ihqReduceAgainstMember (ihqEchelonize secondRows) row
    (ihqEchelonizeWidth secondRows hSecondAll) (ihqAllWidthRow hFirstAll hRow) hRowReduces
  exact ihqEchelonizeSpanSub1 secondRows hSecondAll hInEch

theorem ihqSpanLeBComplete {width : Nat} {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth width firstRows) (hSecondAll : IhqAllWidth width secondRows)
    (hSub : (vector : List QnfRat) -> IhqMemSpan width firstRows vector ->
      IhqMemSpan width secondRows vector) :
    ihqSpanLeB firstRows secondRows = true := by
  refine ihqAllRowsReduceToZeroSpec2 (ihqEchelonize secondRows) firstRows ?_
  intro row hRow
  have hInSecond := hSub row (ihqMemSpanElem hFirstAll hRow)
  have hInEch := ihqEchelonizeSpanSub2 secondRows hSecondAll hInSecond
  exact ihqReduceAgainstComplete (ihqEchelonize secondRows) row
    (ihqEchelonizeWidth secondRows hSecondAll)
    (ihqEchelonizeEchelon secondRows hSecondAll) hInEch

/-- **SOUNDNESS of the span-equality decision**: `true` means the two spans have
the same members. -/
theorem ihqSpanEqBSound {width : Nat} {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth width firstRows) (hSecondAll : IhqAllWidth width secondRows)
    (hEq : ihqSpanEqB firstRows secondRows = true) (vector : List QnfRat) :
    IhqMemSpan width firstRows vector <-> IhqMemSpan width secondRows vector := by
  cases hForward : ihqSpanLeB firstRows secondRows with
  | true =>
      rw [ihqSpanEqBOfLe firstRows secondRows hForward] at hEq
      exact Iff.intro
        (fun hMem => ihqSpanLeBSound hFirstAll hSecondAll hForward hMem)
        (fun hMem => ihqSpanLeBSound hSecondAll hFirstAll hEq hMem)
  | false =>
      rw [ihqSpanEqBOfNotLe firstRows secondRows hForward] at hEq
      exact Bool.noConfusion hEq

/-- **COMPLETENESS of the span-equality decision**: same members means the
decision fires. -/
theorem ihqSpanEqBComplete {width : Nat} {firstRows secondRows : List (List QnfRat)}
    (hFirstAll : IhqAllWidth width firstRows) (hSecondAll : IhqAllWidth width secondRows)
    (hSame : (vector : List QnfRat) ->
      (IhqMemSpan width firstRows vector <-> IhqMemSpan width secondRows vector)) :
    ihqSpanEqB firstRows secondRows = true := by
  rw [ihqSpanEqBOfLe firstRows secondRows
    (ihqSpanLeBComplete hFirstAll hSecondAll (fun vector hMem => (hSame vector).mp hMem))]
  exact ihqSpanLeBComplete hSecondAll hFirstAll
    (fun vector hMem => (hSame vector).mpr hMem)

/-! ## Stage 4 — relations: generator matrices with external arities

A morphism `n -> m` is (the span of) a generator matrix of width `n + m`, domain
block first.  Arities live OUTSIDE the rows; the composition stack puts the shared
middle block LEFTMOST so the zero-middle extraction is the leftmost-pivot argument
(BSZ Lemma 5.10: composition of spans is the kernel/pullback computation). -/

/-- Cons-only concatenation of row lists (fresh, monomorphic). -/
def ihqCatRows : List (List QnfRat) -> List (List QnfRat) -> List (List QnfRat)
  | [], secondRows => secondRows
  | headRow :: restRows, secondRows => headRow :: ihqCatRows restRows secondRows

/-- Cons-only map over row lists (fresh, monomorphic). -/
def ihqMapRows (transform : List QnfRat -> List QnfRat) :
    List (List QnfRat) -> List (List QnfRat)
  | [] => []
  | headRow :: restRows => transform headRow :: ihqMapRows transform restRows

theorem ihqCatRowsMemSplit : {row : List QnfRat} ->
    (leftRows rightRows : List (List QnfRat)) ->
    IhqRowMem row (ihqCatRows leftRows rightRows) ->
    IhqRowMem row leftRows \/ IhqRowMem row rightRows
  | _row, [], _rightRows, hRow => Or.inr hRow
  | _row, _headRow :: restRows, rightRows, hRow => by
      cases hRow with
      | head => exact Or.inl (IhqRowMem.head _ _)
      | tail hRowRest =>
          cases ihqCatRowsMemSplit restRows rightRows hRowRest with
          | inl hInLeft => exact Or.inl (IhqRowMem.tail hInLeft)
          | inr hInRight => exact Or.inr hInRight

theorem ihqCatRowsMemLeft {row : List QnfRat} : (leftRows rightRows : List (List QnfRat)) ->
    IhqRowMem row leftRows -> IhqRowMem row (ihqCatRows leftRows rightRows)
  | [], _rightRows, hRow => nomatch hRow
  | _headRow :: restRows, rightRows, hRow => by
      cases hRow with
      | head => exact IhqRowMem.head _ _
      | tail hRowRest =>
          exact IhqRowMem.tail (ihqCatRowsMemLeft restRows rightRows hRowRest)

theorem ihqCatRowsMemRight : {row : List QnfRat} ->
    (leftRows rightRows : List (List QnfRat)) ->
    IhqRowMem row rightRows -> IhqRowMem row (ihqCatRows leftRows rightRows)
  | _row, [], _rightRows, hRow => hRow
  | _row, _headRow :: restRows, rightRows, hRow =>
      IhqRowMem.tail (ihqCatRowsMemRight restRows rightRows hRow)

theorem ihqCatRowsWidth {width : Nat} : (leftRows rightRows : List (List QnfRat)) ->
    IhqAllWidth width leftRows -> IhqAllWidth width rightRows ->
    IhqAllWidth width (ihqCatRows leftRows rightRows)
  | [], _rightRows, _hLeft, hRight => hRight
  | _headRow :: restRows, rightRows, hLeft, hRight => by
      cases hLeft with
      | cons hHead hRest =>
          exact IhqAllWidth.cons hHead (ihqCatRowsWidth restRows rightRows hRest hRight)

theorem ihqCatRowsSpanLeft {width : Nat} {leftRows rightRows : List (List QnfRat)}
    {vector : List QnfRat} (hMem : IhqMemSpan width leftRows vector) :
    IhqMemSpan width (ihqCatRows leftRows rightRows) vector := by
  induction hMem with
  | zero => exact IhqMemSpan.zero
  | pick scalar row hRow _hVec innerMem =>
      exact IhqMemSpan.pick scalar row (ihqCatRowsMemLeft leftRows rightRows hRow) innerMem

theorem ihqCatRowsSpanRight {width : Nat} {leftRows rightRows : List (List QnfRat)}
    {vector : List QnfRat} (hMem : IhqMemSpan width rightRows vector) :
    IhqMemSpan width (ihqCatRows leftRows rightRows) vector := by
  induction hMem with
  | zero => exact IhqMemSpan.zero
  | pick scalar row hRow _hVec innerMem =>
      exact IhqMemSpan.pick scalar row (ihqCatRowsMemRight leftRows rightRows hRow) innerMem

/-- A member of the concatenated span splits as a sum of one member from each side. -/
theorem ihqCatRowsSpanSplitFwd {width : Nat} {leftRows rightRows : List (List QnfRat)}
    (_hLeftAll : IhqAllWidth width leftRows) (_hRightAll : IhqAllWidth width rightRows)
    {vector : List QnfRat}
    (hMem : IhqMemSpan width (ihqCatRows leftRows rightRows) vector) :
    Exists fun leftPart => Exists fun rightPart =>
      IhqMemSpan width leftRows leftPart /\ IhqMemSpan width rightRows rightPart
        /\ vector = ihqRowAdd leftPart rightPart := by
  induction hMem with
  | zero =>
      refine Exists.intro (ihqZeroRow width) (Exists.intro (ihqZeroRow width)
        (And.intro IhqMemSpan.zero (And.intro IhqMemSpan.zero ?_)))
      rw [ihqRowAddZeroLeft (ihqZeroRow width) width (ihqZeroRowLength width)]
  | pick scalar row hRow _hVec innerSplit =>
      cases innerSplit with
      | intro leftPart hRightPack =>
          cases hRightPack with
          | intro rightPart hParts =>
              cases ihqCatRowsMemSplit leftRows rightRows hRow with
              | inl hInLeft =>
                  refine Exists.intro (ihqRowAdd (ihqRowScale scalar row) leftPart)
                    (Exists.intro rightPart
                      (And.intro (IhqMemSpan.pick scalar row hInLeft hParts.left)
                        (And.intro hParts.right.left ?_)))
                  rw [hParts.right.right,
                    <- ihqRowAddAssoc (ihqRowScale scalar row) leftPart rightPart]
              | inr hInRight =>
                  refine Exists.intro leftPart
                    (Exists.intro (ihqRowAdd (ihqRowScale scalar row) rightPart)
                      (And.intro hParts.left
                        (And.intro (IhqMemSpan.pick scalar row hInRight hParts.right.left)
                          ?_)))
                  rw [hParts.right.right]
                  exact ihqRowAddSwapLeft (ihqRowScale scalar row) leftPart rightPart

theorem ihqMapRowsMemInv (transform : List QnfRat -> List QnfRat) :
    {mappedRow : List QnfRat} -> (rows : List (List QnfRat)) ->
    IhqRowMem mappedRow (ihqMapRows transform rows) ->
    Exists fun sourceRow => IhqRowMem sourceRow rows /\ mappedRow = transform sourceRow
  | _mappedRow, [], hRow => nomatch hRow
  | _mappedRow, headRow :: restRows, hRow => by
      cases hRow with
      | head =>
          exact Exists.intro headRow
            (And.intro (IhqRowMem.head headRow restRows) rfl)
      | tail hRowRest =>
          have hInner := ihqMapRowsMemInv transform restRows hRowRest
          cases hInner with
          | intro sourceRow hBoth =>
              exact Exists.intro sourceRow (And.intro (IhqRowMem.tail hBoth.left) hBoth.right)

theorem ihqMapRowsMemIntro (transform : List QnfRat -> List QnfRat)
    {sourceRow : List QnfRat} :
    (rows : List (List QnfRat)) -> IhqRowMem sourceRow rows ->
    IhqRowMem (transform sourceRow) (ihqMapRows transform rows)
  | [], hRow => nomatch hRow
  | _headRow :: restRows, hRow => by
      cases hRow with
      | head => exact IhqRowMem.head _ _
      | tail hRowRest =>
          exact IhqRowMem.tail (ihqMapRowsMemIntro transform restRows hRowRest)

theorem ihqMapRowsWidth {sourceWidth targetWidth : Nat}
    (transform : List QnfRat -> List QnfRat)
    (hTransformLen : (row : List QnfRat) -> row.length = sourceWidth ->
      (transform row).length = targetWidth) :
    (rows : List (List QnfRat)) -> IhqAllWidth sourceWidth rows ->
    IhqAllWidth targetWidth (ihqMapRows transform rows)
  | [], _hAll => IhqAllWidth.nil
  | headRow :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          exact IhqAllWidth.cons (hTransformLen headRow hHead)
            (ihqMapRowsWidth transform hTransformLen restRows hRest)

/-- Span of a linearly-mapped generator list, forward: every member is the image
of a member. -/
theorem ihqMapRowsSpanFwd {sourceWidth targetWidth : Nat}
    (transform : List QnfRat -> List QnfRat)
    (hTransformZero : transform (ihqZeroRow sourceWidth) = ihqZeroRow targetWidth)
    (hTransformAdd : (firstRow secondRow : List QnfRat) ->
      firstRow.length = sourceWidth -> secondRow.length = sourceWidth ->
      transform (ihqRowAdd firstRow secondRow)
        = ihqRowAdd (transform firstRow) (transform secondRow))
    (hTransformScale : (scalar : QnfRat) -> (row : List QnfRat) ->
      row.length = sourceWidth ->
      transform (ihqRowScale scalar row) = ihqRowScale scalar (transform row))
    {rows : List (List QnfRat)} (hAll : IhqAllWidth sourceWidth rows)
    {mappedVector : List QnfRat}
    (hMem : IhqMemSpan targetWidth (ihqMapRows transform rows) mappedVector) :
    Exists fun sourceVector =>
      IhqMemSpan sourceWidth rows sourceVector /\ mappedVector = transform sourceVector := by
  induction hMem with
  | zero =>
      exact Exists.intro (ihqZeroRow sourceWidth)
        (And.intro IhqMemSpan.zero hTransformZero.symm)
  | pick scalar row hRow hVec innerSplit =>
      cases innerSplit with
      | intro sourceVector hBoth =>
          have hRowInv := ihqMapRowsMemInv transform rows hRow
          cases hRowInv with
          | intro sourceRow hRowBoth =>
              refine Exists.intro
                (ihqRowAdd (ihqRowScale scalar sourceRow) sourceVector)
                (And.intro (IhqMemSpan.pick scalar sourceRow hRowBoth.left hBoth.left) ?_)
              rw [hTransformAdd (ihqRowScale scalar sourceRow) sourceVector
                  ((ihqRowScaleLength scalar sourceRow).trans
                    (ihqAllWidthRow hAll hRowBoth.left))
                  (ihqMemSpanWidth hAll hBoth.left),
                hTransformScale scalar sourceRow (ihqAllWidthRow hAll hRowBoth.left),
                <- hRowBoth.right, <- hBoth.right]

/-- Span of a linearly-mapped generator list, backward: images of members are
members. -/
theorem ihqMapRowsSpanBwd {sourceWidth targetWidth : Nat}
    (transform : List QnfRat -> List QnfRat)
    (hTransformZero : transform (ihqZeroRow sourceWidth) = ihqZeroRow targetWidth)
    (hTransformAdd : (firstRow secondRow : List QnfRat) ->
      firstRow.length = sourceWidth -> secondRow.length = sourceWidth ->
      transform (ihqRowAdd firstRow secondRow)
        = ihqRowAdd (transform firstRow) (transform secondRow))
    (hTransformScale : (scalar : QnfRat) -> (row : List QnfRat) ->
      row.length = sourceWidth ->
      transform (ihqRowScale scalar row) = ihqRowScale scalar (transform row))
    {rows : List (List QnfRat)} (hAll : IhqAllWidth sourceWidth rows)
    {sourceVector : List QnfRat} (hMem : IhqMemSpan sourceWidth rows sourceVector) :
    IhqMemSpan targetWidth (ihqMapRows transform rows) (transform sourceVector) := by
  induction hMem with
  | zero =>
      rw [hTransformZero]
      exact IhqMemSpan.zero
  | pick scalar row hRow hVec innerMem =>
      rw [hTransformAdd (ihqRowScale scalar row) _
          ((ihqRowScaleLength scalar row).trans (ihqAllWidthRow hAll hRow))
          (ihqMemSpanWidth hAll hVec),
        hTransformScale scalar row (ihqAllWidthRow hAll hRow)]
      exact IhqMemSpan.pick scalar (transform row)
        (ihqMapRowsMemIntro transform rows hRow) innerMem

/-- Pair membership: the relation (given by generator rows of width `dom + cod`)
holds of the two boundary vectors. -/
def IhqPairMem (domWidth codWidth : Nat) (relationRows : List (List QnfRat))
    (domVec codVec : List QnfRat) : Prop :=
  domVec.length = domWidth /\ codVec.length = codWidth
    /\ IhqMemSpan (domWidth + codWidth) relationRows (ihqCat domVec codVec)

/-! ### Relational composition: stack with the shared middle LEFTMOST (second
factor's middle NEGATED), echelonize, keep the zero-middle rows, project -/

/-- Embed a first-factor row `(x | y)` as `(y, x, 0)` — middle block leftmost. -/
def ihqComposeEmbedFirst (domWidth codWidth : Nat) (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (ihqDropN domWidth rowPair)
    (ihqCat (ihqTakeN domWidth rowPair) (ihqZeroRow codWidth))

/-- Embed a second-factor row `(y | z)` as `(-y, 0, z)` — middle block leftmost and
NEGATED, so a vanishing middle sum reads `y₁ = y₂` (over F2 negation was invisible;
over ℚ it is what makes the pullback characterization come out as equality). -/
def ihqComposeEmbedSecond (midWidth domWidth : Nat) (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (ihqRowNeg (ihqTakeN midWidth rowPair))
    (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth rowPair))

/-- Keep only the rows whose first `blockWidth` coefficients are all zero. -/
def ihqFilterHeadZero (blockWidth : Nat) : List (List QnfRat) -> List (List QnfRat)
  | [] => []
  | headRow :: restRows =>
      match ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
      | true => headRow :: ihqFilterHeadZero blockWidth restRows
      | false => ihqFilterHeadZero blockWidth restRows

theorem ihqFilterHeadZeroConsTrue (blockWidth : Nat) (headRow : List QnfRat)
    (restRows : List (List QnfRat))
    (hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) = true) :
    ihqFilterHeadZero blockWidth (headRow :: restRows)
      = headRow :: ihqFilterHeadZero blockWidth restRows := by
  show (match ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
    | true => headRow :: ihqFilterHeadZero blockWidth restRows
    | false => ihqFilterHeadZero blockWidth restRows)
    = headRow :: ihqFilterHeadZero blockWidth restRows
  rw [hCheck]

theorem ihqFilterHeadZeroConsFalse (blockWidth : Nat) (headRow : List QnfRat)
    (restRows : List (List QnfRat))
    (hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) = false) :
    ihqFilterHeadZero blockWidth (headRow :: restRows)
      = ihqFilterHeadZero blockWidth restRows := by
  show (match ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
    | true => headRow :: ihqFilterHeadZero blockWidth restRows
    | false => ihqFilterHeadZero blockWidth restRows)
    = ihqFilterHeadZero blockWidth restRows
  rw [hCheck]

theorem ihqFilterHeadZeroMemSub (blockWidth : Nat) : {row : List QnfRat} ->
    (rows : List (List QnfRat)) -> IhqRowMem row (ihqFilterHeadZero blockWidth rows) ->
    IhqRowMem row rows
  | _row, [], hRow => nomatch hRow
  | row, headRow :: restRows, hRow => by
      cases hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
      | true =>
          rw [ihqFilterHeadZeroConsTrue blockWidth headRow restRows hCheck] at hRow
          cases hRow with
          | head => exact IhqRowMem.head _ _
          | tail hRowRest =>
              exact IhqRowMem.tail (ihqFilterHeadZeroMemSub blockWidth restRows hRowRest)
      | false =>
          rw [ihqFilterHeadZeroConsFalse blockWidth headRow restRows hCheck] at hRow
          exact IhqRowMem.tail (ihqFilterHeadZeroMemSub blockWidth restRows hRow)

theorem ihqFilterHeadZeroMemTake (blockWidth : Nat) : {row : List QnfRat} ->
    (rows : List (List QnfRat)) -> IhqRowMem row (ihqFilterHeadZero blockWidth rows) ->
    ihqAreAllCoeffsZero (ihqTakeN blockWidth row) = true
  | _row, [], hRow => nomatch hRow
  | row, headRow :: restRows, hRow => by
      cases hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
      | true =>
          rw [ihqFilterHeadZeroConsTrue blockWidth headRow restRows hCheck] at hRow
          cases hRow with
          | head => exact hCheck
          | tail hRowRest => exact ihqFilterHeadZeroMemTake blockWidth restRows hRowRest
      | false =>
          rw [ihqFilterHeadZeroConsFalse blockWidth headRow restRows hCheck] at hRow
          exact ihqFilterHeadZeroMemTake blockWidth restRows hRow

theorem ihqFilterHeadZeroWidth {width : Nat} (blockWidth : Nat) :
    (rows : List (List QnfRat)) -> IhqAllWidth width rows ->
    IhqAllWidth width (ihqFilterHeadZero blockWidth rows)
  | [], _hAll => IhqAllWidth.nil
  | headRow :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          cases hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
          | true =>
              rw [ihqFilterHeadZeroConsTrue blockWidth headRow restRows hCheck]
              exact IhqAllWidth.cons hHead
                (ihqFilterHeadZeroWidth blockWidth restRows hRest)
          | false =>
              rw [ihqFilterHeadZeroConsFalse blockWidth headRow restRows hCheck]
              exact ihqFilterHeadZeroWidth blockWidth restRows hRest

/-- Filtering does not grow the span. -/
theorem ihqFilterHeadZeroSpanSub {width : Nat} (blockWidth : Nat)
    {rows : List (List QnfRat)} (hAll : IhqAllWidth width rows) {vector : List QnfRat}
    (hMem : IhqMemSpan width (ihqFilterHeadZero blockWidth rows) vector) :
    IhqMemSpan width rows vector := by
  refine ihqMemSpanSub hAll ?_ hMem
  intro row hRow
  exact ihqMemSpanElem hAll (ihqFilterHeadZeroMemSub blockWidth rows hRow)

/-- Members of the filtered span have an all-zero leading block. -/
theorem ihqFilterHeadZeroSpanTake {width : Nat} (blockWidth : Nat)
    {rows : List (List QnfRat)} {vector : List QnfRat}
    (hMem : IhqMemSpan width (ihqFilterHeadZero blockWidth rows) vector) :
    ihqAreAllCoeffsZero (ihqTakeN blockWidth vector) = true :=
  ihqMemSpanTakeAllZero blockWidth
    (fun _row hRow => ihqFilterHeadZeroMemTake blockWidth rows hRow) hMem

/-- THE LEFTMOST-PIVOT EXTRACTION: over an ECHELON list, a span member with an
all-zero leading block already lies in the span of the filtered rows.  The F2
dead branch (head leads inside the block yet the member vanishes there) is LIVE
over ℚ: the split scalar is forced to zero by the integral-domain step and the
member collapses onto its partner. -/
theorem ihqFilterHeadZeroSpanComplete {width : Nat} (blockWidth : Nat) :
    {lowerBound : Nat} -> (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> IhqEchelonFrom lowerBound rows ->
    {vector : List QnfRat} -> IhqMemSpan width rows vector ->
    ihqAreAllCoeffsZero (ihqTakeN blockWidth vector) = true ->
    IhqMemSpan width (ihqFilterHeadZero blockWidth rows) vector
  | _lowerBound, [], _hAll, _hEch, vector, hMem, _hTake => by
      show IhqMemSpan width [] vector
      exact hMem
  | _lowerBound, headRow :: restRows, hAll, hEch, vector, hMem, hTake => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH _hBound hRest =>
          have hSplit := ihqMemSpanConsInv hMem
          cases hSplit with
          | inl hInRest =>
              have hInner := ihqFilterHeadZeroSpanComplete blockWidth restRows hRestAll
                hRest hInRest hTake
              cases hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
              | true =>
                  rw [ihqFilterHeadZeroConsTrue blockWidth headRow restRows hCheck]
                  exact ihqMemSpanWeaken headRow hInner
              | false =>
                  rw [ihqFilterHeadZeroConsFalse blockWidth headRow restRows hCheck]
                  exact hInner
          | inr hSplitPack =>
              cases hSplitPack with
              | intro headScalar hPartnerPack =>
                  cases hPartnerPack with
                  | intro partner hBoth =>
                      have hPartnerLen : partner.length = width :=
                        ihqMemSpanWidth hRestAll hBoth.left
                      cases hCheck : ihqAreAllCoeffsZero (ihqTakeN blockWidth headRow) with
                      | true =>
                          -- the head passes the filter; reduce to the partner
                          have hChain : ihqRowAdd
                              (ihqRowScale (qnfNeg headScalar) headRow) vector
                              = partner := by
                            rw [hBoth.right, ihqRowScaleMergeOnHead (qnfNeg headScalar)
                                headScalar headRow partner,
                              qnfAddNegLeft headScalar, ihqRowScaleZeroScalar headRow,
                              hHead]
                            exact ihqRowAddZeroLeft partner width hPartnerLen
                          have hPartnerTake : ihqAreAllCoeffsZero
                              (ihqTakeN blockWidth partner) = true := by
                            rw [<- hChain, ihqTakeNAdd blockWidth _ vector,
                              ihqTakeNScale (qnfNeg headScalar) blockWidth headRow]
                            exact ihqAreAllCoeffsZeroAdd _ _
                              (ihqAreAllCoeffsZeroScale (qnfNeg headScalar) _ hCheck) hTake
                          have hInner := ihqFilterHeadZeroSpanComplete blockWidth restRows
                            hRestAll hRest hBoth.left hPartnerTake
                          rw [ihqFilterHeadZeroConsTrue blockWidth headRow restRows hCheck,
                            hBoth.right]
                          exact IhqMemSpan.pick headScalar headRow
                            (IhqRowMem.head headRow (ihqFilterHeadZero blockWidth restRows))
                            (ihqMemSpanWeaken headRow hInner)
                      | false =>
                          -- LIVE ℚ branch: the head leads inside the block, the member
                          -- vanishes there, so the split scalar is zero
                          have hLeadInfo := ihqTakeNotAllZeroLead headRow blockWidth hCheck
                          cases hLeadInfo with
                          | intro leadPos hLeadBoth =>
                              have hLeadEq : leadPos = headLead :=
                                Option.some.inj ((hLeadBoth.left).symm.trans hLeadH)
                              have hVecCoeffZero : ihqGetCoeff vector headLead
                                  = qnfZero := by
                                refine ihqAllZeroTakeGetCoeff vector blockWidth headLead
                                  hTake ?_
                                rw [<- hLeadEq]
                                exact hLeadBoth.right
                              have hPartnerCoeff : ihqGetCoeff partner headLead
                                  = qnfZero :=
                                ihqMemSpanCoeffZero headLead hRestAll
                                  (fun row hRow => ihqEchelonRowsCoeffZero hRest row hRow)
                                  hBoth.left
                              have hVecCoeff : ihqGetCoeff vector headLead
                                  = qnfMul headScalar (ihqGetCoeff headRow headLead) := by
                                rw [hBoth.right,
                                  ihqGetCoeffAdd (ihqRowScale headScalar headRow) partner
                                    (by rw [ihqRowScaleLength, hHead, hPartnerLen])
                                    headLead,
                                  ihqGetCoeffScale headScalar headRow headLead,
                                  hPartnerCoeff, qnfAddZeroRight]
                              have hScalarZero : headScalar = qnfZero :=
                                ihqQnfFactorZeroOfMulPivotZero
                                  (ihqQnfNeZeroOfBeqZeroFalse
                                    (ihqLeadCoeffBeqFalse headRow headLead hLeadH))
                                  (hVecCoeff.symm.trans hVecCoeffZero)
                              have hVecIsPartner : vector = partner := by
                                rw [hBoth.right, hScalarZero,
                                  ihqRowScaleZeroScalar headRow, hHead]
                                exact ihqRowAddZeroLeft partner width hPartnerLen
                              rw [hVecIsPartner] at hTake
                              have hInner := ihqFilterHeadZeroSpanComplete blockWidth
                                restRows hRestAll hRest hBoth.left hTake
                              rw [ihqFilterHeadZeroConsFalse blockWidth headRow restRows
                                hCheck, hVecIsPartner]
                              exact hInner

/-- Relational composition of generator matrices: stack with middle leftmost
(second factor's middle negated), echelonize, keep zero-middle rows, drop the
middle block — the BSZ kernel/pullback computation over ℚ. -/
def ihqComposeRows (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat)) : List (List QnfRat) :=
  ihqMapRows (ihqDropN midWidth)
    (ihqFilterHeadZero midWidth
      (ihqEchelonize
        (ihqCatRows
          (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows)
          (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows))))

theorem ihqComposeEmbedFirstLength (domWidth midWidth codWidth : Nat)
    (rowPair : List QnfRat) (hLen : rowPair.length = domWidth + midWidth) :
    (ihqComposeEmbedFirst domWidth codWidth rowPair).length
      = midWidth + (domWidth + codWidth) := by
  show (ihqCat (ihqDropN domWidth rowPair)
      (ihqCat (ihqTakeN domWidth rowPair) (ihqZeroRow codWidth))).length
    = midWidth + (domWidth + codWidth)
  rw [ihqCatLength, ihqCatLength, ihqDropNLength rowPair domWidth midWidth hLen,
    ihqTakeNLength rowPair domWidth midWidth hLen, ihqZeroRowLength]

theorem ihqComposeEmbedFirstZero (domWidth midWidth codWidth : Nat) :
    ihqComposeEmbedFirst domWidth codWidth (ihqZeroRow (domWidth + midWidth))
      = ihqZeroRow (midWidth + (domWidth + codWidth)) := by
  show ihqCat (ihqDropN domWidth (ihqZeroRow (domWidth + midWidth)))
      (ihqCat (ihqTakeN domWidth (ihqZeroRow (domWidth + midWidth)))
        (ihqZeroRow codWidth))
    = ihqZeroRow (midWidth + (domWidth + codWidth))
  rw [ihqDropNZeroRowExact domWidth midWidth, ihqTakeNZeroRowExact domWidth midWidth,
    ihqCatZeroZero domWidth codWidth, ihqCatZeroZero midWidth (domWidth + codWidth)]

theorem ihqComposeEmbedFirstAdd (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = domWidth + midWidth)
    (hSecondLen : secondPair.length = domWidth + midWidth) :
    ihqComposeEmbedFirst domWidth codWidth (ihqRowAdd firstPair secondPair)
      = ihqRowAdd (ihqComposeEmbedFirst domWidth codWidth firstPair)
          (ihqComposeEmbedFirst domWidth codWidth secondPair) := by
  have hDropLens : (ihqDropN domWidth firstPair).length
      = (ihqDropN domWidth secondPair).length := by
    rw [ihqDropNLength firstPair domWidth midWidth hFirstLen,
      ihqDropNLength secondPair domWidth midWidth hSecondLen]
  have hTakeLens : (ihqTakeN domWidth firstPair).length
      = (ihqTakeN domWidth secondPair).length := by
    rw [ihqTakeNLength firstPair domWidth midWidth hFirstLen,
      ihqTakeNLength secondPair domWidth midWidth hSecondLen]
  show ihqCat (ihqDropN domWidth (ihqRowAdd firstPair secondPair))
      (ihqCat (ihqTakeN domWidth (ihqRowAdd firstPair secondPair)) (ihqZeroRow codWidth))
    = ihqRowAdd
        (ihqCat (ihqDropN domWidth firstPair)
          (ihqCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth)))
        (ihqCat (ihqDropN domWidth secondPair)
          (ihqCat (ihqTakeN domWidth secondPair) (ihqZeroRow codWidth)))
  rw [ihqDropNAdd domWidth firstPair secondPair, ihqTakeNAdd domWidth firstPair secondPair,
    ihqRowAddCat (ihqDropN domWidth firstPair)
      (ihqCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth))
      (ihqDropN domWidth secondPair)
      (ihqCat (ihqTakeN domWidth secondPair) (ihqZeroRow codWidth)) hDropLens,
    ihqRowAddCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth)
      (ihqTakeN domWidth secondPair) (ihqZeroRow codWidth) hTakeLens,
    ihqRowAddZeroLeft (ihqZeroRow codWidth) codWidth (ihqZeroRowLength codWidth)]

theorem ihqComposeEmbedFirstScale (domWidth midWidth codWidth : Nat) (scalar : QnfRat)
    (rowPair : List QnfRat) (_hLen : rowPair.length = domWidth + midWidth) :
    ihqComposeEmbedFirst domWidth codWidth (ihqRowScale scalar rowPair)
      = ihqRowScale scalar (ihqComposeEmbedFirst domWidth codWidth rowPair) := by
  show ihqCat (ihqDropN domWidth (ihqRowScale scalar rowPair))
      (ihqCat (ihqTakeN domWidth (ihqRowScale scalar rowPair)) (ihqZeroRow codWidth))
    = ihqRowScale scalar
        (ihqCat (ihqDropN domWidth rowPair)
          (ihqCat (ihqTakeN domWidth rowPair) (ihqZeroRow codWidth)))
  rw [ihqDropNScale scalar domWidth rowPair, ihqTakeNScale scalar domWidth rowPair,
    ihqRowScaleCat scalar (ihqDropN domWidth rowPair)
      (ihqCat (ihqTakeN domWidth rowPair) (ihqZeroRow codWidth)),
    ihqRowScaleCat scalar (ihqTakeN domWidth rowPair) (ihqZeroRow codWidth),
    ihqRowScaleZeroRow scalar codWidth]

theorem ihqComposeEmbedSecondLength (domWidth midWidth codWidth : Nat)
    (rowPair : List QnfRat) (hLen : rowPair.length = midWidth + codWidth) :
    (ihqComposeEmbedSecond midWidth domWidth rowPair).length
      = midWidth + (domWidth + codWidth) := by
  show (ihqCat (ihqRowNeg (ihqTakeN midWidth rowPair))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth rowPair))).length
    = midWidth + (domWidth + codWidth)
  rw [ihqCatLength, ihqCatLength, ihqRowNegLength,
    ihqTakeNLength rowPair midWidth codWidth hLen,
    ihqDropNLength rowPair midWidth codWidth hLen, ihqZeroRowLength]

theorem ihqComposeEmbedSecondZero (domWidth midWidth codWidth : Nat) :
    ihqComposeEmbedSecond midWidth domWidth (ihqZeroRow (midWidth + codWidth))
      = ihqZeroRow (midWidth + (domWidth + codWidth)) := by
  show ihqCat (ihqRowNeg (ihqTakeN midWidth (ihqZeroRow (midWidth + codWidth))))
      (ihqCat (ihqZeroRow domWidth)
        (ihqDropN midWidth (ihqZeroRow (midWidth + codWidth))))
    = ihqZeroRow (midWidth + (domWidth + codWidth))
  rw [ihqTakeNZeroRowExact midWidth codWidth, ihqDropNZeroRowExact midWidth codWidth,
    ihqRowNegZeroRow midWidth,
    ihqCatZeroZero domWidth codWidth, ihqCatZeroZero midWidth (domWidth + codWidth)]

theorem ihqComposeEmbedSecondAdd (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = midWidth + codWidth)
    (hSecondLen : secondPair.length = midWidth + codWidth) :
    ihqComposeEmbedSecond midWidth domWidth (ihqRowAdd firstPair secondPair)
      = ihqRowAdd (ihqComposeEmbedSecond midWidth domWidth firstPair)
          (ihqComposeEmbedSecond midWidth domWidth secondPair) := by
  have hNegTakeLens : (ihqRowNeg (ihqTakeN midWidth firstPair)).length
      = (ihqRowNeg (ihqTakeN midWidth secondPair)).length := by
    rw [ihqRowNegLength, ihqRowNegLength,
      ihqTakeNLength firstPair midWidth codWidth hFirstLen,
      ihqTakeNLength secondPair midWidth codWidth hSecondLen]
  have hZeroLens : (ihqZeroRow domWidth).length = (ihqZeroRow domWidth).length := rfl
  show ihqCat (ihqRowNeg (ihqTakeN midWidth (ihqRowAdd firstPair secondPair)))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth (ihqRowAdd firstPair secondPair)))
    = ihqRowAdd
        (ihqCat (ihqRowNeg (ihqTakeN midWidth firstPair))
          (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth firstPair)))
        (ihqCat (ihqRowNeg (ihqTakeN midWidth secondPair))
          (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth secondPair)))
  rw [ihqTakeNAdd midWidth firstPair secondPair,
    ihqRowNegAddDistrib (ihqTakeN midWidth firstPair) (ihqTakeN midWidth secondPair),
    ihqDropNAdd midWidth firstPair secondPair,
    ihqRowAddCat (ihqRowNeg (ihqTakeN midWidth firstPair))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth firstPair))
      (ihqRowNeg (ihqTakeN midWidth secondPair))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth secondPair)) hNegTakeLens,
    ihqRowAddCat (ihqZeroRow domWidth) (ihqDropN midWidth firstPair)
      (ihqZeroRow domWidth) (ihqDropN midWidth secondPair) hZeroLens,
    ihqRowAddZeroLeft (ihqZeroRow domWidth) domWidth (ihqZeroRowLength domWidth)]

theorem ihqComposeEmbedSecondScale (domWidth midWidth codWidth : Nat) (scalar : QnfRat)
    (rowPair : List QnfRat) (_hLen : rowPair.length = midWidth + codWidth) :
    ihqComposeEmbedSecond midWidth domWidth (ihqRowScale scalar rowPair)
      = ihqRowScale scalar (ihqComposeEmbedSecond midWidth domWidth rowPair) := by
  show ihqCat (ihqRowNeg (ihqTakeN midWidth (ihqRowScale scalar rowPair)))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth (ihqRowScale scalar rowPair)))
    = ihqRowScale scalar
        (ihqCat (ihqRowNeg (ihqTakeN midWidth rowPair))
          (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth rowPair)))
  rw [ihqTakeNScale scalar midWidth rowPair, ihqDropNScale scalar midWidth rowPair,
    <- ihqRowScaleNegComm scalar (ihqTakeN midWidth rowPair),
    ihqRowScaleCat scalar (ihqRowNeg (ihqTakeN midWidth rowPair))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth rowPair)),
    ihqRowScaleCat scalar (ihqZeroRow domWidth) (ihqDropN midWidth rowPair),
    ihqRowScaleZeroRow scalar domWidth]

theorem ihqComposeRowsWidth (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows) :
    IhqAllWidth (domWidth + codWidth)
      (ihqComposeRows domWidth midWidth codWidth firstRows secondRows) := by
  have hStackAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqCatRows
        (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows)
        (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows)) :=
    ihqCatRowsWidth _ _
      (ihqMapRowsWidth _ (fun row hRowLen =>
        ihqComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
        firstRows hFirstAll)
      (ihqMapRowsWidth _ (fun row hRowLen =>
        ihqComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
        secondRows hSecondAll)
  exact ihqMapRowsWidth (ihqDropN midWidth)
    (fun row hRowLen => ihqDropNLength row midWidth (domWidth + codWidth) hRowLen)
    _ (ihqFilterHeadZeroWidth midWidth _ (ihqEchelonizeWidth _ hStackAll))

/-- The sum of the two composition embeddings in blocks: middle block first
(the first factor's middle MINUS the second's), then the outer pair. -/
theorem ihqComposeEmbedAddBlocks (domWidth midWidth codWidth : Nat)
    (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = domWidth + midWidth)
    (hSecondLen : secondPair.length = midWidth + codWidth) :
    ihqRowAdd (ihqComposeEmbedFirst domWidth codWidth firstPair)
        (ihqComposeEmbedSecond midWidth domWidth secondPair)
      = ihqCat
          (ihqRowAdd (ihqDropN domWidth firstPair)
            (ihqRowNeg (ihqTakeN midWidth secondPair)))
          (ihqCat (ihqTakeN domWidth firstPair) (ihqDropN midWidth secondPair)) := by
  show ihqRowAdd
      (ihqCat (ihqDropN domWidth firstPair)
        (ihqCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth)))
      (ihqCat (ihqRowNeg (ihqTakeN midWidth secondPair))
        (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth secondPair)))
    = ihqCat
        (ihqRowAdd (ihqDropN domWidth firstPair)
          (ihqRowNeg (ihqTakeN midWidth secondPair)))
        (ihqCat (ihqTakeN domWidth firstPair) (ihqDropN midWidth secondPair))
  have hMidLens : (ihqDropN domWidth firstPair).length
      = (ihqRowNeg (ihqTakeN midWidth secondPair)).length := by
    rw [ihqDropNLength firstPair domWidth midWidth hFirstLen, ihqRowNegLength,
      ihqTakeNLength secondPair midWidth codWidth hSecondLen]
  have hDomLens : (ihqTakeN domWidth firstPair).length
      = (ihqZeroRow domWidth).length := by
    rw [ihqTakeNLength firstPair domWidth midWidth hFirstLen, ihqZeroRowLength]
  rw [ihqRowAddCat (ihqDropN domWidth firstPair)
      (ihqCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth))
      (ihqRowNeg (ihqTakeN midWidth secondPair))
      (ihqCat (ihqZeroRow domWidth) (ihqDropN midWidth secondPair)) hMidLens,
    ihqRowAddCat (ihqTakeN domWidth firstPair) (ihqZeroRow codWidth)
      (ihqZeroRow domWidth) (ihqDropN midWidth secondPair) hDomLens,
    ihqRowAddZeroRight (ihqTakeN domWidth firstPair) domWidth
      (ihqTakeNLength firstPair domWidth midWidth hFirstLen),
    ihqRowAddZeroLeft (ihqDropN midWidth secondPair) codWidth
      (ihqDropNLength secondPair midWidth codWidth hSecondLen)]

/-- Stack decomposition, forward: a member of the composition stack is the sum of
one embedded member from each factor. -/
theorem ihqComposeStackFwd (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows)
    {stackVec : List QnfRat}
    (hMem : IhqMemSpan (midWidth + (domWidth + codWidth))
      (ihqCatRows
        (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows)
        (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows)) stackVec) :
    Exists fun firstPair => Exists fun secondPair =>
      IhqMemSpan (domWidth + midWidth) firstRows firstPair
        /\ IhqMemSpan (midWidth + codWidth) secondRows secondPair
        /\ stackVec = ihqRowAdd (ihqComposeEmbedFirst domWidth codWidth firstPair)
            (ihqComposeEmbedSecond midWidth domWidth secondPair) := by
  have hLeftAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows) :=
    ihqMapRowsWidth _ (fun row hRowLen =>
      ihqComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
      firstRows hFirstAll
  have hRightAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows) :=
    ihqMapRowsWidth _ (fun row hRowLen =>
      ihqComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
      secondRows hSecondAll
  have hSplit := ihqCatRowsSpanSplitFwd hLeftAll hRightAll hMem
  cases hSplit with
  | intro leftPart hRightPack =>
      cases hRightPack with
      | intro rightPart hParts =>
          have hLeftInv := ihqMapRowsSpanFwd (ihqComposeEmbedFirst domWidth codWidth)
            (ihqComposeEmbedFirstZero domWidth midWidth codWidth)
            (fun firstRow secondRow hFirstLen hSecondLen =>
              ihqComposeEmbedFirstAdd domWidth midWidth codWidth firstRow secondRow
                hFirstLen hSecondLen)
            (fun scalar row hRowLen =>
              ihqComposeEmbedFirstScale domWidth midWidth codWidth scalar row hRowLen)
            hFirstAll hParts.left
          have hRightInv := ihqMapRowsSpanFwd (ihqComposeEmbedSecond midWidth domWidth)
            (ihqComposeEmbedSecondZero domWidth midWidth codWidth)
            (fun firstRow secondRow hFirstLen hSecondLen =>
              ihqComposeEmbedSecondAdd domWidth midWidth codWidth firstRow secondRow
                hFirstLen hSecondLen)
            (fun scalar row hRowLen =>
              ihqComposeEmbedSecondScale domWidth midWidth codWidth scalar row hRowLen)
            hSecondAll hParts.right.left
          cases hLeftInv with
          | intro firstPair hFirstBoth =>
              cases hRightInv with
              | intro secondPair hSecondBoth =>
                  refine Exists.intro firstPair (Exists.intro secondPair
                    (And.intro hFirstBoth.left (And.intro hSecondBoth.left ?_)))
                  rw [hParts.right.right, hFirstBoth.right, hSecondBoth.right]

/-- Stack decomposition, backward. -/
theorem ihqComposeStackBwd (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows)
    {firstPair secondPair : List QnfRat}
    (hFirstMem : IhqMemSpan (domWidth + midWidth) firstRows firstPair)
    (hSecondMem : IhqMemSpan (midWidth + codWidth) secondRows secondPair) :
    IhqMemSpan (midWidth + (domWidth + codWidth))
      (ihqCatRows
        (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows)
        (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows))
      (ihqRowAdd (ihqComposeEmbedFirst domWidth codWidth firstPair)
        (ihqComposeEmbedSecond midWidth domWidth secondPair)) := by
  have hLeftAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows) :=
    ihqMapRowsWidth _ (fun row hRowLen =>
      ihqComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
      firstRows hFirstAll
  have hRightAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows) :=
    ihqMapRowsWidth _ (fun row hRowLen =>
      ihqComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
      secondRows hSecondAll
  have hStackAll := ihqCatRowsWidth _ _ hLeftAll hRightAll
  refine ihqMemSpanAddClosed hStackAll ?_ ?_
  · exact ihqCatRowsSpanLeft
      (ihqMapRowsSpanBwd (ihqComposeEmbedFirst domWidth codWidth)
        (ihqComposeEmbedFirstZero domWidth midWidth codWidth)
        (fun firstRow secondRow hFirstLen hSecondLen =>
          ihqComposeEmbedFirstAdd domWidth midWidth codWidth firstRow secondRow
            hFirstLen hSecondLen)
        (fun scalar row hRowLen =>
          ihqComposeEmbedFirstScale domWidth midWidth codWidth scalar row hRowLen)
        hFirstAll hFirstMem)
  · exact ihqCatRowsSpanRight
      (ihqMapRowsSpanBwd (ihqComposeEmbedSecond midWidth domWidth)
        (ihqComposeEmbedSecondZero domWidth midWidth codWidth)
        (fun firstRow secondRow hFirstLen hSecondLen =>
          ihqComposeEmbedSecondAdd domWidth midWidth codWidth firstRow secondRow
            hFirstLen hSecondLen)
        (fun scalar row hRowLen =>
          ihqComposeEmbedSecondScale domWidth midWidth codWidth scalar row hRowLen)
        hSecondAll hSecondMem)

/-- **THE COMPOSITION SPEC**: the computed composite relates exactly the pairs
joined by some middle vector — the BSZ pullback/kernel characterization
(Lemma 5.10 + Lemma 6.6), specialized to ℚ.  Both directions. -/
theorem ihqComposeSpec (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows)
    (domVec codVec : List QnfRat) :
    IhqPairMem domWidth codWidth
      (ihqComposeRows domWidth midWidth codWidth firstRows secondRows) domVec codVec
    <-> Exists fun midVec =>
        IhqPairMem domWidth midWidth firstRows domVec midVec
          /\ IhqPairMem midWidth codWidth secondRows midVec codVec := by
  have hStackAll : IhqAllWidth (midWidth + (domWidth + codWidth))
      (ihqCatRows
        (ihqMapRows (ihqComposeEmbedFirst domWidth codWidth) firstRows)
        (ihqMapRows (ihqComposeEmbedSecond midWidth domWidth) secondRows)) :=
    ihqCatRowsWidth _ _
      (ihqMapRowsWidth _ (fun row hRowLen =>
        ihqComposeEmbedFirstLength domWidth midWidth codWidth row hRowLen)
        firstRows hFirstAll)
      (ihqMapRowsWidth _ (fun row hRowLen =>
        ihqComposeEmbedSecondLength domWidth midWidth codWidth row hRowLen)
        secondRows hSecondAll)
  have hEchAll := ihqEchelonizeWidth _ hStackAll
  have hFilterAll := ihqFilterHeadZeroWidth midWidth _ hEchAll
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomLen : domVec.length = domWidth := hPair.left
    have hCodLen : codVec.length = codWidth := hPair.right.left
    have hMapMem := hPair.right.right
    have hMapInv := ihqMapRowsSpanFwd (ihqDropN midWidth)
      (ihqDropNZeroRowExact midWidth (domWidth + codWidth))
      (fun firstRow secondRow _hFirstLen _hSecondLen =>
        ihqDropNAdd midWidth firstRow secondRow)
      (fun scalar row _hRowLen => ihqDropNScale scalar midWidth row)
      hFilterAll hMapMem
    cases hMapInv with
    | intro stackVec hStackBoth =>
        have hInFilter := hStackBoth.left
        have hTakeZero := ihqFilterHeadZeroSpanTake midWidth hInFilter
        have hInEch : IhqMemSpan (midWidth + (domWidth + codWidth))
            (ihqEchelonize _) stackVec :=
          ihqFilterHeadZeroSpanSub midWidth hEchAll hInFilter
        have hInStack := ihqEchelonizeSpanSub1 _ hStackAll hInEch
        have hDecomp := ihqComposeStackFwd domWidth midWidth codWidth firstRows secondRows
          hFirstAll hSecondAll hInStack
        cases hDecomp with
        | intro firstPair hSecondPack =>
            cases hSecondPack with
            | intro secondPair hParts =>
                have hFirstPairLen : firstPair.length = domWidth + midWidth :=
                  ihqMemSpanWidth hFirstAll hParts.left
                have hSecondPairLen : secondPair.length = midWidth + codWidth :=
                  ihqMemSpanWidth hSecondAll hParts.right.left
                have hBlocks : stackVec
                    = ihqCat (ihqRowAdd (ihqDropN domWidth firstPair)
                        (ihqRowNeg (ihqTakeN midWidth secondPair)))
                      (ihqCat (ihqTakeN domWidth firstPair)
                        (ihqDropN midWidth secondPair)) := by
                  rw [hParts.right.right]
                  exact ihqComposeEmbedAddBlocks domWidth midWidth codWidth firstPair
                    secondPair hFirstPairLen hSecondPairLen
                have hMidBlockLen : (ihqRowAdd (ihqDropN domWidth firstPair)
                    (ihqRowNeg (ihqTakeN midWidth secondPair))).length = midWidth :=
                  ihqRowAddLength _ _ midWidth
                    (ihqDropNLength firstPair domWidth midWidth hFirstPairLen)
                    ((ihqRowNegLength _).trans
                      (ihqTakeNLength secondPair midWidth codWidth hSecondPairLen))
                have hMidZero : ihqRowAdd (ihqDropN domWidth firstPair)
                    (ihqRowNeg (ihqTakeN midWidth secondPair)) = ihqZeroRow midWidth := by
                  have hTakeStack : ihqTakeN midWidth stackVec
                      = ihqRowAdd (ihqDropN domWidth firstPair)
                          (ihqRowNeg (ihqTakeN midWidth secondPair)) := by
                    rw [hBlocks]
                    exact ihqTakeNCatExact _ _ midWidth hMidBlockLen
                  have hAllZeroMid : ihqAreAllCoeffsZero
                      (ihqRowAdd (ihqDropN domWidth firstPair)
                        (ihqRowNeg (ihqTakeN midWidth secondPair))) = true := by
                    rw [<- hTakeStack]
                    exact hTakeZero
                  have hToZero := ihqZeroRowOfAllCoeffsZero _ hAllZeroMid
                  rw [hMidBlockLen] at hToZero
                  exact hToZero
                have hMidEq : ihqDropN domWidth firstPair
                    = ihqTakeN midWidth secondPair :=
                  ihqRowsEqOfAddNegEqZero _ _ midWidth
                    (ihqDropNLength firstPair domWidth midWidth hFirstPairLen)
                    (ihqTakeNLength secondPair midWidth codWidth hSecondPairLen) hMidZero
                have hDropStack : ihqCat domVec codVec
                    = ihqCat (ihqTakeN domWidth firstPair)
                        (ihqDropN midWidth secondPair) := by
                  rw [hStackBoth.right, hBlocks]
                  exact ihqDropNCatExact _ _ midWidth hMidBlockLen
                have hOuterSplit := ihqCatInj domVec codVec
                  (ihqTakeN domWidth firstPair) (ihqDropN midWidth secondPair)
                  (by rw [hDomLen,
                    ihqTakeNLength firstPair domWidth midWidth hFirstPairLen])
                  hDropStack
                refine Exists.intro (ihqDropN domWidth firstPair)
                  (And.intro (And.intro hDomLen (And.intro
                    (ihqDropNLength firstPair domWidth midWidth hFirstPairLen) ?_))
                    (And.intro
                      (ihqDropNLength firstPair domWidth midWidth hFirstPairLen)
                      (And.intro hCodLen ?_)))
                · have hReassemble : ihqCat domVec (ihqDropN domWidth firstPair)
                      = firstPair := by
                    rw [hOuterSplit.left]
                    exact ihqCatTakeDrop firstPair domWidth midWidth hFirstPairLen
                  rw [hReassemble]
                  exact hParts.left
                · have hReassemble : ihqCat (ihqDropN domWidth firstPair) codVec
                      = secondPair := by
                    rw [hMidEq, hOuterSplit.right]
                    exact ihqCatTakeDrop secondPair midWidth codWidth hSecondPairLen
                  rw [hReassemble]
                  exact hParts.right.left
  · intro hExists
    cases hExists with
    | intro midVec hBothPairs =>
        have hDomLen : domVec.length = domWidth := hBothPairs.left.left
        have hMidLen : midVec.length = midWidth := hBothPairs.left.right.left
        have hCodLen : codVec.length = codWidth := hBothPairs.right.right.left
        have hFirstCatLen : (ihqCat domVec midVec).length = domWidth + midWidth := by
          rw [ihqCatLength, hDomLen, hMidLen]
        have hSecondCatLen : (ihqCat midVec codVec).length = midWidth + codWidth := by
          rw [ihqCatLength, hMidLen, hCodLen]
        have hStackVecEq : ihqRowAdd
            (ihqComposeEmbedFirst domWidth codWidth (ihqCat domVec midVec))
            (ihqComposeEmbedSecond midWidth domWidth (ihqCat midVec codVec))
          = ihqCat (ihqZeroRow midWidth) (ihqCat domVec codVec) := by
          rw [ihqComposeEmbedAddBlocks domWidth midWidth codWidth _ _ hFirstCatLen
            hSecondCatLen,
            ihqDropNCatExact domVec midVec domWidth hDomLen,
            ihqTakeNCatExact midVec codVec midWidth hMidLen,
            ihqTakeNCatExact domVec midVec domWidth hDomLen,
            ihqDropNCatExact midVec codVec midWidth hMidLen,
            ihqRowAddNegRight midVec, hMidLen]
        have hInStack := ihqComposeStackBwd domWidth midWidth codWidth firstRows secondRows
          hFirstAll hSecondAll hBothPairs.left.right.right hBothPairs.right.right.right
        rw [hStackVecEq] at hInStack
        have hInEch := ihqEchelonizeSpanSub2 _ hStackAll hInStack
        have hTakeZero : ihqAreAllCoeffsZero (ihqTakeN midWidth
            (ihqCat (ihqZeroRow midWidth) (ihqCat domVec codVec))) = true := by
          rw [ihqTakeNCatExact (ihqZeroRow midWidth) _ midWidth
            (ihqZeroRowLength midWidth)]
          exact ihqAreAllCoeffsZeroZeroRow midWidth
        have hInFilter := ihqFilterHeadZeroSpanComplete midWidth _ hEchAll
          (ihqEchelonizeEchelon _ hStackAll) hInEch hTakeZero
        have hMapped := ihqMapRowsSpanBwd (ihqDropN midWidth)
          (ihqDropNZeroRowExact midWidth (domWidth + codWidth))
          (fun firstRow secondRow _hFirstLen _hSecondLen =>
            ihqDropNAdd midWidth firstRow secondRow)
          (fun scalar row _hRowLen => ihqDropNScale scalar midWidth row)
          hFilterAll hInFilter
        have hDropEq : ihqDropN midWidth
            (ihqCat (ihqZeroRow midWidth) (ihqCat domVec codVec))
          = ihqCat domVec codVec :=
          ihqDropNCatExact (ihqZeroRow midWidth) _ midWidth (ihqZeroRowLength midWidth)
        rw [hDropEq] at hMapped
        exact And.intro hDomLen (And.intro hCodLen hMapped)

/-! ### Converse and identity generators -/

/-- Swap the domain and codomain blocks of a relation row. -/
def ihqConverseTransform (domWidth : Nat) (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (ihqDropN domWidth rowPair) (ihqTakeN domWidth rowPair)

/-- The converse relation: swap blocks on every generator. -/
def ihqConverseRows (domWidth : Nat) (relationRows : List (List QnfRat)) :
    List (List QnfRat) :=
  ihqMapRows (ihqConverseTransform domWidth) relationRows

theorem ihqConverseTransformLength (domWidth codWidth : Nat) (rowPair : List QnfRat)
    (hLen : rowPair.length = domWidth + codWidth) :
    (ihqConverseTransform domWidth rowPair).length = codWidth + domWidth := by
  show (ihqCat (ihqDropN domWidth rowPair) (ihqTakeN domWidth rowPair)).length
    = codWidth + domWidth
  rw [ihqCatLength, ihqDropNLength rowPair domWidth codWidth hLen,
    ihqTakeNLength rowPair domWidth codWidth hLen]

theorem ihqConverseTransformZero (domWidth codWidth : Nat) :
    ihqConverseTransform domWidth (ihqZeroRow (domWidth + codWidth))
      = ihqZeroRow (codWidth + domWidth) := by
  show ihqCat (ihqDropN domWidth (ihqZeroRow (domWidth + codWidth)))
      (ihqTakeN domWidth (ihqZeroRow (domWidth + codWidth)))
    = ihqZeroRow (codWidth + domWidth)
  rw [ihqDropNZeroRowExact domWidth codWidth, ihqTakeNZeroRowExact domWidth codWidth,
    ihqCatZeroZero codWidth domWidth]

theorem ihqConverseTransformAdd (domWidth codWidth : Nat)
    (firstPair secondPair : List QnfRat)
    (hFirstLen : firstPair.length = domWidth + codWidth)
    (hSecondLen : secondPair.length = domWidth + codWidth) :
    ihqConverseTransform domWidth (ihqRowAdd firstPair secondPair)
      = ihqRowAdd (ihqConverseTransform domWidth firstPair)
          (ihqConverseTransform domWidth secondPair) := by
  have hDropLens : (ihqDropN domWidth firstPair).length
      = (ihqDropN domWidth secondPair).length := by
    rw [ihqDropNLength firstPair domWidth codWidth hFirstLen,
      ihqDropNLength secondPair domWidth codWidth hSecondLen]
  show ihqCat (ihqDropN domWidth (ihqRowAdd firstPair secondPair))
      (ihqTakeN domWidth (ihqRowAdd firstPair secondPair))
    = ihqRowAdd (ihqCat (ihqDropN domWidth firstPair) (ihqTakeN domWidth firstPair))
        (ihqCat (ihqDropN domWidth secondPair) (ihqTakeN domWidth secondPair))
  rw [ihqDropNAdd domWidth firstPair secondPair, ihqTakeNAdd domWidth firstPair secondPair,
    ihqRowAddCat (ihqDropN domWidth firstPair) (ihqTakeN domWidth firstPair)
      (ihqDropN domWidth secondPair) (ihqTakeN domWidth secondPair) hDropLens]

theorem ihqConverseTransformScale (domWidth : Nat) (scalar : QnfRat)
    (rowPair : List QnfRat) :
    ihqConverseTransform domWidth (ihqRowScale scalar rowPair)
      = ihqRowScale scalar (ihqConverseTransform domWidth rowPair) := by
  show ihqCat (ihqDropN domWidth (ihqRowScale scalar rowPair))
      (ihqTakeN domWidth (ihqRowScale scalar rowPair))
    = ihqRowScale scalar
        (ihqCat (ihqDropN domWidth rowPair) (ihqTakeN domWidth rowPair))
  rw [ihqDropNScale scalar domWidth rowPair, ihqTakeNScale scalar domWidth rowPair,
    ihqRowScaleCat scalar (ihqDropN domWidth rowPair) (ihqTakeN domWidth rowPair)]

/-- **THE CONVERSE SPEC**: the block-swapped generators denote exactly the
transposed relation. -/
theorem ihqConverseSpec (domWidth codWidth : Nat) (relationRows : List (List QnfRat))
    (hAll : IhqAllWidth (domWidth + codWidth) relationRows)
    (domVec codVec : List QnfRat) :
    IhqPairMem codWidth domWidth (ihqConverseRows domWidth relationRows) codVec domVec
      <-> IhqPairMem domWidth codWidth relationRows domVec codVec := by
  refine Iff.intro ?_ ?_
  · intro hPair
    have hCodLen : codVec.length = codWidth := hPair.left
    have hDomLen : domVec.length = domWidth := hPair.right.left
    have hMapInv := ihqMapRowsSpanFwd (ihqConverseTransform domWidth)
      (ihqConverseTransformZero domWidth codWidth)
      (fun firstRow secondRow hFirstLen hSecondLen =>
        ihqConverseTransformAdd domWidth codWidth firstRow secondRow hFirstLen hSecondLen)
      (fun scalar row _hRowLen => ihqConverseTransformScale domWidth scalar row)
      hAll hPair.right.right
    cases hMapInv with
    | intro sourceVector hBoth =>
        have hSourceLen : sourceVector.length = domWidth + codWidth :=
          ihqMemSpanWidth hAll hBoth.left
        have hSwapEq : ihqCat codVec domVec
            = ihqCat (ihqDropN domWidth sourceVector) (ihqTakeN domWidth sourceVector) :=
          hBoth.right
        have hBlockSplit := ihqCatInj codVec domVec
          (ihqDropN domWidth sourceVector) (ihqTakeN domWidth sourceVector)
          (by rw [hCodLen, ihqDropNLength sourceVector domWidth codWidth hSourceLen])
          hSwapEq
        have hReassemble : ihqCat domVec codVec = sourceVector := by
          rw [hBlockSplit.left, hBlockSplit.right]
          exact ihqCatTakeDrop sourceVector domWidth codWidth hSourceLen
        refine And.intro hDomLen (And.intro hCodLen ?_)
        rw [hReassemble]
        exact hBoth.left
  · intro hPair
    have hDomLen : domVec.length = domWidth := hPair.left
    have hCodLen : codVec.length = codWidth := hPair.right.left
    have hMapped := ihqMapRowsSpanBwd (ihqConverseTransform domWidth)
      (ihqConverseTransformZero domWidth codWidth)
      (fun firstRow secondRow hFirstLen hSecondLen =>
        ihqConverseTransformAdd domWidth codWidth firstRow secondRow hFirstLen hSecondLen)
      (fun scalar row _hRowLen => ihqConverseTransformScale domWidth scalar row)
      hAll hPair.right.right
    have hSwapEq : ihqConverseTransform domWidth (ihqCat domVec codVec)
        = ihqCat codVec domVec := by
      show ihqCat (ihqDropN domWidth (ihqCat domVec codVec))
          (ihqTakeN domWidth (ihqCat domVec codVec))
        = ihqCat codVec domVec
      rw [ihqDropNCatExact domVec codVec domWidth hDomLen,
        ihqTakeNCatExact domVec codVec domWidth hDomLen]
    rw [hSwapEq] at hMapped
    exact And.intro hCodLen (And.intro hDomLen hMapped)

/-- Pad a diagonal row pair: prepend a zero to both blocks. -/
def ihqPadPairRow (halfWidth : Nat) (rowPair : List QnfRat) : List QnfRat :=
  ihqCat (qnfZero :: ihqTakeN halfWidth rowPair) (qnfZero :: ihqDropN halfWidth rowPair)

/-- Generator matrix of the identity relation (the diagonal subspace): the rows
`(e_i | e_i)`.  NOTE the pitfall pinned by the literature leg: the identity on
`n` is NOT the empty generator list (that is the zero relation); the empty list
is the identity only at `n = 0`. -/
def ihqIdRows : Nat -> List (List QnfRat)
  | 0 => []
  | widthPred + 1 =>
      ihqCat (qnfOne :: ihqZeroRow widthPred) (qnfOne :: ihqZeroRow widthPred)
        :: ihqMapRows (ihqPadPairRow widthPred) (ihqIdRows widthPred)

theorem ihqPadPairRowLength (halfWidth : Nat) (rowPair : List QnfRat)
    (hLen : rowPair.length = halfWidth + halfWidth) :
    (ihqPadPairRow halfWidth rowPair).length = (halfWidth + 1) + (halfWidth + 1) := by
  show (ihqCat (qnfZero :: ihqTakeN halfWidth rowPair)
      (qnfZero :: ihqDropN halfWidth rowPair)).length = (halfWidth + 1) + (halfWidth + 1)
  rw [ihqCatLength]
  show ((ihqTakeN halfWidth rowPair).length + 1)
      + ((ihqDropN halfWidth rowPair).length + 1) = (halfWidth + 1) + (halfWidth + 1)
  rw [ihqTakeNLength rowPair halfWidth halfWidth hLen,
    ihqDropNLength rowPair halfWidth halfWidth hLen]

theorem ihqIdRowsWidth : (identityWidth : Nat) ->
    IhqAllWidth (identityWidth + identityWidth) (ihqIdRows identityWidth)
  | 0 => IhqAllWidth.nil
  | widthPred + 1 => by
      refine IhqAllWidth.cons ?_ ?_
      · show (ihqCat (qnfOne :: ihqZeroRow widthPred)
            (qnfOne :: ihqZeroRow widthPred)).length
          = (widthPred + 1) + (widthPred + 1)
        rw [ihqCatLength]
        show ((ihqZeroRow widthPred).length + 1) + ((ihqZeroRow widthPred).length + 1)
          = (widthPred + 1) + (widthPred + 1)
        rw [ihqZeroRowLength]
      · exact ihqMapRowsWidth (ihqPadPairRow widthPred)
          (fun row hRowLen => ihqPadPairRowLength widthPred row hRowLen)
          (ihqIdRows widthPred) (ihqIdRowsWidth widthPred)

/-! ## Stage 5 — RREF via back-substitution, with row-space preservation (T4)

The canonical-representative FALLBACK exactly as in the F2 brick: `ihqRref`
preserves the row space (proved both directions); syntactic RREF UNIQUENESS is
recorded owner-false below. -/

/-- Back-substitution: reduce each row against the (already back-reduced) rows
below it. -/
def ihqBackReduce : List (List QnfRat) -> List (List QnfRat)
  | [] => []
  | headRow :: restRows =>
      ihqReduceAgainst (ihqBackReduce restRows) headRow :: ihqBackReduce restRows

theorem ihqBackReduceWidth {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> IhqAllWidth width (ihqBackReduce rows)
  | [], _hAll => IhqAllWidth.nil
  | headRow :: restRows, hAll => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInner := ihqBackReduceWidth restRows hRestAll
      exact IhqAllWidth.cons
        (ihqReduceAgainstWidth (ihqBackReduce restRows) headRow hInner hHead) hInner

theorem ihqBackReduceSpanSub1 {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> {vector : List QnfRat} ->
    IhqMemSpan width (ihqBackReduce rows) vector -> IhqMemSpan width rows vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInnerAll := ihqBackReduceWidth restRows hRestAll
      refine ihqMemSpanSub hAll ?_ hMem
      intro row hRow
      cases hRow with
      | head =>
          have hDelta := ihqReduceAgainstSound (ihqBackReduce restRows) headRow
            hInnerAll hHead
          have hDeltaInRest : IhqMemSpan width restRows
              (ihqRowAdd headRow
                (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow))) :=
            ihqBackReduceSpanSub1 restRows hRestAll hDelta
          have hCombined := ihqMemSpanAddClosed hAll
            (ihqMemSpanElem hAll (IhqRowMem.head headRow restRows))
            (ihqMemSpanNegClosed (ihqMemSpanWeaken headRow hDeltaInRest))
          have hReducedLen : (ihqReduceAgainst (ihqBackReduce restRows) headRow).length
              = width :=
            ihqReduceAgainstWidth (ihqBackReduce restRows) headRow hInnerAll hHead
          have hRecover : ihqRowAdd headRow (ihqRowNeg (ihqRowAdd headRow
              (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow))))
              = ihqReduceAgainst (ihqBackReduce restRows) headRow := by
            rw [ihqRowNegAddDistrib headRow
                (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow)),
              ihqRowNegNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow),
              <- ihqRowAddAssoc headRow (ihqRowNeg headRow)
                (ihqReduceAgainst (ihqBackReduce restRows) headRow),
              ihqRowAddNegRight headRow, hHead,
              ihqRowAddZeroLeft (ihqReduceAgainst (ihqBackReduce restRows) headRow)
                width hReducedLen]
          rw [hRecover] at hCombined
          exact hCombined
      | tail hRowRest =>
          have hInRest := ihqBackReduceSpanSub1 restRows hRestAll
            (ihqMemSpanElem hInnerAll hRowRest)
          exact ihqMemSpanWeaken headRow hInRest

theorem ihqBackReduceSpanSub2 {width : Nat} : (rows : List (List QnfRat)) ->
    IhqAllWidth width rows -> {vector : List QnfRat} ->
    IhqMemSpan width rows vector -> IhqMemSpan width (ihqBackReduce rows) vector
  | [], _hAll, _vector, hMem => hMem
  | headRow :: restRows, hAll, vector, hMem => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hInnerAll := ihqBackReduceWidth restRows hRestAll
      have hResultAll : IhqAllWidth width (ihqBackReduce (headRow :: restRows)) :=
        ihqBackReduceWidth (headRow :: restRows) hAll
      refine ihqMemSpanSub hResultAll ?_ hMem
      intro row hRow
      cases hRow with
      | head =>
          have hDelta := ihqReduceAgainstSound (ihqBackReduce restRows) headRow
            hInnerAll hHead
          have hReducedLen : (ihqReduceAgainst (ihqBackReduce restRows) headRow).length
              = width :=
            ihqReduceAgainstWidth (ihqBackReduce restRows) headRow hInnerAll hHead
          have hReducedMem : IhqMemSpan width (ihqBackReduce (headRow :: restRows))
              (ihqReduceAgainst (ihqBackReduce restRows) headRow) :=
            ihqMemSpanElem hResultAll (IhqRowMem.head _ _)
          have hDeltaWeakened : IhqMemSpan width (ihqBackReduce (headRow :: restRows))
              (ihqRowAdd headRow
                (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow))) :=
            ihqMemSpanWeaken _ hDelta
          have hCombined := ihqMemSpanAddClosed hResultAll hReducedMem hDeltaWeakened
          have hRecover : ihqRowAdd (ihqReduceAgainst (ihqBackReduce restRows) headRow)
              (ihqRowAdd headRow
                (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow)))
              = headRow := by
            rw [ihqRowAddSwapLeft (ihqReduceAgainst (ihqBackReduce restRows) headRow)
                headRow
                (ihqRowNeg (ihqReduceAgainst (ihqBackReduce restRows) headRow)),
              ihqRowAddNegRight (ihqReduceAgainst (ihqBackReduce restRows) headRow),
              hReducedLen, ihqRowAddZeroRight headRow width hHead]
          rw [hRecover] at hCombined
          exact hCombined
      | tail hRowRest =>
          have hInRest := ihqBackReduceSpanSub2 restRows hRestAll
            (ihqMemSpanElem hRestAll hRowRest)
          exact ihqMemSpanWeaken _ hInRest

/-- Gaussian elimination to (reduced) row echelon form: echelonize, then
back-substitute.  Pivot NORMALIZATION (leading-1 via `qnfInv`) and syntactic
uniqueness are NOT certified — see `ihqRrefUniquenessStatement`. -/
def ihqRref (rows : List (List QnfRat)) : List (List QnfRat) :=
  ihqBackReduce (ihqEchelonize rows)

/-- CANONICITY THEOREM (a): `ihqRref` preserves the row space. -/
theorem ihqRrefSpansSame {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) (vector : List QnfRat) :
    IhqMemSpan width (ihqRref rows) vector <-> IhqMemSpan width rows vector := by
  have hEchAll := ihqEchelonizeWidth rows hAll
  exact Iff.intro
    (fun hMem => ihqEchelonizeSpanSub1 rows hAll
      (ihqBackReduceSpanSub1 (ihqEchelonize rows) hEchAll hMem))
    (fun hMem => ihqBackReduceSpanSub2 (ihqEchelonize rows) hEchAll
      (ihqEchelonizeSpanSub2 rows hAll hMem))

theorem ihqRrefWidth {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : IhqAllWidth width (ihqRref rows) :=
  ihqBackReduceWidth (ihqEchelonize rows) (ihqEchelonizeWidth rows hAll)

/-- Syntactic uniqueness of the UN-normalized reduced row echelon form over ℚ — span-equal inputs give
literally equal `ihqRref` outputs. This statement is false and is refuted downstream in
`RationalFreeColumnUniqueness` (`rfcIhqRrefUniquenessRefuted`): `[[1,2]]` and `[[2,4]]` span the same line yet
have distinct `ihqRref`. The canonical target is the normalized `rreRref`, which IS unique (`rfcRreRrefUnique`).
Every decision use of uniqueness is served by `ihqSpanEqBSound`/`ihqSpanEqBComplete`. -/
def ihqRrefUniquenessStatement : Prop :=
  (width : Nat) -> (firstRows secondRows : List (List QnfRat)) ->
  IhqAllWidth width firstRows -> IhqAllWidth width secondRows ->
  ((vector : List QnfRat) ->
    (IhqMemSpan width firstRows vector <-> IhqMemSpan width secondRows vector)) ->
  ihqRref firstRows = ihqRref secondRows

/-- Owner flag: the un-normalized `ihqRrefUniquenessStatement` is not proven (it is refuted downstream,
`rfcIhqRrefUniquenessRefuted`); the canonical normalized `rreRref` uniqueness is proven (`rfcRreRrefUnique`). -/
def ihqRrefUniquenessIsProven : Bool := false

/-! ## Stage 6 — kernel-`rfl` fires (T5)

Closed-value pins.  The whole pipeline — `qnfInv` pivots, the counting divider,
the structural-fuel gcd — reduces inside the kernel; magnitudes are kept small
(≤ 6) per the unary-divider budget. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Fire (THE ℚ-content pin): span `{(1,2)}` EQUALS span `{(2,4)}` — the scalar-2
collapse that F2's `{0,1}` scalars cannot express (over F2 these spans differ:
`(1,2) = (1,0)`-pattern vs `(2,4) = (0,0)`-pattern would not even be the same
question). -/
theorem ihqFireScalarTwoSpanCollapse :
    ihqSpanEqB [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 2, qnfOfInt 4]] = true := rfl

/-- Fire (fractional cofactor): span `{(2)}` equals span `{(3)}` — the mutual
reductions run through the genuinely rational scalars `-2/3` and `-3/2`. -/
theorem ihqFireRationalCofactorSpan :
    ihqSpanEqB [[qnfOfInt 2]] [[qnfOfInt 3]] = true := rfl

/-- Fire (char-0 basis exchange): `{(1,0),(0,1)}` and `{(1,1),(1,-1)}` span the
same plane — `(1,1) + (1,-1) = (2,0)` needs division by 2, impossible over F2
(where these two lists do NOT span the same subspace). -/
theorem ihqFireBasisExchange :
    ihqSpanEqB [[qnfOfInt 1, qnfOfInt 0], [qnfOfInt 0, qnfOfInt 1]]
        [[qnfOfInt 1, qnfOfInt 1], [qnfOfInt 1, qnfOfInt (-1)]]
      = true := rfl

/-- Fire (FALSE control): the two axis lines are distinct subspaces. -/
theorem ihqFireSpanFalseControl :
    ihqSpanEqB [[qnfOfInt 1, qnfOfInt 0]] [[qnfOfInt 0, qnfOfInt 1]] = false := rfl

/-- Fire (compose arithmetic, literal output): scale-by-2 composed with
scale-by-3 IS scale-by-6 — the computed generator matrix is literally `[(1, 6)]`. -/
theorem ihqFireComposeScaleTwoThree :
    ihqComposeRows 1 1 1 [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 1, qnfOfInt 3]]
      = [[qnfOfInt 1, qnfOfInt 6]] := rfl

/-- Fire (compose, up to span): the composite of scale-by-2 and scale-by-3 spans
the scale-by-6 graph. -/
theorem ihqFireComposeScaleSpan :
    ihqSpanEqB
        (ihqComposeRows 1 1 1 [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 1, qnfOfInt 3]])
        [[qnfOfInt 1, qnfOfInt 6]]
      = true := rfl

/-- Fire (identity compose, left): `id ; scale-by-2 = scale-by-2` literally. -/
theorem ihqFireComposeIdentityLeft :
    ihqComposeRows 1 1 1 (ihqIdRows 1) [[qnfOfInt 1, qnfOfInt 2]]
      = [[qnfOfInt 1, qnfOfInt 2]] := rfl

/-- Fire (identity compose, right): `scale-by-2 ; id = scale-by-2` literally. -/
theorem ihqFireComposeIdentityRight :
    ihqComposeRows 1 1 1 [[qnfOfInt 1, qnfOfInt 2]] (ihqIdRows 1)
      = [[qnfOfInt 1, qnfOfInt 2]] := rfl

/-- Fire (THE PULLBACK SPEC in anger): `(1, 6)` is related by the computed
composite BECAUSE the middle vector `(2)` witnesses `(1,2) ∈ scale-2` and
`(2,6) ∈ scale-3` — discharged through `ihqComposeSpec.mpr`. -/
theorem ihqFireComposeSpecScaleSix :
    IhqPairMem 1 1
      (ihqComposeRows 1 1 1 [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 1, qnfOfInt 3]])
      [qnfOfInt 1] [qnfOfInt 6] := by
  have hFirstAll : IhqAllWidth 2 [[qnfOfInt 1, qnfOfInt 2]] :=
    IhqAllWidth.cons rfl IhqAllWidth.nil
  have hSecondAll : IhqAllWidth 2 [[qnfOfInt 1, qnfOfInt 3]] :=
    IhqAllWidth.cons rfl IhqAllWidth.nil
  refine (ihqComposeSpec 1 1 1 [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 1, qnfOfInt 3]]
    hFirstAll hSecondAll [qnfOfInt 1] [qnfOfInt 6]).mpr ?_
  refine Exists.intro [qnfOfInt 2] (And.intro ?_ ?_)
  · refine And.intro rfl (And.intro rfl ?_)
    have hPicked := IhqMemSpan.pick (width := 2) (rows := [[qnfOfInt 1, qnfOfInt 2]])
      qnfOne [qnfOfInt 1, qnfOfInt 2]
      (IhqRowMem.head [qnfOfInt 1, qnfOfInt 2] []) IhqMemSpan.zero
    exact hPicked
  · refine And.intro rfl (And.intro rfl ?_)
    have hPicked := IhqMemSpan.pick (width := 2) (rows := [[qnfOfInt 1, qnfOfInt 3]])
      (qnfOfInt 2) [qnfOfInt 1, qnfOfInt 3]
      (IhqRowMem.head [qnfOfInt 1, qnfOfInt 3] []) IhqMemSpan.zero
    exact hPicked

/-- Fire (converse, literal): the converse of the scale-by-2 graph is the
divide-by-2 graph `[(2, 1)]`. -/
theorem ihqFireConverseScaleTwo :
    ihqConverseRows 1 [[qnfOfInt 1, qnfOfInt 2]] = [[qnfOfInt 2, qnfOfInt 1]] := rfl

/-! ## Content marker -/

/-- The ℚ span/relations kit is decided. The span-equality decision `ihqSpanEqB` (mutual reduction over
exact-pivot echelon forms) is sound and complete (`ihqSpanEqBSound`/`ihqSpanEqBComplete`) against the
linear-combination inductive `IhqMemSpan`. Relational composition of ℚ generator-matrix relations
(`ihqComposeRows`) is characterized by the full pullback spec `ihqComposeSpec` (iff, both directions), with the
converse spec (`ihqConverseSpec`) and identity generators (`ihqIdRows`). -/
def ihqHasSpanDecision : Bool := true

end FX1Poly.ComputerAlgebra
