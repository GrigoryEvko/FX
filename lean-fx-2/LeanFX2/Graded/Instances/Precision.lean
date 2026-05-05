import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Precision — precision-bound evidence rows

`PrecisionGrade` tracks floating-point / decimal precision facts.
The carrier preserves rational ULP bounds as numerator plus positive
denominator.  The grade layer does not pretend those bounds form a
verified arithmetic error-propagation semiring yet; instead it records
the evidence as a bounded join-semilattice.  Later numeric rules can
consume the row and prove operation-specific propagation theorems.

`unbounded` is an explicit top grade: once a computation has no checked
precision bound, joining more bounded evidence cannot recover a global
bound.

Per `fx_design.md` §6.3 dim 14 and §3.11.  Zero-axiom verified per
declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Precision evidence rows -/

/-- Rational ULP bound represented as `numerator / (denominatorMinusOne
+ 1)`, so the denominator is positive by construction. -/
structure ULPBound : Type where
  /-- Nonnegative numerator of the rational ULP bound. -/
  numerator : Nat
  /-- Denominator is this value plus one. -/
  denominatorMinusOne : Nat
  deriving DecidableEq, Repr

namespace ULPBound

/-- Denominator of the rational ULP bound; always positive. -/
def denominator (someBound : ULPBound) : Nat :=
  someBound.denominatorMinusOne + 1

/-- Exact zero-error ULP bound. -/
def exact : ULPBound where
  numerator := 0
  denominatorMinusOne := 0

end ULPBound

/-- Atomic precision fact. -/
inductive PrecisionFact : Type
  /-- A checked rational ULP error bound. -/
  | ulpBound (someBound : ULPBound)
  /-- A named strict-control mode, such as a rounding or FMA setting.
  The kernel keeps the evidence; mode compatibility is checked by
  downstream numeric rules. -/
  | controlMode (modeName : String)
  deriving DecidableEq, Repr

/-- A row of known precision evidence. -/
abbrev PrecisionRow : Type := List PrecisionFact

namespace PrecisionRow

/-- Empty known precision row: exact/no precision debt. -/
def empty : PrecisionRow := []

/-- Singleton known precision row. -/
def singleton (someFact : PrecisionFact) : PrecisionRow :=
  [someFact]

/-- Join known precision rows by appending facts. -/
def join (firstRow secondRow : PrecisionRow) : PrecisionRow :=
  firstRow ++ secondRow

/-- `Member someFact precisionRow` asserts that `someFact` occurs in
the row. -/
inductive Member (someFact : PrecisionFact) : PrecisionRow → Prop
  /-- The fact appears at the head of the row. -/
  | head (restRow : PrecisionRow) :
      Member someFact (someFact :: restRow)
  /-- The fact appears in the tail. -/
  | tail (otherFact : PrecisionFact) {restRow : PrecisionRow}
      (alreadyIn : Member someFact restRow) :
      Member someFact (otherFact :: restRow)

/-- Subset relation for precision-evidence rows. -/
def subset (firstRow secondRow : PrecisionRow) : Prop :=
  ∀ (someFact : PrecisionFact),
    Member someFact firstRow → Member someFact secondRow

/-! ## Membership lemmas -/

/-- Members of the left operand stay members after appending. -/
theorem member_append_left
    {someFact : PrecisionFact}
    (firstRow secondRow : PrecisionRow)
    (memberInFirst : Member someFact firstRow) :
    Member someFact (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => cases memberInFirst
  | cons headFact tailRow innerHypothesis =>
    cases memberInFirst with
    | head _ =>
      exact Member.head (tailRow ++ secondRow)
    | tail _ innerProof =>
      exact Member.tail headFact (innerHypothesis innerProof)

/-- Members of the right operand stay members after prepending. -/
theorem member_append_right
    {someFact : PrecisionFact}
    (firstRow secondRow : PrecisionRow)
    (memberInSecond : Member someFact secondRow) :
    Member someFact (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memberInSecond
  | cons headFact _ innerHypothesis =>
    exact Member.tail headFact innerHypothesis

/-- A member of an appended row came from one of the two operands. -/
theorem member_append_inv
    {someFact : PrecisionFact}
    (firstRow secondRow : PrecisionRow)
    (memberInJoin : Member someFact (firstRow ++ secondRow)) :
    Member someFact firstRow ∨ Member someFact secondRow := by
  induction firstRow with
  | nil => exact Or.inr memberInJoin
  | cons headFact tailRow innerHypothesis =>
    cases memberInJoin with
    | head _ =>
      exact Or.inl (Member.head tailRow)
    | tail _ innerProof =>
      cases innerHypothesis innerProof with
      | inl proofInTail =>
        exact Or.inl (Member.tail headFact proofInTail)
      | inr proofInSecond =>
        exact Or.inr proofInSecond

/-! ## Subset and join laws -/

/-- Subset is reflexive. -/
theorem subset_refl (precisionRow : PrecisionRow) :
    subset precisionRow precisionRow :=
  fun _ memberProof => memberProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : PrecisionRow}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun someFact memberInFirst =>
    secondSubset someFact (firstSubset someFact memberInFirst)

/-- Empty precision evidence is bottom among known rows. -/
theorem empty_subset (precisionRow : PrecisionRow) :
    subset empty precisionRow := by
  intro someFact memberInEmpty
  cases memberInEmpty

/-- The left operand is a subset of the row join. -/
theorem join_subset_left (firstRow secondRow : PrecisionRow) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memberInFirst => member_append_left firstRow secondRow memberInFirst

/-- The right operand is a subset of the row join. -/
theorem join_subset_right (firstRow secondRow : PrecisionRow) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memberInSecond => member_append_right firstRow secondRow memberInSecond

/-- Row join is the least upper bound under subset. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : PrecisionRow}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst => exact firstSubset someFact memberInFirst
  | inr memberInSecond => exact secondSubset someFact memberInSecond

/-- Row join is idempotent up to subset. -/
theorem join_idempotent_subset (precisionRow : PrecisionRow) :
    subset (join precisionRow precisionRow) precisionRow := by
  intro someFact memberInJoin
  cases member_append_inv precisionRow precisionRow memberInJoin with
  | inl memberInLeft => exact memberInLeft
  | inr memberInRight => exact memberInRight

/-- Row join commutes up to subset. -/
theorem join_commutes_subset (firstRow secondRow : PrecisionRow) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst =>
    exact member_append_right secondRow firstRow memberInFirst
  | inr memberInSecond =>
    exact member_append_left secondRow firstRow memberInSecond

/-- Row join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : PrecisionRow) :
    subset (join (join firstRow secondRow) thirdRow)
           (join firstRow (join secondRow thirdRow)) := by
  intro someFact memberInOuter
  cases member_append_inv (join firstRow secondRow) thirdRow memberInOuter with
  | inl memberInLeft =>
    cases member_append_inv firstRow secondRow memberInLeft with
    | inl memberInFirst =>
      exact member_append_left firstRow (join secondRow thirdRow) memberInFirst
    | inr memberInSecond =>
      exact member_append_right firstRow (join secondRow thirdRow)
        (member_append_left secondRow thirdRow memberInSecond)
  | inr memberInThird =>
    exact member_append_right firstRow (join secondRow thirdRow)
      (member_append_right secondRow thirdRow memberInThird)

end PrecisionRow

/-! ## Precision grades -/

/-- Precision grade: known precision evidence row, or unbounded top. -/
inductive PrecisionGrade : Type
  /-- Known precision evidence. -/
  | known (someRow : PrecisionRow)
  /-- Explicitly unbounded / unchecked precision. -/
  | unbounded
  deriving Repr

namespace PrecisionGrade

/-- Empty known precision evidence. -/
def exact : PrecisionGrade := .known PrecisionRow.empty

/-- Singleton rational ULP-bound evidence. -/
def ulpBound (someBound : ULPBound) : PrecisionGrade :=
  .known (PrecisionRow.singleton (.ulpBound someBound))

/-- Singleton named control-mode evidence. -/
def controlMode (modeName : String) : PrecisionGrade :=
  .known (PrecisionRow.singleton (.controlMode modeName))

/-- Join precision grades; unbounded absorbs. -/
def join : PrecisionGrade → PrecisionGrade → PrecisionGrade
  | .known firstRow, .known secondRow =>
      .known (PrecisionRow.join firstRow secondRow)
  | .known _, .unbounded => .unbounded
  | .unbounded, .known _ => .unbounded
  | .unbounded, .unbounded => .unbounded

/-- Precision preorder: known rows compare by subset, and every known
row is below unbounded. -/
def le : PrecisionGrade → PrecisionGrade → Prop
  | .known firstRow, .known secondRow => PrecisionRow.subset firstRow secondRow
  | .known _, .unbounded => True
  | .unbounded, .known _ => False
  | .unbounded, .unbounded => True

end PrecisionGrade

/-- Precision evidence forms a bounded join-semilattice with unbounded
as top. -/
instance : GradeJoinSemilattice PrecisionGrade where
  bottom := PrecisionGrade.exact
  join := PrecisionGrade.join
  le := PrecisionGrade.le

  le_refl := by
    intro value
    cases value with
    | known someRow => exact PrecisionRow.subset_refl someRow
    | unbounded => exact True.intro

  le_trans := by
    intro first second third firstLeSecond secondLeThird
    cases first with
    | known firstRow =>
      cases second with
      | known secondRow =>
        cases third with
        | known thirdRow =>
          exact PrecisionRow.subset_trans firstLeSecond secondLeThird
        | unbounded =>
          exact True.intro
      | unbounded =>
        cases third with
        | known _ => contradiction
        | unbounded => exact True.intro
    | unbounded =>
      cases second with
      | known _ => contradiction
      | unbounded =>
        cases third with
        | known _ => contradiction
        | unbounded => exact True.intro

  bottom_le := by
    intro value
    cases value with
    | known someRow => exact PrecisionRow.empty_subset someRow
    | unbounded => exact True.intro

  le_join_left := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact PrecisionRow.join_subset_left leftRow rightRow
      | unbounded => exact True.intro
    | unbounded =>
      cases right with
      | known _ => exact True.intro
      | unbounded => exact True.intro

  le_join_right := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact PrecisionRow.join_subset_right leftRow rightRow
      | unbounded => exact True.intro
    | unbounded =>
      cases right with
      | known _ => exact True.intro
      | unbounded => exact True.intro

  join_least_upper_bound := by
    intro left right upper leftLeUpper rightLeUpper
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow =>
        cases upper with
        | known upperRow =>
          exact PrecisionRow.join_least_upper_bound leftLeUpper rightLeUpper
        | unbounded => exact True.intro
      | unbounded =>
        cases upper with
        | known _ => contradiction
        | unbounded => exact True.intro
    | unbounded =>
      cases right with
      | known _ =>
        cases upper with
        | known _ => contradiction
        | unbounded => exact True.intro
      | unbounded =>
        cases upper with
        | known _ => contradiction
        | unbounded => exact True.intro

  join_idempotent_le := by
    intro value
    cases value with
    | known someRow => exact PrecisionRow.join_idempotent_subset someRow
    | unbounded => exact True.intro

  join_comm_le := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact PrecisionRow.join_commutes_subset leftRow rightRow
      | unbounded => exact True.intro
    | unbounded =>
      cases right with
      | known _ => exact True.intro
      | unbounded => exact True.intro

  join_assoc_le := by
    intro first second third
    cases first with
    | known firstRow =>
      cases second with
      | known secondRow =>
        cases third with
        | known thirdRow =>
          exact PrecisionRow.join_associates_subset firstRow secondRow thirdRow
        | unbounded => exact True.intro
      | unbounded =>
        cases third with
        | known _ => exact True.intro
        | unbounded => exact True.intro
    | unbounded =>
      cases second with
      | known _ =>
        cases third with
        | known _ => exact True.intro
        | unbounded => exact True.intro
      | unbounded =>
        cases third with
        | known _ => exact True.intro
        | unbounded => exact True.intro

/-! ## Smoke samples -/

/-- Exact ULP bound has denominator one. -/
example :
    ULPBound.denominator ULPBound.exact = 1 := rfl

/-- A singleton ULP-bound row contains that bound fact. -/
example :
    PrecisionRow.Member (.ulpBound ULPBound.exact)
      (PrecisionRow.singleton (.ulpBound ULPBound.exact)) :=
  PrecisionRow.Member.head []

/-- Unbounded precision absorbs checked evidence. -/
example :
    PrecisionGrade.join (PrecisionGrade.ulpBound ULPBound.exact) .unbounded
      = .unbounded := rfl

end LeanFX2.Graded.Instances
