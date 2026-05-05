import LeanFX2.Graded.Semiring

/-! # Graded/Instances/ClockDomain — clock-domain row semilattice

`ClockDomainGrade` tracks the set of synchronized clock names touched
by a term.  Combinational logic is the empty row.  Logic synchronized
to one clock is a singleton row.  Joining rows accumulates clock
requirements; a row containing two distinct clock names is a conflict
that downstream typing rules must reject unless an explicit clock
crossing proof is available.

This is a bounded join-semilattice, not a `GradeSemiring`.  Clock
domains accumulate compatibility requirements by row union; pretending
they have semiring multiplication would hide cross-clock errors behind
bogus annihilation laws.

Per `fx_design.md` §6.3 dim 12 and §6.8.  Zero-axiom verified per
declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Clock-domain rows -/

/-- Clock-domain grades are list-backed rows of synchronized clock
names.  Order and duplicates are ignored by the `subset` preorder. -/
abbrev ClockDomainGrade : Type := List String

namespace ClockDomainGrade

/-- Combinational logic touches no synchronous clock. -/
def combinational : ClockDomainGrade := []

/-- A singleton synchronized clock domain. -/
def synchronous (clockName : String) : ClockDomainGrade := [clockName]

/-- Join clock-domain requirements by appending row witnesses. -/
def join (firstRow secondRow : ClockDomainGrade) : ClockDomainGrade :=
  firstRow ++ secondRow

/-! ## Custom membership and subset

The membership predicate is hand-rolled instead of using stdlib list
membership, matching `Effects.Foundation` and keeping the proof
surface small and axiom-auditable. -/

/-- `Member clockName clockRow` asserts that `clockName` occurs in the
row. -/
inductive Member (clockName : String) : ClockDomainGrade → Prop
  /-- The clock name appears at the head of the row. -/
  | head (restRow : ClockDomainGrade) :
      Member clockName (clockName :: restRow)
  /-- The clock name appears in the tail. -/
  | tail (otherClock : String) {restRow : ClockDomainGrade}
      (alreadyIn : Member clockName restRow) :
      Member clockName (otherClock :: restRow)

/-- Subset relation for clock-domain rows. -/
def subset (firstRow secondRow : ClockDomainGrade) : Prop :=
  ∀ (clockName : String),
    Member clockName firstRow → Member clockName secondRow

/-- A row has a cross-clock conflict when it contains two distinct
clock names.  The semilattice records this as a predicate rather than
collapsing the row to a finite top element, so diagnostics can report
the concrete clock names involved. -/
def hasConflict (clockRow : ClockDomainGrade) : Prop :=
  ∃ firstClock secondClock,
    Member firstClock clockRow ∧
    Member secondClock clockRow ∧
    firstClock ≠ secondClock

/-! ## Membership lemmas -/

/-- Members of the left operand stay members after appending. -/
theorem member_append_left
    {clockName : String}
    (firstRow secondRow : ClockDomainGrade)
    (memberInFirst : Member clockName firstRow) :
    Member clockName (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => cases memberInFirst
  | cons headClock tailRow innerHypothesis =>
    cases memberInFirst with
    | head _ =>
      exact Member.head (tailRow ++ secondRow)
    | tail _ innerProof =>
      exact Member.tail headClock (innerHypothesis innerProof)

/-- Members of the right operand stay members after prepending. -/
theorem member_append_right
    {clockName : String}
    (firstRow secondRow : ClockDomainGrade)
    (memberInSecond : Member clockName secondRow) :
    Member clockName (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memberInSecond
  | cons headClock _ innerHypothesis =>
    exact Member.tail headClock innerHypothesis

/-- A member of an appended row came from one of the two operands. -/
theorem member_append_inv
    {clockName : String}
    (firstRow secondRow : ClockDomainGrade)
    (memberInJoin : Member clockName (firstRow ++ secondRow)) :
    Member clockName firstRow ∨ Member clockName secondRow := by
  induction firstRow with
  | nil => exact Or.inr memberInJoin
  | cons headClock tailRow innerHypothesis =>
    cases memberInJoin with
    | head _ =>
      exact Or.inl (Member.head tailRow)
    | tail _ innerProof =>
      cases innerHypothesis innerProof with
      | inl proofInTail =>
        exact Or.inl (Member.tail headClock proofInTail)
      | inr proofInSecond =>
        exact Or.inr proofInSecond

/-! ## Subset and join laws -/

/-- Subset is reflexive. -/
theorem subset_refl (clockRow : ClockDomainGrade) : subset clockRow clockRow :=
  fun _ memberProof => memberProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : ClockDomainGrade}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun clockName memberInFirst =>
    secondSubset clockName (firstSubset clockName memberInFirst)

/-- Combinational logic is the bottom row. -/
theorem combinational_subset (clockRow : ClockDomainGrade) :
    subset combinational clockRow := by
  intro clockName memberInEmpty
  cases memberInEmpty

/-- The left operand is a subset of the join. -/
theorem join_subset_left (firstRow secondRow : ClockDomainGrade) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memberInFirst => member_append_left firstRow secondRow memberInFirst

/-- The right operand is a subset of the join. -/
theorem join_subset_right (firstRow secondRow : ClockDomainGrade) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memberInSecond => member_append_right firstRow secondRow memberInSecond

/-- The join is the least upper bound under subset. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : ClockDomainGrade}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro clockName memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst => exact firstSubset clockName memberInFirst
  | inr memberInSecond => exact secondSubset clockName memberInSecond

/-- Join is idempotent up to subset. -/
theorem join_idempotent_subset (clockRow : ClockDomainGrade) :
    subset (join clockRow clockRow) clockRow := by
  intro clockName memberInJoin
  cases member_append_inv clockRow clockRow memberInJoin with
  | inl memberInLeft => exact memberInLeft
  | inr memberInRight => exact memberInRight

/-- Join commutes up to subset. -/
theorem join_commutes_subset (firstRow secondRow : ClockDomainGrade) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro clockName memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst =>
    exact member_append_right secondRow firstRow memberInFirst
  | inr memberInSecond =>
    exact member_append_left secondRow firstRow memberInSecond

/-- Join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : ClockDomainGrade) :
    subset (join (join firstRow secondRow) thirdRow)
           (join firstRow (join secondRow thirdRow)) := by
  intro clockName memberInOuter
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

end ClockDomainGrade

/-- Clock-domain rows form a bounded join-semilattice under row append
and subset. -/
instance : GradeJoinSemilattice ClockDomainGrade where
  bottom := ClockDomainGrade.combinational
  join := ClockDomainGrade.join
  le := ClockDomainGrade.subset

  le_refl := ClockDomainGrade.subset_refl

  le_trans := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact ClockDomainGrade.subset_trans firstSubset secondSubset

  bottom_le := ClockDomainGrade.combinational_subset

  le_join_left := ClockDomainGrade.join_subset_left

  le_join_right := ClockDomainGrade.join_subset_right

  join_least_upper_bound := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact ClockDomainGrade.join_least_upper_bound firstSubset secondSubset

  join_idempotent_le := ClockDomainGrade.join_idempotent_subset

  join_comm_le := ClockDomainGrade.join_commutes_subset

  join_assoc_le := ClockDomainGrade.join_associates_subset

/-! ## Smoke samples -/

/-- A singleton synchronous row contains its clock name. -/
example :
    ClockDomainGrade.Member "main" (ClockDomainGrade.synchronous "main") :=
  ClockDomainGrade.Member.head []

/-- Joining a combinational row into a synchronous row leaves the
synchronous requirement. -/
example :
    ClockDomainGrade.join ClockDomainGrade.combinational
      (ClockDomainGrade.synchronous "main")
      = ClockDomainGrade.synchronous "main" := rfl

/-- Joining two different clocks records both names for the downstream
conflict check. -/
example :
    ClockDomainGrade.hasConflict
      (ClockDomainGrade.join
        (ClockDomainGrade.synchronous "main")
        (ClockDomainGrade.synchronous "aux")) :=
  Exists.intro "main" (Exists.intro "aux"
    (And.intro
      (ClockDomainGrade.member_append_left ["main"] ["aux"]
        (ClockDomainGrade.Member.head []))
      (And.intro
        (ClockDomainGrade.member_append_right ["main"] ["aux"]
          (ClockDomainGrade.Member.head []))
        (by decide))))

end LeanFX2.Graded.Instances
