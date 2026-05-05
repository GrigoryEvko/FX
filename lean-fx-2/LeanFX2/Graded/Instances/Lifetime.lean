import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Lifetime — lifetime obligation rows

`LifetimeGrade` tracks the named region lifetimes that a value depends
on.  The `'static` case is represented by the empty row: the value has
no borrowed-region obligation.  A value borrowed from region `r` is a
singleton row `[r]`.  Combining computations appends rows and the
custom subset preorder gives set semantics.

This is a bounded join-semilattice, not a `GradeSemiring`.
Lifetimes accumulate obligations and are later discharged against the
typing context's outlives facts; there is no honest annihilating
semiring multiplication at this layer.

Per `fx_design.md` §6.3 dim 7.  Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Lifetime rows -/

/-- Lifetime grades are list-backed rows of named region obligations.
Order and duplicates are ignored by the `subset` preorder. -/
abbrev LifetimeGrade : Type := List String

namespace LifetimeGrade

/-- Static lifetime: no region obligation. -/
def static : LifetimeGrade := []

/-- A singleton named-region obligation. -/
def region (regionName : String) : LifetimeGrade := [regionName]

/-- Join lifetime obligations by appending rows. -/
def join (firstRow secondRow : LifetimeGrade) : LifetimeGrade :=
  firstRow ++ secondRow

/-! ## Custom membership and subset -/

/-- `Member regionName lifetimeRow` asserts that `regionName` occurs in
the row. -/
inductive Member (regionName : String) : LifetimeGrade → Prop
  /-- The region name appears at the head of the row. -/
  | head (restRow : LifetimeGrade) :
      Member regionName (regionName :: restRow)
  /-- The region name appears in the tail. -/
  | tail (otherRegion : String) {restRow : LifetimeGrade}
      (alreadyIn : Member regionName restRow) :
      Member regionName (otherRegion :: restRow)

/-- Subset relation for lifetime rows. -/
def subset (firstRow secondRow : LifetimeGrade) : Prop :=
  ∀ (regionName : String),
    Member regionName firstRow → Member regionName secondRow

/-! ## Membership lemmas -/

/-- Members of the left operand stay members after appending. -/
theorem member_append_left
    {regionName : String}
    (firstRow secondRow : LifetimeGrade)
    (memberInFirst : Member regionName firstRow) :
    Member regionName (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => cases memberInFirst
  | cons headRegion tailRow innerHypothesis =>
    cases memberInFirst with
    | head _ =>
      exact Member.head (tailRow ++ secondRow)
    | tail _ innerProof =>
      exact Member.tail headRegion (innerHypothesis innerProof)

/-- Members of the right operand stay members after prepending. -/
theorem member_append_right
    {regionName : String}
    (firstRow secondRow : LifetimeGrade)
    (memberInSecond : Member regionName secondRow) :
    Member regionName (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memberInSecond
  | cons headRegion _ innerHypothesis =>
    exact Member.tail headRegion innerHypothesis

/-- A member of an appended row came from one of the two operands. -/
theorem member_append_inv
    {regionName : String}
    (firstRow secondRow : LifetimeGrade)
    (memberInJoin : Member regionName (firstRow ++ secondRow)) :
    Member regionName firstRow ∨ Member regionName secondRow := by
  induction firstRow with
  | nil => exact Or.inr memberInJoin
  | cons headRegion tailRow innerHypothesis =>
    cases memberInJoin with
    | head _ =>
      exact Or.inl (Member.head tailRow)
    | tail _ innerProof =>
      cases innerHypothesis innerProof with
      | inl proofInTail =>
        exact Or.inl (Member.tail headRegion proofInTail)
      | inr proofInSecond =>
        exact Or.inr proofInSecond

/-! ## Subset and join laws -/

/-- Subset is reflexive. -/
theorem subset_refl (lifetimeRow : LifetimeGrade) :
    subset lifetimeRow lifetimeRow :=
  fun _ memberProof => memberProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : LifetimeGrade}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun regionName memberInFirst =>
    secondSubset regionName (firstSubset regionName memberInFirst)

/-- Static lifetime is the bottom row. -/
theorem static_subset (lifetimeRow : LifetimeGrade) :
    subset static lifetimeRow := by
  intro regionName memberInEmpty
  cases memberInEmpty

/-- The left operand is a subset of the join. -/
theorem join_subset_left (firstRow secondRow : LifetimeGrade) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memberInFirst => member_append_left firstRow secondRow memberInFirst

/-- The right operand is a subset of the join. -/
theorem join_subset_right (firstRow secondRow : LifetimeGrade) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memberInSecond => member_append_right firstRow secondRow memberInSecond

/-- The join is the least upper bound under subset. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : LifetimeGrade}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro regionName memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst => exact firstSubset regionName memberInFirst
  | inr memberInSecond => exact secondSubset regionName memberInSecond

/-- Join is idempotent up to subset. -/
theorem join_idempotent_subset (lifetimeRow : LifetimeGrade) :
    subset (join lifetimeRow lifetimeRow) lifetimeRow := by
  intro regionName memberInJoin
  cases member_append_inv lifetimeRow lifetimeRow memberInJoin with
  | inl memberInLeft => exact memberInLeft
  | inr memberInRight => exact memberInRight

/-- Join commutes up to subset. -/
theorem join_commutes_subset (firstRow secondRow : LifetimeGrade) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro regionName memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst =>
    exact member_append_right secondRow firstRow memberInFirst
  | inr memberInSecond =>
    exact member_append_left secondRow firstRow memberInSecond

/-- Join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : LifetimeGrade) :
    subset (join (join firstRow secondRow) thirdRow)
           (join firstRow (join secondRow thirdRow)) := by
  intro regionName memberInOuter
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

end LifetimeGrade

/-- Lifetime obligation rows form a bounded join-semilattice under row
append and subset. -/
instance : GradeJoinSemilattice LifetimeGrade where
  bottom := LifetimeGrade.static
  join := LifetimeGrade.join
  le := LifetimeGrade.subset

  le_refl := LifetimeGrade.subset_refl

  le_trans := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact LifetimeGrade.subset_trans firstSubset secondSubset

  bottom_le := LifetimeGrade.static_subset

  le_join_left := LifetimeGrade.join_subset_left

  le_join_right := LifetimeGrade.join_subset_right

  join_least_upper_bound := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact LifetimeGrade.join_least_upper_bound firstSubset secondSubset

  join_idempotent_le := LifetimeGrade.join_idempotent_subset

  join_comm_le := LifetimeGrade.join_commutes_subset

  join_assoc_le := LifetimeGrade.join_associates_subset

/-! ## Smoke samples -/

/-- A singleton region row contains its region name. -/
example :
    LifetimeGrade.Member "arena" (LifetimeGrade.region "arena") :=
  LifetimeGrade.Member.head []

/-- Joining static into a region obligation leaves the region row. -/
example :
    LifetimeGrade.join LifetimeGrade.static (LifetimeGrade.region "arena")
      = LifetimeGrade.region "arena" := rfl

/-- Joining two borrowed regions records both obligations. -/
example :
    LifetimeGrade.Member "session"
      (LifetimeGrade.join
        (LifetimeGrade.region "arena")
        (LifetimeGrade.region "session")) :=
  LifetimeGrade.member_append_right ["arena"] ["session"]
    (LifetimeGrade.Member.head [])

end LeanFX2.Graded.Instances
