import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Version — version evidence rows

`VersionGrade` tracks version labels and explicit adapter edges known
for a value or declaration.  Version compatibility is not a numeric
resource law: a migration edge from `v1` to `v2` is directional
evidence, and composing versions requires graph reachability checks in
the surface/elaboration layer.  The kernel-grade layer therefore keeps
the evidence as a row and provides only the honest bounded
join-semilattice structure.

This is deliberately not a `GradeSemiring`; there is no annihilating
multiplication for version labels and adapter edges.

Per `fx_design.md` §6.3 dim 21 and §15.  Zero-axiom verified per
declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Version evidence rows -/

/-- Atomic version fact. -/
inductive VersionFact : Type
  /-- A declaration/value is associated with a version label. -/
  | label (versionName : String)
  /-- There is an explicit adapter/migration edge from one version to
  another. -/
  | adapter (fromVersion toVersion : String)
  deriving DecidableEq, Repr

/-- Version grades are list-backed rows of version evidence.  Order and
duplicates are ignored by the `subset` preorder. -/
abbrev VersionGrade : Type := List VersionFact

namespace VersionGrade

/-- Empty version evidence row. -/
def empty : VersionGrade := []

/-- Singleton version-label row. -/
def label (versionName : String) : VersionGrade :=
  [VersionFact.label versionName]

/-- Singleton adapter-edge row. -/
def adapter (fromVersion toVersion : String) : VersionGrade :=
  [VersionFact.adapter fromVersion toVersion]

/-- Join version evidence by appending rows. -/
def join (firstRow secondRow : VersionGrade) : VersionGrade :=
  firstRow ++ secondRow

/-- `Member someFact versionRow` asserts that `someFact` occurs in the
row. -/
inductive Member (someFact : VersionFact) : VersionGrade → Prop
  /-- The fact appears at the head of the row. -/
  | head (restRow : VersionGrade) :
      Member someFact (someFact :: restRow)
  /-- The fact appears in the tail. -/
  | tail (otherFact : VersionFact) {restRow : VersionGrade}
      (alreadyIn : Member someFact restRow) :
      Member someFact (otherFact :: restRow)

/-- Subset relation for version-evidence rows. -/
def subset (firstRow secondRow : VersionGrade) : Prop :=
  ∀ (someFact : VersionFact),
    Member someFact firstRow → Member someFact secondRow

/-! ## Membership lemmas -/

/-- Members of the left operand stay members after appending. -/
theorem member_append_left
    {someFact : VersionFact}
    (firstRow secondRow : VersionGrade)
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
    {someFact : VersionFact}
    (firstRow secondRow : VersionGrade)
    (memberInSecond : Member someFact secondRow) :
    Member someFact (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memberInSecond
  | cons headFact _ innerHypothesis =>
    exact Member.tail headFact innerHypothesis

/-- A member of an appended row came from one of the two operands. -/
theorem member_append_inv
    {someFact : VersionFact}
    (firstRow secondRow : VersionGrade)
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
theorem subset_refl (versionRow : VersionGrade) :
    subset versionRow versionRow :=
  fun _ memberProof => memberProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : VersionGrade}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun someFact memberInFirst =>
    secondSubset someFact (firstSubset someFact memberInFirst)

/-- Empty version evidence is bottom. -/
theorem empty_subset (versionRow : VersionGrade) :
    subset empty versionRow := by
  intro someFact memberInEmpty
  cases memberInEmpty

/-- The left operand is a subset of the join. -/
theorem join_subset_left (firstRow secondRow : VersionGrade) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memberInFirst => member_append_left firstRow secondRow memberInFirst

/-- The right operand is a subset of the join. -/
theorem join_subset_right (firstRow secondRow : VersionGrade) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memberInSecond => member_append_right firstRow secondRow memberInSecond

/-- The join is the least upper bound under subset. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : VersionGrade}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst => exact firstSubset someFact memberInFirst
  | inr memberInSecond => exact secondSubset someFact memberInSecond

/-- Join is idempotent up to subset. -/
theorem join_idempotent_subset (versionRow : VersionGrade) :
    subset (join versionRow versionRow) versionRow := by
  intro someFact memberInJoin
  cases member_append_inv versionRow versionRow memberInJoin with
  | inl memberInLeft => exact memberInLeft
  | inr memberInRight => exact memberInRight

/-- Join commutes up to subset. -/
theorem join_commutes_subset (firstRow secondRow : VersionGrade) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst =>
    exact member_append_right secondRow firstRow memberInFirst
  | inr memberInSecond =>
    exact member_append_left secondRow firstRow memberInSecond

/-- Join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : VersionGrade) :
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

end VersionGrade

/-- Version evidence rows form a bounded join-semilattice under row
append and subset. -/
instance : GradeJoinSemilattice VersionGrade where
  bottom := VersionGrade.empty
  join := VersionGrade.join
  le := VersionGrade.subset

  le_refl := VersionGrade.subset_refl

  le_trans := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact VersionGrade.subset_trans firstSubset secondSubset

  bottom_le := VersionGrade.empty_subset

  le_join_left := VersionGrade.join_subset_left

  le_join_right := VersionGrade.join_subset_right

  join_least_upper_bound := by
    intro firstRow secondRow thirdRow firstSubset secondSubset
    exact VersionGrade.join_least_upper_bound firstSubset secondSubset

  join_idempotent_le := VersionGrade.join_idempotent_subset

  join_comm_le := VersionGrade.join_commutes_subset

  join_assoc_le := VersionGrade.join_associates_subset

/-! ## Smoke samples -/

/-- A singleton label row contains that label fact. -/
example :
    VersionGrade.Member (.label "v1") (VersionGrade.label "v1") :=
  VersionGrade.Member.head []

/-- Joining an adapter row preserves the adapter evidence. -/
example :
    VersionGrade.Member (.adapter "v1" "v2")
      (VersionGrade.join
        (VersionGrade.label "v1")
        (VersionGrade.adapter "v1" "v2")) :=
  VersionGrade.member_append_right
    [VersionFact.label "v1"]
    [VersionFact.adapter "v1" "v2"]
    (VersionGrade.Member.head [])

end LeanFX2.Graded.Instances
