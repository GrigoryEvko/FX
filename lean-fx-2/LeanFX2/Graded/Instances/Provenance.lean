import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Provenance — provenance row semilattice

`ProvenanceGrade` tracks where a value came from.  Known provenance is
a row of source/derivation facts with set-style subset semantics.
`unknown` is an explicit top grade: once provenance is unknown, later
joins cannot recover a precise origin.

This is a bounded join-semilattice, not a `GradeSemiring`.
Provenance accumulates evidence by join; no annihilating multiplication
is mathematically honest for origin tracking at this layer.

Per `fx_design.md` §6.3 dim 8.  Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Provenance rows -/

/-- Atomic provenance fact.  The row carrier stores these facts without
deduplication; semantic equality is by mutual subset. -/
inductive ProvenanceFact : Type
  /-- Value originated at a named source boundary. -/
  | source (sourceName : String)
  /-- Value was derived from a named parent by a named transform. -/
  | derived (parentName transformName : String)
  /-- Value was aggregated from a named group/source collection. -/
  | aggregated (groupName : String)
  deriving DecidableEq, Repr

/-- A row of known provenance facts. -/
abbrev ProvenanceRow : Type := List ProvenanceFact

namespace ProvenanceRow

/-- Empty known provenance row. -/
def empty : ProvenanceRow := []

/-- Singleton known provenance row. -/
def singleton (someFact : ProvenanceFact) : ProvenanceRow :=
  [someFact]

/-- Join known provenance rows by appending facts. -/
def join (firstRow secondRow : ProvenanceRow) : ProvenanceRow :=
  firstRow ++ secondRow

/-- `Member someFact someRow` asserts that `someFact` occurs in the
row. -/
inductive Member (someFact : ProvenanceFact) : ProvenanceRow → Prop
  /-- The fact appears at the head of the row. -/
  | head (restRow : ProvenanceRow) :
      Member someFact (someFact :: restRow)
  /-- The fact appears in the tail. -/
  | tail (otherFact : ProvenanceFact) {restRow : ProvenanceRow}
      (alreadyIn : Member someFact restRow) :
      Member someFact (otherFact :: restRow)

/-- Subset relation for known provenance rows. -/
def subset (firstRow secondRow : ProvenanceRow) : Prop :=
  ∀ (someFact : ProvenanceFact),
    Member someFact firstRow → Member someFact secondRow

/-- Members of the left operand stay members after appending. -/
theorem member_append_left
    {someFact : ProvenanceFact}
    (firstRow secondRow : ProvenanceRow)
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
    {someFact : ProvenanceFact}
    (firstRow secondRow : ProvenanceRow)
    (memberInSecond : Member someFact secondRow) :
    Member someFact (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memberInSecond
  | cons headFact _ innerHypothesis =>
    exact Member.tail headFact innerHypothesis

/-- A member of an appended row came from one of the two operands. -/
theorem member_append_inv
    {someFact : ProvenanceFact}
    (firstRow secondRow : ProvenanceRow)
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

/-- Subset is reflexive. -/
theorem subset_refl (someRow : ProvenanceRow) : subset someRow someRow :=
  fun _ memberProof => memberProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : ProvenanceRow}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun someFact memberInFirst =>
    secondSubset someFact (firstSubset someFact memberInFirst)

/-- Empty provenance is bottom among known rows. -/
theorem empty_subset (someRow : ProvenanceRow) : subset empty someRow := by
  intro someFact memberInEmpty
  cases memberInEmpty

/-- The left operand is a subset of the row join. -/
theorem join_subset_left (firstRow secondRow : ProvenanceRow) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memberInFirst => member_append_left firstRow secondRow memberInFirst

/-- The right operand is a subset of the row join. -/
theorem join_subset_right (firstRow secondRow : ProvenanceRow) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memberInSecond => member_append_right firstRow secondRow memberInSecond

/-- Row join is the least upper bound under subset. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : ProvenanceRow}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst => exact firstSubset someFact memberInFirst
  | inr memberInSecond => exact secondSubset someFact memberInSecond

/-- Row join is idempotent up to subset. -/
theorem join_idempotent_subset (someRow : ProvenanceRow) :
    subset (join someRow someRow) someRow := by
  intro someFact memberInJoin
  cases member_append_inv someRow someRow memberInJoin with
  | inl memberInLeft => exact memberInLeft
  | inr memberInRight => exact memberInRight

/-- Row join commutes up to subset. -/
theorem join_commutes_subset (firstRow secondRow : ProvenanceRow) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro someFact memberInJoin
  cases member_append_inv firstRow secondRow memberInJoin with
  | inl memberInFirst =>
    exact member_append_right secondRow firstRow memberInFirst
  | inr memberInSecond =>
    exact member_append_left secondRow firstRow memberInSecond

/-- Row join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : ProvenanceRow) :
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

end ProvenanceRow

/-! ## Provenance grades -/

/-- Provenance grade: known row of provenance facts, or unknown top. -/
inductive ProvenanceGrade : Type
  /-- Known provenance facts with set-row semantics. -/
  | known (someRow : ProvenanceRow)
  /-- Unknown provenance; lattice top. -/
  | unknown
  deriving Repr

namespace ProvenanceGrade

/-- Empty known provenance. -/
def empty : ProvenanceGrade := .known ProvenanceRow.empty

/-- Singleton source-origin provenance. -/
def source (sourceName : String) : ProvenanceGrade :=
  .known (ProvenanceRow.singleton (.source sourceName))

/-- Singleton derivation provenance. -/
def derived (parentName transformName : String) : ProvenanceGrade :=
  .known (ProvenanceRow.singleton (.derived parentName transformName))

/-- Singleton aggregation provenance. -/
def aggregated (groupName : String) : ProvenanceGrade :=
  .known (ProvenanceRow.singleton (.aggregated groupName))

/-- Join provenance grades; unknown absorbs. -/
def join : ProvenanceGrade → ProvenanceGrade → ProvenanceGrade
  | .known firstRow, .known secondRow =>
      .known (ProvenanceRow.join firstRow secondRow)
  | .known _, .unknown => .unknown
  | .unknown, .known _ => .unknown
  | .unknown, .unknown => .unknown

/-- Provenance preorder: known rows compare by subset, and every known
row is below unknown. -/
def le : ProvenanceGrade → ProvenanceGrade → Prop
  | .known firstRow, .known secondRow => ProvenanceRow.subset firstRow secondRow
  | .known _, .unknown => True
  | .unknown, .known _ => False
  | .unknown, .unknown => True

end ProvenanceGrade

/-- Provenance grades form a bounded join-semilattice with unknown as
top. -/
instance : GradeJoinSemilattice ProvenanceGrade where
  bottom := ProvenanceGrade.empty
  join := ProvenanceGrade.join
  le := ProvenanceGrade.le

  le_refl := by
    intro value
    cases value with
    | known someRow => exact ProvenanceRow.subset_refl someRow
    | unknown => exact True.intro

  le_trans := by
    intro first second third firstLeSecond secondLeThird
    cases first with
    | known firstRow =>
      cases second with
      | known secondRow =>
        cases third with
        | known thirdRow =>
          exact ProvenanceRow.subset_trans firstLeSecond secondLeThird
        | unknown =>
          exact True.intro
      | unknown =>
        cases third with
        | known _ => contradiction
        | unknown => exact True.intro
    | unknown =>
      cases second with
      | known _ => contradiction
      | unknown =>
        cases third with
        | known _ => contradiction
        | unknown => exact True.intro

  bottom_le := by
    intro value
    cases value with
    | known someRow => exact ProvenanceRow.empty_subset someRow
    | unknown => exact True.intro

  le_join_left := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact ProvenanceRow.join_subset_left leftRow rightRow
      | unknown => exact True.intro
    | unknown =>
      cases right with
      | known _ => exact True.intro
      | unknown => exact True.intro

  le_join_right := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact ProvenanceRow.join_subset_right leftRow rightRow
      | unknown => exact True.intro
    | unknown =>
      cases right with
      | known _ => exact True.intro
      | unknown => exact True.intro

  join_least_upper_bound := by
    intro left right upper leftLeUpper rightLeUpper
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow =>
        cases upper with
        | known upperRow =>
          exact ProvenanceRow.join_least_upper_bound leftLeUpper rightLeUpper
        | unknown => exact True.intro
      | unknown =>
        cases upper with
        | known _ => contradiction
        | unknown => exact True.intro
    | unknown =>
      cases right with
      | known _ =>
        cases upper with
        | known _ => contradiction
        | unknown => exact True.intro
      | unknown =>
        cases upper with
        | known _ => contradiction
        | unknown => exact True.intro

  join_idempotent_le := by
    intro value
    cases value with
    | known someRow => exact ProvenanceRow.join_idempotent_subset someRow
    | unknown => exact True.intro

  join_comm_le := by
    intro left right
    cases left with
    | known leftRow =>
      cases right with
      | known rightRow => exact ProvenanceRow.join_commutes_subset leftRow rightRow
      | unknown => exact True.intro
    | unknown =>
      cases right with
      | known _ => exact True.intro
      | unknown => exact True.intro

  join_assoc_le := by
    intro first second third
    cases first with
    | known firstRow =>
      cases second with
      | known secondRow =>
        cases third with
        | known thirdRow =>
          exact ProvenanceRow.join_associates_subset firstRow secondRow thirdRow
        | unknown => exact True.intro
      | unknown =>
        cases third with
        | known _ => exact True.intro
        | unknown => exact True.intro
    | unknown =>
      cases second with
      | known _ =>
        cases third with
        | known _ => exact True.intro
        | unknown => exact True.intro
      | unknown =>
        cases third with
        | known _ => exact True.intro
        | unknown => exact True.intro

/-! ## Smoke samples -/

/-- A singleton source provenance row contains its source fact. -/
example :
    ProvenanceRow.Member (.source "sensor")
      (ProvenanceRow.singleton (.source "sensor")) :=
  ProvenanceRow.Member.head []

/-- Joining source provenance with derived provenance preserves the
derived fact. -/
example :
    ProvenanceRow.Member (.derived "sensor" "normalize")
      (ProvenanceRow.join
        (ProvenanceRow.singleton (.source "sensor"))
        (ProvenanceRow.singleton (.derived "sensor" "normalize"))) :=
  ProvenanceRow.member_append_right
    [ProvenanceFact.source "sensor"]
    [ProvenanceFact.derived "sensor" "normalize"]
    (ProvenanceRow.Member.head [])

/-- Unknown provenance absorbs known provenance. -/
example :
    ProvenanceGrade.join (ProvenanceGrade.source "sensor") .unknown
      = .unknown := rfl

end LeanFX2.Graded.Instances
