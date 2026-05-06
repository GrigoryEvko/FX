/-! # Foundation/Effect — effect rows and operation permission

This module holds the effect-row primitives that the raw-aware `Term`
kernel may mention without importing the later `Effects` layer.
The richer row-level step and handler semantics remain in
`LeanFX2.Effects.Step` / `LeanFX2.Effects.Handlers`.
-/

namespace LeanFX2.Effects

universe payloadLevel sourcePayloadLevel targetPayloadLevel

/-! ## Effect labels and rows -/

/-- Built-in effect labels. -/
inductive EffectLabel : Type
  /-- Pure terminating effect. -/
  | tot
  /-- May diverge. -/
  | div
  /-- Erased proof-time effect. -/
  | ghost
  /-- May raise exceptions. -/
  | exn
  /-- General input/output. -/
  | io
  /-- May allocate heap memory. -/
  | alloc
  /-- May read from state. -/
  | read
  /-- May write state; semantically subsumes read. -/
  | write
  /-- Asynchronous operations. -/
  | async
  deriving DecidableEq, Repr

/-- Effect rows are lists of labels.  The preorder below gives them
set-style semantics without needing normalization or quotienting. -/
abbrev EffectRow := List EffectLabel

namespace EffectRow

/-- The empty effect row, i.e. total/pure computation. -/
def empty : EffectRow := []

/-- A singleton effect row. -/
def singleton (someLabel : EffectLabel) : EffectRow :=
  [someLabel]

/-- Custom row membership predicate.  This keeps row proofs independent of
stdlib list-membership lemmas. -/
inductive Member (someLabel : EffectLabel) : EffectRow → Prop
  /-- The label is at the head of the row. -/
  | head (restRow : EffectRow) :
      Member someLabel (someLabel :: restRow)
  /-- The label is in the tail of the row. -/
  | tail (otherLabel : EffectLabel) {restRow : EffectRow}
      (alreadyIn : Member someLabel restRow) :
      Member someLabel (otherLabel :: restRow)

/-- Row preorder: every label in `firstRow` is available in `secondRow`. -/
def subset (firstRow secondRow : EffectRow) : Prop :=
  ∀ (someLabel : EffectLabel),
    Member someLabel firstRow → Member someLabel secondRow

/-- Row join.  Append is enough because `subset` gives set-style semantics. -/
def join (firstRow secondRow : EffectRow) : EffectRow :=
  firstRow ++ secondRow

/-- Members of the left operand remain members after join. -/
theorem member_append_left
    {someLabel : EffectLabel}
    (firstRow secondRow : EffectRow)
    (memInFirst : Member someLabel firstRow) :
    Member someLabel (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => cases memInFirst
  | cons headLabel tailRow innerHypothesis =>
    cases memInFirst with
    | head _ =>
      exact Member.head (tailRow ++ secondRow)
    | tail _ innerProof =>
      exact Member.tail headLabel (innerHypothesis innerProof)

/-- Members of the right operand remain members after join. -/
theorem member_append_right
    {someLabel : EffectLabel}
    (firstRow secondRow : EffectRow)
    (memInSecond : Member someLabel secondRow) :
    Member someLabel (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memInSecond
  | cons headLabel _ innerHypothesis =>
    exact Member.tail headLabel innerHypothesis

/-- Inversion for membership in an appended row. -/
theorem member_append_inv
    {someLabel : EffectLabel}
    (firstRow secondRow : EffectRow)
    (memInJoin : Member someLabel (firstRow ++ secondRow)) :
    Member someLabel firstRow ∨ Member someLabel secondRow := by
  induction firstRow with
  | nil => exact Or.inr memInJoin
  | cons headLabel tailRow innerHypothesis =>
    cases memInJoin with
    | head _ =>
      exact Or.inl (Member.head tailRow)
    | tail _ innerProof =>
      cases innerHypothesis innerProof with
      | inl proofInTail =>
        exact Or.inl (Member.tail headLabel proofInTail)
      | inr proofInSecond =>
        exact Or.inr proofInSecond

/-- Subset is reflexive. -/
theorem subset_refl (someRow : EffectRow) : subset someRow someRow :=
  fun _ memProof => memProof

/-- Subset is transitive. -/
theorem subset_trans
    {firstRow secondRow thirdRow : EffectRow}
    (firstSubset : subset firstRow secondRow)
    (secondSubset : subset secondRow thirdRow) :
    subset firstRow thirdRow :=
  fun someLabel memInFirst =>
    secondSubset someLabel (firstSubset someLabel memInFirst)

/-- Empty is the bottom row. -/
theorem empty_subset (someRow : EffectRow) : subset empty someRow := by
  intro _ memInEmpty
  cases memInEmpty

/-- The left operand is included in the join. -/
theorem join_subset_left (firstRow secondRow : EffectRow) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memInFirst => member_append_left firstRow secondRow memInFirst

/-- The right operand is included in the join. -/
theorem join_subset_right (firstRow secondRow : EffectRow) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memInSecond => member_append_right firstRow secondRow memInSecond

/-- The join is the least upper bound for the row preorder. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : EffectRow}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro someLabel memInJoin
  cases member_append_inv firstRow secondRow memInJoin with
  | inl memInFirst => exact firstSubset someLabel memInFirst
  | inr memInSecond => exact secondSubset someLabel memInSecond

/-- Join is idempotent up to subset. -/
theorem join_idempotent_subset (someRow : EffectRow) :
    subset (join someRow someRow) someRow := by
  intro someLabel memInJoin
  cases member_append_inv someRow someRow memInJoin with
  | inl memInLeft => exact memInLeft
  | inr memInRight => exact memInRight

/-- Join commutes up to subset. -/
theorem join_commutes_subset
    (firstRow secondRow : EffectRow) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro someLabel memInJoin
  cases member_append_inv firstRow secondRow memInJoin with
  | inl memInFirst =>
    exact member_append_right secondRow firstRow memInFirst
  | inr memInSecond =>
    exact member_append_left secondRow firstRow memInSecond

/-- Join associates up to subset. -/
theorem join_associates_subset
    (firstRow secondRow thirdRow : EffectRow) :
    subset (join (join firstRow secondRow) thirdRow)
           (join firstRow (join secondRow thirdRow)) := by
  intro someLabel memInOuter
  cases member_append_inv (join firstRow secondRow) thirdRow memInOuter with
  | inl memInLeft =>
    cases member_append_inv firstRow secondRow memInLeft with
    | inl memInFirst =>
      exact member_append_left firstRow (join secondRow thirdRow) memInFirst
    | inr memInSecond =>
      exact member_append_right firstRow (join secondRow thirdRow)
        (member_append_left secondRow thirdRow memInSecond)
  | inr memInThird =>
    exact member_append_right firstRow (join secondRow thirdRow)
      (member_append_right secondRow thirdRow memInThird)

end EffectRow

/-! ## Built-in subeffect chain -/

/-- The canonical witness for read availability under a write-capable row. -/
theorem read_subset_writeRead :
    EffectRow.subset
      (EffectRow.singleton EffectLabel.read)
      (EffectLabel.write :: EffectLabel.read :: EffectRow.empty) := by
  intro _ memInRead
  cases memInRead with
  | head _ =>
    exact EffectRow.Member.tail EffectLabel.write
      (EffectRow.Member.head EffectRow.empty)
  | tail _ memInEmpty => cases memInEmpty

/-! ## Operation signatures and permission -/

/-- A row-level effect operation signature. -/
structure OperationSignature (PayloadType : Type payloadLevel) :
    Type payloadLevel where
  /-- The effect capability required by this operation. -/
  effectLabel : EffectLabel
  /-- The carrier expected by the operation argument. -/
  argumentCarrier : PayloadType
  /-- The carrier produced by the operation result. -/
  resultCarrier : PayloadType

namespace OperationSignature

/-- Map the payload carriers of an operation signature while preserving its
effect label. -/
def map {SourcePayload : Type sourcePayloadLevel}
    {TargetPayload : Type targetPayloadLevel}
    (payloadMap : SourcePayload → TargetPayload)
    (operation : OperationSignature SourcePayload) :
    OperationSignature TargetPayload where
  effectLabel := operation.effectLabel
  argumentCarrier := payloadMap operation.argumentCarrier
  resultCarrier := payloadMap operation.resultCarrier

end OperationSignature

/-- Evidence that an effect row permits an operation. -/
inductive CanPerform {PayloadType : Type payloadLevel}
    (availableRow : EffectRow) :
    OperationSignature PayloadType → Prop where
  /-- The row directly contains the operation's required label. -/
  | direct {operation : OperationSignature PayloadType} :
      EffectRow.Member operation.effectLabel availableRow →
      CanPerform availableRow operation
  /-- A write-capable row may perform read operations. -/
  | readViaWrite
      (argumentCarrier resultCarrier : PayloadType) :
      EffectRow.Member EffectLabel.write availableRow →
      CanPerform availableRow
        { effectLabel := EffectLabel.read
          argumentCarrier := argumentCarrier
          resultCarrier := resultCarrier }

namespace CanPerform

/-- Transport operation-permission evidence across a payload-carrier map. -/
def map {SourcePayload : Type sourcePayloadLevel}
    {TargetPayload : Type targetPayloadLevel}
    {availableRow : EffectRow}
    {operation : OperationSignature SourcePayload}
    (payloadMap : SourcePayload → TargetPayload) :
    CanPerform availableRow operation →
      CanPerform availableRow (operation.map payloadMap)
  | .direct rowMember => .direct rowMember
  | .readViaWrite argumentCarrier resultCarrier rowMember =>
      .readViaWrite (payloadMap argumentCarrier)
        (payloadMap resultCarrier) rowMember

/-- Operation permission is monotone in the effect row preorder. -/
theorem mono
    {PayloadType : Type payloadLevel}
    {firstRow secondRow : EffectRow}
    {operation : OperationSignature PayloadType}
    (rowSubset : EffectRow.subset firstRow secondRow)
    (canPerformInFirst : CanPerform firstRow operation) :
    CanPerform secondRow operation := by
  cases canPerformInFirst with
  | direct memberProof =>
      exact CanPerform.direct (rowSubset _ memberProof)
  | readViaWrite argumentCarrier resultCarrier writeMember =>
      exact CanPerform.readViaWrite argumentCarrier resultCarrier
        (rowSubset _ writeMember)

/-- An operation allowed by the left row is allowed by the joined row. -/
theorem join_left
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {operation : OperationSignature PayloadType}
    (canPerformInFirst : CanPerform firstRow operation) :
    CanPerform (EffectRow.join firstRow secondRow) operation :=
  mono (EffectRow.join_subset_left firstRow secondRow) canPerformInFirst

/-- An operation allowed by the right row is allowed by the joined row. -/
theorem join_right
    {PayloadType : Type payloadLevel}
    (firstRow secondRow : EffectRow)
    {operation : OperationSignature PayloadType}
    (canPerformInSecond : CanPerform secondRow operation) :
    CanPerform (EffectRow.join firstRow secondRow) operation :=
  mono (EffectRow.join_subset_right firstRow secondRow) canPerformInSecond

end CanPerform

/-! ## Smoke samples -/

/-- The IO row contains the IO label. -/
example :
    EffectRow.Member EffectLabel.io
        (EffectRow.singleton EffectLabel.io) :=
  EffectRow.Member.head []

/-- The empty row is a subset of every row. -/
example (someRow : EffectRow) :
    EffectRow.subset EffectRow.empty someRow :=
  EffectRow.empty_subset someRow

/-- Joining IO and Alloc gives a row containing Alloc. -/
example :
    EffectRow.Member EffectLabel.alloc
        (EffectRow.join (EffectRow.singleton EffectLabel.io)
                        (EffectRow.singleton EffectLabel.alloc)) :=
  EffectRow.member_append_right [EffectLabel.io] _
    (EffectRow.Member.head [])

end LeanFX2.Effects
