/-! # Effects/Foundation — effect labels, rows, and subset preorder

Per `fx_design.md` §9: FX's effect system is a bounded join-
semilattice `(Effects, ⊔, Tot)` where `Tot` is the identity
(empty effect) and `⊔` is row union.  The only built-in
subeffect chain is `Read ≤ Write` — every other built-in is
an incomparable lattice element.

## What ships (Phase 12.A.6 — Effects layer foundation)

* `EffectLabel` — closed enum of nine built-in effects (Tot,
  Div, Ghost, Exn, IO, Alloc, Read, Write, Async)
* `EffectRow` — list-based encoding with set-membership
  semantics
* `Member` — custom inductive membership predicate (avoids
  any stdlib `List.mem_append_*` lemmas that might leak
  propext)
* `subset` — preorder lifting list membership
* `join` — list union (the lattice's `⊔`)
* Algebraic laws: subset reflexivity / transitivity, empty is
  bottom, join is the least upper bound, idempotency,
  commutativity, associativity (all up to mutual subset)
* `read_subset_writeRead` — the only built-in subeffect chain

## What defers (later phases)

* `Op` (operation signatures) and `effectPerform` /
  `effectHandle` — depend on Term-level integration (Layer
  K, kernel side); deferred to Phase 13+
* User-defined effects (`effect ... end effect`) — surface
  syntax + elaboration in Phase 14+
* Effect handlers with one-shot vs multi-shot continuations
  (§9.7) — needs delimited-continuation infrastructure
* Per-platform effect availability (§9.10 platform-conditional
  effects) — needs target backend integration

Zero-axiom verified per declaration. -/

namespace LeanFX2.Effects

/-! ## Effect labels

The nine built-in effect labels per `fx_design.md` §9.4.  Closed
enum: every `EffectLabel` is one of these; user-defined effects
attach via the surface elaborator (deferred). -/

/-- Built-in effect labels.  Per §9.4:

* `tot` — pure terminating (the default empty effect)
* `div` — may diverge (non-terminating)
* `ghost` — erased at runtime, checked at compile time
* `exn` — may raise exceptions
* `io` — general input/output
* `alloc` — may allocate heap
* `read` — may read from references / state
* `write` — may write (implies read; see `read_subset_writeRead`)
* `async` — async operations -/
inductive EffectLabel : Type
  /-- Pure terminating (default empty effect). -/
  | tot
  /-- May diverge. -/
  | div
  /-- Erased at runtime, checked at compile time. -/
  | ghost
  /-- May raise exceptions. -/
  | exn
  /-- General input/output. -/
  | io
  /-- May allocate heap memory. -/
  | alloc
  /-- May read from references / state. -/
  | read
  /-- May write (implies read). -/
  | write
  /-- Asynchronous operations. -/
  | async
  deriving DecidableEq, Repr

/-! ## Effect rows

An `EffectRow` is a list of effect labels with set-membership
semantics — order and multiplicity are irrelevant when checking
subset, but encoding as `List` keeps reductions definitional. -/

/-- Effect rows are lists of labels.  Set-semantics is enforced
by the `subset` relation, not by deduplication. -/
abbrev EffectRow := List EffectLabel

namespace EffectRow

/-- The empty effect row corresponds to `Tot` (the lattice
bottom).  An expression with row `empty` performs no effects. -/
def empty : EffectRow := []

/-- A singleton effect row containing exactly one label. -/
def singleton (someLabel : EffectLabel) : EffectRow :=
  [someLabel]

/-! ## Custom membership predicate

We avoid stdlib's `List.Mem` + `List.mem_append_*` lemma chain
to stay 100% clear of any propext / Quot.sound leaks lurking in
stdlib derivations.  Our `Member` is a plain inductive `Prop`
with explicit `head` / `tail` constructors. -/

/-- `Member someLabel someRow` asserts that `someLabel` appears
somewhere in `someRow`.  Custom inductive instead of the
default `Membership` instance to control the proof surface.
`someLabel` is a parameter (not an index) so cases-split arities
are minimal — head takes 1 fresh name, tail takes 2. -/
inductive Member (someLabel : EffectLabel) : EffectRow → Prop
  /-- The label is at the head of the row. -/
  | head (restRow : EffectRow) :
      Member someLabel (someLabel :: restRow)
  /-- The label is in the tail (cons more in front). -/
  | tail (otherLabel : EffectLabel) {restRow : EffectRow}
      (alreadyIn : Member someLabel restRow) :
      Member someLabel (otherLabel :: restRow)

/-! ## Subset preorder

`subset firstRow secondRow` holds when every label in
`firstRow` also appears in `secondRow`.  This is the lattice
preorder. -/

/-- The subset relation: every label of `firstRow` is a member
of `secondRow`. -/
def subset (firstRow secondRow : EffectRow) : Prop :=
  ∀ (someLabel : EffectLabel),
    Member someLabel firstRow → Member someLabel secondRow

/-! ## Join (least upper bound)

Join is plain list append; deduplication is a representational
detail handled by the subset preorder. -/

/-- Join two effect rows.  Implementation: list append; the
subset preorder handles deduplication semantically. -/
def join (firstRow secondRow : EffectRow) : EffectRow :=
  firstRow ++ secondRow

/-! ## Membership lemmas

Hand-rolled by structural induction to avoid stdlib's lemma
chain. -/

/-- Members of the left operand stay members after appending. -/
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

/-- Members of the right operand stay members after prepending. -/
theorem member_append_right
    {someLabel : EffectLabel}
    (firstRow secondRow : EffectRow)
    (memInSecond : Member someLabel secondRow) :
    Member someLabel (firstRow ++ secondRow) := by
  induction firstRow with
  | nil => exact memInSecond
  | cons headLabel _ innerHypothesis =>
    exact Member.tail headLabel innerHypothesis

/-- A member of an appended row came from one of the two
operands.  Inverse to `member_append_left` / `_right`. -/
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

/-! ## Subset preorder laws -/

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

/-- Empty (Tot) is the bottom of the lattice — subset of every
row. -/
theorem empty_subset (someRow : EffectRow) : subset empty someRow := by
  intro someLabel memInEmpty
  cases memInEmpty

/-! ## Join laws -/

/-- The left operand is a subset of the join. -/
theorem join_subset_left (firstRow secondRow : EffectRow) :
    subset firstRow (join firstRow secondRow) :=
  fun _ memInFirst => member_append_left firstRow secondRow memInFirst

/-- The right operand is a subset of the join. -/
theorem join_subset_right (firstRow secondRow : EffectRow) :
    subset secondRow (join firstRow secondRow) :=
  fun _ memInSecond => member_append_right firstRow secondRow memInSecond

/-- The join is the least upper bound: any row that contains
both operands as subsets contains the join. -/
theorem join_least_upper_bound
    {firstRow secondRow thirdRow : EffectRow}
    (firstSubset : subset firstRow thirdRow)
    (secondSubset : subset secondRow thirdRow) :
    subset (join firstRow secondRow) thirdRow := by
  intro someLabel memInJoin
  cases member_append_inv firstRow secondRow memInJoin with
  | inl memInFirst => exact firstSubset someLabel memInFirst
  | inr memInSecond => exact secondSubset someLabel memInSecond

/-- Join is idempotent up to subset: `row ⊔ row ⊑ row`. -/
theorem join_idempotent_subset (someRow : EffectRow) :
    subset (join someRow someRow) someRow := by
  intro someLabel memInJoin
  cases member_append_inv someRow someRow memInJoin with
  | inl memInLeft => exact memInLeft
  | inr memInRight => exact memInRight

/-- Join commutes up to subset: `firstRow ⊔ secondRow ⊑
secondRow ⊔ firstRow`. -/
theorem join_commutes_subset
    (firstRow secondRow : EffectRow) :
    subset (join firstRow secondRow) (join secondRow firstRow) := by
  intro someLabel memInJoin
  cases member_append_inv firstRow secondRow memInJoin with
  | inl memInFirst =>
    exact member_append_right secondRow firstRow memInFirst
  | inr memInSecond =>
    exact member_append_left secondRow firstRow memInSecond

/-- Join associates up to subset: `(firstRow ⊔ secondRow) ⊔
thirdRow ⊑ firstRow ⊔ (secondRow ⊔ thirdRow)`. -/
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

/-! ## Built-in subeffect chain: Read ≤ Write

Per `fx_design.md` §9.3, `Read ≤ Write` is the only built-in
subeffect chain.  Encoded here as: a row containing `read`
alone is a subset of a row containing `write` together with
`read` (the canonical "Write subsumes Read" closure). -/

/-- The Read-below-Write subeffect chain.  A function declared
`with Write` semantically also has `Read` available; we
witness this with the row `[write, read]` containing `read`
as a subset of `[read]`. -/
theorem read_subset_writeRead :
    EffectRow.subset
      (EffectRow.singleton EffectLabel.read)
      (EffectLabel.write :: EffectLabel.read :: EffectRow.empty) := by
  intro someLabel memInRead
  cases memInRead with
  | head _ =>
    exact EffectRow.Member.tail EffectLabel.write
      (EffectRow.Member.head EffectRow.empty)
  | tail _ memInEmpty => cases memInEmpty

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

/-- Joining IO and Alloc gives a row containing both. -/
example :
    EffectRow.Member EffectLabel.alloc
        (EffectRow.join (EffectRow.singleton EffectLabel.io)
                        (EffectRow.singleton EffectLabel.alloc)) :=
  EffectRow.member_append_right [EffectLabel.io] _
    (EffectRow.Member.head [])

end LeanFX2.Effects
