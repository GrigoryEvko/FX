/-! # FX1Poly/Core/MultisetOrder
    — the Dershowitz-Manna multiset ordering and its well-foundedness

The Dershowitz-Manna multiset order is the foundational well-founded termination order: a multiset shrinks when
one element is replaced by finitely many strictly-smaller ones.  It is the order RPO uses for multiset-status
function symbols and the natural measure for ι-eliminator termination (a recursor on a constructor
replaces the redex by sub-computations on smaller arguments — the certified-fragment termination).

This file mechanizes it from scratch over `Init` only, ZERO-AXIOM.  A true multiset is the quotient of `List` by
permutation, but `Quot.sound` is banned under the zero-axiom policy — so the order is formulated as an
EXISTENTIAL relation on plain `List` (no quotient): `MultisetRedOne baseRel small big` holds when `big` splits as
`prefix ++ removed :: suffix` and `small` is `prefix ++ added ++ suffix` with every `added` element
`baseRel`-below `removed`.  Working on `List` rather than the quotient keeps the relation propext-free; the order
is permutation-aware in effect because `prefix`/`suffix` may place the replaced element anywhere.

## The Dershowitz-Manna theorem

`MultisetRedOne.isWellFounded` : `WellFounded baseRel → WellFounded (MultisetRedOne baseRel)`.  The classic
nested-accessibility proof (Nipkow's inductive argument): the empty list is accessible (no predecessors); and
prepending an `Acc baseRel` head to an `Acc (MultisetRedOne baseRel)` tail stays accessible, by induction on the
head's `baseRel`-accessibility (outer) and the tail's multiset-accessibility (inner), with an inner helper that
appending strictly-below elements preserves accessibility.

## What is proved

* `MultisetRedOne` — the single-step multiset reduction relation (existential on `List`).
* `MultisetRedOne.replaceHead` / `underContext` — introduction lemmas (replace the head by smaller elements;
  take a step under a kept context head) so the order is constructible.
* `MultisetRedOne.emptyAccessible` — `[]` is accessible (no predecessors).
* `MultisetRedOne.consAccessible` — the crux: `Acc baseRel head → Acc (MultisetRedOne baseRel) tail →
  Acc (MultisetRedOne baseRel) (head :: tail)`.
* `MultisetRedOne.isWellFounded` — the Dershowitz-Manna theorem.

## Zero-axiom verification

The relation is a plain `∃`; inversion is `obtain` + `cases prefixList` (a clean `List` split, NOT an
indexed-inductive `cases` — so no propext leak); `List.cons.inj` / `List.Mem.head` / `List.Mem.tail` /
`List.cons_ne_nil` are propext-free; the `List.nil_append` / `List.cons_append` rewrites are `rfl`-lemmas.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Elem : Type carrierUniverse}

/-- **Dershowitz-Manna single step** on lists (no quotient): `smallList` is obtained from `bigList` by replacing
one element `removed` (at some position `prefixList ++ removed :: suffixList`) with a list `addedList` of
elements all strictly `baseRel`-below `removed`. -/
def MultisetRedOne (baseRel : Elem → Elem → Prop)
    (smallList bigList : List Elem) : Prop :=
  ∃ (removed : Elem) (prefixList suffixList addedList : List Elem),
    bigList = prefixList ++ removed :: suffixList
      ∧ smallList = prefixList ++ addedList ++ suffixList
      ∧ ∀ x, x ∈ addedList → baseRel x removed

/-- Introduction: replace the head element by a list of strictly-smaller ones. -/
theorem MultisetRedOne.replaceHead (baseRel : Elem → Elem → Prop)
    (removed : Elem) (addedList restList : List Elem)
    (smaller : ∀ x, x ∈ addedList → baseRel x removed) :
    MultisetRedOne baseRel (addedList ++ restList) (removed :: restList) :=
  ⟨removed, [], restList, addedList, rfl, rfl, smaller⟩

/-- Introduction: a multiset step under a kept context head. -/
theorem MultisetRedOne.underContext (baseRel : Elem → Elem → Prop)
    (keep : Elem) {smallList bigList : List Elem}
    (inner : MultisetRedOne baseRel smallList bigList) :
    MultisetRedOne baseRel (keep :: smallList) (keep :: bigList) := by
  obtain ⟨removed, prefixList, suffixList, addedList, bigEq, smallEq, smaller⟩ := inner
  refine ⟨removed, keep :: prefixList, suffixList, addedList, ?_, ?_, smaller⟩
  · rw [bigEq]; rfl
  · rw [smallEq]; rfl

/-- The empty list has no `MultisetRedOne` predecessor, hence is accessible. -/
theorem MultisetRedOne.emptyAccessible (baseRel : Elem → Elem → Prop) :
    Acc (MultisetRedOne baseRel) [] := by
  apply Acc.intro
  intro candidate step
  obtain ⟨_removed, prefixList, _suffixList, _addedList, bigEq, _, _⟩ := step
  cases prefixList with
  | nil => exact absurd bigEq.symm (List.cons_ne_nil _ _)
  | cons _ _ => exact absurd bigEq.symm (List.cons_ne_nil _ _)

/-- **The crux**: prepending a `baseRel`-accessible head to a multiset-accessible tail stays multiset-accessible.
Nested induction on the head's `baseRel`-accessibility (outer) and the tail's accessibility (inner); the inner
helper `accAppendBelow` appends strictly-below elements while preserving accessibility (consuming the outer IH). -/
theorem MultisetRedOne.consAccessible (baseRel : Elem → Elem → Prop) (headElem : Elem)
    (accHead : Acc baseRel headElem) :
    ∀ tailList : List Elem, Acc (MultisetRedOne baseRel) tailList →
      Acc (MultisetRedOne baseRel) (headElem :: tailList) := by
  induction accHead with
  | intro headElem _accHeadPred ihHead =>
    intro tailList accTail
    induction accTail with
    | intro tailList accTailPred ihTail =>
      have accAppendBelow : ∀ (addedList : List Elem),
          (∀ x, x ∈ addedList → baseRel x headElem) →
          Acc (MultisetRedOne baseRel) (addedList ++ tailList) := by
        intro addedList
        induction addedList with
        | nil => intro _; exact Acc.intro tailList accTailPred
        | cons headAdd tailAdd ihAdd =>
            intro allSmaller
            exact ihHead headAdd (allSmaller headAdd (List.Mem.head _))
              (tailAdd ++ tailList)
              (ihAdd (fun x hx => allSmaller x (List.Mem.tail _ hx)))
      apply Acc.intro
      intro candidate step
      obtain ⟨removed, prefixList, suffixList, addedList, bigEq, smallEq, smaller⟩ := step
      cases prefixList with
      | nil =>
          simp only [List.nil_append] at bigEq smallEq
          obtain ⟨removedEq, suffixEq⟩ := List.cons.inj bigEq
          subst removedEq; subst suffixEq; subst smallEq
          exact accAppendBelow addedList smaller
      | cons prefixHead prefixTail =>
          simp only [List.cons_append] at bigEq smallEq
          obtain ⟨headEq, tailEq⟩ := List.cons.inj bigEq
          subst headEq; subst tailEq; subst smallEq
          exact ihTail (prefixTail ++ addedList ++ suffixList)
            ⟨removed, prefixTail, suffixList, addedList, rfl, rfl, smaller⟩

/-- **The Dershowitz-Manna theorem**: the multiset order over a well-founded base order is well-founded. -/
theorem MultisetRedOne.isWellFounded (baseRel : Elem → Elem → Prop)
    (baseWellFounded : WellFounded baseRel) :
    WellFounded (MultisetRedOne baseRel) := by
  apply WellFounded.intro
  intro listValue
  induction listValue with
  | nil => exact MultisetRedOne.emptyAccessible baseRel
  | cons headElem tailList ihTail =>
      exact MultisetRedOne.consAccessible baseRel headElem
        (baseWellFounded.apply headElem) tailList ihTail

end FX1Poly.Core
