import FX1Poly.Core.MultisetOrder

/-! # FX1Poly/Core/TerminationOrders
    — the lexicographic list order + measure-based termination certificates

Companion to the Dershowitz-Manna multiset order.  This file adds the other classical argument-comparison
order — the LEXICOGRAPHIC order on equal-length lists, with its well-foundedness — and the measure-based
termination certificates that turn either order into a `WellFounded` proof for a step relation.

The lexicographic order is the comparison LPO uses for its arguments ("for ι-eliminator rules") and that
RPO uses for lexicographic-status symbols; the multiset order is for multiset-status symbols.
The recursive PATH ordering on the FX term structure (composing a precedence on the 194 generators with these two
comparison orders) is the larger downstream construction the FX certified-fragment termination
(typed-SN-gated) assembles — this file supplies the lex comparison order it builds on.

## What is proved

* `LexListStep` — lexicographic single step on equal-length lists (existential on `List`, no indexed inductive):
  a common prefix, then the first differing position where small's head is `baseRel`-below big's head, with
  length-matched tails.
* `LexListStep.length_eq` — lex steps preserve length (so the order is per-length).
* `LexListStep.emptyAccessible` / `consAccessible` / `accessibleByLength` / `isWellFounded` — the lexicographic
  order over a well-founded base is well-founded, by length-indexed nested accessibility.
* `wellFounded_of_multisetMeasure` / `wellFounded_of_lexMeasure` — **termination certificates**: a step relation
  whose multiset / lexicographic measure strictly decreases at every step is well-founded (terminating), via
  `InvImage.wf` of the multiset / the lex order.

## Zero-axiom verification

Same `List`-existential discipline as the multiset order: inversion by `obtain` + `cases commonPrefix` (a clean `List` split,
NOT indexed-`cases`).  Length facts use a local propext-free `listLengthAppendLocal` and rely on defeq
(`List.length_cons`); impossible-length cases use `Nat.noConfusion` DIRECTLY (NOT `absurd _ (Nat.succ_ne_zero _)`,
which leaks propext).  The measure certificates are `Subrelation.wf` + `InvImage.wf`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse elemUniverse
variable {Elem : Type elemUniverse}

/-- List-append length distribution by structural induction — propext-free (unlike core `List.length_append`). -/
private theorem listLengthAppendLocal (firstList secondList : List Elem) :
    (firstList ++ secondList).length = firstList.length + secondList.length := by
  induction firstList with
  | nil => exact (Nat.zero_add _).symm
  | cons _ tail inductionHypothesis =>
      show (tail ++ secondList).length + 1 = (tail.length + 1) + secondList.length
      rw [inductionHypothesis, Nat.add_right_comm]

/-- **Lexicographic single step** on equal-length lists (existential, no indexed inductive): a common prefix,
then the first differing position where `smallHead` is `baseRel`-below `bigHead`, with length-matched tails. -/
def LexListStep (baseRel : Elem → Elem → Prop) (smallList bigList : List Elem) : Prop :=
  ∃ (commonPrefix : List Elem) (smallHead bigHead : Elem) (smallTail bigTail : List Elem),
    bigList = commonPrefix ++ bigHead :: bigTail
      ∧ smallList = commonPrefix ++ smallHead :: smallTail
      ∧ smallTail.length = bigTail.length
      ∧ baseRel smallHead bigHead

/-- Lex steps preserve length (the order stays within a length class). -/
theorem LexListStep.length_eq (baseRel : Elem → Elem → Prop)
    {smallList bigList : List Elem} (step : LexListStep baseRel smallList bigList) :
    smallList.length = bigList.length := by
  obtain ⟨commonPrefix, _smallHead, _bigHead, smallTail, bigTail, bigEq, smallEq, tailLenEq, _⟩ := step
  subst bigEq; subst smallEq
  rw [listLengthAppendLocal, listLengthAppendLocal]
  simp only [List.length_cons]
  rw [tailLenEq]

/-- `[]` is lex-accessible (no predecessors). -/
theorem LexListStep.emptyAccessible (baseRel : Elem → Elem → Prop) :
    Acc (LexListStep baseRel) [] := by
  apply Acc.intro
  intro candidate step
  obtain ⟨commonPrefix, _, _, _, _, bigEq, _, _, _⟩ := step
  cases commonPrefix with
  | nil => exact absurd bigEq.symm (List.cons_ne_nil _ _)
  | cons _ _ => exact absurd bigEq.symm (List.cons_ne_nil _ _)

/-- Cons accessibility, given all length-`lengthN` lists are accessible (the length-IH supplies the arbitrary
length-matched tails of the head-decrease case; the inner induction handles the tail-decrease case). -/
theorem LexListStep.consAccessible (baseRel : Elem → Elem → Prop) (lengthN : Nat)
    (allLenNAccessible : ∀ t : List Elem, t.length = lengthN → Acc (LexListStep baseRel) t)
    (headElem : Elem) (accHead : Acc baseRel headElem) :
    ∀ tailList : List Elem, tailList.length = lengthN →
      Acc (LexListStep baseRel) (headElem :: tailList) := by
  induction accHead with
  | intro headElem _accHeadPred ihHead =>
    intro tailList tailLen
    have innerHelper : ∀ tail : List Elem, Acc (LexListStep baseRel) tail →
        tail.length = lengthN → Acc (LexListStep baseRel) (headElem :: tail) := by
      intro tail accTail
      induction accTail with
      | intro tail _accTailPred ihTail =>
        intro tailLenInner
        apply Acc.intro
        intro candidate step
        obtain ⟨commonPrefix, smallHead, bigHead, smallTail, bigTail,
          bigEq, smallEq, tailLenEq, headStep⟩ := step
        cases commonPrefix with
        | nil =>
            simp only [List.nil_append] at bigEq smallEq
            obtain ⟨bigHeadEq, bigTailEq⟩ := List.cons.inj bigEq
            subst bigHeadEq; subst bigTailEq; subst smallEq
            exact ihHead smallHead headStep smallTail (tailLenEq.trans tailLenInner)
        | cons prefixHead prefixTail =>
            simp only [List.cons_append] at bigEq smallEq
            obtain ⟨prefixHeadEq, tailEq⟩ := List.cons.inj bigEq
            subst prefixHeadEq; subst tailEq; subst smallEq
            refine ihTail (prefixTail ++ smallHead :: smallTail) ?_ ?_
            · exact ⟨prefixTail, smallHead, bigHead, smallTail, bigTail, rfl, rfl, tailLenEq, headStep⟩
            · exact (LexListStep.length_eq baseRel
                ⟨prefixTail, smallHead, bigHead, smallTail, bigTail, rfl, rfl, tailLenEq, headStep⟩).trans
                tailLenInner
    exact innerHelper tailList (allLenNAccessible tailList tailLen) tailLen

/-- Every list is lex-accessible, by induction on its length (lex steps preserve length, so length-`n`
predecessors are handled by the length-`n` IH). -/
theorem LexListStep.accessibleByLength (baseRel : Elem → Elem → Prop)
    (baseWellFounded : WellFounded baseRel) :
    ∀ (lengthN : Nat) (listValue : List Elem), listValue.length = lengthN →
      Acc (LexListStep baseRel) listValue := by
  intro lengthN
  induction lengthN with
  | zero =>
      intro listValue lenZero
      cases listValue with
      | nil => exact LexListStep.emptyAccessible baseRel
      | cons _ _ => exact Nat.noConfusion lenZero
  | succ predLength ihLength =>
      intro listValue lenSucc
      cases listValue with
      | nil => exact Nat.noConfusion lenSucc
      | cons headElem tailList =>
          have tailLen : tailList.length = predLength := Nat.succ.inj lenSucc
          exact LexListStep.consAccessible baseRel predLength ihLength headElem
            (baseWellFounded.apply headElem) tailList tailLen

/-- **The lexicographic order over a well-founded base is well-founded.** -/
theorem LexListStep.isWellFounded (baseRel : Elem → Elem → Prop)
    (baseWellFounded : WellFounded baseRel) :
    WellFounded (LexListStep baseRel) := by
  apply WellFounded.intro
  intro listValue
  exact LexListStep.accessibleByLength baseRel baseWellFounded listValue.length listValue rfl

variable {Carrier : Type carrierUniverse}

/-- **Termination by a multiset measure**: a step relation whose Dershowitz-Manna multiset measure strictly
decreases at every step is well-founded (terminating).  The reduction relation `target ≺ source` embeds into the
inverse image of the multiset order under the measure. -/
theorem wellFounded_of_multisetMeasure
    {stepRel : Carrier → Carrier → Prop} {measure : Carrier → List Elem}
    {baseRel : Elem → Elem → Prop}
    (baseWellFounded : WellFounded baseRel)
    (measureDecreases : ∀ source target, stepRel source target →
      MultisetRedOne baseRel (measure target) (measure source)) :
    WellFounded (fun target source => stepRel source target) := by
  apply Subrelation.wf (r := InvImage (MultisetRedOne baseRel) measure)
  · intro target source step
    exact measureDecreases source target step
  · exact InvImage.wf measure (MultisetRedOne.isWellFounded baseRel baseWellFounded)

/-- **Termination by a lexicographic measure**: a step relation whose lexicographic measure strictly decreases at
every step is well-founded (terminating). -/
theorem wellFounded_of_lexMeasure
    {stepRel : Carrier → Carrier → Prop} {measure : Carrier → List Elem}
    {baseRel : Elem → Elem → Prop}
    (baseWellFounded : WellFounded baseRel)
    (measureDecreases : ∀ source target, stepRel source target →
      LexListStep baseRel (measure target) (measure source)) :
    WellFounded (fun target source => stepRel source target) := by
  apply Subrelation.wf (r := InvImage (LexListStep baseRel) measure)
  · intro target source step
    exact measureDecreases source target step
  · exact InvImage.wf measure (LexListStep.isWellFounded baseRel baseWellFounded)

end FX1Poly.Core
