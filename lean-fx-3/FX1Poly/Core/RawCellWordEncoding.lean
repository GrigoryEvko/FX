import FX1Poly.Core.RawCell

/-! # FX1Poly/Core/RawCellWordEncoding
    — the dim-1 free-monoid rule-word encoding of the RawCell composite layer

The Leg-3 (Makkai/Forest) word-problem route decides FX `Conv` as word equality in the free omega-category
over a generating polygraph (polycell.md §2.3 / §3.9).  The OmegacE toy polygraphs demonstrate the decision on
concrete systems; `GeneratorFinitePolygraph` presents the FX kernel's 194 term-formers as a finite polygraph.  This file starts
the ACTUAL FX-Conv-to-word bridge: it encodes the `RawCell` composite layer into the free monoid of its
generating-cell rule ids — the dimension-1 free monoid whose letters are the FX REWRITE RULES.

## Why the rule-id free monoid, not `OmegacEWord`

The abstract scaffold `OmegacECell` (`OmegacEAt.lean`) has exactly two generators per dimension (the walking
equivalence) — the wrong alphabet for FX.  The faithful dim-1 free monoid here is over the FX rewrite-rule
alphabet: a `RawCell.generatingCell` carries a `ruleId : Nat` naming the FX reduction it instantiates, and these
generating cells ARE the dim-1 (and higher) generators of the REWRITING polygraph — distinct from the
194 term-FORMERS (the term polygraph).  So the word of a cell is the ordered sequence of rule ids in its
composite expression — exactly a reduction-path word, which is what the `Conv`-to-word problem ranges over.

`OmegacEWord dimension = {cells : List (OmegacECell dimension)}` is the free monoid on the scaffold alphabet;
this file uses `List Nat` — the free monoid on the rule-id alphabet — with the SAME `(++, [], assoc, unit)`
monoid structure (the laws reproved locally, propext-free, as in `WordFreeMonoid.lean`).

## What is proved

* `RawCell.encodeRuleWord` — the encoding: `termBase`/`identityCell` to the empty word (`[]`, the unit),
  `generatingCell ruleId _ _` to the one-letter word `[ruleId]`, and both composites to `++` (concatenation).
* `encodeRuleWord_{termBase,generatingCell,verticalComposite,horizontalComposite,identityCell}` — the
  per-constructor computation rules (all `rfl`).
* `encodeRuleWord_assoc` — the encoding RESPECTS reassociation of horizontal composition (the free-monoid
  associative law, via `listAppendAssocLocal`).
* `encodeRuleWord_identity_left` / `_right` — `identityCell` is a two-sided unit under the encoding (left by
  `rfl`, right via `listAppendNilLocal`).  Together with `_assoc` this is the MONOID HOMOMORPHISM: the RawCell
  composite structure maps homomorphically onto the dim-1 free monoid, with `identityCell` to the unit.
* `RawCell.generatingCellCount` + `encodeRuleWord_length_eq_generatingCellCount` — FAITHFULNESS to the
  generating-cell content: the word length equals the number of generating-cell leaves (a real structural
  induction, so the encoding is not collapsing the rewrite content).

This is the lift of the dim-1 free monoid to dim-2 cells.  `StepRewriteRuleMap` maps each `generatingCell`'s
source/target (themselves cells, recovered by `encodeRuleWord`) to a rewrite RULE `source-word ⇒ target-word`;
the bridge soundness `Step a b ⟹ RewritesOneStep` is gated on typed SN per `core_raw_sn_false_natrec`
(raw `Step` is not globally terminating).  Here we build only the encoding and its monoid/faithfulness laws.

## Zero-axiom verification

`encodeRuleWord` / `generatingCellCount` are structural recursions over `RawCell` (uniform scope index), so the
per-constructor rules are `rfl`.  The monoid laws reduce to list `++` associativity / right-identity, proved by
structural induction (`listAppendAssocLocal` / `listAppendNilLocal`) rather than core `List.append_assoc` /
`List.append_nil` (which carry `propext` in this Init-only setting); the length invariant uses a local
`listLengthAppendLocal` with explicit `Nat.zero_add` / `Nat.add_right_comm`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- List-append associativity by structural induction — propext-free, unlike core `List.append_assoc`. -/
private theorem listAppendAssocLocal {elementType : Type _}
    (firstList secondList thirdList : List elementType) :
    (firstList ++ secondList) ++ thirdList = firstList ++ (secondList ++ thirdList) := by
  induction firstList with
  | nil => rfl
  | cons head _tail inductionHypothesis => exact congrArg (List.cons head) inductionHypothesis

/-- List-append right identity by structural induction — propext-free, unlike core `List.append_nil`. -/
private theorem listAppendNilLocal {elementType : Type _} (listValue : List elementType) :
    listValue ++ [] = listValue := by
  induction listValue with
  | nil => rfl
  | cons head _tail inductionHypothesis => exact congrArg (List.cons head) inductionHypothesis

/-- List-append length distribution by structural induction — propext-free, unlike core
`List.length_append`.  The cons step closes by `Nat.add_right_comm` (moving the `+1` past `secondList.length`). -/
private theorem listLengthAppendLocal {elementType : Type _}
    (firstList secondList : List elementType) :
    (firstList ++ secondList).length = firstList.length + secondList.length := by
  induction firstList with
  | nil => exact (Nat.zero_add secondList.length).symm
  | cons _head tail inductionHypothesis =>
      show (tail ++ secondList).length + 1 = (tail.length + 1) + secondList.length
      rw [inductionHypothesis, Nat.add_right_comm]

/-- The dim-1 **rule word** of a cell: the ordered sequence of generating-cell rule ids in its composite
expression.  Objects (`termBase`) and identities (`identityCell`) contribute the empty word (the monoid unit);
a `generatingCell` contributes the one-letter word of its rule id; the composites concatenate.  The
generating cell's source/target boundaries are NOT descended into — they are the (lower-dimensional) boundary
of the rule, handled separately by the `StepRewriteRuleMap` rule map. -/
def RawCell.encodeRuleWord {scope : Nat} : RawCell scope → List Nat
  | .termBase _ => []
  | .generatingCell ruleId _ _ => [ruleId]
  | .verticalComposite first second => first.encodeRuleWord ++ second.encodeRuleWord
  | .horizontalComposite left right => left.encodeRuleWord ++ right.encodeRuleWord
  | .identityCell _ => []

/-- An object cell carries the empty rule word. -/
theorem encodeRuleWord_termBase {scope : Nat} (term : RawTerm scope) :
    (RawCell.termBase term).encodeRuleWord = [] := rfl

/-- A generating cell carries the one-letter word of its rule id. -/
theorem encodeRuleWord_generatingCell {scope : Nat}
    (ruleId : Nat) (source target : RawCell scope) :
    (RawCell.generatingCell ruleId source target).encodeRuleWord = [ruleId] := rfl

/-- Vertical composition maps to word concatenation (the multiplication half of the homomorphism). -/
theorem encodeRuleWord_verticalComposite {scope : Nat} (first second : RawCell scope) :
    (RawCell.verticalComposite first second).encodeRuleWord
      = first.encodeRuleWord ++ second.encodeRuleWord := rfl

/-- Horizontal composition maps to word concatenation (the multiplication half of the homomorphism). -/
theorem encodeRuleWord_horizontalComposite {scope : Nat} (left right : RawCell scope) :
    (RawCell.horizontalComposite left right).encodeRuleWord
      = left.encodeRuleWord ++ right.encodeRuleWord := rfl

/-- An identity cell carries the empty rule word (the monoid unit). -/
theorem encodeRuleWord_identityCell {scope : Nat} (base : RawCell scope) :
    (RawCell.identityCell base).encodeRuleWord = [] := rfl

/-- **The encoding respects associativity** of horizontal composition: reassociating the composite leaves the
rule word unchanged (the free monoid's associative law witnessed by the encoding). -/
theorem encodeRuleWord_assoc {scope : Nat} (firstCell secondCell thirdCell : RawCell scope) :
    (RawCell.horizontalComposite
        (RawCell.horizontalComposite firstCell secondCell) thirdCell).encodeRuleWord
      = (RawCell.horizontalComposite
          firstCell (RawCell.horizontalComposite secondCell thirdCell)).encodeRuleWord :=
  listAppendAssocLocal firstCell.encodeRuleWord secondCell.encodeRuleWord thirdCell.encodeRuleWord

/-- **Left unit**: composing an identity on the left leaves the rule word unchanged (`[] ++ word = word`). -/
theorem encodeRuleWord_identity_left {scope : Nat} (base inner : RawCell scope) :
    (RawCell.horizontalComposite (RawCell.identityCell base) inner).encodeRuleWord
      = inner.encodeRuleWord := rfl

/-- **Right unit**: composing an identity on the right leaves the rule word unchanged (`word ++ [] = word`). -/
theorem encodeRuleWord_identity_right {scope : Nat} (inner base : RawCell scope) :
    (RawCell.horizontalComposite inner (RawCell.identityCell base)).encodeRuleWord
      = inner.encodeRuleWord :=
  listAppendNilLocal inner.encodeRuleWord

/-- The number of generating-cell leaves in a cell's composite expression (matching `encodeRuleWord`: objects
and identities contribute 0, a generating cell contributes 1, composites sum). -/
def RawCell.generatingCellCount {scope : Nat} : RawCell scope → Nat
  | .termBase _ => 0
  | .generatingCell _ _ _ => 1
  | .verticalComposite first second => first.generatingCellCount + second.generatingCellCount
  | .horizontalComposite left right => left.generatingCellCount + right.generatingCellCount
  | .identityCell _ => 0

/-- **Faithfulness to generating-cell content**: the rule word's length equals the number of generating-cell
leaves — the encoding loses no rewrite content beyond the (separately tracked) boundaries. -/
theorem encodeRuleWord_length_eq_generatingCellCount {scope : Nat} (cell : RawCell scope) :
    cell.encodeRuleWord.length = cell.generatingCellCount := by
  induction cell with
  | termBase _ => rfl
  | generatingCell _ _ _ _ _ => rfl
  | verticalComposite first second firstIH secondIH =>
      show (first.encodeRuleWord ++ second.encodeRuleWord).length
        = first.generatingCellCount + second.generatingCellCount
      rw [listLengthAppendLocal, firstIH, secondIH]
  | horizontalComposite left right leftIH rightIH =>
      show (left.encodeRuleWord ++ right.encodeRuleWord).length
        = left.generatingCellCount + right.generatingCellCount
      rw [listLengthAppendLocal, leftIH, rightIH]
  | identityCell _ _ => rfl

end FX1Poly.Core
