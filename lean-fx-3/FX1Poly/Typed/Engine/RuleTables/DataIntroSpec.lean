import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables

/-! # FX1Poly/Typed/DataIntroSpec — TYTAB-1 brick 3 (arm collapse): unified data-intro descriptors

The data-intro family of `HasTypeUnionOver` shipped as eight per-family arms.  The census
(reconnaissance) showed these are NOT all uniform — they split by the Lean strict-positivity wall:

  * The RECURSIVE intros (`recursiveUnaryIntro` = natSucc, `recursiveBinaryIntro` = listCons) carry a
    premise typed in the UNION ITSELF.  That recursive premise MUST stay explicit in the arm (a
    data-driven premise descriptor would hide the union under an opaque function, defeating the
    positivity checker).  But everything ELSE the two arms differ in — whether a grown head precedes
    the recursive child, the recursive child's classifier, the member cell, the output container — is
    first-order DATA.  So the two arms collapse to ONE generic `recursiveDataIntro` arm reading a
    `RecursiveDataIntroSpec`, with the union premise kept explicit and the variation in the descriptor.

This module is the descriptor + the two instances + the lookup table.  The generic arm (in
`HasTypeUnion.lean`) and the companion re-proofs follow.  A `natSucc`/`listCons`-shaped former is now a
descriptor row, not an arm.

Zero-axiom: a record, two `def` instances, an `if`-chain table, and a propext-clean `_cases` inverter
(the `by_cases` + `Option.some.inj` idiom the sibling `native*RuleOf_cases` lemmas use). -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ★ **The unified recursive-data-intro descriptor.**  Subsumes the `natSucc` (no head) and `listCons`
(grown head) shapes: one union-recursive child (kept explicit in the arm for positivity), an optional
grown head before it, and the first-order data — recursive child's classifier, member cell, output
container — all functions of the (possibly-phantom) element type. -/
structure RecursiveDataIntroSpec where
  /-- Whether a GROWN head child precedes the recursive child (`listCons` yes, `natSucc` no). -/
  hasGrownHead : Bool
  /-- The classifier the union-recursive child must inhabit, as a function of the element type.
  (`natSucc`: the constant `Nat`; `listCons`: `List(elementType)`.) -/
  recursiveChildType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The member cell built from the (possibly-phantom) grown head and the recursive child.
  (`natSucc`: ignores the head, `natSucc child`; `listCons`: `cons head tail`.) -/
  memberCell : (scope : Nat) → (head recursiveChild : RawTerm scope) → RawTerm scope
  /-- The output container type, as a function of the element type.  (`natSucc`: constant `Nat`;
  `listCons`: `List(elementType)`.) -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm scope

/-- The `gen_natSucc` recursive-data-intro row: no grown head; the recursive child and output are both
the constant `Nat`; the member ignores the phantom head and wraps the child in `natSucc`. -/
def natSuccRecursiveDataIntroSpec : RecursiveDataIntroSpec where
  hasGrownHead := false
  recursiveChildType := fun _ _ => natTypeCell
  memberCell := fun _ _ recursiveChild => natSuccCell recursiveChild
  outputType := fun _ _ => natTypeCell

/-- The `gen_listCons` recursive-data-intro row: a grown head at the element type, the recursive tail
at `List(elementType)`, the member `cons head tail`, the output `List(elementType)`. -/
def listConsRecursiveDataIntroSpec : RecursiveDataIntroSpec where
  hasGrownHead := true
  recursiveChildType := fun _ elementType => listTypeCell elementType
  memberCell := fun _ head recursiveChild => listConsCell head recursiveChild
  outputType := fun _ elementType => listTypeCell elementType

/-- The unified recursive-data-intro table: `natSucc` and `listCons` rows. -/
def recursiveDataIntroSpecOf (generator : Generator) : Option RecursiveDataIntroSpec :=
  if generator = .gen_natSucc then some natSuccRecursiveDataIntroSpec
  else if generator = .gen_listCons then some listConsRecursiveDataIntroSpec
  else none

/-- Table metadata: the `natSucc` row is hit. -/
theorem recursiveDataIntroSpecOf_natSucc :
    recursiveDataIntroSpecOf .gen_natSucc = some natSuccRecursiveDataIntroSpec := rfl

/-- Table metadata: the `listCons` row is hit. -/
theorem recursiveDataIntroSpecOf_listCons :
    recursiveDataIntroSpecOf .gen_listCons = some listConsRecursiveDataIntroSpec := rfl

/-- **A recursive-data-intro table hit pins one of the two rows.**  The propext-clean inverter feeding
the generic arm's companion re-proofs: every Mode-A transport case and Mode-B inversion stub recovers
the concrete generator/spec from this. -/
theorem recursiveDataIntroSpecOf_cases {generator : Generator} {spec : RecursiveDataIntroSpec}
    (tableHit : recursiveDataIntroSpecOf generator = some spec) :
    (generator = .gen_natSucc ∧ spec = natSuccRecursiveDataIntroSpec) ∨
    (generator = .gen_listCons ∧ spec = listConsRecursiveDataIntroSpec) := by
  unfold recursiveDataIntroSpecOf at tableHit
  by_cases isNatSucc : generator = .gen_natSucc
  · rw [if_pos isNatSucc] at tableHit
    exact Or.inl ⟨isNatSucc, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isNatSucc] at tableHit
    by_cases isListCons : generator = .gen_listCons
    · rw [if_pos isListCons] at tableHit
      exact Or.inr ⟨isListCons, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isListCons] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

end FX1Poly.Typed
