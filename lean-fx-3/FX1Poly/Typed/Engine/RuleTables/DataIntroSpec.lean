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

/-! ## The GROWN data-intro families — five arms in one fixed-slot descriptor

The five grown data-intro arms (`pinnedUnary` = optionSome, `nullaryFreeType` = optionNone / listNil,
`coproduct` = eitherInl / eitherInr, `nonDependentBinary` = pair, `reflexive` = refl) all have premises
that mention only the GROWN engine (`HasTypeDescPi`), NEVER the union being defined — so, unlike the
recursive families, their entire premise SHAPE can be carried as first-order data with no positivity
cost.  The census found their variation fits a fixed shape: at most TWO stored member children, at most
TWO existential type parameters, and an OPTIONAL grown-formedness premise (a type parameter formed at a
universe).  `refl`'s output reads the child value, so `outputType` takes the children too.  All five
collapse into ONE generic `grownDataIntro` arm reading a `GrownDataIntroSpec`. -/

/-- ★ **The unified grown-data-intro descriptor.**  Fixed-slot (≤2 member children, ≤2 type params, one
optional grown-formedness premise), every field first-order data because the premises are grown.  The
`hasChild0` / `hasChild1` / `hasFormedness` flags gate which premises the arm demands; the `*Type`
functions give each premise's classifier as a function of the type params; `memberCell` builds the cell
from the children; `outputType` builds the classifier from the children (for `refl`) and the params. -/
structure GrownDataIntroSpec where
  /-- Whether the first member child is present and grown-typed. -/
  hasChild0 : Bool
  /-- Whether the second member child is present and grown-typed (`pair` only). -/
  hasChild1 : Bool
  /-- Whether the optional grown-formedness premise is demanded (`optionNone` / `listNil` / coproduct). -/
  hasFormedness : Bool
  /-- The grown classifier of the first child, as a function of the two type params. -/
  child0Type : (scope : Nat) → (typeParam0 typeParam1 : RawTerm scope) → RawTerm scope
  /-- The grown classifier of the second child. -/
  child1Type : (scope : Nat) → (typeParam0 typeParam1 : RawTerm scope) → RawTerm scope
  /-- The term whose formedness (at a universe) is demanded, as a function of the type params. -/
  formednessTarget : (scope : Nat) → (typeParam0 typeParam1 : RawTerm scope) → RawTerm scope
  /-- The member cell, built from the (possibly-phantom) two children. -/
  memberCell : (scope : Nat) → (child0 child1 : RawTerm scope) → RawTerm scope
  /-- The output type code, from the children (`refl` reads `child0`) and the type params. -/
  outputType : (scope : Nat) → (child0 child1 typeParam0 typeParam1 : RawTerm scope) → RawTerm scope

/-- `optionSome`: one grown child at the element type (`typeParam0`); output `option(typeParam0)`. -/
def optionSomeGrownSpec : GrownDataIntroSpec where
  hasChild0 := true; hasChild1 := false; hasFormedness := false
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ typeParam0 _ => typeParam0
  memberCell := fun _ child0 _ => optionSomeCell child0
  outputType := fun _ _ _ typeParam0 _ => optionTypeCell typeParam0

/-- `optionNone`: no child, a grown-formedness premise on the free element type (`typeParam0`); output
`option(typeParam0)`. -/
def optionNoneGrownSpec : GrownDataIntroSpec where
  hasChild0 := false; hasChild1 := false; hasFormedness := true
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ typeParam0 _ => typeParam0
  memberCell := fun _ _ _ => optionNoneCell
  outputType := fun _ _ _ typeParam0 _ => optionTypeCell typeParam0

/-- `listNil`: the `optionNone` twin with the list container. -/
def listNilGrownSpec : GrownDataIntroSpec where
  hasChild0 := false; hasChild1 := false; hasFormedness := true
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ typeParam0 _ => typeParam0
  memberCell := fun _ _ _ => listNilCell
  outputType := fun _ _ _ typeParam0 _ => listTypeCell typeParam0

/-- `eitherInl`: a grown value at the pinned LEFT type (`typeParam0`), a grown-formedness premise on the
free RIGHT type (`typeParam1`); output `either(typeParam0, typeParam1)`. -/
def eitherInlGrownSpec : GrownDataIntroSpec where
  hasChild0 := true; hasChild1 := false; hasFormedness := true
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ _ typeParam1 => typeParam1
  memberCell := fun _ child0 _ => eitherInlCell child0
  outputType := fun _ _ _ typeParam0 typeParam1 => eitherTypeCell typeParam0 typeParam1

/-- `eitherInr`: a grown value pinning the RIGHT type (`typeParam0`), free LEFT (`typeParam1`); output
`either(typeParam1, typeParam0)` (the free side first). -/
def eitherInrGrownSpec : GrownDataIntroSpec where
  hasChild0 := true; hasChild1 := false; hasFormedness := true
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ _ typeParam1 => typeParam1
  memberCell := fun _ child0 _ => eitherInrCell child0
  outputType := fun _ _ _ typeParam0 typeParam1 => eitherTypeCell typeParam1 typeParam0

/-- `pair`: two grown children at two independent type params; output `product(typeParam0, typeParam1)`. -/
def pairGrownSpec : GrownDataIntroSpec where
  hasChild0 := true; hasChild1 := true; hasFormedness := false
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ _ typeParam1 => typeParam1
  formednessTarget := fun _ typeParam0 _ => typeParam0
  memberCell := fun _ child0 child1 => pairCell child0 child1
  outputType := fun _ _ _ typeParam0 typeParam1 => productTypeCell typeParam0 typeParam1

/-- `refl`: a grown witness at its type (`typeParam0`); output `Id(typeParam0, witness, witness)` — the
output reads the child VALUE. -/
def reflGrownSpec : GrownDataIntroSpec where
  hasChild0 := true; hasChild1 := false; hasFormedness := false
  child0Type := fun _ typeParam0 _ => typeParam0
  child1Type := fun _ typeParam0 _ => typeParam0
  formednessTarget := fun _ typeParam0 _ => typeParam0
  memberCell := fun _ child0 _ => reflCell child0
  outputType := fun _ child0 _ typeParam0 _ => idTypeCell typeParam0 child0 child0

/-- The unified grown-data-intro table: the seven grown-family rows. -/
def grownDataIntroSpecOf (generator : Generator) : Option GrownDataIntroSpec :=
  if generator = .gen_optionSome then some optionSomeGrownSpec
  else if generator = .gen_optionNone then some optionNoneGrownSpec
  else if generator = .gen_listNil then some listNilGrownSpec
  else if generator = .gen_eitherInl then some eitherInlGrownSpec
  else if generator = .gen_eitherInr then some eitherInrGrownSpec
  else if generator = .gen_pair then some pairGrownSpec
  else if generator = .gen_refl then some reflGrownSpec
  else none

theorem grownDataIntroSpecOf_optionSome :
    grownDataIntroSpecOf .gen_optionSome = some optionSomeGrownSpec := rfl
theorem grownDataIntroSpecOf_optionNone :
    grownDataIntroSpecOf .gen_optionNone = some optionNoneGrownSpec := rfl
theorem grownDataIntroSpecOf_listNil :
    grownDataIntroSpecOf .gen_listNil = some listNilGrownSpec := rfl
theorem grownDataIntroSpecOf_eitherInl :
    grownDataIntroSpecOf .gen_eitherInl = some eitherInlGrownSpec := rfl
theorem grownDataIntroSpecOf_eitherInr :
    grownDataIntroSpecOf .gen_eitherInr = some eitherInrGrownSpec := rfl
theorem grownDataIntroSpecOf_pair :
    grownDataIntroSpecOf .gen_pair = some pairGrownSpec := rfl
theorem grownDataIntroSpecOf_refl :
    grownDataIntroSpecOf .gen_refl = some reflGrownSpec := rfl

/-- **A grown-data-intro table hit pins one of the seven rows.**  The propext-clean inverter the
companion re-proofs dispatch on. -/
theorem grownDataIntroSpecOf_cases {generator : Generator} {spec : GrownDataIntroSpec}
    (tableHit : grownDataIntroSpecOf generator = some spec) :
    (generator = .gen_optionSome ∧ spec = optionSomeGrownSpec) ∨
    (generator = .gen_optionNone ∧ spec = optionNoneGrownSpec) ∨
    (generator = .gen_listNil ∧ spec = listNilGrownSpec) ∨
    (generator = .gen_eitherInl ∧ spec = eitherInlGrownSpec) ∨
    (generator = .gen_eitherInr ∧ spec = eitherInrGrownSpec) ∨
    (generator = .gen_pair ∧ spec = pairGrownSpec) ∨
    (generator = .gen_refl ∧ spec = reflGrownSpec) := by
  unfold grownDataIntroSpecOf at tableHit
  by_cases isOptionSome : generator = .gen_optionSome
  · rw [if_pos isOptionSome] at tableHit
    exact Or.inl ⟨isOptionSome, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isOptionSome] at tableHit
    by_cases isOptionNone : generator = .gen_optionNone
    · rw [if_pos isOptionNone] at tableHit
      exact Or.inr (Or.inl ⟨isOptionNone, (Option.some.inj tableHit).symm⟩)
    · rw [if_neg isOptionNone] at tableHit
      by_cases isListNil : generator = .gen_listNil
      · rw [if_pos isListNil] at tableHit
        exact Or.inr (Or.inr (Or.inl ⟨isListNil, (Option.some.inj tableHit).symm⟩))
      · rw [if_neg isListNil] at tableHit
        by_cases isEitherInl : generator = .gen_eitherInl
        · rw [if_pos isEitherInl] at tableHit
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨isEitherInl, (Option.some.inj tableHit).symm⟩)))
        · rw [if_neg isEitherInl] at tableHit
          by_cases isEitherInr : generator = .gen_eitherInr
          · rw [if_pos isEitherInr] at tableHit
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨isEitherInr, (Option.some.inj tableHit).symm⟩))))
          · rw [if_neg isEitherInr] at tableHit
            by_cases isPair : generator = .gen_pair
            · rw [if_pos isPair] at tableHit
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨isPair, (Option.some.inj tableHit).symm⟩)))))
            · rw [if_neg isPair] at tableHit
              by_cases isRefl : generator = .gen_refl
              · rw [if_pos isRefl] at tableHit
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨isRefl, (Option.some.inj tableHit).symm⟩)))))
              · rw [if_neg isRefl] at tableHit
                exact absurd tableHit (by intro hit; cases hit)

end FX1Poly.Typed
