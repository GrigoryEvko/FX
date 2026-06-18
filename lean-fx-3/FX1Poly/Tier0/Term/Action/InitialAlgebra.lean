import FX1Poly.Tier0.Term.Action.Fold

/-! # Tier0/Term — RawTerm is the initial algebra of the term signature (term-1, the real UP)

`Action/Fold.lean` ships the RawTerm-VALUED action-fold (the rename/subst traversal engine), and
`Action/FoldUniqueness.lean` proves THAT engine is the unique solution to its equations.  Neither is the
initial-algebra universal property: both are about maps `RawTerm → RawTerm` threading a Container.

This file ships the genuine term-1 statement — **`RawTerm` is the initial algebra of its term signature
functor**: the catamorphism into an ARBITRARY carrier family `C : Nat → Type`, and its uniqueness.  For
any model (a `CarrierAlgebra C`, i.e. an interpretation of every generator into `C`), there is a UNIQUE
homomorphism `RawTerm → C` — the structural recursor `cata`.  This is "constructors = initial algebra":
the constructor signature presents the free term algebra, and any structure-preserving map factors
through the recursor uniquely (the left-adjoint / free-functor universal property).

The pure catamorphism is UNIFORM over all 205 generators — `gen_var` is just a constructor whose `Fin`
payload is handed to `combine`, so there is no variable dispatch, no Container threading, and no binder
lift (each child folds at its own shifted scope).  This is strictly simpler than the action-fold, and it
is the textbook witness that an inductive type is the initial algebra of its signature.

## What this file ships (each zero-axiom)

  * **`CarrierChildren C`** — the signature functor's children spine valued in `C` (the `C`-analogue of
    `RawTermChildren`: each child lives at the parent scope plus its binder shift).
  * **`CarrierAlgebra C`** — a model of the term signature: `combine` interprets every generator + payload
    + folded children into `C`.
  * **`cata` / `cataChildren`** — the catamorphism: the structural recursor `RawTerm s → C s`, uniform over
    all generators, with its defining equations holding by `rfl` (`cata_mkGen` etc.).
  * **`IsCarrierHomomorphism`** + **`unique` / `uniqueChildren`** — UNIQUENESS: any homomorphism (a map
    satisfying `cata`'s equations) agrees with `cata`.  The recursor's universal property.
  * **`cataHomomorphism`** — EXISTENCE: `cata` IS a homomorphism (its equations hold), so existence +
    uniqueness give the initial-algebra UP.  **`carrier_hom_ext`** — two homomorphisms into the same
    carrier agree.

The dependent eliminator generalizing `cata` is Lean's auto-generated `RawTerm.rec` (the induction
principle); `cata` is its non-dependent (constant-motive) instance.  The arbitrary-binding-SIGNATURE lift
(SigTerm over an arbitrary `Signature` is initial; the CwR bi-initiality) is SIG-5 — a further
generalization over the signature, distinct from this fixed-signature, arbitrary-CARRIER statement.

## Zero-axiom verification

A strictly-positive carrier-children inductive, a model record, the mutual catamorphism (structural
recursion on `RawTerm`/`RawTermChildren`, no dispatch), three `rfl` equation lemmas, the mutual uniqueness
proof (`match` + `rw` + a `show` to expose the catamorphism reduction), the existence witness (all fields
`rfl`), and the extensionality corollary.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TermInitialAlgebra.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Tier0.Syntax

/-- The term signature functor's children spine valued in a carrier family `C` — the `C`-analogue of
`RawTermChildren`.  A spine of folded children, the `i`-th living at the parent scope plus the `i`-th
binder shift. -/
inductive CarrierChildren (C : Nat → Type) : List Nat → Nat → Type where
  /-- The empty folded spine. -/
  | cnil {scope : Nat} : CarrierChildren C [] scope
  /-- A folded head (at the shifted scope) followed by the rest of the folded spine. -/
  | ccons {headShift : Nat} {restShifts : List Nat} {scope : Nat}
      (foldedHead : C (scope + headShift))
      (foldedTail : CarrierChildren C restShifts scope) :
      CarrierChildren C (headShift :: restShifts) scope

/-- A **model of the term signature** into a carrier family `C`: an interpretation of every generator,
given its payload and its folded children, into `C`.  Uniform over all 205 generators (`gen_var`
included — its `Fin` payload is handled by `combine` like any other). -/
structure CarrierAlgebra (C : Nat → Type) where
  /-- Combine a generator + payload + folded children into the carrier. -/
  combine : {scope : Nat} → (generator : Generator) → (payload : generator.payload scope) →
    (foldedChildren : CarrierChildren C generator.binderShifts scope) → C scope

mutual

/-- The **catamorphism**: the unique structural recursor `RawTerm s → C s` for a model `algebra`.  Folds
each node by recursively folding its children and combining via the algebra — uniform over all generators,
no variable dispatch. -/
def cata {C : Nat → Type} (algebra : CarrierAlgebra C) {scope : Nat}
    (term : RawTerm scope) : C scope :=
  match term with
  | .mkGen generator payload children =>
    algebra.combine generator payload (cataChildren algebra children)

/-- The catamorphism on a children spine. -/
def cataChildren {C : Nat → Type} (algebra : CarrierAlgebra C)
    {binderShifts : List Nat} {scope : Nat}
    (children : RawTermChildren binderShifts scope) : CarrierChildren C binderShifts scope :=
  match binderShifts, children with
  | [], .childNil => .cnil
  | _headShift :: _restShifts, .childCons childHead childTail =>
    .ccons (cata algebra childHead) (cataChildren algebra childTail)

end -- mutual

/-- Defining equation of `cata` on a node (holds by `rfl` — the catamorphism has no dispatch). -/
theorem cata_mkGen {C : Nat → Type} (algebra : CarrierAlgebra C) {scope : Nat}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    cata algebra (.mkGen generator payload children)
      = algebra.combine generator payload (cataChildren algebra children) := rfl

/-- Defining equation of `cataChildren` on the empty spine. -/
theorem cataChildren_nil {C : Nat → Type} (algebra : CarrierAlgebra C) {scope : Nat} :
    cataChildren algebra (.childNil : RawTermChildren [] scope) = .cnil := rfl

/-- Defining equation of `cataChildren` on a cons spine. -/
theorem cataChildren_cons {C : Nat → Type} (algebra : CarrierAlgebra C)
    {headShift : Nat} {restShifts : List Nat} {scope : Nat}
    (childHead : RawTerm (scope + headShift))
    (childTail : RawTermChildren restShifts scope) :
    cataChildren algebra (.childCons childHead childTail)
      = .ccons (cata algebra childHead) (cataChildren algebra childTail) := rfl

/-- A **homomorphism out of `RawTerm`** into a model: a `map`/`mapChildren` family satisfying the
catamorphism's defining equations (combine on nodes, nil/cons on the spine).  The structure of solutions
to the recursor's equations. -/
structure IsCarrierHomomorphism {C : Nat → Type} (algebra : CarrierAlgebra C) where
  /-- The candidate map on terms. -/
  map : {scope : Nat} → RawTerm scope → C scope
  /-- The candidate map on children spines. -/
  mapChildren : {binderShifts : List Nat} → {scope : Nat} →
    RawTermChildren binderShifts scope → CarrierChildren C binderShifts scope
  /-- Combine on a node. -/
  onGen : ∀ {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope),
    map (.mkGen generator payload children)
      = algebra.combine generator payload (mapChildren children)
  /-- Empty spine. -/
  onNil : ∀ {scope : Nat},
    mapChildren (.childNil : RawTermChildren [] scope) = .cnil
  /-- Cons spine. -/
  onCons : ∀ {headShift : Nat} {restShifts : List Nat} {scope : Nat}
    (childHead : RawTerm (scope + headShift)) (childTail : RawTermChildren restShifts scope),
    mapChildren (.childCons childHead childTail)
      = .ccons (map childHead) (mapChildren childTail)

mutual

/-- ★ **Initiality (uniqueness, terms).**  Any homomorphism out of `RawTerm` into a model agrees with the
catamorphism on every term — `cata` is the UNIQUE homomorphism, so `RawTerm` is the initial algebra of its
signature. -/
theorem IsCarrierHomomorphism.unique {C : Nat → Type} {algebra : CarrierAlgebra C}
    (homomorphism : IsCarrierHomomorphism algebra)
    {scope : Nat} (term : RawTerm scope) :
    homomorphism.map term = cata algebra term := by
  match term with
  | .mkGen generator payload children =>
    rw [homomorphism.onGen generator payload children]
    show algebra.combine generator payload (homomorphism.mapChildren children)
          = algebra.combine generator payload (cataChildren algebra children)
    rw [homomorphism.uniqueChildren children]

/-- ★ **Initiality (uniqueness, children).**  Any homomorphism agrees with `cataChildren` on every spine. -/
theorem IsCarrierHomomorphism.uniqueChildren {C : Nat → Type} {algebra : CarrierAlgebra C}
    (homomorphism : IsCarrierHomomorphism algebra)
    {binderShifts : List Nat} {scope : Nat}
    (children : RawTermChildren binderShifts scope) :
    homomorphism.mapChildren children = cataChildren algebra children := by
  match binderShifts, children with
  | [], .childNil =>
    exact homomorphism.onNil
  | _headShift :: _restShifts, .childCons childHead childTail =>
    rw [homomorphism.onCons childHead childTail]
    show CarrierChildren.ccons (homomorphism.map childHead) (homomorphism.mapChildren childTail)
          = CarrierChildren.ccons (cata algebra childHead) (cataChildren algebra childTail)
    rw [homomorphism.unique childHead, homomorphism.uniqueChildren childTail]

end -- mutual

/-- **Existence: `cata` is a homomorphism.**  The catamorphism satisfies its own defining equations (each
by `rfl`), so it is a witness of `IsCarrierHomomorphism`.  Existence + uniqueness = the initial-algebra
universal property. -/
def cataHomomorphism {C : Nat → Type} (algebra : CarrierAlgebra C) :
    IsCarrierHomomorphism algebra where
  map := fun term => cata algebra term
  mapChildren := fun children => cataChildren algebra children
  onGen := fun _generator _payload _children => rfl
  onNil := rfl
  onCons := fun _childHead _childTail => rfl

/-- **Homomorphism extensionality.**  Two homomorphisms out of `RawTerm` into the same model agree on
every term — both equal `cata` by uniqueness.  The universal property packaged for direct comparison:
to compare two maps out of the initial algebra, it suffices that both are homomorphisms. -/
theorem carrier_hom_ext {C : Nat → Type} {algebra : CarrierAlgebra C}
    (firstHomomorphism secondHomomorphism : IsCarrierHomomorphism algebra)
    {scope : Nat} (term : RawTerm scope) :
    firstHomomorphism.map term = secondHomomorphism.map term :=
  (firstHomomorphism.unique term).trans (secondHomomorphism.unique term).symm

end FX1Poly.Core
