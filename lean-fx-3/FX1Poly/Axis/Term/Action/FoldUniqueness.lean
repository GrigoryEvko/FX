import FX1Poly.Axis.Term.Action.Fold

/-! # Axis/Term — action-fold uniqueness: the rename/subst engine is unique (supports term-2 / term-26)

NOTE: this is NOT the term-1 initial-algebra universal property — that is `Action/InitialAlgebra.lean`
(`cata` + `IsCarrierHomomorphism.unique`, the catamorphism into an ARBITRARY carrier).  This file is the
separate uniqueness of the RawTerm-VALUED, Container-threaded rename/subst fold ENGINE.

`Action/Fold.lean` ships `fold`/`foldChildren` — the Allais-style "Semantics" traversal that `rename`,
`weaken`, and `subst` all instantiate. That is the EXISTENCE leg of the term-axis recursor: for any
`GenAlgebra` and any `Container` action, `fold` builds a map `RawTerm → RawTerm`.

This file adds the missing UNIQUENESS leg — `fold` is the UNIQUE solution to its defining equations. A
`candidate` family that combines variables via the Container and non-variable generators via the algebra
(exactly the two equations `fold` itself satisfies) must agree with `fold` everywhere. This is the
universal-property half of "the constructor signature presents the recursor": the structural recursor is
unique, so any structure-preserving map factors through it uniquely.

## Honest scope (not oversold)

The shipped `GenAlgebra` is RawTerm-VALUED (its `algebra` field returns `RawTerm scope`), tailored to the
rename/subst use case; the Container threads variables and binder lifts at the fold layer. So this is the
catamorphism-uniqueness / recursor-uniqueness theorem for THAT action-fold — NOT arbitrary-carrier SOAS
initiality (RawTerm initial among models into an ARBITRARY carrier), which would require a carrier-general
`GenAlgebra` (the field's docstring flags this as a future variant) and is a separate refactor.

## What this file ships (each zero-axiom)

  * **`IsFoldHomomorphism`** — a `candidate`/`candidateChildren` family together with the four equations
    `fold` satisfies (var via the Container, non-var via the algebra, nil/cons on the children spine).
  * **`IsFoldHomomorphism.unique_term` / `unique_children`** — the mutual structural-recursion proof that any
    such candidate agrees with `fold`/`foldChildren` pointwise (for every action and term). The recursor's
    universal property.
  * **`foldHomomorphism`** — `fold` itself IS a fold-homomorphism (its four equations hold), so existence and
    uniqueness combine: `fold` is THE unique fold-homomorphism.
  * **`IsFoldHomomorphism.eq_fold`** + **`foldHomomorphism_unique`** — the packaged universal property, and
    **`fold_hom_ext`** — two fold-homomorphisms (over the same algebra) agree on every term.

## Zero-axiom verification

A single-field-bundle structure, two mutual structural-recursion theorems (mirroring
`RawTerm.subst_compose`'s `match` + `by_cases hVar` + `dsimp only [fold]` + `dif_pos`/`dif_neg` idiom; the
var case reduces the `Eq.rec`-cast by `rfl`, the non-var case aligns the shared payload cast and recurses on
the children), and the existence/extensionality corollaries. No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`. Per-declaration gated in
`FX1PolyAudit/AuditAxisTermFoldUniqueness.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Axis.Syntax

/-- A **fold-homomorphism** for a `GenAlgebra`: a `Container`-indexed family `candidate` (with its children
companion `candidateChildren`) satisfying exactly the four equations that `fold` does — the variable case
dispatched to the Container, the non-variable case combined by the algebra (under the shared scope-invariance
payload cast), and the nil/cons structure on the children spine.  The recursor's algebra of solutions. -/
structure IsFoldHomomorphism {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] (algebra : GenAlgebra) where
  /-- The candidate map on terms. -/
  candidate : {sourceScope targetScope : Nat} →
    Container sourceScope targetScope → RawTerm sourceScope → RawTerm targetScope
  /-- The candidate map on children spines. -/
  candidateChildren : {sourceScope targetScope : Nat} → {binderShifts : List Nat} →
    Container sourceScope targetScope →
      RawTermChildren binderShifts sourceScope → RawTermChildren binderShifts targetScope
  /-- Variable case: dispatch to the Container's variable bridge. -/
  onVar : ∀ {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (position : Fin sourceScope),
    candidate action (.mkGen .gen_var position .childNil)
      = ActsOnRawTermVar.varToRawTerm action position
  /-- Non-variable case: combine the folded children via the algebra, under the scope-invariance cast. -/
  onNonVar : ∀ {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (generator : Generator)
    (hNotVar : generator ≠ .gen_var) (payload : generator.payload sourceScope)
    (children : RawTermChildren generator.binderShifts sourceScope),
    candidate action (.mkGen generator payload children)
      = algebra.algebra generator
          ((Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope) ▸ payload)
          (candidateChildren action children)
  /-- Empty children spine. -/
  onNil : ∀ {sourceScope targetScope : Nat} (action : Container sourceScope targetScope),
    candidateChildren (binderShifts := []) action .childNil = .childNil
  /-- Cons children spine: the head is folded under its binder lift. -/
  onCons : ∀ {sourceScope targetScope : Nat} {headShift : Nat} {restShifts : List Nat}
    (action : Container sourceScope targetScope)
    (childHead : RawTerm (sourceScope + headShift))
    (childTail : RawTermChildren restShifts sourceScope),
    candidateChildren action (.childCons childHead childTail)
      = .childCons (candidate (iterateLiftRaw action headShift) childHead)
          (candidateChildren action childTail)

mutual

/-- ★ **Recursor uniqueness (terms).**  Any fold-homomorphism's `candidate` agrees with `fold` on every term
— `fold` is the unique solution to its defining equations. -/
theorem IsFoldHomomorphism.unique_term {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] {algebra : GenAlgebra}
    (homomorphism : IsFoldHomomorphism algebra)
    {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (term : RawTerm sourceScope) :
    homomorphism.candidate action term = fold algebra action term := by
  match term with
  | .mkGen generator payload children =>
    by_cases hVar : generator = .gen_var
    case pos =>
      subst hVar
      match children with
      | .childNil =>
        rw [homomorphism.onVar action payload]
        dsimp only [fold]
        rw [dif_pos rfl]
    case neg =>
      rw [homomorphism.onNonVar action generator hVar payload children]
      dsimp only [fold]
      rw [dif_neg hVar]
      congr 1
      exact homomorphism.unique_children action children

/-- ★ **Recursor uniqueness (children).**  Any fold-homomorphism's `candidateChildren` agrees with
`foldChildren` on every children spine. -/
theorem IsFoldHomomorphism.unique_children {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] {algebra : GenAlgebra}
    (homomorphism : IsFoldHomomorphism algebra)
    {sourceScope targetScope : Nat} {binderShifts : List Nat}
    (action : Container sourceScope targetScope)
    (children : RawTermChildren binderShifts sourceScope) :
    homomorphism.candidateChildren action children = foldChildren algebra action children := by
  match binderShifts, children with
  | [], .childNil =>
    exact homomorphism.onNil action
  | headShift :: _restShifts, .childCons childHead childTail =>
    rw [homomorphism.onCons action childHead childTail]
    show RawTermChildren.childCons
            (homomorphism.candidate (iterateLiftRaw action headShift) childHead)
            (homomorphism.candidateChildren action childTail)
          = RawTermChildren.childCons
              (fold algebra (iterateLiftRaw action headShift) childHead)
              (foldChildren algebra action childTail)
    rw [homomorphism.unique_term (iterateLiftRaw action headShift) childHead,
        homomorphism.unique_children action childTail]

end -- mutual

/-- **Existence: `fold` is a fold-homomorphism.**  The canonical traversal satisfies its own four equations
(each by `rfl` after the variable/non-variable dispatch reduces), so `fold` is a witness of
`IsFoldHomomorphism` — existence to pair with the uniqueness above. -/
def foldHomomorphism {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] (algebra : GenAlgebra) :
    IsFoldHomomorphism (Container := Container) algebra where
  candidate := fun {sourceScope targetScope} (action : Container sourceScope targetScope) term =>
    fold (Container := Container) algebra action term
  candidateChildren := fun {sourceScope targetScope _binderShifts}
      (action : Container sourceScope targetScope) children =>
    foldChildren (Container := Container) algebra action children
  onVar := fun _action _position => rfl
  onNonVar := fun _action _generator hNotVar _payload _children => by
    dsimp only [fold]; rw [dif_neg hNotVar]
  onNil := fun _action => rfl
  onCons := fun _action _childHead _childTail => rfl

/-- The packaged universal property: any fold-homomorphism's `candidate` is the `foldHomomorphism`'s
`candidate` — they are equal at every action and term. -/
theorem IsFoldHomomorphism.eq_fold {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] {algebra : GenAlgebra}
    (homomorphism : IsFoldHomomorphism algebra)
    {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (term : RawTerm sourceScope) :
    homomorphism.candidate action term = (foldHomomorphism algebra).candidate action term :=
  homomorphism.unique_term action term

/-- `foldHomomorphism` is THE unique fold-homomorphism (up to pointwise agreement): every fold-homomorphism's
candidate equals it. -/
theorem foldHomomorphism_unique {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] {algebra : GenAlgebra}
    (homomorphism : IsFoldHomomorphism algebra)
    {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (term : RawTerm sourceScope) :
    homomorphism.candidate action term = fold algebra action term :=
  homomorphism.unique_term action term

/-- **Fold-homomorphism extensionality.**  Two fold-homomorphisms over the same algebra agree on every term —
both equal `fold` by uniqueness.  The universal property packaged for direct comparison. -/
theorem fold_hom_ext {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermVar Container] {algebra : GenAlgebra}
    (firstHomomorphism secondHomomorphism : IsFoldHomomorphism algebra)
    {sourceScope targetScope : Nat}
    (action : Container sourceScope targetScope) (term : RawTerm sourceScope) :
    firstHomomorphism.candidate action term = secondHomomorphism.candidate action term :=
  (firstHomomorphism.unique_term action term).trans
    (secondHomomorphism.unique_term action term).symm

end FX1Poly.Core
