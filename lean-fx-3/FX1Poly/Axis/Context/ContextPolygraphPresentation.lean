import FX1Poly.Axis.Context.ContextMarkedComplicial

/-! # context-40 — the context category as a FINITELY-PRESENTED (∞,ω)-polygraph + decidable admissibility

`context-40` (★, on the fib-* arc, →fib-13 THE-ONE-OBJECT grand capstone) presents the context category as a
FINITELY-PRESENTED polygraph (computad): the GENERATORS are the context formers — the `TypingContext`
constructors `empty` / `cons` / `lockCons` (the typed-layer kernel telescope, modeled here over the real
scope substrate `Nat`) — plus a DECIDABLE "is this candidate extension admissible" predicate at the
strict / finite level.

## The polygraph generators ARE the context formers

A polygraph presents an ω-category by generators-and-relations at each dimension.  Here:

  * **`empty`** — the 0-ary / root generator (an OBJECT generator: the empty context, scope `0`).
  * **`cons`** — a generating 1-cell `scope ↦ scope + 1` (extend by an ordinary binding).
  * **`lockCons`** — a generating 1-cell `scope ↦ scope + 1` (extend by the affine transpension dimension
    LOCK `◐`, the MTT/MATT context-lock).

These are EXACTLY the kernel's `TypingContext` constructors (`FX1Poly/Typed/.../TypingContext.lean`),
modeled here as the finite enumeration `ContextFormer` (a Axis design-lock cannot import the typed layer,
so — as `context-5`/`context-39` abstract a model's contexts — the generators are modeled over the scope
substrate `Nat`, the binding-type payload `RawTerm scope` being the `×type` content abstracted away; the
LOCK MARK distinguishing `cons` from `lockCons` IS preserved).  The free words over the generators are
`ContextExpr` (the `×type`-abstracted telescopes).

## Finite presentation + decidable admissible-extension (both reachable, zero-axiom)

  * **Finite presentation**: the generating set is the explicit finite list `contextFormers = [empty, cons,
    lockCons]` (`contextFormers_length = 3`), and it is COMPLETE / EXHAUSTIVE (`contextFormers_complete`,
    `contextFormers_exhaustive`: every former is one of the three).
  * **Decidable admissible extension**: `isAdmissibleExtension former baseScope targetScope` decides — by
    STRUCTURAL recursion on the former and a self-contained structural `natEq` (NEVER `decide_of_iff`, NEVER
    `Nat`'s `==`) — whether a candidate generating-cell application respects the former's ARITY and SCOPE
    arithmetic: `empty` admissible only at the trivial base producing scope `0`; `cons` / `lockCons`
    admissible iff `targetScope = baseScope + 1`.  Its `Prop` form `IsAdmissibleExtension` carries a
    propext-free structural `Decidable` instance (a `match` on the `Bool` with the equation proof,
    `Bool.noConfusion` for the negative branch).  Admissibility is GROUNDED in real construction: every
    `ContextExpr` extension is admissible (`cons_extension_admissible` etc.).

## What is deferred (the honest wall)

  * The FULL (∞,ω) POLYGRAPH presentation — the GENERATING HIGHER CELLS (2-cells between context-building
    paths, 3-cells, … up to ω) and the ω-categorical coherence quotient — is NOT shipped: the higher cells
    are the marked-complicial cells of `context-36`, whose full Verity horn-filling and the ω-quotient need
    `Quot.sound` (`fxContextPolygraph_hasFullInfinityOmegaPolygraph = false`).
  * The presentation here is the SELF-CONTAINED Axis analog, NOT a Core `StepOverTable` iota row
    (`fxContextPolygraph_isOverCoreIotaTable = false`).

Imports only `ContextMarkedComplicial` (its `context-36` sibling — the marked (∞,ω) structure whose
dimension-1 marking is the polygraph's thin 1-cells, plus transitively the `RawCategory` /
`discreteUniverseObject` substrate).  A Axis design-lock must not import up into `Core/` / `Typed/`.  Zero
external dependencies — raw Lean 4 + Init only.

Reference: Burroni, "Higher-dimensional word problems" (polygraphs / computads); Guiraud–Malbos, "Polygraphs
of finite derivation type"; Henry–Lanari–Loubaton on (∞,ω)-polygraphs; the kernel `TypingContext`
(`FX1Poly/Typed/Engine/Classifier/TypingContext.lean`); the `context-36` marked complicial structure
(`ContextMarkedComplicial.lean`).
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## The generators — the context formers -/

/-- The **generating context formers** — the `TypingContext` constructors as a finite enumeration: the
GENERATORS of the context polygraph.  `empty` is the 0-ary root; `cons` / `lockCons` are the two generating
1-cells (ordinary binding vs the affine dimension LOCK `◐`). -/
inductive ContextFormer where
  /-- The 0-ary root generator: the empty context (scope `0`). -/
  | empty
  /-- The generating 1-cell extending by an ordinary binding (`scope ↦ scope + 1`). -/
  | cons
  /-- The generating 1-cell extending by the affine transpension dimension LOCK (`scope ↦ scope + 1`). -/
  | lockCons

/-- The **arity** of a generator — the number of context-inputs it consumes: `empty` is nullary (0), `cons`
and `lockCons` are unary (1). -/
def ContextFormer.arity : ContextFormer → Nat
  | .empty => 0
  | .cons => 1
  | .lockCons => 1

/-- The **scope action** of a generator on its (single) input scope: `empty` lands at scope `0` (ignoring any
input — it is the root); `cons` / `lockCons` both lift the scope by one. -/
def ContextFormer.scopeShift : ContextFormer → Nat → Nat
  | .empty, _ => 0
  | .cons, baseScope => baseScope + 1
  | .lockCons, baseScope => baseScope + 1

/-- The finite generating set of the context polygraph — exactly the three context formers. -/
def contextFormers : List ContextFormer := [.empty, .cons, .lockCons]

/-- Finiteness: the generating set has exactly THREE generators. -/
theorem contextFormers_length : contextFormers.length = 3 := rfl

/-- The generating set is COMPLETE — every context former appears in `contextFormers`. -/
theorem contextFormers_complete : ∀ former : ContextFormer, former ∈ contextFormers
  | .empty => List.Mem.head _
  | .cons => List.Mem.tail _ (List.Mem.head _)
  | .lockCons => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The generating set is EXHAUSTIVE — every former is one of the three (the finite presentation has no
hidden generators). -/
theorem contextFormers_exhaustive (former : ContextFormer) :
    former = .empty ∨ former = .cons ∨ former = .lockCons := by
  cases former
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ## The free words over the generators -/

/-- The **free context words** over the generators — the `×type`-abstracted telescopes built from `empty` and
the two extension generators.  Mirrors `TypingContext` with the binding-type payload `RawTerm scope`
abstracted away (the `×type` content), the LOCK mark preserved. -/
inductive ContextExpr where
  /-- The empty context word. -/
  | empty
  /-- Extend a word by an ordinary binding. -/
  | cons (rest : ContextExpr)
  /-- Extend a word by the affine dimension LOCK. -/
  | lockCons (rest : ContextExpr)

/-- The scope (binding count) of a free context word, by structural recursion — every extension lifts the
scope by one, exactly as `TypingContext.length`. -/
def ContextExpr.scope : ContextExpr → Nat
  | .empty => 0
  | .cons rest => rest.scope + 1
  | .lockCons rest => rest.scope + 1

/-! ## A self-contained structural Nat-equality (no `decide_of_iff`, no `Nat`'s `==`) -/

/-- Structural boolean equality on `Nat` — recursion on both arguments.  Self-contained so the admissibility
decision and its reflexivity are propext-free and under our control (the kernel's `==` / `decide` routes are
deliberately avoided). -/
def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | first + 1, second + 1 => natEq first second

/-- `natEq` is reflexive — `natEq n n = true`, by structural recursion on `n`. -/
theorem natEq_refl : ∀ n : Nat, natEq n n = true
  | 0 => rfl
  | n + 1 => natEq_refl n

/-! ## The decidable admissible-extension predicate -/

/-- ★ **The decidable admissible-extension check.**  Decides whether a candidate generating-cell application
— former `former` applied to a base of scope `baseScope`, claiming result scope `targetScope` — is ADMISSIBLE
in the polygraph: it must respect the former's arity and scope arithmetic.  `empty` (the root) is admissible
only at the trivial base producing scope `0`; `cons` / `lockCons` are admissible iff `targetScope =
baseScope + 1`.  Structural recursion on the former + self-contained `natEq` — decidable, zero-axiom. -/
def isAdmissibleExtension : ContextFormer → Nat → Nat → Bool
  | .empty, baseScope, targetScope => natEq baseScope 0 && natEq targetScope 0
  | .cons, baseScope, targetScope => natEq targetScope (baseScope + 1)
  | .lockCons, baseScope, targetScope => natEq targetScope (baseScope + 1)

/-- The root generator `empty` is admissible at the trivial base producing scope `0`. -/
theorem isAdmissibleExtension_empty : isAdmissibleExtension .empty 0 0 = true := rfl

/-- A `cons` extension is admissible exactly when it lifts the base scope by one. -/
theorem isAdmissibleExtension_cons (baseScope : Nat) :
    isAdmissibleExtension .cons baseScope (baseScope + 1) = true :=
  natEq_refl (baseScope + 1)

/-- A `lockCons` extension is admissible exactly when it lifts the base scope by one. -/
theorem isAdmissibleExtension_lockCons (baseScope : Nat) :
    isAdmissibleExtension .lockCons baseScope (baseScope + 1) = true :=
  natEq_refl (baseScope + 1)

/-- The root generator is INADMISSIBLE over a non-trivial base — `empty` cannot extend an existing context
(it is nullary). -/
theorem isAdmissibleExtension_empty_overNonemptyBase (baseScope : Nat) :
    isAdmissibleExtension .empty (baseScope + 1) 0 = false := rfl

/-- The `Prop` form of admissibility — the candidate generating-cell application is admissible. -/
def IsAdmissibleExtension (former : ContextFormer) (baseScope targetScope : Nat) : Prop :=
  isAdmissibleExtension former baseScope targetScope = true

/-- ★ **Admissibility is DECIDABLE** — a propext-free STRUCTURAL `Decidable` instance: match on the `Bool`
value of `isAdmissibleExtension` with the equation proof; the positive branch is `isTrue` of the equation,
the negative branch derives `False` from `false = true` via `Bool.noConfusion`.  No `decide_of_iff`. -/
instance instDecidableIsAdmissibleExtension
    (former : ContextFormer) (baseScope targetScope : Nat) :
    Decidable (IsAdmissibleExtension former baseScope targetScope) :=
  match isMatch : isAdmissibleExtension former baseScope targetScope with
  | true => isTrue isMatch
  | false => isFalse (fun isAdmissible => Bool.noConfusion (isMatch.symm.trans isAdmissible))

/-- ★ **The admissible-extension predicate is decidable** (the deliverable, exposing the structural
instance): for every candidate generating-cell application, admissibility is decided. -/
def contextPolygraph_admissibleExtension_decidable
    (former : ContextFormer) (baseScope targetScope : Nat) :
    Decidable (IsAdmissibleExtension former baseScope targetScope) :=
  instDecidableIsAdmissibleExtension former baseScope targetScope

/-! ## Admissibility grounded in real construction over the free words -/

/-- A `cons` extension of any context word is admissible — extending a word of scope `rest.scope` to
`rest.scope + 1`.  Grounds admissibility in genuine context construction (non-vacuity). -/
theorem cons_extension_admissible (rest : ContextExpr) :
    IsAdmissibleExtension .cons rest.scope (ContextExpr.cons rest).scope :=
  isAdmissibleExtension_cons rest.scope

/-- A `lockCons` (affine dimension LOCK) extension of any context word is admissible. -/
theorem lockCons_extension_admissible (rest : ContextExpr) :
    IsAdmissibleExtension .lockCons rest.scope (ContextExpr.lockCons rest).scope :=
  isAdmissibleExtension_lockCons rest.scope

/-- The root word `empty` is an admissible 0-ary extension at the trivial base. -/
theorem empty_extension_admissible :
    IsAdmissibleExtension .empty ContextExpr.empty.scope ContextExpr.empty.scope :=
  isAdmissibleExtension_empty

/-! ## The packaged finite presentation -/

/-- The **finite polygraph presentation** of the context category: the finite generating set of context
formers (with their arity and scope action) plus the COMPLETENESS of the generating set.  The generating
HIGHER CELLS (the full (∞,ω) polygraph) are walled — see the honesty markers. -/
structure ContextPolygraphPresentation where
  /-- The finite list of generators. -/
  generators : List ContextFormer
  /-- Each generator's arity (number of context-inputs). -/
  arityOf : ContextFormer → Nat
  /-- Each generator's action on the input scope. -/
  scopeShiftOf : ContextFormer → Nat → Nat
  /-- The generating set is complete — every context former is a generator. -/
  generatorsComplete : ∀ former : ContextFormer, former ∈ generators

/-- ★ **The canonical finite presentation** of the context category — the three context formers as
generators, with their arity / scope action and the completeness witness. -/
def contextPolygraph : ContextPolygraphPresentation where
  generators := contextFormers
  arityOf := ContextFormer.arity
  scopeShiftOf := ContextFormer.scopeShift
  generatorsComplete := contextFormers_complete

/-! ## Bridge to `context-36`: the 0-skeleton and the scope-increasing generators -/

/-- A `Nat` is never its own successor — the two-element diagonal on scopes, by structural recursion. -/
theorem natSuccNeSelf : ∀ n : Nat, n + 1 ≠ n
  | 0 => fun isEq => Nat.noConfusion isEq
  | n + 1 => fun isEq => natSuccNeSelf n (Nat.succ.inj isEq)

/-- The polygraph's **0-skeleton** — its generating OBJECTS are the scopes, presented as the discrete context
category (`context-30`'s `discreteUniverseObject` on `Nat`, transitively via `context-36`).  The generating
1-cells (`cons`/`lockCons`) are added ON TOP of this 0-skeleton, whose marking is `context-36`'s
`IsContextEquivalence`. -/
def contextPolygraphZeroSkeleton : RawCategory := discreteUniverseObject Nat

/-- The `cons` generator is a GENUINELY NEW 1-cell, not a degeneracy: it strictly increases the scope
(`scopeShift .cons baseScope = baseScope + 1 ≠ baseScope`), so it is not an identity of the 0-skeleton. -/
theorem consGenerator_scopeStrictlyIncreases (baseScope : Nat) :
    ContextFormer.scopeShift .cons baseScope ≠ baseScope :=
  natSuccNeSelf baseScope

/-- The `lockCons` generator is likewise a genuinely new 1-cell — the affine dimension LOCK strictly
increases the scope. -/
theorem lockConsGenerator_scopeStrictlyIncreases (baseScope : Nat) :
    ContextFormer.scopeShift .lockCons baseScope ≠ baseScope :=
  natSuccNeSelf baseScope

/-! ## Honesty markers -/

/-- **Honesty marker.**  The context category is FINITELY PRESENTED as a polygraph: the generating set is the
explicit finite list of three context formers (`contextFormers`, `contextFormers_length = 3`), COMPLETE and
EXHAUSTIVE, packaged as `contextPolygraph`.  `= true`. -/
def fxContextPolygraph_hasFinitePresentation : Bool := true

/-- **Honesty marker.**  The "is this candidate extension admissible" predicate is DECIDABLE at the finite /
strict level via a propext-free structural `Decidable` instance (`isAdmissibleExtension` +
`instDecidableIsAdmissibleExtension`), grounded in real context construction.  `= true`. -/
def fxContextPolygraph_hasDecidableAdmissibleExtension : Bool := true

/-- **Honesty marker.**  The FULL (∞,ω) POLYGRAPH presentation — the generating HIGHER CELLS (2-cells between
context-building paths, 3-cells, … up to ω) and the ω-categorical coherence quotient (the marked-complicial
cells of `context-36`, whose full horn-filling needs `Quot.sound`) — is NOT shipped.  `= false`. -/
def fxContextPolygraph_hasFullInfinityOmegaPolygraph : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of a Core table-native polygraph row; a
Axis design-lock cannot import the Core engine (nor the typed-layer `TypingContext`), so the generators are
re-modeled here over the scope substrate.  Gluing the Axis and Core forms is cross-axis `×type`.  `= false`. -/
def fxContextPolygraph_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: a concrete `cons` extension `scope 3 ↦ scope 4` is admissible — the decided positive case. -/
theorem contextPolygraph_cons_admissible_smoke : IsAdmissibleExtension .cons 3 4 :=
  isAdmissibleExtension_cons 3

/-- Smoke: a concrete `lockCons` (affine LOCK) extension `scope 2 ↦ scope 3` is admissible. -/
theorem contextPolygraph_lockCons_admissible_smoke : IsAdmissibleExtension .lockCons 2 3 :=
  isAdmissibleExtension_lockCons 2

/-- Smoke: the root generator `empty` is rejected over a non-trivial base — `empty` cannot extend an existing
context. -/
theorem contextPolygraph_empty_rejected_smoke :
    isAdmissibleExtension .empty 1 0 = false := rfl

end FX1Poly.Axis
