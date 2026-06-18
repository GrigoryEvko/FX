/-! # Tier0/Term — the terminal coalgebra of the stream functor (term-3, RIGHT / co-signature)

`term-1` showed `RawTerm` is the INITIAL ALGEBRA of its signature — the LEFT universal property (terms as
0-cells, the catamorphism `cata` into an arbitrary CARRIER).  `term-3` is the op-dual RIGHT leg: the
TERMINAL (final) COALGEBRA, with corecursion (the anamorphism) and bisimulation.  Where `term-1` gave the
unique map INTO an arbitrary carrier from the initial algebra, `term-3` gives the unique map FROM an
arbitrary carrier into the terminal coalgebra.

The kernel has no concrete coinductive carrier — `gen_codataUnfold` / `gen_codataDest` / `gen_polyNu` are
`reserved` GENERATOR TAGS with no coinductive semantics (only the `productiveClass` classifier metadata).
So unlike `term-1` (whose `RawTerm` IS the FX term former), `term-3` builds the terminal-coalgebra
machinery on the CANONICAL instance: the final coalgebra of the stream functor `X ↦ A × X`, generic over
the source coalgebra carrier.  This is the exact dual of `term-1`'s arbitrary-CARRIER initiality (there:
fixed FX signature, varying carrier; here: fixed stream functor, varying SOURCE coalgebra carrier).

## The honest scope (the dual of `term-2`'s thin-category collapse)

Lean 4 core has no `coinductive` declaration; the final coalgebra is represented as the
observation function `Nat → A` (the standard model — the n-th observation of the stream).  Because we do
NOT use funext (`= Quot.sound`, banned), equality of streams is OBSERVATIONAL / BISIMULATION, never
on-the-nose: every "uniqueness" and "commutation" statement is stated POINTWISE (`∀ n, … .observe n = …`).
This is exactly the dual of `term-2`, where the `Prop`-truncation collapsed the category laws to proof
irrelevance: here the absence of funext makes equality observational.  On-the-nose stream equality would
need funext (avoided).

The FX co-signature proper — terminal-coalgebra SEMANTICS for `gen_codataUnfold` / `gen_codataDest` over
the whole generator table, plus a DECIDABLE-and-COMPLETE guardedness/productivity criterion (the "scary
core") — is the deferred generalization, the co-dual of `SIG-5`.

## What this file ships (each zero-axiom)

  * **`FinalStream A`** — the terminal coalgebra of `X ↦ A × X`, with co-structure `head` / `tail`
    (the observations / destructors — the co-signature's generating set).
  * **`StreamCoalgebra Carrier A`** — a source coalgebra `Carrier → A × Carrier` (`out` / `next`); the
    op-dual of `term-1`'s `CarrierAlgebra`.
  * **`StreamCoalgebra.ana`** — the ANAMORPHISM (corecursion): the coalgebra morphism FROM the source
    INTO the terminal coalgebra; the op-dual of `cata`.
  * **`ana_head` / `ana_tail`** + **`ana_isHom`** — the coalgebra-HOMOMORPHISM laws: `ana` commutes with
    the observations (the op-dual of `term-1`'s `onGen` / `term-2`'s universal triangle), so `ana` IS a
    coalgebra hom (existence).
  * **`ana_unique`** — TERMINALITY: any coalgebra hom into `FinalStream` agrees with `ana` up to
    bisimulation (the op-dual of `IsCarrierHomomorphism.unique`).
  * **`IsBisimulation`** + **`bisim_observe`** — bisimulation and the COINDUCTION PRINCIPLE: every
    bisimulation is contained in observational equality (bisimulation-is-equality, the coinductive proof
    method).  **`observationallyEqual_isBisimulation`** — observational equality is itself a bisimulation,
    so it is the LARGEST one (the bisimilarity).
  * **`structureCoalgebra`** + **`ana_structureCoalgebra`** — `FinalStream` is its own coalgebra, and `ana`
    of that structure is the identity (up to bisimulation): the terminal object mediates itself, the
    op-dual of `mediate_selfCocone`.

## Zero-axiom verification

A pair of one-field/two-field structures, structural `Nat` recursion (`iterate`, `ana`), `rfl`
co-structure laws, and three `Nat` inductions (`ana_unique`, `bisim_observe`, `ana_structureCoalgebra`)
generalised over the stream/state.  No funext, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TermTerminalCoalgebra.lean`.
-/

namespace FX1Poly.Core

/-- The **terminal coalgebra** of the stream functor `X ↦ A × X`, represented as the observation function
`Nat → A`: `observe n` is the value seen after `n` destructor steps.  This is the standard model of the
final coalgebra (Lean 4 core has no `coinductive` declaration). -/
structure FinalStream (A : Type) where
  /-- The `n`-th observation of the stream. -/
  observe : Nat → A

/-- The **head** observation (the `A`-component of the coalgebra structure map). -/
def FinalStream.head {A : Type} (stream : FinalStream A) : A :=
  stream.observe 0

/-- The **tail** (the `FinalStream A`-component of the coalgebra structure map): drop one observation. -/
def FinalStream.tail {A : Type} (stream : FinalStream A) : FinalStream A :=
  ⟨fun index => stream.observe (index + 1)⟩

/-- A **source coalgebra** for the stream functor: a carrier with a structure map
`Carrier → A × Carrier` split into the observation `out` and the transition `next`.  The op-dual of
`term-1`'s `CarrierAlgebra`. -/
structure StreamCoalgebra (Carrier : Type) (A : Type) where
  /-- The observation emitted at the current state. -/
  out : Carrier → A
  /-- The transition to the next state. -/
  next : Carrier → Carrier

/-- Iterate the transition `next` a given number of times (peeling from the front:
`iterate (n+1) state = iterate n (next state)`). -/
def StreamCoalgebra.iterate {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A) :
    Nat → Carrier → Carrier
  | 0, state => state
  | step + 1, state => coalgebra.iterate step (coalgebra.next state)

/-- ★ **The anamorphism (corecursion).**  The unique-up-to-bisimulation coalgebra morphism from a source
coalgebra INTO the terminal coalgebra: the `n`-th observation is the `out` of the state after `n`
transitions.  The op-dual of `term-1`'s `cata`. -/
def StreamCoalgebra.ana {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    (state : Carrier) : FinalStream A :=
  ⟨fun index => coalgebra.out (coalgebra.iterate index state)⟩

/-- **Coalgebra-homomorphism law (head).**  `ana` sends the head observation to the source's `out` — the
op-dual of `term-1`'s `onGen` head case; holds by `rfl`. -/
theorem StreamCoalgebra.ana_head {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    (state : Carrier) :
    (coalgebra.ana state).head = coalgebra.out state := rfl

/-- ★ **Coalgebra-homomorphism law (tail) — the co-triangle.**  Observing the tail of `ana state` agrees
with `ana` of the next state: corecursion commutes with the destructor.  Stated OBSERVATIONALLY
(funext-free); holds by `rfl` at every index. -/
theorem StreamCoalgebra.ana_tail {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    (state : Carrier) (index : Nat) :
    ((coalgebra.ana state).tail).observe index
      = (coalgebra.ana (coalgebra.next state)).observe index := rfl

/-- A **coalgebra homomorphism** into the terminal coalgebra: a candidate map `Carrier → FinalStream A`
commuting with the observations (head + tail, the latter observationally).  The op-dual of `term-1`'s
`IsCarrierHomomorphism`. -/
structure IsStreamCoalgebraHom {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    (candidate : Carrier → FinalStream A) : Prop where
  /-- The candidate's head is the source observation. -/
  headLaw : ∀ state, (candidate state).head = coalgebra.out state
  /-- The candidate's tail observes as the candidate of the next state. -/
  tailLaw : ∀ state index,
    ((candidate state).tail).observe index = (candidate (coalgebra.next state)).observe index

/-- **Existence: `ana` is a coalgebra homomorphism.**  Both observation laws hold by `rfl`, so `ana`
witnesses `IsStreamCoalgebraHom` — existence to pair with the terminality uniqueness below.  The op-dual
of `term-1`'s `cataHomomorphism`. -/
theorem StreamCoalgebra.ana_isHom {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A) :
    IsStreamCoalgebraHom coalgebra coalgebra.ana where
  headLaw := fun _state => rfl
  tailLaw := fun _state _index => rfl

/-- ★ **Terminality (uniqueness up to bisimulation).**  Any coalgebra homomorphism into the terminal
coalgebra agrees with `ana` at every observation — `ana` is THE morphism, unique up to bisimulation.  The
op-dual of `IsCarrierHomomorphism.unique`.  Proved by induction on the observation index, peeling head/tail
through the homomorphism laws. -/
theorem StreamCoalgebra.ana_unique {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    {candidate : Carrier → FinalStream A} (isHom : IsStreamCoalgebraHom coalgebra candidate) :
    ∀ (index : Nat) (state : Carrier),
      (candidate state).observe index = (coalgebra.ana state).observe index := by
  intro index
  induction index with
  | zero =>
    intro state
    exact isHom.headLaw state
  | succ previous inductionHypothesis =>
    intro state
    exact (isHom.tailLaw state previous).trans (inductionHypothesis (coalgebra.next state))

/-- A **bisimulation** on the terminal coalgebra: a relation closed under the observations — related
streams have equal heads and related tails.  The relational proof method for coinductive equality. -/
def IsBisimulation {A : Type} (related : FinalStream A → FinalStream A → Prop) : Prop :=
  ∀ {first second : FinalStream A}, related first second →
    first.head = second.head ∧ related first.tail second.tail

/-- ★ **The coinduction principle: bisimulation is observational equality.**  Every bisimulation is
contained in observational equality — to prove two streams equal at every observation, exhibit a
bisimulation relating them.  Proved by induction on the observation index. -/
theorem FinalStream.bisim_observe {A : Type} {related : FinalStream A → FinalStream A → Prop}
    (isBisimulation : IsBisimulation related) :
    ∀ (index : Nat) {first second : FinalStream A}, related first second →
      first.observe index = second.observe index := by
  intro index
  induction index with
  | zero =>
    intro _first _second isRelated
    exact (isBisimulation isRelated).left
  | succ previous inductionHypothesis =>
    intro _first _second isRelated
    exact inductionHypothesis (isBisimulation isRelated).right

/-- Two streams are **observationally equal** when they agree at every observation (the funext-free
stand-in for stream equality). -/
def FinalStream.observationallyEqual {A : Type} (first second : FinalStream A) : Prop :=
  ∀ index, first.observe index = second.observe index

/-- Observational equality is itself a bisimulation — so, with `bisim_observe`, it is the LARGEST
bisimulation: the bisimilarity. -/
theorem FinalStream.observationallyEqual_isBisimulation {A : Type} :
    IsBisimulation (A := A) FinalStream.observationallyEqual := by
  intro first second areObservationallyEqual
  exact ⟨areObservationallyEqual 0, fun index => areObservationallyEqual (index + 1)⟩

/-- The terminal coalgebra carries its OWN coalgebra structure (`head` / `tail`) — the structure map of
the final coalgebra. -/
def FinalStream.structureCoalgebra (A : Type) : StreamCoalgebra (FinalStream A) A where
  out := FinalStream.head
  next := FinalStream.tail

/-- ★ **The terminal object mediates itself.**  `ana` of `FinalStream`'s own structure coalgebra is the
identity (up to bisimulation): every stream is observationally equal to its own anamorphic image.  The
op-dual of `mediate_selfCocone` — confirming `FinalStream` is genuinely terminal. -/
theorem FinalStream.ana_structureCoalgebra {A : Type} :
    ∀ (index : Nat) (stream : FinalStream A),
      ((FinalStream.structureCoalgebra A).ana stream).observe index = stream.observe index := by
  intro index
  induction index with
  | zero =>
    intro _stream
    rfl
  | succ previous inductionHypothesis =>
    intro stream
    exact inductionHypothesis stream.tail

end FX1Poly.Core
