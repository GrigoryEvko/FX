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
  * **`cons`** + **`head_cons` / `tail_cons` / `cons_head_tail`** — the stream CONSTRUCTOR and LAMBEK's
    lemma: the structure map `⟨head, tail⟩` and `cons` are mutually inverse, so `FinalStream A` is a
    FIXPOINT of the functor (`FinalStream A ≅ A × FinalStream A`) — the op-dual of "the initial algebra's
    constructor is an iso".
  * **`StreamCoalgebra Carrier A`** — a source coalgebra `Carrier → A × Carrier` (`out` / `next`); the
    op-dual of `term-1`'s `CarrierAlgebra`.
  * **`StreamCoalgebra.ana`** — the ANAMORPHISM (corecursion): the coalgebra morphism FROM the source
    INTO the terminal coalgebra; the op-dual of `cata`.
  * **`ana_head` / `ana_tail`** + **`ana_isHom`** — the coalgebra-HOMOMORPHISM laws: `ana` commutes with
    the observations (the op-dual of `term-1`'s `onGen` / `term-2`'s universal triangle), so `ana` IS a
    coalgebra hom (existence).
  * **`ana_unique`** — TERMINALITY: any coalgebra hom into `FinalStream` agrees with `ana` up to
    bisimulation (the op-dual of `IsCarrierHomomorphism.unique`).  **`ana_fusion`** — anamorphism fusion
    over a coalgebra morphism (the op-dual of cata fusion; the UP is functorial).  **`coalgebraHom_ext`**
    — two homs out of the same coalgebra agree (the op-dual of `carrier_hom_ext`).
  * **`IsBisimulation`** + **`bisim_observe`** — bisimulation and the COINDUCTION PRINCIPLE: every
    bisimulation is contained in observational equality (bisimulation-is-equality, the coinductive proof
    method).  **`observationallyEqual_isBisimulation`** — observational equality is itself a bisimulation,
    so it is the LARGEST one (the bisimilarity).
  * **`structureCoalgebra`** + **`ana_structureCoalgebra`** — `FinalStream` is its own coalgebra, and `ana`
    of that structure is the identity (up to bisimulation): the terminal object mediates itself, the
    op-dual of `mediate_selfCocone`.
  * **`constStream`** + **`constStream_observe` / `constStream_unfold`** — a concrete computing witness:
    corecursion produces a genuine infinite object that computes (`observe = value`) and satisfies its
    codata unfold equation `s ~ cons value s`.

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

/-- The **stream constructor** (`cons`): prepend an observation.  The other half of the codata interface
(the destructors are `head` / `tail`) and the inverse of the coalgebra structure map (Lambek below). -/
def FinalStream.cons {A : Type} (first : A) (rest : FinalStream A) : FinalStream A :=
  ⟨fun index => match index with | 0 => first | previous + 1 => rest.observe previous⟩

/-- Head of a `cons` recovers the prepended observation (by `rfl`). -/
theorem FinalStream.head_cons {A : Type} (first : A) (rest : FinalStream A) :
    (FinalStream.cons first rest).head = first := rfl

/-- Tail of a `cons` recovers the rest (observationally, by `rfl`). -/
theorem FinalStream.tail_cons {A : Type} (first : A) (rest : FinalStream A) (index : Nat) :
    ((FinalStream.cons first rest).tail).observe index = rest.observe index := rfl

/-- ★ **Lambek's lemma (the fixpoint property).**  Destructing then reconstructing is the identity (up
to observation): `cons (head s) (tail s)` agrees with `s` at every observation.  With `head_cons` /
`tail_cons`, the coalgebra structure map `⟨head, tail⟩` and `cons` are mutually inverse — so
`FinalStream A` is a FIXPOINT of the stream functor `X ↦ A × X` (`FinalStream A ≅ A × FinalStream A`).
The op-dual of "the initial algebra's constructor is an isomorphism". -/
theorem FinalStream.cons_head_tail {A : Type} (stream : FinalStream A) (index : Nat) :
    (FinalStream.cons stream.head stream.tail).observe index = stream.observe index := by
  cases index with
  | zero => rfl
  | succ _previous => rfl

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

/-- ★ **Anamorphism fusion.**  A coalgebra MORPHISM `morphism` (commuting with `out` and `next`) fuses
into the anamorphism: `ana` of the source agrees with `ana` of the target precomposed with `morphism`.
The op-dual of catamorphism fusion; follows from terminality (`ana_unique`), demonstrating the universal
property is functorial in the source coalgebra. -/
theorem StreamCoalgebra.ana_fusion {SourceCarrier TargetCarrier A : Type}
    (source : StreamCoalgebra SourceCarrier A) (target : StreamCoalgebra TargetCarrier A)
    (morphism : SourceCarrier → TargetCarrier)
    (preservesOut : ∀ state, target.out (morphism state) = source.out state)
    (preservesNext : ∀ state, morphism (source.next state) = target.next (morphism state)) :
    ∀ (index : Nat) (state : SourceCarrier),
      (source.ana state).observe index = (target.ana (morphism state)).observe index := by
  have isHom : IsStreamCoalgebraHom source (fun state => target.ana (morphism state)) :=
    { headLaw := fun state => (target.ana_head (morphism state)).trans (preservesOut state)
      tailLaw := fun state position => by
        rw [target.ana_tail (morphism state) position, preservesNext state] }
  intro index state
  exact (source.ana_unique isHom index state).symm

/-- **Coalgebra-homomorphism extensionality.**  Two coalgebra homomorphisms out of the SAME source
coalgebra agree at every observation — both equal `ana` by terminality.  The op-dual of `term-1`'s
`carrier_hom_ext`. -/
theorem StreamCoalgebra.coalgebraHom_ext {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
    {first second : Carrier → FinalStream A}
    (firstIsHom : IsStreamCoalgebraHom coalgebra first)
    (secondIsHom : IsStreamCoalgebraHom coalgebra second) :
    ∀ (index : Nat) (state : Carrier),
      (first state).observe index = (second state).observe index :=
  fun index state =>
    (coalgebra.ana_unique firstIsHom index state).trans
      (coalgebra.ana_unique secondIsHom index state).symm

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

/-! ## A concrete computing witness — corecursion produces a genuine infinite object -/

/-- The **constant stream** built by the anamorphism from a one-state coalgebra (`out` is constant,
`next` loops).  A concrete inhabitant of the terminal coalgebra demonstrating `ana` is non-vacuous. -/
def FinalStream.constStream {A : Type} (value : A) : FinalStream A :=
  (⟨fun _ => value, fun _ => ()⟩ : StreamCoalgebra Unit A).ana ()

/-- The constant stream computes: every observation is `value` (by `rfl` — corecursion reduces). -/
theorem FinalStream.constStream_observe {A : Type} (value : A) (index : Nat) :
    (FinalStream.constStream value).observe index = value := rfl

/-- ★ The constant stream satisfies its corecursive UNFOLD equation `s ~ cons value s` — a concrete
demonstration that the anamorphism produces a genuine FIXPOINT of `s ↦ cons value s`, computing through
the `cons` constructor. -/
theorem FinalStream.constStream_unfold {A : Type} (value : A) (index : Nat) :
    (FinalStream.constStream value).observe index
      = (FinalStream.cons value (FinalStream.constStream value)).observe index := by
  cases index with
  | zero => rfl
  | succ _previous => rfl

end FX1Poly.Core
