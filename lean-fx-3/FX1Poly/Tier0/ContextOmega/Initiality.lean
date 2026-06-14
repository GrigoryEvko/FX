import FX1Poly.Tier0.ContextOmega.ModalLock

/-! # Tier0/ContextOmega/Initiality — the syntactic context category is the initial context-algebra (context-5)

The initiality half of the context ω-category: "the syntactic CwF is the initial CwF".  A CwF morphism
out of the syntactic CwF is determined by where it sends the empty context and how it acts on context
extension — and it is UNIQUE.  The full statement (morphism action on substitutions + the type/term
layers + uniqueness of the whole CwF-morphism) is the QIIT recursor over intrinsic syntax and is
funext-blocked for uniqueness (see the honest boundary).  This module ships the cleanly-provable,
zero-axiom CORE of that initiality: the **object level**.

## The object-level universal property = Lawvere's natural-numbers object

The objects of the FX context category `fxBaseSubstCategory` are scopes (`Nat`); the empty context is
`0` and context extension is the lock `◐ : scope ↦ scope + 1` (context-4).  So the context objects are
exactly the FREE structure on a point (`empty`) closed under one endo-operation (`extend`) — i.e. the
initial `ContextAlgebra`, which is Lawvere's natural-numbers object.  Its universal property:

  * `ContextAlgebra` — the object-level data any model supplies: a carrier, an `empty` element, and an
    `extend` endo-operation.
  * `interpretScope` — THE map from scopes into any context-algebra: `0 ↦ empty`, `n+1 ↦ extend (…n)`.
    Structural `Nat.rec` (constant-motive, propext-free).
  * ★ `interpretScope_unique` — any algebra map IS `interpretScope`.  This is OBJECT-LEVEL INITIALITY,
    proved zero-axiom by `Nat` induction.  (Contrast: the functor/substitution-level uniqueness would
    compare whole functor families and needs funext — off the zero-axiom path.)
  * `interpretScope_syntactic_id` — interpreting the syntactic contexts back into THEMSELVES along the
    lock is the identity: the self-initiality fixed point.

## Honest boundary (recorded, not faked)

The FULL CwF-initiality — a unique CwF-morphism into ANY category-with-families, acting on
substitutions, types, and terms — needs the recursor of the intrinsic-syntax QIIT, and its uniqueness
compares whole functor / natural-transformation families (the `morphismMap` of context-4's
`RawEndofunctor`, the `component` of a `SubstFamilyMap`), which are infinite function families →
`funext` = `Quot.sound`-derived, OFF the zero-axiom path (the same boundary as context-3/4's adjoint
hom-bijections).  What IS zero-axiom is the object skeleton: the context category's objects are the
initial context-algebra, with `Nat.rec` as the unique interpretation and `Nat`-induction uniqueness.

## Zero-axiom verification

`interpretScope` is `Nat.rec` at a constant motive; its computation rules are `rfl`; `interpretScope_unique`
is `Nat` induction (`Nat.rec` at an equality motive) closed by `rw`; the self-identity is the uniqueness
theorem applied to `id` (the lock's object map IS `+1`, `dimensionLock_objectMap`).  No `funext`, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

universe u

/-! ## The object-level context algebra (the natural-numbers object) -/

/-- **A context algebra** — the OBJECT-level data any CwF model provides for interpreting contexts: a
carrier of objects, the `empty` context, and a context-`extend` operation.  The FX context category's
objects (scopes) form the INITIAL such algebra. -/
structure ContextAlgebra where
  /-- The carrier of context objects. -/
  Object : Type u
  /-- The empty context. -/
  empty : Object
  /-- Context extension by one variable. -/
  extend : Object → Object

/-- **The unique algebra map from scopes into any context algebra.**  Interpret the empty context `0`
as `empty` and an extended context `n+1` as `extend` of the interpretation of `n` — structural
`Nat.rec` at the constant motive `alg.Object`. -/
def ContextAlgebra.interpretScope (alg : ContextAlgebra) : Nat → alg.Object :=
  fun scope => Nat.rec alg.empty (fun _priorScope priorInterpretation => alg.extend priorInterpretation) scope

/-- The interpretation of the empty context is the algebra's `empty`. -/
theorem ContextAlgebra.interpretScope_zero (alg : ContextAlgebra) :
    alg.interpretScope 0 = alg.empty := rfl

/-- The interpretation of an extended context is `extend` of the interpretation. -/
theorem ContextAlgebra.interpretScope_succ (alg : ContextAlgebra) (scope : Nat) :
    alg.interpretScope (scope + 1) = alg.extend (alg.interpretScope scope) := rfl

/-- ★ **Object-level initiality.**  Any map `candidate` from scopes into the algebra that respects the
empty context and extension IS the canonical interpretation — the universal property exhibiting the
syntactic context objects as the INITIAL context-algebra (Lawvere's natural-numbers object).  Proved
zero-axiom by `Nat` induction. -/
theorem ContextAlgebra.interpretScope_unique (alg : ContextAlgebra) (candidate : Nat → alg.Object)
    (mapsEmpty : candidate 0 = alg.empty)
    (mapsExtend : ∀ scope : Nat, candidate (scope + 1) = alg.extend (candidate scope)) :
    ∀ scope : Nat, candidate scope = alg.interpretScope scope := by
  intro scope
  induction scope with
  | zero => exact mapsEmpty
  | succ priorScope priorEquation =>
      show candidate (priorScope + 1) = alg.extend (alg.interpretScope priorScope)
      rw [mapsExtend priorScope, priorEquation]

/-! ## The syntactic self-interpretation -/

/-- **The syntactic context category AS a context algebra.**  Carrier = scopes (`Nat`), empty context
= `0`, extension = the modal lock's object map `◐ : scope ↦ scope + 1` (context-4). -/
def syntacticContextAlgebra : ContextAlgebra where
  Object := Nat
  empty := 0
  extend := dimensionLock.objectMap

/-- **Self-initiality.**  Interpreting the syntactic contexts back into themselves (along the lock) is
the identity on scopes — the unique endo-interpretation fixing the empty context and extension is the
identity.  Via `interpretScope_unique` applied to `id` (the lock's object map IS `+1`). -/
theorem interpretScope_syntactic_id (scope : Nat) :
    syntacticContextAlgebra.interpretScope scope = scope :=
  (ContextAlgebra.interpretScope_unique syntacticContextAlgebra (fun selfScope => selfScope)
    rfl (fun priorScope => (dimensionLock_objectMap priorScope).symm) scope).symm

end FX1Poly.Tier0.ContextOmega
