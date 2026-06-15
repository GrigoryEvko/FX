import FX1Poly.Tier0.Context.Context

/-! # The modal lock `◐_μ` + LOCK 2-functoriality (`context-4`, the context-side residue)

`context-0` shipped the context-axis bundle `ContextAxis` with an ABSTRACT lock slot
`lockOn : Modality → RawEndofunctor substMode` (`Context.lean`) — each modality `μ` is meant to act
on the context category by a lock `◐_μ`, an endofunctor, the trivial mode wiring it to
`RawEndofunctor.identity`.  `context-4`'s job is to fill that slot with the genuine modal-CwF lock
structure: the lock `◐_μ`, its **2-functoriality** (`◐_id ≅ id`, `◐_(ν∘μ) ≅ ◐_μ ∘ ◐_ν`, keys from
2-cells), and the **dependent right adjoint** `⟨μ | −⟩`.

## The honest `×mode` / `.context` split

The task is annotated `⟦→CORE/ ×mode · fib-3⟧`: the cross-axis part — the FAMILY `μ ↦ ◐_μ` indexed by
a mode 2-category `M`, the 2-functor `M^coop → End(𝒞)`, the keys read off `M`'s 2-cells, and the
mode-relative metatheory (Gratzer: `Conv`-decidability = mode-decidability) — needs `Tier0/ModeOmega`
and is deferred to `fib-3`.  What the CONTEXT axis owns OUTRIGHT, and what lands here, is the TARGET
of that mode 2-functor: the structure a lock IS, independent of any mode theory.

  * the lock CARRIER is `RawEndofunctor` (exactly the type `ContextAxis.lockOn` already returns);
  * locks COMPOSE and have an IDENTITY — the strict monoid / one-object 2-category `End(𝒞)` in which
    `LOCK` 2-functoriality lives — and that is what this file ships.

## What lands here (Layer A — all zero-axiom)

  * `RawEndofunctor.compose` — composition of locks (the gap `context-0` flagged: needed for
    `◐_(ν∘μ) = ◐_μ ∘ ◐_ν`), with both functor laws PROVED.
  * `RawEndofunctor.identity_compose` / `compose_identity` / `compose_assoc` — the three
    STRICT monoid laws on locks (the strict 2-functoriality target); `End(𝒞)` is a genuine monoid.
  * `RawEndofunctorTransformation` — the generic natural transformation between two locks (the only
    nat-trans shipped so far, `SliceNatTrans`, is slice-specialised).  These are the **keys**: a
    2-cell `μ ⇒ ν` will map to a `RawEndofunctorTransformation ◐_ν ◐_μ`.
  * `RawEndofunctorTransformation.identity` / `vcomp` (+ the componentwise unit laws) — the vertical
    2-cell structure on keys, naturality squares PROVED.

The dependent right adjoint `⟨μ|−⟩` (the adjunction abstraction + recognising the shipped
comprehension as a DRA) and the concrete locks on `fxBaseSubstCategory` land in the following
increments; the `×mode` family and the type-indexed DRA over `Core/` stay deferred to `fib-3`.

Zero external dependencies.  Raw Lean 4 + Init only.  No `funext` (nat-trans laws are stated
componentwise), no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Tier0

universe u v

/-! ## Composition of locks — the monoid `End(𝒞)` -/

/-- **Composition of locks.**  `firstFunctor.compose secondFunctor` applies `firstFunctor` then
`secondFunctor` (DIAGRAMMATIC order, matching `RawCategory.compose`): on objects it is
`secondFunctor.mapObject ∘ firstFunctor.mapObject`.  This is the operation `LOCK` 2-functoriality
needs — `◐_(ν∘μ) = ◐_μ ∘ ◐_ν` — and the gap `context-0` left open next to `RawEndofunctor.identity`. -/
def RawEndofunctor.compose {category : RawCategory.{u, v}}
    (firstFunctor secondFunctor : RawEndofunctor category) : RawEndofunctor category where
  mapObject := fun object => secondFunctor.mapObject (firstFunctor.mapObject object)
  mapMorphism := fun morphism => secondFunctor.mapMorphism (firstFunctor.mapMorphism morphism)
  preservesIdentity := fun objectA => by
    rw [firstFunctor.preservesIdentity, secondFunctor.preservesIdentity]
  preservesComposition := fun morphismF morphismG => by
    rw [firstFunctor.preservesComposition, secondFunctor.preservesComposition]

/-- **Left identity law for locks.**  The identity lock is a left unit for composition — the
trivial-mode lock `◐_id` precomposed is invisible.  Strict (holds on the nose by `RawEndofunctor`
eta), not merely up to natural iso. -/
theorem RawEndofunctor.identity_compose {category : RawCategory.{u, v}}
    (functor : RawEndofunctor category) :
    (RawEndofunctor.identity category).compose functor = functor := rfl

/-- **Right identity law for locks.**  The identity lock is a right unit for composition. -/
theorem RawEndofunctor.compose_identity {category : RawCategory.{u, v}}
    (functor : RawEndofunctor category) :
    functor.compose (RawEndofunctor.identity category) = functor := rfl

/-- **Associativity of lock composition.**  `(◐ ∘ ◐') ∘ ◐'' = ◐ ∘ (◐' ∘ ◐'')` — strict.  Together
with the two identity laws, `End(𝒞)` (the locks on the context category) is a genuine MONOID: the
one-object strict 2-category in which `LOCK` 2-functoriality takes values. -/
theorem RawEndofunctor.compose_assoc {category : RawCategory.{u, v}}
    (firstFunctor secondFunctor thirdFunctor : RawEndofunctor category) :
    (firstFunctor.compose secondFunctor).compose thirdFunctor
      = firstFunctor.compose (secondFunctor.compose thirdFunctor) := rfl

/-! ## Natural transformations between locks — the keys (2-cells) -/

/-- A **natural transformation between two locks** — the generic endofunctor nat-trans (the shipped
`SliceNatTrans` is slice-specialised).  These are the **keys** of `LOCK` 2-functoriality: a mode
2-cell `α : μ ⇒ ν` will map to a `RawEndofunctorTransformation ◐_ν ◐_μ` (that mode-indexed read-off
is the `×mode` part, `fib-3`).  The naturality square is stated in the category's diagrammatic order,
matching `SliceNatTrans`. -/
structure RawEndofunctorTransformation {category : RawCategory.{u, v}}
    (sourceFunctor targetFunctor : RawEndofunctor category) where
  /-- The component at each object: a morphism `◐(object) ⟶ ◐'(object)`. -/
  component : (object : category.Object) →
    category.Morphism (sourceFunctor.mapObject object) (targetFunctor.mapObject object)
  /-- NATURALITY: the component commutes with both locks' action on every morphism. -/
  naturality : ∀ {objectA objectB : category.Object}
      (morphism : category.Morphism objectA objectB),
    category.compose (sourceFunctor.mapMorphism morphism) (component objectB) =
      category.compose (component objectA) (targetFunctor.mapMorphism morphism)

/-- The identity key on a lock — component is the identity morphism, naturality from the two unit
laws. -/
def RawEndofunctorTransformation.identity {category : RawCategory.{u, v}}
    (functor : RawEndofunctor category) :
    RawEndofunctorTransformation functor functor where
  component := fun object => category.identity (functor.mapObject object)
  naturality := fun {objectA objectB} morphism => by
    show category.compose (functor.mapMorphism morphism)
        (category.identity (functor.mapObject objectB))
      = category.compose (category.identity (functor.mapObject objectA))
        (functor.mapMorphism morphism)
    rw [category.identityRight, category.identityLeft]

/-- **Vertical composition of keys** — compose the components; the naturality square is the two
component squares pasted along associativity. -/
def RawEndofunctorTransformation.vcomp {category : RawCategory.{u, v}}
    {sourceFunctor middleFunctor targetFunctor : RawEndofunctor category}
    (firstKey : RawEndofunctorTransformation sourceFunctor middleFunctor)
    (secondKey : RawEndofunctorTransformation middleFunctor targetFunctor) :
    RawEndofunctorTransformation sourceFunctor targetFunctor where
  component := fun object =>
    category.compose (firstKey.component object) (secondKey.component object)
  naturality := fun {objectA objectB} morphism => by
    show category.compose (sourceFunctor.mapMorphism morphism)
        (category.compose (firstKey.component objectB) (secondKey.component objectB))
      = category.compose
        (category.compose (firstKey.component objectA) (secondKey.component objectA))
        (targetFunctor.mapMorphism morphism)
    rw [← category.composeAssoc, firstKey.naturality morphism, category.composeAssoc,
        secondKey.naturality morphism, ← category.composeAssoc]

/-- The identity key acts as the identity component. -/
theorem RawEndofunctorTransformation.identity_component {category : RawCategory.{u, v}}
    (functor : RawEndofunctor category) (object : category.Object) :
    (RawEndofunctorTransformation.identity functor).component object
      = category.identity (functor.mapObject object) := rfl

/-- Vertical composition acts componentwise. -/
theorem RawEndofunctorTransformation.vcomp_component {category : RawCategory.{u, v}}
    {sourceFunctor middleFunctor targetFunctor : RawEndofunctor category}
    (firstKey : RawEndofunctorTransformation sourceFunctor middleFunctor)
    (secondKey : RawEndofunctorTransformation middleFunctor targetFunctor)
    (object : category.Object) :
    (firstKey.vcomp secondKey).component object
      = category.compose (firstKey.component object) (secondKey.component object) := rfl

/-- Left unit law for keys, componentwise (the global functor-2-category equation would need
`funext`; stated pointwise to stay zero-axiom, matching `SliceNatTrans`). -/
theorem RawEndofunctorTransformation.identity_vcomp_component {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor)
    (object : category.Object) :
    ((RawEndofunctorTransformation.identity sourceFunctor).vcomp key).component object
      = key.component object :=
  category.identityLeft (key.component object)

/-- Right unit law for keys, componentwise. -/
theorem RawEndofunctorTransformation.vcomp_identity_component {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor)
    (object : category.Object) :
    (key.vcomp (RawEndofunctorTransformation.identity targetFunctor)).component object
      = key.component object :=
  category.identityRight (key.component object)

end FX1Poly.Tier0
