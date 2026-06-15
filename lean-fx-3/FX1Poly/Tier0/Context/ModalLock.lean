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

/-! ## The dependent right adjoint — a lock and its modal type former

A modal lock `◐_μ` is the LEFT adjoint of an adjunction; the modal type former `⟨μ | −⟩` is its
RIGHT adjoint — the **dependent right adjoint** (BCMMSV 2020).  At the context level (independent of
any mode theory) this is a plain adjunction of context endofunctors, stated in the natural
hom-bijection form `Hom(◐ a, b) ≅ Hom(a, ⟨b⟩)` (the funext-free shape, matching the shipped
comprehension `Bijection`).  The genuinely DEPENDENT (type-family) upgrade over the `Core/` type
fibration is the `×mode` deliverable, `fib-3`. -/

/-- An ADJUNCTION between two locks, `leftAdjoint ⊣ rightAdjoint` — the lock `◐_μ` as left adjoint
and its dependent right adjoint `⟨μ|−⟩` as right adjoint.  Given as the natural transpose bijection
`Hom(◐ a, b) ≅ Hom(a, ⟨b⟩)`: `transposeRight`/`transposeLeft` are mutually inverse and natural in both
arguments (the two naturality squares are stated on the `transposeRight` side; the `transposeLeft`
side follows). -/
structure IsEndoAdjunction {category : RawCategory.{u, v}}
    (leftAdjoint rightAdjoint : RawEndofunctor category) where
  /-- Transpose a map `◐ a ⟶ b` to its adjunct `a ⟶ ⟨b⟩`. -/
  transposeRight : {objectA objectB : category.Object} →
    category.Morphism (leftAdjoint.mapObject objectA) objectB →
    category.Morphism objectA (rightAdjoint.mapObject objectB)
  /-- Transpose a map `a ⟶ ⟨b⟩` back to `◐ a ⟶ b` — the inverse direction. -/
  transposeLeft : {objectA objectB : category.Object} →
    category.Morphism objectA (rightAdjoint.mapObject objectB) →
    category.Morphism (leftAdjoint.mapObject objectA) objectB
  /-- `transposeLeft ∘ transposeRight = id` — the bijection's first round-trip. -/
  transposeLeft_transposeRight : ∀ {objectA objectB : category.Object}
      (morphism : category.Morphism (leftAdjoint.mapObject objectA) objectB),
    transposeLeft (transposeRight morphism) = morphism
  /-- `transposeRight ∘ transposeLeft = id` — the bijection's second round-trip. -/
  transposeRight_transposeLeft : ∀ {objectA objectB : category.Object}
      (morphism : category.Morphism objectA (rightAdjoint.mapObject objectB)),
    transposeRight (transposeLeft morphism) = morphism
  /-- NATURALITY in the domain: reindexing the source commutes with the transpose. -/
  transposeRight_natural_left : ∀ {sourceA objectA objectB : category.Object}
      (reindex : category.Morphism sourceA objectA)
      (morphism : category.Morphism (leftAdjoint.mapObject objectA) objectB),
    transposeRight (category.compose (leftAdjoint.mapMorphism reindex) morphism)
      = category.compose reindex (transposeRight morphism)
  /-- NATURALITY in the codomain: postcomposing the target commutes with the transpose. -/
  transposeRight_natural_right : ∀ {objectA objectB targetB : category.Object}
      (morphism : category.Morphism (leftAdjoint.mapObject objectA) objectB)
      (after : category.Morphism objectB targetB),
    transposeRight (category.compose morphism after)
      = category.compose (transposeRight morphism) (rightAdjoint.mapMorphism after)

/-- The IDENTITY adjunction — the identity lock is its own dependent right adjoint (`◐_id ⊣ ⟨id⟩`,
both the identity endofunctor), the transpose being the identity on morphisms. -/
def IsEndoAdjunction.identity (category : RawCategory.{u, v}) :
    IsEndoAdjunction (RawEndofunctor.identity category) (RawEndofunctor.identity category) where
  transposeRight := fun morphism => morphism
  transposeLeft := fun morphism => morphism
  transposeLeft_transposeRight := fun _ => rfl
  transposeRight_transposeLeft := fun _ => rfl
  transposeRight_natural_left := fun _ _ => rfl
  transposeRight_natural_right := fun _ _ => rfl

/-- **Composition of adjunctions.**  `L ⊣ R` and `L' ⊣ R'` compose to `(◐ then ◐') ⊣ (⟨R'⟩ then ⟨R⟩)`
— note the dependent right adjoints compose in the OPPOSITE order: this contravariance is exactly
`LOCK` 2-functoriality `◐_(ν∘μ) = ◐_μ ∘ ◐_ν` carried on the type-former side.  The transpose of the
composite is the composite of transposes; the round-trips and naturality squares paste. -/
def IsEndoAdjunction.compose {category : RawCategory.{u, v}}
    {leftFirst rightFirst leftSecond rightSecond : RawEndofunctor category}
    (firstAdjunction : IsEndoAdjunction leftFirst rightFirst)
    (secondAdjunction : IsEndoAdjunction leftSecond rightSecond) :
    IsEndoAdjunction (leftFirst.compose leftSecond) (rightSecond.compose rightFirst) where
  transposeRight := fun morphism =>
    firstAdjunction.transposeRight (secondAdjunction.transposeRight morphism)
  transposeLeft := fun morphism =>
    secondAdjunction.transposeLeft (firstAdjunction.transposeLeft morphism)
  transposeLeft_transposeRight := fun morphism => by
    rw [firstAdjunction.transposeLeft_transposeRight,
        secondAdjunction.transposeLeft_transposeRight]
  transposeRight_transposeLeft := fun morphism => by
    rw [secondAdjunction.transposeRight_transposeLeft,
        firstAdjunction.transposeRight_transposeLeft]
  transposeRight_natural_left := fun reindex morphism => by
    show firstAdjunction.transposeRight (secondAdjunction.transposeRight
          (category.compose (leftSecond.mapMorphism (leftFirst.mapMorphism reindex)) morphism))
        = category.compose reindex
            (firstAdjunction.transposeRight (secondAdjunction.transposeRight morphism))
    rw [secondAdjunction.transposeRight_natural_left (leftFirst.mapMorphism reindex) morphism,
        firstAdjunction.transposeRight_natural_left reindex
          (secondAdjunction.transposeRight morphism)]
  transposeRight_natural_right := fun morphism after => by
    show firstAdjunction.transposeRight (secondAdjunction.transposeRight
          (category.compose morphism after))
        = category.compose
            (firstAdjunction.transposeRight (secondAdjunction.transposeRight morphism))
            (rightFirst.mapMorphism (rightSecond.mapMorphism after))
    rw [secondAdjunction.transposeRight_natural_right morphism after,
        firstAdjunction.transposeRight_natural_right (secondAdjunction.transposeRight morphism)
          (rightSecond.mapMorphism after)]

/-- **A modal lock with its dependent right adjoint.**  The data `context-4` slots into
`ContextAxis.lockOn`: a lock endofunctor `◐_μ`, the modal type former `⟨μ|−⟩` as its dependent right
adjoint, and the adjunction tying them.  At the trivial modality this is `identity`; the
mode-indexed family `μ ↦ ◐_μ` is the `×mode` deliverable (`fib-3`). -/
structure ContextLock (category : RawCategory.{u, v}) where
  /-- The lock endofunctor `◐_μ` (the left adjoint). -/
  lock : RawEndofunctor category
  /-- The modal type former `⟨μ|−⟩` (the dependent right adjoint). -/
  dependentRightAdjoint : RawEndofunctor category
  /-- The adjunction `◐_μ ⊣ ⟨μ|−⟩`. -/
  adjunction : IsEndoAdjunction lock dependentRightAdjoint

/-- The IDENTITY lock `◐_id` — the trivial-mode lock (exactly what `fxContextAxis.lockOn` wires),
self-adjoint. -/
def ContextLock.identity (category : RawCategory.{u, v}) : ContextLock category where
  lock := RawEndofunctor.identity category
  dependentRightAdjoint := RawEndofunctor.identity category
  adjunction := IsEndoAdjunction.identity category

/-- **Composition of locks** — `◐_μ` then `◐_ν` is a lock, its dependent right adjoint the
COMPOSITE `⟨ν|−⟩` then `⟨μ|−⟩` (contravariant).  This is `LOCK` 2-functoriality on locks-with-DRA:
together with `ContextLock.identity` it makes the modal locks on the context category a monoid whose
multiplication carries the whole adjunction. -/
def ContextLock.compose {category : RawCategory.{u, v}}
    (firstLock secondLock : ContextLock category) : ContextLock category where
  lock := firstLock.lock.compose secondLock.lock
  dependentRightAdjoint :=
    secondLock.dependentRightAdjoint.compose firstLock.dependentRightAdjoint
  adjunction := firstLock.adjunction.compose secondLock.adjunction

end FX1Poly.Tier0
