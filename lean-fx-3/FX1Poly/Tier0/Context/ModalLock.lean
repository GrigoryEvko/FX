import FX1Poly.Tier0.Context.Context
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstColimits

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

## What lands here (all zero-axiom)

**Layer A — the monoid `End(𝒞)` and its 2-cells (the keys).**

  * `RawEndofunctor.compose` — composition of locks (the gap `context-0` flagged: needed for
    `◐_(ν∘μ) = ◐_μ ∘ ◐_ν`), with both functor laws PROVED.
  * `RawEndofunctor.identity_compose` / `compose_identity` / `compose_assoc` — the three
    STRICT monoid laws on locks (the strict 2-functoriality target); `End(𝒞)` is a genuine monoid.
  * `RawEndofunctorTransformation` — the generic natural transformation between two locks (the only
    nat-trans shipped so far, `SliceNatTrans`, is slice-specialised).  These are the **keys**: a
    2-cell `μ ⇒ ν` maps to a `RawEndofunctorTransformation ◐_ν ◐_μ`.
  * `RawEndofunctorTransformation.identity` / `vcomp` (+ the componentwise unit laws) — the vertical
    2-cell structure on keys, naturality squares PROVED.

**Layer B — the dependent right adjoint `⟨μ|−⟩`.**

  * `IsEndoAdjunction` — a lock and its DRA as an adjunction `◐_μ ⊣ ⟨μ|−⟩`, in the funext-free
    natural-hom-bijection form (matching the shipped comprehension `Bijection`), with both
    naturality squares.
  * `IsEndoAdjunction.identity` / `compose` — the identity adjunction and adjunction composition
    (the DRAs compose CONTRAVARIANTLY — `LOCK` 2-functoriality on the type-former side).
  * `IsEndoAdjunction.unit` / `counit` — the modal unit `η : id ⇒ ⟨μ|◐_μ −⟩` and counit
    `ε : ◐_μ⟨μ|−⟩ ⇒ id` recovered from the transpose, as genuine `RawEndofunctorTransformation`s,
    each naturality square PROVED (the counit via `transposeRight`-injectivity).
  * `IsEndoAdjunction.transposeLeft_natural_left` / `transposeLeft_natural_right` +
    `unit_counit_left_triangle` / `unit_counit_right_triangle` — the two TRIANGLE IDENTITIES,
    certifying `η` / `ε` genuinely form a unit / counit (the unit/counit definition of an adjunction
    coincides with the shipped hom-bijection one).
  * `ContextLock` — the bundled lock-with-DRA the slot `ContextAxis.lockOn` ultimately carries, with
    `ContextLock.identity` / `compose`.

**Layer C — concrete locks on the FX substitution category `fxBaseSubstCategory`.**

  * `fxIdentityLock` — the trivial-mode lock as a full `ContextLock` (self-adjoint identity).
  * `fxContextAxis_lockOn_eq_identityLock` — the WIRING theorem: the endofunctor `context-0`'s
    `fxContextAxis.lockOn` deposits at the trivial modality IS `fxIdentityLock.lock`, so the slot
    `context-0` declared is now provably filled by `context-4`'s structure.
  * `fxWeakeningLock` — the non-trivial weakening lock `A ↦ A + K` (context extension by `K`), a
    genuine `RawEndofunctor` with both functor laws from the `context-3` coproduct bifunctor.  It
    ships as a lock CARRIER only: `(− + K)` has no endo-right-adjoint in the bare context category
    (its DRA is the type-level `∀`-over-`K`, living over the `Core/` type fibration), so the DRA —
    and the whole `×mode` family `μ ↦ ◐_μ` indexed by a mode 2-category — stay deferred to `fib-3`.

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

/-! ## Horizontal composition and the interchange law — the strict 2-category `End(𝒞)`

`vcomp` above gives the 2-cells (keys) their VERTICAL composition; `LOCK` 2-functoriality takes
values in the full strict 2-category `End(𝒞)`, which also has the 1-cell-direction (HORIZONTAL)
composition of 2-cells and the two whiskerings, subject to the INTERCHANGE law.  That is the literal
target structure of `LOCK` 2-functoriality, and it lands here.  (The `×mode` 2-functor
`M^coop → End(𝒞)` reading off a mode 2-category is `fib-3`; this is its codomain.) -/

/-- **Right whiskering** — post-compose a 2-cell with a functor.  `key.whiskerOuter outerFunctor`
sends the key `F ⇒ F'` to `(F ∘ G) ⇒ (F' ∘ G)` (here `G = outerFunctor`, applied OUTSIDE/last).
Component is `G`'s action on `key`'s component; naturality is `G`'s functoriality pasted with `key`'s
naturality.  (The `hcomp` special case with the identity key on `G`.) -/
def RawEndofunctorTransformation.whiskerOuter {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor)
    (outerFunctor : RawEndofunctor category) :
    RawEndofunctorTransformation (sourceFunctor.compose outerFunctor)
      (targetFunctor.compose outerFunctor) where
  component := fun object => outerFunctor.mapMorphism (key.component object)
  naturality := fun {objectA objectB} morphism => by
    show category.compose
          (outerFunctor.mapMorphism (sourceFunctor.mapMorphism morphism))
          (outerFunctor.mapMorphism (key.component objectB))
        = category.compose
          (outerFunctor.mapMorphism (key.component objectA))
          (outerFunctor.mapMorphism (targetFunctor.mapMorphism morphism))
    rw [← outerFunctor.preservesComposition, ← outerFunctor.preservesComposition,
        key.naturality morphism]

/-- **Left whiskering** — pre-compose a functor with a 2-cell.  `whiskerInner innerFunctor key`
sends the key `G ⇒ G'` to `(F ∘ G) ⇒ (F ∘ G')` (here `F = innerFunctor`, applied INSIDE/first).
Component is `key` at the `F`-image; naturality is exactly `key`'s naturality at `F`'s morphism
action.  (The `hcomp` special case with the identity key on `F`.) -/
def RawEndofunctorTransformation.whiskerInner {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (innerFunctor : RawEndofunctor category)
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor) :
    RawEndofunctorTransformation (innerFunctor.compose sourceFunctor)
      (innerFunctor.compose targetFunctor) where
  component := fun object => key.component (innerFunctor.mapObject object)
  naturality := fun {_objectA _objectB} morphism =>
    key.naturality (innerFunctor.mapMorphism morphism)

/-- **Horizontal composition (the Godement product) of keys.**  Given `innerKey : F ⇒ F'` and
`outerKey : G ⇒ G'`, produce `(F ∘ G) ⇒ (F' ∘ G')`.  Component at `a`: `G`'s action on `innerKey_a`,
then `outerKey` at `F' a` (the upper-right path of the naturality square; the lower-left path agrees
by `outerKey`'s naturality).  This is the genuine 1-cell-direction composite of 2-cells which, with
`vcomp`, makes `End(𝒞)` a strict 2-category. -/
def RawEndofunctorTransformation.hcomp {category : RawCategory.{u, v}}
    {innerSource innerTarget outerSource outerTarget : RawEndofunctor category}
    (innerKey : RawEndofunctorTransformation innerSource innerTarget)
    (outerKey : RawEndofunctorTransformation outerSource outerTarget) :
    RawEndofunctorTransformation (innerSource.compose outerSource)
      (innerTarget.compose outerTarget) where
  component := fun object =>
    category.compose (outerSource.mapMorphism (innerKey.component object))
      (outerKey.component (innerTarget.mapObject object))
  naturality := fun {objectA objectB} morphism => by
    show category.compose
          (outerSource.mapMorphism (innerSource.mapMorphism morphism))
          (category.compose (outerSource.mapMorphism (innerKey.component objectB))
            (outerKey.component (innerTarget.mapObject objectB)))
        = category.compose
          (category.compose (outerSource.mapMorphism (innerKey.component objectA))
            (outerKey.component (innerTarget.mapObject objectA)))
          (outerTarget.mapMorphism (innerTarget.mapMorphism morphism))
    rw [← category.composeAssoc, ← outerSource.preservesComposition,
        innerKey.naturality morphism, outerSource.preservesComposition,
        category.composeAssoc, outerKey.naturality (innerTarget.mapMorphism morphism),
        ← category.composeAssoc]

/-- Right whiskering acts as the outer functor on the component. -/
theorem RawEndofunctorTransformation.whiskerOuter_component {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor)
    (outerFunctor : RawEndofunctor category) (object : category.Object) :
    (key.whiskerOuter outerFunctor).component object
      = outerFunctor.mapMorphism (key.component object) := rfl

/-- Left whiskering acts as the component at the inner functor's image. -/
theorem RawEndofunctorTransformation.whiskerInner_component {category : RawCategory.{u, v}}
    {sourceFunctor targetFunctor : RawEndofunctor category}
    (innerFunctor : RawEndofunctor category)
    (key : RawEndofunctorTransformation sourceFunctor targetFunctor) (object : category.Object) :
    (RawEndofunctorTransformation.whiskerInner innerFunctor key).component object
      = key.component (innerFunctor.mapObject object) := rfl

/-- Horizontal composition acts by the upper-right path of the Godement square. -/
theorem RawEndofunctorTransformation.hcomp_component {category : RawCategory.{u, v}}
    {innerSource innerTarget outerSource outerTarget : RawEndofunctor category}
    (innerKey : RawEndofunctorTransformation innerSource innerTarget)
    (outerKey : RawEndofunctorTransformation outerSource outerTarget) (object : category.Object) :
    (innerKey.hcomp outerKey).component object
      = category.compose (outerSource.mapMorphism (innerKey.component object))
          (outerKey.component (innerTarget.mapObject object)) := rfl

/-- **The interchange law** (componentwise) — the strict 2-category coherence relating the two
compositions of 2-cells: horizontally composing two VERTICAL composites equals vertically composing
two HORIZONTAL composites, `(α ⊟ α') ⋆ (β ⊟ β') = (α ⋆ β) ⊟ (α' ⋆ β')` (writing `⊟` for `vcomp`,
`⋆` for `hcomp`).  The single non-formal step is `β`'s naturality at `α'`'s component; the rest is
associativity and `outerSource`'s functoriality.  Stated componentwise (funext-free), matching the
file's convention. -/
theorem RawEndofunctorTransformation.interchange_component {category : RawCategory.{u, v}}
    {innerSource innerMiddle innerTarget : RawEndofunctor category}
    {outerSource outerMiddle outerTarget : RawEndofunctor category}
    (alpha : RawEndofunctorTransformation innerSource innerMiddle)
    (alphaPrime : RawEndofunctorTransformation innerMiddle innerTarget)
    (beta : RawEndofunctorTransformation outerSource outerMiddle)
    (betaPrime : RawEndofunctorTransformation outerMiddle outerTarget)
    (object : category.Object) :
    ((alpha.vcomp alphaPrime).hcomp (beta.vcomp betaPrime)).component object
      = ((alpha.hcomp beta).vcomp (alphaPrime.hcomp betaPrime)).component object := by
  show category.compose
        (outerSource.mapMorphism
          (category.compose (alpha.component object) (alphaPrime.component object)))
        (category.compose (beta.component (innerTarget.mapObject object))
          (betaPrime.component (innerTarget.mapObject object)))
      = category.compose
        (category.compose (outerSource.mapMorphism (alpha.component object))
          (beta.component (innerMiddle.mapObject object)))
        (category.compose (outerMiddle.mapMorphism (alphaPrime.component object))
          (betaPrime.component (innerTarget.mapObject object)))
  rw [outerSource.preservesComposition,
      category.composeAssoc (outerSource.mapMorphism (alpha.component object))
        (outerSource.mapMorphism (alphaPrime.component object))
        (category.compose (beta.component (innerTarget.mapObject object))
          (betaPrime.component (innerTarget.mapObject object))),
      ← category.composeAssoc (outerSource.mapMorphism (alphaPrime.component object))
        (beta.component (innerTarget.mapObject object))
        (betaPrime.component (innerTarget.mapObject object)),
      beta.naturality (alphaPrime.component object),
      category.composeAssoc (beta.component (innerMiddle.mapObject object))
        (outerMiddle.mapMorphism (alphaPrime.component object))
        (betaPrime.component (innerTarget.mapObject object)),
      ← category.composeAssoc (outerSource.mapMorphism (alpha.component object))
        (beta.component (innerMiddle.mapObject object))
        (category.compose (outerMiddle.mapMorphism (alphaPrime.component object))
          (betaPrime.component (innerTarget.mapObject object)))]

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

/-! ## The modal unit and counit — `η` and `ε` of the lock-DRA adjunction

From the hom-bijection an adjunction yields its UNIT `η : id ⇒ ⟨μ|◐_μ −⟩` (transpose of the identity
on `◐_μ a`) and COUNIT `ε : ◐_μ⟨μ|−⟩ ⇒ id` (inverse-transpose of the identity on `⟨μ|b⟩`) — the modal
`intro` / `elim` of MTT.  Both are genuine `RawEndofunctorTransformation`s; the counit's naturality is
the dual square, proved by transporting through `transposeRight` (injective, being one half of the
bijection). -/

/-- The **unit** `η : id ⇒ ⟨μ|◐_μ −⟩` of a lock-DRA adjunction — at each object the transpose of the
identity `◐_μ a ⟶ ◐_μ a`.  The naturality square is the transpose's two naturalities pasted across an
identity. -/
def IsEndoAdjunction.unit {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) :
    RawEndofunctorTransformation (RawEndofunctor.identity category)
      (leftAdjoint.compose rightAdjoint) where
  component := fun object =>
    adjunction.transposeRight (category.identity (leftAdjoint.mapObject object))
  naturality := fun {objectA objectB} morphism => by
    show category.compose morphism
          (adjunction.transposeRight (category.identity (leftAdjoint.mapObject objectB)))
        = category.compose
            (adjunction.transposeRight (category.identity (leftAdjoint.mapObject objectA)))
            (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism morphism))
    rw [← adjunction.transposeRight_natural_left morphism
          (category.identity (leftAdjoint.mapObject objectB)),
        category.identityRight,
        ← adjunction.transposeRight_natural_right
          (category.identity (leftAdjoint.mapObject objectA))
          (leftAdjoint.mapMorphism morphism),
        category.identityLeft]

/-- The **counit** `ε : ◐_μ⟨μ|−⟩ ⇒ id` of a lock-DRA adjunction — at each object the inverse-transpose
of the identity `⟨μ|b⟩ ⟶ ⟨μ|b⟩`.  Naturality is the dual square: both sides transpose (under
`transposeRight`) to `⟨μ|morphism⟩`, and `transposeRight` is injective (its left inverse is
`transposeLeft`), so equality of transposes gives equality of the components. -/
def IsEndoAdjunction.counit {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) :
    RawEndofunctorTransformation (rightAdjoint.compose leftAdjoint)
      (RawEndofunctor.identity category) where
  component := fun object =>
    adjunction.transposeLeft (category.identity (rightAdjoint.mapObject object))
  naturality := fun {objectA objectB} morphism => by
    show category.compose
          (leftAdjoint.mapMorphism (rightAdjoint.mapMorphism morphism))
          (adjunction.transposeLeft (category.identity (rightAdjoint.mapObject objectB)))
        = category.compose
            (adjunction.transposeLeft (category.identity (rightAdjoint.mapObject objectA)))
            morphism
    have key :
        adjunction.transposeRight (category.compose
            (leftAdjoint.mapMorphism (rightAdjoint.mapMorphism morphism))
            (adjunction.transposeLeft (category.identity (rightAdjoint.mapObject objectB))))
          = adjunction.transposeRight (category.compose
            (adjunction.transposeLeft (category.identity (rightAdjoint.mapObject objectA)))
            morphism) := by
      rw [adjunction.transposeRight_natural_left,
          adjunction.transposeRight_transposeLeft, category.identityRight,
          adjunction.transposeRight_natural_right,
          adjunction.transposeRight_transposeLeft, category.identityLeft]
    have transposed := congrArg adjunction.transposeLeft key
    rw [adjunction.transposeLeft_transposeRight,
        adjunction.transposeLeft_transposeRight] at transposed
    exact transposed

/-! ## Naturality of the inverse transpose + the triangle identities

The hom-bijection form already certifies the adjunction completely; here it is reconciled with the
unit/counit form by proving the two TRIANGLE IDENTITIES — the coherence laws that make `η` / `ε` a
genuine unit / counit (not just two arbitrary nat-transs).  Each is stated componentwise
(funext-free) and rides the derived naturality of `transposeLeft` (dual to the structure's
`transposeRight` naturalities, proved via `transposeRight`-injectivity). -/

/-- Naturality of the inverse transpose in the DOMAIN — dual to `transposeRight_natural_left`, proved
by transporting through the injective `transposeRight`. -/
theorem IsEndoAdjunction.transposeLeft_natural_left {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint)
    {sourceA objectA objectB : category.Object}
    (reindex : category.Morphism sourceA objectA)
    (morphism : category.Morphism objectA (rightAdjoint.mapObject objectB)) :
    adjunction.transposeLeft (category.compose reindex morphism)
      = category.compose (leftAdjoint.mapMorphism reindex) (adjunction.transposeLeft morphism) := by
  have key : adjunction.transposeRight (adjunction.transposeLeft (category.compose reindex morphism))
      = adjunction.transposeRight
          (category.compose (leftAdjoint.mapMorphism reindex) (adjunction.transposeLeft morphism)) := by
    rw [adjunction.transposeRight_transposeLeft, adjunction.transposeRight_natural_left,
        adjunction.transposeRight_transposeLeft]
  have transposed := congrArg adjunction.transposeLeft key
  rw [adjunction.transposeLeft_transposeRight, adjunction.transposeLeft_transposeRight] at transposed
  exact transposed

/-- Naturality of the inverse transpose in the CODOMAIN — dual to `transposeRight_natural_right`. -/
theorem IsEndoAdjunction.transposeLeft_natural_right {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint)
    {objectA objectB targetB : category.Object}
    (morphism : category.Morphism objectA (rightAdjoint.mapObject objectB))
    (after : category.Morphism objectB targetB) :
    adjunction.transposeLeft (category.compose morphism (rightAdjoint.mapMorphism after))
      = category.compose (adjunction.transposeLeft morphism) after := by
  have key : adjunction.transposeRight
        (adjunction.transposeLeft (category.compose morphism (rightAdjoint.mapMorphism after)))
      = adjunction.transposeRight (category.compose (adjunction.transposeLeft morphism) after) := by
    rw [adjunction.transposeRight_transposeLeft, adjunction.transposeRight_natural_right,
        adjunction.transposeRight_transposeLeft]
  have transposed := congrArg adjunction.transposeLeft key
  rw [adjunction.transposeLeft_transposeRight, adjunction.transposeLeft_transposeRight] at transposed
  exact transposed

/-- **Left triangle identity** `ε_{◐a} ∘ ◐(η_a) = id_{◐a}` — one half of the unit/counit coherence,
componentwise.  Both sides transpose (under `transposeRight`) to `η_a`. -/
theorem IsEndoAdjunction.unit_counit_left_triangle {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) (object : category.Object) :
    category.compose (leftAdjoint.mapMorphism (adjunction.unit.component object))
        (adjunction.counit.component (leftAdjoint.mapObject object))
      = category.identity (leftAdjoint.mapObject object) := by
  have key : adjunction.transposeRight
        (category.compose (leftAdjoint.mapMorphism (adjunction.unit.component object))
          (adjunction.counit.component (leftAdjoint.mapObject object)))
      = adjunction.transposeRight (category.identity (leftAdjoint.mapObject object)) := by
    show adjunction.transposeRight
          (category.compose
            (leftAdjoint.mapMorphism
              (adjunction.transposeRight (category.identity (leftAdjoint.mapObject object))))
            (adjunction.transposeLeft
              (category.identity (rightAdjoint.mapObject (leftAdjoint.mapObject object)))))
        = adjunction.transposeRight (category.identity (leftAdjoint.mapObject object))
    rw [adjunction.transposeRight_natural_left, adjunction.transposeRight_transposeLeft,
        category.identityRight]
  have injective :
      ∀ {firstMor secondMor :
          category.Morphism (leftAdjoint.mapObject object) (leftAdjoint.mapObject object)},
        adjunction.transposeRight firstMor = adjunction.transposeRight secondMor →
          firstMor = secondMor := fun {firstMor secondMor} equalTransposes =>
    (adjunction.transposeLeft_transposeRight firstMor).symm.trans
      ((congrArg adjunction.transposeLeft equalTransposes).trans
        (adjunction.transposeLeft_transposeRight secondMor))
  exact injective key

/-- **Right triangle identity** `⟨ε_b⟩ ∘ η_{⟨b⟩} = id_{⟨b⟩}` — the other half, componentwise, via the
derived inverse-transpose codomain naturality.  Both sides transpose (under `transposeLeft`) to
`ε_b`. -/
theorem IsEndoAdjunction.unit_counit_right_triangle {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) (object : category.Object) :
    category.compose (adjunction.unit.component (rightAdjoint.mapObject object))
        (rightAdjoint.mapMorphism (adjunction.counit.component object))
      = category.identity (rightAdjoint.mapObject object) := by
  have key : adjunction.transposeLeft
        (category.compose (adjunction.unit.component (rightAdjoint.mapObject object))
          (rightAdjoint.mapMorphism (adjunction.counit.component object)))
      = adjunction.transposeLeft (category.identity (rightAdjoint.mapObject object)) := by
    show adjunction.transposeLeft
          (category.compose
            (adjunction.transposeRight
              (category.identity (leftAdjoint.mapObject (rightAdjoint.mapObject object))))
            (rightAdjoint.mapMorphism
              (adjunction.transposeLeft (category.identity (rightAdjoint.mapObject object)))))
        = adjunction.transposeLeft (category.identity (rightAdjoint.mapObject object))
    rw [adjunction.transposeLeft_natural_right, adjunction.transposeLeft_transposeRight,
        category.identityLeft]
  have injective :
      ∀ {firstMor secondMor :
          category.Morphism (rightAdjoint.mapObject object) (rightAdjoint.mapObject object)},
        adjunction.transposeLeft firstMor = adjunction.transposeLeft secondMor →
          firstMor = secondMor := fun {firstMor secondMor} equalTransposes =>
    (adjunction.transposeRight_transposeLeft firstMor).symm.trans
      ((congrArg adjunction.transposeRight equalTransposes).trans
        (adjunction.transposeRight_transposeLeft secondMor))
  exact injective key

/-! ## The modal monad `⟨μ|◐_μ −⟩` generated by the adjunction

Every adjunction `◐_μ ⊣ ⟨μ|−⟩` generates a MONAD on the context category — the modal monad
`T = ⟨μ|◐_μ −⟩` (in diagrammatic order `T = leftAdjoint.compose rightAdjoint`), whose unit is the
adjunction `unit` and whose multiplication `μ` is `⟨μ|−⟩` applied to the counit at `◐_μ a`.  This is
the dependent right adjoint's semantic payload: the modal `intro`/`elim`'s round-trip equations ARE
the monad laws, and they fall straight out of the two triangle identities.  Stated componentwise
(funext-free). -/

/-- The **multiplication** `μ : T∘T ⇒ T` of the modal monad `T = ⟨μ|◐_μ −⟩` — at each object the
right adjoint `⟨μ|−⟩` applied to the counit at `◐_μ a`.  (`T = leftAdjoint.compose rightAdjoint`;
`T∘T` collapses by lock composition.)  Naturality is the counit's naturality, wrapped through the
right adjoint's functoriality. -/
def IsEndoAdjunction.modalMultiplication {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) :
    RawEndofunctorTransformation
      ((leftAdjoint.compose rightAdjoint).compose (leftAdjoint.compose rightAdjoint))
      (leftAdjoint.compose rightAdjoint) where
  component := fun object =>
    rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject object))
  naturality := fun {objectA objectB} morphism => by
    show category.compose
          (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism
            (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism morphism))))
          (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject objectB)))
        = category.compose
          (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject objectA)))
          (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism morphism))
    rw [← rightAdjoint.preservesComposition, ← rightAdjoint.preservesComposition]
    exact congrArg rightAdjoint.mapMorphism
      (adjunction.counit.naturality (leftAdjoint.mapMorphism morphism))

/-- **Modal monad left-unit law** (componentwise): `μ ∘ ηT = id_T`.  IS the RIGHT triangle identity
read at `◐_μ a` — modal `elim` after `intro`-on-the-modal-type is the identity. -/
theorem IsEndoAdjunction.modalMonad_leftUnit {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) (object : category.Object) :
    category.compose
        (adjunction.unit.component (rightAdjoint.mapObject (leftAdjoint.mapObject object)))
        (adjunction.modalMultiplication.component object)
      = category.identity (rightAdjoint.mapObject (leftAdjoint.mapObject object)) :=
  adjunction.unit_counit_right_triangle (leftAdjoint.mapObject object)

/-- **Modal monad right-unit law** (componentwise): `μ ∘ Tη = id_T`.  IS `⟨μ|−⟩` applied to the LEFT
triangle identity — modal `elim` after `intro`-under-the-lock is the identity. -/
theorem IsEndoAdjunction.modalMonad_rightUnit {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) (object : category.Object) :
    category.compose
        ((leftAdjoint.compose rightAdjoint).mapMorphism (adjunction.unit.component object))
        (adjunction.modalMultiplication.component object)
      = category.identity (rightAdjoint.mapObject (leftAdjoint.mapObject object)) := by
  show category.compose
        (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism (adjunction.unit.component object)))
        (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject object)))
      = category.identity (rightAdjoint.mapObject (leftAdjoint.mapObject object))
  rw [← rightAdjoint.preservesComposition, adjunction.unit_counit_left_triangle]
  exact rightAdjoint.preservesIdentity (leftAdjoint.mapObject object)

/-- **Modal monad associativity law** (componentwise): `μ ∘ Tμ = μ ∘ μT`.  Both sides are `⟨μ|−⟩`
applied to the counit's naturality AT the counit — the associativity coherence of the modal monad,
a direct corollary of `counit`'s naturality square. -/
theorem IsEndoAdjunction.modalMonad_assoc {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint) (object : category.Object) :
    category.compose
        ((leftAdjoint.compose rightAdjoint).mapMorphism
          (adjunction.modalMultiplication.component object))
        (adjunction.modalMultiplication.component object)
      = category.compose
        (adjunction.modalMultiplication.component
          (rightAdjoint.mapObject (leftAdjoint.mapObject object)))
        (adjunction.modalMultiplication.component object) := by
  show category.compose
        (rightAdjoint.mapMorphism (leftAdjoint.mapMorphism
          (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject object)))))
        (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject object)))
      = category.compose
        (rightAdjoint.mapMorphism (adjunction.counit.component
          (leftAdjoint.mapObject (rightAdjoint.mapObject (leftAdjoint.mapObject object)))))
        (rightAdjoint.mapMorphism (adjunction.counit.component (leftAdjoint.mapObject object)))
  rw [← rightAdjoint.preservesComposition, ← rightAdjoint.preservesComposition]
  exact congrArg rightAdjoint.mapMorphism
    (adjunction.counit.naturality (adjunction.counit.component (leftAdjoint.mapObject object)))

/-! ## The lock preserves colimits (RAPL) — back to `context-3`

A lock `◐_μ` is the LEFT adjoint of its adjunction, and left adjoints preserve colimits (the RAPL
slogan).  `context-3` shipped the context category's finite colimits — the initial object and the
binary coproduct — as abstract `IsInitialObject` / `IsBinaryCoproduct` universal properties over a
`RawCategory`.  Here the lock-DRA adjunction transports both: the lock sends the initial object to an
initial object and a binary coproduct to a binary coproduct, with the new universal data read off the
transpose.  This closes the loop between `context-4`'s lock and `context-3`'s colimits — the modal
lock is a genuine colimit-preserving functor of the context category. -/

/-- **The lock preserves the INITIAL object.**  If `I` is initial, so is `◐_μ I`: the unique map out
is the transpose of `I`'s unique map into `⟨μ|−⟩`'s value, and uniqueness rides the transpose
bijection (`◐_μ` preserves the empty colimit). -/
def IsEndoAdjunction.mapInitialObject {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint)
    {initialObject : category.Object} (initial : IsInitialObject category initialObject) :
    IsInitialObject category (leftAdjoint.mapObject initialObject) where
  fromInitial := fun target =>
    adjunction.transposeLeft (initial.fromInitial (rightAdjoint.mapObject target))
  fromInitialUnique := fun {_target} morphism =>
    (adjunction.transposeLeft_transposeRight morphism).symm.trans
      (congrArg adjunction.transposeLeft
        (initial.fromInitialUnique (adjunction.transposeRight morphism)))

/-- **The lock preserves BINARY COPRODUCTS.**  If `A + B` is the coproduct of `A`, `B`, then
`◐_μ(A + B)` is the coproduct of `◐_μ A`, `◐_μ B`: injections are `◐_μ` applied to the originals,
copairing transposes both legs and copairs them downstairs, and the three universal-property laws all
ride the transpose naturalities + bijection (`◐_μ` preserves the binary colimit). -/
def IsEndoAdjunction.mapBinaryCoproduct {category : RawCategory.{u, v}}
    {leftAdjoint rightAdjoint : RawEndofunctor category}
    (adjunction : IsEndoAdjunction leftAdjoint rightAdjoint)
    {leftSummand rightSummand coproductObject : category.Object}
    (coproduct : IsBinaryCoproduct category leftSummand rightSummand coproductObject) :
    IsBinaryCoproduct category (leftAdjoint.mapObject leftSummand)
      (leftAdjoint.mapObject rightSummand) (leftAdjoint.mapObject coproductObject) where
  injectLeft := leftAdjoint.mapMorphism coproduct.injectLeft
  injectRight := leftAdjoint.mapMorphism coproduct.injectRight
  copair := fun leftLeg rightLeg =>
    adjunction.transposeLeft
      (coproduct.copair (adjunction.transposeRight leftLeg) (adjunction.transposeRight rightLeg))
  copairInjectLeft := fun leftLeg rightLeg => by
    show category.compose (leftAdjoint.mapMorphism coproduct.injectLeft)
        (adjunction.transposeLeft (coproduct.copair (adjunction.transposeRight leftLeg)
          (adjunction.transposeRight rightLeg)))
      = leftLeg
    rw [← adjunction.transposeLeft_natural_left, coproduct.copairInjectLeft,
        adjunction.transposeLeft_transposeRight]
  copairInjectRight := fun leftLeg rightLeg => by
    show category.compose (leftAdjoint.mapMorphism coproduct.injectRight)
        (adjunction.transposeLeft (coproduct.copair (adjunction.transposeRight leftLeg)
          (adjunction.transposeRight rightLeg)))
      = rightLeg
    rw [← adjunction.transposeLeft_natural_left, coproduct.copairInjectRight,
        adjunction.transposeLeft_transposeRight]
  copairUnique := fun mediator leftLeg rightLeg afterLeft afterRight => by
    have leftFactor : category.compose coproduct.injectLeft (adjunction.transposeRight mediator)
        = adjunction.transposeRight leftLeg := by
      rw [← adjunction.transposeRight_natural_left, afterLeft]
    have rightFactor : category.compose coproduct.injectRight (adjunction.transposeRight mediator)
        = adjunction.transposeRight rightLeg := by
      rw [← adjunction.transposeRight_natural_left, afterRight]
    have unique := coproduct.copairUnique (adjunction.transposeRight mediator)
      (adjunction.transposeRight leftLeg) (adjunction.transposeRight rightLeg)
      leftFactor rightFactor
    exact (adjunction.transposeLeft_transposeRight mediator).symm.trans
      (congrArg adjunction.transposeLeft unique)

/-! ## Concrete locks on the FX substitution category

The two structures above are independent of any concrete category; here they are inhabited on the
shipped FX context category `fxBaseSubstCategory`.  The identity lock fills the slot `context-0`
declared; the weakening lock exhibits a NON-trivial lock carrier so the structure is not vacuous. -/

/-- ★ The **identity lock** on the FX context category — the trivial-mode lock `◐_id` as a full
`ContextLock` (self-adjoint identity endofunctor).  This is exactly the lock `fxContextAxis.lockOn`
deposits at the (only) trivial modality. -/
def fxIdentityLock : ContextLock fxBaseSubstCategory :=
  ContextLock.identity fxBaseSubstCategory

/-- ★ **The wiring theorem.**  The endofunctor `context-0`'s `fxContextAxis.lockOn` deposits at the
trivial modality IS `context-4`'s `fxIdentityLock.lock` — the abstract lock slot `context-0` declared
is now provably filled by the modal-lock structure shipped here, not merely by an anonymous
`RawEndofunctor.identity`. -/
theorem fxContextAxis_lockOn_eq_identityLock (modality : Unit) :
    (@ContextAxis.lockOn trivialMode fxContextAxis () () modality) = fxIdentityLock.lock := rfl

/-- The **weakening lock** `◐_{+K} : A ↦ A + K` — context extension by `K` fresh variables, the
canonical NON-trivial lock.  A genuine endofunctor of `fxBaseSubstCategory`: its morphism action is
the `context-3` coproduct bifunctor `coproductMap (−) (id K)`, so both functor laws are exactly the
shipped `coproductMap_identity` / `coproductMap_compose`.  It ships as a lock CARRIER only — `(− + K)`
has no endo-right-adjoint in the bare context category (its DRA is the type-level `∀`-over-`K` over
`Core/`), so it is NOT bundled into a `ContextLock`; the DRA is deferred to `fib-3`. -/
def fxWeakeningLock (extraScope : Nat) : RawEndofunctor fxBaseSubstCategory where
  mapObject := fun (scope : Nat) => scope + extraScope
  mapMorphism := fun morphism => SubstVec.coproductMap morphism (SubstVec.identity extraScope)
  preservesIdentity := fun scope =>
    SubstVec.coproductMap_identity scope extraScope
  preservesComposition := fun firstVec secondVec => by
    have base := SubstVec.coproductMap_compose firstVec secondVec
      (SubstVec.identity extraScope) (SubstVec.identity extraScope)
    rw [SubstVec.identity_compose] at base
    exact base

end FX1Poly.Tier0
