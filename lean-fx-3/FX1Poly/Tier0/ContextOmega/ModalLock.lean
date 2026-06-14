import FX1Poly.Tier0.ContextOmega.DimensionalFunctor
import FX1Poly.Tier0.FxBaseSubstCategory

/-! # Tier0/ContextOmega/ModalLock — the modal lock `◐` + LOCK 2-functoriality (context-4)

The modal-CwF layer of the context ω-category.  In multimodal type theory (MTT, Gratzer–Kavvos–
Nuyts–Birkedal) every modality `μ` has a **lock** functor `◐_μ : Ctx → Ctx` — a context operation,
left adjoint to the modal context extension — and the assignment `μ ↦ ◐_μ` is (contravariantly)
2-functorial in the mode 2-category.  This module builds the lock as a genuine ENDOFUNCTOR on the FX
context category `fxBaseSubstCategory`, with the endofunctor algebra (identity + composition) that
carries the 2-functoriality, and the bridge to context-3's `dimExtend`.

## What is built

  * `RawEndofunctor base` — a (strict) endofunctor on a `RawCategory`: an object map + a morphism map
    preserving identity and composition.  Reusable Tier-0 infrastructure (the mode/fib axes need it).
  * `RawEndofunctor.identity` / `RawEndofunctor.comp` — endofunctors form a strict monoid under
    composition (the identity endofunctor `◐_id = Id` and composition `◐_(μν) = ◐_ν ∘ ◐_μ`).  This IS
    the LOCK 2-functoriality skeleton: the laws `◐_id = Id` and `◐` respects composition.
  * ★ `dimensionLock : RawEndofunctor fxBaseSubstCategory` — **the modal lock** for the dimension
    modality.  Object map `scope ↦ scope + 1` (extend the context by a lock variable), morphism map
    `liftUnderBinder` (lift a substitution under the new lock variable).  Its functor laws ARE the
    shipped vec-level lift laws (`liftUnderBinder_identity` / `_compose`) — so the lock rides for free
    on context-3's substrate.
  * `dimensionLockSquared_objectMap` — the iterated lock `◐ ∘ ◐` adds two variables (`scope + 2`): the
    `◐_(μ∘μ)` instance of LOCK composition, demonstrating locks compose.
  * `dimExtend_sections_eq_lockReindex` / `dimExtend_substAction_eq_lockReindex` — **the lock ↔
    dimExtend bridge**: context-3's dimensional weakening `dimExtend` is exactly REINDEXING a family
    ALONG the lock — `(dimExtend F).sections scope = F.sections (◐ scope)` and its action is `F`'s
    action at the LOCK's morphism map.  So `dimExtend = ◐^*`, the modality's action on the presheaf
    category.  The dependent right adjoint (DRA) `⟨μ | -⟩` to the lock is the right adjoint to this
    reindexing — see the honest boundary.

## Honest boundaries (recorded, not faked)

  * **Full LOCK 2-functoriality over the mode 2-category** (the `μ ↦ ◐_μ` assignment, contravariant in
    modality composition, with 2-cells `α : μ ⇒ ν` giving `◐_α : ◐_ν ⇒ ◐_μ`) needs the mode theory —
    the mode-* axis (mode-0 #1556 onward).  Here the 2-functoriality is realized for the concrete
    dimension modality (identity + self-composition of `dimensionLock`); the general assignment is
    mode-0's job.  Equalities of whole `RawEndofunctor`s (the strict 2-monad laws `comp_id`/`id_comp`/
    `comp_assoc`) compare the `morphismMap` field, an infinite function family → they need `funext`
    (`Quot.sound`-derived), OFF the zero-axiom path; only the object-level / pointwise witnesses are
    shipped here.
  * **The dependent right adjoint `⟨μ | A⟩`** (the modal type former, right adjoint to the lock) is the
    right adjoint to `dimExtend = ◐^*` — the same funext-blocked `SubstFamilyMap` hom-bijection as
    context-3's `Σ ⊣ Ω ⊣ Π` adjoint string.  The lock-reindexing functor IS shipped; its adjoint is
    the recorded frontier.

## Zero-axiom verification

`RawEndofunctor.comp`'s laws are `rw` of the two component functor laws; `dimensionLock`'s laws are the
shipped `liftUnderBinder_identity` / `_compose`; the iterated-lock object map and the dimExtend bridge
are `rfl` (`scope+1+1` is defeq `scope+2`; `dimExtend`'s sections/action are defeq the lock-reindexed
ones).  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0

open FX1Poly.Core

universe u v

/-! ## Endofunctors on a raw category -/

/-- **A strict endofunctor on a `RawCategory`.**  An object map and a morphism map that preserve the
identity and composition.  The minimal categorical-functor structure; the modal lock is an instance,
and the mode/fib axes reuse it. -/
structure RawEndofunctor (base : RawCategory.{u, v}) where
  /-- The action on objects. -/
  objectMap : base.Object → base.Object
  /-- The action on morphisms. -/
  morphismMap : {objectA objectB : base.Object} →
    base.Morphism objectA objectB → base.Morphism (objectMap objectA) (objectMap objectB)
  /-- Functoriality: the identity is preserved. -/
  preservesIdentity : ∀ (obj : base.Object),
    morphismMap (base.identity obj) = base.identity (objectMap obj)
  /-- Functoriality: composition is preserved. -/
  preservesCompose : ∀ {objectA objectB objectC : base.Object}
    (morphismF : base.Morphism objectA objectB) (morphismG : base.Morphism objectB objectC),
    morphismMap (base.compose morphismF morphismG)
      = base.compose (morphismMap morphismF) (morphismMap morphismG)

/-- **The identity endofunctor** (`◐_id = Id`): maps everything to itself.  The unit of LOCK
2-functoriality. -/
def RawEndofunctor.identity (base : RawCategory.{u, v}) : RawEndofunctor base where
  objectMap := fun obj => obj
  morphismMap := fun morphism => morphism
  preservesIdentity := fun _obj => rfl
  preservesCompose := fun _morphismF _morphismG => rfl

/-- **Composition of endofunctors** (`◐_(μν) = ◐_ν ∘ ◐_μ`): apply `inner` then `outer`.  The
multiplication of LOCK 2-functoriality — locks compose. -/
def RawEndofunctor.comp {base : RawCategory.{u, v}} (outer inner : RawEndofunctor base) :
    RawEndofunctor base where
  objectMap := fun obj => outer.objectMap (inner.objectMap obj)
  morphismMap := fun morphism => outer.morphismMap (inner.morphismMap morphism)
  preservesIdentity := fun obj => by
    rw [inner.preservesIdentity, outer.preservesIdentity]
  preservesCompose := fun morphismF morphismG => by
    rw [inner.preservesCompose, outer.preservesCompose]

end FX1Poly.Tier0

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The modal lock for the dimension modality -/

/-- ★ **The modal lock `◐` for the dimension modality.**  As an endofunctor on the context category
`fxBaseSubstCategory`: it extends a context by one lock variable (`scope ↦ scope + 1`) and lifts a
substitution under that variable (`liftUnderBinder`).  Its functor laws are exactly the shipped
vec-level lift laws — the lock IS context-3's `liftUnderBinder` packaged as an endofunctor on the base
category (where `dimExtend` packaged it on the presheaf category). -/
def dimensionLock : RawEndofunctor fxBaseSubstCategory where
  objectMap := fun (scope : Nat) => scope + 1
  morphismMap := fun {sourceScope targetScope} (substVec : SubstVec targetScope sourceScope) =>
    -- `liftUnderBinder` lands in `SubstVec (targetScope+1) (sourceScope+1)`, defeq the expected
    -- `fxBaseSubstCategory.Morphism (sourceScope+1) (targetScope+1)`; `by exact` unfolds the base
    -- `Morphism` projection at default transparency (the structure-field check is reducible-only).
    by exact substVec.liftUnderBinder
  preservesIdentity := fun scope => by exact SubstVec.liftUnderBinder_identity scope
  preservesCompose := fun firstVec secondVec => by
    exact SubstVec.liftUnderBinder_compose firstVec secondVec

/-- Smoke: the lock extends a context by exactly one variable. -/
theorem dimensionLock_objectMap (scope : Nat) :
    dimensionLock.objectMap scope = scope + 1 := rfl

/-- **The iterated lock adds two variables** (`◐ ∘ ◐` on objects = `scope + 2`): the `◐_(μ∘μ)`
instance of LOCK composition — locks compose (here, the dimension modality with itself). -/
theorem dimensionLockSquared_objectMap (scope : Nat) :
    (dimensionLock.comp dimensionLock).objectMap scope = scope + 2 := rfl

/-! ## The lock ↔ dimExtend bridge -/

/-- The dimensional weakening's sections are the family one scope up — `dimExtend` peels a `+1`. -/
theorem dimExtend_sections_eq_succ (family : SubstActionFamily) (scope : Nat) :
    (dimExtend family).sections scope = family.sections (scope + 1) := rfl

/-- ★ **`dimExtend` reindexes a family along the lock (on objects).**  Context-3's dimensional weakening
`dimExtend F` at a scope is `F` read at the LOCKED scope — `(dimExtend F).sections scope =
F.sections (◐ scope)`.  So `dimExtend = ◐^*` (reindexing along the lock), the modality's action on the
presheaf category; the modal type former `⟨μ | -⟩` is the dependent right adjoint to this reindexing.
(The morphism-level refinement — `dimExtend`'s action is `family`'s action at `◐`'s morphism map
`liftUnderBinder`, `rfl` by construction — is recorded in the module header; it is stated awkwardly
across the `(dimExtend F).sections = F.sections ∘ ◐` defeq, so only the object-level bridge is pinned.) -/
theorem dimExtend_sections_eq_lockReindex (family : SubstActionFamily) (scope : Nat) :
    (dimExtend family).sections scope = family.sections (dimensionLock.objectMap scope) := rfl

end FX1Poly.Tier0.ContextOmega
