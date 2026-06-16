import FX1Poly.Tier0.Context.RepresentableMapCategory
import FX1Poly.Tier0.Context.InternalSconing
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecRMC
import FX1Poly.Tier0.Context.Instances.Renaming.FxBaseRenamingVecGlobalSections
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstGlobalSections

/-! # The context ω-category — Tier-0 axis root (`context-0` design-lock)

This is the root interface of the **context axis**: the category of contexts
and substitutions, developed as its own ω-category that the other axes
(`.term`, `.type`, `.mode`, `.protocol`) plug into at `Core/`.  It bundles the
shipped L0 bricks into one `ContextAxis` interface and exhibits the concrete FX
witness `fxContextAxis`, proving L0 is inhabited.  It does NOT prove the tower
(L1–L5) — those fill the slots declared here.

## The two-category structure (Uemura mode separation)

The context axis is the **pair** renaming-RMC / substitution-category, NOT a
single category: the renamings are the **representable maps**
(`fxBaseRenamingVecRMC : RepresentableMapCategory`), and the substitutions are
the bigger CwF base (`fxBaseSubstCategory : RawCategory`).  This is Uemura's
renaming-mode / substitution-mode separation, the structure normalization
(NbE) runs on.

## Locked decisions

1. **Extrinsic.**  Objects are scopes, morphisms are substitution/renaming
   vectors — no intrinsic `Con/Ty/Tm/Sub` (Lean strict-positivity rejects the
   Ctx-indexed `Ty` mutual block; that is *why* FX is `RawTerm` + extrinsic
   `HasType`).
2. **Two-category.**  renaming-RMC + substitution-`RawCategory`, both shipped.
3. **Abstract mode.**  `ContextAxis` is parameterized over a `ContextModeData`;
   the lock slot `lockOn` is filled by an abstract modality.  The concrete FX
   mode theory binds at `fib-3`, never here.  The L0 witness is at the
   `trivialMode` (one mode, identity lock).
4. **Substitution split.**  The context axis owns the *category* of
   substitutions; the substitution *operation* (the SSC algebra / Allais fold)
   is `Tier0/Term`.
5. **Cross-axis → Core.**  Definitional univalence, transpension, the Uemura
   type-former bijection, the concrete modal CwF, CwF-initiality, and universe
   univalence ship in `Core/`, not here.
6. **L0 = 0-truncation of L5.**  This 1-categorical interface is the
   0-truncation target of the marked (∞,ω) structure (L5); it does not
   pre-bake (∞,ω).
7. **No Bool theater.**  Status is which `theorem`s exist, not `hasX : Bool`
   construction-ledgers.  ADOPTED EXCEPTION (hybrid): a `fxX_has<CrossAxisCore> : Bool := false`
   CROSS-AXIS deferral marker IS the honest idiom — it names WHERE the deferred content ships
   (`fib-3` / `×type` / `×mode`), is `#assert_no_axioms`-gated, and never fakes a `true`.  What #7
   forbids is the IN-CORE status-ledger (a `hasX : Bool` restating "no theorem yet" for content that
   belongs in this file); those are trimmed in favour of the absent theorem + the prose deferral.
8. **Zero-axiom, Init-only.**

## Module layout (`Tier0/Context/`)

* L0 (shipped): `RepresentableMapCategory`, `Instances/{Renaming,Subst,ThinScope}`,
  `InternalSconing`, `FireTriangle`, `AxisObligation`, and this root.
* L1 mode slot: `Modal/` (abstract interface; concrete locks → `Core/`).
* L4 context-univalence: `Univalence/` (SIP-for-contexts, observational subst).
* L5 frontier: `Directed/`, `InfinityOmega/`, `SelfClassify/`.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

universe u v

/-- Abstract mode data — the parameter the context axis is fibered over.

This is the *minimal* interface a mode theory must expose for the context
category to be modal: a type of modes, hom-types of modalities (1-cells), and
the identity modality.  The full mode 2-category is `mode-0`'s deliverable; the
gluing (binding a concrete mode theory) is `fib-3`.  Keeping this abstract is
the purity lock — the context axis imports no concrete mode theory. -/
structure ContextModeData where
  /-- The type of modes (places). -/
  Mode : Type
  /-- Hom-types of modalities (1-cells between modes). -/
  Modality : Mode → Mode → Type
  /-- The identity modality at each mode. -/
  idModality : (modeObject : Mode) → Modality modeObject modeObject

/-- A raw endofunctor on a category — the vehicle for the abstract lock slot.

A modality `μ` acts on the context category by a lock `◐_μ`, an endofunctor.
At the trivial mode the lock is the identity (`RawEndofunctor.identity`); the
concrete modal locks are `context-4`'s deliverable, shipping in `Core/`. -/
structure RawEndofunctor (category : RawCategory.{u, v}) where
  /-- Action on objects. -/
  mapObject : category.Object → category.Object
  /-- Action on morphisms. -/
  mapMorphism : {objectA objectB : category.Object} →
                category.Morphism objectA objectB →
                category.Morphism (mapObject objectA) (mapObject objectB)
  /-- Preserves identity. -/
  preservesIdentity : ∀ (objectA : category.Object),
    mapMorphism (category.identity objectA) =
      category.identity (mapObject objectA)
  /-- Preserves composition. -/
  preservesComposition :
    ∀ {objectA objectB objectC : category.Object}
      (morphismF : category.Morphism objectA objectB)
      (morphismG : category.Morphism objectB objectC),
    mapMorphism (category.compose morphismF morphismG) =
      category.compose (mapMorphism morphismF) (mapMorphism morphismG)

/-- The identity endofunctor — the trivial-mode lock. -/
def RawEndofunctor.identity (category : RawCategory.{u, v}) :
    RawEndofunctor category where
  mapObject := fun object => object
  mapMorphism := fun morphism => morphism
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- The **context axis** bundle, parameterized over abstract mode data.

Bundles the two-category structure (renaming-RMC + substitution-`RawCategory`),
the global-sections functors (closed renamings / closed terms — the sconing
substrate), the abstract lock slot, and the Fire-Triangle leg.  The inclusion
renaming ⊂ substitution and comprehension are `context-1`; the Uemura bijection
is `context-2` (→ `Core/`). -/
structure ContextAxis (modeData : ContextModeData) where
  /-- The renaming-mode: the representable-map category (variables / thin). -/
  renamingMode : RepresentableMapCategory.{0, 0}
  /-- The substitution-mode: the CwF base category (terms). -/
  substMode : RawCategory.{0, 0}
  /-- Global sections of the renaming category (closed renamings). -/
  renamingGlobalSections : GlobalSections.{0, 0, 0} renamingMode.underlying
  /-- Global sections of the substitution category (closed terms). -/
  substGlobalSections : GlobalSections.{0, 0, 0} substMode
  /-- The abstract lock slot: each modality acts on the context category by an
  endofunctor.  Concrete locks (`context-4`) ship in `Core/`. -/
  lockOn : {sourceMode targetMode : modeData.Mode} →
           modeData.Modality sourceMode targetMode → RawEndofunctor substMode
  /-- The Fire-Triangle leg this axis restricts (substrate restricts none). -/
  fireTriangleLeg : Option FireTriangleLeg

/-- The trivial mode: one mode, only the identity modality.  The L0 witness
lives here — the non-modal context category with identity locks. -/
def trivialMode : ContextModeData where
  Mode := Unit
  Modality := fun _ _ => Unit
  idModality := fun _ => ()

/-- ★ The L0 witness — the FX context axis at the trivial mode, wiring the
shipped renaming RMC, substitution category, and both global-sections functors.
Its existence is the proof that L0 (the two-category CwF spine) is delivered;
the design-lock has teeth because `ContextAxis` is now a type the whole
`context-*` track must satisfy. -/
def fxContextAxis : ContextAxis trivialMode where
  renamingMode := fxBaseRenamingVecRMC
  substMode := fxBaseSubstCategory
  renamingGlobalSections := fxBaseRenamingVecGlobalSections
  substGlobalSections := fxBaseSubstGlobalSections
  lockOn := fun _ => RawEndofunctor.identity fxBaseSubstCategory
  fireTriangleLeg := none

/-- The renaming-mode of the FX context axis is the shipped representable-map
category. -/
theorem fxContextAxis_renamingMode :
    fxContextAxis.renamingMode = fxBaseRenamingVecRMC := rfl

/-- The substitution-mode of the FX context axis is the shipped CwF base
category. -/
theorem fxContextAxis_substMode :
    fxContextAxis.substMode = fxBaseSubstCategory := rfl

/-- The substrate restricts no Fire-Triangle leg. -/
theorem fxContextAxis_fireTriangleLeg :
    fxContextAxis.fireTriangleLeg = none := rfl

/-- At the trivial mode the lock is the identity endofunctor — the design
intent (concrete locks are deferred to `context-4` / `Core/`). -/
theorem fxContextAxis_trivialLock_isIdentity (modality : Unit) :
    (@ContextAxis.lockOn trivialMode fxContextAxis () () modality) =
      RawEndofunctor.identity fxBaseSubstCategory := rfl

end FX1Poly.Tier0
