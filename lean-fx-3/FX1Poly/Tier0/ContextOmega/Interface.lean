import FX1Poly.Tier0.RepresentableMapCategory

/-!
# Context omega-category — the modal representable map category interface (design-lock)

This module re-roots the **context axis** of PolyCell as a standalone
omega-category at Tier-0.  The context axis answers the question "what is a
context, and how do substitutions and modal locks act on it?".  Its
categorical home is the (modal) **Representable Map Category** of Uemura
2023 — a category whose objects are type theories and whose distinguished
representable maps are the display/projection substitutions.

## What this file locks

The non-modal representable-map-category interface already lives in
`FX1Poly.Tier0.RepresentableMapCategory` (`RepresentableMapCategory`,
`CwRMorphism`, the three closure axioms) and the concrete FX instances live
in `FX1Poly.Tier0.FxBaseSubst*` / `FxBaseRenamingVec*` / `FxThinScope*`.
This design-lock builds the **modal** layer on top of that surviving
substrate and nothing is duplicated:

  1. `CwRMorphism.compose` — composition of CwR-functors (the missing API
     companion to the shipped `CwRMorphism.identity`), needed to state lock
     pseudofunctoriality.
  2. `ModeSkeleton` — the minimal mode-theory interface the lock functors
     index over (modes, modalities, identity, composition, category laws).
     It is deliberately ABSTRACT: the rich mode omega-category is the mode
     axis (`Tier0/ModeOmega`, rebuilt separately) and will supply a
     `ModeSkeleton` instance.  Keeping context independent of mode's
     internals is exactly the "context and mode are sibling load-bearing
     axes that meet at Core/" discipline.
  3. `ModalRepresentableMapCategory` — Gratzer's multimodal model shape: a
     CwR per mode plus a CONTRAVARIANT lock CwR-functor per modality,
     pseudofunctorial (`lockIdentity`, `lockCompose`).  The lock is the
     left leg of the dependent right adjoint that interprets the modal
     type former; the adjoint itself is the `ModalLock`/`Transpension`
     rungs below.
  4. A zero-axiom NON-VACUITY witness: the terminal CwR carries a trivial
     one-mode identity-lock modal RMC (`fxContextModalRMCWitness`).  The
     interface is realizable, not vacuous.

## The context-axis module roadmap (rungs developed in sibling files)

Each rung is one file under `Tier0/ContextOmega/`, organized by the
left/middle/right adjoint structure of the context omega-category:

  * `Comprehension`   — LEFT: context extension as comprehension + Frobenius Sigma
  * `Uemura`          — MIDDLE: type-formers <-> representable natural transformations
  * `Transpension`    — RIGHT: the dimensional adjoint quadruple + pushouts of contexts
  * `ModalLock`       — the lock 2-functor + dependent right adjoints (consumes 3 above)
  * `Initiality`      — the syntactic CwF is the initial CwF
  * `Biequivalence`   — CwF ~= natural model ~= RMC ~= CwA ~= contextual category
  * `Strictification` — the local-universes coherence theorem
  * `Fibration`       — Jacobs fibred adjoints + Beck-Chevalley
  * `Sconing`         — synthetic Tait computability over the context base
  * `MultimodalNormalization` — Gratzer multimodal NbE over the modal base
  * (model rungs) `SimplicialModel`, `GroupoidModel`, `PresheafModel`,
    `CubicalSetModel`, `ForcingModel`, `Realizability`

The concrete instantiation of `ModalRepresentableMapCategory` by FX's real
context category (`fxBaseSubst*`) is the `ModalLock`/`Initiality` rungs; this
file fixes only the INTERFACE and proves it inhabitable.

Reference: Uemura, MSCS 33(3) 2023 (arXiv:1904.04097); Gratzer,
"Multimodal Dependent Type Theory", LMCS 2021 (arXiv:2011.15021).

Zero external dependencies.  Raw Lean 4 + Init only.  ASCII identifiers.
-/

namespace FX1Poly.Tier0

universe u v

/-- Composition of CwR-functors (representable-map-preserving functors).
The companion to the shipped `CwRMorphism.identity`; the two make
`RepresentableMapCategory` into a category of CwRs and let us state lock
pseudofunctoriality.  Zero-axiom: the functor-law fields chain via
`congrArg`/`Eq.trans`, never `propext`. -/
def CwRMorphism.compose {cwrA cwrB cwrC : RepresentableMapCategory.{u, v}}
    (functorF : CwRMorphism cwrA cwrB) (functorG : CwRMorphism cwrB cwrC) :
    CwRMorphism cwrA cwrC where
  mapObject := fun object => functorG.mapObject (functorF.mapObject object)
  mapMorphism := fun morphism => functorG.mapMorphism (functorF.mapMorphism morphism)
  preservesIdentity := fun object =>
    (congrArg functorG.mapMorphism (functorF.preservesIdentity object)).trans
      (functorG.preservesIdentity (functorF.mapObject object))
  preservesComposition := fun morphismF morphismG =>
    (congrArg functorG.mapMorphism
        (functorF.preservesComposition morphismF morphismG)).trans
      (functorG.preservesComposition
        (functorF.mapMorphism morphismF) (functorF.mapMorphism morphismG))
  preservesRepresentable := fun morphism memberWitness =>
    functorG.preservesRepresentable _ (functorF.preservesRepresentable morphism memberWitness)

/-- Left identity law for CwR-functor composition. -/
theorem CwRMorphism.identityCompose
    {cwrA cwrB : RepresentableMapCategory.{u, v}} (functorF : CwRMorphism cwrA cwrB) :
    CwRMorphism.compose (CwRMorphism.identity cwrA) functorF = functorF := rfl

/-- Right identity law for CwR-functor composition. -/
theorem CwRMorphism.composeIdentity
    {cwrA cwrB : RepresentableMapCategory.{u, v}} (functorF : CwRMorphism cwrA cwrB) :
    CwRMorphism.compose functorF (CwRMorphism.identity cwrB) = functorF := rfl

/-- CwR-functor composition is associative.  Together with the two identity
laws this makes representable map categories and their representable-map-
preserving functors into a genuine category — the ambient category the
context omega-category's lock functors live in. -/
theorem CwRMorphism.composeAssoc
    {cwrA cwrB cwrC cwrD : RepresentableMapCategory.{u, v}}
    (functorF : CwRMorphism cwrA cwrB) (functorG : CwRMorphism cwrB cwrC)
    (functorH : CwRMorphism cwrC cwrD) :
    CwRMorphism.compose (CwRMorphism.compose functorF functorG) functorH =
    CwRMorphism.compose functorF (CwRMorphism.compose functorG functorH) := rfl

end FX1Poly.Tier0

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0

universe u v w x

/-! ## The mode skeleton the lock functors index over -/

/-- The minimal mode-theory interface a modal RMC indexes over: modes
(objects), modalities (1-cells), identity, composition, and the three
category laws.  The 2-cell layer (modality transformations / keys) is the
`ModalLock` rung and the rich mode omega-category is the `Tier0/ModeOmega`
axis; this skeleton is the 1-truncation sufficient to state lock
pseudofunctoriality at the design-lock. -/
structure ModeSkeleton where
  /-- The modes (objects of the mode 2-category). -/
  Mode : Type w
  /-- The modalities (1-cells) between two modes. -/
  Modality : Mode → Mode → Type x
  /-- The identity modality at each mode. -/
  idModality : (mode : Mode) → Modality mode mode
  /-- Vertical composition of modalities. -/
  composeModality : {modeA modeB modeC : Mode} →
    Modality modeA modeB → Modality modeB modeC → Modality modeA modeC
  /-- Modality composition is associative. -/
  composeAssoc : ∀ {modeA modeB modeC modeD : Mode}
    (modalityF : Modality modeA modeB) (modalityG : Modality modeB modeC)
    (modalityH : Modality modeC modeD),
    composeModality (composeModality modalityF modalityG) modalityH =
    composeModality modalityF (composeModality modalityG modalityH)
  /-- Identity modality is a left unit. -/
  idLeft : ∀ {modeA modeB : Mode} (modality : Modality modeA modeB),
    composeModality (idModality modeA) modality = modality
  /-- Identity modality is a right unit. -/
  idRight : ∀ {modeA modeB : Mode} (modality : Modality modeA modeB),
    composeModality modality (idModality modeB) = modality

/-! ## The modal representable map category -/

/-- A **modal representable map category** over a mode skeleton (Gratzer's
multimodal model shape): a CwR at each mode, and a CONTRAVARIANT lock
CwR-functor for each modality, pseudofunctorial in the modality.

The contravariance (`Modality modeSource modeTarget` maps to a functor
`atMode modeTarget -> atMode modeSource`) is the defining feature of the
modal lock: a modality `mu : n -> m` locks the context at mode `m` down to
mode `n`, and the modal type former at `m` is right adjoint to this lock. -/
structure ModalRepresentableMapCategory (modeSkeleton : ModeSkeleton.{w, x}) where
  /-- The representable map category at each mode. -/
  atMode : modeSkeleton.Mode → RepresentableMapCategory.{u, v}
  /-- The lock CwR-functor of each modality (contravariant in the modality). -/
  lock : {modeSource modeTarget : modeSkeleton.Mode} →
    modeSkeleton.Modality modeSource modeTarget →
    CwRMorphism (atMode modeTarget) (atMode modeSource)
  /-- The identity modality locks to the identity functor. -/
  lockIdentity : ∀ (mode : modeSkeleton.Mode),
    lock (modeSkeleton.idModality mode) = CwRMorphism.identity (atMode mode)
  /-- The lock is a contravariant pseudofunctor:
  `lock (F then G) = lock G then lock F`. -/
  lockCompose : ∀ {modeA modeB modeC : modeSkeleton.Mode}
    (modalityF : modeSkeleton.Modality modeA modeB)
    (modalityG : modeSkeleton.Modality modeB modeC),
    lock (modeSkeleton.composeModality modalityF modalityG) =
    CwRMorphism.compose (lock modalityG) (lock modalityF)

/-! ## Non-vacuity: the interface is realizable

The terminal CwR (one object, one morphism — every morphism representable)
carries a trivial one-mode identity-lock modal RMC.  This proves the modal
interface is inhabitable; the FX-context instantiation is a later rung. -/

/-- The terminal category: one object, one morphism. -/
def terminalRawCategory : RawCategory.{u, v} where
  Object := PUnit
  Morphism := fun _ _ => PUnit
  identity := fun _ => PUnit.unit
  compose := fun _ _ => PUnit.unit
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- In the terminal category every morphism is representable. -/
def terminalRepresentableMaps : MorphismClass terminalRawCategory.{u, v} where
  member := fun _ => True
  memberDecidable := fun _ => isTrue True.intro

/-- The terminal representable map category (every morphism representable;
the three closure axioms hold trivially). -/
def terminalCwR : RepresentableMapCategory.{u, v} where
  underlying := terminalRawCategory
  representableMaps := terminalRepresentableMaps
  closedUnderPullback := fun _ _ _ =>
    ⟨{ pullbackObject := PUnit.unit
       projectionLeft := PUnit.unit
       projectionRight := PUnit.unit
       commutes := rfl
       isUniversal := fun _ _ _ _ => ⟨PUnit.unit, rfl, rfl⟩ }, True.intro⟩
  isomorphismsRepresentable := fun _ _ => True.intro
  closedUnderComposition := fun _ _ _ _ => True.intro

/-- The trivial mode skeleton: one mode, one (identity) modality. -/
def trivialModeSkeleton : ModeSkeleton.{w, x} where
  Mode := PUnit
  Modality := fun _ _ => PUnit
  idModality := fun _ => PUnit.unit
  composeModality := fun _ _ => PUnit.unit
  composeAssoc := fun _ _ _ => rfl
  idLeft := fun _ => rfl
  idRight := fun _ => rfl

/-- The trivial modal RMC over any base CwR: every mode is the base, every
lock is the identity functor.  Pseudofunctoriality holds by the CwR-functor
identity laws. -/
def trivialModalRMC (baseCwR : RepresentableMapCategory.{u, v}) :
    ModalRepresentableMapCategory.{u, v, w, x} trivialModeSkeleton where
  atMode := fun _ => baseCwR
  lock := fun _ => CwRMorphism.identity baseCwR
  lockIdentity := fun _ => rfl
  lockCompose := fun _ _ => rfl

/-- ★ The modal RMC interface is realizable: the terminal CwR carries a
modal representable map category.  This is the design-lock's non-vacuity
certificate. -/
def fxContextModalRMCWitness :
    ModalRepresentableMapCategory.{u, v, w, x} trivialModeSkeleton :=
  trivialModalRMC terminalCwR

/-- The witness's lock at the identity modality is the identity functor —
the non-vacuity witness computes the lock pseudofunctor correctly. -/
theorem fxContextModalRMCWitness_lock_identity :
    (fxContextModalRMCWitness.{u, v, w, x}).lock
      (trivialModeSkeleton.idModality PUnit.unit) =
    CwRMorphism.identity (terminalCwR.{u, v}) := rfl

end FX1Poly.Tier0.ContextOmega
