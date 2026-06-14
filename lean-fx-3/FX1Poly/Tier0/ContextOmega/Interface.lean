import FX1Poly.Tier0.FxBaseRenamingVecRMC
import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections

/-! # Tier0/ContextOmega — the context axis as a standalone ω-category (context-0)

This module locks the **context** PolyCell axis as its own Tier-0 object, the
load-bearing ω-category of the four (context · mode · term · type).  It is the
DESIGN-LOCK of the `context-*` track: the interface every later context brick
extends, and the honest construction ledger that records, in the four-axis
vocabulary, exactly what is built versus reserved.

## Why this namespace exists (the reorganization)

The shipped context substrate is real but was scattered across the flat
`Tier0/` bag under the *technique* framing (`FxBaseSubst*`, `FxBaseRenaming*`,
`RepresentableMapCategory`, `InternalSconing`) and tracked by the OLD 13-axis
`Core/PolyProfile` honesty ledger.  That ledger is organized by paper
(Shape · Gray · Saturation · …), which is orthogonal to the four PolyCell axes.
`Tier0/ContextOmega/` is the four-axis-aligned home: it does NOT duplicate the
substrate — it REFERENCES the shipped `fxBaseRenamingVecRMC` /
`fxBaseRenamingVecGlobalSections` — and it carries the context slice of the
honesty ledger, superseding the scattered per-technique ledger.

## The context ω-category (dimensions)

  * dim 0 — contexts (objects of the representable map category)
  * dim 1 — substitutions, with the distinguished *display* maps (context
    projections) as the representable sub-class; comprehension (context
    extension) is left adjoint to reindexing, the dimensional adjoint string
    `Ⅎ ⊣ Σ ⊣ Ω ⊣ Π ⊣ ◊` runs to the right (transpension `◊` is the rightmost,
    historically-neglected join), and the lock `◐_μ` is the modal extension.
  * dim ≥ 2 — the substitution homotopy layer (reserved, context-20).

## Honest boundary surfaced here

`fxBaseRenamingVecRMC` chose its representable class to be the categorical
*isomorphisms* — the first genuine non-degenerate CwR, but NOT yet the genuine
display-map class.  The display projection (weakening `scope+1 ⟶ scope`) is not
an isomorphism, so `ComprehensionStructure` is a SKELETON here: inhabiting it
for the FX base requires promoting the representable class from isos to display
maps, which is exactly the `context-1`/`context-2` (Uemura bijection, SN-088)
work.  The ledger records this as `hasComprehensionPromoted = false`.

Zero external dependencies; raw Lean 4 + Init only.  All declarations are
structures, total functions, full-enumeration `Bool` projections, and `rfl`
pins — no `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

universe u v w

/-- **The context ω-category at Tier 0.**  A standalone axis object packaging
the (modal) representable map category of contexts-and-substitutions together
with its global-sections (closed-points) functor.  Comprehension, the
right-adjoint transpension string, and the modal lock are layered on top as the
`ComprehensionStructure` / `TranspensionRightAdjoint` / `LockExtension`
extensions (filled by `context-1`/`context-3`/`context-4`). -/
structure ContextOmegaCategory where
  /-- Dim 0+1: the representable map category of contexts and substitutions
  (Uemura's CwR — objects are contexts, the representable class is the display
  maps). -/
  representableBase : RepresentableMapCategory.{u, v}
  /-- The global-sections functor — the closed points of every context.  For a
  type theory, `Γ(ctx)` is the closed substitutions into `ctx`. -/
  globalSections : GlobalSections.{u, v, w} representableBase.underlying

/-- **The FX context ω-category.**  Bridges to the shipped genuine CwR
`fxBaseRenamingVecRMC` (the three CwR axioms hold by construction — see
`FxBaseRenamingVecRMC.lean`) and its representable global-sections functor at
the terminal scope.  No new substrate is built; this is the four-axis-aligned
re-presentation of the shipped context category. -/
def fxContextOmega : ContextOmegaCategory.{0, 0, 0} where
  representableBase := fxBaseRenamingVecRMC
  globalSections := fxBaseRenamingVecGlobalSections

/-- The FX context ω-category's base is exactly the shipped renaming CwR — so
the three CwR axioms (pullback / iso / composition closure) ride along. -/
theorem fxContextOmega_base_eq_renamingVecRMC :
    fxContextOmega.representableBase = fxBaseRenamingVecRMC := rfl

/-- The FX context ω-category's global sections is exactly the shipped
terminal-scope representable functor. -/
theorem fxContextOmega_globalSections_eq_renamingVecGlobalSections :
    fxContextOmega.globalSections = fxBaseRenamingVecGlobalSections := rfl

/-- **Global sections genuinely pick unique closed points.**  The sections of
the FX context ω-category at any context form a subsingleton — there is exactly
one closed substitution into the terminal context — re-exposing the shipped
`fxBaseRenamingVecGlobalSections_terminal_subsingleton` through the axis object.
This is the non-degeneracy witness that the design-lock is not vacuous. -/
theorem fxContextOmega_globalSections_terminal_subsingleton (scope : Nat)
    (firstSection secondSection : fxContextOmega.globalSections.sections scope) :
    firstSection = secondSection :=
  fxBaseRenamingVecGlobalSections_terminal_subsingleton scope firstSection secondSection

/-! ## The honest construction ledger (context slice of the four-axis ledger) -/

/-- **How far the context ω-category is built**, in the four-axis vocabulary.
A monotone ladder: each level subsumes the previous.  This SUPERSEDES, for the
context axis, the scattered `Core/PolyProfile` technique-ledger
(`fxProfile_universeConstructionLevel`, the `FxBaseSubst*`/`FxBaseRenaming*`
bricks).  `context-1` … `context-21` advance it. -/
inductive ContextOmegaConstructionLevel where
  /-- The representable base + global sections are built (this design-lock). -/
  | representableBaseAndGlobalSections
  /-- Comprehension promoted into the Tier-0 RMC (context-1, SUBSTVEC-4). -/
  | comprehensionPromoted
  /-- The Uemura bijection: type-formers ↔ representable nat-trans (context-2). -/
  | uemuraBijection
  /-- The right-adjoint transpension string `… ⊣ Π ⊣ ◊` (context-3). -/
  | rightAdjointTranspension
  /-- The modal lock `◐_μ` over a mode theory (context-4). -/
  | modalLockExtended
  /-- The dim-2 substitution homotopy layer (context-20). -/
  | dimTwoHomotopy
  /-- The standalone modal RMC capstone (context-21). -/
  | standaloneModalRMC
  deriving DecidableEq, Repr

/-- The representable base is built at every level (the floor). -/
def ContextOmegaConstructionLevel.hasRepresentableBase :
    ContextOmegaConstructionLevel → Bool
  | _ => true

/-- The global-sections functor is built at every level. -/
def ContextOmegaConstructionLevel.hasGlobalSections :
    ContextOmegaConstructionLevel → Bool
  | _ => true

/-- Comprehension is promoted from level `comprehensionPromoted` onward. -/
def ContextOmegaConstructionLevel.hasComprehensionPromoted :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => true
  | .uemuraBijection => true
  | .rightAdjointTranspension => true
  | .modalLockExtended => true
  | .dimTwoHomotopy => true
  | .standaloneModalRMC => true

/-- The Uemura bijection holds from level `uemuraBijection` onward. -/
def ContextOmegaConstructionLevel.hasUemuraBijection :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => false
  | .uemuraBijection => true
  | .rightAdjointTranspension => true
  | .modalLockExtended => true
  | .dimTwoHomotopy => true
  | .standaloneModalRMC => true

/-- The right-adjoint transpension string is built from `rightAdjointTranspension`. -/
def ContextOmegaConstructionLevel.hasRightAdjointTranspension :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => false
  | .uemuraBijection => false
  | .rightAdjointTranspension => true
  | .modalLockExtended => true
  | .dimTwoHomotopy => true
  | .standaloneModalRMC => true

/-- The modal lock is built from `modalLockExtended` onward. -/
def ContextOmegaConstructionLevel.hasModalLock :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => false
  | .uemuraBijection => false
  | .rightAdjointTranspension => false
  | .modalLockExtended => true
  | .dimTwoHomotopy => true
  | .standaloneModalRMC => true

/-- The dim-2 homotopy layer is built from `dimTwoHomotopy` onward. -/
def ContextOmegaConstructionLevel.hasDimTwoHomotopy :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => false
  | .uemuraBijection => false
  | .rightAdjointTranspension => false
  | .modalLockExtended => false
  | .dimTwoHomotopy => true
  | .standaloneModalRMC => true

/-- The standalone modal RMC capstone holds only at the top level.  Fully
enumerated (no specific-arm-then-wildcard) to stay propext-free. -/
def ContextOmegaConstructionLevel.hasStandaloneModalRMC :
    ContextOmegaConstructionLevel → Bool
  | .representableBaseAndGlobalSections => false
  | .comprehensionPromoted => false
  | .uemuraBijection => false
  | .rightAdjointTranspension => false
  | .modalLockExtended => false
  | .dimTwoHomotopy => false
  | .standaloneModalRMC => true

/-- The honest current level of the FX context ω-category: representable base +
global sections, no comprehension promotion / Uemura / transpension / lock /
homotopy yet. -/
def fxContextOmegaConstructionLevel : ContextOmegaConstructionLevel :=
  .representableBaseAndGlobalSections

/-- BUILT: the FX context ω-category has its representable base. -/
theorem fxContextOmega_hasRepresentableBase :
    fxContextOmegaConstructionLevel.hasRepresentableBase = true := rfl

/-- BUILT: the FX context ω-category has its global-sections functor. -/
theorem fxContextOmega_hasGlobalSections :
    fxContextOmegaConstructionLevel.hasGlobalSections = true := rfl

/-- GAP → context-1: comprehension is not yet promoted into the Tier-0 RMC
(`SubstVec.cons` ships, but the representable class must first move from isos to
display maps). -/
theorem fxContextOmega_hasNoComprehensionPromoted :
    fxContextOmegaConstructionLevel.hasComprehensionPromoted = false := rfl

/-- GAP → context-2: the Uemura bijection (SN-088) is not yet established. -/
theorem fxContextOmega_hasNoUemuraBijection :
    fxContextOmegaConstructionLevel.hasUemuraBijection = false := rfl

/-- GAP → context-3: the right-adjoint transpension string is not yet built. -/
theorem fxContextOmega_hasNoRightAdjointTranspension :
    fxContextOmegaConstructionLevel.hasRightAdjointTranspension = false := rfl

/-- GAP → context-4: the modal lock `◐_μ` is not yet built. -/
theorem fxContextOmega_hasNoModalLock :
    fxContextOmegaConstructionLevel.hasModalLock = false := rfl

/-- GAP → context-20: the dim-2 substitution homotopy layer is not yet built. -/
theorem fxContextOmega_hasNoDimTwoHomotopy :
    fxContextOmegaConstructionLevel.hasDimTwoHomotopy = false := rfl

/-- GAP → context-21: the standalone modal RMC capstone is not yet assembled. -/
theorem fxContextOmega_hasNoStandaloneModalRMC :
    fxContextOmegaConstructionLevel.hasStandaloneModalRMC = false := rfl

/-! ## Reserved interface skeletons (the design-lock the context-* track fills) -/

/-- **LEFT / comprehension skeleton** (context-1 #1535).  Context extension
`ctx ↦ ctx.A` with its display projection, required to be a representable
(display) map.  Inhabiting this for the FX base promotes `SubstVec.cons` and
forces the representable class to the genuine display maps — see the honest
boundary in the module header. -/
structure ComprehensionStructure (base : ContextOmegaCategory.{u, v, w}) where
  /-- Context extension on objects (the well-scoped `scope ↦ scope + 1`). -/
  extendContext :
    base.representableBase.underlying.Object → base.representableBase.underlying.Object
  /-- The display projection out of the extended context (the weakening). -/
  displayProjection : (ctx : base.representableBase.underlying.Object) →
    base.representableBase.underlying.Morphism (extendContext ctx) ctx
  /-- The display projection is a representable (display) map. -/
  displayIsRepresentable : ∀ (ctx : base.representableBase.underlying.Object),
    base.representableBase.representableMaps.member (displayProjection ctx)

/-- **RIGHT / transpension skeleton** (context-3 #1537).  The transpension
functor `◊`, right adjoint to the dimensional Π — the rightmost, historically
neglected join in `Ⅎ ⊣ Σ ⊣ Ω ⊣ Π ⊣ ◊` (Nuyts-Devriese 2008.08533).  Over a
fresh/affine dimension it is universal name-abstraction; over the cartesian cube
it is the amazing `√`.  context-3 supplies the adjunction (recorded in its
docstring) for finite/affine multipliers. -/
structure TranspensionRightAdjoint (base : ContextOmegaCategory.{u, v, w}) where
  /-- The transpension object-map `◊`. -/
  transpensionObject :
    base.representableBase.underlying.Object → base.representableBase.underlying.Object
  /-- The dimensional product `Π` this is right adjoint to. -/
  dimensionalProduct :
    base.representableBase.underlying.Object → base.representableBase.underlying.Object

/-- **Modal lock skeleton** `◐_μ` (context-4 #1538, references `mode-0`).  The
modal context extension: the left adjoint to the modality `⟦μ⟧`, the categorical
realization of the `.context ↔ .mode` correspondence.  2-functoriality + the
dependent-right-adjoint coherence are context-4's obligation. -/
structure LockExtension (base : ContextOmegaCategory.{u, v, w}) where
  /-- The lock object-map `◐_μ` on contexts. -/
  lockObject :
    base.representableBase.underlying.Object → base.representableBase.underlying.Object

end FX1Poly.Tier0.ContextOmega
