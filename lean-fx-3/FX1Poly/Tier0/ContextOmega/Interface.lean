import FX1Poly.Tier0.FxBaseRenamingVecRMC
import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections

/-! # Tier0/ContextOmega — the context axis as a standalone ω-category (context-0)

This module locks the **context** PolyCell axis as its own Tier-0 object, the
load-bearing ω-category of the four (context · mode · term · type).  It is the
DESIGN-LOCK of the `context-*` track: the interface every later context brick
extends.

## Why this namespace exists (the reorganization)

The shipped context substrate is real but was scattered across the flat
`Tier0/` bag under the *technique* framing (`FxBaseSubst*`, `FxBaseRenaming*`,
`RepresentableMapCategory`, `InternalSconing`).  `Tier0/ContextOmega/` is the
four-axis-aligned home: it does NOT duplicate the substrate — it REFERENCES the
shipped `fxBaseRenamingVecRMC` / `fxBaseRenamingVecGlobalSections`.

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
work.

Zero external dependencies; raw Lean 4 + Init only.  All declarations are
structures, total functions, and constructor witnesses — no `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

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

/-! ## Reserved interface skeletons (the design-lock the context-* track fills) -/

/-- **LEFT / comprehension skeleton** (context-1).  Context extension
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

/-- **RIGHT / transpension skeleton** (context-3).  The transpension
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

/-- **Modal lock skeleton** `◐_μ` (context-4, references `mode-0`).  The
modal context extension: the left adjoint to the modality `⟦μ⟧`, the categorical
realization of the `.context ↔ .mode` correspondence.  2-functoriality + the
dependent-right-adjoint coherence are context-4's obligation. -/
structure LockExtension (base : ContextOmegaCategory.{u, v, w}) where
  /-- The lock object-map `◐_μ` on contexts. -/
  lockObject :
    base.representableBase.underlying.Object → base.representableBase.underlying.Object

end FX1Poly.Tier0.ContextOmega
