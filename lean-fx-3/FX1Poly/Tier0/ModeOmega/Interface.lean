import FX1Poly.MTTNorm.ModeTheory

/-! # Tier0/ModeOmega — the mode axis as a standalone ω-category (mode-0)

This module locks the **mode** PolyCell axis as its own Tier-0 object — the SECOND load-bearing
ω-category of the four (context · mode · term · type), the one the kernel is *fibered over* (every
binding's grade vector lives in a product of mode-indexed structure-class algebras).  It is the
DESIGN-LOCK of the `mode-*` track: the interface every later mode brick extends, and the honest
construction ledger that records, in the four-axis vocabulary, exactly what is built versus reserved.

## Why this namespace exists (the reorganization)

The shipped mode substrate is real but was scattered — the mode 2-category lives under
`MTTNorm/ModeTheory.lean` (Gratzer's mode-theory interface + the concrete `fxModeTheory`), and the
per-dimension structure-class certificates (effect/trust/security/mutation/overflow/lifetime/session/
version — bounded-join-semilattices, ordered semirings, total-order chains, the M3 diamond, preorders,
involutions, categories) live under `Modal/`.  `Tier0/ModeOmega/` is the four-axis-aligned home: it does
NOT duplicate the substrate — it REFERENCES the shipped `fxModeTheory` — and it carries the mode slice of
the honesty ledger.

## The mode ω-category (dimensions)

  * dim 0 — modes (objects of the mode theory; FX's `FXModeAtom`: pure, linear, affine, …).
  * dim 1 — modalities (1-cells, the mode shifts and their composites; FX's `FXModePath`), with strict
    category laws (`composeAssoc` / `identityLeft` / `identityRight`).
  * dim 2 — modality transformations / coherences (2-cells), with the convergent 3-polygraph making
    2-cell equality decidable (reserved, mode-3).
  * the per-mode **structure-class certificate** (mode-2 = DIM-CLASS for modes) attaches to each mode
    the lattice / semiring / order shape its grade algebra is; the **adjoint strings** (mode-4) and the
    **transpension universal modality** (mode-11) run to the right.

## Honest boundary surfaced here

`fxModeTheory` is the strict 2-category's dim-0/dim-1 core (modes + modalities + category laws) — a
genuine non-trivial free-path category.  The dim-2 coherences (2-cells), the structure-class certificate
wiring, the adjoint strings, and the transpension universal modality are RESERVED: the design-lock marks
them as construction-ladder GAPs the `mode-*` track fills.

Zero external dependencies; raw Lean 4 + Init only.  All declarations are structures, total functions,
full-enumeration `Bool` projections, `rfl` pins, and constructor witnesses — no `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModeOmega.lean`. -/

namespace FX1Poly.Tier0.ModeOmega

open FX1Poly.MTTNorm

/-- **The mode ω-category at Tier 0.**  A standalone axis object packaging the mode theory — the strict
2-category whose 0-cells are modes, 1-cells are modalities, and 2-cells are modality coherences.  The
per-mode structure-class certificate, the adjoint strings, and the transpension universal modality are
layered on top as the `StructureClassCertificate` / `AdjointStringExtension` / `TranspensionModeModality`
extensions (filled by `mode-2`/`mode-4`/`mode-11`). -/
structure ModeOmegaCategory where
  /-- Dim 0+1: the mode theory (Gratzer's finitary 2-category — modes, modalities, category laws). -/
  modeTheory : ModeTheory

/-- **The FX mode ω-category.**  Bridges to the shipped `fxModeTheory` (the free finite-path category
over the accepted FX mode shifts — the category laws hold by construction, see `MTTNorm/ModeTheory.lean`).
No new substrate is built; this is the four-axis-aligned re-presentation of the shipped mode theory. -/
def fxModeOmega : ModeOmegaCategory where
  modeTheory := fxModeTheory

/-- The FX mode ω-category's mode theory is exactly the shipped `fxModeTheory` — so the strict category
laws (associativity / unit) ride along. -/
theorem fxModeOmega_modeTheory_eq_fxModeTheory :
    fxModeOmega.modeTheory = fxModeTheory := rfl

/-- **The FX mode polygraph is non-degenerate.**  It carries a genuine NON-identity modality — the
`ghost ⟶ pure` shift — unlike the one-object `trivialModeTheory` whose only modality is the identity.
This is the non-degeneracy witness that the design-lock is not vacuous. -/
theorem fxModeOmega_hasNonIdentityModality :
    Nonempty (fxModeOmega.modeTheory.Modality FXModeAtom.ghost FXModeAtom.pure) :=
  ⟨FXModePath.cons FXModeShift.ghostToPure (FXModePath.identity FXModeAtom.pure)⟩

/-- **Modalities compose strictly-associatively in the FX mode ω-category.**  Re-exposing the shipped
`fxModeTheory.composeAssoc` through the axis object: the dim-1 layer is a strict category. -/
theorem fxModeOmega_composeAssoc {modeA modeB modeC modeD : fxModeOmega.modeTheory.Mode}
    (modalityF : fxModeOmega.modeTheory.Modality modeA modeB)
    (modalityG : fxModeOmega.modeTheory.Modality modeB modeC)
    (modalityH : fxModeOmega.modeTheory.Modality modeC modeD) :
    fxModeOmega.modeTheory.composeModality
        (fxModeOmega.modeTheory.composeModality modalityF modalityG) modalityH =
      fxModeOmega.modeTheory.composeModality modalityF
        (fxModeOmega.modeTheory.composeModality modalityG modalityH) :=
  fxModeOmega.modeTheory.composeAssoc modalityF modalityG modalityH

/-! ## The honest construction ledger (mode slice of the four-axis ledger) -/

/-- **How far the mode ω-category is built**, in the four-axis vocabulary.  A monotone ladder: each
level subsumes the previous.  `mode-1` … `mode-21` advance it. -/
inductive ModeOmegaConstructionLevel where
  /-- The mode-theory interface + the concrete `fxModeTheory` (this design-lock). -/
  | modeTheoryInterface
  /-- The strict 2-category core + the `fxModeTheory` round-trip (mode-1). -/
  | strictTwoCategoryCore
  /-- The per-mode structure-class certificate = DIM-CLASS for modes (mode-2). -/
  | structureClassCertificate
  /-- The convergent 3-polygraph making 2-cell equality decidable (mode-3). -/
  | threeCellsDecidable
  /-- The full per-modality adjoint strings — sharp + transpension + cohesion (mode-4). -/
  | adjointStrings
  /-- The transpension universal modality recovering Gel/Glue/√/nominal (mode-11). -/
  | transpensionUniversalModality
  /-- The standalone (weak) higher-polygraph mode ω-category capstone (mode-21). -/
  | standaloneModeOmega
  deriving DecidableEq, Repr

/-- The mode-theory interface is present at every level (the floor). -/
def ModeOmegaConstructionLevel.hasModeTheoryInterface :
    ModeOmegaConstructionLevel → Bool
  | _ => true

/-- The strict 2-category core round-trip is built from `strictTwoCategoryCore` onward. -/
def ModeOmegaConstructionLevel.hasStrictTwoCategoryCore :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => true
  | .structureClassCertificate => true
  | .threeCellsDecidable => true
  | .adjointStrings => true
  | .transpensionUniversalModality => true
  | .standaloneModeOmega => true

/-- The structure-class certificate is built from `structureClassCertificate` onward. -/
def ModeOmegaConstructionLevel.hasStructureClassCertificate :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => false
  | .structureClassCertificate => true
  | .threeCellsDecidable => true
  | .adjointStrings => true
  | .transpensionUniversalModality => true
  | .standaloneModeOmega => true

/-- Decidable 2-cell equality is built from `threeCellsDecidable` onward. -/
def ModeOmegaConstructionLevel.hasThreeCellsDecidable :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => false
  | .structureClassCertificate => false
  | .threeCellsDecidable => true
  | .adjointStrings => true
  | .transpensionUniversalModality => true
  | .standaloneModeOmega => true

/-- The adjoint strings are built from `adjointStrings` onward. -/
def ModeOmegaConstructionLevel.hasAdjointStrings :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => false
  | .structureClassCertificate => false
  | .threeCellsDecidable => false
  | .adjointStrings => true
  | .transpensionUniversalModality => true
  | .standaloneModeOmega => true

/-- The transpension universal modality is built from `transpensionUniversalModality` onward. -/
def ModeOmegaConstructionLevel.hasTranspensionUniversalModality :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => false
  | .structureClassCertificate => false
  | .threeCellsDecidable => false
  | .adjointStrings => false
  | .transpensionUniversalModality => true
  | .standaloneModeOmega => true

/-- The standalone mode ω-category capstone holds only at the top level.  Fully enumerated (no
specific-arm-then-wildcard) to stay propext-free. -/
def ModeOmegaConstructionLevel.hasStandaloneModeOmega :
    ModeOmegaConstructionLevel → Bool
  | .modeTheoryInterface => false
  | .strictTwoCategoryCore => false
  | .structureClassCertificate => false
  | .threeCellsDecidable => false
  | .adjointStrings => false
  | .transpensionUniversalModality => false
  | .standaloneModeOmega => true

/-- The honest current level of the FX mode ω-category: the mode-theory interface + the concrete
`fxModeTheory` (the strict dim-0/1 core), no 2-cells / structure-class certificate / adjoints / capstone
yet. -/
def fxModeOmegaConstructionLevel : ModeOmegaConstructionLevel :=
  .modeTheoryInterface

/-- BUILT: the FX mode ω-category has its mode-theory interface. -/
theorem fxModeOmega_hasModeTheoryInterface :
    fxModeOmegaConstructionLevel.hasModeTheoryInterface = true := rfl

/-- GAP → mode-1: the strict 2-category core round-trip is not yet formally landed. -/
theorem fxModeOmega_hasNoStrictTwoCategoryCore :
    fxModeOmegaConstructionLevel.hasStrictTwoCategoryCore = false := rfl

/-- GAP → mode-2: the per-mode structure-class certificate (DIM-CLASS for modes) is not yet wired. -/
theorem fxModeOmega_hasNoStructureClassCertificate :
    fxModeOmegaConstructionLevel.hasStructureClassCertificate = false := rfl

/-- GAP → mode-3: decidable 2-cell equality (the convergent 3-polygraph) is not yet built. -/
theorem fxModeOmega_hasNoThreeCellsDecidable :
    fxModeOmegaConstructionLevel.hasThreeCellsDecidable = false := rfl

/-- GAP → mode-4: the per-modality adjoint strings are not yet built. -/
theorem fxModeOmega_hasNoAdjointStrings :
    fxModeOmegaConstructionLevel.hasAdjointStrings = false := rfl

/-- GAP → mode-11: the transpension universal modality is not yet built. -/
theorem fxModeOmega_hasNoTranspensionUniversalModality :
    fxModeOmegaConstructionLevel.hasTranspensionUniversalModality = false := rfl

/-- GAP → mode-21: the standalone mode ω-category capstone is not yet assembled. -/
theorem fxModeOmega_hasNoStandaloneModeOmega :
    fxModeOmegaConstructionLevel.hasStandaloneModeOmega = false := rfl

/-! ## Reserved interface skeletons (the design-lock the mode-* track fills) -/

/-- **Structure-class labels** — the DIM-CLASS taxonomy of grade-algebra shapes a mode can carry
(§6.3).  Each PolyCell dimension's grade algebra is exactly one of these shapes; the shipped `Modal/`
certificates prove the laws.  `mode-2` attaches the right label to each mode. -/
inductive StructureClassLabel where
  /-- Ordered semiring (security flow — `unclassified < classified`). -/
  | orderedSemiring
  /-- Bounded join-semilattice (effect / trust). -/
  | boundedJoinSemilattice
  /-- Total-order chain (mutation — `immutable < … < read_write`). -/
  | totalOrderChain
  /-- The non-distributive diamond M3 (overflow — `{exact, wrap, trap, saturate}`). -/
  | diamondLatticeM3
  /-- Preorder, possibly non-antisymmetric (lifetime / region outlives). -/
  | preorder
  /-- Involution (session duality — `dual ∘ dual = id`). -/
  | involution
  /-- Category (version — labels with adapter edges). -/
  | category
  deriving DecidableEq, Repr

/-- **Structure-class certificate skeleton** (mode-2 #1558).  Attaches to each mode the DIM-CLASS shape
its grade algebra is — the multiplier certificate (Gratzer Fig 7/9).  Inhabiting this for the FX modes
wires the shipped `Modal/` lattice/semiring/order certificates into the mode ω-category. -/
structure StructureClassCertificate (base : ModeOmegaCategory) where
  /-- The structure-class shape of each mode's grade algebra. -/
  structureClassOf : base.modeTheory.Mode → StructureClassLabel

/-- **Adjoint-string skeleton** (mode-4 #1560).  Each modality `μ` sits in an adjoint string
`… ⊣ μ! ⊣ μ ⊣ μ* ⊣ …` — the per-modality left/right adjoints (sharp, transpension, cohesion).  `mode-4`
supplies the adjunction units/counits. -/
structure AdjointStringExtension (base : ModeOmegaCategory) where
  /-- The right-adjoint modality of each modality (the `♯`-direction). -/
  rightAdjointModality : {modeA modeB : base.modeTheory.Mode} →
    base.modeTheory.Modality modeA modeB → base.modeTheory.Modality modeB modeA

/-- **Transpension universal-modality skeleton** (mode-11 #1567).  The rightmost adjoint in the mode
adjoint string — the universal modality that recovers Gel/Glue/Weld/mill/√/Φ/Ψ/nominal across the four
axes.  `mode-11` supplies the universal property. -/
structure TranspensionModeModality (base : ModeOmegaCategory) where
  /-- The transpension modality's object-map on modes (the fresh-dimension extension). -/
  transpensionMode : base.modeTheory.Mode → base.modeTheory.Mode

end FX1Poly.Tier0.ModeOmega
