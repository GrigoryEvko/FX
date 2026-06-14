import FX1Poly.Tier0.ModeOmega.ModeTheory

/-! # Tier0/ModeOmega — the mode axis as a standalone ω-category (mode-0)

This module locks the **mode** PolyCell axis as its own Tier-0 object — the SECOND load-bearing
ω-category of the four (context · mode · term · type), the one the kernel is *fibered over* (every
binding's grade vector lives in a product of mode-indexed structure-class algebras).  It is the
DESIGN-LOCK of the `mode-*` track: the interface every later mode brick extends.

## Why this namespace exists (the reorganization)

The shipped mode substrate is real but was scattered — the mode 2-category lived under
`MTTNorm/ModeTheory.lean` (Gratzer's mode-theory interface + the concrete `fxModeTheory`), and the
per-dimension structure-class certificates (effect/trust/security/mutation/overflow/lifetime/session/
version — bounded-join-semilattices, ordered semirings, total-order chains, the M3 diamond, preorders,
involutions, categories) live under `Modal/`.  `Tier0/ModeOmega/` is the four-axis-aligned home: the mode
theory is now NATIVE here (`Tier0/ModeOmega/ModeTheory.lean` — Gratzer's interface + `fxModeTheory`), so
the sealed mode axis no longer imports the higher `MTTNorm` layer; `MTTNorm/ModeTheory.lean` re-exports
it.  This module carries the mode slice of the design lock over the native substrate.

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
wiring, the adjoint strings, and the transpension universal modality are RESERVED — the design-lock
exposes them as the interface skeletons the `mode-*` track fills.

Zero external dependencies; raw Lean 4 + Init only.  All declarations are structures, total functions,
and constructor witnesses — no `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModeOmega.lean`. -/

namespace FX1Poly.Tier0.ModeOmega

/-- **The mode ω-category at Tier 0.**  A standalone axis object packaging the mode theory — the strict
2-category whose 0-cells are modes, 1-cells are modalities, and 2-cells are modality coherences.  The
per-mode structure-class certificate, the adjoint strings, and the transpension universal modality are
layered on top as the `StructureClassCertificate` / `AdjointStringExtension` / `TranspensionModeModality`
extensions (filled by `mode-2`/`mode-4`/`mode-11`). -/
structure ModeOmegaCategory where
  /-- Dim 0+1: the mode theory (Gratzer's finitary 2-category — modes, modalities, category laws). -/
  modeTheory : ModeTheory

/-- **The FX mode ω-category.**  Bridges to the native `fxModeTheory` (the free finite-path category over
the accepted FX mode shifts — the category laws hold by construction, see `Tier0/ModeOmega/ModeTheory.lean`).
No new substrate is built here; this is the four-axis-aligned re-presentation of the native mode theory. -/
def fxModeOmega : ModeOmegaCategory where
  modeTheory := fxModeTheory

/-- The FX mode ω-category's mode theory is exactly the native `fxModeTheory` — so the strict category
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

/-- **Structure-class certificate skeleton** (mode-2).  Attaches to each mode the DIM-CLASS shape
its grade algebra is — the multiplier certificate (Gratzer Fig 7/9).  Inhabiting this for the FX modes
wires the shipped `Modal/` lattice/semiring/order certificates into the mode ω-category. -/
structure StructureClassCertificate (base : ModeOmegaCategory) where
  /-- The structure-class shape of each mode's grade algebra. -/
  structureClassOf : base.modeTheory.Mode → StructureClassLabel

/-- **Adjoint-string skeleton** (mode-4).  Each modality `μ` sits in an adjoint string
`… ⊣ μ! ⊣ μ ⊣ μ* ⊣ …` — the per-modality left/right adjoints (sharp, transpension, cohesion).  `mode-4`
supplies the adjunction units/counits. -/
structure AdjointStringExtension (base : ModeOmegaCategory) where
  /-- The right-adjoint modality of each modality (the `♯`-direction). -/
  rightAdjointModality : {modeA modeB : base.modeTheory.Mode} →
    base.modeTheory.Modality modeA modeB → base.modeTheory.Modality modeB modeA

/-- **Transpension universal-modality skeleton** (mode-11).  The rightmost adjoint in the mode
adjoint string — the universal modality that recovers Gel/Glue/Weld/mill/√/Φ/Ψ/nominal across the four
axes.  `mode-11` supplies the universal property. -/
structure TranspensionModeModality (base : ModeOmegaCategory) where
  /-- The transpension modality's object-map on modes (the fresh-dimension extension). -/
  transpensionMode : base.modeTheory.Mode → base.modeTheory.Mode

end FX1Poly.Tier0.ModeOmega
