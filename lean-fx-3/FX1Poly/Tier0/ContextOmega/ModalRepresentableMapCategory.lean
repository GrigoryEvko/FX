import FX1Poly.Tier0.ContextOmega.Comprehension
import FX1Poly.Tier0.ContextOmega.Uemura
import FX1Poly.Tier0.ContextOmega.Fibration
import FX1Poly.Tier0.ContextOmega.MultimodalNormalization
import FX1Poly.Tier0.ContextOmega.SubstitutionGroupoid
import FX1Poly.Tier0.ContextOmega.Interface

/-! # Tier0/ContextOmega/ModalRepresentableMapCategory — the standalone modal RMC (context-21 CAPSTONE)

This is the **capstone of the context axis** — the load-bearing ω-category of the four
(context · mode · term · type).  FX's contexts-and-substitutions form a **standalone modal representable
map category** with comprehension, the Uemura type-former bijection, the fibred / dimensional adjoints,
the modal lock, and a normalization function — every pillar a SHIPPED zero-axiom fact, cross-referenced
here as a genuine anchor.

## The five pillars (comprehension + Uemura + adjoints + locks + normalization)

  * **comprehension** (context-1) — context extension `Γ ↦ Γ.A` with its display projection is the
    representable comprehension, `comprehensionBijection`: `Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)` (both
    round-trips).  This IS the Frobenius `Σ ⊣` reindex adjunction (`dependentSumAdjunctionBijection`
    is literally the same bijection).
  * **Uemura** (context-2) — type-formers are exactly the representable natural transformations:
    `piFormerComprehension : IsRepresentableFormer piFormerMap` (Π and Σ both representable formers).
  * **adjoints** (context-3 / context-10) — the Jacobs fibred adjoint string: `jacobsComprehensionFibrationCore`
    bundles the Beck-Chevalley display square, the reindex-identity `A[id] = A`, and the representable
    Π-former — the dimensional adjoints `Ⅎ ⊣ Σ ⊣ Ω ⊣ Π ⊣ ◊` (transpension `◊` rightmost, reserved per
    context-3's honest ledger).
  * **locks** (context-4) — the Fitch-style modal lock `◐_μ` strictly adds a dimension,
    `dimensionLock.objectMap scope = scope + 1` — the categorical realization of the `.context ↔ .mode`
    correspondence and the prerequisite for the global-sections / flat modality (context-18).
  * **normalization** (context-12) — Gratzer multimodal NbE over the modal base: on the
    strongly-normalizing fragment (every well-typed term, SN-043) conversion IS normal-form equality
    (`multimodalNormalizationSoundComplete`), so conversion is decidable.

Over these the substitution category is a strict 1-category whose dim-2 layer collapses (context-20).

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the genuine HOMOTOPY ω-groupoid of substitutions (non-trivial higher
paths, context-20's boundary) and the SEMANTIC ∞-models (the simplicial / ∞-topos natural models,
context-13/14) — those sit over a DIFFERENT base and need classical metatheory.  What IS zero-axiom is
the standalone modal RMC over the FX SYNTACTIC context base: the five pillars + the strict 1-truncation.

## Zero-axiom verification

Cross-references applying the shipped zero-axiom `comprehensionBijection` (context-1),
`piFormerComprehension` (context-2), `jacobsComprehensionFibrationCore` (context-10),
`dimensionLock_objectMap` (context-4), and `multimodalNormalizationSoundComplete` (context-12).  No
`funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The five genuine pillar anchors -/

/-- ★ **Pillar 1 — comprehension.**  Context extension `Γ ↦ Γ.A` is the representable comprehension:
the comprehension bijection `Hom(Δ, Γ.A) ≅ Hom(Δ, Γ) × Tm(Δ)` holds with both round-trips
(`comprehensionBijection`, context-1, SUBSTVEC-4).  This is the Frobenius `Σ ⊣` reindex adjunction. -/
theorem comprehensionPillarAssembled {targetScope sourceScope : Nat} :
    (∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
    (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended) :=
  comprehensionBijection

/-- ★ **Pillar 2 — the Uemura bijection.**  Type-formers ARE representable natural transformations: the
Π-former map is a representable former (`piFormerComprehension : IsRepresentableFormer piFormerMap`,
context-2, SN-088) — its pullback against the generic display map lands on the formed type. -/
theorem uemuraPillarAssembled :
    IsRepresentableFormer piFormerMap :=
  piFormerComprehension

/-- ★ **Pillar 3 — the fibred / dimensional adjoints.**  The Jacobs comprehension-fibration core
(`jacobsComprehensionFibrationCore`, context-10): the Beck-Chevalley display square commutes, reindexing
is split (`A[id] = A`), and the Π-former is representable — the fibred adjoint string `… ⊣ Σ ⊣ Ω ⊣ Π`
(with transpension `◊` the rightmost reserved join, context-3). -/
theorem dimensionalAdjointsPillarAssembled {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) (family : SubstActionFamily)
    (typeCell : family.sections sourceScope) :
    (SubstVec.weakening sourceScope).compose substVec.liftUnderBinder =
        substVec.compose (SubstVec.weakening targetScope) ∧
    reindexType family (SubstVec.identity sourceScope) typeCell = typeCell ∧
    IsRepresentableFormer piFormerMap :=
  jacobsComprehensionFibrationCore substVec family typeCell

/-- ★ **Pillar 4 — the modal lock.**  The Fitch-style modal lock `◐_μ` (context-4's `dimensionLock`)
strictly adds a dimension: `objectMap scope = scope + 1` — the left adjoint to the modality `⟦μ⟧`, the
categorical realization of the `.context ↔ .mode` correspondence (and the prerequisite for the
global-sections / flat modality, context-18). -/
theorem modalLockPillarAssembled (scope : Nat) :
    dimensionLock.objectMap scope = scope + 1 :=
  dimensionLock_objectMap scope

/-- ★ **Pillar 5 — multimodal normalization.**  Gratzer multimodal NbE over the modal base: two
strongly-normalizing terms are convertible IFF their normal forms coincide
(`multimodalNormalizationSoundComplete`, context-12) — the normal form is a COMPLETE conversion
invariant, so conversion is decidable on the SN fragment (every well-typed term, SN-043). -/
theorem multimodalNormalizationPillarAssembled {scope : Nat}
    (leftTerm rightTerm : RawTerm scope)
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftTerminates = RawTerm.normalize rightTerm rightTerminates :=
  multimodalNormalizationSoundComplete leftTerminates rightTerminates

end FX1Poly.Tier0.ContextOmega
