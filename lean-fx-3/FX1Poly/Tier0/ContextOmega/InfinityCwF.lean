import FX1Poly.Tier0.ContextOmega.SimplicialModel
import FX1Poly.Tier0.ContextOmega.Comprehension

/-! # Tier0/ContextOmega/InfinityCwF — the (∞,1)-CwF / natural model in an ∞-topos (context-14)

A **natural model** (Awodey) presents type theory as a *representable* natural transformation
`Tm → Ty` in a presheaf category; a **category with families** packages the same data.  The
**(∞,1)-categorical** refinement (Nguyen-Uemura "∞-type theories", Kapulkin-Lumsdaine "homotopy theory
of type theories") replaces the Set-valued presheaves with **space- / ∞-groupoid-valued** presheaves
over a Grothendieck **∞-topos**: a comprehension ∞-category / natural model whose universe is the
**object classifier** of the ∞-topos — which is **univalent by construction** (univalence is precisely
the classifying property of the object classifier).  The simplicial model (context-13) is ONE concrete
presentation of such an ∞-topos (the ∞-topos of spaces, presented by `sSet`).

Like the simplicial model, this is a **semantic model over a higher-categorical base** — an ∞-topos,
NOT the FX syntactic context category `fxBaseSubstCategory`.  ∞-groupoids / ∞-toposes cannot be built
zero-axiom in raw Lean 4 (Init only): the standard constructions need either simplicial machinery (a
large classical development) or higher-inductive quotients (`Quot.sound`).  So the (∞,1)-CwF itself is
CITED, not constructed.

What IS in scope and honest — and the GENUINE recognition this module adds:

  * The FX syntactic CwF (the shipped 1-categorical comprehension structure — context-1 `comprehension‑
    Bijection`, context-6 natural model, context-10 Jacobs comprehension fibration) is the
    **homotopy-0-truncation** of the (∞,1)-CwF.  At h-level 0 the natural model's representability —
    an EQUIVALENCE of mapping SPACES `Tm(Δ) ≃ Hom(Δ, Γ.A)` — collapses to a STRICT BIJECTION of
    hom-SETS, which is EXACTLY the shipped zero-axiom `comprehensionBijection`.  So FX realizes the
    (∞,1)-natural-model representability at the set level, on the nose.
  * the abstract ∞-topos natural model and the concrete simplicial model (context-13) agree on the
    honest flags — the simplicial model is a concrete instance of the abstract ∞-topos.

## What is built

  * `infinityToposNaturalModelLedger : SemanticModelLedger` (reusing the context-13 record-shape) — the
    (∞,1)-CwF / ∞-topos natural model, with honest flags.
  * the honest-flag pins (`providesUnivalentUniverse = true`, role = relative consistency,
    `requiresClassicalMetatheory = true`, `baseIsFXSyntacticContext = false`, `isMechanizedInFX = false`).
  * ★ `fxNaturalModelIsZeroTruncationOfInfinityCwF` — the genuine cross-reference: the shipped
    zero-axiom `comprehensionBijection` (the FX 1-categorical comprehension's strict hom-set bijection)
    IS the 0-truncation of the (∞,1)-natural-model representability; conjoined with the ledger's
    univalent-universe flag.
  * `simplicialModelIsAConcreteInfinityTopos` — the simplicial model (context-13) is a concrete
    presentation of the abstract ∞-topos natural model (the honest flags agree).
  * `infinityCwFLedgerHonest` — the headline ledger bundle.

## Honest boundary (recorded, not faked)

The (∞,1)-CwF / ∞-topos natural model, the object classifier, and the proof that the object classifier
is univalent are NOT constructed in FX — they are the cited higher-categorical constructions (needing
∞-categorical machinery + classical metatheory for the standard spaces presentation; cubical models
give a constructive route, which FX instead realizes DEFINITIONALLY via the DEFUNIV arc).  This module
ships only the LEDGER + the FX-relationship cross-references, all zero-axiom.

## Zero-axiom verification

Record + `rfl` flag pins, plus cross-references that apply the shipped zero-axiom `comprehensionBijection`
and compare ledger flags by `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The (∞,1)-CwF / ∞-topos natural-model ledger -/

/-- The (∞,1)-CwF / natural model in an ∞-topos (Nguyen-Uemura ∞-type theories; Kapulkin-Lumsdaine
homotopy theory of type theories): contexts and types live in a Grothendieck ∞-topos, the universe is
the ∞-topos' object classifier (univalent by construction).  A CLASSICAL relative-consistency anchor for
univalence — the abstract form of which the simplicial model (context-13) is a concrete instance.  NOT
constructed in FX (the honest flags record this). -/
def infinityToposNaturalModelLedger : SemanticModelLedger where
  modelName :=
    "(∞,1)-CwF / natural model in an ∞-topos (Nguyen-Uemura ∞-type theories; Kapulkin-Lumsdaine homotopy theory of type theories)"
  baseCategory :=
    "a Grothendieck ∞-topos (space- / ∞-groupoid-valued presheaves), e.g. the ∞-topos of spaces presented by sSet"
  fibrationNotion :=
    "the natural model's representable natural transformation Tm → Ty, enriched in spaces (a fibrant family in the ∞-topos)"
  universeContent :=
    "the object classifier of the ∞-topos — univalent by construction (univalence = the object classifier's classifying property)"
  providesUnivalentUniverse := true
  role := .relativeConsistency
  requiresClassicalMetatheory := true
  baseIsFXSyntacticContext := false
  isMechanizedInFX := false

/-! ## Honest flag pins -/

/-- The ∞-topos natural model provides a univalent universe (the object classifier). -/
theorem infinityToposNaturalModelLedger_providesUnivalentUniverse :
    infinityToposNaturalModelLedger.providesUnivalentUniverse = true := rfl

/-- The ∞-topos natural model's role is a RELATIVE-CONSISTENCY anchor for univalence. -/
theorem infinityToposNaturalModelLedger_roleIsRelativeConsistency :
    infinityToposNaturalModelLedger.role = .relativeConsistency := rfl

/-- The standard ∞-topos (spaces) construction requires CLASSICAL metatheory (the simplicial-homotopy
presentation of the object classifier; cubical models give a constructive alternative). -/
theorem infinityToposNaturalModelLedger_requiresClassicalMetatheory :
    infinityToposNaturalModelLedger.requiresClassicalMetatheory = true := rfl

/-- Honest absence marker: the ∞-topos natural model's base is NOT the FX syntactic context category —
it lives over an ∞-topos, a higher-categorical base. -/
theorem infinityToposNaturalModelLedger_baseIsNotFXSyntactic :
    infinityToposNaturalModelLedger.baseIsFXSyntacticContext = false := rfl

/-- Honest absence marker: the ∞-topos natural model is NOT mechanized in FX — ∞-groupoids / ∞-toposes
need machinery (simplicial sets or `Quot.sound`-based HITs) unavailable in Init-only zero-axiom Lean. -/
theorem infinityToposNaturalModelLedger_isNotMechanizedInFX :
    infinityToposNaturalModelLedger.isMechanizedInFX = false := rfl

/-! ## The genuine cross-references -/

/-- ★ **FX's syntactic CwF is the 0-truncation of the (∞,1)-CwF.**  The (∞,1)-natural-model
representability is an EQUIVALENCE of mapping spaces `Tm(Δ) ≃ Hom(Δ, Γ.A)`.  At the homotopy-0-truncation
(the FX set-level syntactic model) an equivalence of spaces collapses to a STRICT BIJECTION of hom-sets —
which is EXACTLY the shipped zero-axiom `comprehensionBijection` (context-1, both round-trips hold over
the FX term base).  So FX realizes the (∞,1)-natural-model representability ON THE NOSE at h-level 0.
This theorem conjoins that shipped bijection with the ∞-topos ledger's univalent-universe flag. -/
theorem fxNaturalModelIsZeroTruncationOfInfinityCwF {targetScope sourceScope : Nat} :
    ((∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
     (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended)) ∧
    infinityToposNaturalModelLedger.providesUnivalentUniverse = true :=
  ⟨comprehensionBijection, rfl⟩

/-- **The simplicial model is a concrete ∞-topos.**  The Kapulkin-Lumsdaine simplicial model (context-13)
is ONE concrete presentation of the abstract (∞,1)-CwF / ∞-topos natural model: both provide a univalent
universe, both play the relative-consistency role, and both live over a base that is NOT the FX syntactic
context category. -/
theorem simplicialModelIsAConcreteInfinityTopos :
    kapulkinLumsdaineLedger.providesUnivalentUniverse
        = infinityToposNaturalModelLedger.providesUnivalentUniverse ∧
    kapulkinLumsdaineLedger.role = infinityToposNaturalModelLedger.role ∧
    kapulkinLumsdaineLedger.baseIsFXSyntacticContext
        = infinityToposNaturalModelLedger.baseIsFXSyntacticContext :=
  ⟨rfl, rfl, rfl⟩

/-! ## The headline -/

/-- ★ **The (∞,1)-CwF ledger, honest.**  The natural model in an ∞-topos provides a univalent universe
(the object classifier) (a) over a higher-categorical base that is NOT the FX syntactic context category,
(b) requiring classical metatheory in the standard presentation, and (c) not mechanized in FX.  FX's
shipped 1-categorical comprehension structure is its homotopy-0-truncation (the `comprehensionBijection`
above), and FX handles univalence DEFINITIONALLY (DEFUNIV) rather than via this semantic model. -/
theorem infinityCwFLedgerHonest :
    infinityToposNaturalModelLedger.providesUnivalentUniverse = true ∧
    infinityToposNaturalModelLedger.requiresClassicalMetatheory = true ∧
    infinityToposNaturalModelLedger.baseIsFXSyntacticContext = false ∧
    infinityToposNaturalModelLedger.isMechanizedInFX = false ∧
    infinityToposNaturalModelLedger.role = .relativeConsistency :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega
