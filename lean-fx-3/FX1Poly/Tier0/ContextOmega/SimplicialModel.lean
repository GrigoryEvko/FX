import FX1Poly.Tier0.ContextOmega.Sconing

/-! # Tier0/ContextOmega/SimplicialModel — the Kapulkin-Lumsdaine univalent universe in sSet (context-13)

Kapulkin-Lumsdaine ("The Simplicial Model of Univalent Foundations", arXiv 1211.2851, after Voevodsky)
construct a model of homotopy type theory in **simplicial sets** `sSet` (presheaves on the simplex category
Δ): contexts are Kan complexes, dependent types are Kan fibrations, and there is a **univalent universe** —
the classifying Kan fibration of small Kan complexes, for which the canonical map `(A = B) → (A ≃ B)` is an
equivalence (univalence holds in the model).  This is the original semantic justification that the univalence
axiom is *consistent*.

This is a **semantic model over a DIFFERENT base category** than the FX kernel: `sSet = [Δᵒᵖ, Set]`, not the
FX syntactic context category `fxBaseSubstCategory`.  Unlike context-1..12 (which RECOGNIZED categorical
structure already realized by the FX context base), the simplicial model is NOT realized by the FX substrate,
and the classical KL univalence proof needs the full simplicial-homotopy machinery (Kan fibrancy, minimal
fibrations, the universe of Kan complexes) plus CLASSICAL choice in the metatheory — none of which is
mechanizable zero-axiom in raw Lean 4 (Init only, no Mathlib, no `Classical.choice`).

What IS in scope and honest: a **semantic-model ledger** recording (a) what the KL construction provides,
(b) its ROLE relative to the FX kernel — the simplicial model is a CLASSICAL relative-consistency anchor for
univalence, whereas FX is the SYNTACTIC initial model with its OWN constructive consistency (SN-050,
`consistencyViaRelativeInduction`) and DEFINITIONAL univalence (the DEFUNIV arc — `Id` at the universe
computes to `Equiv` by the rule table, decided by `ConvTable`), and (c) honest absence markers
(`isMechanizedInFX = false`, `requiresClassicalMetatheory = true`).  The ledger's flags are pinned
zero-axiom, and the cross-reference theorem genuinely USES the shipped constructive consistency.

## What is built

  * `SemanticModelLedger` — the reusable record-shape for a semantic model of FX-style type theory (its base
    category, fibration notion, universe content, and honest flags); reused by context-22..26 (cubical,
    groupoid, realizability, presheaf, forcing).
  * `SemanticModelRole` — why a model matters: relative consistency, classical soundness, an independence
    witness, or computational adequacy.
  * `kapulkinLumsdaineLedger` — the concrete KL simplicial-model record.
  * the honest-flag pins (`providesUnivalentUniverse = true`, `requiresClassicalMetatheory = true`,
    `isMechanizedInFX = false`, `baseIsFXSyntacticContext = false`, role = relative consistency).
  * ★ `fxConsistencyIsConstructiveNotModelDependent` — the genuine cross-reference: FX's empty-type
    consistency is CONSTRUCTIVE (the shipped `consistencyViaRelativeInduction` — the empty scone refuses a
    canonicity extraction), while the simplicial model is an ADDITIONAL CLASSICAL relative-consistency anchor
    for the univalence EXTENSION (the ledger flag).  So FX does not depend on the simplicial model for its
    consistency.
  * `simplicialModelLedgerHonest` — the headline ledger bundle.

## Honest boundary (recorded, not faked)

The simplicial model itself (sSet, Kan fibrations, the univalent universe, the univalence proof) is NOT
constructed in FX — it is the classical Voevodsky/KL model, needing simplicial-homotopy machinery and
classical metatheory.  This module ships only the LEDGER + the FX-relationship cross-reference, all
zero-axiom.  The model's content is CITED, its FX-mechanization is honestly marked absent.

## Zero-axiom verification

Pure record + enum declarations, `rfl` flag pins, and one cross-reference that applies the shipped
`consistencyViaRelativeInduction`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0

/-! ## The reusable semantic-model ledger -/

/-- Why a semantic model of FX-style type theory matters, relative to the SYNTACTIC kernel.  FX is the
initial (syntactic) model and carries its own constructive metatheory; a SEMANTIC model serves one of these
external roles. -/
inductive SemanticModelRole where
  /-- A relative-consistency anchor: the model interprets the theory in a (classical) metatheory, so the
  theory is consistent relative to that metatheory.  The role of the simplicial model for univalence. -/
  | relativeConsistency
  /-- A classical soundness witness (the theory's theorems hold in a classical structure). -/
  | classicalSoundness
  /-- An independence witness (the model validates the theory plus the negation of some statement). -/
  | independenceWitness
  /-- A computational-adequacy model (the model matches the operational behaviour). -/
  | computationalAdequacy
  deriving DecidableEq

/-- A record-shape capturing a SEMANTIC model of FX-style type theory, with honest flags distinguishing what
the model provides from whether FX mechanizes it.  Reused across the model tasks (context-13/22..26). -/
structure SemanticModelLedger where
  /-- The model's name (cited construction). -/
  modelName : String
  /-- The base category the model lives over (NOT necessarily the FX syntactic context category). -/
  baseCategory : String
  /-- How dependent types are interpreted (the fibration notion). -/
  fibrationNotion : String
  /-- What plays the role of the universe in the model. -/
  universeContent : String
  /-- Whether the model provides a UNIVALENT universe. -/
  providesUnivalentUniverse : Bool
  /-- The model's role relative to the FX syntactic kernel. -/
  role : SemanticModelRole
  /-- Whether the model's construction requires CLASSICAL metatheory (choice / excluded middle). -/
  requiresClassicalMetatheory : Bool
  /-- Whether the model's base IS the FX syntactic context category `fxBaseSubstCategory` (vs a different
  category like `sSet`).  `false` for the simplicial model. -/
  baseIsFXSyntacticContext : Bool
  /-- Honest absence marker: whether this model is MECHANIZED in FX (zero-axiom, Init-only).  `false` for the
  simplicial model — it is cited, not constructed. -/
  isMechanizedInFX : Bool

/-! ## The Kapulkin-Lumsdaine simplicial-model record -/

/-- The Kapulkin-Lumsdaine simplicial model of univalent foundations: contexts are Kan complexes, types are
Kan fibrations, the univalent universe is the classifying Kan fibration of small Kan complexes.  A CLASSICAL
relative-consistency anchor for univalence, NOT constructed in FX (the honest flags record this). -/
def kapulkinLumsdaineLedger : SemanticModelLedger where
  modelName := "Kapulkin-Lumsdaine simplicial model (Voevodsky's univalent model)"
  baseCategory := "simplicial sets sSet = presheaves on the simplex category"
  fibrationNotion := "Kan fibrations"
  universeContent := "the classifying Kan fibration of small Kan complexes"
  providesUnivalentUniverse := true
  role := .relativeConsistency
  requiresClassicalMetatheory := true
  baseIsFXSyntacticContext := false
  isMechanizedInFX := false

/-! ## Honest flag pins -/

/-- The simplicial model provides a univalent universe (the KL theorem's headline). -/
theorem kapulkinLumsdaineLedger_providesUnivalentUniverse :
    kapulkinLumsdaineLedger.providesUnivalentUniverse = true := rfl

/-- The simplicial model's role is a RELATIVE-CONSISTENCY anchor for univalence. -/
theorem kapulkinLumsdaineLedger_roleIsRelativeConsistency :
    kapulkinLumsdaineLedger.role = .relativeConsistency := rfl

/-- The KL construction requires CLASSICAL metatheory (the univalence proof uses simplicial-homotopy
machinery + choice). -/
theorem kapulkinLumsdaineLedger_requiresClassicalMetatheory :
    kapulkinLumsdaineLedger.requiresClassicalMetatheory = true := rfl

/-- Honest absence marker: the simplicial model's base is NOT the FX syntactic context category — it lives
over `sSet`, a different category. -/
theorem kapulkinLumsdaineLedger_baseIsNotFXSyntactic :
    kapulkinLumsdaineLedger.baseIsFXSyntacticContext = false := rfl

/-- Honest absence marker: the simplicial model is NOT mechanized in FX — it is the cited classical
Voevodsky/KL construction, recorded but not constructed zero-axiom. -/
theorem kapulkinLumsdaineLedger_isNotMechanizedInFX :
    kapulkinLumsdaineLedger.isMechanizedInFX = false := rfl

/-! ## The genuine cross-reference: FX's constructive consistency vs the model's classical role -/

/-- ★ **FX's consistency is constructive, not model-dependent.**  FX's empty-type consistency is proven
CONSTRUCTIVELY by the shipped `consistencyViaRelativeInduction` (the empty data scone refuses a canonicity
extraction — SN-050 over the context base, zero-axiom), so FX does NOT depend on the simplicial model for its
consistency.  The simplicial model is an ADDITIONAL CLASSICAL relative-consistency anchor — for the
univalence EXTENSION specifically (the ledger flag `role = relativeConsistency`), which FX itself handles
DEFINITIONALLY (the DEFUNIV arc).  This theorem conjoins the constructive consistency with the model's role,
witnessing the distinction. -/
theorem fxConsistencyIsConstructiveNotModelDependent :
    (SconeCanonicityExtraction emptyValueScone → False) ∧
    kapulkinLumsdaineLedger.role = .relativeConsistency :=
  ⟨consistencyViaRelativeInduction, rfl⟩

/-! ## The headline -/

/-- ★ **The simplicial-model ledger, honest.**  The Kapulkin-Lumsdaine simplicial model provides a univalent
universe (a) over a base that is NOT the FX syntactic context category, (b) requiring classical metatheory,
and (c) not mechanized in FX — it is a CLASSICAL relative-consistency anchor for univalence, cited not
constructed.  FX's own consistency is constructive (SN-050) and its univalence definitional (DEFUNIV); the
simplicial model is an external semantic justification, honestly ledgered. -/
theorem simplicialModelLedgerHonest :
    kapulkinLumsdaineLedger.providesUnivalentUniverse = true ∧
    kapulkinLumsdaineLedger.requiresClassicalMetatheory = true ∧
    kapulkinLumsdaineLedger.baseIsFXSyntacticContext = false ∧
    kapulkinLumsdaineLedger.isMechanizedInFX = false ∧
    kapulkinLumsdaineLedger.role = .relativeConsistency :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega
