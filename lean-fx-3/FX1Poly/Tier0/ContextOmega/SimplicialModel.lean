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

The simplicial model itself is NOT constructed in FX — it is the classical Voevodsky/KL model, CITED here
as documentary data (`kapulkinLumsdaineLedger`), with its FX-mechanization honestly marked absent
(`isMechanizedInFX = false`).  The one machine-checked content is the cross-reference
`fxConsistencyIsConstructiveNotModelDependent`: FX's own consistency is CONSTRUCTIVE (the shipped
`consistencyViaRelativeInduction`), so FX does NOT depend on the simplicial model for its consistency — the
simplicial model is an external CLASSICAL relative-consistency anchor for the univalence EXTENSION, which FX
itself handles DEFINITIONALLY (the DEFUNIV arc).  The `SemanticModelLedger` / `SemanticModelRole` record
shapes are the reusable documentary scaffolding for the model tasks (context-13/14/22..26).

Raw Lean 4 + Init only; the cross-reference applies the shipped `consistencyViaRelativeInduction`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0

/-! ## The reusable semantic-model documentary record -/

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
the model provides from whether FX mechanizes it.  Documentary data reused across the model tasks
(context-13/14/22..26). -/
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

/-! ## The genuine cross-reference: FX's constructive consistency vs the model's classical role -/

/-- ★ **FX's consistency is constructive, not model-dependent.**  FX's empty-type consistency is proven
CONSTRUCTIVELY by the shipped `consistencyViaRelativeInduction` (the empty data scone refuses a canonicity
extraction — SN-050 over the context base, zero-axiom), so FX does NOT depend on the Kapulkin-Lumsdaine
simplicial model for its consistency.  The simplicial model (`kapulkinLumsdaineLedger`) is an ADDITIONAL
CLASSICAL relative-consistency anchor — for the univalence EXTENSION specifically — which FX itself handles
DEFINITIONALLY (the DEFUNIV arc).  Delegates to the shipped constructive consistency. -/
theorem fxConsistencyIsConstructiveNotModelDependent :
    SconeCanonicityExtraction emptyValueScone → False :=
  consistencyViaRelativeInduction

end FX1Poly.Tier0.ContextOmega
