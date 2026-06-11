import FX1Poly.STC.Modalities
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
/-! # FX1Poly/STC/FxLogicalRelation — the FX STC logical relation (closed fragment)

The Axis 12 ledger gap closed: this module builds the FX logical
relation IN the shipped STC vocabulary — the gluing of FX syntax with
computability evidence through `canonicalSTCModel.Glue` — together
with its fundamental theorem, the first non-toy `ExtensionType`
inhabitant, and the BRIDGED-to-Tait identification pins.

## Orientation: the shipped primitives vs Li-Yao-Harper (arXiv:2509.11418 §3)

* `OpenMod` (○A = SynPhase → A) is the paper's open modality as a
  phase-indexed family; with the current SINGLE phase it is the
  identity up to the constant family — honest divergence: the paper's
  phase is a proposition in a topos, ours is a one-element token.
* `ClosedMod` is a one-constructor wrapper, NOT the paper's pushout
  (HIT) closed modality — the HIT would pull `Quot.sound`, which the
  zero-axiom discipline forbids.  Everything in this module uses only
  `Glue`/`ExtensionType`/○, never a ●-quotient property.
* `StrictGlue` is the paper's gluing pair (syntactic component +
  semantic component over it); `ExtensionType` is the
  {a | a restricts to the prescription under the phase} subtype.

## What the relation IS — and the bridge

`fxStcRelationAt profile classifier` glues a CLOSED grown-typed FX
term with its computability evidence, where the semantic side is the
kernel's Tait-derived strong normalization.  This is BRIDGED, not
independent: synthetic Tait computability is Tait computability — the
semantic component is definitionally the Tait pipeline's SN witness
(`fxStcRelation_semProp_eq`, the same identification discipline as
`sconingScone_computable_eq_candidate` on the sconing leg).  The
parity ledger's sconing/STC cells therefore stay BRIDGED; what this
module adds is the CONSTRUCTION the `logicalRelationConstruction`
ledger level names: the glue family, the fundamental theorem, and the
extension-type wiring, all in the STC model's own vocabulary.

A genuinely INDEPENDENT second semantics through this interface would
need the HIT closed modality (Quot.sound) or a non-Tait `computable`
— the SN-102 question, NOT claimed here.

## Honest scope

The relation is the CLOSED fragment (scope-0 subjects over the empty
context) — exactly what the canonicity consumer (SN-100) quantifies
over.  An open-context Kripke-STC relation is future work.

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean` (the
`FX1Poly.STC` namespace sweep + per-decl headline gates). -/

namespace FX1Poly.STC

open FX1Poly.Core FX1Poly.Typed

/-- A closed FX term certified by the grown engine at a classifier —
the SYNTACTIC component of the FX STC relation. -/
structure ClosedTypedTerm (profile : PolyProfile) (classifier : RawTerm 0) where
  /-- The closed subject. -/
  term : RawTerm 0
  /-- Its grown-engine typing at the classifier, over the empty context. -/
  typed : HasTypeDescPi profile TypingContext.empty term classifier

/-- ★ **The FX STC logical relation** at a closed classifier: the
canonical STC model's `Glue` of the closed typed syntax with the
computability evidence (strong normalization, `PLift`ed from `Prop`
into the model's `Type` vocabulary). -/
def fxStcRelationAt (profile : PolyProfile) (classifier : RawTerm 0) : Type :=
  canonicalSTCModel.Glue (ClosedTypedTerm profile classifier)
    (fun typedTerm => PLift (StepStar.IsStronglyNormalizing typedTerm.term))

/-- ★★ **The STC fundamental theorem, closed fragment**: every closed
grown-typed FX term GLUES — its syntax pairs with its computability
witness.  The semantic component is the kernel's closed SN
(`stronglyNormalizingOfWfContextDesc` at the trivially well-formed
empty context) — the Tait pipeline, which is the BRIDGE. -/
def fxStcFundamental {profile : PolyProfile} {term classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty term classifier) :
    fxStcRelationAt profile classifier :=
  ⟨⟨term, typed⟩,
    ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc
      WfContextDesc.emptyIsWellFormed typed⟩⟩

/-! ## The BRIDGED identification pins (the sconing-leg discipline) -/

/-- The relation's glue former IS the canonical model's glue former
(the relation lives in the model's own vocabulary, by definition). -/
theorem fxStcRelationAt_isModelGlue (profile : PolyProfile)
    (classifier : RawTerm 0) :
    fxStcRelationAt profile classifier
      = canonicalSTCModel.Glue (ClosedTypedTerm profile classifier)
          (fun typedTerm =>
            PLift (StepStar.IsStronglyNormalizing typedTerm.term)) := rfl

/-- The fundamental theorem's semantic component IS the Tait
pipeline's named closed-SN witness — the Tait-bridge pin, mirroring
`sconingSN_eq_taitComposition` on the sconing leg: the "synthetic"
computability the relation displays is the kernel's Tait
computability, not a second semantics.  Genuine independence would
need a different semantic side, which the non-HIT scaffold cannot
supply (see the module docstring). -/
theorem fxStcFundamental_semantic_isTaitWitness {profile : PolyProfile}
    {term classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty term classifier) :
    (fxStcFundamental typed).semantic
      = ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc
          WfContextDesc.emptyIsWellFormed typed⟩ := rfl

/-! ## The first non-toy ExtensionType inhabitant

The glued term's syntactic component restricts to its prescribed
value under EVERY phase — the extension-type discipline, inhabited by
the glue itself (trivially under the single phase, but the genuine
interface wiring: the syntactic phase determines the syntax). -/

/-- The glued subject under the open modality: the constant
phase-family at its syntax. -/
def fxStcSyntacticOpen {profile : PolyProfile} {classifier : RawTerm 0}
    (gluedTerm : fxStcRelationAt profile classifier) :
    OpenMod (RawTerm 0) :=
  OpenMod.unit gluedTerm.syntactic.term

/-- ★ The glued subject inhabits the extension type over its own
syntactic prescription: under the syntactic phase, the glue
RESTRICTS to its syntax. -/
def fxStcExtension {profile : PolyProfile} {classifier : RawTerm 0}
    (gluedTerm : fxStcRelationAt profile classifier) :
    ExtensionType (RawTerm 0) (fxStcSyntacticOpen gluedTerm) :=
  ⟨gluedTerm.syntactic.term, fun _ => rfl⟩

/-- Round-trip: the fundamental theorem's glue carries exactly the
input term and typing (no laundering through the relation). -/
theorem fxStcFundamental_syntactic_eq {profile : PolyProfile}
    {term classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty term classifier) :
    (fxStcFundamental typed).syntactic.term = term := rfl

end FX1Poly.STC
