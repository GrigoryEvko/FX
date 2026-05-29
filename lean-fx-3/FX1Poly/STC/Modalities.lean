/-!
# STC Open/Closed Modalities (Sterling, Li-Yao-Harper arXiv:2509.11418)

Synthetic Tait Computability internalizes the gluing model as a MODAL
type theory with phase distinction. The open modality ○ isolates the
syntactic phase; the closed modality ● projects the semantic phase.

This file is only the current scaffold: phase token, open/closed
operations, strict-glue and extension records, and a toy Bool retraction
witness.  It does not build the FX logical relation and does not prove
canonicity or normalization.

Reference: arXiv:2509.11418 §3.
Zero external dependencies.
-/

namespace FX1Poly.STC

universe u

/-- Honesty ledger for Axis 12.  Later levels are strictly stronger than
earlier interface records. -/
inductive STCConstructionLevel where
  /-- Syntactic phase plus open/closed operations. -/
  | phaseAndModalInterfaces : STCConstructionLevel
  /-- Strict glue and extension record interfaces are present. -/
  | strictGlueAndExtensionTypes : STCConstructionLevel
  /-- STC model record is populated. -/
  | stcModelRecord : STCConstructionLevel
  /-- Toy Bool retraction witness is present. -/
  | toyBoolWitness : STCConstructionLevel
  /-- FX logical relation construction is present. -/
  | logicalRelationConstruction : STCConstructionLevel
  /-- FX canonicity theorem is present. -/
  | canonicityTheorem : STCConstructionLevel
  /-- FX normalization theorem is present. -/
  | normalizationTheorem : STCConstructionLevel
  /-- STC has replaced the generic FX reducibility route. -/
  | fxGenericSTCReplacement : STCConstructionLevel
  deriving DecidableEq, Repr

/-- Axis 12 has phase and modal interfaces at every level. -/
def STCConstructionLevel.hasPhaseAndModalInterfaces :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => true
  | .strictGlueAndExtensionTypes => true
  | .stcModelRecord => true
  | .toyBoolWitness => true
  | .logicalRelationConstruction => true
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has strict-glue and extension records from this level onward. -/
def STCConstructionLevel.hasStrictGlueAndExtensionTypes :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => true
  | .stcModelRecord => true
  | .toyBoolWitness => true
  | .logicalRelationConstruction => true
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has the STC model record from this level onward. -/
def STCConstructionLevel.hasSTCModelRecord :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => true
  | .toyBoolWitness => true
  | .logicalRelationConstruction => true
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has the toy Bool witness from this level onward. -/
def STCConstructionLevel.hasToyBoolWitness :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => false
  | .toyBoolWitness => true
  | .logicalRelationConstruction => true
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has an FX logical relation from this level onward. -/
def STCConstructionLevel.hasLogicalRelationConstruction :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => false
  | .toyBoolWitness => false
  | .logicalRelationConstruction => true
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has an FX canonicity theorem from this level onward. -/
def STCConstructionLevel.hasCanonicityTheorem :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => false
  | .toyBoolWitness => false
  | .logicalRelationConstruction => false
  | .canonicityTheorem => true
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has an FX normalization theorem from this level onward. -/
def STCConstructionLevel.hasNormalizationTheorem :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => false
  | .toyBoolWitness => false
  | .logicalRelationConstruction => false
  | .canonicityTheorem => false
  | .normalizationTheorem => true
  | .fxGenericSTCReplacement => true

/-- Axis 12 has replaced the generic FX reducibility route only at the
final ledger level. -/
def STCConstructionLevel.hasFXGenericSTCReplacement :
    STCConstructionLevel → Bool
  | .phaseAndModalInterfaces => false
  | .strictGlueAndExtensionTypes => false
  | .stcModelRecord => false
  | .toyBoolWitness => false
  | .logicalRelationConstruction => false
  | .canonicityTheorem => false
  | .normalizationTheorem => false
  | .fxGenericSTCReplacement => true

/-- Current Axis 12 status: record interfaces plus toy Bool retraction.
There is no FX logical relation or metatheorem here. -/
def fxSTCConstructionLevel : STCConstructionLevel :=
  .toyBoolWitness

theorem fxSTCConstructionLevel_eq :
    fxSTCConstructionLevel = STCConstructionLevel.toyBoolWitness := rfl

theorem fxSTC_hasPhaseAndModalInterfaces :
    fxSTCConstructionLevel.hasPhaseAndModalInterfaces = true := rfl

theorem fxSTC_hasStrictGlueAndExtensionTypes :
    fxSTCConstructionLevel.hasStrictGlueAndExtensionTypes = true := rfl

theorem fxSTC_hasSTCModelRecord :
    fxSTCConstructionLevel.hasSTCModelRecord = true := rfl

theorem fxSTC_hasToyBoolWitness :
    fxSTCConstructionLevel.hasToyBoolWitness = true := rfl

/-- Current Axis 12 has no FX logical relation construction. -/
theorem fxSTC_hasNoLogicalRelationConstruction :
    fxSTCConstructionLevel.hasLogicalRelationConstruction = false := rfl

/-- Current Axis 12 has no FX canonicity theorem. -/
theorem fxSTC_hasNoCanonicityTheorem :
    fxSTCConstructionLevel.hasCanonicityTheorem = false := rfl

/-- Current Axis 12 has no FX normalization theorem. -/
theorem fxSTC_hasNoNormalizationTheorem :
    fxSTCConstructionLevel.hasNormalizationTheorem = false := rfl

/-- Current Axis 12 has not replaced the generic FX reducibility route. -/
theorem fxSTC_hasNoFXGenericSTCReplacement :
    fxSTCConstructionLevel.hasFXGenericSTCReplacement = false := rfl

/-- The syntactic-phase token. Represents the single syntactic world used by
the current STC scaffold. -/
inductive SynPhase : Type where
  | syntactic
  deriving DecidableEq, Repr

/-- The open modality ○A: "A parameterized by the syntactic phase."
○A = SynPhase → A. In the open modality, values depend on the phase. -/
def OpenMod (carrier : Type u) : Type u := SynPhase → carrier

/-- Unit of the open modality: every value lives in ○ (constant family). -/
def OpenMod.unit {carrier : Type u} (value : carrier) : OpenMod carrier := fun _ => value

/-- The open modality is a monad: bind/join. -/
def OpenMod.join {carrier : Type u} (nested : OpenMod (OpenMod carrier)) : OpenMod carrier :=
  fun phase => nested phase phase

/-- Extract from the open modality given a phase witness. -/
def OpenMod.extract {carrier : Type u} (openValue : OpenMod carrier) (phase : SynPhase) : carrier :=
  openValue phase

/-- The closed operation ●A currently used by the scaffold.  It is a
computable one-constructor wrapper, not a quotient HIT. -/
inductive ClosedMod (carrier : Type u) : Type u where
  | mk : carrier → ClosedMod carrier

/-- Unit of the closed modality. -/
def ClosedMod.unit {carrier : Type u} (value : carrier) : ClosedMod carrier := .mk value

/-- Extract from the closed modality (forgets the closure). -/
def ClosedMod.extract {carrier : Type u} : ClosedMod carrier → carrier
  | .mk value => value

/-- Unit-shaped map for the future open/closed adjunction. -/
def openClosedUnit {carrier : Type u} (value : carrier) : ClosedMod (OpenMod carrier) :=
  .mk (OpenMod.unit value)

/-- Counit-shaped map for the current one-phase scaffold. -/
def openClosedCounit {carrier : Type u} (openClosed : OpenMod (ClosedMod carrier)) : carrier :=
  (openClosed .syntactic).extract

/-- Idempotence of ○: ○(○A) ≃ ○A (the open modality is idempotent). -/
def OpenMod.idempotent {carrier : Type u} : OpenMod (OpenMod carrier) → OpenMod carrier :=
  OpenMod.join

/-- Idempotence of ●: ●(●A) ≃ ●A (the closed modality is idempotent). -/
def ClosedMod.idempotent {carrier : Type u} : ClosedMod (ClosedMod carrier) → ClosedMod carrier
  | .mk (.mk value) => .mk value

/-- A strict glue record: pairs a syntactic witness with semantic data.
The logical-relation construction that would use this record is not present
in this file. -/
structure StrictGlue (synType : Type u) (semProp : synType → Type u) where
  syntactic : synType
  semantic : semProp syntactic

/-- An extension type: a subtype that restricts to a given value under
the syntactic phase. { a : A | ∀ phase, a = prescribed phase } -/
structure ExtensionType (carrier : Type u) (prescribed : SynPhase → carrier) where
  value : carrier
  restricts : ∀ (phase : SynPhase), value = prescribed phase

/-- The STC model bundles the current operations and idempotent maps. -/
structure STCModel where
  /-- The syntactic phase type (abstract). -/
  Phase : Type
  /-- Open modality parameterized by phase. -/
  Open : Type u → Type u
  /-- Closed modality collapsing phase. -/
  Closed : Type u → Type u
  /-- Glue: syntactic + semantic paired. -/
  Glue : (synType : Type u) → (synType → Type u) → Type u
  /-- Open is idempotent. -/
  openIdempotent : {carrier : Type u} → Open (Open carrier) → Open carrier
  /-- Closed is idempotent. -/
  closedIdempotent : {carrier : Type u} → Closed (Closed carrier) → Closed carrier

/-- The canonical STC model using our definitions. -/
def canonicalSTCModel : STCModel.{u} where
  Phase := SynPhase
  Open := OpenMod
  Closed := ClosedMod
  Glue := StrictGlue
  openIdempotent := OpenMod.idempotent
  closedIdempotent := ClosedMod.idempotent

/-- Retraction-shaped data for a base type and its chosen canonical forms.
This is not a theorem about closed FX terms. -/
structure CanonicityWitness (baseType : Type u) where
  CanonicalForm : Type u
  embed : CanonicalForm → baseType
  extract : baseType → CanonicalForm
  roundtrip : ∀ (canonical : CanonicalForm), extract (embed canonical) = canonical

/-- Toy Bool retraction witness.  This does not prove FX Bool canonicity. -/
def boolCanonicityWitness : CanonicityWitness Bool where
  CanonicalForm := Bool
  embed := id
  extract := id
  roundtrip := fun _ => rfl

end FX1Poly.STC
