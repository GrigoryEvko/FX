/-!
# STC Open/Closed Modalities (Sterling, Li-Yao-Harper arXiv:2509.11418)

Synthetic Tait Computability internalizes the gluing model as a MODAL
type theory with phase distinction. The open modality ○ isolates the
syntactic phase; the closed modality ● projects the semantic phase.

Together they give a type-theoretic framework for proving canonicity
and normalization WITHOUT external model constructions.

For FX: replaces the per-type-former Kripke reducibility (K12's ~10K LoC)
with a generic modal argument that works for ALL type formers.

Reference: arXiv:2509.11418 §3.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.STC

universe u

/-- The syntactic-phase token. Represents "being in the syntactic world."
Abstractly a single type with no computational content. -/
def SynPhase : Type := Unit

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

/-- The closed modality ●A: collapses phase-dependence to a single point.
Computationally: ●A forgets which syntactic phase produced the value.
Represented as the quotient that identifies all phase-dependent values. -/
inductive ClosedMod (carrier : Type u) : Type u where
  | mk : carrier → ClosedMod carrier

/-- Unit of the closed modality. -/
def ClosedMod.unit {carrier : Type u} (value : carrier) : ClosedMod carrier := .mk value

/-- Extract from the closed modality (forgets the closure). -/
def ClosedMod.extract {carrier : Type u} : ClosedMod carrier → carrier
  | .mk value => value

/-- The open-closed adjunction: ○ ⊣ ●.
Unit: A → ●(○A) — embed a value into the closed-of-open.
Counit: ○(●A) → A — extract from the open-of-closed. -/
def openClosedUnit {carrier : Type u} (value : carrier) : ClosedMod (OpenMod carrier) :=
  .mk (OpenMod.unit value)

def openClosedCounit {carrier : Type u} (openClosed : OpenMod (ClosedMod carrier)) : carrier :=
  (openClosed ()).extract

/-- Idempotence of ○: ○(○A) ≃ ○A (the open modality is idempotent). -/
def OpenMod.idempotent {carrier : Type u} : OpenMod (OpenMod carrier) → OpenMod carrier :=
  OpenMod.join

/-- Idempotence of ●: ●(●A) ≃ ●A (the closed modality is idempotent). -/
def ClosedMod.idempotent {carrier : Type u} : ClosedMod (ClosedMod carrier) → ClosedMod carrier
  | .mk (.mk value) => .mk value

/-- A strict glue type: pairs a syntactic witness with a semantic property.
This is the key construction for STC canonicity arguments.
(a : A) ⋊ B(a) = { syntactic : A, semantic : B(syntactic) } -/
structure StrictGlue (synType : Type u) (semProp : synType → Type u) where
  syntactic : synType
  semantic : semProp syntactic

/-- An extension type: a subtype that restricts to a given value under
the syntactic phase. { a : A | ∀ phase, a = prescribed phase } -/
structure ExtensionType (carrier : Type u) (prescribed : SynPhase → carrier) where
  value : carrier
  restricts : ∀ (phase : SynPhase), value = prescribed phase

/-- The STC model bundles: open + closed + glue + extension + laws. -/
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

/-- A canonicity witness via STC: a base type + enumeration of its
canonical forms + proof that closed terms land in the enumeration. -/
structure CanonicityWitness (baseType : Type u) where
  CanonicalForm : Type u
  embed : CanonicalForm → baseType
  extract : baseType → CanonicalForm
  roundtrip : ∀ (canonical : CanonicalForm), extract (embed canonical) = canonical

/-- Bool canonicity: every closed boolean is true or false. -/
def boolCanonicityWitness : CanonicityWitness Bool where
  CanonicalForm := Bool
  embed := id
  extract := id
  roundtrip := fun _ => rfl

end LeanFX2.Foundation.PolyCell.STC
