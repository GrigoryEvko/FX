import FX1Poly.Tier0.FxBaseSubstWitnessScone
import FX1Poly.Tier0.FxBaseSubstConcreteScone
import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections

/-! # FX1Poly/Tier0/FxBaseSubstCanonicityExtraction
    — canonicity extraction is a PER-SCONE property: the global record refuted, the honest form shipped (SN-093, #596)

`InternalSconing.lean` transcribed the BKS canonicity-extraction obligation as a record whose
`extract` field quantifies over EVERY sconing object of the base.  This file settles that interface
with a refutation and replaces it with the honest per-scone form:

  * ★ `canonicityExtraction_overSubstBase_isFalse` / `_overRenamingBase_isFalse` — **the global
    record is UNINHABITABLE** over both shipped `GlobalSections`: the adversarial scone with an
    EMPTY semantic domain (`emptyDomainScone`) sits over scope `0`, whose sections are `PUnit`
    (inhabited), so a global `extract` would inhabit `PEmpty`.  Extraction is not a property of the
    base — it is a property of EACH scone (surjectivity of its realization).
  * `SconeCanonicityExtraction sconedType` — the honest PER-SCONE record: the same two fields
    (`extract` + `extractRealizes`), for a FIXED scone.  `realizationIsSurjective` makes the
    characterization explicit, and `isFalse_ofUnrealizedSection` is the refutation criterion (one
    orphan section kills extraction).
  * `tautologicalSconeCanonicityExtraction` — generic inhabitation (extract = `id`, realizes `rfl`).
  * ★ `closedTermSconeCanonicityExtraction` — the GENUINE instance: the closed-term scone's
    realization (`closedTermAsSection`, the term-presheaf embedding) is split by
    `sectionAsClosedTerm` with a definitional round-trip — a non-tautological extraction whose
    `extract` genuinely reads the canonical (closed-term) form off a global element.
  * `emptyValueScone_hasNoCanonicityExtraction` — the CONSISTENCY reading: the empty type's
    predicate-carrying scone (SUBSTVEC-9) has NO extraction — its semantic domain is uninhabited
    while its sections are not.  Extraction over predicate-carrying scones is exactly the typed
    surjectivity canonicity supplies, and the empty type rightly refuses it.

## Where the TRANSFER theorem lives

The law-carrying canonicity TRANSFER for the glued model is `GluedTypeCell.canonicityTransfer`
(`GluedModelTypeFormers.lean`): for every glued type — in particular the SN-091 Π/Σ/universe lifts —
the scone turns well-typedness into canonicity (`SconingWitness.canonicity`, extraction free by
CR1).  This file supplies the categorical-record half: which sconing objects admit extraction at
all, with the global form refuted and the per-scone form characterized and concretely inhabited.
The `fxSconingConstructionLevel` ledger advances to `.canonicityTransferTheorem` on this package
(see `InternalSconing.lean`).

## Zero-axiom verification

The refutations are one adversarial construction + one application; the per-scone record is two
fields; the instances are the shipped SUBSTVEC-6 round-trips (`rfl`) and the SUBSTVEC-9
uninhabitedness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

universe u v w

/-- **The adversarial scone over the term base**: empty semantic domain over scope `0` (whose
sections `SubstVec 0 0 = PUnit` are inhabited).  The witness that kills the global extraction
record. -/
def emptyDomainScone : SconingObject fxBaseSubstCategory fxBaseSubstGlobalSections where
  syntacticObject := (0 : Nat)
  semanticDomain := PEmpty
  realizationMap := fun adversarialMember => adversarialMember.elim

/-- ★ **The global `CanonicityExtraction` record is UNINHABITABLE over the term base.**  A global
`extract` applied to the adversarial empty-domain scone at the inhabited scope-`0` section would
inhabit `PEmpty`.  Extraction is a per-scone property, not a property of the base. -/
theorem canonicityExtraction_overSubstBase_isFalse
    (globalExtraction : CanonicityExtraction fxBaseSubstGlobalSections) : False :=
  (globalExtraction.extract emptyDomainScone (PUnit.unit : SubstVec 0 0)).elim

/-- The adversarial scone over the RENAMING base (sections at scope `0` are `PUnit` there too). -/
def emptyDomainSconeOverRenamingBase :
    SconingObject fxBaseRenamingVecCategory fxBaseRenamingVecGlobalSections where
  syntacticObject := (0 : Nat)
  semanticDomain := PEmpty
  realizationMap := fun adversarialMember => adversarialMember.elim

/-- The renaming-base twin of the refutation: no global extraction there either. -/
theorem canonicityExtraction_overRenamingBase_isFalse
    (globalExtraction : CanonicityExtraction fxBaseRenamingVecGlobalSections) : False :=
  (globalExtraction.extract emptyDomainSconeOverRenamingBase
    (PUnit.unit : RenamingVec 1 0)).elim

/-- **The honest PER-SCONE canonicity-extraction record**: the same two obligations the global
record carried, for a FIXED sconing object — extract a semantic (canonical) witness from every
global element, realizing back to it.  Inhabitable exactly when the scone's realization is
split-surjective. -/
structure SconeCanonicityExtraction {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    (sconedType : SconingObject category globalSections) where
  /-- Extract the canonical form of a global element of the sconed type. -/
  extract : globalSections.sections sconedType.syntacticObject → sconedType.semanticDomain
  /-- The extracted canonical form realizes the original global element. -/
  extractRealizes :
    ∀ closedTerm : globalSections.sections sconedType.syntacticObject,
      sconedType.realizationMap (extract closedTerm) = closedTerm

/-- A per-scone extraction makes the realization surjective — the characterization direction that
needs no choice. -/
theorem SconeCanonicityExtraction.realizationIsSurjective {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    {sconedType : SconingObject category globalSections}
    (extraction : SconeCanonicityExtraction sconedType)
    (closedTerm : globalSections.sections sconedType.syntacticObject) :
    ∃ member : sconedType.semanticDomain, sconedType.realizationMap member = closedTerm :=
  ⟨extraction.extract closedTerm, extraction.extractRealizes closedTerm⟩

/-- **The refutation criterion**: one global element no semantic member realizes kills the
extraction. -/
theorem SconeCanonicityExtraction.isFalse_ofUnrealizedSection {category : RawCategory.{u, v}}
    {globalSections : GlobalSections.{u, v, w} category}
    {sconedType : SconingObject category globalSections}
    (orphanSection : globalSections.sections sconedType.syntacticObject)
    (isUnrealized : ∀ member : sconedType.semanticDomain,
      sconedType.realizationMap member ≠ orphanSection)
    (extraction : SconeCanonicityExtraction sconedType) : False :=
  isUnrealized (extraction.extract orphanSection) (extraction.extractRealizes orphanSection)

/-- The tautological scone always admits extraction (extract = `id`, realizes `rfl`) — generic
interface inhabitation over any base. -/
def tautologicalSconeCanonicityExtraction {category : RawCategory.{u, v}}
    (globalSections : GlobalSections.{u, v, w} category) (baseObject : category.Object) :
    SconeCanonicityExtraction (SconingObject.tautological globalSections baseObject) where
  extract := id
  extractRealizes := fun _closedTerm => rfl

/-- ★ **The genuine instance**: the closed-term scone's realization (the term-presheaf embedding
`closedTermAsSection`) is split by `sectionAsClosedTerm`, with the SUBSTVEC-6 round-trip closing
`extractRealizes` definitionally — a non-tautological extraction reading the closed-term canonical
form off a global element. -/
def closedTermSconeCanonicityExtraction :
    SconeCanonicityExtraction fxBaseSubstClosedTermScone where
  extract := sectionAsClosedTerm
  extractRealizes := closedTermAsSection_sectionAsClosedTerm

/-- **The consistency reading at the extraction level**: the EMPTY type's predicate-carrying scone
(SUBSTVEC-9) admits NO extraction — its semantic domain is uninhabited while its sections are not.
Extraction over predicate-carrying scones is exactly the typed surjectivity that canonicity
supplies, and the empty type rightly refuses it. -/
theorem emptyValueScone_hasNoCanonicityExtraction
    (extraction : SconeCanonicityExtraction emptyValueScone) : False :=
  emptyValueScone_semanticIsUninhabited
    (extraction.extract (closedTermAsSection (RawTerm.mkGen .gen_unit () .childNil)))

end FX1Poly.Tier0
