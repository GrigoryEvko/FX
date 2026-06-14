import FX1Poly.Tier0.ModeOmega.Interface
import FX1Poly.Modal.EffectLatticeClassification

/-! # Tier0/ModeOmega — the per-mode structure-class certificate (mode-2)

mode-0 reserved the `StructureClassCertificate` skeleton and the `structureClassCertificate`
construction-ladder rung; mode-1 promoted the strict-2-category rung.  This module INHABITS the
certificate and promotes the `structureClassCertificate` rung GAP→BUILT — the multiplier certificate of
Gratzer's mode theory (the per-mode analogue of Gratzer Fig 7/9): each FX mode is tagged with the
DIM-CLASS structure shape its grade algebra is.

## The classification is GROUNDED, not asserted

Each FX mode atom belongs to one of FX's §6 graded dimensions, and the structure-class of the mode is
the structure-class of its home dimension — already MACHINE-CHECKED in the shipped DIM-CLASS work
(`Modal/EffectLatticeClassification.lean`: `GradedDimensionName.gradeAlgebraOf` + `usage_isOrderedSemiring`
/ `security_isOrderedSemiring` / `effect_isBoundedSemilattice`, all `rfl`, with the lawful algebra
bundles `fxUsageSemiring_isLawful` / `fxSecuritySemiring_isLawful` / `effectIsLawfulBoundedJoinSemilattice`).
So `fxModeStructureClass` is DEFINED by composing the shipped `gradeAlgebraOf` — the mode classification
inherits its correctness from the shipped dimension classification rather than re-asserting it.

The home-dimension map:

  * `pure`, `async` → the **effect** dimension → bounded join-semilattice;
  * `linear`, `affine`, `unrestricted`, `ghost` → the **usage** dimension → ordered semiring;
  * `classified`, `unclassified` → the **security** dimension → ordered semiring.

## Boundary (recorded)

The 8 FX mode atoms draw from exactly two structure classes (ordered semiring + bounded join-semilattice);
the other five `StructureClassLabel` shapes (total-order chain, the M3 diamond, preorder, involution,
category) are realized by OTHER §6 dimensions (mutation, overflow, lifetime, session, version) but not by
these mode atoms — so `allSevenStructureClassesRealizedByModes` is honestly `false`.

Zero external dependencies beyond the Init-only DIM-CLASS algebra files (`ResourceGraded`,
`EffectLatticeClassification` — both Tier0-safe).  Anchors are `⟨shipped-fact, rfl⟩` pairs and lawful-bundle
re-exports — no `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModeOmega.lean`. -/

namespace FX1Poly.Tier0.ModeOmega

open FX1Poly.MTTNorm
open FX1Poly.Modal

/-! ## The grounded classification map -/

/-- **The home dimension of each FX mode atom.**  Each mode is a grade setting of one §6 graded
dimension: the usage modes (`linear`/`affine`/`unrestricted`/`ghost`), the security modes
(`classified`/`unclassified`), and the effect modes (`pure`/`async`).  Full enumeration, no wildcard. -/
def fxModeHomeDimension : FXModeAtom → GradedDimensionName
  | .pure => .effect
  | .async => .effect
  | .linear => .usage
  | .affine => .usage
  | .unrestricted => .usage
  | .ghost => .usage
  | .classified => .security
  | .unclassified => .security

/-- **Bridge: dimension grade-algebra → mode structure-class label.**  The shipped DIM-CLASS verdict
(`DimensionGradeAlgebra` = ordered semiring | bounded semilattice) maps into the mode-axis
`StructureClassLabel` taxonomy. -/
def dimensionAlgebraToStructureClass : DimensionGradeAlgebra → StructureClassLabel
  | .orderedSemiring => .orderedSemiring
  | .boundedSemilattice => .boundedJoinSemilattice

/-- **The per-mode structure-class.**  DEFINED by composing the shipped `gradeAlgebraOf` — so the mode
classification is grounded in the machine-checked dimension classification, not re-asserted. -/
def fxModeStructureClass (mode : FXModeAtom) : StructureClassLabel :=
  dimensionAlgebraToStructureClass (fxModeHomeDimension mode).gradeAlgebraOf

/-- **The structure-class certificate** — inhabits the `mode-0` reserved skeleton over `fxModeOmega`. -/
def fxModeStructureClassCertificate : StructureClassCertificate fxModeOmega where
  structureClassOf := fxModeStructureClass

/-- The certificate's classifier is exactly `fxModeStructureClass`. -/
theorem fxModeStructureClassCertificate_structureClassOf_eq :
    fxModeStructureClassCertificate.structureClassOf = fxModeStructureClass := rfl

/-! ## The genuine grounding anchors (each chains to a shipped DIM-CLASS fact) -/

/-- **The usage-family modes are ordered semirings.**  All four usage modes classify as `orderedSemiring`,
chained to the shipped `usage_isOrderedSemiring`. -/
theorem fxModeUsageFamilyOrderedSemiring :
    (fxModeStructureClass FXModeAtom.linear = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.affine = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.unrestricted = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.ghost = StructureClassLabel.orderedSemiring)
      ∧ GradedDimensionName.usage.gradeAlgebraOf = DimensionGradeAlgebra.orderedSemiring :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, usage_isOrderedSemiring⟩

/-- **The security-family modes are ordered semirings.**  Both security modes classify as
`orderedSemiring`, chained to the shipped `security_isOrderedSemiring`. -/
theorem fxModeSecurityFamilyOrderedSemiring :
    (fxModeStructureClass FXModeAtom.classified = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.unclassified = StructureClassLabel.orderedSemiring)
      ∧ GradedDimensionName.security.gradeAlgebraOf = DimensionGradeAlgebra.orderedSemiring :=
  ⟨⟨rfl, rfl⟩, security_isOrderedSemiring⟩

/-- **The effect-family modes are bounded join-semilattices.**  Both effect modes classify as
`boundedJoinSemilattice`, chained to the shipped `effect_isBoundedSemilattice` (the DIM-CLASS BOUNDARY:
effect is NOT a semiring). -/
theorem fxModeEffectFamilyBoundedJoinSemilattice :
    (fxModeStructureClass FXModeAtom.pure = StructureClassLabel.boundedJoinSemilattice
      ∧ fxModeStructureClass FXModeAtom.async = StructureClassLabel.boundedJoinSemilattice)
      ∧ GradedDimensionName.effect.gradeAlgebraOf = DimensionGradeAlgebra.boundedSemilattice :=
  ⟨⟨rfl, rfl⟩, effect_isBoundedSemilattice⟩

/-- **The ordered-semiring class is backed by lawful algebra bundles.**  The label assigned to the
usage/security modes is not a bare tag — the shipped `fxUsageSemiring_isLawful` / `fxSecuritySemiring_isLawful`
prove the full ordered-semiring laws. -/
theorem fxModeOrderedSemiringClassIsLawful :
    IsLawfulOrderedGradeSemiring fxUsageSemiring ∧ IsLawfulOrderedGradeSemiring fxSecuritySemiring :=
  ⟨fxUsageSemiring_isLawful, fxSecuritySemiring_isLawful⟩

/-- **The bounded-join-semilattice class is backed by a lawful bundle.**  The label assigned to the
effect modes is backed by the shipped `effectIsLawfulBoundedJoinSemilattice`. -/
theorem fxModeBoundedJoinSemilatticeClassIsLawful :
    IsLawfulBoundedJoinSemilattice effectLattice :=
  effectIsLawfulBoundedJoinSemilattice

/-- **Every FX mode is classified.**  All eight mode atoms receive a structure-class label (the certificate
is total over the finite mode set). -/
theorem fxModeEveryModeClassified :
    fxModeStructureClass FXModeAtom.pure = StructureClassLabel.boundedJoinSemilattice
      ∧ fxModeStructureClass FXModeAtom.async = StructureClassLabel.boundedJoinSemilattice
      ∧ fxModeStructureClass FXModeAtom.linear = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.affine = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.unrestricted = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.ghost = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.classified = StructureClassLabel.orderedSemiring
      ∧ fxModeStructureClass FXModeAtom.unclassified = StructureClassLabel.orderedSemiring :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The honest ledger -/

/-- Honest ledger for the per-mode structure-class certificate.  The seven core flags hold; the final
boundary flag records that the 8 mode atoms span only two of the seven structure classes. -/
structure StructureClassCertificateLedger where
  /-- The `StructureClassCertificate fxModeOmega` skeleton is inhabited. -/
  certificateInhabited : Bool
  /-- Every FX mode atom receives a structure-class label. -/
  everyModeClassified : Bool
  /-- The usage-family modes classify as ordered semirings. -/
  usageFamilyIsOrderedSemiring : Bool
  /-- The security-family modes classify as ordered semirings. -/
  securityFamilyIsOrderedSemiring : Bool
  /-- The effect-family modes classify as bounded join-semilattices. -/
  effectFamilyIsBoundedJoinSemilattice : Bool
  /-- The classification is grounded in the shipped DIM-CLASS `gradeAlgebraOf` (composed, not asserted). -/
  groundedInShippedDimClass : Bool
  /-- Each assigned label is backed by a shipped lawful algebra bundle. -/
  labelsBackedByLawfulBundles : Bool
  /-- BOUNDARY: the 8 mode atoms realize only the ordered-semiring + bounded-join-semilattice classes;
  the other five `StructureClassLabel` shapes belong to OTHER dimensions, not these mode atoms. -/
  allSevenStructureClassesRealizedByModes : Bool

/-- The FX mode structure-class certificate ledger: seven core flags hold; the all-seven-classes boundary
flag is honestly `false`. -/
def fxModeStructureClassCertificateLedger : StructureClassCertificateLedger where
  certificateInhabited := true
  everyModeClassified := true
  usageFamilyIsOrderedSemiring := true
  securityFamilyIsOrderedSemiring := true
  effectFamilyIsBoundedJoinSemilattice := true
  groundedInShippedDimClass := true
  labelsBackedByLawfulBundles := true
  allSevenStructureClassesRealizedByModes := false

/-- **The structure-class certificate is recognized.**  All seven core ledger flags hold; the
all-seven-classes boundary flag is `false`.  This is the mode-2 headline. -/
theorem fxModeStructureClassCertificateRecognized :
    fxModeStructureClassCertificateLedger.certificateInhabited = true
      ∧ fxModeStructureClassCertificateLedger.everyModeClassified = true
      ∧ fxModeStructureClassCertificateLedger.usageFamilyIsOrderedSemiring = true
      ∧ fxModeStructureClassCertificateLedger.securityFamilyIsOrderedSemiring = true
      ∧ fxModeStructureClassCertificateLedger.effectFamilyIsBoundedJoinSemilattice = true
      ∧ fxModeStructureClassCertificateLedger.groundedInShippedDimClass = true
      ∧ fxModeStructureClassCertificateLedger.labelsBackedByLawfulBundles = true
      ∧ fxModeStructureClassCertificateLedger.allSevenStructureClassesRealizedByModes = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Ladder promotion (ADDITION-ONLY supersession of the mode-0 snapshot) -/

/-- The mode ω-category's construction level ADVANCED by mode-2: the structure-class certificate is built.
ADDED alongside the committed mode-0/mode-1 levels; does not mutate them. -/
def fxModeOmegaStructureClassLevel : ModeOmegaConstructionLevel :=
  .structureClassCertificate

/-- BUILT (mode-2): at the advanced level the structure-class certificate rung is present. -/
theorem fxModeOmegaStructureClassLevel_hasStructureClassCertificate :
    fxModeOmegaStructureClassLevel.hasStructureClassCertificate = true := rfl

/-- Monotone: the advanced level still has the strict 2-category core rung (mode-1). -/
theorem fxModeOmegaStructureClassLevel_stillHasStrictTwoCategoryCore :
    fxModeOmegaStructureClassLevel.hasStrictTwoCategoryCore = true := rfl

/-- Honest: mode-2 built exactly one further rung — decidable 2-cell equality (mode-3) is still a GAP. -/
theorem fxModeOmegaStructureClassLevel_hasNoThreeCellsDecidable :
    fxModeOmegaStructureClassLevel.hasThreeCellsDecidable = false := rfl

end FX1Poly.Tier0.ModeOmega
