import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.UnionParitySurpassLedger

/-! # FX1PolyAudit/AuditUnionParitySurpassLedger — zero-axiom gate for the union parity-and-surpass ledger

Per-declaration `#assert_no_axioms` over every shipped decl of
`FX1Poly.Typed.UnionParitySurpassLedger`, plus the ledger COVERAGE gate: the count theorems are
re-asserted here so a silent regression in the honest accounting (e.g. flipping an `open` cell to
`proven` without a citation, which would change `coveredCapabilityCount`) fails this audit file.

The ledger's anchors are proof-term aliases of shipped union theorems; gating each anchor re-certifies
that the union's witness for that capability is itself zero-axiom.  The `open` capability rows carry NO
anchor (no union theorem exists for them yet) — only their status `rfl` facts are gated, which is the
honest record that the row is open.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` is introduced
by this file. -/

open FX1Poly.Typed

/-! ## The capability-row enums and status projection -/

#assert_no_axioms FX1Poly.Typed.UnionCapability
#assert_no_axioms FX1Poly.Typed.ParityStatus
#assert_no_axioms FX1Poly.Typed.UnionCapability.parityStatus

/-! ## The capability anchors (the proven / bridged cell witnesses) -/

#assert_no_axioms FX1Poly.Typed.unionAnchor_typingAdequacy
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_pathLamHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_lamHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_natElimHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_natSuccHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_boolElimHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_idJHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_natRecHead
#assert_no_axioms FX1Poly.Typed.unionAnchor_inversion_genericRefutation
#assert_no_axioms FX1Poly.Typed.unionAnchor_substitution
#assert_no_axioms FX1Poly.Typed.unionAnchor_rootSubjectReduction
#assert_no_axioms FX1Poly.Typed.unionAnchor_reverseAdequacy
#assert_no_axioms FX1Poly.Typed.unionAnchor_honestyClassifier_table
#assert_no_axioms FX1Poly.Typed.unionAnchor_honestyClassifier_equivalence
#assert_no_axioms FX1Poly.Typed.unionAnchor_affineRejection

/-! ## The parity ledger facts -/

#assert_no_axioms FX1Poly.Typed.typingAdequacy_atParity
#assert_no_axioms FX1Poly.Typed.inversion_atParity
#assert_no_axioms FX1Poly.Typed.substitution_atParity
#assert_no_axioms FX1Poly.Typed.rootSubjectReduction_isBridged
#assert_no_axioms FX1Poly.Typed.reverseAdequacy_atParity
#assert_no_axioms FX1Poly.Typed.honestyClassifier_atParity
#assert_no_axioms FX1Poly.Typed.affineRejection_atParity
#assert_no_axioms FX1Poly.Typed.weakening_isOpen
#assert_no_axioms FX1Poly.Typed.uniqueness_isOpen
#assert_no_axioms FX1Poly.Typed.reducibilityStrongNormalization_isOpen
#assert_no_axioms FX1Poly.Typed.canonicity_isOpen
#assert_no_axioms FX1Poly.Typed.contextConversion_isOpen

/-! ## The parity criterion + computed counts -/

#assert_no_axioms FX1Poly.Typed.ParityStatus.isCovered
#assert_no_axioms FX1Poly.Typed.ParityStatus.isStrictlyProven
#assert_no_axioms FX1Poly.Typed.allCapabilities
#assert_no_axioms FX1Poly.Typed.coveredCapabilityCount
#assert_no_axioms FX1Poly.Typed.strictlyProvenCapabilityCount
#assert_no_axioms FX1Poly.Typed.openCapabilityCount
#assert_no_axioms FX1Poly.Typed.coveredCapabilityCount_isSeven
#assert_no_axioms FX1Poly.Typed.strictlyProvenCapabilityCount_isSix
#assert_no_axioms FX1Poly.Typed.openCapabilityCount_isFive
#assert_no_axioms FX1Poly.Typed.unionFullParity_not_yet_achieved

/-! ## The surpass enum, projection, anchors, and criterion -/

#assert_no_axioms FX1Poly.Typed.SurpassCapability
#assert_no_axioms FX1Poly.Typed.SurpassCapability.isShipped
#assert_no_axioms FX1Poly.Typed.surpassAnchor_affineRejection
#assert_no_axioms FX1Poly.Typed.surpassAnchor_twoPathSubsumption
#assert_no_axioms FX1Poly.Typed.surpassAnchor_tableClassifier
#assert_no_axioms FX1Poly.Typed.surpassAnchor_tableEquivalence
#assert_no_axioms FX1Poly.Typed.surpassAnchor_crossFamilyRootSR
#assert_no_axioms FX1Poly.Typed.conversionArmAdmitsReclassification
#assert_no_axioms FX1Poly.Typed.allSurpassCapabilities
#assert_no_axioms FX1Poly.Typed.shippedSurpassCount
#assert_no_axioms FX1Poly.Typed.allSurpassCapabilitiesShipped
#assert_no_axioms FX1Poly.Typed.unionSurpasses_isMet

/-! ## Non-vacuity discriminations -/

#assert_no_axioms FX1Poly.Typed.parity_discriminates_proven_vs_open
#assert_no_axioms FX1Poly.Typed.parity_discriminates_bridged_vs_proven
#assert_no_axioms FX1Poly.Typed.parity_discriminates_bridged_vs_open

/-! ## The coverage gate

These re-assert the ledger's honest counts HERE so a regression in the accounting (e.g. an `open` cell
flipped to `proven` without a citation, changing the covered/open split) fails this audit file rather
than silently passing.  The criterion theorems are re-checked, and the SHIPPED surpass count is pinned
at five.  All close by the ledger's own `rfl` facts. -/

/-- COVERAGE: the present honest split is 7 covered / 6 strictly proven / 5 open of 12 rows, and all 5
surpass capabilities are shipped.  Any drift in the ledger breaks this conjunction. -/
theorem unionParityLedgerCoverageGate :
    coveredCapabilityCount = 7 ∧
    strictlyProvenCapabilityCount = 6 ∧
    openCapabilityCount = 5 ∧
    shippedSurpassCount = 5 ∧
    ¬ unionAchievesFullParity ∧
    unionSurpasses :=
  ⟨coveredCapabilityCount_isSeven, strictlyProvenCapabilityCount_isSix, openCapabilityCount_isFive,
    allSurpassCapabilitiesShipped, unionFullParity_not_yet_achieved, unionSurpasses_isMet⟩

#assert_no_axioms unionParityLedgerCoverageGate
