import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ModeAdmit

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ModeAdmit — zero-axiom gate for the mode-theory admission gate
(MODE-ADMIT r1, #2214)

Per-declaration zero-axiom gate for the whole gate: the fingerprint carrier (`FlatTwoGen` / `PresentationData` +
their hand-rolled `DecidableEq` instances), the fingerprint extraction (`ModeComputad.toPresentationData` +
`flattenTwoGen`) and the two extracted fingerprints, the decidable renaming matcher (`erasePair` /
`isPermutationOfPairs` / `isThinPresentationMatch`), the thin reference walker + registry + admission functions
(`thinComputadFamily` / `thinReferenceComputad` / `thinReferenceFamily` / `RegisteredModule` /
`modeAdmitRegistry` / `admitByName` / `isRegisteredThinRenaming` / `admitModeTheory`), the payoff theorems
(`admitByName_monad_isMonadFamily` / `admitByName_idempotent_isIdempotentFamily` /
`admitModeTheory_thinReference_isSome`), the end-to-end rehearsal (fingerprints distinct / matched / rejected,
the two admitted cells, the two verdicts + their `_holds`), and the four honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- P1: the fingerprint carrier + its hand-rolled DecidableEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.FlatTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.FlatTwoGen.decEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.instDecidableEqFlatTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.PresentationData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.PresentationData.decEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.instDecidableEqPresentationData

-- P1: the fingerprint extraction + the two extracted fingerprints + their distinctness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flattenTwoGen
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toPresentationData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionPresentation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPresentation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionPresentation_ne_monadPresentation

-- P3: the decidable renaming matcher
#assert_no_axioms FX1Poly.Polygraph.Amalgam.erasePair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isPermutationOfPairs
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isThinPresentationMatch

-- P4: the thin reference walker, the registry, and the admission functions
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinComputadFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinReferenceComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinReferenceFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RegisteredModule
#assert_no_axioms FX1Poly.Polygraph.Amalgam.modeAdmitRegistry
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByName
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isRegisteredThinRenaming
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitModeTheory

-- P4: the payoff theorems (accepted ==> packaged decider)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByName_monad_isMonadFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByName_idempotent_isIdempotentFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitModeTheory_thinReference_isSome

-- P5: the end-to-end rehearsal (distinctness / match / reject / cells / verdicts)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinRenamedComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinDistinctComputad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.firstGeneratorSource
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinRenamedPresentation_ne_reference
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinRenamed_matches_reference
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinDistinct_notMatches_reference
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monad_notThinMatches_reference
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinRenamedNilCellA
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinRenamedNilCellB
#assert_no_axioms FX1Poly.Polygraph.Amalgam.endToEndThinVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.endToEndThinVerdict_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.endToEndMonadSeparatesVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.endToEndMonadSeparatesVerdict_holds

-- P6: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasRegistryGate
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasEndToEndAdmission
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasRenamingDeciderTransport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasDataFingerprintAdmission

-- P1 (r2): the row-aware fingerprint — reflected cell data + its structural Bool equality
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawCellData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RawCellData.beq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.beqLawRow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.beqLawRows
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RowAwarePresentationData
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toRowAwarePresentationData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadGeneratorWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedEta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedMu
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reflectedIdT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadLawRowsData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentLawRowsData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadLawRowsData_ne_idempotentLawRowsData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRowAware
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentRowAware
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRowAware_idempotentRowAware_sameBase
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isRowAwarePresentationMatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRowAware_matches_self
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRowAware_notMatches_idempotent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentRowAware_notMatches_monad

-- P3 (r2): row-aware recognition registry + admission + inherited both-verdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RowAwareModule
#assert_no_axioms FX1Poly.Polygraph.Amalgam.rowAwareRegistry
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByRowAware
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByRowAware_monad_isMonadFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.admitByRowAware_idempotent_isIdempotentFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.rowAwareInheritedBothVerdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.rowAwareInheritedBothVerdicts_holds

-- P2 (r2): the renaming-iso witness interface + the forward transport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RenamingIso
#assert_no_axioms FX1Poly.Polygraph.Amalgam.transportConvForwardAlong

-- P6 (r2): the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasRowAwareRecognizedSeparation
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasRenamingWitnessInterface
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxModeAdmit_hasCertifiedDataAdmission

end FX1PolyAudit
