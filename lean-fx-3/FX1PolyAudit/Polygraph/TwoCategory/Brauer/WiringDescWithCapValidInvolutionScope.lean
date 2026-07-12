import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScope

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScope — zero-axiom gate (r53)

Per-declaration zero-axiom gate for the BRAUER r53 with-cap valid-involution scoping: the valid-involution predicate
(`isInvolutionPartner`, `realizesValidInvolution`), the exact-iff census enumerators (`countValidInvolutionWords`,
`countValidInvolutionR51Realizing`, `countRepresentativeRealizeXorValid`, `withCapValidInvolutionCount`,
`withCapValidRepresentativeFailCount`, `capFreeValidCount`), the cap-DUAL refutation
(`reconstructStandardFormExt5CapDual`, `classRepresentativeCapDual`, `capDualRealizes`, `countCapDualRealizing`,
`countCapDualGainOverR51`, `capDualRegressesAt_capCrossCup1`), the re-diagnosis witnesses
(`capSideWitness0_isMalformedTarget`, `capSideWitness1_isMalformedTarget`, `capSideWitness2_isMalformedTarget`,
`safeCapWord_valid_andRealizes`, `capSideWitness0_topCountInflated`), the widened fold target
(`BrauerExt5CorrectedFoldReachesValidInvolution`), the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix` — the
predicate and census defs are structural over `List.all`/`List.filter`/`Nat.beq`/`Nat.blt`, the sibling extractor is a
flat record over the shipped read-offs, and the refutation / re-diagnosis witnesses are `decide`s over small concrete
diagrams.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isInvolutionPartner
#assert_no_axioms FX1Poly.Polygraph.realizesValidInvolution
#assert_no_axioms FX1Poly.Polygraph.countValidInvolutionWords
#assert_no_axioms FX1Poly.Polygraph.countValidInvolutionR51Realizing
#assert_no_axioms FX1Poly.Polygraph.countRepresentativeRealizeXorValid
#assert_no_axioms FX1Poly.Polygraph.withCapValidInvolutionCount
#assert_no_axioms FX1Poly.Polygraph.withCapValidRepresentativeFailCount
#assert_no_axioms FX1Poly.Polygraph.capFreeValidCount
#assert_no_axioms FX1Poly.Polygraph.reconstructStandardFormExt5CapDual
#assert_no_axioms FX1Poly.Polygraph.classRepresentativeCapDual
#assert_no_axioms FX1Poly.Polygraph.capDualRealizes
#assert_no_axioms FX1Poly.Polygraph.countCapDualRealizing
#assert_no_axioms FX1Poly.Polygraph.countCapDualGainOverR51
#assert_no_axioms FX1Poly.Polygraph.capDualRegressesAt_capCrossCup1
#assert_no_axioms FX1Poly.Polygraph.capSideWitness0_isMalformedTarget
#assert_no_axioms FX1Poly.Polygraph.capSideWitness1_isMalformedTarget
#assert_no_axioms FX1Poly.Polygraph.capSideWitness2_isMalformedTarget
#assert_no_axioms FX1Poly.Polygraph.safeCapWord_valid_andRealizes
#assert_no_axioms FX1Poly.Polygraph.capSideWitness0_topCountInflated
#assert_no_axioms FX1Poly.Polygraph.BrauerExt5CorrectedFoldReachesValidInvolution
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedExtractorValidInvolutionCoverage
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasValidInvolutionFoldDischarged
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_withCapValidInvolutionScopeTerminalState

end FX1PolyAudit
