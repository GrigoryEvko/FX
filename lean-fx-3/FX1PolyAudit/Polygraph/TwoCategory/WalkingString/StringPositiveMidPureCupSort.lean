import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidPureCupSort

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidPureCupSort — zero-axiom gate (FC-3 r45, R4 + R5, THE BRICK)

Per-declaration zero-axiom gate for THE BRICK `stringPositiveMidPureCupDeterminacy_proof` (inhabiting the
LITERAL `StringPositiveMidPureCupDeterminacy`, `StringPositiveMidCupSortResidual:89`) + the fueled sort's base
floor + the now-UNCONDITIONAL tower fired through the brick (the discharged completeness residual, the
unconditional `convOfMapEq`, the total decision) + the genuine distinct-double-cup fire.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The independent `#print axioms`
cross-check lives in the sibling `...AxiomWitness` file (it catches a `decide` silently degraded to `sorryAx`
and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★★ THE BRICK — the positive-mid pure-cup determinacy, INHABITED (the verbatim :89 statement)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidPureCupDeterminacy_proof

-- the now-UNCONDITIONAL tower fired through the brick
#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_holds
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_holds
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_holds
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_holds

-- the genuine positive-mid distinct-pair fire (equal matchingOfSpineList 2, distinct spines)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidBrick_firesOnDistinctDoubleCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidPureCupSort

end FX1PolyAudit
