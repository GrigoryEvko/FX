import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulSwapTraceInvariance

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulSwapTraceInvariance — zero-axiom gate

Per-declaration zero-axiom gate for the r14 (I2 + I4) FAITHFUL swap TRACE-INVARIANCE: the inductive congruence
`FaithfulSwapTraceEquiv` (the reflexive-symmetric-transitive closure of the r13 dispatcher's admissible two-step
exchange move) and ★ `extractArc_eq_of_faithfulSwapTraceEquiv` (the extract-after-`rest` is invariant along it, by
STRUCTURAL induction on the equivalence derivation firing `arcFaithfulSwapExtractRestCommute` in the `ofSwap`
arm).  Plus the crossing-involving non-vacuity witnesses and the I4 honesty marker + pins.

The critical check: induction on the `Prop`-valued inductive must NOT leak `propext` (its motive is an `Eq`, and
`symm` / `trans` route through `Eq.symm` / `Eq.trans` — structural, not propositional-extensionality).

The file flips ONLY its own NEW marker `fxMode_hasArcFaithfulTraceInvariance := true`; the permanent originals stay
false — `fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and `fxMode_hasArcGodementSamePartitionFreshProof`
(the `:545` / #2043 / WP-AMALG keystone) are re-asserted `false` by `rfl`; the dispatcher provider stays `true`.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the trace congruence + its extract-invariance
#assert_no_axioms FX1Poly.Polygraph.FaithfulSwapTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulSwapTraceEquiv

-- crossing-involving non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.faithfulSwapTraceEquiv_mixedSeed_confirms
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulSwapTraceEquiv_mixedSeed_confirms

-- I4 honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulTraceInvariance
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_dispatcher_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.FaithfulSwapTraceEquiv
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulSwapTraceEquiv
#print axioms FX1Poly.Polygraph.faithfulSwapTraceEquiv_mixedSeed_confirms
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulSwapTraceEquiv_mixedSeed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulTraceInvariance
#print axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_dispatcher_stays_true
#print axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulTraceInvariance_samePartitionFreshProof_stays_false

end FX1PolyAudit
