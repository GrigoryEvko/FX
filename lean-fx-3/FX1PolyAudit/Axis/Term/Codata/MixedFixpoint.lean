import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Codata.MixedFixpoint

/-! # FX1PolyAudit/AuditAxisTermMixedFixpoint — zero-axiom gate for term-14 (mixed μ/ν parity)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Codata/MixedFixpoint.lean`: the least fixpoint
(`MuTree` / `MuTree.fold` / `MuTree.fold_unique` induction / `MuTree.size`), the greatest fixpoint
(`NuStream` / `head` / `tail` / `corec` + the head/tail laws + `corec_unique` coinduction), the mixed
`ν(μ)` type (`MixedMuNu` / `mixedFold` + head/tail commutation), and the μ/ν parity (`mu_isFinite` vs
`nu_canBeUnbounded`), plus the witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The least fixpoint μ: finite trees + the fold + the induction principle + finiteness
#assert_no_axioms FX1Poly.Core.MuTree
#assert_no_axioms FX1Poly.Core.MuTree.fold
#assert_no_axioms FX1Poly.Core.MuTree.size
#assert_no_axioms FX1Poly.Core.MuTree.fold_unique
#assert_no_axioms FX1Poly.Core.MuTree.fold_fusion

-- The greatest fixpoint ν: streams + corec + the laws + the coinduction principle
#assert_no_axioms FX1Poly.Core.NuStream
#assert_no_axioms FX1Poly.Core.NuStream.head
#assert_no_axioms FX1Poly.Core.NuStream.tail
#assert_no_axioms FX1Poly.Core.iterateAdvance
#assert_no_axioms FX1Poly.Core.NuStream.corec
#assert_no_axioms FX1Poly.Core.NuStream.corec_head
#assert_no_axioms FX1Poly.Core.iterateAdvance_commute
#assert_no_axioms FX1Poly.Core.NuStream.corec_tail
#assert_no_axioms FX1Poly.Core.NuStream.corec_unique
#assert_no_axioms FX1Poly.Core.NuStream.corec_fusion

-- The mixed ν(μ) type + the fold/observe commutation
#assert_no_axioms FX1Poly.Core.MixedMuNu
#assert_no_axioms FX1Poly.Core.mixedFold
#assert_no_axioms FX1Poly.Core.mixedFold_head
#assert_no_axioms FX1Poly.Core.mixedFold_tail

-- The μ/ν parity (finiteness vs unboundedness) + the witness
#assert_no_axioms FX1Poly.Core.mu_isFinite
#assert_no_axioms FX1Poly.Core.nu_canBeUnbounded
#assert_no_axioms FX1Poly.Core.exampleMixedFold

end FX1PolyAudit
