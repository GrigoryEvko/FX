import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableNormalize

/-! # FX1PolyAudit/AuditTableNormalize — IOTA-T9 normalizer/Conv shard

Per-declaration zero-axiom gate for the table normalizer (Acc-recursion
+ correctness), the chain-from-normal-form collapse, table conversion
(join form, with confluence-powered transitivity), the
normalize-equality characterization, decidable conversion on the SN
fragment, and the canonical `StepTable.normalize`/`ConvTable`
instantiations.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The normalizer -/

#assert_no_axioms FX1Poly.Core.normalizeOverTable
#assert_no_axioms FX1Poly.Core.normalizeOverTable_unfold
#assert_no_axioms FX1Poly.Core.normalizeOverTable_reducesTo
#assert_no_axioms FX1Poly.Core.normalizeOverTable_isNormalForm
#assert_no_axioms FX1Poly.Core.ReflTransClosure.eq_of_isNormalFormOverTable

/-! ## Table conversion -/

#assert_no_axioms FX1Poly.Core.ConvOverTable
#assert_no_axioms FX1Poly.Core.ConvOverTable.refl
#assert_no_axioms FX1Poly.Core.ConvOverTable.sym
#assert_no_axioms FX1Poly.Core.ConvOverTable.fromClosure
#assert_no_axioms FX1Poly.Core.ConvOverTable.trans

/-! ## Normalize-equality + decidability -/

#assert_no_axioms FX1Poly.Core.ConvOverTable.iff_normalize_eq
#assert_no_axioms FX1Poly.Core.ConvOverTable.decidableOfStronglyNormalizing

/-! ## The canonical instantiation -/

#assert_no_axioms FX1Poly.Core.StepTable.normalize
#assert_no_axioms FX1Poly.Core.ConvTable
#assert_no_axioms FX1Poly.Core.ConvTable.refl
#assert_no_axioms FX1Poly.Core.ConvTable.sym
#assert_no_axioms FX1Poly.Core.ConvTable.trans
#assert_no_axioms FX1Poly.Core.ConvTable.decidableOfStronglyNormalizing

end FX1PolyAudit
