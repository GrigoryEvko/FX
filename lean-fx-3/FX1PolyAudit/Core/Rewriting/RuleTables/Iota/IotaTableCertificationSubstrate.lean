import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableCertificationSubstrate

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableCertificationSubstrate

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableCertificationSubstrate`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.PolyCell.atDim0

#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftZero

#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftOne

#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftTwo

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftZero

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftOne

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftTwo

#assert_no_axioms FX1Poly.Core.PolyCell.invertGenAtDim0

#assert_no_axioms FX1Poly.Core.PolyCell.pairSubstDim0Cells

#assert_no_axioms FX1Poly.Core.HasCertifiedCellDim0.preservedBySubstPair

#assert_no_axioms FX1Poly.Core.PolyCell.varCell

#assert_no_axioms FX1Poly.Core.PolyCell.subst0_dim0

#assert_no_axioms FX1Poly.Core.PolyCell.substPair_dim0

#assert_no_axioms FX1Poly.Core.PolyCell.weakenBy_dim0

#assert_no_axioms FX1Poly.Core.PolyCell.weakenBodyUnderOneBinderBy_dim0

#assert_no_axioms FX1Poly.Core.PolyCell.weakenBodyUnderTwoBindersBy_dim0

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedWeakenSpineBy

#assert_no_axioms FX1Poly.Core.PolyCell.ofDim0

#assert_no_axioms FX1Poly.Core.replacementIntoShiftCertified

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedReplaceChildAt

#assert_no_axioms FX1Poly.Core.ReductTemplate.CertifiesAtSort

#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.CertifyAgainstSpecs

#assert_no_axioms FX1Poly.Core.SpineReplacements.CertifyReplacementSorts

end FX1PolyAudit
