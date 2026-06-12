import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableCertificationSubstrate

/-! # FX1PolyAudit/AuditIotaTableCertification — IOTA-T3 audit shard (certification substrate)

Per-declaration zero-axiom gate for the IOTA-T3 bricks: the dim-0
boundary collapse, the slot-indexed certified spine projections (shift
0/1/2, stated against the interpreter's own lookups), the
sort-universal generator-cell inversion, and the two-variable
substitution stability.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## Dim-0 collapse -/

#assert_no_axioms FX1Poly.Core.PolyCell.atDim0

/-! ## Per-shift head extraction -/

#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftZero
#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftOne
#assert_no_axioms FX1Poly.Core.ScopedChild.certifiedOfAtShiftTwo

/-! ## Slot-indexed certified projections -/

#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftZero
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftOne
#assert_no_axioms FX1Poly.Core.CertifiedTermSpine.certifiedAtShiftTwo

/-! ## Cell inversion -/

#assert_no_axioms FX1Poly.Core.PolyCell.invertGenAtDim0

/-! ## Two-variable substitution certifies -/

#assert_no_axioms FX1Poly.Core.PolyCell.pairSubstDim0Cells
#assert_no_axioms FX1Poly.Core.HasCertifiedCellDim0.preservedBySubstPair

end FX1PolyAudit
