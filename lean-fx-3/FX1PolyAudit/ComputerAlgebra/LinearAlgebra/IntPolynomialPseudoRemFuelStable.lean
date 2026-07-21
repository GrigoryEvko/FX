import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoRemFuelStable

/-! # FX1PolyAudit/.../IntPolynomialPseudoRemFuelStable — zero-axiom gate

Per-declaration zero-axiom gate for the adequate-fuel pseudo-remainder stability: for a non-constant divisor,
extra fuel leaves the pseudo-remainder unchanged once fuel is adequate
(`polyPseudoRemFuelStableNonconstant`).  Structural fuel recursion; guard `Nat.decLt`; `Nat.add_right_comm`
+ core Nat order lemmas + the step degree-decrease.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemFuelStableNonconstant
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemFuelStableGrounding

end FX1PolyAudit
