import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CongruenceWithId

/-! # FX1PolyAudit.Polygraph.Omega.CongruenceWithIdAudit — zero-axiom gate for the OMEGA-3 r2 idCongr sibling.

Per-declaration `#assert_no_axioms` on the idCongr-extended saturated congruence, its absorbing structure,
its 11-arm eliminator, the free embedding old -> new, and the vcompIdLeft jam-discharge lemma.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`
— including `SaturatedConvOverWithId.recInto`, whose `idCongr` arm bumps the dimension index. -/

namespace FX1PolyAudit

-- CongruenceWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.SaturatedConvOverWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.IsSaturatedCongruenceWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.SaturatedConvOverWithId.recInto
#assert_no_axioms FX1Poly.Polygraph.Omega.isSaturatedCongruenceEmbedWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.embedSaturatedConvOver
#assert_no_axioms FX1Poly.Polygraph.Omega.vcompIdLeft_bridgedWithId

end FX1PolyAudit
