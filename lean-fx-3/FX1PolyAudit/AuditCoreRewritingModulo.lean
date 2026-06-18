import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RewritingModulo

/-! # FX1PolyAudit/AuditCoreRewritingModulo — zero-axiom gate for term-16 (Church-Rosser modulo E)

Per-declaration zero-axiom gate for `FX1Poly/Core/Rewriting/RewritingModulo.lean`: the modulo-`E` vocabulary
(`JoinableModulo` / `equationalTheory_of_rtc` / `equationalTheory_of_joinableModulo`), Church-Rosser modulo
`E` (`ChurchRosserModulo` / `churchRosserModulo_characterization`), the trivial-`E` bridge to ordinary
confluence (`joinableModulo_eq_joinable` / `equationalTheory_collapseEq` / `churchRosserModulo_eq_of_confluent`),
and the commutativity (AC-flavored) equational theory witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Joinability modulo E + the easy half of CR-modulo
#assert_no_axioms FX1Poly.Core.JoinableModulo
#assert_no_axioms FX1Poly.Core.equationalTheory_of_rtc
#assert_no_axioms FX1Poly.Core.equationalTheory_of_joinableModulo

-- Church-Rosser modulo E + the characterization
#assert_no_axioms FX1Poly.Core.ChurchRosserModulo
#assert_no_axioms FX1Poly.Core.churchRosserModulo_characterization

-- The bridge to ordinary Church-Rosser (term-7): trivial E
#assert_no_axioms FX1Poly.Core.joinableModulo_eq_joinable
#assert_no_axioms FX1Poly.Core.equationalTheory_collapseEq
#assert_no_axioms FX1Poly.Core.churchRosserModulo_eq_of_confluent

-- The commutativity (AC-flavored) equational theory + witness
#assert_no_axioms FX1Poly.Core.commutativeEquiv
#assert_no_axioms FX1Poly.Core.commutativeEquiv_refl
#assert_no_axioms FX1Poly.Core.commutativeEquiv_symm
#assert_no_axioms FX1Poly.Core.commutativeEquiv_trans
#assert_no_axioms FX1Poly.Core.swapConvertibleModuloCommutativity

end FX1PolyAudit
