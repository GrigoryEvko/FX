import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.RewritingModulo

/-! # FX1PolyAudit.Polygraph.Rewriting.RewritingModulo

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.RewritingModulo`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Joinability modulo E + the easy half of CR-modulo
#assert_no_axioms FX1Poly.Core.JoinableModulo

#assert_no_axioms FX1Poly.Core.equationalTheory_of_rtc

#assert_no_axioms FX1Poly.Core.equationalTheory_of_joinableModulo

-- JoinableModulo is reflexive + symmetric (an equivalence when E is)
#assert_no_axioms FX1Poly.Core.joinableModulo_refl

#assert_no_axioms FX1Poly.Core.joinableModulo_symm

-- The generalized bridge: E below R-convertibility ⟹ CR modulo E
#assert_no_axioms FX1Poly.Core.equationalTheory_collapseInto

#assert_no_axioms FX1Poly.Core.churchRosserModulo_of_subconvertible

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
