import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation — zero-axiom gate (the three monad laws)

Per-declaration zero-axiom gate for the bespoke-free monad law carrier (POLY-TAB r6 S1): the three monad-law rows
over the already-shipped `MonadLawRel` and the non-vacuity row.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadLeftUnitRowGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRightUnitRowGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadAssocRowGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadAssocRowConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasLawRelationLeaf

end FX1PolyAudit
