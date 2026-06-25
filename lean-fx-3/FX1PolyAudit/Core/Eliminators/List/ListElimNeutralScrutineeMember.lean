import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.List.ListElimNeutralScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The neutral-scrutinee regime of the List recursor: the listElim mirror of the Nat regime, bringing the
-- three recursive recursors (natElim/natRec/listElim) to neutral-coverage parity.  A neutral scrutinee is never
-- a List constructor and stays neutral under Step, so listElim never iota-fires; the cell is a stuck neutral,
-- member of any candidate by memberOfStronglyNormalizingNeutral.  Discriminators
-- rootGenerator_ne_listNil/listCons + the triple-Acc cell-SN recursor (iota cases vacuous by neutrality).
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_listNil

#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_listCons

#assert_no_axioms FX1Poly.Core.listElim_neutralScrutinee_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.listElimNeutralScrutineeMember

end FX1PolyAudit
