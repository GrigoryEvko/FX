import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Sconing.SconingSNObjectUnique

/-! # FX1PolyAudit.Core.Metatheory.Sconing.SconingSNObjectUnique

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Sconing.SconingSNObjectUnique`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Generalization of the cross-leg triangulation to the WHOLE class of SN-scones: IsStronglyNormalizing is a
-- Prop, so by definitional proof irrelevance any two sconing witnesses extract the IDENTICAL SN proof
-- (sconingSN_objectUnique), hence any SN-scone's extracted SN IS the Tait CR1∘fundamental witness
-- (anySconingSN_eq_taitComposition), recovering sconingSN_eq_taitComposition as an instance
-- (sconingSN_eq_taitComposition_ofGeneral).  No sconing construction is an independent SN object — the cell is
-- bridgedToTait by theorem; independence can only live in the `computable` predicate, which is STC-blocked.
#assert_no_axioms FX1Poly.Core.sconingSN_objectUnique

#assert_no_axioms FX1Poly.Core.anySconingSN_eq_taitComposition

#assert_no_axioms FX1Poly.Core.sconingSN_eq_taitComposition_ofGeneral

end FX1PolyAudit
