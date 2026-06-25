import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Conversion.ConvRenameEquivariance

/-! # FX1PolyAudit.Core.Rewriting.Conversion.ConvRenameEquivariance

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Conversion.ConvRenameEquivariance`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- STR-7: the Conv/NF renaming-EQUIVARIANCE bundle (ConvRenameEquivariance) — the two shipped halves
-- (preservation Conv.rename #370 + reflection Conv.reflectRename* #1167) assembled as iffs at the three
-- shapes the whnf-directed checker compares classifiers in (general Fin-injective / weaken / lift), plus
-- structural-normality invariance under EVERY renaming (Step.rename pushes a source step forward,
-- Step.reflectRename pulls an image step back — Bool case split, no excluded middle).
#assert_no_axioms FX1Poly.Core.Conv.rename_iff_ofFinInjective

#assert_no_axioms FX1Poly.Core.Conv.renameWeaken_iff

#assert_no_axioms FX1Poly.Core.Conv.renameLift_iff

#assert_no_axioms FX1Poly.Core.RawTerm.isStepNormalForm_rename_iff

end FX1PolyAudit
