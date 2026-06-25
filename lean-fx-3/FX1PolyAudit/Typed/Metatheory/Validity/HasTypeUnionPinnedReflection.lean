import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionPinnedReflection

/-! # FX1PolyAudit/AuditHasTypeUnionPinnedReflection — the union fibration reflection leg zero-axiom gate

Per-declaration zero-axiom gate for `FX1Poly/Typed/Metatheory/Validity/HasTypeUnionPinnedReflection.lean`:
the union renaming-reflection condition machinery, the host (`HasTypeDescPi`) reflection wrapper via the
shipped premise-free host master, the native re-pin (`HasTypeUnion.retypeAtUniverseReflect`), the
universe-code-pinned union reflection master (`conv` recurses; `var` + `universeFormation` reflect NATIVELY
via the re-pin; only `ofGrown` still routes through the host master; the three table-driven arms via
`UnionTableReflectionResidual`), and the strengthening corollary.  Every declaration below must be free of
`propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The reflection condition machinery.
#assert_no_axioms FX1Poly.Typed.UnionRenameReflectsContext
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.RenameRespectsContext.toUnionReflects
#assert_no_axioms FX1Poly.Typed.UnionRenameReflectsContext.toContextReflectsRename
#assert_no_axioms FX1Poly.Typed.UnionRenameReflectsContext.ofWeakenCons

-- The host reflection engine (the `ofGrown` arm), via the shipped premise-free host master.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.retypeAtUniverseReflect
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reflectsRenamePinned

-- The native re-pin (the union twin of the host `retypeAtUniverseReflect`), consumed by the var/universe arms.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.retypeAtUniverseReflect

-- The universe-code-pinned union reflection conclusion + the residual structure + the master.
#assert_no_axioms FX1Poly.Typed.UnionReflectsAtUniverse
#assert_no_axioms FX1Poly.Typed.UnionTableReflectionResidual
#assert_no_axioms FX1Poly.Typed.flatFormationReflects
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.reflectsRenameAtUniverse

-- The strengthening corollary (the un-weakening leg at a universe code).
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.strengthenAtUniverse

end FX1PolyAudit
