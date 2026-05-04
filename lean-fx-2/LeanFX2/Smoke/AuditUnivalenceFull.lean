import LeanFX2.HoTT.UnivalenceFull

/-! # Smoke/AuditUnivalenceFull — Audit gates for HoTT/UnivalenceFull.

Verifies every shipped declaration in `HoTT/UnivalenceFull.lean`
audits zero-axiom under `#print axioms`.

## Scope

Every theorem, lemma, def shipped in `HoTT/UnivalenceFull.lean`:

* **§1 forward direction full-generality coherences** (7 decls):
  - `idToEquivMeta_isEquiv_invFun` (def)
  - `idToEquivMeta_eq_reflEquiv_atSelfPath` (theorem)
  - `idToEquivMeta_symm_symm_toFun` (theorem)
  - `idToEquivMeta_toFun_invFun_pointwise` (theorem)
  - `idToEquivMeta_invFun_toFun_pointwise` (theorem)
  - `idToEquivMeta_trans_toFun_pointwise` (theorem)
  - `idToEquivMeta_trans_invFun_pointwise` (theorem)
  - `idToEquivMeta_symm_full` (theorem)

* **§2 backward direction at the rfl-fragment** (3 decls):
  - `equivToIdMetaAtRefl` (def)
  - `equivToIdMetaAtRefl_const` (theorem)
  - `equivToIdMetaAtRefl_forgetful` (theorem)

* **§3 round-trip properties at refl** (4 decls):
  - `idToEquivMeta_equivToIdMetaAtRefl_anyPath` (theorem)
  - `idToEquivMeta_equivToIdMetaAtRefl_rfl` (theorem)
  - `equivToIdMetaAtRefl_idToEquivMeta_reflEquiv` (theorem)
  - `equivToIdMetaAtRefl_idToEquivMeta_anyEquiv` (theorem)

* **§4 kernel-meta correspondence** (1 decl):
  - `kernelMetaCorrespondence_atRefl` (theorem)

* **§5 funext forward direction** (4 decls):
  - `Funext.fnEqToPointwiseMeta` (def)
  - `Funext.fnEqToPointwiseMeta_refl` (theorem)
  - `Funext.fnEqToPointwiseMeta_symm` (theorem)
  - `Funext.fnEqToPointwiseMeta_trans` (theorem)

* **§6 funext backward at rfl-fragment** (3 decls):
  - `Funext.pointwiseMetaToFnEqAtRefl` (def)
  - `Funext.pointwiseMetaToFnEqAtRefl_const` (theorem)
  - `Funext.fnEqToPointwiseMeta_pointwiseToFnEqAtRefl_refl` (theorem)

* **§7 documentation theorem** (1 decl):
  - `kernelRflFragmentAlignsWithMeta` (theorem)

Total: ~23 zero-axiom shipped declarations.

## Audit gate format

Every `#print axioms <name>` MUST report:
```
'<name>' does not depend on any axioms
```

If any reports `propext`, `Quot.sound`, `Classical.choice`, `funext`
(Lean stdlib axiom), `Univalence` (recursive), or any user-declared
axiom, the corresponding declaration is NOT shipped — rewrite or
delete.
-/

namespace LeanFX2

/-! ## §1. Forward direction full-generality coherences. -/

#print axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_invFun
#print axioms LeanFX2.Univalence.idToEquivMeta_eq_reflEquiv_atSelfPath
#print axioms LeanFX2.Univalence.idToEquivMeta_symm_symm_toFun
#print axioms LeanFX2.Univalence.idToEquivMeta_toFun_invFun_pointwise
#print axioms LeanFX2.Univalence.idToEquivMeta_invFun_toFun_pointwise
#print axioms LeanFX2.Univalence.idToEquivMeta_trans_toFun_pointwise
#print axioms LeanFX2.Univalence.idToEquivMeta_trans_invFun_pointwise
#print axioms LeanFX2.Univalence.idToEquivMeta_symm_full

/-! ## §2. Backward direction at the rfl-fragment. -/

#print axioms LeanFX2.Univalence.equivToIdMetaAtRefl
#print axioms LeanFX2.Univalence.equivToIdMetaAtRefl_const
#print axioms LeanFX2.Univalence.equivToIdMetaAtRefl_forgetful

/-! ## §3. Round-trip properties at refl. -/

#print axioms LeanFX2.Univalence.idToEquivMeta_equivToIdMetaAtRefl_anyPath
#print axioms LeanFX2.Univalence.idToEquivMeta_equivToIdMetaAtRefl_rfl
#print axioms LeanFX2.Univalence.equivToIdMetaAtRefl_idToEquivMeta_reflEquiv
#print axioms LeanFX2.Univalence.equivToIdMetaAtRefl_idToEquivMeta_anyEquiv

/-! ## §4. Kernel-meta correspondence. -/

#print axioms LeanFX2.Univalence.kernelMetaCorrespondence_atRefl

/-! ## §5. Funext forward direction. -/

#print axioms LeanFX2.Funext.fnEqToPointwiseMeta
#print axioms LeanFX2.Funext.fnEqToPointwiseMeta_refl
#print axioms LeanFX2.Funext.fnEqToPointwiseMeta_symm
#print axioms LeanFX2.Funext.fnEqToPointwiseMeta_trans

/-! ## §6. Funext backward at rfl-fragment. -/

#print axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl
#print axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl_const
#print axioms LeanFX2.Funext.fnEqToPointwiseMeta_pointwiseToFnEqAtRefl_refl

/-! ## §7. Documentation theorem. -/

#print axioms LeanFX2.Univalence.kernelRflFragmentAlignsWithMeta

end LeanFX2
