import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeNativeUnionCanonicalForms

/-! # FX1PolyAudit/AuditHasTypeNativeUnionCanonicalForms — zero-axiom gate for NATIVE-38

Per-declaration `#assert_no_axioms` over every shipped decl of
`FX1Poly.Typed.HasTypeNativeUnionCanonicalForms`: the generator-containment substrate, the
head-stability pack, the lane-code/lane-value vocabulary with its pinning lemmas, the two table
peels, and the headline `HasTypeNativeUnion.closedNormalLaneCanonicalForms` master with its bool/nat
canonicity corollaries.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` is introduced
by this file. -/

open FX1Poly.Core FX1Poly.Typed

/-! ## Generator-containment substrate (`FX1Poly.Core`) -/

#assert_no_axioms FX1Poly.Core.RawTerm.containsGeneratorBool
#assert_no_axioms FX1Poly.Core.RawTermChildren.containGeneratorBool
#assert_no_axioms FX1Poly.Core.andProjectLeft
#assert_no_axioms FX1Poly.Core.andProjectRight
#assert_no_axioms FX1Poly.Core.orProjectLeftFalse
#assert_no_axioms FX1Poly.Core.orProjectRightFalse
#assert_no_axioms FX1Poly.Core.RawTerm.containsGeneratorBool_headHit
#assert_no_axioms FX1Poly.Core.RawTerm.containsGeneratorBool_children
#assert_no_axioms FX1Poly.Core.RawTermChildren.containGeneratorBool_head
#assert_no_axioms FX1Poly.Core.RawTermChildren.containGeneratorBool_tail
#assert_no_axioms FX1Poly.Core.RawTerm.isStepNormalFormBool_children
#assert_no_axioms FX1Poly.Core.RawTermChildren.areStepNormalFormsBool_head
#assert_no_axioms FX1Poly.Core.RawTermChildren.areStepNormalFormsBool_tail

/-! ## Head-stability pack (`FX1Poly.Typed`) -/

#assert_no_axioms FX1Poly.Typed.noStep_boolTypeCell
#assert_no_axioms FX1Poly.Typed.noStep_natTypeCell
#assert_no_axioms FX1Poly.Typed.noStep_unitCodeCell
#assert_no_axioms FX1Poly.Typed.noStep_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_boolTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_natTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_unitCodeCell
#assert_no_axioms FX1Poly.Typed.headReaches_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headReaches_optionTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_eitherTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_productTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_idTypeCell
#assert_no_axioms FX1Poly.Typed.headReaches_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.headReaches_listTypeCell
#assert_no_axioms FX1Poly.Typed.Conv.refutedByDistinctStableHeads

/-! ## Lane vocabulary -/

#assert_no_axioms FX1Poly.Typed.IsLaneCode
#assert_no_axioms FX1Poly.Typed.LaneValue
#assert_no_axioms FX1Poly.Typed.LaneValue.atBool
#assert_no_axioms FX1Poly.Typed.LaneValue.atNat
#assert_no_axioms FX1Poly.Typed.LaneValue.atOption
#assert_no_axioms FX1Poly.Typed.LaneValue.atEither
#assert_no_axioms FX1Poly.Typed.LaneValue.atProduct
#assert_no_axioms FX1Poly.Typed.LaneValue.atIdentity
#assert_no_axioms FX1Poly.Typed.LaneValue.atPi

/-! ## Lane refuters + pinning lemmas -/

#assert_no_axioms FX1Poly.Typed.IsLaneCode.refuteConvFromStableHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.notConvFromUniverse
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByBoolHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByNatHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByOptionHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByEitherHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByProductHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByIdentityHead
#assert_no_axioms FX1Poly.Typed.IsLaneCode.pinnedByPiHead

/-! ## Table peels -/

#assert_no_axioms FX1Poly.Typed.termIndexedFormerDescOf_outputIsUniverse
#assert_no_axioms FX1Poly.Typed.nativeRecursiveElimRuleOf_cases

/-! ## ★ The NATIVE-38 headline + corollaries -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.closedNormalLaneCanonicalForms
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.closedNormalBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.closedNormalNatCanonicalForms
