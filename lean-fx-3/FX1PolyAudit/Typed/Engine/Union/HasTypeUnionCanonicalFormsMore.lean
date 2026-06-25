import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms

/-! # FX1PolyAudit/Typed/Engine/Union/HasTypeUnionCanonicalFormsMore — zero-axiom gate for NATIVE-38 (Core half)

Per-declaration `#assert_no_axioms` over the `FX1Poly.Core` generator-containment substrate that
`FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms` stands on: the `containsGeneratorBool` /
`containGeneratorBool` walkers, the boolean `and`/`or` projection helpers, and the step-normal-form
children reflections.  The typed head-stability / lane / headline decls live in the sibling
`HasTypeUnionCanonicalForms` shard; split out to keep each audit shard under the eval ceiling.

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
