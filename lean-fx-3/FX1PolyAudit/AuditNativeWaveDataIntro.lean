import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.DataIntroNaryUnionSpike

/-! # FX1PolyAudit/AuditNativeWaveDataIntro — NATIVE-34 zero-axiom gate

Per-declaration `#assert_no_axioms` gate for the n-ary + recursive data-constructor introduction rows
(`FX1Poly.Typed.DataIntroNaryUnionSpike`): the six telescope-shaped rule tables, their metadata
lookups, the spike judgment's bespoke→spike adequacy maps (premise parity — the fold's
delete-safety), the headline numeral-`2`-through-the-recursive-row-twice smoke, the closed-`cons`
recursive-binary smoke, the per-row closed-witness smokes, and the coverage verdict.

Every shipped declaration is asserted free of `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical.choice`, `native_decide`, `omega`.  The tables are `if`-then-`else` over
`DecidableEq Generator` (rfl on the diagonal); the spike is a strictly-positive inductive (engine
embeddings + recursive table arms); the adequacy is `induction` (recursive engines) / `cases`
(non-recursive engines) over the bespoke arms with `rfl` row-lookups. -/

-- The telescope-shaped rule structures and the spike judgment (pure-data inductives).
#assert_no_axioms FX1Poly.Typed.RecursiveUnaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.RecursiveBinaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.PinnedUnaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.CoproductDataIntroRule
#assert_no_axioms FX1Poly.Typed.NonDependentBinaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.NullaryFreeTypeDataIntroRule
#assert_no_axioms FX1Poly.Typed.ReflexiveDataIntroRule
#assert_no_axioms FX1Poly.Typed.DataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.DataIntroNaryCoverage

-- The per-generator rule rows and tables + their metadata lookups.
#assert_no_axioms FX1Poly.Typed.natSuccRecursiveUnaryRule
#assert_no_axioms FX1Poly.Typed.recursiveUnaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.recursiveUnaryDataIntroRuleOf_natSucc
#assert_no_axioms FX1Poly.Typed.listConsRecursiveBinaryRule
#assert_no_axioms FX1Poly.Typed.recursiveBinaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.recursiveBinaryDataIntroRuleOf_listCons
#assert_no_axioms FX1Poly.Typed.optionSomePinnedUnaryRule
#assert_no_axioms FX1Poly.Typed.pinnedUnaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.pinnedUnaryDataIntroRuleOf_optionSome
#assert_no_axioms FX1Poly.Typed.eitherInlCoproductRule
#assert_no_axioms FX1Poly.Typed.eitherInrCoproductRule
#assert_no_axioms FX1Poly.Typed.coproductDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.coproductDataIntroRuleOf_eitherInl
#assert_no_axioms FX1Poly.Typed.coproductDataIntroRuleOf_eitherInr
#assert_no_axioms FX1Poly.Typed.pairNonDependentBinaryRule
#assert_no_axioms FX1Poly.Typed.nonDependentBinaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nonDependentBinaryDataIntroRuleOf_pair
#assert_no_axioms FX1Poly.Typed.optionNoneNullaryFreeTypeRule
#assert_no_axioms FX1Poly.Typed.nullaryFreeTypeDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nullaryFreeTypeDataIntroRuleOf_optionNone
#assert_no_axioms FX1Poly.Typed.reflReflexiveRule
#assert_no_axioms FX1Poly.Typed.reflexiveDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.reflexiveDataIntroRuleOf_refl

-- The per-family bespoke→spike adequacy maps (premise parity / delete-safety).
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.toDataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.toDataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.toDataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescPairIntro.toDataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.toDataIntroNaryUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdIntro.toDataIntroNaryUnionSpike

-- The headline numeral-2-through-the-recursive-row-twice smoke + the recursive-binary cons smoke.
#assert_no_axioms FX1Poly.Typed.numeralTwoTypedThroughRecursiveRowTwice
#assert_no_axioms FX1Poly.Typed.closedListConsTypedThroughRecursiveRow

-- The per-row closed-witness smokes.
#assert_no_axioms FX1Poly.Typed.pairTypedThroughNonDependentBinaryRow
#assert_no_axioms FX1Poly.Typed.eitherInlTypedThroughCoproductRow
#assert_no_axioms FX1Poly.Typed.optionSomeTypedThroughPinnedUnaryRow
#assert_no_axioms FX1Poly.Typed.optionNoneTypedThroughNullaryFreeTypeRow
#assert_no_axioms FX1Poly.Typed.reflTypedThroughReflexiveRow

-- The coverage verdict gate.
#assert_no_axioms FX1Poly.Typed.dataIntroNaryCoverageWitness
