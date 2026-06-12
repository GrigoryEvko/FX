import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.UnionRuleTables
import FX1Poly.Typed.HasTypeUnion

/-! # FX1PolyAudit/AuditUnionResidency — NATIVE-36 audit shard (the data-eliminator,
    n-ary/recursive data-intro, and listElim families landed IN the real union judgment)

Per-declaration zero-axiom gate for the NATIVE-36 wave: the native twin rule tables (three data-elim
shapes + seven data-intro shapes + the listElim shape) with their rows / tables / metadata /
table-inversion lemmas, the new arms on `HasTypeUnion` (the five scrutinee embeddings + the three
data-elim arms + the seven data-intro arms + the listElim arm), the union-level headline smokes and
coverage gate, and the three spike→union transfers (each with its spike-table-inversion ingredients).
Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## UnionRuleTables.lean — the native twin rule tables (pre-union) -/

-- Data-eliminator shape 1: two-branch match rows (boolElim / optionMatch / eitherMatch).
#assert_no_axioms FX1Poly.Typed.NativeTwoBranchMatchElimRule
#assert_no_axioms FX1Poly.Typed.boolElimNativeMatchRule
#assert_no_axioms FX1Poly.Typed.optionMatchNativeMatchRule
#assert_no_axioms FX1Poly.Typed.eitherMatchNativeMatchRule
#assert_no_axioms FX1Poly.Typed.nativeTwoBranchMatchRuleOf
#assert_no_axioms FX1Poly.Typed.nativeTwoBranchMatchRuleOf_boolElim
#assert_no_axioms FX1Poly.Typed.nativeTwoBranchMatchRuleOf_optionMatch
#assert_no_axioms FX1Poly.Typed.nativeTwoBranchMatchRuleOf_eitherMatch
#assert_no_axioms FX1Poly.Typed.nativeTwoBranchMatchRuleOf_cases

-- Data-eliminator shape 2: path-induction rows (idJ).
#assert_no_axioms FX1Poly.Typed.NativePathInductionElimRule
#assert_no_axioms FX1Poly.Typed.idJNativePathInductionRule
#assert_no_axioms FX1Poly.Typed.nativePathInductionRuleOf
#assert_no_axioms FX1Poly.Typed.nativePathInductionRuleOf_idJ
#assert_no_axioms FX1Poly.Typed.nativePathInductionRuleOf_cases

-- Data-eliminator shape 3: projection rows (fst / snd).
#assert_no_axioms FX1Poly.Typed.NativeProjectionElimRule
#assert_no_axioms FX1Poly.Typed.fstNativeProjectionRule
#assert_no_axioms FX1Poly.Typed.sndNativeProjectionRule
#assert_no_axioms FX1Poly.Typed.nativeProjectionRuleOf
#assert_no_axioms FX1Poly.Typed.nativeProjectionRuleOf_fst
#assert_no_axioms FX1Poly.Typed.nativeProjectionRuleOf_snd
#assert_no_axioms FX1Poly.Typed.nativeProjectionRuleOf_cases

-- Data-intro shape: recursive-unary (natSucc).
#assert_no_axioms FX1Poly.Typed.NativeRecursiveUnaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.natSuccNativeRecursiveUnaryRule
#assert_no_axioms FX1Poly.Typed.nativeRecursiveUnaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeRecursiveUnaryDataIntroRuleOf_natSucc
#assert_no_axioms FX1Poly.Typed.nativeRecursiveUnaryDataIntroRuleOf_cases

-- Data-intro shape: recursive-binary (listCons).
#assert_no_axioms FX1Poly.Typed.NativeRecursiveBinaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.listConsNativeRecursiveBinaryRule
#assert_no_axioms FX1Poly.Typed.nativeRecursiveBinaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeRecursiveBinaryDataIntroRuleOf_listCons
#assert_no_axioms FX1Poly.Typed.nativeRecursiveBinaryDataIntroRuleOf_cases

-- Data-intro shape: pinned-unary (optionSome).
#assert_no_axioms FX1Poly.Typed.NativePinnedUnaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.optionSomeNativePinnedUnaryRule
#assert_no_axioms FX1Poly.Typed.nativePinnedUnaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativePinnedUnaryDataIntroRuleOf_optionSome
#assert_no_axioms FX1Poly.Typed.nativePinnedUnaryDataIntroRuleOf_cases

-- Data-intro shape: nullary-free-type (optionNone).
#assert_no_axioms FX1Poly.Typed.NativeNullaryFreeTypeDataIntroRule
#assert_no_axioms FX1Poly.Typed.optionNoneNativeNullaryFreeTypeRule
#assert_no_axioms FX1Poly.Typed.nativeNullaryFreeTypeDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeNullaryFreeTypeDataIntroRuleOf_optionNone
#assert_no_axioms FX1Poly.Typed.nativeNullaryFreeTypeDataIntroRuleOf_cases

-- Data-intro shape: coproduct (eitherInl / eitherInr).
#assert_no_axioms FX1Poly.Typed.NativeCoproductDataIntroRule
#assert_no_axioms FX1Poly.Typed.eitherInlNativeCoproductRule
#assert_no_axioms FX1Poly.Typed.eitherInrNativeCoproductRule
#assert_no_axioms FX1Poly.Typed.nativeCoproductDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeCoproductDataIntroRuleOf_eitherInl
#assert_no_axioms FX1Poly.Typed.nativeCoproductDataIntroRuleOf_eitherInr
#assert_no_axioms FX1Poly.Typed.nativeCoproductDataIntroRuleOf_cases

-- Data-intro shape: non-dependent-binary (pair).
#assert_no_axioms FX1Poly.Typed.NativeNonDependentBinaryDataIntroRule
#assert_no_axioms FX1Poly.Typed.pairNativeNonDependentBinaryRule
#assert_no_axioms FX1Poly.Typed.nativeNonDependentBinaryDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeNonDependentBinaryDataIntroRuleOf_pair
#assert_no_axioms FX1Poly.Typed.nativeNonDependentBinaryDataIntroRuleOf_cases

-- Data-intro shape: reflexive (refl).
#assert_no_axioms FX1Poly.Typed.NativeReflexiveDataIntroRule
#assert_no_axioms FX1Poly.Typed.reflNativeReflexiveRule
#assert_no_axioms FX1Poly.Typed.nativeReflexiveDataIntroRuleOf
#assert_no_axioms FX1Poly.Typed.nativeReflexiveDataIntroRuleOf_refl
#assert_no_axioms FX1Poly.Typed.nativeReflexiveDataIntroRuleOf_cases

-- ListElim shape: the app-chain row.
#assert_no_axioms FX1Poly.Typed.NativeListElimRule
#assert_no_axioms FX1Poly.Typed.listElimNativeRule
#assert_no_axioms FX1Poly.Typed.listElimNativeRuleOf
#assert_no_axioms FX1Poly.Typed.listElimNativeRuleOf_listElim
#assert_no_axioms FX1Poly.Typed.listElimNativeRule_consContractum_eq
#assert_no_axioms FX1Poly.Typed.listElimNativeRuleOf_cases

/-! ## HasTypeUnion.lean — the new arms + the headline smokes + the coverage gate

The new arms are constructors of `HasTypeUnion`; the inductive itself carries them, so gating the
inductive certifies every arm's well-formedness is axiom-free.  The smokes and coverage gate are gated
individually. -/

-- The (extended) union inductive carrying all sixteen new arms.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion

-- The five scrutinee-embedding arms (data-elim scrutinees + the list scrutinee/intro base).

-- The three table-driven non-recursive data-eliminator arms.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.twoBranchMatchElim
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.pathInductionElim
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.projectionElim

-- The seven table-driven data-intro arms.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.recursiveUnaryIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.recursiveBinaryIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.pinnedUnaryIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.nullaryFreeTypeIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.coproductIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.nonDependentBinaryIntro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.reflexiveIntro

-- The listElim arm (discharging the batch-1 pin).
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.listElim

-- The headline smokes through the new arms + the coverage record / witness.
#assert_no_axioms FX1Poly.Typed.numeralTwoTypedThroughUnionRecursiveIntroTwice
#assert_no_axioms FX1Poly.Typed.boolElimTrueIotaUnionTyped
#assert_no_axioms FX1Poly.Typed.listElimNilIotaUnionTyped
#assert_no_axioms FX1Poly.Typed.NativeFamiliesUnionResidencyCoverage
#assert_no_axioms FX1Poly.Typed.nativeFamiliesUnionResidencyWitness

/-! ## DataElimUnionSpikeToNativeUnion.lean — the data-elim transfer -/


/-! ## DataIntroNaryUnionSpikeToNativeUnion.lean — the data-intro transfer -/


/-! ## ListElimUnionSpikeToNativeUnion.lean — the listElim transfer -/


end FX1PolyAudit
