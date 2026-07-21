import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Category.RestrictionWordProblem

/-! # Zero-axiom gate for the free restriction category word problem

Per-declaration zero-axiom gate for the restriction-category word-problem kit: the
Boolean and `Nat` micro-kit, decidable list equality, hand-rolled append laws, the guard
meet-semilattice (membership, subset, and set-equality with commutativity, idempotency,
absorption, and congruence), the restriction-morphism normal form `RcmMor` with the
combinator `rcmRestrict`, composition `rcmComp`, and well-formedness `rcmWfComp`, the R1-R4
restriction axioms and category laws sound on the normal form, the raw term calculus
`RcmTerm` with the generated congruence `RestrConv`, the decision `rcmDecideConv` with its
soundness `rcmConvDecides`, the guard-semilattice fragment completeness building blocks
(`rcmRestrIdem`, `rcmGuardSwap`, `rcmGuardContract`, `rcmGuardDup`), the capability and wall
markers, and the ground fires.

Full readback completeness is walled (`rcmHasFullReadbackCompleteness = false`); richer
restriction-category structure beyond the commutative-idempotent guard model, namely the deep
prefix-subsuming free restriction category and the Turing-category universal-object extension,
is walled (`rcmHasRicherRestrictionCategory = false`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmCondTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmCondFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmBoolAndElim
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmBoolAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmBoolOrInl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmBoolOrInr
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmListBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmListBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmListBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmAppendNil
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNilAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmAppendAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemBool
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemConsHead
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemConsTail
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemAppLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemAppRight
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemAppSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubset
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetConsElim
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetConsIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetWeakenRight
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetWeakenLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmMemOfSubset
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSubsetAppIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEq
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqElim
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqAppComm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqAppSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqApp
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmSetEqAppAbsorb
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmMor
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmMor.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmGen
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmComp
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmRestrict
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmWf
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmWfId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmWfGen
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmWfRestrict
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmWfComp
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmNfEquiv
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNfEquivRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNfEquivSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNfEquivTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNfEquivComp
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmNfEquivRestr
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmR1
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmR2
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmR3
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmR4
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmLeftId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmRightId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmTerm.gen
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmTerm.idTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmTerm.comp
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RcmTerm.restr
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmEval
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.compCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.restrCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.assoc
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.leftId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.rightId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.r1
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.r2
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.r3
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.RestrConv.r4
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmConvSound
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmDecideConv
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmConvDecides
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmGuardTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmRestrIdem
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmGuardSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmGuardContract
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmGuardDup
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmDecidesRestrictionCategoryWordProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmHasFullReadbackCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmHasRicherRestrictionCategory
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireRestrictGen
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireRestrictNotId
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireR1Decides
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireR1Nf
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireR2Decides
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireControlDistinctPaths
#assert_no_axioms FX1Poly.ComputerAlgebra.Category.rcmFireControlDistinctGuards

end FX1PolyAudit
