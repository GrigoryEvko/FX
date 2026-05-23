import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage.TargetImageTotality

/-! # AuditTerm.TargetImageTotality — target-direction wrapper axiom gates.

The 78 `partialStrengthenTyped?_isSome_target_<ctor>` wrappers in
`Term/StrengtheningImage/TargetImageTotality.lean` are the
target-direction typed image-totality leaves consumed by the eventual
universal driver feeding `Step.par.preserves_rename_image` (#2022
`unblock-B.t5.par`).  Each wrapper pulls the input typed term down to
its unique canonical-shape representative via the matching
`Term.<ctor>_unique` inversion, then consumes the dispatcher's
definitional reduction at the corresponding arm.

These gates lock the zero-axiom contract on the entire target-direction
fleet so any future regression flips a build-failing audit signal.
Companion source-direction `strengthenTyped?_rename_isSome_<ctor>`
wrappers are gated in `AuditTerm/StrengtheningImage.lean`. -/

namespace LeanFX2.Tools

-- Closed-atomic 0-IH wrappers (HEq unique → eq_of_heq → subst → rfl).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_unit
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_boolTrue
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_boolFalse
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_natZero
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_interval0
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_interval1

-- Single-recursive non-binder wrappers (one child IH, no type-side).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_natSucc
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_optionSome

-- Single-recursive wrappers with phantom-side type strengthening.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_eitherInl
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_eitherInr

-- Binary-recursive non-binder wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_listCons

-- Binary-recursive wrappers with binder-side secondType.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_pair

-- Type-preserving modal unary wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_modIntro
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_modElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_subsume

-- Single-recursive wrap (Ty.record).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_recordIntro

-- Binary-recursive with binder-side predicate.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_refineIntro

-- Binary-recursive with two type sides + mode hypothesis.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_glueIntro

-- Binary-recursive with single non-binder type side.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_codataUnfold

-- Sigma projection wrappers with existential secondType.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_fst
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_snd

-- Eliminator projections with single non-binder side.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_recordProj

-- Eliminator projection with binder-side predicate.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_refineElim

-- Function application wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_app
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_appPi

-- Codata destructor wrapper.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_codataDest

-- Interval algebra unary + binary wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_intervalOpp
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_intervalMeet
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_intervalJoin

-- Universe code with attributes (closed-atomic with attributes).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_universeCode

-- Closed-atomic with Ty+Raw sides.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_refl
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_oeqRefl

-- Session communication wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_sessionRecv
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_sessionSend

-- Cumulativity lift wrapper.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_cumulUp

-- Closed-atomic Ty-only sides.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivReflId

-- Closed-atomic Ty+Raw sides + universe attribute.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivReflIdAtId

-- funext-refl shape wrappers (2 Ty sides + lifted Raw side).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_funextRefl
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_funextReflAtId

-- Strict-id reflexivity wrapper.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_idStrictRefl

-- TypeCode binary-raw at back wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_arrowCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_productCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_sumCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_eitherCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivCode

-- TypeCode binary-raw with binder wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_piTyCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_sigmaTyCode

-- TypeCode single-raw wrappers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_listCode
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_optionCode

-- TypeCode ternary-raw wrapper.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_idCode

-- Parametric atomic wrappers (closed-atomic with element-type parameter).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_listNil
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_optionNone

-- Var wrapper (single-arm dispatch via Term.var_unique).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_var

-- Equivalence application wrappers (univalence-α and -β).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivApp
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivApply

-- Boolean elimination wrapper.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_boolElim

-- Natural-number eliminators.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_natElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_natRec

-- List/option/either match eliminators.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_listElim
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_optionMatch
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_eitherMatch

-- J recursors with phantom motiveType (idJ / oeqJ / idStrictRec).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_idJ
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_oeqJ
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_idStrictRec

-- Cubical destructors (modeIsUnivalent attribute).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_pathApp
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_glueElim

-- Cubical transport + homogeneous composition + path-shaped composition.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_transp
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_hcomp
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_hcompPath

-- Observational funext + heterogeneous equivalence + univalence intros.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_oeqFunext
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_equivIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_uaIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_funextIntroHet
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_uaToEquiv

-- Binders (lam / lamPi with parametric body IH at lifted strengthening).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_lam
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_lamPi

-- Path lambda binder (fixed-Ty.interval body).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_pathLam

-- Algebraic effect performance ctor with embedded carriers.
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_target_effectPerform

end LeanFX2.Tools
