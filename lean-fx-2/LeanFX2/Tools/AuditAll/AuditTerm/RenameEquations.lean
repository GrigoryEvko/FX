import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PartialStrengthen

/-! # AuditTerm.RenameEquations — strength-T1 rename equation gates. -/

namespace LeanFX2.Tools

-- strength-T1: per-ctor renaming-image dispatcher equations.
-- Closed-atomic (7): unit / boolTrue / boolFalse / natZero / interval0 /
-- interval1 / universeCode.  Each closes by `rfl`.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_unit
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_boolTrue
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_boolFalse
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natZero
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_interval0
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_interval1
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_universeCode
-- strength-T1 parametric-atomic (7): subst-via-witness pattern.  Each
-- ctor with Ty (or Ty + RawTerm) payload but no Term children — the
-- dispatcher's match-with-binding is unblocked by `subst`-ing the
-- propositional equality between the bound witness and the original
-- (derived from `Ty.partialStrengthen?_rename_some` / `Ty.rename_identity`
-- and their raw companions).
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listNil
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionNone
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivReflId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_oeqRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idStrictRefl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivReflIdAtId
-- strength-T1 1-IH non-binder atomic: subst-via-witness on inner Term IH.
-- Each ctor wraps a single Term sub-result (optionally with Ty / RawTerm
-- payloads, or value-level data) via the partialStrengthenTyped helpers'
-- match-then-construct shape.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natSucc
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalOpp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_modIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_modElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_subsume
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionSome
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherInl
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherInr
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sessionRecv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_cumulUp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_recordProj
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_codataDest
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_recordIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_glueElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listCons
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_natRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_app
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherMatch
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_oeqJ
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idStrictRec
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalMeet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_intervalJoin
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_hcomp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_listCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_optionCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_arrowCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sumCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_productCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_eitherCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_idCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_piTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sigmaTyCode
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_funextReflAtId
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refineIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_refineElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_sessionSend
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_transp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_hcompPath
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_glueIntro
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_pathApp
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_codataUnfold
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_fst
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_equivApply
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_uaToEquiv
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_uaIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_funextIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_eq_effectPerform

-- strength-T1 cast-invariance helper lemmas used to peel Eq.mpr casts in
-- the 11 cast-wrapped ctors (lam, lamPi, appPi, snd, pair, boolElim,
-- pathLam, oeqFunext, funextRefl, equivIntroHet, var).
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_isSome_castInvariant
#assert_no_axioms LeanFX2.Term.partialStrengthenTyped?_castInvariantHEq
#assert_no_axioms LeanFX2.Term.termTypeCastHEq
#assert_no_axioms LeanFX2.Term.rename_oeqFunext_unfolds

-- strength-T1 cast-wrapped ctors (HEq-form pivot — Eq-form structurally
-- blocked because the named cast equations like funextReflType_rename are
-- non-rfl, so `cases castProof` fails past Eq.mpr ▸).  Pivot ships as HEq
-- via partialStrengthenTyped?_castInvariantHEq; downstream consumers bridge
-- HEq → Eq via the named cast equation when needed.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_var
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_appPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_snd
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_pair
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_lam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_lamPi
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_pathLam
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_oeqFunext
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_equivIntroHet
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_boolElim
#assert_no_axioms LeanFX2.Term.strengthenTyped?_rename_heq_funextRefl

end LeanFX2.Tools
