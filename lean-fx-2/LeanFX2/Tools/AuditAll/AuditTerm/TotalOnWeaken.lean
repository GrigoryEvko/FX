import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage

/-! # AuditTerm.TotalOnWeaken — weaken-image totality gates. -/

namespace LeanFX2.Tools

-- BIG-ASS THEOREM (closed-atomic foundation): `IsTotalOnWeaken`
-- predicate and the 7 closed-atomic ctor totality witnesses.  Each
-- atomic case shipped as a direct `rfl` proof both at the
-- `(strengthenTyped? (Term.weaken nt _)).isSome` level and at the
-- user-facing `unweaken?_weaken_<ctor>` level.  The recursive 71
-- ctors land in a follow-up via `IsTotalOnWeaken`'s composition rule.

#assert_no_axioms LeanFX2.Term.IsTotalOnWeaken

#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_unit
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolTrue
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolFalse
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natZero
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_interval0
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_interval1
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_var

-- True 0-IH parametric atomic: universeCode (no scope-indexed payload).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_universeCode

-- 1-IH non-binder ctor totality (compositional rules — natSucc and
-- intervalOpp as canonical templates; remaining 13 single-IH ctors
-- follow the same unfold + split + ▸ pattern).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natSucc
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalOpp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionSome
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_modIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_modElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_subsume
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_cumulUp

-- Wave A: parametric atomic 0-IH ctors (no Term IH; sub-payloads
-- strengthen via Ty.strengthen?_weaken / RawTerm.strengthen?_weaken).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listNil
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionNone
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqRefl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idStrictRefl

-- Wave A.2: universe-code 0-IH ctors (only outer-scope RawTerm payloads).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_arrowCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_productCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sumCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivCode

-- Wave B.1: 1-IH non-binder ctors (single Term recursion + zero or
-- more Ty/RawTerm payloads).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_recordIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_recordProj
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherInl
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherInr
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sessionRecv
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_codataDest

-- Wave C.1: 2-IH non-binder ctors.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listCons
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalMeet
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_intervalJoin
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_app
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_codataUnfold
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sessionSend

-- Wave C.2: more 2-IH non-binder ctors + 3-IH identity-elimination
-- ctors (idJ, oeqJ, idStrictRec) with carrier+leftEndpoint+rightEndpoint
-- + baseCase + witness chains.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivApp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivApply
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idJ
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqJ
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_idStrictRec

-- Wave D: cubical / HoTT non-binder ctors.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivReflId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_glueElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_hcomp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_glueIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_transp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_uaToEquiv
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_pathApp
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_hcompPath
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_uaIntroHet

-- Wave E: eliminator ctors (3-IH non-binder pattern).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_natRec
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_listElim
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_optionMatch
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_eitherMatch

-- Wave F: effects ctor (operation signature carrier strengthening
-- via OperationSignature.map definitional unfolding).
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_effectPerform

-- Wave G: lift-based universe-code ctors (codomain at scope+1).
-- Use the lift-after-lift composition (lift_dropNewest_weaken_lift)
-- + RawTerm.partialStrengthen?_rename_some + rename_identity.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_piTyCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_sigmaTyCode
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_fst
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refineIntro
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_refineElim

-- Wave H: HoTT canonical-witness ctors with scope+1 applyRaw payloads.
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextReflAtId
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextIntroHet

-- Wave I: Eq.mpr-blocked ctor totality via weaken_<ctor>_eq + cast invariance.
-- These ctors' Term.rename arms wrap the constructed value in (eq).symm ▸ ...
-- which blocks the standard unfold+split template; resolved via per-ctor
-- rewrite lemmas + strengthenTyped?_isSome_castInvariant.
#assert_no_axioms LeanFX2.Term.strengthenTyped?_isSome_castInvariant
#assert_no_axioms LeanFX2.Term.weaken_snd_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_snd
#assert_no_axioms LeanFX2.Term.weaken_funextRefl_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_funextRefl
#assert_no_axioms LeanFX2.Term.weaken_appPi_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_appPi
#assert_no_axioms LeanFX2.Term.weaken_pair_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_pair
#assert_no_axioms LeanFX2.Term.weaken_oeqFunext_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_oeqFunext
#assert_no_axioms LeanFX2.Term.weaken_equivIntroHet_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_equivIntroHet
#assert_no_axioms LeanFX2.Term.weaken_boolElim_unfolds
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_boolElim

-- User-facing unweaken?_weaken_<ctor> headline theorems.  Each is a
-- direct `rfl` witness — concrete totality for the closed atomic
-- ctors, consumable by Step.eta-cascade SR proofs.
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_unit
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_boolTrue
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_boolFalse
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_natZero
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_interval0
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_interval1
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_var
#assert_no_axioms LeanFX2.Term.unweaken?_weaken_universeCode

-- Genuine (non-tautological) iff for the closed-atomic unit case.
-- Augments the existing tautological iff with concrete totality
-- content on a closed source.
#assert_no_axioms LeanFX2.Term.weaken_image_iff_strengthenTyped?_some_TRUE_unit

end LeanFX2.Tools
