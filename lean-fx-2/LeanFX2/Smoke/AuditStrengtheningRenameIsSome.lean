import LeanFX2.Term.StrengtheningImage

/-! # Smoke/AuditStrengtheningRenameIsSome

Reviewer-facing `#print axioms` gate for the per-arm
`Term.strengthenTyped?_rename_isSome[_<ctor>[_of_childIsSome]]`
family — 101 zero-axiom dispatcher arms covering every Term
ctor's renaming-image strengthening proof.

Per the renaming-image API (T1 / #1952 / `RenameImageInterface`):
each arm shows that under an injective renaming, the typed
strengthening dispatcher returns `some` whenever any structurally
required child sub-strengthening returns `some` (or
unconditionally for 0-IH closed-atomic ctors).

Three sub-families:

* **Headlines** (2): the universal `_rename_isSome` totality lemma
  and `_rename_some` existence form;
* **Atomic-0-IH** (15): closed-type and HoTT-atomic ctors whose
  arms succeed unconditionally (var / unit / boolTrue / boolFalse /
  natZero / interval0 / interval1 / universeCode / listNil /
  optionNone / equivReflId / refl / oeqRefl / idStrictRefl /
  equivReflIdAtId);
* **1-IH `_of_childIsSome`** (23): unary and elimination ctors
  whose arms succeed given a child witness;
* **Plain 1+IH ctors** (61): the same arms re-exported without
  the `_of_childIsSome` suffix, dispatching from explicit
  intermediate results.

Each entry mirrors `Tools/AuditAll/AuditTerm/StrengtheningImage.lean:
52-154` and must report "does not depend on any axioms" — strict
Layer K gate. -/

namespace LeanFX2.Smoke.AuditStrengtheningRenameIsSome

-- Headlines.
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_some

-- Atomic-0-IH closed-type and HoTT-atomic ctors.
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_var
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_unit
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolTrue
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolFalse
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natZero
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_interval0
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_interval1
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_universeCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listNil
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionNone
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivReflId
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refl
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqRefl
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idStrictRefl
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivReflIdAtId

-- `_of_childIsSome` arms for 1-IH ctors (witness-gated).
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natSucc_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalOpp_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modIntro_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modElim_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_subsume_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionSome_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInl_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInr_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionRecv_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_cumulUp_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordProj_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataDest_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordIntro_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueElim_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCons_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natElim_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natRec_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_app_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listElim_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionMatch_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherMatch_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalMeet_of_childIsSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalJoin_of_childIsSome

-- Plain ctor arms (1-IH unary).
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natSucc
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalOpp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modIntro
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_modElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_subsume
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionSome
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInl
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherInr
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionRecv
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_cumulUp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordProj
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataDest
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_recordIntro
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCons
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_natRec
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_app
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionMatch
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherMatch
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalMeet
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_intervalJoin

-- Type-code ctors.
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_listCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_optionCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_arrowCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sumCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_productCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_eitherCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_piTyCode
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sigmaTyCode

-- HoTT eliminators and cubical β.
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idJ
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqJ
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_idStrictRec
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_hcomp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextReflAtId
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refineIntro
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_refineElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_sessionSend
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivApp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_fst
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_codataUnfold
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivApply
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_uaToEquiv
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_uaIntroHet
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextIntroHet
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_funextRefl

-- Binders and parametric multi-IH ctors.
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_appPi
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_snd
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pair
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_lam
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_lamPi
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pathLam
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_oeqFunext
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_equivIntroHet
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_boolElim
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_transp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_hcompPath
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_glueIntro
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_pathApp
#print axioms LeanFX2.Term.strengthenTyped?_rename_isSome_effectPerform

end LeanFX2.Smoke.AuditStrengtheningRenameIsSome
