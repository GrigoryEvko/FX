import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore
import LeanFX2.Term.StrengtheningImage.AggregatorSoundUnary
import LeanFX2.Term.StrengtheningImage.AggregatorSoundStructured
import LeanFX2.Term.StrengtheningImage.AggregatorSoundEliminators
import LeanFX2.Term.StrengtheningImage.AggregatorSoundCubical

/-! # Term/StrengtheningImage/AggregatorSoundUniversal

Universal aggregator-soundness theorem over typed terms.
-/

namespace LeanFX2

namespace Term

/-! ## Headline universal aggregator soundness

The universal headline `∀ sourceTerm, IsAggregatorSound sourceTerm`
composes the 78 per-arm `isAggregatorSound_<ctor>` wrappers via
structural induction on `Term`.  Every well-typed source term
satisfies the uniform aggregator-soundness predicate. -/

/-- HEADLINE: every typed Term satisfies `IsAggregatorSound`.

Proved by structural induction on `sourceTerm`, dispatching each
of the 78 constructor arms to its corresponding
`isAggregatorSound_<ctor>` wrapper.  Recursive children supply
their `IsAggregatorSound` certificate via the induction
hypothesis.

This unblocks the image theorem trio (right-inverse soundness,
totality, headline iff) and downstream `Step.eta` cascade
shipments per `extended-roadmap.md` Day 32. -/
theorem isAggregatorSound_universal {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) :
    IsAggregatorSound sourceTerm := by
  induction sourceTerm with
  -- 0-IH closed atomics (wrappers all-implicit)
  | var position => exact isAggregatorSound_var position
  | unit => exact isAggregatorSound_unit
  | boolTrue => exact isAggregatorSound_boolTrue
  | boolFalse => exact isAggregatorSound_boolFalse
  | natZero => exact isAggregatorSound_natZero
  | interval0 => exact isAggregatorSound_interval0
  | interval1 => exact isAggregatorSound_interval1
  -- 0-IH parametric atomics (wrapper takes explicit elementType)
  | listNil => exact isAggregatorSound_listNil _
  | optionNone => exact isAggregatorSound_optionNone _
  -- 0-IH HoTT atomics (wrappers all-implicit; ctor explicits ignored)
  | refl _ _ => exact isAggregatorSound_refl
  | oeqRefl _ _ => exact isAggregatorSound_oeqRefl
  | idStrictRefl _ _ _ => exact isAggregatorSound_idStrictRefl
  | equivReflId _ => exact isAggregatorSound_equivReflId
  -- 0-IH HoTT atomics (wrappers take explicit non-IH args)
  | funextRefl domainType codomainType applyRaw =>
      exact isAggregatorSound_funextRefl domainType codomainType applyRaw
  | equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      exact isAggregatorSound_equivReflIdAtId innerLevel innerLevelLt
        carrier carrierRaw
  | funextReflAtId domainType codomainType applyRaw =>
      exact isAggregatorSound_funextReflAtId domainType codomainType
        applyRaw
  | funextIntroHet domainType codomainType applyARaw applyBRaw =>
      exact isAggregatorSound_funextIntroHet domainType codomainType
        applyARaw applyBRaw
  -- 0-IH type codes (wrappers all take outerLevel + levelLe + raw forms)
  | arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_arrowCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_piTyCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_sigmaTyCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      exact isAggregatorSound_productCode outerLevel levelLe
        firstCodeRaw secondCodeRaw
  | sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      exact isAggregatorSound_sumCode outerLevel levelLe
        leftCodeRaw rightCodeRaw
  | listCode outerLevel levelLe elementCodeRaw =>
      exact isAggregatorSound_listCode outerLevel levelLe elementCodeRaw
  | optionCode outerLevel levelLe elementCodeRaw =>
      exact isAggregatorSound_optionCode outerLevel levelLe elementCodeRaw
  | eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      exact isAggregatorSound_eitherCode outerLevel levelLe
        leftCodeRaw rightCodeRaw
  | idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      exact isAggregatorSound_idCode outerLevel levelLe
        typeCodeRaw leftRaw rightRaw
  | equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      exact isAggregatorSound_equivCode outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw
  | universeCode innerLevel outerLevel cumulOk levelLe =>
      exact isAggregatorSound_universeCode innerLevel outerLevel
        cumulOk levelLe
  -- 1-IH non-binder (wrapper takes only IH)
  | natSucc _ ih => exact isAggregatorSound_natSucc ih
  | optionSome _ ih => exact isAggregatorSound_optionSome ih
  | modIntro _ ih => exact isAggregatorSound_modIntro ih
  | modElim _ ih => exact isAggregatorSound_modElim ih
  | subsume _ ih => exact isAggregatorSound_subsume ih
  | eitherInl _ ih => exact isAggregatorSound_eitherInl ih
  | eitherInr _ ih => exact isAggregatorSound_eitherInr ih
  | recordIntro _ ih => exact isAggregatorSound_recordIntro ih
  | recordProj _ ih => exact isAggregatorSound_recordProj ih
  | refineElim _ ih => exact isAggregatorSound_refineElim ih
  | fst _ ih => exact isAggregatorSound_fst ih
  | snd _ ih => exact isAggregatorSound_snd ih
  | intervalOpp _ ih => exact isAggregatorSound_intervalOpp ih
  | codataDest _ ih => exact isAggregatorSound_codataDest ih
  | sessionRecv _ ih => exact isAggregatorSound_sessionRecv ih
  -- 1-IH cumulUp (5 explicit non-IH params)
  | cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh _ ih =>
      exact isAggregatorSound_cumulUp lowerLevel higherLevel
        cumulMonotone levelLeLow levelLeHigh ih
  -- 1-IH uaToEquiv (6 explicit non-IH params + 1 IH)
  | uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw rightTyRaw _ ih =>
      exact isAggregatorSound_uaToEquiv innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw ih
  -- 1-IH glueElim (1 modeIsUnivalent + 1 IH)
  | glueElim _ _ ih => exact isAggregatorSound_glueElim ih
  -- 2-IH non-binder (wrappers all take 2 IHs)
  | pair _ _ ih1 ih2 => exact isAggregatorSound_pair ih1 ih2
  | listCons _ _ ih1 ih2 => exact isAggregatorSound_listCons ih1 ih2
  | app _ _ ih1 ih2 => exact isAggregatorSound_app ih1 ih2
  | appPi _ _ ih1 ih2 => exact isAggregatorSound_appPi ih1 ih2
  | intervalMeet _ _ ih1 ih2 => exact isAggregatorSound_intervalMeet ih1 ih2
  | intervalJoin _ _ ih1 ih2 => exact isAggregatorSound_intervalJoin ih1 ih2
  | codataUnfold _ _ ih1 ih2 => exact isAggregatorSound_codataUnfold ih1 ih2
  | refineIntro predicate _ _ ih1 ih2 =>
      exact isAggregatorSound_refineIntro predicate ih1 ih2
  | idJ _ _ ih1 ih2 => exact isAggregatorSound_idJ ih1 ih2
  | oeqJ _ _ ih1 ih2 => exact isAggregatorSound_oeqJ ih1 ih2
  | idStrictRec _ _ _ ih1 ih2 => exact isAggregatorSound_idStrictRec ih1 ih2
  | oeqFunext _ _ _ _ _ ih => exact isAggregatorSound_oeqFunext ih
  | sessionSend protocolStep _ _ ih1 ih2 =>
      exact isAggregatorSound_sessionSend protocolStep ih1 ih2
  | equivApp _ _ ih1 ih2 => exact isAggregatorSound_equivApp ih1 ih2
  | equivApply _ _ ih1 ih2 => exact isAggregatorSound_equivApply ih1 ih2
  -- 1-IH uaIntroHet (4 explicit non-IH params + 1 IH)
  | uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw _ ih =>
      exact isAggregatorSound_uaIntroHet innerLevel innerLevelLt
        carrierARaw carrierBRaw ih
  -- 4-IH equivIntroHet (4 Term children)
  | equivIntroHet _ _ _ _ ih1 ih2 ih3 ih4 =>
      exact isAggregatorSound_equivIntroHet ih1 ih2 ih3 ih4
  -- 3-IH eliminators
  | boolElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_boolElim ih1 ih2 ih3
  | natElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_natElim ih1 ih2 ih3
  | natRec _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_natRec ih1 ih2 ih3
  | listElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_listElim ih1 ih2 ih3
  | optionMatch _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_optionMatch ih1 ih2 ih3
  | eitherMatch _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_eitherMatch ih1 ih2 ih3
  -- Effect performance (wrapper only takes canPerformOperation + 2 IH; rest implicit)
  | effectPerform _ _ _ canPerformOperation _ _ ih1 ih2 =>
      exact isAggregatorSound_effectPerform canPerformOperation ih1 ih2
  -- Binders (1-IH body)
  | lam _ ih => exact isAggregatorSound_lam ih
  | lamPi _ ih => exact isAggregatorSound_lamPi ih
  -- Cubical binders/builders (with mode/carrier/endpoint metadata)
  | pathLam modeIsUnivalent _ _ _ _ ih =>
      exact isAggregatorSound_pathLam (modeIsUnivalent := modeIsUnivalent)
        (bodyAggregator := ih)
  | pathApp modeIsUnivalent _ _ ih1 ih2 =>
      exact isAggregatorSound_pathApp (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | glueIntro modeIsUnivalent _ _ _ _ ih1 ih2 =>
      exact isAggregatorSound_glueIntro (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw _ _ ih1 ih2 =>
      exact isAggregatorSound_transp (modeIsUnivalent := modeIsUnivalent)
        universeLevel universeLevelLt sourceType targetType
        sourceTypeRaw targetTypeRaw ih1 ih2
  | hcomp modeIsUnivalent _ _ ih1 ih2 =>
      exact isAggregatorSound_hcomp (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | hcompPath modeIsUnivalent leftEndpoint rightEndpoint _ _ ih1 ih2 =>
      exact isAggregatorSound_hcompPath (modeIsUnivalent := modeIsUnivalent)
        leftEndpoint rightEndpoint ih1 ih2

end Term

end LeanFX2
