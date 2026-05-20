import LeanFX2.Term.RenameInjective.ConstructorFamilies

/-! # Term/RenameInjective/BinderInversions

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

private theorem rawTerm_ne_refl_self
    {scope : Nat} (sourceRaw : RawTerm scope) :
    sourceRaw ≠ RawTerm.refl sourceRaw := by
  intro rawEq
  induction sourceRaw with
  | var position => cases rawEq
  | unit => cases rawEq
  | lam body bodyIH => cases rawEq
  | app functionTerm argumentTerm functionIH argumentIH => cases rawEq
  | pair firstValue secondValue firstIH secondIH => cases rawEq
  | fst pairTerm pairIH => cases rawEq
  | snd pairTerm pairIH => cases rawEq
  | boolTrue => cases rawEq
  | boolFalse => cases rawEq
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      cases rawEq
  | natZero => cases rawEq
  | natSucc predecessor predecessorIH => cases rawEq
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      cases rawEq
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      cases rawEq
  | listNil => cases rawEq
  | listCons headTerm tailTerm headIH tailIH => cases rawEq
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      cases rawEq
  | optionNone => cases rawEq
  | optionSome valueTerm valueIH => cases rawEq
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      cases rawEq
  | eitherInl valueTerm valueIH => cases rawEq
  | eitherInr valueTerm valueIH => cases rawEq
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      cases rawEq
  | refl rawWitness witnessIH =>
      exact witnessIH (by injection rawEq)
  | idJ baseCase witness baseIH witnessIH => cases rawEq
  | modIntro raw rawIH => cases rawEq
  | modElim raw rawIH => cases rawEq
  | subsume raw rawIH => cases rawEq
  | interval0 => cases rawEq
  | interval1 => cases rawEq
  | intervalOpp intervalTerm intervalIH => cases rawEq
  | intervalMeet leftInterval rightInterval leftIH rightIH => cases rawEq
  | intervalJoin leftInterval rightInterval leftIH rightIH => cases rawEq
  | pathLam body bodyIH => cases rawEq
  | pathApp pathTerm intervalArg pathIH intervalIH => cases rawEq
  | glueIntro baseValue partialValue baseIH partialIH => cases rawEq
  | glueElim gluedValue gluedIH => cases rawEq
  | transp path source pathIH sourceIH => cases rawEq
  | hcomp sides cap sidesIH capIH => cases rawEq
  | oeqRefl witness witnessIH => cases rawEq
  | oeqJ baseCase witness baseIH witnessIH => cases rawEq
  | oeqFunext pointwiseEquality pointwiseIH => cases rawEq
  | idStrictRefl witness witnessIH => cases rawEq
  | idStrictRec baseCase witness baseIH witnessIH => cases rawEq
  | equivIntro forwardFn backwardFn forwardIH backwardIH => cases rawEq
  | equivApp equivTerm argument equivIH argumentIH => cases rawEq
  | refineIntro rawValue predicateProof valueIH proofIH => cases rawEq
  | refineElim refinedValue refinedIH => cases rawEq
  | recordIntro firstField fieldIH => cases rawEq
  | recordProj recordValue recordIH => cases rawEq
  | codataUnfold initialState transition initialIH transitionIH => cases rawEq
  | codataDest codataValue codataIH => cases rawEq
  | sessionSend channel payload channelIH payloadIH => cases rawEq
  | sessionRecv channel channelIH => cases rawEq
  | effectPerform operationTag arguments tagIH argumentsIH => cases rawEq
  | universeCode innerLevel => cases rawEq
  | arrowCode domainCode codomainCode domainIH codomainIH => cases rawEq
  | piTyCode domainCode codomainCode domainIH codomainIH => cases rawEq
  | sigmaTyCode domainCode codomainCode domainIH codomainIH => cases rawEq
  | productCode firstCode secondCode firstIH secondIH => cases rawEq
  | sumCode leftCode rightCode leftIH rightIH => cases rawEq
  | listCode elementCode elementIH => cases rawEq
  | optionCode elementCode elementIH => cases rawEq
  | eitherCode leftCode rightCode leftIH rightIH => cases rawEq
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH => cases rawEq
  | equivCode leftTypeCode rightTypeCode leftIH rightIH => cases rawEq
  | cumulUpMarker innerCodeRaw innerIH => cases rawEq
  | uaToEquiv proofRaw proofIH => cases rawEq
  | equivApply equivRaw argRaw equivIH argIH => cases rawEq
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH => cases rawEq
  | idToEquiv proofRaw proofIH => cases rawEq
  | oeqTrans firstProof secondProof firstIH secondIH => cases rawEq
  | equivCompose firstEquiv secondEquiv firstIH secondIH => cases rawEq
  | transpFill pathTy currentInterval source pathIH intervalIH sourceIH =>
      cases rawEq

private theorem renamedLamPi_ne_renamedFunextReflCast
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (baseCodomain : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (bodyRawEq : bodyRaw = RawTerm.refl applyRaw)
    (codomainEq :
      codomainType = Ty.id baseCodomain.weaken applyRaw applyRaw) :
    HEq
      (Term.rename termRenaming (Term.lamPi bodyTerm))
      (Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx) domainType baseCodomain
          applyRaw)) →
      False := by
  intro renameHEq
  cases bodyRawEq
  cases codomainEq
  dsimp only [Term.rename] at renameHEq
  have uncastHEq :
      HEq
        (Term.lamPi (Term.rename (termRenaming.lift domainType) bodyTerm))
        (Term.funextRefl (context := targetCtx)
          (domainType.rename rho) (baseCodomain.rename rho)
          (applyRaw.rename rho.lift)) :=
    HEq.trans renameHEq
      (termRenameInjectiveCastHEq
        (funextReflType_rename rho domainType baseCodomain applyRaw).symm
        (Term.funextRefl (context := targetCtx)
          (domainType.rename rho) (baseCodomain.rename rho)
          (applyRaw.rename rho.lift)))
  exact
    Term.noConfusion (P := False) rfl rfl rfl HEq.rfl
      (by
        unfold funextReflType
        dsimp only [Ty.rename]
        exact
          heq_of_eq
            (congrArg
              (fun renamedCodomain =>
                Ty.piTy (domainType.rename rho)
                  (Ty.id renamedCodomain
                    (applyRaw.rename rho.lift)
                    (applyRaw.rename rho.lift)))
              (Ty.weaken_rename_commute rho baseCodomain)))
      HEq.rfl uncastHEq

def Term.lam_raw_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {genericType : Ty level scope}
    (someTerm : Term sourceCtx genericType (RawTerm.lam bodyRaw)) :
    (Σ' (domainA codomainA : Ty level scope),
      Σ' (bodyTerm :
          Term (sourceCtx.cons domainA) codomainA.weaken bodyRaw),
        Σ' (_ : genericType = Ty.arrow domainA codomainA),
          HEq someTerm (Term.lam bodyTerm)) ⊕'
    (Σ' (domainA : Ty level scope),
      Σ' (codomainA : Ty level (scope + 1)),
        Σ' (bodyTerm : Term (sourceCtx.cons domainA) codomainA bodyRaw),
          Σ' (_ : genericType = Ty.piTy domainA codomainA),
            HEq someTerm (Term.lamPi bodyTerm)) ⊕'
    (Σ' (domainA codomainA : Ty level scope),
      Σ' (applyRaw : RawTerm (scope + 1)),
        Σ' (_ : bodyRaw = RawTerm.refl applyRaw),
          Σ' (_ :
              genericType =
                funextReflType domainA codomainA applyRaw),
            HEq someTerm
              (Term.funextRefl (context := sourceCtx) domainA
                codomainA applyRaw)) ⊕'
    (Σ' (domainA codomainA : Ty level scope),
      Σ' (applyRaw : RawTerm (scope + 1)),
        Σ' (_ : bodyRaw = RawTerm.refl applyRaw),
          Σ' (_ :
              genericType =
                Ty.id (Ty.arrow domainA codomainA)
                  (RawTerm.lam (RawTerm.refl applyRaw))
                  (RawTerm.lam (RawTerm.refl applyRaw))),
            HEq someTerm
              (Term.funextReflAtId (context := sourceCtx) domainA
                codomainA applyRaw)) ⊕'
    (Σ' (domainA codomainA : Ty level scope),
      Σ' (applyARaw applyBRaw : RawTerm (scope + 1)),
        Σ' (_ : bodyRaw = RawTerm.refl applyARaw),
          Σ' (_ :
              genericType =
                Ty.id (Ty.arrow domainA codomainA)
                  (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw)),
            HEq someTerm
              (Term.funextIntroHet (context := sourceCtx) domainA
                codomainA applyARaw applyBRaw)) := by
  cases someTerm
  case lam domainType codomainType body =>
    exact PSum.inl ⟨domainType, codomainType, body, rfl, HEq.rfl⟩
  case lamPi domainType codomainType body =>
    exact PSum.inr (PSum.inl
      ⟨domainType, codomainType, body, rfl, HEq.rfl⟩)
  case funextRefl domainType codomainType applyRaw =>
    exact PSum.inr (PSum.inr (PSum.inl
      ⟨domainType, codomainType, applyRaw, rfl, rfl, HEq.rfl⟩))
  case funextReflAtId domainType codomainType applyRaw =>
    exact PSum.inr (PSum.inr (PSum.inr (PSum.inl
      ⟨domainType, codomainType, applyRaw, rfl, rfl, HEq.rfl⟩)))
  case funextIntroHet domainType codomainType applyARaw applyBRaw =>
    exact PSum.inr (PSum.inr (PSum.inr (PSum.inr
      ⟨domainType, codomainType, applyARaw, applyBRaw, rfl, rfl,
        HEq.rfl⟩)))

def Term.lam_arrow_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (genericTerm :
      Term sourceCtx (Ty.arrow domainType codomainType)
        (RawTerm.lam bodyRaw)) :
    Σ' (bodyTerm :
        Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw),
      HEq genericTerm (Term.lam bodyTerm) := by
  cases Term.lam_raw_inv genericTerm with
    | inl lamView =>
      obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := lamView
      injection typeEq
      subst domainA
      subst codomainA
      exact ⟨bodyTerm, termHEq⟩
    | inr restView =>
      cases restView with
      | inl piView =>
        obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := piView
        cases typeEq
      | inr restView =>
        cases restView with
        | inl reflView =>
          obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
            termHEq⟩ := reflView
          unfold funextReflType at typeEq
          cases typeEq
        | inr restView =>
          cases restView with
          | inl reflAtIdView =>
            obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
              termHEq⟩ := reflAtIdView
            cases typeEq
          | inr introView =>
            obtain ⟨domainA, codomainA, applyARaw, applyBRaw, rawEq,
              typeEq, termHEq⟩ := introView
            cases typeEq

def Term.lam_pi_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (genericTerm :
      Term sourceCtx (Ty.piTy domainType codomainType)
        (RawTerm.lam bodyRaw)) :
    (Σ' (bodyTerm : Term (sourceCtx.cons domainType) codomainType bodyRaw),
      HEq genericTerm (Term.lamPi bodyTerm)) ⊕'
    (Σ' (baseCodomain : Ty level scope)
      (applyRaw : RawTerm (scope + 1))
      (_ : bodyRaw = RawTerm.refl applyRaw)
      (_ : codomainType = Ty.id baseCodomain.weaken applyRaw applyRaw),
      HEq genericTerm
        (Term.funextRefl (context := sourceCtx) domainType baseCodomain
          applyRaw)) := by
  cases Term.lam_raw_inv genericTerm with
  | inl lamView =>
    obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := lamView
    cases typeEq
  | inr restView =>
    cases restView with
    | inl piView =>
      obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := piView
      injection typeEq
      subst domainA
      subst codomainA
      exact PSum.inl ⟨bodyTerm, termHEq⟩
    | inr restView =>
      cases restView with
      | inl reflView =>
        obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
          termHEq⟩ := reflView
        unfold funextReflType at typeEq
        injection typeEq
        subst domainA
        exact PSum.inr
          ⟨codomainA, applyRaw, rawEq, by assumption, termHEq⟩
      | inr restView =>
        cases restView with
        | inl reflAtIdView =>
          obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
            termHEq⟩ := reflAtIdView
          cases typeEq
        | inr introView =>
          obtain ⟨domainA, codomainA, applyARaw, applyBRaw, rawEq,
            typeEq, termHEq⟩ := introView
          cases typeEq

def Term.lam_arrow_id_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {leftRaw rightRaw : RawTerm (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (genericTerm :
      Term sourceCtx
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam leftRaw) (RawTerm.lam rightRaw))
        (RawTerm.lam bodyRaw)) :
    (Σ' (applyRaw : RawTerm (scope + 1)),
      Σ' (_ : bodyRaw = RawTerm.refl applyRaw),
        Σ' (_ : leftRaw = RawTerm.refl applyRaw),
          Σ' (_ : rightRaw = RawTerm.refl applyRaw),
            HEq genericTerm
              (Term.funextReflAtId (context := sourceCtx)
                domainType codomainType applyRaw)) ⊕'
    (Σ' (applyARaw applyBRaw : RawTerm (scope + 1)),
      Σ' (_ : bodyRaw = RawTerm.refl applyARaw),
        Σ' (_ : leftRaw = applyARaw),
          Σ' (_ : rightRaw = applyBRaw),
            HEq genericTerm
              (Term.funextIntroHet (context := sourceCtx)
                domainType codomainType applyARaw applyBRaw)) := by
  cases Term.lam_raw_inv genericTerm with
  | inl lamView =>
    obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := lamView
    cases typeEq
  | inr restView =>
    cases restView with
    | inl piView =>
      obtain ⟨domainA, codomainA, bodyTerm, typeEq, termHEq⟩ := piView
      cases typeEq
    | inr restView =>
      cases restView with
      | inl reflView =>
        obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
          termHEq⟩ := reflView
        unfold funextReflType at typeEq
        cases typeEq
      | inr restView =>
        cases restView with
        | inl reflAtIdView =>
          obtain ⟨domainA, codomainA, applyRaw, rawEq, typeEq,
            termHEq⟩ := reflAtIdView
          injection typeEq with _ carrierEq leftEq rightEq
          injection carrierEq with domainEq codomainEq
          injection leftEq with leftRawEq
          injection rightEq with rightRawEq
          subst domainA
          subst codomainA
          subst leftRaw
          subst rightRaw
          exact PSum.inl ⟨applyRaw, rawEq, rfl, rfl, termHEq⟩
        | inr introView =>
          obtain ⟨domainA, codomainA, applyARaw, applyBRaw, rawEq,
            typeEq, termHEq⟩ := introView
          injection typeEq with _ carrierEq leftEq rightEq
          injection carrierEq with domainEq codomainEq
          injection leftEq with leftRawEq
          injection rightEq with rightRawEq
          subst domainA
          subst codomainA
          subst leftRaw
          subst rightRaw
          exact PSum.inr
            ⟨applyARaw, applyBRaw, rawEq, rfl, rfl, termHEq⟩

theorem Term.rename_injective_atLamArrow_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ (bodyA bodyB :
          Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw),
        HEq (Term.rename (termRenaming.lift domainType) bodyA)
          (Term.rename (termRenaming.lift domainType) bodyB) →
        HEq bodyA bodyB)
    (termA termB :
      Term sourceCtx (Ty.arrow domainType codomainType)
        (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  obtain ⟨bodyA, termHEqA⟩ := Term.lam_arrow_inv termA
  obtain ⟨bodyB, termHEqB⟩ := Term.lam_arrow_inv termB
  cases termHEqA
  cases termHEqB
  exact
    Term.rename_injective_lam_ctor termRenaming bodyInjective bodyA bodyB
      renameEq

theorem Term.rename_injective_atLamPi_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ (bodyA bodyB :
          Term (sourceCtx.cons domainType) codomainType bodyRaw),
        HEq (Term.rename (termRenaming.lift domainType) bodyA)
          (Term.rename (termRenaming.lift domainType) bodyB) →
        HEq bodyA bodyB)
    (termA termB :
      Term sourceCtx (Ty.piTy domainType codomainType)
        (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  cases Term.lam_pi_inv termA with
  | inl lamViewA =>
    obtain ⟨bodyA, termHEqA⟩ := lamViewA
    cases Term.lam_pi_inv termB with
    | inl lamViewB =>
      obtain ⟨bodyB, termHEqB⟩ := lamViewB
      cases termHEqA
      cases termHEqB
      exact
        Term.rename_injective_lamPi_ctor termRenaming bodyInjective bodyA
          bodyB renameEq
    | inr reflViewB =>
      obtain ⟨baseCodomainB, applyRawB, bodyRawEqB, codomainEqB,
        termHEqB⟩ := reflViewB
      cases termHEqA
      cases bodyRawEqB
      cases codomainEqB
      cases termHEqB
      exact False.elim
        (renamedLamPi_ne_renamedFunextReflCast termRenaming bodyA
          baseCodomainB applyRawB rfl rfl
          (heq_of_eq renameEq))
  | inr reflViewA =>
    obtain ⟨baseCodomainA, applyRawA, bodyRawEqA, codomainEqA,
      termHEqA⟩ := reflViewA
    cases Term.lam_pi_inv termB with
    | inl lamViewB =>
      obtain ⟨bodyB, termHEqB⟩ := lamViewB
      cases bodyRawEqA
      cases codomainEqA
      cases termHEqA
      cases termHEqB
      exact False.elim
        (renamedLamPi_ne_renamedFunextReflCast termRenaming bodyB
          baseCodomainA applyRawA rfl rfl
          (HEq.symm (heq_of_eq renameEq)))
    | inr reflViewB =>
      obtain ⟨baseCodomainB, applyRawB, bodyRawEqB, codomainEqB,
        termHEqB⟩ := reflViewB
      cases bodyRawEqA
      cases codomainEqA
      have applyRawEq : applyRawA = applyRawB := by
        injection bodyRawEqB
      cases applyRawEq
      have baseWeakenEq :
          baseCodomainA.weaken = baseCodomainB.weaken := by
        injection codomainEqB
      have baseCodomainEq : baseCodomainA = baseCodomainB :=
        Ty.rename_injective_under_injective_renaming baseCodomainA
          RawRenamingInjective.weaken baseCodomainB baseWeakenEq
      cases baseCodomainEq
      cases codomainEqB
      cases termHEqA
      cases termHEqB
      rfl

theorem Term.rename_injective_atLamArrowId
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {leftRaw rightRaw bodyRaw : RawTerm (sourceScope + 1)}
    (termA termB :
      Term sourceCtx
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam leftRaw) (RawTerm.lam rightRaw))
        (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  cases Term.lam_arrow_id_inv termA with
  | inl reflViewA =>
    obtain ⟨applyRawA, bodyRawEqA, leftRawEqA, rightRawEqA,
      termHEqA⟩ := reflViewA
    cases Term.lam_arrow_id_inv termB with
    | inl reflViewB =>
      obtain ⟨applyRawB, bodyRawEqB, leftRawEqB, rightRawEqB,
        termHEqB⟩ := reflViewB
      cases bodyRawEqA
      have applyRawEq : applyRawA = applyRawB := by
        injection bodyRawEqB
      cases applyRawEq
      cases leftRawEqA
      cases leftRawEqB
      cases rightRawEqA
      cases rightRawEqB
      cases termHEqA
      cases termHEqB
      exact
        Term.rename_injective_funextReflAtId_ctor termRenaming
          domainType codomainType applyRawA renameEq
    | inr introViewB =>
      obtain ⟨applyARawB, applyBRawB, bodyRawEqB, leftRawEqB,
        rightRawEqB, termHEqB⟩ := introViewB
      cases bodyRawEqA
      have applyARawEq : applyRawA = applyARawB := by
        injection bodyRawEqB
      cases applyARawEq
      cases leftRawEqA
      exact False.elim
        (rawTerm_ne_refl_self _ leftRawEqB.symm)
  | inr introViewA =>
    obtain ⟨applyARawA, applyBRawA, bodyRawEqA, leftRawEqA,
      rightRawEqA, termHEqA⟩ := introViewA
    cases Term.lam_arrow_id_inv termB with
    | inl reflViewB =>
      obtain ⟨applyRawB, bodyRawEqB, leftRawEqB, rightRawEqB,
        termHEqB⟩ := reflViewB
      cases bodyRawEqA
      have applyRawEq : applyARawA = applyRawB := by
        injection bodyRawEqB
      cases applyRawEq
      cases leftRawEqA
      exact False.elim
        (rawTerm_ne_refl_self _ leftRawEqB)
    | inr introViewB =>
      obtain ⟨applyARawB, applyBRawB, bodyRawEqB, leftRawEqB,
        rightRawEqB, termHEqB⟩ := introViewB
      cases bodyRawEqA
      have applyARawEq : applyARawA = applyARawB := by
        injection bodyRawEqB
      cases applyARawEq
      cases leftRawEqA
      cases leftRawEqB
      cases rightRawEqA
      cases rightRawEqB
      cases termHEqA
      cases termHEqB
      rfl

end LeanFX2
