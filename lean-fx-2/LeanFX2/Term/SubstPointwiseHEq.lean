import LeanFX2.Term.LiftPointwiseHEq
import LeanFX2.Term.SubstTargetCtxCast
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq

/-! # LeanFX2.Term.SubstPointwiseHEq  (strength-T8 infrastructure, WIP)

Cross-sigma heterogeneous analogue of `Term.subst_pointwise`.  Where
`Term.subst_pointwise` (`…/SubstPointwise.lean`) bridges two TermSubsts over the
*same* underlying `Subst` (homogeneous `Eq` result), this bridges two TermSubsts
over *different but pointwise-equal* Substs, yielding a heterogeneous (HEq) equality
of the two substitution results.

This is the bridge that closes the binder / scope+1 arms of
`Term.rename_subst_commute` (strength-T8, #1964 → 34 subst0 arms of #2027): a binder
arm's IH lands at `precompose (rho.lift) (sigma.lift)`, and this bridge realigns it
to `(precompose rho sigma).lift` (pointwise-equal Substs).

Axiom-clean by construction: the type indices are bridged by the cross-sigma
`Ty.subst_pointwise` (homogeneous Eq, no funext), the raw indices by
`RawTerm.subst_pointwise`, the per-constructor recombination by the `_HEq_congr`
family, and the binder arms recurse through the axiom-free
`TermSubst.lift_pointwise_HEq`.

## Status: COMPLETE — all 78 constructor arms discharged, zero-axiom
(`#print axioms` reports no axiom dependence).  Binder arms use the
`TermSubst.lift_pointwise_HEq` + `SubstTargetCtxCast` bridge; cast-carrying arms
peel via `Term.type_eq_cast_heq`; `effectPerform` uses the generalised
`effectPerform_HEq_congr_subst` (Prop proof irrelevance on `CanPerform`). -/

namespace LeanFX2

/-- Mapping an operation signature's carriers by two pointwise-equal substitutions
yields equal signatures.  Pure per-field congruence (no funext): the effect label
is invariant, and the two carrier Ty fields are bridged by the cross-sigma
`Ty.subst_pointwise`.  Supports the cross-sigma `effectPerform` bridge arm. -/
theorem Effects.OperationSignature.map_subst_pointwise
    {level scope targetScope : Nat}
    {sigma1 sigma2 : Subst level scope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position)
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position)
    (operation : Effects.OperationSignature (Ty level scope)) :
    operation.map (fun carrierType => carrierType.subst sigma1)
      = operation.map (fun carrierType => carrierType.subst sigma2) := by
  show Effects.OperationSignature.mk operation.effectLabel
        (operation.argumentCarrier.subst sigma1) (operation.resultCarrier.subst sigma1)
      = Effects.OperationSignature.mk operation.effectLabel
        (operation.argumentCarrier.subst sigma2) (operation.resultCarrier.subst sigma2)
  rw [Ty.subst_pointwise forTyEq forRawEq operation.argumentCarrier,
      Ty.subst_pointwise forTyEq forRawEq operation.resultCarrier]

/-- Generalised HEq congruence for `Term.effectPerform` permitting DIFFERENT operation
signatures (bridged by an `Eq`).  `Effects.CanPerform` is a `Prop`, so the two
permission witnesses are definitionally equal by proof irrelevance once their
signature indices align — no explicit witness HEq is needed.  This is the bridge the
plain `effectPerform_HEq_congr` cannot supply, since `Term.subst` maps the operation
signature (and `CanPerform`) by the underlying substitution. -/
theorem Term.effectPerform_HEq_congr_subst
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectRow : Effects.EffectRow}
    {operationSignature1 operationSignature2 : Effects.OperationSignature (Ty level scope)}
    (operationSignatureEq : operationSignature1 = operationSignature2)
    {canPerform1 : Effects.CanPerform effectRow operationSignature1}
    {canPerform2 : Effects.CanPerform effectRow operationSignature2}
    {effectTag1 effectTag2 : RawTerm scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 : RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect operationSignature1.argumentCarrier effectTag1) operationRaw1}
    {operationTag2 :
      Term context (Ty.effect operationSignature2.argumentCarrier effectTag2) operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context operationSignature1.argumentCarrier argumentsRaw1}
    {arguments2 : Term context operationSignature2.argumentCarrier argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq (Term.effectPerform effectTag1 effectRow operationSignature1 canPerform1
          operationTag1 arguments1)
        (Term.effectPerform effectTag2 effectRow operationSignature2 canPerform2
          operationTag2 arguments2) := by
  subst operationSignatureEq
  subst effectTagEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  exact HEq.rfl

/-- `Term.subst` respects cross-sigma pointwise heterogeneous equality of TermSubsts.
If two TermSubsts (over pointwise-equal Substs) agree heterogeneously on every
variable, they substitute heterogeneously-equally into every term. -/
theorem Term.subst_pointwise_HEq
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma1 sigma2 : Subst level sourceScope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position)
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position)
    {firstTermSubst : TermSubst sourceCtx targetCtx sigma1}
    {secondTermSubst : TermSubst sourceCtx targetCtx sigma2}
    (entryHEq :
      ∀ position, HEq (firstTermSubst position) (secondTermSubst position)) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        HEq (Term.subst firstTermSubst someTerm)
            (Term.subst secondTermSubst someTerm)
  | _, _, .var position => entryHEq position
  | _, _, .unit => HEq.refl _
  | _, _, .app fnTerm argTerm =>
      Term.app_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq fnTerm)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq argTerm)
  -- Non-dep arrow binder.  `Term.subst` lifts each subst by `domainType`, landing
  -- in `targetCtx.cons (domainType.subst sigmaᵢ)` — divergent target contexts.  We
  -- cast the second lift back onto the first's target via `congrArg cons`, certify the
  -- cast is substitution-innocent (`SubstTargetCtxCast`), then the shared-context IH
  -- fires on `body`.  Outer cast peeled by `type_eq_cast_heq`.
  | _, _, .lam (domainType := domainType) (codomainType := codomainType)
              (bodyRaw := bodyRaw) body =>
      let domainEq := Ty.subst_pointwise forTyEq forRawEq domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEq.symm
      let entryHEqLifted := fun position =>
        HEq.trans
          (TermSubst.lift_pointwise_HEq forTyEq forRawEq entryHEq domainType position)
          (TermSubst.targetCtx_cast_entry_HEq targetCtxEq
            (secondTermSubst.lift domainType) position).symm
      let coreLifted :=
        Term.subst_pointwise_HEq (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) entryHEqLifted body
      let coreUncast :=
        Term.subst_targetCtx_cast_HEq targetCtxEq (secondTermSubst.lift domainType) body
      Term.lam_HEq_congr domainEq
        (Ty.subst_pointwise forTyEq forRawEq codomainType)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) bodyRaw)
        (HEq.trans
          (Term.type_eq_cast_heq (Ty.weaken_subst_commute sigma1 codomainType)
            (Term.subst (firstTermSubst.lift domainType) body))
          (HEq.trans (HEq.trans coreLifted coreUncast)
            (Term.type_eq_cast_heq (Ty.weaken_subst_commute sigma2 codomainType)
              (Term.subst (secondTermSubst.lift domainType) body)).symm))
  -- Dep Π binder.  `Term.subst` lifts without a cast (body type is `codomainType`
  -- directly), so the body HEq is exactly the cast-bridged shared-context IH.
  | _, _, .lamPi (domainType := domainType) (codomainType := codomainType)
                (bodyRaw := bodyRaw) body =>
      let domainEq := Ty.subst_pointwise forTyEq forRawEq domainType
      let targetCtxEq := congrArg (Ctx.cons targetCtx) domainEq.symm
      let entryHEqLifted := fun position =>
        HEq.trans
          (TermSubst.lift_pointwise_HEq forTyEq forRawEq entryHEq domainType position)
          (TermSubst.targetCtx_cast_entry_HEq targetCtxEq
            (secondTermSubst.lift domainType) position).symm
      let coreLifted :=
        Term.subst_pointwise_HEq (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) entryHEqLifted body
      let coreUncast :=
        Term.subst_targetCtx_cast_HEq targetCtxEq (secondTermSubst.lift domainType) body
      Term.lamPi_HEq_congr domainEq
        (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) codomainType)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) bodyRaw)
        (HEq.trans coreLifted coreUncast)
  -- Σ first projection: no cast (`Term.subst` on `.fst` is structural).
  | _, _, .fst pairTerm =>
      Term.fst_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq pairTerm)
  -- Σ second projection: result type cast `subst0_subst_commute.symm ▸` (outer); peel
  -- both sides with `type_eq_symm_cast_heq` around the structural `snd_HEq_congr`.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
              (pairRaw := pairRaw) pairTerm =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw) sigma1))
        (HEq.trans
          (Term.snd_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
            (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
              (Subst.lift_forRaw_pointwise forRawEq) _)
            (RawTerm.subst_pointwise forRawEq _)
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq pairTerm))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw) sigma2)).symm)
  -- Dep Π application: result type cast `subst0_subst_commute.symm ▸` (outer); same
  -- outer-peel shape as `snd`.  Codomain index lives at scope+1 (lifted witnesses).
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                (argumentRaw := argumentRaw) fn arg =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_subst_commute codomainType domainType argumentRaw sigma1))
        (HEq.trans
          (Term.appPi_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
            (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
              (Subst.lift_forRaw_pointwise forRawEq) _)
            (RawTerm.subst_pointwise forRawEq _)
            (RawTerm.subst_pointwise forRawEq _)
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq fn)
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq arg))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute codomainType domainType argumentRaw sigma2)).symm)
  -- Σ pair: the SECOND component carries a forward `subst0_subst_commute ▸` cast (the
  -- first does not); peel only the second-child HEq with `type_eq_cast_heq`.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
              (firstRaw := firstRaw) fv sv =>
      Term.pair_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq fv)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.subst0_subst_commute secondType firstType firstRaw sigma1)
            (Term.subst firstTermSubst sv))
          (HEq.trans
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq sv)
            (Term.type_eq_cast_heq
              (Ty.subst0_subst_commute secondType firstType firstRaw sigma2)
              (Term.subst secondTermSubst sv)).symm))
  -- Closed-value leaves: both sides definitionally identical (no sigma dependence).
  | _, _, .boolTrue => HEq.refl _
  | _, _, .boolFalse => HEq.refl _
  | _, _, .natZero => HEq.refl _
  -- Eliminator + structural arms (uniform `app` template): every Ty index bridged by
  -- `Ty.subst_pointwise forTyEq forRawEq _`, every raw by `RawTerm.subst_pointwise
  -- forRawEq _`, every child by the IH (same termSubsts — eliminator branches are
  -- arrow-typed in the unextended context, no lift threaded through).
  | _, _, .natSucc predecessor =>
      Term.natSucc_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq zeroBranch)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq zeroBranch)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq succBranch)
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq headTerm)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq nilBranch)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq consBranch)
  | _, _, .optionSome valueTerm =>
      Term.optionSome_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq noneBranch)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq someBranch)
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq leftBranch)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq rightBranch)
  | _, _, .recordIntro firstField =>
      Term.recordIntro_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq recordValue)
  | _, _, .codataDest codataValue =>
      Term.codataDest_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq codataValue)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq equivTerm)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq argumentTerm)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq initialState)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq transition)
  -- Parametric leaves (element type varies, no children).
  | _, _, .listNil =>
      Term.listNil_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
  | _, _, .optionNone =>
      Term.optionNone_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
  | _, _, .interval0 => HEq.refl _
  | _, _, .interval1 => HEq.refl _
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq leftValue)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq leftValue)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq rightValue)
  | _, _, .sessionRecv channel =>
      Term.sessionRecv_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq channel)
  | _, _, .sessionSend _ channel payload =>
      Term.sessionSend_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq channel)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq payload)
  -- Type codes (base-scope raw sub-codes; level data only, so no IH).
  | _, _, .universeCode _ _ _ _ => HEq.refl _
  | _, _, .arrowCode outerLevel levelLe _ _ =>
      Term.arrowCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .productCode outerLevel levelLe _ _ =>
      Term.productCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .sumCode outerLevel levelLe _ _ =>
      Term.sumCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .listCode outerLevel levelLe _ =>
      Term.listCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .optionCode outerLevel levelLe _ =>
      Term.optionCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .eitherCode outerLevel levelLe _ _ =>
      Term.eitherCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .idCode outerLevel levelLe _ _ _ =>
      Term.idCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .equivCode outerLevel levelLe _ _ =>
      Term.equivCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  -- Identity / observational-equality formers (carrier + raw witnesses).
  | _, _, .refl _ _ =>
      Term.refl_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .idJ baseCase witness =>
      Term.idJ_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq baseCase)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq witness)
  | _, _, .oeqRefl _ _ =>
      Term.oeqRefl_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq baseCase)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq witness)
  | _, _, .idStrictRefl modeIsStrict _ _ =>
      Term.idStrictRefl_HEq_congr modeIsStrict
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .idStrictRec modeIsStrict baseCase witness =>
      Term.idStrictRec_HEq_congr modeIsStrict
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq baseCase)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq witness)
  -- Modal introduction / elimination / subsumption (single inner child).
  | _, _, .modIntro inner =>
      Term.modIntro_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq inner)
  | _, _, .modElim inner =>
      Term.modElim_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq inner)
  | _, _, .subsume inner =>
      Term.subsume_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq inner)
  | _, _, .cumulUp _ _ _ _ _ typeCode =>
      Term.cumulUp_HEq_congr
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq typeCode)
  | _, _, .equivReflId _ =>
      Term.equivReflId_HEq_congr (Ty.subst_pointwise forTyEq forRawEq _)
  | _, _, .equivReflIdAtId _ _ _ _ =>
      Term.equivReflIdAtId_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
  | _, _, .uaToEquiv _ _ _ _ _ _ proof =>
      Term.uaToEquiv_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq proof)
  | _, _, .equivApply equivTerm argumentTerm =>
      Term.equivApply_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq equivTerm)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq argumentTerm)
  -- Cubical structural arms (no cast in `Term.subst`): same `app` template, Cubical congr.
  | _, _, .pathApp modeIsUnivalent pathTerm intervalTerm =>
      Term.pathApp_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq pathTerm)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq intervalTerm)
  | _, _, .glueIntro modeIsUnivalent baseType boundaryWitness baseValue partialValue =>
      Term.glueIntro_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq baseValue)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq partialValue)
  | _, _, .glueElim modeIsUnivalent gluedValue =>
      Term.glueElim_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq gluedValue)
  | _, _, .transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
              sourceTypeRaw targetTypeRaw typePath sourceValue =>
      Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq typePath)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq sourceValue)
  -- Path binder: lifts by the CLOSED `Ty.interval` (so the two lifted target contexts are
  -- defeq), still cast-bridged via the lam recipe for uniformity; `weaken_subst_commute`
  -- cast peeled by `type_eq_cast_heq`.
  | _, _, .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body =>
      let targetCtxEq := congrArg (Ctx.cons targetCtx)
        (Ty.subst_pointwise forTyEq forRawEq Ty.interval).symm
      let entryHEqLifted := fun position =>
        HEq.trans
          (TermSubst.lift_pointwise_HEq forTyEq forRawEq entryHEq Ty.interval position)
          (TermSubst.targetCtx_cast_entry_HEq targetCtxEq
            (secondTermSubst.lift Ty.interval) position).symm
      let coreLifted :=
        Term.subst_pointwise_HEq (Subst.lift_forTy_pointwise forTyEq)
          (Subst.lift_forRaw_pointwise forRawEq) entryHEqLifted body
      let coreUncast :=
        Term.subst_targetCtx_cast_HEq targetCtxEq (secondTermSubst.lift Ty.interval) body
      Term.pathLam_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
        (HEq.trans
          (Term.type_eq_cast_heq (Ty.weaken_subst_commute sigma1 carrierType)
            (Term.subst (firstTermSubst.lift Ty.interval) body))
          (HEq.trans (HEq.trans coreLifted coreUncast)
            (Term.type_eq_cast_heq (Ty.weaken_subst_commute sigma2 carrierType)
              (Term.subst (secondTermSubst.lift Ty.interval) body)).symm))
  -- Homogeneous composition (structural, no cast).
  | _, _, .hcomp modeIsUnivalent sidesValue capValue =>
      Term.hcomp_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq sidesValue)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq capValue)
  -- Path-shaped composition (structural, no cast; endpoints are raw children).
  | _, _, .hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue =>
      Term.hcompPath_HEq_congr modeIsUnivalent
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq sidesPath)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq capValue)
  -- Bool eliminator: result carries OUTER `subst0_subst_commute.symm ▸`, and the two
  -- branches each carry an inner `subst0_subst_commute ▸` (at boolTrue / boolFalse).
  -- Peel the outer with `type_eq_symm_cast_heq`, each branch with `type_eq_cast_heq`.
  | _, _, .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
              scrutinee thenBranch elseBranch =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw sigma1))
        (HEq.trans
          (Term.boolElim_HEq_congr
            (Ty.subst_pointwise (Subst.lift_forTy_pointwise forTyEq)
              (Subst.lift_forRaw_pointwise forRawEq) _)
            (RawTerm.subst_pointwise forRawEq _)
            (RawTerm.subst_pointwise forRawEq _)
            (RawTerm.subst_pointwise forRawEq _)
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq scrutinee)
            (HEq.trans
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue sigma1)
                (Term.subst firstTermSubst thenBranch))
              (HEq.trans
                (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq thenBranch)
                (Term.type_eq_cast_heq
                  (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue sigma2)
                  (Term.subst secondTermSubst thenBranch)).symm))
            (HEq.trans
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse sigma1)
                (Term.subst firstTermSubst elseBranch))
              (HEq.trans
                (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq elseBranch)
                (Term.type_eq_cast_heq
                  (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse sigma2)
                  (Term.subst secondTermSubst elseBranch)).symm)))
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw sigma2)).symm)
  -- Refinement elimination (structural; predicate is a scope+1 raw → lifted witness).
  | _, _, .refineElim refinedValue =>
      Term.refineElim_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq refinedValue)
  -- Refinement introduction (structural; predicate scope+1; proof is at `Ty.unit`).
  | _, _, .refineIntro predicate baseValue predicateProof =>
      Term.refineIntro_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq baseValue)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq predicateProof)
  -- Funext-refl witness (value, no subterm): result carries outer `funextReflType_subst.symm
  -- ▸`; peel both sides with `type_eq_symm_cast_heq`.  applyRaw is scope+1.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (funextReflType_subst sigma1 domainType codomainType applyRaw))
        (HEq.trans
          (Term.funextRefl_HEq_congr
            (Ty.subst_pointwise forTyEq forRawEq _)
            (Ty.subst_pointwise forTyEq forRawEq _)
            (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _))
          (Term.type_eq_symm_cast_heq
            (funextReflType_subst sigma2 domainType codomainType applyRaw)).symm)
  -- Funext-refl-at-Id witness (value, no cast, no subterm); applyRaw is scope+1.
  | _, _, .funextReflAtId domainType codomainType applyRaw =>
      Term.funextReflAtId_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
  -- Observational funext: the pointwiseProof child carries a forward
  -- `oeqFunextPointwiseType_subst ▸` cast; peel it with `type_eq_cast_heq`.
  | _, _, .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
              pointwiseProof =>
      Term.oeqFunext_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (oeqFunextPointwiseType_subst sigma1 domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.subst firstTermSubst pointwiseProof))
          (HEq.trans
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq pointwiseProof)
            (Term.type_eq_cast_heq
              (oeqFunextPointwiseType_subst sigma2 domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              (Term.subst secondTermSubst pointwiseProof)).symm))
  -- Binder type codes: domain code at scope, codomain code at scope+1 (lifted raw).
  | _, _, .piTyCode outerLevel levelLe _ _ =>
      Term.piTyCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
  | _, _, .sigmaTyCode outerLevel levelLe _ _ =>
      Term.sigmaTyCode_HEq_congr outerLevel levelLe
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
  -- Heterogeneous funext-intro (value, no cast); applyA/B raws are scope+1.
  | _, _, .funextIntroHet _ _ _ _ =>
      Term.funextIntroHet_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
        (RawTerm.subst_pointwise (Subst.lift_forRaw_pointwise forRawEq) _)
  -- Heterogeneous univalence-intro (structural; equivWitness raw is equivIntro of two raws).
  | _, _, .uaIntroHet innerLevel innerLevelLt _ _ equivWitness =>
      Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq equivWitness)
  -- Heterogeneous equivalence-intro: the two inverse witnesses each carry an inner
  -- `equivIntroHet{Left,Right}InverseType_subst ▸` cast; peel with `type_eq_cast_heq`.
  | _, _, .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
              (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
              forward backward leftInv rightInv =>
      Term.equivIntroHet_HEq_congr
        (Ty.subst_pointwise forTyEq forRawEq _)
        (Ty.subst_pointwise forTyEq forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq forward)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq backward)
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetLeftInverseType_subst sigma1 carrierA forwardRaw backwardRaw)
            (Term.subst firstTermSubst leftInv))
          (HEq.trans
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq leftInv)
            (Term.type_eq_cast_heq
              (equivIntroHetLeftInverseType_subst sigma2 carrierA forwardRaw backwardRaw)
              (Term.subst secondTermSubst leftInv)).symm))
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetRightInverseType_subst sigma1 carrierB forwardRaw backwardRaw)
            (Term.subst firstTermSubst rightInv))
          (HEq.trans
            (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq rightInv)
            (Term.type_eq_cast_heq
              (equivIntroHetRightInverseType_subst sigma2 carrierB forwardRaw backwardRaw)
              (Term.subst secondTermSubst rightInv)).symm))
  -- Effect perform: `Term.subst` maps the operationSignature (and the Prop-valued
  -- CanPerform) by substituting each carrier Ty, so the two sides carry DIFFERENT
  -- operation signatures.  The generalised `effectPerform_HEq_congr_subst` accepts the
  -- signature `Eq` (via `OperationSignature.map_subst_pointwise`, no funext) and absorbs
  -- the two permission witnesses by proof irrelevance.
  | _, _, .effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag arguments =>
      Term.effectPerform_HEq_congr_subst
        (Effects.OperationSignature.map_subst_pointwise forTyEq forRawEq operationSignature)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (RawTerm.subst_pointwise forRawEq _)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq operationTag)
        (Term.subst_pointwise_HEq forTyEq forRawEq entryHEq arguments)

end LeanFX2
