import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.PrecomposeLiftEntryHEq
import LeanFX2.Term.SubstPointwiseHEq
import LeanFX2.Term.SubstTargetCtxCast
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.RenameSubstCommute.Binders

/-! # LeanFX2.Term.RenameSubstCommute  (strength-T8 — dispatcher driver)

Typed term-level rename/subst FUSION: substituting into a renamed term equals
substituting by the input-precomposed substitution.  This is the typed mirror of
`RawTerm.rename_subst_commute` and the load-bearing fusion that makes
`Term.subst0_rename_commute` (strength-T8, #1964) a short corollary — which in turn
turns the 34 subst0-family arms of `Step.par.rename_compatible_typed` (#2027) into
one-line `castTargetTerm` applications.

## Status: WIP scaffold

The supporting machinery is already proven:
  * `Term.subst_pointwise` (full all-ctor) — `…/SubstPointwise.lean`
  * `TermSubst.precomposeRenaming` + `precomposeRenaming_position_HEq` — `…/Precompose.lean`,
    `…/SingletonPrecompose.lean`
  * `Ty.rename_subst_commute` (= `Subst.precomposeRenaming` Ty fusion) — `Foundation/Subst.lean`

This file assembles them into the term-level fusion by structural induction on the term,
mirroring the arm structure of `Term.subst_pointwise`.  Base cases (`var`, `unit`) land
first; the structural arms are filled incrementally.  NOT imported by the kernel root and
NOT committed until every arm is discharged and `#assert_no_axioms` is clean. -/

namespace LeanFX2

/-- Term-level rename/subst fusion (HEq form): `(t.rename ρ).subst σ` is heterogeneously
equal to `t.subst (precomposeRenaming ρ σ)`.  The two sides differ in both the Ty index
(bridged by `Ty.rename_subst_commute`) and the raw index (bridged definitionally through
`Subst.precomposeRenaming.forRaw`), hence the `HEq`. -/
theorem Term.rename_subst_commute
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        HEq (Term.subst termSubst (Term.rename termRenaming someTerm))
            (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst) someTerm)
  | _, _, .var position =>
      -- `Term.subst termSubst (Term.rename termRenaming (var p))` strips the rename
      -- cast (subst_type_eq_cast_heq) to `termSubst (rho p)`; the RHS is
      -- `(precomposeRenaming termRenaming termSubst) p`, heterogeneously equal to the
      -- same `termSubst (rho p)` by `precomposeRenaming_position_HEq`.
      HEq.trans
        (Term.subst_type_eq_cast_heq termSubst (termRenaming position)
          (Term.var (context := middleCtx) (rho position)))
        (TermSubst.precomposeRenaming_position_HEq termRenaming termSubst position).symm
  | _, _, .unit =>
      -- Both sides reduce definitionally to `Term.unit` at the closed type `Ty.unit`
      -- (which is fixed by both rename and subst), so the heterogeneous equality is refl.
      HEq.refl _
  | _, _, .boolTrue => HEq.refl _
  | _, _, .boolFalse => HEq.refl _
  | _, _, .natZero => HEq.refl _
  | _, _, .app fnTerm argTerm =>
      -- Structural template: `Term.rename`/`Term.subst` push through `app`
      -- definitionally; the per-ctor HEq congruence recombines the two child IHs,
      -- with the four index equalities supplied by the Ty/raw rename-subst fusions.
      Term.app_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst fnTerm)
        (Term.rename_subst_commute termRenaming termSubst argTerm)
  -- Eliminator and structural arms below are fully uniform: every Ty index is
  -- bridged by `Ty.rename_subst_commute rho sigma _`, every raw index by
  -- `RawTerm.rename_subst_commute rho sigma.forRaw _`, and every child by the IH
  -- (with the *same* termRenaming/termSubst — eliminator branches are arrow-typed
  -- in the unextended context, so no lifting is threaded through them).
  | _, _, .natSucc predecessor =>
      Term.natSucc_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst scrutinee)
        (Term.rename_subst_commute termRenaming termSubst zeroBranch)
        (Term.rename_subst_commute termRenaming termSubst succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst scrutinee)
        (Term.rename_subst_commute termRenaming termSubst zeroBranch)
        (Term.rename_subst_commute termRenaming termSubst succBranch)
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst headTerm)
        (Term.rename_subst_commute termRenaming termSubst tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst scrutinee)
        (Term.rename_subst_commute termRenaming termSubst nilBranch)
        (Term.rename_subst_commute termRenaming termSubst consBranch)
  | _, _, .optionSome valueTerm =>
      Term.optionSome_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst scrutinee)
        (Term.rename_subst_commute termRenaming termSubst noneBranch)
        (Term.rename_subst_commute termRenaming termSubst someBranch)
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst scrutinee)
        (Term.rename_subst_commute termRenaming termSubst leftBranch)
        (Term.rename_subst_commute termRenaming termSubst rightBranch)
  | _, _, .recordIntro firstField =>
      Term.recordIntro_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst recordValue)
  | _, _, .codataDest codataValue =>
      Term.codataDest_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst codataValue)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst equivTerm)
        (Term.rename_subst_commute termRenaming termSubst argumentTerm)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst initialState)
        (Term.rename_subst_commute termRenaming termSubst transition)
  -- Base parametric leaves (type index varies, no children).
  | _, _, .listNil =>
      Term.listNil_HEq_congr (Ty.rename_subst_commute rho sigma _)
  | _, _, .optionNone =>
      Term.optionNone_HEq_congr (Ty.rename_subst_commute rho sigma _)
  -- Closed-type interval endpoints: both sides definitionally identical.
  | _, _, .interval0 => HEq.refl _
  | _, _, .interval1 => HEq.refl _
  -- Interval lattice operations (closed type `Ty.interval`, raw children only).
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst leftValue)
        (Term.rename_subst_commute termRenaming termSubst rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst leftValue)
        (Term.rename_subst_commute termRenaming termSubst rightValue)
  -- Session primitives: protocol step lives in the channel's type as a raw.
  | _, _, .sessionRecv channel =>
      Term.sessionRecv_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst channel)
  | _, _, .sessionSend _ channel payload =>
      Term.sessionSend_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst channel)
        (Term.rename_subst_commute termRenaming termSubst payload)
  -- Type codes (base-scope raw sub-codes; carry only level data, so no IH).
  -- `universeCode` is invariant under both operations (level-only payload).
  | _, _, .universeCode _ _ _ _ => HEq.refl _
  | _, _, .arrowCode outerLevel levelLe _ _ =>
      Term.arrowCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .productCode outerLevel levelLe _ _ =>
      Term.productCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .sumCode outerLevel levelLe _ _ =>
      Term.sumCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .listCode outerLevel levelLe _ =>
      Term.listCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .optionCode outerLevel levelLe _ =>
      Term.optionCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .eitherCode outerLevel levelLe _ _ =>
      Term.eitherCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .idCode outerLevel levelLe _ _ _ =>
      Term.idCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .equivCode outerLevel levelLe _ _ =>
      Term.equivCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  -- Identity / observational-equality formers (carrier + raw witnesses).
  | _, _, .refl _ _ =>
      Term.refl_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .idJ baseCase witness =>
      Term.idJ_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst baseCase)
        (Term.rename_subst_commute termRenaming termSubst witness)
  | _, _, .oeqRefl _ _ =>
      Term.oeqRefl_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst baseCase)
        (Term.rename_subst_commute termRenaming termSubst witness)
  -- (`oeqFunext` deferred: `Term.rename`/`subst` push a `▸` cast through its
  -- `pointwiseProof` child, so the plain IH does not match — needs cast-aware arm.)
  | _, _, .idStrictRefl modeIsStrict _ _ =>
      Term.idStrictRefl_HEq_congr modeIsStrict
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .idStrictRec modeIsStrict baseCase witness =>
      Term.idStrictRec_HEq_congr modeIsStrict
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst baseCase)
        (Term.rename_subst_commute termRenaming termSubst witness)
  -- Modal introduction / elimination / subsumption (single inner child).
  | _, _, .modIntro inner =>
      Term.modIntro_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst inner)
  | _, _, .modElim inner =>
      Term.modElim_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst inner)
  | _, _, .subsume inner =>
      Term.subsume_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst inner)
  -- Universe cumulativity (level data implicit; one raw code child).
  | _, _, .cumulUp _ _ _ _ _ typeCode =>
      Term.cumulUp_HEq_congr
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst typeCode)
  -- HoTT identity-equivalence witnesses (base-scope variants).
  | _, _, .equivReflId _ =>
      Term.equivReflId_HEq_congr (Ty.rename_subst_commute rho sigma _)
  | _, _, .equivReflIdAtId _ _ _ _ =>
      Term.equivReflIdAtId_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
  | _, _, .uaToEquiv _ _ _ _ _ _ proof =>
      Term.uaToEquiv_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst proof)
  | _, _, .equivApply equivTerm argumentTerm =>
      Term.equivApply_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst equivTerm)
        (Term.rename_subst_commute termRenaming termSubst argumentTerm)
  -- Cast-free structural arms (mirror of the eliminator template): every Ty index by
  -- `Ty.rename_subst_commute rho sigma _`, every base-scope raw by
  -- `RawTerm.rename_subst_commute rho sigma.forRaw _`, every child by the shared IH.
  -- These constructors have a non-dependent result type, so neither `Term.rename` nor
  -- `Term.subst` inserts a `subst0`/`weaken` cast, and `_HEq_congr` recombines directly.
  -- (The binders and the refine/type-code predicates carry a scope+1 *raw* index and are
  -- handled separately; `fst`'s scope+1 Σ-codomain uses the lifted Ty fusion witness.)
  | _, _, .fst pairTerm =>
      Term.fst_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute_lift rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst pairTerm)
  | _, _, .pathApp modeIsUnivalent pathTerm intervalTerm =>
      Term.pathApp_HEq_congr modeIsUnivalent
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst pathTerm)
        (Term.rename_subst_commute termRenaming termSubst intervalTerm)
  | _, _, .glueIntro modeIsUnivalent _ _ baseValue partialValue =>
      Term.glueIntro_HEq_congr modeIsUnivalent
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst baseValue)
        (Term.rename_subst_commute termRenaming termSubst partialValue)
  | _, _, .glueElim modeIsUnivalent gluedValue =>
      Term.glueElim_HEq_congr modeIsUnivalent
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst gluedValue)
  | _, _, .transp modeIsUnivalent universeLevel universeLevelLt _ _ _ _ typePath sourceValue =>
      Term.transp_HEq_congr modeIsUnivalent universeLevel universeLevelLt
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst typePath)
        (Term.rename_subst_commute termRenaming termSubst sourceValue)
  | _, _, .hcomp modeIsUnivalent sidesValue capValue =>
      Term.hcomp_HEq_congr modeIsUnivalent
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst sidesValue)
        (Term.rename_subst_commute termRenaming termSubst capValue)
  | _, _, .hcompPath modeIsUnivalent _ _ sidesPath capValue =>
      Term.hcompPath_HEq_congr modeIsUnivalent
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst sidesPath)
        (Term.rename_subst_commute termRenaming termSubst capValue)
  | _, _, .uaIntroHet innerLevel innerLevelLt _ _ equivWitness =>
      Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst equivWitness)
  -- Scope+1-raw arms: the predicate / codomain-code / apply-witness raw lives under a binder,
  -- so its fusion witness is the LIFTED `RawTerm.rename_subst_commute_lift rho sigma _`; the
  -- base-scope Ty/raw indices keep the plain fusions.  (Cast-free in both rename and subst.)
  | _, _, .refineElim refinedValue =>
      Term.refineElim_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst refinedValue)
  | _, _, .refineIntro _ baseValue predicateProof =>
      Term.refineIntro_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst baseValue)
        (Term.rename_subst_commute termRenaming termSubst predicateProof)
  | _, _, .piTyCode outerLevel levelLe _ _ =>
      Term.piTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
  | _, _, .sigmaTyCode outerLevel levelLe _ _ =>
      Term.sigmaTyCode_HEq_congr outerLevel levelLe
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
  | _, _, .funextReflAtId _ _ _ =>
      Term.funextReflAtId_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
  | _, _, .funextIntroHet _ _ _ _ =>
      Term.funextIntroHet_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
        (RawTerm.rename_subst_commute_lift rho sigma _)
  -- Cast-carrying arms: in fusion the inner `rename` cast sits UNDER the outer `subst` cast.
  -- Four-step peel: (1) `subst_type_eq_cast_heq` peels the inner rename cast off the LHS;
  -- (2) `type_eq_symm_cast_heq` peels the LHS-core `subst` cast (renamed indices); (3) the
  -- bare-ctor `_HEq_congr` bridges the two cores via the child IH; (4) the RHS-core `subst`
  -- cast (original indices, precomposed) is re-applied via `(type_eq_symm_cast_heq _).symm`.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      HEq.trans
        (Term.subst_type_eq_cast_heq termSubst
          (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRaw) rho).symm
          (Term.snd (Term.rename termRenaming pairTerm)))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute (secondType.rename rho.lift) (firstType.rename rho)
              (RawTerm.fst (pairRaw.rename rho)) sigma))
          (HEq.trans
            (Term.snd_HEq_congr
              (Ty.rename_subst_commute rho sigma _)
              (Ty.rename_subst_commute_lift rho sigma _)
              (RawTerm.rename_subst_commute rho sigma.forRaw _)
              (Term.rename_subst_commute termRenaming termSubst pairTerm))
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_subst_commute secondType firstType (RawTerm.fst pairRaw)
                (Subst.precomposeRenaming rho sigma))).symm))
  -- Dep Π application: same outer-cast shape as `snd` (the β-redex result type is
  -- `codomainType.subst0 domainType argumentRaw`).
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                (argumentRaw := argumentRaw) fn arg =>
      HEq.trans
        (Term.subst_type_eq_cast_heq termSubst
          (Ty.subst0_rename_commute codomainType domainType argumentRaw rho).symm
          (Term.appPi (Term.rename termRenaming fn) (Term.rename termRenaming arg)))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute (codomainType.rename rho.lift) (domainType.rename rho)
              (argumentRaw.rename rho) sigma))
          (HEq.trans
            (Term.appPi_HEq_congr
              (Ty.rename_subst_commute rho sigma _)
              (Ty.rename_subst_commute_lift rho sigma _)
              (RawTerm.rename_subst_commute rho sigma.forRaw _)
              (RawTerm.rename_subst_commute rho sigma.forRaw _)
              (Term.rename_subst_commute termRenaming termSubst fn)
              (Term.rename_subst_commute termRenaming termSubst arg))
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_subst_commute codomainType domainType argumentRaw
                (Subst.precomposeRenaming rho sigma))).symm))
  -- Σ pair: NO outer cast (result is the plain `sigmaTy`), but the SECOND component carries
  -- a FORWARD `subst0_*_commute ▸` cast in both rename and subst.  So `pair_HEq_congr` takes
  -- the first child as the plain IH and the second child as a 4-step double-peel chain that
  -- uses FORWARD `type_eq_cast_heq` (not `.symm`) for the two subst0 casts.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) firstValue secondValue =>
      Term.pair_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute_lift rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst firstValue)
        (HEq.trans
          (Term.type_eq_cast_heq
            (Ty.subst0_subst_commute (secondType.rename rho.lift) (firstType.rename rho)
              (firstRaw.rename rho) sigma)
            (Term.subst termSubst
              (Ty.subst0_rename_commute secondType firstType firstRaw rho ▸
                Term.rename termRenaming secondValue)))
          (HEq.trans
            (Term.subst_type_eq_cast_heq termSubst
              (Ty.subst0_rename_commute secondType firstType firstRaw rho)
              (Term.rename termRenaming secondValue))
            (HEq.trans
              (Term.rename_subst_commute termRenaming termSubst secondValue)
              (Term.type_eq_cast_heq
                (Ty.subst0_subst_commute secondType firstType firstRaw
                  (Subst.precomposeRenaming rho sigma))
                (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                  secondValue)).symm)))
  -- Observational funext: `pair`-shaped — no outer cast, but the `pointwiseProof` child carries
  -- a FORWARD `oeqFunextPointwiseType_{rename,subst} ▸` cast.  Both domain and codomain are at
  -- base scope (no `_lift`).  The single child HEq is a forward double-peel.
  | _, _, .oeqFunext domainType codomainType
              leftFunctionRaw rightFunctionRaw pointwiseProof =>
      Term.oeqFunext_HEq_congr
        (Ty.rename_subst_commute rho sigma _)
        (Ty.rename_subst_commute rho sigma _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (HEq.trans
          (Term.type_eq_cast_heq
            (oeqFunextPointwiseType_subst sigma (domainType.rename rho)
              (codomainType.rename rho) (leftFunctionRaw.rename rho)
              (rightFunctionRaw.rename rho))
            (Term.subst termSubst
              (oeqFunextPointwiseType_rename rho domainType codomainType
                leftFunctionRaw rightFunctionRaw ▸
                Term.rename termRenaming pointwiseProof)))
          (HEq.trans
            (Term.subst_type_eq_cast_heq termSubst
              (oeqFunextPointwiseType_rename rho domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              (Term.rename termRenaming pointwiseProof))
            (HEq.trans
              (Term.rename_subst_commute termRenaming termSubst pointwiseProof)
              (Term.type_eq_cast_heq
                (oeqFunextPointwiseType_subst (Subst.precomposeRenaming rho sigma)
                  domainType codomainType leftFunctionRaw rightFunctionRaw)
                (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                  pointwiseProof)).symm)))
  -- Funext-refl witness: `snd`-shaped OUTER `.symm ▸` cast but the cast lemma is
  -- `funextReflType_{rename,subst}` (not subst0) and there is NO Term child — just the
  -- `funextRefl_HEq_congr` index witnesses (applyRaw scope+1 → `_lift`).
  | _, _, .funextRefl domainType codomainType applyRaw =>
      HEq.trans
        (Term.subst_type_eq_cast_heq termSubst
          (funextReflType_rename rho domainType codomainType applyRaw).symm
          (Term.funextRefl (domainType.rename rho) (codomainType.rename rho)
            (applyRaw.rename rho.lift)))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (funextReflType_subst sigma (domainType.rename rho) (codomainType.rename rho)
              (applyRaw.rename rho.lift)))
          (HEq.trans
            (Term.funextRefl_HEq_congr
              (Ty.rename_subst_commute rho sigma _)
              (Ty.rename_subst_commute rho sigma _)
              (RawTerm.rename_subst_commute_lift rho sigma _))
            (Term.type_eq_symm_cast_heq
              (funextReflType_subst (Subst.precomposeRenaming rho sigma)
                domainType codomainType applyRaw)).symm))
  -- Heterogeneous equivalence-intro: `pair`-style via the congr; forward/backward are plain
  -- IH children; leftInv/rightInv carry FORWARD `equivIntroHet{Left,Right}InverseType` casts.
  -- The inner `cast ▸ rename child` needs a TYPE ASCRIPTION (the cast motive can't be inferred
  -- through the complex InverseType def without it) — so leftInvRaw/rightInvRaw are pattern-bound.
  | _, _, .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
              (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
              (leftInvRaw := leftInvRaw) (rightInvRaw := rightInvRaw)
              forward backward leftInv rightInv =>
      Term.equivIntroHet_HEq_congr
        (Ty.rename_subst_commute rho sigma carrierA)
        (Ty.rename_subst_commute rho sigma carrierB)
        (RawTerm.rename_subst_commute rho sigma.forRaw forwardRaw)
        (RawTerm.rename_subst_commute rho sigma.forRaw backwardRaw)
        (RawTerm.rename_subst_commute rho sigma.forRaw leftInvRaw)
        (RawTerm.rename_subst_commute rho sigma.forRaw rightInvRaw)
        (Term.rename_subst_commute termRenaming termSubst forward)
        (Term.rename_subst_commute termRenaming termSubst backward)
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetLeftInverseType_subst sigma (carrierA.rename rho)
              (forwardRaw.rename rho) (backwardRaw.rename rho))
            (Term.subst termSubst
              (equivIntroHetLeftInverseType_rename rho carrierA forwardRaw backwardRaw ▸
                Term.rename termRenaming leftInv :
                Term middleCtx
                  (equivIntroHetLeftInverseType (carrierA.rename rho)
                    (forwardRaw.rename rho) (backwardRaw.rename rho))
                  (leftInvRaw.rename rho))))
          (HEq.trans
            (Term.subst_type_eq_cast_heq termSubst
              (equivIntroHetLeftInverseType_rename rho carrierA forwardRaw backwardRaw)
              (Term.rename termRenaming leftInv))
            (HEq.trans
              (Term.rename_subst_commute termRenaming termSubst leftInv)
              (Term.type_eq_cast_heq
                (equivIntroHetLeftInverseType_subst (Subst.precomposeRenaming rho sigma)
                  carrierA forwardRaw backwardRaw)
                (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                  leftInv)).symm)))
        (HEq.trans
          (Term.type_eq_cast_heq
            (equivIntroHetRightInverseType_subst sigma (carrierB.rename rho)
              (forwardRaw.rename rho) (backwardRaw.rename rho))
            (Term.subst termSubst
              (equivIntroHetRightInverseType_rename rho carrierB forwardRaw backwardRaw ▸
                Term.rename termRenaming rightInv :
                Term middleCtx
                  (equivIntroHetRightInverseType (carrierB.rename rho)
                    (forwardRaw.rename rho) (backwardRaw.rename rho))
                  (rightInvRaw.rename rho))))
          (HEq.trans
            (Term.subst_type_eq_cast_heq termSubst
              (equivIntroHetRightInverseType_rename rho carrierB forwardRaw backwardRaw)
              (Term.rename termRenaming rightInv))
            (HEq.trans
              (Term.rename_subst_commute termRenaming termSubst rightInv)
              (Term.type_eq_cast_heq
                (equivIntroHetRightInverseType_subst (Subst.precomposeRenaming rho sigma)
                  carrierB forwardRaw backwardRaw)
                (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                  rightInv)).symm)))
  -- Bool eliminator: OUTER `.symm ▸ subst0_subst_commute … scrutineeRaw` peel (snd-shape)
  -- around `boolElim_HEq_congr`; scrutinee is a plain IH; then/else branches are forward
  -- double-peels (pair-shape).  Like equivIntroHet, the cast-wrapped branches need
  -- TYPE ASCRIPTION (so thenRaw/elseRaw are pattern-bound).  motive scope+1 → `_lift`.
  | _, _, .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
                    (thenRaw := thenRaw) (elseRaw := elseRaw)
                    scrutinee thenBranch elseBranch =>
      HEq.trans
        (Term.subst_type_eq_cast_heq termSubst
          (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho).symm
          (Term.boolElim (motiveType := motiveType.rename rho.lift)
            (Term.rename termRenaming scrutinee)
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
              Term.rename termRenaming thenBranch :
              Term middleCtx ((motiveType.rename rho.lift).subst0 Ty.bool RawTerm.boolTrue)
                (thenRaw.rename rho))
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
              Term.rename termRenaming elseBranch :
              Term middleCtx ((motiveType.rename rho.lift).subst0 Ty.bool RawTerm.boolFalse)
                (elseRaw.rename rho))))
        (HEq.trans
          (Term.type_eq_symm_cast_heq
            (Ty.subst0_subst_commute (motiveType.rename rho.lift) Ty.bool
              (scrutineeRaw.rename rho) sigma))
          (HEq.trans
            (Term.boolElim_HEq_congr
              (Ty.rename_subst_commute_lift rho sigma _)
              (RawTerm.rename_subst_commute rho sigma.forRaw scrutineeRaw)
              (RawTerm.rename_subst_commute rho sigma.forRaw thenRaw)
              (RawTerm.rename_subst_commute rho sigma.forRaw elseRaw)
              (Term.rename_subst_commute termRenaming termSubst scrutinee)
              (HEq.trans
                (Term.type_eq_cast_heq
                  (Ty.subst0_subst_commute (motiveType.rename rho.lift) Ty.bool
                    RawTerm.boolTrue sigma)
                  (Term.subst termSubst
                    (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
                      Term.rename termRenaming thenBranch :
                      Term middleCtx
                        ((motiveType.rename rho.lift).subst0 Ty.bool RawTerm.boolTrue)
                        (thenRaw.rename rho))))
                (HEq.trans
                  (Term.subst_type_eq_cast_heq termSubst
                    (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho)
                    (Term.rename termRenaming thenBranch))
                  (HEq.trans
                    (Term.rename_subst_commute termRenaming termSubst thenBranch)
                    (Term.type_eq_cast_heq
                      (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
                        (Subst.precomposeRenaming rho sigma))
                      (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                        thenBranch)).symm)))
              (HEq.trans
                (Term.type_eq_cast_heq
                  (Ty.subst0_subst_commute (motiveType.rename rho.lift) Ty.bool
                    RawTerm.boolFalse sigma)
                  (Term.subst termSubst
                    (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
                      Term.rename termRenaming elseBranch :
                      Term middleCtx
                        ((motiveType.rename rho.lift).subst0 Ty.bool RawTerm.boolFalse)
                        (elseRaw.rename rho))))
                (HEq.trans
                  (Term.subst_type_eq_cast_heq termSubst
                    (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho)
                    (Term.rename termRenaming elseBranch))
                  (HEq.trans
                    (Term.rename_subst_commute termRenaming termSubst elseBranch)
                    (Term.type_eq_cast_heq
                      (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
                        (Subst.precomposeRenaming rho sigma))
                      (Term.subst (TermSubst.precomposeRenaming termRenaming termSubst)
                        elseBranch)).symm))))
            (Term.type_eq_symm_cast_heq
              (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
                (Subst.precomposeRenaming rho sigma))).symm))
  -- Binder arms dispatch to the standalone fusion lemmas in
  -- `RenameSubstCommute/Binders.lean` (parallelizable; the recursion supplies the
  -- body fusion HEq as the hypothesis each lemma takes).
  | _, _, .lamPi (domainType := domainType) body =>
      Term.rename_subst_commute_lamPi termRenaming termSubst body
        (Term.rename_subst_commute (termRenaming.lift domainType)
          (termSubst.lift (domainType.rename rho)) body)
  | _, _, .lam (domainType := domainType) body =>
      Term.rename_subst_commute_lam termRenaming termSubst body
        (Term.rename_subst_commute (termRenaming.lift domainType)
          (termSubst.lift (domainType.rename rho)) body)
  | _, _, .pathLam modeIsUnivalent _ _ _ body =>
      Term.rename_subst_commute_pathLam termRenaming termSubst modeIsUnivalent body
        (Term.rename_subst_commute (termRenaming.lift Ty.interval)
          (termSubst.lift Ty.interval) body)
  -- Effect perform: `Term.rename`/`Term.subst` map the operation signature (and the
  -- Prop-valued `CanPerform`) by acting on each carrier `Ty`, so the two sides carry
  -- DIFFERENT signatures bridged by `map_rename_subst_commute`.  The generalised
  -- `effectPerform_HEq_congr_subst` accepts the signature `Eq` and absorbs the two
  -- permission witnesses by proof irrelevance.
  | _, _, .effectPerform effectTag effectRow operationSignature
              canPerformOperation operationTag arguments =>
      Term.effectPerform_HEq_congr_subst
        (Effects.OperationSignature.map_rename_subst_commute rho sigma
          operationSignature)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (RawTerm.rename_subst_commute rho sigma.forRaw _)
        (Term.rename_subst_commute termRenaming termSubst operationTag)
        (Term.rename_subst_commute termRenaming termSubst arguments)

end LeanFX2
