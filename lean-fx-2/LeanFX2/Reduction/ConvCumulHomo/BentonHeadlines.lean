import LeanFX2.Reduction.ConvCumulHomo.Bridge

/-! # LeanFX2.Reduction.ConvCumulHomo.BentonHeadlines

Pattern 2 (Benton-Hur-Kennedy-McBride JAR'12): recursive `rename` and
`subst` compatibility headlines for `ConvCumulHomo`.

Each headline is a genuine recursive theorem proven by `induction` on
the relation.  Works because the homogeneous indices unify cleanly
(this is exactly the wall that `viaUp` defeats on full `ConvCumul`).

All 26 ctors discharged at zero axioms, including the four cast cases
(lam, appPi, pair, snd) plus dependent-eliminator cong cases
(boolElim, natElim, ...) via the `cast_eq_indep` "have inner := ..."
ordering trick from `Bridge.lean`.

## Root status

Layer 3 conv-cumul homogeneous helper. -/

namespace LeanFX2


/-! # Pattern 2 (Benton JAR'12): rename_compatible — recursive headline

Single typed `TermRenaming` lifts an existing `ConvCumulHomo` to
the renamed pair.  Proven by `induction` on `ConvCumulHomo` —
works because the homogeneous indices unify cleanly. -/

/-- **Benton headline**: `ConvCumulHomo` is preserved under typed
renaming.  Genuine recursive theorem, proven by induction on the
relation. -/
theorem ConvCumulHomo.rename_compatible_benton
    {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
      {rho : RawRenaming sourceScope targetScope}
      (termRenaming : TermRenaming sourceCtx targetCtx rho),
      ConvCumulHomo (firstTerm.rename termRenaming)
                    (secondTerm.rename termRenaming) := by
  induction cumulRel with
  | refl _ => intros; exact ConvCumulHomo.refl _
  | sym _ ih => intros; exact ConvCumulHomo.sym (ih _)
  | trans _ _ ihAB ihBC => intros; exact ConvCumulHomo.trans (ihAB _) (ihBC _)
  | lamCong _ ih =>
      intros _ _ _ termRenaming
      have inner := ih (TermRenaming.lift termRenaming _)
      exact ConvCumulHomo.lamCong
              (ConvCumulHomo.cast_eq_indep _ _ inner)
  | lamPiCong _ ih =>
      intros _ _ _ termRenaming
      exact ConvCumulHomo.lamPiCong (ih (TermRenaming.lift termRenaming _))
  | appCong _ _ ihFn ihArg =>
      intros _ _ _ termRenaming
      exact ConvCumulHomo.appCong (ihFn termRenaming) (ihArg termRenaming)
  | appPiCong _ _ ihFn ihArg =>
      intros _ _ _ termRenaming
      have inner := ConvCumulHomo.appPiCong (ihFn termRenaming) (ihArg termRenaming)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | pairCong _ _ ihFst ihSnd =>
      intros _ _ _ termRenaming
      have innerSnd := ihSnd termRenaming
      exact ConvCumulHomo.pairCong (ihFst termRenaming)
              (ConvCumulHomo.cast_eq_indep _ _ innerSnd)
  | fstCong _ ih => intros _ _ _ termRenaming; exact ConvCumulHomo.fstCong (ih termRenaming)
  | sndCong _ ih =>
      intros _ _ _ termRenaming
      have inner := ConvCumulHomo.sndCong (ih termRenaming)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | boolElimCong _ _ _ ihS ihT ihE =>
      -- Codex's dependent-eliminator refactor: branch types are now
      -- `motiveType.subst0 Ty.bool boolTrue/False`, so renaming/substing
      -- introduces a `Ty.subst0_rename_commute`/`subst_commute` cast.
      -- `cast_eq_indep` bridges the gap between the IH form and what
      -- `boolElimCong` expects.
      rename_i relationScope relationContext motiveType
        scrutFirstRaw scrutSecondRaw thenFirstRaw thenSecondRaw
        elseFirstRaw elseSecondRaw scrutFirst scrutSecond thenFirst
        thenSecond elseFirst elseSecond scrutRel thenRel elseRel
      intros targetScope targetCtx rho termRenaming
      let renamedMotiveType := motiveType.rename rho.lift
      have thenTypeEq :
          (motiveType.subst0 Ty.bool RawTerm.boolTrue).rename rho =
            renamedMotiveType.subst0 Ty.bool RawTerm.boolTrue := by
        simpa [renamedMotiveType] using
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolTrue rho)
      have elseTypeEq :
          (motiveType.subst0 Ty.bool RawTerm.boolFalse).rename rho =
            renamedMotiveType.subst0 Ty.bool RawTerm.boolFalse := by
        simpa [renamedMotiveType] using
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolFalse rho)
      have firstResultEq :
          (motiveType.subst0 Ty.bool scrutFirstRaw).rename rho =
            renamedMotiveType.subst0 Ty.bool (scrutFirstRaw.rename rho) := by
        simpa [renamedMotiveType] using
          (Ty.subst0_rename_commute motiveType Ty.bool
            scrutFirstRaw rho)
      have secondResultEq :
          (motiveType.subst0 Ty.bool scrutSecondRaw).rename rho =
            renamedMotiveType.subst0 Ty.bool (scrutSecondRaw.rename rho) := by
        simpa [renamedMotiveType] using
          (Ty.subst0_rename_commute motiveType Ty.bool
            scrutSecondRaw rho)
      have inner :
          ConvCumulHomo
            (Term.boolElim
              (motiveType := renamedMotiveType)
              (Term.rename termRenaming scrutFirst)
              (thenTypeEq ▸ Term.rename termRenaming thenFirst)
              (elseTypeEq ▸ Term.rename termRenaming elseFirst))
            (Term.boolElim
              (motiveType := renamedMotiveType)
              (Term.rename termRenaming scrutSecond)
              (thenTypeEq ▸ Term.rename termRenaming thenSecond)
              (elseTypeEq ▸ Term.rename termRenaming elseSecond)) :=
        ConvCumulHomo.boolElimCong
          (motiveType := renamedMotiveType)
          (ihS termRenaming)
          (ConvCumulHomo.cast_eq_both thenTypeEq (ihT termRenaming))
          (ConvCumulHomo.cast_eq_both elseTypeEq (ihE termRenaming))
      exact ConvCumulHomo.cast_eq_indep
        firstResultEq.symm secondResultEq.symm inner
  | natElimCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natElimCong (ihS _) (ihZ _) (ihK _)
  | natRecCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natRecCong (ihS _) (ihZ _) (ihK _)
  | listElimCong _ _ _ ihS ihN ihC =>
      intros; exact ConvCumulHomo.listElimCong (ihS _) (ihN _) (ihC _)
  | optionMatchCong _ _ _ ihS ihN ihM =>
      intros; exact ConvCumulHomo.optionMatchCong (ihS _) (ihN _) (ihM _)
  | eitherMatchCong _ _ _ ihS ihL ihR =>
      intros; exact ConvCumulHomo.eitherMatchCong (ihS _) (ihL _) (ihR _)
  | natSuccCong _ ih => intros; exact ConvCumulHomo.natSuccCong (ih _)
  | listConsCong _ _ ihH ihT => intros; exact ConvCumulHomo.listConsCong (ihH _) (ihT _)
  | optionSomeCong _ ih => intros; exact ConvCumulHomo.optionSomeCong (ih _)
  | eitherInlCong _ ih => intros; exact ConvCumulHomo.eitherInlCong (ih _)
  | eitherInrCong _ ih => intros; exact ConvCumulHomo.eitherInrCong (ih _)
  | idJCong _ _ ihB ihW => intros; exact ConvCumulHomo.idJCong (ihB _) (ihW _)
  | modIntroCong _ ih => intros; exact ConvCumulHomo.modIntroCong (ih _)
  | modElimCong _ ih => intros; exact ConvCumulHomo.modElimCong (ih _)
  | subsumeCong _ ih => intros; exact ConvCumulHomo.subsumeCong (ih _)
  | cumulUpCong lowerLevel higherLevel cumulMonotone
                levelLeLow levelLeHigh _ ih =>
      -- Phase CUMUL-2.6 Design D: Term.{rename,subst}'s cumulUp arm
      -- recurses on typeCode.  IH provides the substituted inner
      -- relation; ConvCumulHomo.cumulUpCong rebuilds at target ctx.
      intros _ _ _ context4
      exact ConvCumulHomo.cumulUpCong lowerLevel higherLevel cumulMonotone
                                      levelLeLow levelLeHigh
                                      (ih context4)

/-! # Pattern 2 (BHKM JAR'12): subst_compatible — recursive headline (the SUBST rung)

`Term.subst` is the substitution analog of `Term.rename`.  Same
recursive structure, same cast-handling pattern: where the subst
arm wraps in `Ty.weaken_subst_commute` or `Ty.subst0_subst_commute`,
we use `cast_eq_indep` with the `have inner := ...` ordering trick
to let Lean elaborate the inner term type concretely first. -/

/-- **Benton subst headline**: `ConvCumulHomo` is preserved under
typed substitution.  Genuine recursive theorem, proven by induction
on the relation.  All 24 ctors discharged at zero axioms,
including the four cast cases (lam, appPi, pair, snd). -/
theorem ConvCumulHomo.subst_compatible_benton
    {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
      {sigma : Subst level sourceScope targetScope}
      (termSubst : TermSubst sourceCtx targetCtx sigma),
      ConvCumulHomo (firstTerm.subst termSubst)
                    (secondTerm.subst termSubst) := by
  induction cumulRel with
  | refl _ => intros; exact ConvCumulHomo.refl _
  | sym _ ih => intros; exact ConvCumulHomo.sym (ih _)
  | trans _ _ ihAB ihBC => intros; exact ConvCumulHomo.trans (ihAB _) (ihBC _)
  | lamCong _ ih =>
      intros _ _ _ termSubst
      have inner := ih (TermSubst.lift termSubst _)
      exact ConvCumulHomo.lamCong
              (ConvCumulHomo.cast_eq_indep _ _ inner)
  | lamPiCong _ ih =>
      intros _ _ _ termSubst
      exact ConvCumulHomo.lamPiCong (ih (TermSubst.lift termSubst _))
  | appCong _ _ ihFn ihArg =>
      intros _ _ _ termSubst
      exact ConvCumulHomo.appCong (ihFn termSubst) (ihArg termSubst)
  | appPiCong _ _ ihFn ihArg =>
      intros _ _ _ termSubst
      have inner := ConvCumulHomo.appPiCong (ihFn termSubst) (ihArg termSubst)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | pairCong _ _ ihFst ihSnd =>
      intros _ _ _ termSubst
      have innerSnd := ihSnd termSubst
      exact ConvCumulHomo.pairCong (ihFst termSubst)
              (ConvCumulHomo.cast_eq_indep _ _ innerSnd)
  | fstCong _ ih => intros _ _ _ termSubst; exact ConvCumulHomo.fstCong (ih termSubst)
  | sndCong _ ih =>
      intros _ _ _ termSubst
      have inner := ConvCumulHomo.sndCong (ih termSubst)
      exact ConvCumulHomo.cast_eq_indep _ _ inner
  | boolElimCong _ _ _ ihS ihT ihE =>
      -- Codex's dependent-eliminator refactor: branch types are now
      -- `motiveType.subst0 Ty.bool boolTrue/False`, so renaming/substing
      -- introduces a `Ty.subst0_rename_commute`/`subst_commute` cast.
      -- `cast_eq_indep` bridges the gap between the IH form and what
      -- `boolElimCong` expects.
      rename_i relationScope relationContext motiveType
        scrutFirstRaw scrutSecondRaw thenFirstRaw thenSecondRaw
        elseFirstRaw elseSecondRaw scrutFirst scrutSecond thenFirst
        thenSecond elseFirst elseSecond scrutRel thenRel elseRel
      intros targetScope targetCtx sigma termSubst
      let substitutedMotiveType := motiveType.subst sigma.lift
      have thenTypeEq :
          (motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma =
            substitutedMotiveType.subst0 Ty.bool RawTerm.boolTrue := by
        simpa [substitutedMotiveType] using
          (Ty.subst0_subst_commute motiveType Ty.bool
            RawTerm.boolTrue sigma)
      have elseTypeEq :
          (motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma =
            substitutedMotiveType.subst0 Ty.bool RawTerm.boolFalse := by
        simpa [substitutedMotiveType] using
          (Ty.subst0_subst_commute motiveType Ty.bool
            RawTerm.boolFalse sigma)
      have firstResultEq :
          (motiveType.subst0 Ty.bool scrutFirstRaw).subst sigma =
            substitutedMotiveType.subst0 Ty.bool
              (scrutFirstRaw.subst sigma.forRaw) := by
        simpa [substitutedMotiveType] using
          (Ty.subst0_subst_commute motiveType Ty.bool
            scrutFirstRaw sigma)
      have secondResultEq :
          (motiveType.subst0 Ty.bool scrutSecondRaw).subst sigma =
            substitutedMotiveType.subst0 Ty.bool
              (scrutSecondRaw.subst sigma.forRaw) := by
        simpa [substitutedMotiveType] using
          (Ty.subst0_subst_commute motiveType Ty.bool
            scrutSecondRaw sigma)
      have inner :
          ConvCumulHomo
            (Term.boolElim
              (motiveType := substitutedMotiveType)
              (Term.subst termSubst scrutFirst)
              (thenTypeEq ▸ Term.subst termSubst thenFirst)
              (elseTypeEq ▸ Term.subst termSubst elseFirst))
            (Term.boolElim
              (motiveType := substitutedMotiveType)
              (Term.subst termSubst scrutSecond)
              (thenTypeEq ▸ Term.subst termSubst thenSecond)
              (elseTypeEq ▸ Term.subst termSubst elseSecond)) :=
        ConvCumulHomo.boolElimCong
          (motiveType := substitutedMotiveType)
          (ihS termSubst)
          (ConvCumulHomo.cast_eq_both thenTypeEq (ihT termSubst))
          (ConvCumulHomo.cast_eq_both elseTypeEq (ihE termSubst))
      exact ConvCumulHomo.cast_eq_indep
        firstResultEq.symm secondResultEq.symm inner
  | natElimCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natElimCong (ihS _) (ihZ _) (ihK _)
  | natRecCong _ _ _ ihS ihZ ihK =>
      intros; exact ConvCumulHomo.natRecCong (ihS _) (ihZ _) (ihK _)
  | listElimCong _ _ _ ihS ihN ihC =>
      intros; exact ConvCumulHomo.listElimCong (ihS _) (ihN _) (ihC _)
  | optionMatchCong _ _ _ ihS ihN ihM =>
      intros; exact ConvCumulHomo.optionMatchCong (ihS _) (ihN _) (ihM _)
  | eitherMatchCong _ _ _ ihS ihL ihR =>
      intros; exact ConvCumulHomo.eitherMatchCong (ihS _) (ihL _) (ihR _)
  | natSuccCong _ ih => intros; exact ConvCumulHomo.natSuccCong (ih _)
  | listConsCong _ _ ihH ihT => intros; exact ConvCumulHomo.listConsCong (ihH _) (ihT _)
  | optionSomeCong _ ih => intros; exact ConvCumulHomo.optionSomeCong (ih _)
  | eitherInlCong _ ih => intros; exact ConvCumulHomo.eitherInlCong (ih _)
  | eitherInrCong _ ih => intros; exact ConvCumulHomo.eitherInrCong (ih _)
  | idJCong _ _ ihB ihW => intros; exact ConvCumulHomo.idJCong (ihB _) (ihW _)
  | modIntroCong _ ih => intros; exact ConvCumulHomo.modIntroCong (ih _)
  | modElimCong _ ih => intros; exact ConvCumulHomo.modElimCong (ih _)
  | subsumeCong _ ih => intros; exact ConvCumulHomo.subsumeCong (ih _)
  | cumulUpCong lowerLevel higherLevel cumulMonotone
                levelLeLow levelLeHigh _ ih =>
      -- Phase CUMUL-2.6 Design D: Term.{rename,subst}'s cumulUp arm
      -- recurses on typeCode.  IH provides the substituted inner
      -- relation; ConvCumulHomo.cumulUpCong rebuilds at target ctx.
      intros _ _ _ context4
      exact ConvCumulHomo.cumulUpCong lowerLevel higherLevel cumulMonotone
                                      levelLeLow levelLeHigh
                                      (ih context4)

end LeanFX2
