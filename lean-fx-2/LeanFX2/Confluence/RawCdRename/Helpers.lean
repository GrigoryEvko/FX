import LeanFX2.Confluence.RawCd.Core
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer

namespace LeanFX2

/-! ## Helper-rename lemma 1 of 17: cdAppCase. -/

/-- `cdAppCase` commutes with `rename`: developing the head of an
application before renaming yields the same result as developing it
after renaming.  The β arm uses `subst0_rename_commute`; the 66
other arms close by `rfl` because `rename` is homomorphic over each
outer ctor and `cdAppCase` falls through to `RawTerm.app`. -/
theorem RawTerm.cdAppCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedFunction developedArgument : RawTerm sourceScope) :
    (RawTerm.cdAppCase developedFunction developedArgument).rename rho =
    RawTerm.cdAppCase (developedFunction.rename rho)
      (developedArgument.rename rho) := by
  cases developedFunction
  case lam body =>
      show (body.subst0 developedArgument).rename rho =
           (body.rename rho.lift).subst0 (developedArgument.rename rho)
      exact RawTerm.subst0_rename_commute body developedArgument rho
  all_goals rfl

/-! ## Helper-rename lemma 2 of 17: cdPathAppCase. -/

/-- `cdPathAppCase` commutes with `rename`.  The β arm uses
`subst0_rename_commute`; all other arms fall through to
`pathApp _ _` and close by `rfl`. -/
theorem RawTerm.cdPathAppCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedPath developedInterval : RawTerm sourceScope) :
    (RawTerm.cdPathAppCase developedPath developedInterval).rename rho =
    RawTerm.cdPathAppCase (developedPath.rename rho)
      (developedInterval.rename rho) := by
  cases developedPath
  case pathLam body =>
      show (body.subst0 developedInterval).rename rho =
           (body.rename rho.lift).subst0 (developedInterval.rename rho)
      exact RawTerm.subst0_rename_commute body developedInterval rho
  all_goals rfl

/-! ## Helper-rename lemma 3 of 17: cdGlueElimCase.

The β arm `glueIntro base _ => base` projects an unsubstituted
subterm; `rename` distributes through `glueIntro` and the projection
commutes by `rfl`.  Pilot for the simpler `cases <;> rfl` shape. -/

/-- `cdGlueElimCase` commutes with `rename`. -/
theorem RawTerm.cdGlueElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedGlued : RawTerm sourceScope) :
    (RawTerm.cdGlueElimCase developedGlued).rename rho =
    RawTerm.cdGlueElimCase (developedGlued.rename rho) := by
  cases developedGlued <;> rfl

/-! ## Helper-rename lemma 4 of 17: cdModElimCase. -/

/-- `cdModElimCase` commutes with `rename`. -/
theorem RawTerm.cdModElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedInner : RawTerm sourceScope) :
    (RawTerm.cdModElimCase developedInner).rename rho =
    RawTerm.cdModElimCase (developedInner.rename rho) := by
  cases developedInner <;> rfl

/-! ## Helper-rename lemma 5 of 17: cdRefineElimCase. -/

/-- `cdRefineElimCase` commutes with `rename`. -/
theorem RawTerm.cdRefineElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedRefined : RawTerm sourceScope) :
    (RawTerm.cdRefineElimCase developedRefined).rename rho =
    RawTerm.cdRefineElimCase (developedRefined.rename rho) := by
  cases developedRefined <;> rfl

/-! ## Helper-rename lemma 6 of 17: cdRecordProjCase. -/

/-- `cdRecordProjCase` commutes with `rename`. -/
theorem RawTerm.cdRecordProjCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedRecord : RawTerm sourceScope) :
    (RawTerm.cdRecordProjCase developedRecord).rename rho =
    RawTerm.cdRecordProjCase (developedRecord.rename rho) := by
  cases developedRecord <;> rfl

/-! ## Helper-rename lemma 7 of 17: cdCodataDestCase. -/

/-- `cdCodataDestCase` commutes with `rename`. -/
theorem RawTerm.cdCodataDestCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedCodata : RawTerm sourceScope) :
    (RawTerm.cdCodataDestCase developedCodata).rename rho =
    RawTerm.cdCodataDestCase (developedCodata.rename rho) := by
  cases developedCodata <;> rfl

/-! ## Helper-rename lemma 8 of 17: cdFstCase. -/

/-- `cdFstCase` commutes with `rename`. -/
theorem RawTerm.cdFstCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedPair : RawTerm sourceScope) :
    (RawTerm.cdFstCase developedPair).rename rho =
    RawTerm.cdFstCase (developedPair.rename rho) := by
  cases developedPair <;> rfl

/-! ## Helper-rename lemma 9 of 17: cdSndCase. -/

/-- `cdSndCase` commutes with `rename`. -/
theorem RawTerm.cdSndCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedPair : RawTerm sourceScope) :
    (RawTerm.cdSndCase developedPair).rename rho =
    RawTerm.cdSndCase (developedPair.rename rho) := by
  cases developedPair <;> rfl

/-! ## Helper-rename lemma 10 of 17: cdBoolElimCase. -/

/-- `cdBoolElimCase` commutes with `rename`.  Two β arms (true/false)
both project a developed branch; `rename` distributes through
`boolTrue` / `boolFalse` (both atomic), so all 67 arms close by `rfl`. -/
theorem RawTerm.cdBoolElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedThen developedElse : RawTerm sourceScope) :
    (RawTerm.cdBoolElimCase developedScrutinee developedThen developedElse).rename rho =
    RawTerm.cdBoolElimCase (developedScrutinee.rename rho)
      (developedThen.rename rho) (developedElse.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 11 of 17: cdNatElimCase. -/

/-- `cdNatElimCase` commutes with `rename`.  Two β arms (zero / succ);
the succ arm constructs `app developedSucc predecessor` and `rename`
distributes through `app` and `natSucc` so all arms close by `rfl`. -/
theorem RawTerm.cdNatElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedZero developedSucc : RawTerm sourceScope) :
    (RawTerm.cdNatElimCase developedScrutinee developedZero developedSucc).rename rho =
    RawTerm.cdNatElimCase (developedScrutinee.rename rho)
      (developedZero.rename rho) (developedSucc.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 12 of 17: cdNatRecCase. -/

/-- `cdNatRecCase` commutes with `rename`.  Two β arms; the succ arm
constructs `app (app developedSucc predecessor) (natRec ...)` which
`rename` distributes through trivially. -/
theorem RawTerm.cdNatRecCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedZero developedSucc : RawTerm sourceScope) :
    (RawTerm.cdNatRecCase developedScrutinee developedZero developedSucc).rename rho =
    RawTerm.cdNatRecCase (developedScrutinee.rename rho)
      (developedZero.rename rho) (developedSucc.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 13 of 17: cdListElimCase. -/

/-- `cdListElimCase` commutes with `rename`. -/
theorem RawTerm.cdListElimCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedNil developedCons : RawTerm sourceScope) :
    (RawTerm.cdListElimCase developedScrutinee developedNil developedCons).rename rho =
    RawTerm.cdListElimCase (developedScrutinee.rename rho)
      (developedNil.rename rho) (developedCons.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 14 of 17: cdOptionMatchCase. -/

/-- `cdOptionMatchCase` commutes with `rename`. -/
theorem RawTerm.cdOptionMatchCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedNone developedSome : RawTerm sourceScope) :
    (RawTerm.cdOptionMatchCase developedScrutinee developedNone developedSome).rename rho =
    RawTerm.cdOptionMatchCase (developedScrutinee.rename rho)
      (developedNone.rename rho) (developedSome.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 15 of 17: cdEitherMatchCase. -/

/-- `cdEitherMatchCase` commutes with `rename`. -/
theorem RawTerm.cdEitherMatchCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedScrutinee developedLeft developedRight : RawTerm sourceScope) :
    (RawTerm.cdEitherMatchCase developedScrutinee developedLeft developedRight).rename rho =
    RawTerm.cdEitherMatchCase (developedScrutinee.rename rho)
      (developedLeft.rename rho) (developedRight.rename rho) := by
  cases developedScrutinee <;> rfl

/-! ## Helper-rename lemma 16 of 17: cdIdJCase. -/

/-- `cdIdJCase` commutes with `rename`. -/
theorem RawTerm.cdIdJCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedBase developedWitness : RawTerm sourceScope) :
    (RawTerm.cdIdJCase developedBase developedWitness).rename rho =
    RawTerm.cdIdJCase (developedBase.rename rho) (developedWitness.rename rho) := by
  cases developedWitness <;> rfl

/-! ## Helper-rename lemma 17 of 17: cdIdStrictRecCase. -/

/-- `cdIdStrictRecCase` commutes with `rename`. -/
theorem RawTerm.cdIdStrictRecCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedBase developedWitness : RawTerm sourceScope) :
    (RawTerm.cdIdStrictRecCase developedBase developedWitness).rename rho =
    RawTerm.cdIdStrictRecCase (developedBase.rename rho) (developedWitness.rename rho) := by
  cases developedWitness <;> rfl

/-! ## Helper-rename lemma 19 of 19: cdIdToEquivCase.

The `refl` arm produces a CLOSED term (`equivIntro (lam (var 0))
(lam (var 0))`) which equals its own rename.  All 67 non-refl arms
rebuild as plain `idToEquiv` and close by `rfl`. -/

/-- `cdIdToEquivCase` commutes with `rename`.  Closed-target arm:
when `developedProof = refl _`, both sides reduce to
`equivIntro (lam (var 0)) (lam (var 0))` because the contractum is
closed (no free variables — only the binder-bound `var 0`).  All
other arms rebuild `idToEquiv developedProof` and rename
distributes. -/
theorem RawTerm.cdIdToEquivCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedProof : RawTerm sourceScope) :
    (RawTerm.cdIdToEquivCase developedProof).rename rho =
    RawTerm.cdIdToEquivCase (developedProof.rename rho) := by
  cases developedProof <;> rfl

/-! ## D3.6-S6 helper-rename lemmas 20 + 21:
`cdUaToEquivApplyCase` + `cdEquivApplyCase`. -/

/-- `cdUaToEquivApplyCase` commutes with `rename`.  When the inner
proof is `oeqRefl _`, both sides reduce to `developedArg.rename rho`
(the contractum is just the developed source, which renames
distributively).  All other arms rebuild
`equivApply (uaToEquiv proof) developedArg` and rename
distributes. -/
theorem RawTerm.cdUaToEquivApplyCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (proof developedArg : RawTerm sourceScope) :
    (RawTerm.cdUaToEquivApplyCase proof developedArg).rename rho =
    RawTerm.cdUaToEquivApplyCase (proof.rename rho) (developedArg.rename rho) := by
  cases proof <;> rfl

/-- `cdEquivApplyCase` commutes with `rename`.  The `uaToEquiv` arm
dispatches through `cdUaToEquivApplyCase`; rename commutes via the
above lemma.  All other 66 arms rebuild as plain `equivApply` cong
and close by `rfl`. -/
theorem RawTerm.cdEquivApplyCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedEquiv developedArg : RawTerm sourceScope) :
    (RawTerm.cdEquivApplyCase developedEquiv developedArg).rename rho =
    RawTerm.cdEquivApplyCase (developedEquiv.rename rho)
      (developedArg.rename rho) := by
  cases developedEquiv
  case uaToEquiv proof =>
      show (RawTerm.cdUaToEquivApplyCase proof developedArg).rename rho =
           RawTerm.cdUaToEquivApplyCase (proof.rename rho)
             (developedArg.rename rho)
      exact RawTerm.cdUaToEquivApplyCase_rename rho proof developedArg
  all_goals rfl

/-! ## Helper-rename lemma 18 of 18: cdTranspCase.

The `pathLam` arm dispatches on `unweaken? pathBody`; both branches
are aligned via `RawTerm.unweaken?_rename_lift_commute` plus a case
split on `unweaken? pathBody`.  The 66 non-pathLam ctors all rebuild
as plain `transp` cong and close by `rfl`. -/

/-- `cdTranspCase` commutes with `rename`.  The pathLam case splits
on `unweaken? pathBody`: when `some inner`, both sides reduce to
`developedSource.rename rho` (using `weaken_rename_commute` and
`unweaken?_weaken`); when `none`, both sides reduce to
`transp (pathLam (pathBody.rename rho.lift)) (developedSource.rename rho)`
(using the commute lemma to align the dispatch). -/
theorem RawTerm.cdTranspCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedPath developedSource : RawTerm sourceScope) :
    (RawTerm.cdTranspCase developedPath developedSource).rename rho =
    RawTerm.cdTranspCase (developedPath.rename rho)
      (developedSource.rename rho) := by
  cases developedPath
  case pathLam pathBody =>
      show ((match RawTerm.unweaken? pathBody with
              | some _ => developedSource
              | none =>
                  RawTerm.transp (RawTerm.pathLam pathBody) developedSource).rename rho) =
           (match RawTerm.unweaken? (pathBody.rename rho.lift) with
              | some _ => developedSource.rename rho
              | none =>
                  RawTerm.transp (RawTerm.pathLam (pathBody.rename rho.lift))
                    (developedSource.rename rho))
      rw [RawTerm.unweaken?_rename_lift_commute pathBody rho]
      cases hUnwk : RawTerm.unweaken? pathBody with
      | some _ => rfl
      | none => rfl
  all_goals rfl

/-- `cdTranspPiCase` commutes with `rename`.  The dispatch on
`matchTranspPiBetaShape? pathBody` splits two ways: when `some
(innerDomain, codomainCode)`, both sides reduce to
`transpPiBetaContractum (codomainCode.rename rho.lift.lift)
(developedSource.rename rho)` via `transpPiBetaContractum_rename`;
when `none`, both sides reduce to `transp (pathLam (pathBody.rename
rho.lift)) (developedSource.rename rho)` definitionally.  Bridges
via `matchTranspPiBetaShape?_rename` to align the recognizer-image
on each side of the equation. -/
theorem RawTerm.cdTranspPiCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (pathBody : RawTerm (sourceScope + 1))
    (developedSource : RawTerm sourceScope) :
    (RawTerm.cdTranspPiCase pathBody developedSource).rename rho =
    RawTerm.cdTranspPiCase (pathBody.rename rho.lift)
      (developedSource.rename rho) := by
  show ((match RawTerm.matchTranspPiBetaShape? pathBody with
          | some (_, codomainCode) =>
              RawTerm.transpPiBetaContractum codomainCode developedSource
          | none =>
              RawTerm.transp (RawTerm.pathLam pathBody) developedSource).rename rho) =
       (match RawTerm.matchTranspPiBetaShape? (pathBody.rename rho.lift) with
          | some (_, codomainCode) =>
              RawTerm.transpPiBetaContractum codomainCode (developedSource.rename rho)
          | none =>
              RawTerm.transp (RawTerm.pathLam (pathBody.rename rho.lift))
                (developedSource.rename rho))
  rw [RawTerm.matchTranspPiBetaShape?_rename rho pathBody]
  cases RawTerm.matchTranspPiBetaShape? pathBody with
  | none => rfl
  | some pair =>
      exact RawTerm.transpPiBetaContractum_rename rho pair.2 developedSource

/-- `cdHcompCase` commutes with `rename`.  Structurally identical to
`cdTranspCase_rename` modulo `transp ↔ hcomp` and `developedSource ↔
developedCap`.  The pathLam case splits on `unweaken? sidesBody`:
when `some inner`, both sides reduce to `developedCap.rename rho`;
when `none`, both sides reduce to
`hcomp (pathLam (sidesBody.rename rho.lift)) (developedCap.rename rho)`
(using `unweaken?_rename_lift_commute` to align the dispatch). -/
theorem RawTerm.cdHcompCase_rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (developedSides developedCap : RawTerm sourceScope) :
    (RawTerm.cdHcompCase developedSides developedCap).rename rho =
    RawTerm.cdHcompCase (developedSides.rename rho)
      (developedCap.rename rho) := by
  cases developedSides
  case pathLam sidesBody =>
      show ((match RawTerm.unweaken? sidesBody with
              | some _ => developedCap
              | none => RawTerm.hcomp (RawTerm.pathLam sidesBody) developedCap).rename rho) =
           (match RawTerm.unweaken? (sidesBody.rename rho.lift) with
              | some _ => developedCap.rename rho
              | none => RawTerm.hcomp (RawTerm.pathLam (sidesBody.rename rho.lift))
                          (developedCap.rename rho))
      rw [RawTerm.unweaken?_rename_lift_commute sidesBody rho]
      cases RawTerm.unweaken? sidesBody <;> rfl
  all_goals rfl

end LeanFX2
