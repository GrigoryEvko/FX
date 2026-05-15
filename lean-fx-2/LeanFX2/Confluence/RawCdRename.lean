import LeanFX2.Confluence.RawCd
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer

/-! # Confluence/RawCdRename — `cd` commutes with `rename`.

Headline: `RawTerm.cd_rename : (RawTerm.cd term).rename rho = RawTerm.cd (term.rename rho)`.

Proof shape: 67-arm structural induction on `term`.  Most arms
are pure cong and close by rewriting with the IH on subterms.
The redex-bearing arms (app / pathApp / fst / snd / boolElim /
natElim / natRec / listElim / optionMatch / eitherMatch / glueElim
/ refineElim / recordProj / codataDest / idJ / idStrictRec /
modElim) dispatch to a per-redex helper (cdAppCase, cdFstCase,
...) — each helper is rename-stable per its own helper lemma below.

## Why we need this

The cd cascade extension for `transpReflBeta` (D2.5.4) requires
`unweaken? (cd typeRaw.weaken) = some (cd typeRaw)` so that
`cdTranspCase` can recognize a developed constant pathLam and fire
the β reduction.  The composition decomposes as:

  unweaken? (cd typeRaw.weaken)
    = unweaken? ((cd typeRaw).weaken)        [cd_weaken corollary]
    = some (cd typeRaw)                       [unweaken?_weaken]

`cd_weaken` is the specialization to `RawRenaming.weaken`.

## Helper-rename lemma menu

Each cd-helper splits on its developed-function/path's outer ctor.
The redex arm fires `subst0` (closed by `subst0_rename_commute`);
the 66 cong fall-through arms close by `rfl` because rename is
homomorphic over each ctor.

  * `cdAppCase_rename`        — app/lam β
  * `cdPathAppCase_rename`    — pathApp/pathLam β
  * `cdFstCase_rename`        — fst/pair β
  * `cdSndCase_rename`        — snd/pair β
  * `cdGlueElimCase_rename`   — glueElim/glueIntro β
  * `cdRefineElimCase_rename` — refineElim/refineIntro β
  * `cdRecordProjCase_rename` — recordProj/recordIntro β
  * `cdCodataDestCase_rename` — codataDest/codataUnfold ι
  * `cdBoolElimCase_rename`   — boolElim/boolTrue/boolFalse ι
  * `cdNatElimCase_rename`    — natElim/natZero/natSucc ι
  * `cdNatRecCase_rename`     — natRec/natZero/natSucc ι
  * `cdListElimCase_rename`   — listElim/listNil/listCons ι
  * `cdOptionMatchCase_rename` — optionMatch/optionNone/optionSome ι
  * `cdEitherMatchCase_rename` — eitherMatch/eitherInl/eitherInr ι
  * `cdIdJCase_rename`        — idJ/refl ι
  * `cdIdStrictRecCase_rename` — idStrictRec/idStrictRefl ι
  * `cdModElimCase_rename`    — modElim/modIntro/subsume ι

Total 17 helper lemmas.  The main `cd_rename` theorem composes them.
-/

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

/-! ## Main theorem: `cd` commutes with `rename`.

Structural induction on `term`.  Atomic ctors close by `rfl`; pure
cong ctors rewrite via the appropriate IH; helper-using ctors invoke
the matching `cd<Helper>Case_rename` lemma above and then unfold cd
+ rewrite IHs.

Modeled on `RawTerm.rename_compose` (`Foundation/RawSubst.lean:375`)
— same induction shape, same case enumeration, plus an extra
helper-rename rewrite step for the 17 redex-bearing ctors. -/

theorem RawTerm.cd_rename {sourceScope : Nat} (term : RawTerm sourceScope) :
    ∀ {targetScope : Nat} (rho : RawRenaming sourceScope targetScope),
      (RawTerm.cd term).rename rho = RawTerm.cd (term.rename rho) := by
  induction term with
  | var position => intro _ _; rfl
  | unit => intro _ _; rfl
  | lam body bodyIH =>
      intro _ rho
      show (RawTerm.lam (RawTerm.cd body)).rename rho =
           RawTerm.cd (RawTerm.lam (body.rename rho.lift))
      simp only [RawTerm.rename, RawTerm.cd]
      exact congrArg RawTerm.lam (bodyIH rho.lift)
  | app fn arg fnIH argIH =>
      intro _ rho
      show (RawTerm.cdAppCase (RawTerm.cd fn) (RawTerm.cd arg)).rename rho =
           RawTerm.cd (RawTerm.app (fn.rename rho) (arg.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdAppCase_rename rho (RawTerm.cd fn) (RawTerm.cd arg),
          fnIH rho, argIH rho]
  | pair fv sv fvIH svIH =>
      intro _ rho
      show (RawTerm.pair (RawTerm.cd fv) (RawTerm.cd sv)).rename rho =
           RawTerm.cd (RawTerm.pair (fv.rename rho) (sv.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [fvIH rho, svIH rho]
  | fst pairTerm pairIH =>
      intro _ rho
      show (RawTerm.cdFstCase (RawTerm.cd pairTerm)).rename rho =
           RawTerm.cd (RawTerm.fst (pairTerm.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdFstCase_rename rho (RawTerm.cd pairTerm), pairIH rho]
  | snd pairTerm pairIH =>
      intro _ rho
      show (RawTerm.cdSndCase (RawTerm.cd pairTerm)).rename rho =
           RawTerm.cd (RawTerm.snd (pairTerm.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdSndCase_rename rho (RawTerm.cd pairTerm), pairIH rho]
  | boolTrue => intro _ _; rfl
  | boolFalse => intro _ _; rfl
  | boolElim s t e sIH tIH eIH =>
      intro _ rho
      show (RawTerm.cdBoolElimCase (RawTerm.cd s) (RawTerm.cd t) (RawTerm.cd e)).rename rho =
           RawTerm.cd (RawTerm.boolElim (s.rename rho) (t.rename rho) (e.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdBoolElimCase_rename rho (RawTerm.cd s) (RawTerm.cd t) (RawTerm.cd e),
          sIH rho, tIH rho, eIH rho]
  | natZero => intro _ _; rfl
  | natSucc p pIH =>
      intro _ rho
      show (RawTerm.natSucc (RawTerm.cd p)).rename rho =
           RawTerm.cd (RawTerm.natSucc (p.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [pIH rho]
  | natElim s z c sIH zIH cIH =>
      intro _ rho
      show (RawTerm.cdNatElimCase (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.natElim (s.rename rho) (z.rename rho) (c.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdNatElimCase_rename rho (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c),
          sIH rho, zIH rho, cIH rho]
  | natRec s z c sIH zIH cIH =>
      intro _ rho
      show (RawTerm.cdNatRecCase (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.natRec (s.rename rho) (z.rename rho) (c.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdNatRecCase_rename rho (RawTerm.cd s) (RawTerm.cd z) (RawTerm.cd c),
          sIH rho, zIH rho, cIH rho]
  | listNil => intro _ _; rfl
  | listCons h t hIH tIH =>
      intro _ rho
      show (RawTerm.listCons (RawTerm.cd h) (RawTerm.cd t)).rename rho =
           RawTerm.cd (RawTerm.listCons (h.rename rho) (t.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [hIH rho, tIH rho]
  | listElim s n c sIH nIH cIH =>
      intro _ rho
      show (RawTerm.cdListElimCase (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.listElim (s.rename rho) (n.rename rho) (c.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdListElimCase_rename rho (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c),
          sIH rho, nIH rho, cIH rho]
  | optionNone => intro _ _; rfl
  | optionSome v vIH =>
      intro _ rho
      show (RawTerm.optionSome (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.optionSome (v.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | optionMatch s n c sIH nIH cIH =>
      intro _ rho
      show (RawTerm.cdOptionMatchCase (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c)).rename rho =
           RawTerm.cd (RawTerm.optionMatch (s.rename rho) (n.rename rho) (c.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdOptionMatchCase_rename rho (RawTerm.cd s) (RawTerm.cd n) (RawTerm.cd c),
          sIH rho, nIH rho, cIH rho]
  | eitherInl v vIH =>
      intro _ rho
      show (RawTerm.eitherInl (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.eitherInl (v.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | eitherInr v vIH =>
      intro _ rho
      show (RawTerm.eitherInr (RawTerm.cd v)).rename rho =
           RawTerm.cd (RawTerm.eitherInr (v.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [vIH rho]
  | eitherMatch s l r sIH lIH rIH =>
      intro _ rho
      show (RawTerm.cdEitherMatchCase (RawTerm.cd s) (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.eitherMatch (s.rename rho) (l.rename rho) (r.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdEitherMatchCase_rename rho (RawTerm.cd s) (RawTerm.cd l) (RawTerm.cd r),
          sIH rho, lIH rho, rIH rho]
  | refl witness witnessIH =>
      intro _ rho
      show (RawTerm.refl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.refl (witness.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | idJ base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.cdIdJCase (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idJ (base.rename rho) (witness.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdIdJCase_rename rho (RawTerm.cd base) (RawTerm.cd witness),
          baseIH rho, witnessIH rho]
  | modIntro inner innerIH =>
      intro _ rho
      show (RawTerm.modIntro (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.modIntro (inner.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | modElim inner innerIH =>
      intro _ rho
      show (RawTerm.cdModElimCase (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.modElim (inner.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdModElimCase_rename rho (RawTerm.cd inner), innerIH rho]
  | subsume inner innerIH =>
      intro _ rho
      show (RawTerm.subsume (RawTerm.cd inner)).rename rho =
           RawTerm.cd (RawTerm.subsume (inner.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | interval0 => intro _ _; rfl
  | interval1 => intro _ _; rfl
  | intervalOpp i iIH =>
      intro _ rho
      show (RawTerm.intervalOpp (RawTerm.cd i)).rename rho =
           RawTerm.cd (RawTerm.intervalOpp (i.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [iIH rho]
  | intervalMeet l r lIH rIH =>
      intro _ rho
      show (RawTerm.intervalMeet (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.intervalMeet (l.rename rho) (r.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [lIH rho, rIH rho]
  | intervalJoin l r lIH rIH =>
      intro _ rho
      show (RawTerm.intervalJoin (RawTerm.cd l) (RawTerm.cd r)).rename rho =
           RawTerm.cd (RawTerm.intervalJoin (l.rename rho) (r.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [lIH rho, rIH rho]
  | pathLam body bodyIH =>
      intro _ rho
      show (RawTerm.pathLam (RawTerm.cd body)).rename rho =
           RawTerm.cd (RawTerm.pathLam (body.rename rho.lift))
      simp only [RawTerm.rename, RawTerm.cd]
      exact congrArg RawTerm.pathLam (bodyIH rho.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro _ rho
      show (RawTerm.cdPathAppCase (RawTerm.cd pathTerm) (RawTerm.cd intervalArg)).rename rho =
           RawTerm.cd (RawTerm.pathApp (pathTerm.rename rho) (intervalArg.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdPathAppCase_rename rho (RawTerm.cd pathTerm) (RawTerm.cd intervalArg),
          pathIH rho, intervalIH rho]
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro _ rho
      show (RawTerm.glueIntro (RawTerm.cd baseValue) (RawTerm.cd partialValue)).rename rho =
           RawTerm.cd (RawTerm.glueIntro (baseValue.rename rho) (partialValue.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [baseIH rho, partialIH rho]
  | glueElim gluedValue gluedIH =>
      intro _ rho
      show (RawTerm.cdGlueElimCase (RawTerm.cd gluedValue)).rename rho =
           RawTerm.cd (RawTerm.glueElim (gluedValue.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdGlueElimCase_rename rho (RawTerm.cd gluedValue), gluedIH rho]
  | transp pathTerm sourceTerm pathIH sourceIH =>
      intro _ rho
      show (RawTerm.cdTranspCase (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm)).rename rho =
           RawTerm.cd (RawTerm.transp (pathTerm.rename rho) (sourceTerm.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdTranspCase_rename rho (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm),
          pathIH rho, sourceIH rho]
  | hcomp sides cap sidesIH capIH =>
      intro _ rho
      show (RawTerm.cdHcompCase (RawTerm.cd sides) (RawTerm.cd cap)).rename rho =
           RawTerm.cd (RawTerm.hcomp (sides.rename rho) (cap.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdHcompCase_rename rho (RawTerm.cd sides) (RawTerm.cd cap),
          sidesIH rho, capIH rho]
  | oeqRefl witness witnessIH =>
      intro _ rho
      show (RawTerm.oeqRefl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.oeqRefl (witness.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | oeqJ base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.oeqJ (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.oeqJ (base.rename rho) (witness.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [baseIH rho, witnessIH rho]
  | oeqFunext pointwise pointwiseIH =>
      intro _ rho
      show (RawTerm.oeqFunext (RawTerm.cd pointwise)).rename rho =
           RawTerm.cd (RawTerm.oeqFunext (pointwise.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [pointwiseIH rho]
  | idStrictRefl witness witnessIH =>
      intro _ rho
      show (RawTerm.idStrictRefl (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idStrictRefl (witness.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [witnessIH rho]
  | idStrictRec base witness baseIH witnessIH =>
      intro _ rho
      show (RawTerm.cdIdStrictRecCase (RawTerm.cd base) (RawTerm.cd witness)).rename rho =
           RawTerm.cd (RawTerm.idStrictRec (base.rename rho) (witness.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdIdStrictRecCase_rename rho (RawTerm.cd base) (RawTerm.cd witness),
          baseIH rho, witnessIH rho]
  | equivIntro fwd bwd fwdIH bwdIH =>
      intro _ rho
      show (RawTerm.equivIntro (RawTerm.cd fwd) (RawTerm.cd bwd)).rename rho =
           RawTerm.cd (RawTerm.equivIntro (fwd.rename rho) (bwd.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [fwdIH rho, bwdIH rho]
  | equivApp equivTerm argument equivIH argIH =>
      intro _ rho
      show (RawTerm.equivApp (RawTerm.cd equivTerm) (RawTerm.cd argument)).rename rho =
           RawTerm.cd (RawTerm.equivApp (equivTerm.rename rho) (argument.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [equivIH rho, argIH rho]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      intro _ rho
      show (RawTerm.refineIntro (RawTerm.cd rawValue) (RawTerm.cd predicateProof)).rename rho =
           RawTerm.cd (RawTerm.refineIntro (rawValue.rename rho) (predicateProof.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [valueIH rho, proofIH rho]
  | refineElim refinedValue refinedIH =>
      intro _ rho
      show (RawTerm.cdRefineElimCase (RawTerm.cd refinedValue)).rename rho =
           RawTerm.cd (RawTerm.refineElim (refinedValue.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdRefineElimCase_rename rho (RawTerm.cd refinedValue), refinedIH rho]
  | recordIntro firstField firstIH =>
      intro _ rho
      show (RawTerm.recordIntro (RawTerm.cd firstField)).rename rho =
           RawTerm.cd (RawTerm.recordIntro (firstField.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho]
  | recordProj recordValue recordIH =>
      intro _ rho
      show (RawTerm.cdRecordProjCase (RawTerm.cd recordValue)).rename rho =
           RawTerm.cd (RawTerm.recordProj (recordValue.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdRecordProjCase_rename rho (RawTerm.cd recordValue), recordIH rho]
  | codataUnfold initialState transition stateIH transIH =>
      intro _ rho
      show (RawTerm.codataUnfold (RawTerm.cd initialState) (RawTerm.cd transition)).rename rho =
           RawTerm.cd (RawTerm.codataUnfold (initialState.rename rho) (transition.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [stateIH rho, transIH rho]
  | codataDest codataValue codataIH =>
      intro _ rho
      show (RawTerm.cdCodataDestCase (RawTerm.cd codataValue)).rename rho =
           RawTerm.cd (RawTerm.codataDest (codataValue.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdCodataDestCase_rename rho (RawTerm.cd codataValue), codataIH rho]
  | sessionSend channel payload chIH payloadIH =>
      intro _ rho
      show (RawTerm.sessionSend (RawTerm.cd channel) (RawTerm.cd payload)).rename rho =
           RawTerm.cd (RawTerm.sessionSend (channel.rename rho) (payload.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [chIH rho, payloadIH rho]
  | sessionRecv channel chIH =>
      intro _ rho
      show (RawTerm.sessionRecv (RawTerm.cd channel)).rename rho =
           RawTerm.cd (RawTerm.sessionRecv (channel.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [chIH rho]
  | effectPerform operationTag arguments tagIH argsIH =>
      intro _ rho
      show (RawTerm.effectPerform (RawTerm.cd operationTag) (RawTerm.cd arguments)).rename rho =
           RawTerm.cd (RawTerm.effectPerform (operationTag.rename rho) (arguments.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [tagIH rho, argsIH rho]
  | universeCode innerLevel => intro _ _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.arrowCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.arrowCode (domainCode.rename rho) (codomainCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.piTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.piTyCode (domainCode.rename rho) (codomainCode.rename rho.lift))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho.lift]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro _ rho
      show (RawTerm.sigmaTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)).rename rho =
           RawTerm.cd (RawTerm.sigmaTyCode (domainCode.rename rho) (codomainCode.rename rho.lift))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [domainIH rho, codomainIH rho.lift]
  | productCode firstCode secondCode firstIH secondIH =>
      intro _ rho
      show (RawTerm.productCode (RawTerm.cd firstCode) (RawTerm.cd secondCode)).rename rho =
           RawTerm.cd (RawTerm.productCode (firstCode.rename rho) (secondCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]
  | sumCode leftCode rightCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.sumCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)).rename rho =
           RawTerm.cd (RawTerm.sumCode (leftCode.rename rho) (rightCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | listCode elementCode elementIH =>
      intro _ rho
      show (RawTerm.listCode (RawTerm.cd elementCode)).rename rho =
           RawTerm.cd (RawTerm.listCode (elementCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [elementIH rho]
  | optionCode elementCode elementIH =>
      intro _ rho
      show (RawTerm.optionCode (RawTerm.cd elementCode)).rename rho =
           RawTerm.cd (RawTerm.optionCode (elementCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [elementIH rho]
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.eitherCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)).rename rho =
           RawTerm.cd (RawTerm.eitherCode (leftCode.rename rho) (rightCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro _ rho
      show (RawTerm.idCode (RawTerm.cd typeCode) (RawTerm.cd leftRaw) (RawTerm.cd rightRaw)).rename rho =
           RawTerm.cd (RawTerm.idCode (typeCode.rename rho) (leftRaw.rename rho) (rightRaw.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [typeIH rho, leftIH rho, rightIH rho]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro _ rho
      show (RawTerm.equivCode (RawTerm.cd leftTypeCode) (RawTerm.cd rightTypeCode)).rename rho =
           RawTerm.cd (RawTerm.equivCode (leftTypeCode.rename rho) (rightTypeCode.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | cumulUpMarker innerCodeRaw innerIH =>
      intro _ rho
      show (RawTerm.cumulUpMarker (RawTerm.cd innerCodeRaw)).rename rho =
           RawTerm.cd (RawTerm.cumulUpMarker (innerCodeRaw.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [innerIH rho]
  | uaToEquiv proofRaw proofIH =>
      intro _ rho
      show (RawTerm.uaToEquiv (RawTerm.cd proofRaw)).rename rho =
           RawTerm.cd (RawTerm.uaToEquiv (proofRaw.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [proofIH rho]
  | equivApply equivRaw argRaw equivIH argIH =>
      intro _ rho
      show (RawTerm.cdEquivApplyCase (RawTerm.cd equivRaw) (RawTerm.cd argRaw)).rename rho =
           RawTerm.cd (RawTerm.equivApply (equivRaw.rename rho) (argRaw.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdEquivApplyCase_rename rho (RawTerm.cd equivRaw) (RawTerm.cd argRaw),
        equivIH rho, argIH rho]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro _ rho
      show (RawTerm.pathCompose (RawTerm.cd leftPathRaw) (RawTerm.cd rightPathRaw)).rename rho =
           RawTerm.cd (RawTerm.pathCompose (leftPathRaw.rename rho)
                                            (rightPathRaw.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [leftIH rho, rightIH rho]
  | idToEquiv proofRaw proofIH =>
      intro _ rho
      show (RawTerm.cdIdToEquivCase (RawTerm.cd proofRaw)).rename rho =
           RawTerm.cd (RawTerm.idToEquiv (proofRaw.rename rho))
      simp only [RawTerm.cd]
      rw [RawTerm.cdIdToEquivCase_rename rho (RawTerm.cd proofRaw),
        proofIH rho]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro _ rho
      show (RawTerm.oeqTrans (RawTerm.cd firstProof) (RawTerm.cd secondProof)).rename rho =
           RawTerm.cd (RawTerm.oeqTrans (firstProof.rename rho)
                                        (secondProof.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro _ rho
      show (RawTerm.equivCompose (RawTerm.cd firstEquiv) (RawTerm.cd secondEquiv)).rename rho =
           RawTerm.cd (RawTerm.equivCompose (firstEquiv.rename rho)
                                            (secondEquiv.rename rho))
      simp only [RawTerm.rename, RawTerm.cd]
      rw [firstIH rho, secondIH rho]

/-! ## Specialization: `cd_weaken`. -/

/-- Specialization of `cd_rename` to weakening: developing the
weakened term equals weakening the developed term.  This is the
load-bearing fact for the `transpReflBeta` cd cascade — together
with `RawTerm.unweaken?_weaken` it gives `unweaken? (cd t.weaken) =
some (cd t)`, recognizing constant-path transp at the cd layer. -/
theorem RawTerm.cd_weaken {scope : Nat} (term : RawTerm scope) :
    RawTerm.cd term.weaken = (RawTerm.cd term).weaken := by
  show RawTerm.cd (term.rename RawRenaming.weaken) =
       (RawTerm.cd term).rename RawRenaming.weaken
  exact (RawTerm.cd_rename term RawRenaming.weaken).symm

/-! ## Corollary: `unweaken? ∘ cd ∘ weaken = some ∘ cd`. -/

/-- The cd cascade's recognizer fact: weakening a term and then
developing makes the weakened structure recoverable via `unweaken?`,
and the recovered preimage is `cd term`.  Closes the chain
`unweaken? (cd t.weaken) = unweaken? (cd t).weaken = some (cd t)`. -/
theorem RawTerm.unweaken?_cd_weaken {scope : Nat} (term : RawTerm scope) :
    RawTerm.unweaken? (RawTerm.cd term.weaken) = some (RawTerm.cd term) := by
  rw [RawTerm.cd_weaken term]
  exact RawTerm.unweaken?_weaken (RawTerm.cd term)

end LeanFX2

