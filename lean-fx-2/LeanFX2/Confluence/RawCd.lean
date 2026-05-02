import LeanFX2.Foundation.RawSubst

/-! # Confluence/RawCd — raw-side complete development

`RawTerm.cd : RawTerm scope → RawTerm scope` produces the maximal
parallel reduct of a raw term: every redex visible at the head fires,
and every subterm is recursively complete-developed.

## Why a raw-side cd

The typed `Term.cd` (Layer 3 / `Confluence/Cd.lean`) carries Ty
indices and HEq casts on β-reduction arms — substantial work to get
right.  The raw side has no type indices, so cd is a clean recursive
definition with no casts.  Combined with `Bridge.lean`'s
`Step.par.toRawBridge`, raw confluence transfers to typed parallel
reductions on the projected raw indices: the bridge guarantees that
typed Step.par chains form raw Step.par chains, and raw confluence
gives a common raw reduct.

This is the ROI play for unblocking confluence work without first
clearing the typed-Term HEq cascade (W7 wall).

## Zero-axiom discipline

Every inner `match` enumerates all 28 `RawTerm` constructors
explicitly — no `_ =>` wildcards — to satisfy AXIOMS.md Layer M
strict-zero-axiom policy.  Per
`feedback_lean_zero_axiom_match.md`, full enumeration over a
non-dependent inductive (RawTerm is Nat-indexed only) keeps the
match compiler from emitting `propext` to discharge the catch-all
redundancy obligation.

## Construction sketch

* Atomic ctors (var, unit, *True/False/Zero/Nil/None) → identity
* Cong ctors (lam, pair, listCons, optionSome, eitherInl/Inr,
  natSucc, refl, modIntro/Elim, subsume) → recurse into subterms
* Redex-bearing ctors (app, fst, snd, boolElim, natElim, natRec,
  listElim, optionMatch, eitherMatch, idJ) → develop subterms,
  then dispatch on the developed scrutinee:
  - canonical ctor → contract
  - any other ctor → reconstruct with developed subterms

Modal ctors `modIntro`, `modElim`, `subsume` are pure cong (no
`iotaModal` rule lives in `RawStep.par` yet; will be added when
Layer 6 ships its modal reduction rules).
-/

namespace LeanFX2

/-- Complete development on raw terms.  Maximal parallel reduct:
every visible redex contracts, every subterm is recursively
developed.  Zero axioms: full enumeration in every inner match
keeps Lean's match compiler from leaking propext. -/
def RawTerm.cd : ∀ {scope : Nat}, RawTerm scope → RawTerm scope
  | _, .var position => RawTerm.var position
  | _, .unit => RawTerm.unit
  | _, .lam body => RawTerm.lam (RawTerm.cd body)
  | _, .app functionTerm argumentTerm =>
      let developedFunction := RawTerm.cd functionTerm
      let developedArgument := RawTerm.cd argumentTerm
      match developedFunction with
      | RawTerm.lam body => body.subst0 developedArgument
      | RawTerm.var _ => RawTerm.app developedFunction developedArgument
      | RawTerm.unit => RawTerm.app developedFunction developedArgument
      | RawTerm.app _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.pair _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.fst _ => RawTerm.app developedFunction developedArgument
      | RawTerm.snd _ => RawTerm.app developedFunction developedArgument
      | RawTerm.boolTrue => RawTerm.app developedFunction developedArgument
      | RawTerm.boolFalse => RawTerm.app developedFunction developedArgument
      | RawTerm.boolElim _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.natZero => RawTerm.app developedFunction developedArgument
      | RawTerm.natSucc _ => RawTerm.app developedFunction developedArgument
      | RawTerm.natElim _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.natRec _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.listNil => RawTerm.app developedFunction developedArgument
      | RawTerm.listCons _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.listElim _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.optionNone => RawTerm.app developedFunction developedArgument
      | RawTerm.optionSome _ => RawTerm.app developedFunction developedArgument
      | RawTerm.optionMatch _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.eitherInl _ => RawTerm.app developedFunction developedArgument
      | RawTerm.eitherInr _ => RawTerm.app developedFunction developedArgument
      | RawTerm.eitherMatch _ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.refl _ => RawTerm.app developedFunction developedArgument
      | RawTerm.idJ _ _ => RawTerm.app developedFunction developedArgument
      | RawTerm.modIntro _ => RawTerm.app developedFunction developedArgument
      | RawTerm.modElim _ => RawTerm.app developedFunction developedArgument
      | RawTerm.subsume _ => RawTerm.app developedFunction developedArgument
  | _, .pair firstValue secondValue =>
      RawTerm.pair (RawTerm.cd firstValue) (RawTerm.cd secondValue)
  | _, .fst pairTerm =>
      let developedPair := RawTerm.cd pairTerm
      match developedPair with
      | RawTerm.pair firstValue _ => firstValue
      | RawTerm.var _ => RawTerm.fst developedPair
      | RawTerm.unit => RawTerm.fst developedPair
      | RawTerm.lam _ => RawTerm.fst developedPair
      | RawTerm.app _ _ => RawTerm.fst developedPair
      | RawTerm.fst _ => RawTerm.fst developedPair
      | RawTerm.snd _ => RawTerm.fst developedPair
      | RawTerm.boolTrue => RawTerm.fst developedPair
      | RawTerm.boolFalse => RawTerm.fst developedPair
      | RawTerm.boolElim _ _ _ => RawTerm.fst developedPair
      | RawTerm.natZero => RawTerm.fst developedPair
      | RawTerm.natSucc _ => RawTerm.fst developedPair
      | RawTerm.natElim _ _ _ => RawTerm.fst developedPair
      | RawTerm.natRec _ _ _ => RawTerm.fst developedPair
      | RawTerm.listNil => RawTerm.fst developedPair
      | RawTerm.listCons _ _ => RawTerm.fst developedPair
      | RawTerm.listElim _ _ _ => RawTerm.fst developedPair
      | RawTerm.optionNone => RawTerm.fst developedPair
      | RawTerm.optionSome _ => RawTerm.fst developedPair
      | RawTerm.optionMatch _ _ _ => RawTerm.fst developedPair
      | RawTerm.eitherInl _ => RawTerm.fst developedPair
      | RawTerm.eitherInr _ => RawTerm.fst developedPair
      | RawTerm.eitherMatch _ _ _ => RawTerm.fst developedPair
      | RawTerm.refl _ => RawTerm.fst developedPair
      | RawTerm.idJ _ _ => RawTerm.fst developedPair
      | RawTerm.modIntro _ => RawTerm.fst developedPair
      | RawTerm.modElim _ => RawTerm.fst developedPair
      | RawTerm.subsume _ => RawTerm.fst developedPair
  | _, .snd pairTerm =>
      let developedPair := RawTerm.cd pairTerm
      match developedPair with
      | RawTerm.pair _ secondValue => secondValue
      | RawTerm.var _ => RawTerm.snd developedPair
      | RawTerm.unit => RawTerm.snd developedPair
      | RawTerm.lam _ => RawTerm.snd developedPair
      | RawTerm.app _ _ => RawTerm.snd developedPair
      | RawTerm.fst _ => RawTerm.snd developedPair
      | RawTerm.snd _ => RawTerm.snd developedPair
      | RawTerm.boolTrue => RawTerm.snd developedPair
      | RawTerm.boolFalse => RawTerm.snd developedPair
      | RawTerm.boolElim _ _ _ => RawTerm.snd developedPair
      | RawTerm.natZero => RawTerm.snd developedPair
      | RawTerm.natSucc _ => RawTerm.snd developedPair
      | RawTerm.natElim _ _ _ => RawTerm.snd developedPair
      | RawTerm.natRec _ _ _ => RawTerm.snd developedPair
      | RawTerm.listNil => RawTerm.snd developedPair
      | RawTerm.listCons _ _ => RawTerm.snd developedPair
      | RawTerm.listElim _ _ _ => RawTerm.snd developedPair
      | RawTerm.optionNone => RawTerm.snd developedPair
      | RawTerm.optionSome _ => RawTerm.snd developedPair
      | RawTerm.optionMatch _ _ _ => RawTerm.snd developedPair
      | RawTerm.eitherInl _ => RawTerm.snd developedPair
      | RawTerm.eitherInr _ => RawTerm.snd developedPair
      | RawTerm.eitherMatch _ _ _ => RawTerm.snd developedPair
      | RawTerm.refl _ => RawTerm.snd developedPair
      | RawTerm.idJ _ _ => RawTerm.snd developedPair
      | RawTerm.modIntro _ => RawTerm.snd developedPair
      | RawTerm.modElim _ => RawTerm.snd developedPair
      | RawTerm.subsume _ => RawTerm.snd developedPair
  | _, .boolTrue => RawTerm.boolTrue
  | _, .boolFalse => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedThen := RawTerm.cd thenBranch
      let developedElse := RawTerm.cd elseBranch
      match developedScrutinee with
      | RawTerm.boolTrue => developedThen
      | RawTerm.boolFalse => developedElse
      | RawTerm.var _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.unit =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.lam _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.app _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.pair _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.fst _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.snd _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.boolElim _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.natZero =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.natSucc _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.natElim _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.natRec _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.listNil =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.listCons _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.listElim _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.optionNone =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.optionSome _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.eitherInl _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.eitherInr _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.refl _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.idJ _ _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.modIntro _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.modElim _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
      | RawTerm.subsume _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
  | _, .natZero => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc (RawTerm.cd predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedZero := RawTerm.cd zeroBranch
      let developedSucc := RawTerm.cd succBranch
      match developedScrutinee with
      | RawTerm.natZero => developedZero
      | RawTerm.natSucc predecessor =>
          RawTerm.app developedSucc predecessor
      | RawTerm.var _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.unit =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.lam _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.app _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.pair _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.fst _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.snd _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.boolTrue =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.boolFalse =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.boolElim _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.natElim _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.natRec _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.listNil =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.listCons _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.listElim _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.optionNone =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.optionSome _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.eitherInl _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.eitherInr _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.refl _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.idJ _ _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.modIntro _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.modElim _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
      | RawTerm.subsume _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
  | _, .natRec scrutinee zeroBranch succBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedZero := RawTerm.cd zeroBranch
      let developedSucc := RawTerm.cd succBranch
      match developedScrutinee with
      | RawTerm.natZero => developedZero
      | RawTerm.natSucc predecessor =>
          RawTerm.app (RawTerm.app developedSucc predecessor)
            (RawTerm.natRec predecessor developedZero developedSucc)
      | RawTerm.var _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.unit =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.lam _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.app _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.pair _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.fst _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.snd _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.boolTrue =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.boolFalse =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.boolElim _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.natElim _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.natRec _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.listNil =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.listCons _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.listElim _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.optionNone =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.optionSome _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.eitherInl _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.eitherInr _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.refl _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.idJ _ _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.modIntro _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.modElim _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
      | RawTerm.subsume _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
  | _, .listNil => RawTerm.listNil
  | _, .listCons headTerm tailTerm =>
      RawTerm.listCons (RawTerm.cd headTerm) (RawTerm.cd tailTerm)
  | _, .listElim scrutinee nilBranch consBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedNil := RawTerm.cd nilBranch
      let developedCons := RawTerm.cd consBranch
      match developedScrutinee with
      | RawTerm.listNil => developedNil
      | RawTerm.listCons headTerm tailTerm =>
          RawTerm.app (RawTerm.app developedCons headTerm) tailTerm
      | RawTerm.var _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.unit =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.lam _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.app _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.pair _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.fst _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.snd _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.boolTrue =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.boolFalse =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.boolElim _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.natZero =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.natSucc _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.natElim _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.natRec _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.listElim _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.optionNone =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.optionSome _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.eitherInl _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.eitherInr _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.refl _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.idJ _ _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.modIntro _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.modElim _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
      | RawTerm.subsume _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
  | _, .optionNone => RawTerm.optionNone
  | _, .optionSome valueTerm => RawTerm.optionSome (RawTerm.cd valueTerm)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedNone := RawTerm.cd noneBranch
      let developedSome := RawTerm.cd someBranch
      match developedScrutinee with
      | RawTerm.optionNone => developedNone
      | RawTerm.optionSome valueTerm =>
          RawTerm.app developedSome valueTerm
      | RawTerm.var _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.unit =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.lam _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.app _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.pair _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.fst _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.snd _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.boolTrue =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.boolFalse =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.boolElim _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.natZero =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.natSucc _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.natElim _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.natRec _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.listNil =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.listCons _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.listElim _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.eitherInl _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.eitherInr _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.refl _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.idJ _ _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.modIntro _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.modElim _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
      | RawTerm.subsume _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
  | _, .eitherInl valueTerm => RawTerm.eitherInl (RawTerm.cd valueTerm)
  | _, .eitherInr valueTerm => RawTerm.eitherInr (RawTerm.cd valueTerm)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedLeft := RawTerm.cd leftBranch
      let developedRight := RawTerm.cd rightBranch
      match developedScrutinee with
      | RawTerm.eitherInl valueTerm => RawTerm.app developedLeft valueTerm
      | RawTerm.eitherInr valueTerm => RawTerm.app developedRight valueTerm
      | RawTerm.var _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.unit =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.lam _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.app _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.pair _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.fst _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.snd _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.boolTrue =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.boolFalse =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.boolElim _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.natZero =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.natSucc _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.natElim _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.natRec _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.listNil =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.listCons _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.listElim _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.optionNone =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.optionSome _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.optionMatch _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.eitherMatch _ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.refl _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.idJ _ _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.modIntro _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.modElim _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
      | RawTerm.subsume _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | _, .refl rawWitness => RawTerm.refl (RawTerm.cd rawWitness)
  | _, .idJ baseCase witness =>
      let developedBase := RawTerm.cd baseCase
      let developedWitness := RawTerm.cd witness
      match developedWitness with
      | RawTerm.refl _ => developedBase
      | RawTerm.var _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.unit => RawTerm.idJ developedBase developedWitness
      | RawTerm.lam _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.app _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.pair _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.fst _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.snd _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.boolTrue => RawTerm.idJ developedBase developedWitness
      | RawTerm.boolFalse => RawTerm.idJ developedBase developedWitness
      | RawTerm.boolElim _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.natZero => RawTerm.idJ developedBase developedWitness
      | RawTerm.natSucc _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.natElim _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.natRec _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.listNil => RawTerm.idJ developedBase developedWitness
      | RawTerm.listCons _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.listElim _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.optionNone => RawTerm.idJ developedBase developedWitness
      | RawTerm.optionSome _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.optionMatch _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.eitherInl _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.eitherInr _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.eitherMatch _ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.idJ _ _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.modIntro _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.modElim _ => RawTerm.idJ developedBase developedWitness
      | RawTerm.subsume _ => RawTerm.idJ developedBase developedWitness
  | _, .modIntro innerTerm => RawTerm.modIntro (RawTerm.cd innerTerm)
  | _, .modElim innerTerm => RawTerm.modElim (RawTerm.cd innerTerm)
  | _, .subsume innerTerm => RawTerm.subsume (RawTerm.cd innerTerm)

end LeanFX2
