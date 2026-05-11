import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Polygraph.PolyTerm

/-! # `PolyTermAction` — K11.13 Phase A raw-layer rename + commute.

Per the K-lineage roadmap, K11.13 wires the polygraph encoding into
the unified Action/Subst framework so that downstream operations on
`PolyTerm` dispatch through the same rename/subst infrastructure that
`RawTerm` and `Term` use.

## Phase A scope (this file)

* `RawPolyTerm.rename` — structural rename mirroring all 73 cases of
  `RawTerm.rename` in `Foundation/RawSubst.lean`.
* `@[reducible] RawPolyTerm.weaken` — single-binder weakening mirror
  of `RawTerm.weaken`.
* `RawTerm.rename_toRawPoly_commute` — the headline commute lemma
  binding `RawTerm.toRawPoly` to `rename` along the raw-layer
  bijection: `(raw.rename ρ).toRawPoly = raw.toRawPoly.rename ρ`.

## Why this matters

Without this commute, every Phase B/C/D-D theorem that lifts a
typed-Term-level renaming through the polygraph encoding has to
re-prove the commute case-by-case.  Shipping it once at the raw layer
discharges every future PolyTerm-rename obligation via a single rewrite.

## Phase B/C/D plan (follow-ups, separate commits)

* Phase B (#1745): raw-layer subst (`RawPolyTermSubst`,
  `RawPolyTerm.subst`, `RawTerm.subst_toRawPoly_commute`).
* Phase C (#1745): typed `PolyTerm.rename` + `Term.rename_toPoly_commute`.
* Phase D (#1745): typed `PolyTerm.subst` + `Term.subst_toPoly_commute`.

## Audit

Every declaration ships zero-axiom.  `RawPolyTerm.rename` mirrors a
match-compiler-clean definition known to be zero-axiom on RawTerm.
The commute lemma uses `induction rawTerm generalizing targetScope`
to revert `rawRenaming` (which depends on the generalized scope) into
the IH; each case discharges via `simp only [...]` over the three
named `def`s (no equation lemmas leaking propext) plus `congrArg`. -/

namespace LeanFX2.Foundation.Polygraph

open LeanFX2

/-- Apply a raw renaming to a `RawPolyTerm`.  Mirrors `RawTerm.rename`
(73 cases) constructor-for-constructor; binder constructors (`lam`,
`pathLam`, `piTyCode`, `sigmaTyCode`) recurse with `rawRenaming.lift`
on the body.  Structural recursion is total since every recursive
call descends on a constructor argument. -/
def RawPolyTerm.rename : ∀ {sourceScope targetScope : Nat},
    RawPolyTerm sourceScope → RawRenaming sourceScope targetScope →
    RawPolyTerm targetScope
  | _, _, .var position, rawRenaming => .var (rawRenaming position)
  | _, _, .unit, _ => .unit
  | _, _, .lam body, rawRenaming =>
      .lam (body.rename rawRenaming.lift)
  | _, _, .app functionTerm argumentTerm, rawRenaming =>
      .app (functionTerm.rename rawRenaming)
           (argumentTerm.rename rawRenaming)
  | _, _, .pair firstValue secondValue, rawRenaming =>
      .pair (firstValue.rename rawRenaming)
            (secondValue.rename rawRenaming)
  | _, _, .fst pairTerm, rawRenaming => .fst (pairTerm.rename rawRenaming)
  | _, _, .snd pairTerm, rawRenaming => .snd (pairTerm.rename rawRenaming)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, rawRenaming =>
      .boolElim (scrutinee.rename rawRenaming)
                (thenBranch.rename rawRenaming)
                (elseBranch.rename rawRenaming)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, rawRenaming =>
      .natSucc (predecessor.rename rawRenaming)
  | _, _, .natElim scrutinee zeroBranch succBranch, rawRenaming =>
      .natElim (scrutinee.rename rawRenaming)
               (zeroBranch.rename rawRenaming)
               (succBranch.rename rawRenaming)
  | _, _, .natRec scrutinee zeroBranch succBranch, rawRenaming =>
      .natRec (scrutinee.rename rawRenaming)
              (zeroBranch.rename rawRenaming)
              (succBranch.rename rawRenaming)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, rawRenaming =>
      .listCons (headTerm.rename rawRenaming)
                (tailTerm.rename rawRenaming)
  | _, _, .listElim scrutinee nilBranch consBranch, rawRenaming =>
      .listElim (scrutinee.rename rawRenaming)
                (nilBranch.rename rawRenaming)
                (consBranch.rename rawRenaming)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, rawRenaming =>
      .optionSome (valueTerm.rename rawRenaming)
  | _, _, .optionMatch scrutinee noneBranch someBranch, rawRenaming =>
      .optionMatch (scrutinee.rename rawRenaming)
                   (noneBranch.rename rawRenaming)
                   (someBranch.rename rawRenaming)
  | _, _, .eitherInl valueTerm, rawRenaming =>
      .eitherInl (valueTerm.rename rawRenaming)
  | _, _, .eitherInr valueTerm, rawRenaming =>
      .eitherInr (valueTerm.rename rawRenaming)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, rawRenaming =>
      .eitherMatch (scrutinee.rename rawRenaming)
                   (leftBranch.rename rawRenaming)
                   (rightBranch.rename rawRenaming)
  | _, _, .refl rawWitness, rawRenaming =>
      .refl (rawWitness.rename rawRenaming)
  | _, _, .idJ baseCase witness, rawRenaming =>
      .idJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .modIntro raw, rawRenaming =>
      .modIntro (raw.rename rawRenaming)
  | _, _, .modElim raw, rawRenaming =>
      .modElim (raw.rename rawRenaming)
  | _, _, .subsume raw, rawRenaming =>
      .subsume (raw.rename rawRenaming)
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp intervalTerm, rawRenaming =>
      .intervalOpp (intervalTerm.rename rawRenaming)
  | _, _, .intervalMeet leftInterval rightInterval, rawRenaming =>
      .intervalMeet (leftInterval.rename rawRenaming)
                    (rightInterval.rename rawRenaming)
  | _, _, .intervalJoin leftInterval rightInterval, rawRenaming =>
      .intervalJoin (leftInterval.rename rawRenaming)
                    (rightInterval.rename rawRenaming)
  | _, _, .pathLam body, rawRenaming =>
      .pathLam (body.rename rawRenaming.lift)
  | _, _, .pathApp pathTerm intervalArg, rawRenaming =>
      .pathApp (pathTerm.rename rawRenaming)
               (intervalArg.rename rawRenaming)
  | _, _, .glueIntro baseValue partialValue, rawRenaming =>
      .glueIntro (baseValue.rename rawRenaming)
                 (partialValue.rename rawRenaming)
  | _, _, .glueElim gluedValue, rawRenaming =>
      .glueElim (gluedValue.rename rawRenaming)
  | _, _, .transp path source, rawRenaming =>
      .transp (path.rename rawRenaming) (source.rename rawRenaming)
  | _, _, .hcomp sides cap, rawRenaming =>
      .hcomp (sides.rename rawRenaming) (cap.rename rawRenaming)
  | _, _, .oeqRefl witness, rawRenaming =>
      .oeqRefl (witness.rename rawRenaming)
  | _, _, .oeqJ baseCase witness, rawRenaming =>
      .oeqJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .oeqFunext pointwiseEquality, rawRenaming =>
      .oeqFunext (pointwiseEquality.rename rawRenaming)
  | _, _, .idStrictRefl witness, rawRenaming =>
      .idStrictRefl (witness.rename rawRenaming)
  | _, _, .idStrictRec baseCase witness, rawRenaming =>
      .idStrictRec (baseCase.rename rawRenaming)
                   (witness.rename rawRenaming)
  | _, _, .equivIntro forwardFn backwardFn, rawRenaming =>
      .equivIntro (forwardFn.rename rawRenaming)
                  (backwardFn.rename rawRenaming)
  | _, _, .equivApp equivTerm argument, rawRenaming =>
      .equivApp (equivTerm.rename rawRenaming)
                (argument.rename rawRenaming)
  | _, _, .refineIntro rawValue predicateProof, rawRenaming =>
      .refineIntro (rawValue.rename rawRenaming)
                   (predicateProof.rename rawRenaming)
  | _, _, .refineElim refinedValue, rawRenaming =>
      .refineElim (refinedValue.rename rawRenaming)
  | _, _, .recordIntro firstField, rawRenaming =>
      .recordIntro (firstField.rename rawRenaming)
  | _, _, .recordProj recordValue, rawRenaming =>
      .recordProj (recordValue.rename rawRenaming)
  | _, _, .codataUnfold initialState transition, rawRenaming =>
      .codataUnfold (initialState.rename rawRenaming)
                    (transition.rename rawRenaming)
  | _, _, .codataDest codataValue, rawRenaming =>
      .codataDest (codataValue.rename rawRenaming)
  | _, _, .sessionSend channel payload, rawRenaming =>
      .sessionSend (channel.rename rawRenaming)
                   (payload.rename rawRenaming)
  | _, _, .sessionRecv channel, rawRenaming =>
      .sessionRecv (channel.rename rawRenaming)
  | _, _, .effectPerform operationTag arguments, rawRenaming =>
      .effectPerform (operationTag.rename rawRenaming)
                     (arguments.rename rawRenaming)
  -- Universe code carries a level Nat only, no Fin-indexed payload.
  | _, _, .universeCode innerLevel, _ => .universeCode innerLevel
  -- Per-shape type codes (CUMUL-2.1).
  | _, _, .arrowCode domainCode codomainCode, rawRenaming =>
      .arrowCode (domainCode.rename rawRenaming)
                 (codomainCode.rename rawRenaming)
  | _, _, .piTyCode domainCode codomainCode, rawRenaming =>
      .piTyCode (domainCode.rename rawRenaming)
                (codomainCode.rename rawRenaming.lift)
  | _, _, .sigmaTyCode domainCode codomainCode, rawRenaming =>
      .sigmaTyCode (domainCode.rename rawRenaming)
                   (codomainCode.rename rawRenaming.lift)
  | _, _, .productCode firstCode secondCode, rawRenaming =>
      .productCode (firstCode.rename rawRenaming)
                   (secondCode.rename rawRenaming)
  | _, _, .sumCode leftCode rightCode, rawRenaming =>
      .sumCode (leftCode.rename rawRenaming)
               (rightCode.rename rawRenaming)
  | _, _, .listCode elementCode, rawRenaming =>
      .listCode (elementCode.rename rawRenaming)
  | _, _, .optionCode elementCode, rawRenaming =>
      .optionCode (elementCode.rename rawRenaming)
  | _, _, .eitherCode leftCode rightCode, rawRenaming =>
      .eitherCode (leftCode.rename rawRenaming)
                  (rightCode.rename rawRenaming)
  | _, _, .idCode typeCode leftRaw rightRaw, rawRenaming =>
      .idCode (typeCode.rename rawRenaming)
              (leftRaw.rename rawRenaming)
              (rightRaw.rename rawRenaming)
  | _, _, .equivCode leftTypeCode rightTypeCode, rawRenaming =>
      .equivCode (leftTypeCode.rename rawRenaming)
                 (rightTypeCode.rename rawRenaming)
  | _, _, .cumulUpMarker innerCodeRaw, rawRenaming =>
      .cumulUpMarker (innerCodeRaw.rename rawRenaming)
  -- D3.6-P1 uaToEquiv.
  | _, _, .uaToEquiv proofRaw, rawRenaming =>
      .uaToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-P2 equivApply.
  | _, _, .equivApply equivRaw argRaw, rawRenaming =>
      .equivApply (equivRaw.rename rawRenaming)
                  (argRaw.rename rawRenaming)
  -- D3.6-S3 pathCompose.
  | _, _, .pathCompose leftPathRaw rightPathRaw, rawRenaming =>
      .pathCompose (leftPathRaw.rename rawRenaming)
                   (rightPathRaw.rename rawRenaming)
  -- D3.6-S4 idToEquiv.
  | _, _, .idToEquiv proofRaw, rawRenaming =>
      .idToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-S5 oeqTrans.
  | _, _, .oeqTrans firstProof secondProof, rawRenaming =>
      .oeqTrans (firstProof.rename rawRenaming)
                (secondProof.rename rawRenaming)
  -- D3.6-S5 equivCompose.
  | _, _, .equivCompose firstEquiv secondEquiv, rawRenaming =>
      .equivCompose (firstEquiv.rename rawRenaming)
                    (secondEquiv.rename rawRenaming)

/-- Single-binder weakening on a `RawPolyTerm`.  Mirrors
`RawTerm.weaken`.  Marked `@[reducible]` for the same reason
`RawTerm.weaken` is — downstream Term-level ctor signatures may
reference this through definitional equalities. -/
@[reducible] def RawPolyTerm.weaken {scope : Nat}
    (polyRaw : RawPolyTerm scope) : RawPolyTerm (scope + 1) :=
  polyRaw.rename RawRenaming.weaken

end LeanFX2.Foundation.Polygraph

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Local 1-argument congruence — `f a = f a'` from `a = a'`.
Zero-axiom: `congrArg` is from Init.Prelude. -/
private theorem congrArgLam {scope : Nat}
    {leftBody rightBody : RawPolyTerm (scope + 1)}
    (bodyEq : leftBody = rightBody) :
    (RawPolyTerm.lam leftBody : RawPolyTerm scope) =
      RawPolyTerm.lam rightBody :=
  congrArg RawPolyTerm.lam bodyEq

/-- Local 2-argument congruence for `RawPolyTerm` constructors.  Zero-
axiom: built from `congrArg` and `congr` (Init.Prelude). -/
private theorem congrArg2 {alpha beta gamma : Sort _}
    (functionMap : alpha → beta → gamma)
    {leftFirst rightFirst : alpha}
    {leftSecond rightSecond : beta}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond) :
    functionMap leftFirst leftSecond =
      functionMap rightFirst rightSecond :=
  congr (congrArg functionMap firstEq) secondEq

/-- Local 3-argument congruence for `RawPolyTerm` constructors.
Zero-axiom: composes `congrArg2` with `congr`. -/
private theorem congrArg3 {alpha beta gamma delta : Sort _}
    (functionMap : alpha → beta → gamma → delta)
    {leftFirst rightFirst : alpha}
    {leftSecond rightSecond : beta}
    {leftThird rightThird : gamma}
    (firstEq : leftFirst = rightFirst)
    (secondEq : leftSecond = rightSecond)
    (thirdEq : leftThird = rightThird) :
    functionMap leftFirst leftSecond leftThird =
      functionMap rightFirst rightSecond rightThird :=
  congr (congrArg2 functionMap firstEq secondEq) thirdEq

/-- The K11.13 Phase A headline commute lemma: applying a raw
renaming and then converting to `RawPolyTerm` is the same as
converting to `RawPolyTerm` and then applying the renaming there.
Structural induction on `rawTerm` with `targetScope` generalised (so
the IH for binder cases accepts `rawRenaming.lift`).  Every case
discharges by `simp only [RawTerm.rename, RawTerm.toRawPoly,
RawPolyTerm.rename]` followed by `congrArg{,2,3}` applied to the
inductive hypotheses. -/
theorem RawTerm.rename_toRawPoly_commute :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
        (rawTerm.rename rawRenaming).toRawPoly =
          rawTerm.toRawPoly.rename rawRenaming := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArgLam (bodyIH rawRenaming.lift)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.app
        (functionIH rawRenaming) (argumentIH rawRenaming)
  | pair firstValue secondValue firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pair
        (firstIH rawRenaming) (secondIH rawRenaming)
  | fst pairTerm pairIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.fst (pairIH rawRenaming)
  | snd pairTerm pairIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.snd (pairIH rawRenaming)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.boolElim
        (scrutineeIH rawRenaming) (thenIH rawRenaming)
        (elseIH rawRenaming)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.natSucc (predecessorIH rawRenaming)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.natElim
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.natRec
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.listCons
        (headIH rawRenaming) (tailIH rawRenaming)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.listElim
        (scrutineeIH rawRenaming) (nilIH rawRenaming)
        (consIH rawRenaming)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.optionSome (valueIH rawRenaming)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.optionMatch
        (scrutineeIH rawRenaming) (noneIH rawRenaming)
        (someIH rawRenaming)
  | eitherInl valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.eitherInl (valueIH rawRenaming)
  | eitherInr valueTerm valueIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.eitherInr (valueIH rawRenaming)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.eitherMatch
        (scrutineeIH rawRenaming) (leftIH rawRenaming)
        (rightIH rawRenaming)
  | refl rawWitness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.refl (witnessIH rawRenaming)
  | idJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.idJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | modIntro inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.modIntro (innerIH rawRenaming)
  | modElim inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.modElim (innerIH rawRenaming)
  | subsume inner innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.subsume (innerIH rawRenaming)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.intervalOpp (intervalIH rawRenaming)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.intervalMeet
        (leftIH rawRenaming) (rightIH rawRenaming)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.intervalJoin
        (leftIH rawRenaming) (rightIH rawRenaming)
  | pathLam body bodyIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.pathLam (bodyIH rawRenaming.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pathApp
        (pathIH rawRenaming) (intervalIH rawRenaming)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.glueIntro
        (baseIH rawRenaming) (partialIH rawRenaming)
  | glueElim gluedValue gluedIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.glueElim (gluedIH rawRenaming)
  | transp path source pathIH sourceIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.transp
        (pathIH rawRenaming) (sourceIH rawRenaming)
  | hcomp sides cap sidesIH capIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.hcomp
        (sidesIH rawRenaming) (capIH rawRenaming)
  | oeqRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.oeqRefl (witnessIH rawRenaming)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.oeqJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.oeqFunext (pointwiseIH rawRenaming)
  | idStrictRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.idStrictRefl (witnessIH rawRenaming)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.idStrictRec
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivIntro
        (forwardIH rawRenaming) (backwardIH rawRenaming)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivApp
        (equivIH rawRenaming) (argumentIH rawRenaming)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.refineIntro
        (rawIH rawRenaming) (proofIH rawRenaming)
  | refineElim refinedValue refinedIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.refineElim (refinedIH rawRenaming)
  | recordIntro firstField firstIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.recordIntro (firstIH rawRenaming)
  | recordProj recordValue recordIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.recordProj (recordIH rawRenaming)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.codataUnfold
        (initialIH rawRenaming) (transitionIH rawRenaming)
  | codataDest codataValue codataIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.codataDest (codataIH rawRenaming)
  | sessionSend channel payload channelIH payloadIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sessionSend
        (channelIH rawRenaming) (payloadIH rawRenaming)
  | sessionRecv channel channelIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.sessionRecv (channelIH rawRenaming)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.effectPerform
        (operationIH rawRenaming) (argumentsIH rawRenaming)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.arrowCode
        (domainIH rawRenaming) (codomainIH rawRenaming)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.piTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sigmaTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | productCode firstCode secondCode firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.productCode
        (firstIH rawRenaming) (secondIH rawRenaming)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.sumCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | listCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.listCode (elementIH rawRenaming)
  | optionCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.optionCode (elementIH rawRenaming)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.eitherCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg3 RawPolyTerm.idCode
        (typeIH rawRenaming) (leftIH rawRenaming) (rightIH rawRenaming)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.cumulUpMarker (innerIH rawRenaming)
  | uaToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.uaToEquiv (proofIH rawRenaming)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivApply
        (equivIH rawRenaming) (argIH rawRenaming)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.pathCompose
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg RawPolyTerm.idToEquiv (proofIH rawRenaming)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.oeqTrans
        (firstIH rawRenaming) (secondIH rawRenaming)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro rawRenaming
      simp only [RawTerm.rename, RawTerm.toRawPoly, RawPolyTerm.rename]
      exact congrArg2 RawPolyTerm.equivCompose
        (firstIH rawRenaming) (secondIH rawRenaming)

/-- Corollary: weakening commutes with `toRawPoly`. -/
theorem RawTerm.weaken_toRawPoly_commute {scope : Nat}
    (rawTerm : RawTerm scope) :
    rawTerm.weaken.toRawPoly =
      (rawTerm.toRawPoly : RawPolyTerm scope).weaken :=
  RawTerm.rename_toRawPoly_commute rawTerm RawRenaming.weaken

end LeanFX2

/-! ## K11.13 Phase B — raw-layer substitution + commute.

Mirrors `RawSubst.lean`'s substitution algebra at the polygraph
layer:

* `RawPolyTermSubst source target := Fin source → RawPolyTerm target`
* `RawPolyTermSubst.identity / .lift / .singleton`
* `RawPolyTerm.subst` — 73-case structural recursion mirroring
  `RawTerm.subst`
* `RawPolyTerm.subst0` — single-binder substitution
* `RawPolyTermSubst.lift_pointwise` + `RawPolyTerm.subst_pointwise`
  — substitution respects pointwise equality
* `RawTermSubst.toRawPolySubst` — pointwise converter from
  `RawTermSubst` to `RawPolyTermSubst` via the K11.10/12 bijection
* `RawTermSubst.lift_toRawPolySubst_commute` — lift commutes with
  the converter (POINTWISE — discharged via Phase A's
  `RawTerm.weaken_toRawPoly_commute` at the succ case)
* `RawTerm.subst_toRawPoly_commute` — HEADLINE: subst commutes with
  toRawPoly along the converter
* `RawTerm.subst0_toRawPoly_commute` — corollary at the single-binder
  substitution shape

Audit: every declaration ships zero-axiom under the same proof
template as Phase A (induction generalizing target, `simp only` over
the named `def`s, `congrArg{,2,3}` over IHs, binder cases threaded
through pointwise lemmas + Phase A commute). -/

namespace LeanFX2.Foundation.Polygraph

open LeanFX2

/-- A raw substitution targeting `RawPolyTerm`. -/
@[reducible] def RawPolyTermSubst (source target : Nat) : Type :=
  Fin source → RawPolyTerm target

/-- Identity substitution: each position to its variable. -/
@[reducible] def RawPolyTermSubst.identity {scope : Nat} :
    RawPolyTermSubst scope scope :=
  fun position => RawPolyTerm.var position

/-- Lift a substitution under a binder. -/
@[reducible] def RawPolyTermSubst.lift {source target : Nat}
    (substitution : RawPolyTermSubst source target) :
    RawPolyTermSubst (source + 1) (target + 1)
  | ⟨0, _⟩     => RawPolyTerm.var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩ => (substitution ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename
                    RawRenaming.weaken

/-- Single-binder substitution at the polygraph layer.  Mirrors
`RawTermSubst.singleton`. -/
@[reducible] def RawPolyTermSubst.singleton {scope : Nat}
    (rawPolyArg : RawPolyTerm scope) :
    RawPolyTermSubst (scope + 1) scope
  | ⟨0, _⟩     => rawPolyArg
  | ⟨k + 1, h⟩ => RawPolyTerm.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Apply a substitution to a `RawPolyTerm`.  73 cases mirroring
`RawTerm.subst`. -/
def RawPolyTerm.subst : ∀ {source target : Nat},
    RawPolyTerm source → RawPolyTermSubst source target →
    RawPolyTerm target
  | _, _, .var position, substitution => substitution position
  | _, _, .unit, _ => .unit
  | _, _, .lam body, substitution =>
      .lam (body.subst substitution.lift)
  | _, _, .app functionTerm argumentTerm, substitution =>
      .app (functionTerm.subst substitution)
           (argumentTerm.subst substitution)
  | _, _, .pair firstValue secondValue, substitution =>
      .pair (firstValue.subst substitution)
            (secondValue.subst substitution)
  | _, _, .fst pairTerm, substitution =>
      .fst (pairTerm.subst substitution)
  | _, _, .snd pairTerm, substitution =>
      .snd (pairTerm.subst substitution)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, substitution =>
      .boolElim (scrutinee.subst substitution)
                (thenBranch.subst substitution)
                (elseBranch.subst substitution)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, substitution =>
      .natSucc (predecessor.subst substitution)
  | _, _, .natElim scrutinee zeroBranch succBranch, substitution =>
      .natElim (scrutinee.subst substitution)
               (zeroBranch.subst substitution)
               (succBranch.subst substitution)
  | _, _, .natRec scrutinee zeroBranch succBranch, substitution =>
      .natRec (scrutinee.subst substitution)
              (zeroBranch.subst substitution)
              (succBranch.subst substitution)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, substitution =>
      .listCons (headTerm.subst substitution)
                (tailTerm.subst substitution)
  | _, _, .listElim scrutinee nilBranch consBranch, substitution =>
      .listElim (scrutinee.subst substitution)
                (nilBranch.subst substitution)
                (consBranch.subst substitution)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, substitution =>
      .optionSome (valueTerm.subst substitution)
  | _, _, .optionMatch scrutinee noneBranch someBranch, substitution =>
      .optionMatch (scrutinee.subst substitution)
                   (noneBranch.subst substitution)
                   (someBranch.subst substitution)
  | _, _, .eitherInl valueTerm, substitution =>
      .eitherInl (valueTerm.subst substitution)
  | _, _, .eitherInr valueTerm, substitution =>
      .eitherInr (valueTerm.subst substitution)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, substitution =>
      .eitherMatch (scrutinee.subst substitution)
                   (leftBranch.subst substitution)
                   (rightBranch.subst substitution)
  | _, _, .refl rawWitness, substitution =>
      .refl (rawWitness.subst substitution)
  | _, _, .idJ baseCase witness, substitution =>
      .idJ (baseCase.subst substitution) (witness.subst substitution)
  | _, _, .modIntro raw, substitution =>
      .modIntro (raw.subst substitution)
  | _, _, .modElim raw, substitution =>
      .modElim (raw.subst substitution)
  | _, _, .subsume raw, substitution =>
      .subsume (raw.subst substitution)
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp intervalTerm, substitution =>
      .intervalOpp (intervalTerm.subst substitution)
  | _, _, .intervalMeet leftInterval rightInterval, substitution =>
      .intervalMeet (leftInterval.subst substitution)
                    (rightInterval.subst substitution)
  | _, _, .intervalJoin leftInterval rightInterval, substitution =>
      .intervalJoin (leftInterval.subst substitution)
                    (rightInterval.subst substitution)
  | _, _, .pathLam body, substitution =>
      .pathLam (body.subst substitution.lift)
  | _, _, .pathApp pathTerm intervalArg, substitution =>
      .pathApp (pathTerm.subst substitution)
               (intervalArg.subst substitution)
  | _, _, .glueIntro baseValue partialValue, substitution =>
      .glueIntro (baseValue.subst substitution)
                 (partialValue.subst substitution)
  | _, _, .glueElim gluedValue, substitution =>
      .glueElim (gluedValue.subst substitution)
  | _, _, .transp path source, substitution =>
      .transp (path.subst substitution) (source.subst substitution)
  | _, _, .hcomp sides cap, substitution =>
      .hcomp (sides.subst substitution) (cap.subst substitution)
  | _, _, .oeqRefl witness, substitution =>
      .oeqRefl (witness.subst substitution)
  | _, _, .oeqJ baseCase witness, substitution =>
      .oeqJ (baseCase.subst substitution) (witness.subst substitution)
  | _, _, .oeqFunext pointwiseEquality, substitution =>
      .oeqFunext (pointwiseEquality.subst substitution)
  | _, _, .idStrictRefl witness, substitution =>
      .idStrictRefl (witness.subst substitution)
  | _, _, .idStrictRec baseCase witness, substitution =>
      .idStrictRec (baseCase.subst substitution)
                   (witness.subst substitution)
  | _, _, .equivIntro forwardFn backwardFn, substitution =>
      .equivIntro (forwardFn.subst substitution)
                  (backwardFn.subst substitution)
  | _, _, .equivApp equivTerm argument, substitution =>
      .equivApp (equivTerm.subst substitution)
                (argument.subst substitution)
  | _, _, .refineIntro rawValue predicateProof, substitution =>
      .refineIntro (rawValue.subst substitution)
                   (predicateProof.subst substitution)
  | _, _, .refineElim refinedValue, substitution =>
      .refineElim (refinedValue.subst substitution)
  | _, _, .recordIntro firstField, substitution =>
      .recordIntro (firstField.subst substitution)
  | _, _, .recordProj recordValue, substitution =>
      .recordProj (recordValue.subst substitution)
  | _, _, .codataUnfold initialState transition, substitution =>
      .codataUnfold (initialState.subst substitution)
                    (transition.subst substitution)
  | _, _, .codataDest codataValue, substitution =>
      .codataDest (codataValue.subst substitution)
  | _, _, .sessionSend channel payload, substitution =>
      .sessionSend (channel.subst substitution)
                   (payload.subst substitution)
  | _, _, .sessionRecv channel, substitution =>
      .sessionRecv (channel.subst substitution)
  | _, _, .effectPerform operationTag arguments, substitution =>
      .effectPerform (operationTag.subst substitution)
                     (arguments.subst substitution)
  | _, _, .universeCode innerLevel, _ => .universeCode innerLevel
  | _, _, .arrowCode domainCode codomainCode, substitution =>
      .arrowCode (domainCode.subst substitution)
                 (codomainCode.subst substitution)
  | _, _, .piTyCode domainCode codomainCode, substitution =>
      .piTyCode (domainCode.subst substitution)
                (codomainCode.subst substitution.lift)
  | _, _, .sigmaTyCode domainCode codomainCode, substitution =>
      .sigmaTyCode (domainCode.subst substitution)
                   (codomainCode.subst substitution.lift)
  | _, _, .productCode firstCode secondCode, substitution =>
      .productCode (firstCode.subst substitution)
                   (secondCode.subst substitution)
  | _, _, .sumCode leftCode rightCode, substitution =>
      .sumCode (leftCode.subst substitution)
               (rightCode.subst substitution)
  | _, _, .listCode elementCode, substitution =>
      .listCode (elementCode.subst substitution)
  | _, _, .optionCode elementCode, substitution =>
      .optionCode (elementCode.subst substitution)
  | _, _, .eitherCode leftCode rightCode, substitution =>
      .eitherCode (leftCode.subst substitution)
                  (rightCode.subst substitution)
  | _, _, .idCode typeCode leftRaw rightRaw, substitution =>
      .idCode (typeCode.subst substitution)
              (leftRaw.subst substitution)
              (rightRaw.subst substitution)
  | _, _, .equivCode leftTypeCode rightTypeCode, substitution =>
      .equivCode (leftTypeCode.subst substitution)
                 (rightTypeCode.subst substitution)
  | _, _, .cumulUpMarker innerCodeRaw, substitution =>
      .cumulUpMarker (innerCodeRaw.subst substitution)
  | _, _, .uaToEquiv proofRaw, substitution =>
      .uaToEquiv (proofRaw.subst substitution)
  | _, _, .equivApply equivRaw argRaw, substitution =>
      .equivApply (equivRaw.subst substitution)
                  (argRaw.subst substitution)
  | _, _, .pathCompose leftPathRaw rightPathRaw, substitution =>
      .pathCompose (leftPathRaw.subst substitution)
                   (rightPathRaw.subst substitution)
  | _, _, .idToEquiv proofRaw, substitution =>
      .idToEquiv (proofRaw.subst substitution)
  | _, _, .oeqTrans firstProof secondProof, substitution =>
      .oeqTrans (firstProof.subst substitution)
                (secondProof.subst substitution)
  | _, _, .equivCompose firstEquiv secondEquiv, substitution =>
      .equivCompose (firstEquiv.subst substitution)
                    (secondEquiv.subst substitution)

/-- Single-binder substitution at the polygraph layer.  Mirrors
`RawTerm.subst0`. -/
@[reducible] def RawPolyTerm.subst0 {scope : Nat}
    (body : RawPolyTerm (scope + 1)) (rawPolyArg : RawPolyTerm scope) :
    RawPolyTerm scope :=
  body.subst (RawPolyTermSubst.singleton rawPolyArg)

/-- Lift respects pointwise equality. -/
theorem RawPolyTermSubst.lift_pointwise {sourceScope targetScope : Nat}
    {substitution1 substitution2 : RawPolyTermSubst sourceScope targetScope}
    (substEq : ∀ position, substitution1 position = substitution2 position) :
    ∀ position, substitution1.lift position = substitution2.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawPolyTermSubst.lift]
      rw [substEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- `RawPolyTerm.subst` respects pointwise substitution equality. -/
theorem RawPolyTerm.subst_pointwise {sourceScope targetScope : Nat}
    {substitution1 substitution2 : RawPolyTermSubst sourceScope targetScope}
    (substEq : ∀ position, substitution1 position = substitution2 position) :
    ∀ (polyTerm : RawPolyTerm sourceScope),
      polyTerm.subst substitution1 = polyTerm.subst substitution2 := by
  intro polyTerm
  induction polyTerm generalizing targetScope with
  | var position =>
      simp only [RawPolyTerm.subst]; rw [substEq position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawPolyTerm.subst]
      rw [bodyIH (RawPolyTermSubst.lift_pointwise substEq)]
  | app fn arg fnIH argIH =>
      simp only [RawPolyTerm.subst]; rw [fnIH substEq, argIH substEq]
  | pair fv sv fvIH svIH =>
      simp only [RawPolyTerm.subst]; rw [fvIH substEq, svIH substEq]
  | fst pairTerm pairIH =>
      simp only [RawPolyTerm.subst]; rw [pairIH substEq]
  | snd pairTerm pairIH =>
      simp only [RawPolyTerm.subst]; rw [pairIH substEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, tIH substEq, eIH substEq]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawPolyTerm.subst]; rw [pIH substEq]
  | natElim s z c sIH zIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, zIH substEq, cIH substEq]
  | natRec s z c sIH zIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, zIH substEq, cIH substEq]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawPolyTerm.subst]
      rw [headIH substEq, tailIH substEq]
  | listElim s n c sIH nIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, nIH substEq, cIH substEq]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, nIH substEq, cIH substEq]
  | eitherInl v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | eitherInr v vIH =>
      simp only [RawPolyTerm.subst]; rw [vIH substEq]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawPolyTerm.subst]
      rw [sIH substEq, lIH substEq, rIH substEq]
  | refl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | idJ base witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]
      rw [baseIH substEq, witnessIH substEq]
  | modIntro inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | modElim inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | subsume inner innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawPolyTerm.subst]; rw [iIH substEq]
  | intervalMeet l r lIH rIH =>
      simp only [RawPolyTerm.subst]; rw [lIH substEq, rIH substEq]
  | intervalJoin l r lIH rIH =>
      simp only [RawPolyTerm.subst]; rw [lIH substEq, rIH substEq]
  | pathLam body bodyIH =>
      simp only [RawPolyTerm.subst]
      rw [bodyIH (RawPolyTermSubst.lift_pointwise substEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawPolyTerm.subst]
      rw [pathIH substEq, intervalIH substEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawPolyTerm.subst]
      rw [baseIH substEq, partialIH substEq]
  | glueElim gluedValue gluedIH =>
      simp only [RawPolyTerm.subst]; rw [gluedIH substEq]
  | transp path source pathIH sourceIH =>
      simp only [RawPolyTerm.subst]
      rw [pathIH substEq, sourceIH substEq]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawPolyTerm.subst]; rw [sidesIH substEq, capIH substEq]
  | oeqRefl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawPolyTerm.subst]; rw [pointwiseIH substEq]
  | idStrictRefl witness witnessIH =>
      simp only [RawPolyTerm.subst]; rw [witnessIH substEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawPolyTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      simp only [RawPolyTerm.subst]
      rw [forwardIH substEq, backwardIH substEq]
  | equivApp equivTerm argument equivIH argumentIH =>
      simp only [RawPolyTerm.subst]
      rw [equivIH substEq, argumentIH substEq]
  | refineIntro rawValue predicateProof rawIH proofIH =>
      simp only [RawPolyTerm.subst]; rw [rawIH substEq, proofIH substEq]
  | refineElim refinedValue refinedIH =>
      simp only [RawPolyTerm.subst]; rw [refinedIH substEq]
  | recordIntro firstField firstIH =>
      simp only [RawPolyTerm.subst]; rw [firstIH substEq]
  | recordProj recordValue recordIH =>
      simp only [RawPolyTerm.subst]; rw [recordIH substEq]
  | codataUnfold initialState transition initialIH transitionIH =>
      simp only [RawPolyTerm.subst]
      rw [initialIH substEq, transitionIH substEq]
  | codataDest codataValue codataIH =>
      simp only [RawPolyTerm.subst]; rw [codataIH substEq]
  | sessionSend channel payload channelIH payloadIH =>
      simp only [RawPolyTerm.subst]
      rw [channelIH substEq, payloadIH substEq]
  | sessionRecv channel channelIH =>
      simp only [RawPolyTerm.subst]; rw [channelIH substEq]
  | effectPerform operationTag arguments operationIH argumentsIH =>
      simp only [RawPolyTerm.subst]
      rw [operationIH substEq, argumentsIH substEq]
  | universeCode innerLevel => rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq, codomainIH substEq]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq,
          codomainIH (RawPolyTermSubst.lift_pointwise substEq)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawPolyTerm.subst]
      rw [domainIH substEq,
          codomainIH (RawPolyTermSubst.lift_pointwise substEq)]
  | productCode firstCode secondCode firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]
  | sumCode leftCode rightCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | listCode elementCode elementIH =>
      simp only [RawPolyTerm.subst]; rw [elementIH substEq]
  | optionCode elementCode elementIH =>
      simp only [RawPolyTerm.subst]; rw [elementIH substEq]
  | eitherCode leftCode rightCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [typeIH substEq, leftIH substEq, rightIH substEq]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | cumulUpMarker innerCodeRaw innerIH =>
      simp only [RawPolyTerm.subst]; rw [innerIH substEq]
  | uaToEquiv proofRaw proofIH =>
      simp only [RawPolyTerm.subst]; rw [proofIH substEq]
  | equivApply equivRaw argRaw equivIH argIH =>
      simp only [RawPolyTerm.subst]; rw [equivIH substEq, argIH substEq]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      simp only [RawPolyTerm.subst]
      rw [leftIH substEq, rightIH substEq]
  | idToEquiv proofRaw proofIH =>
      simp only [RawPolyTerm.subst]; rw [proofIH substEq]
  | oeqTrans firstProof secondProof firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      simp only [RawPolyTerm.subst]
      rw [firstIH substEq, secondIH substEq]

end LeanFX2.Foundation.Polygraph

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Cross-layer converter: a raw substitution targeting `RawTerm`
becomes a raw substitution targeting `RawPolyTerm` by pointwise
application of `RawTerm.toRawPoly`.  Marked `@[reducible]` so
downstream rewrites can unfold the converter definitionally. -/
@[reducible] def RawTermSubst.toRawPolySubst {source target : Nat}
    (substitution : RawTermSubst source target) :
    RawPolyTermSubst source target :=
  fun position => (substitution position).toRawPoly

/-- The `lift` operation commutes with the cross-layer converter
pointwise.  Succ case uses Phase A's `RawTerm.weaken_toRawPoly_commute`
to bridge `(σ k).rename weaken |>.toRawPoly = (σ k).toRawPoly.rename
weaken`. -/
theorem RawTermSubst.lift_toRawPolySubst_commute
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    ∀ position,
      substitution.lift.toRawPolySubst position =
        substitution.toRawPolySubst.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawTermSubst.toRawPolySubst, RawTermSubst.lift,
                 RawPolyTermSubst.lift]
      exact RawTerm.weaken_toRawPoly_commute
        (substitution ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- The K11.13 Phase B headline commute lemma: applying a raw
substitution and then converting to `RawPolyTerm` is the same as
converting both the term and the substitution to the polygraph
layer and substituting there.  Structural induction on `rawTerm`
with `targetScope` generalised so the binder cases receive
`bodyIH substitution.lift`.  Binder cases combine the IH with
`subst_pointwise` over `lift_toRawPolySubst_commute` to bridge
`substitution.lift.toRawPolySubst` against
`substitution.toRawPolySubst.lift`. -/
theorem RawTerm.subst_toRawPoly_commute :
    ∀ {sourceScope targetScope : Nat}
      (rawTerm : RawTerm sourceScope)
      (substitution : RawTermSubst sourceScope targetScope),
        (rawTerm.subst substitution).toRawPoly =
          rawTerm.toRawPoly.subst substitution.toRawPolySubst := by
  intro sourceScope targetScope rawTerm
  induction rawTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArgLam
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.app
        (functionIH substitution) (argumentIH substitution)
  | pair firstValue secondValue firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pair
        (firstIH substitution) (secondIH substitution)
  | fst pairTerm pairIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.fst (pairIH substitution)
  | snd pairTerm pairIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.snd (pairIH substitution)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch
      scrutineeIH thenIH elseIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.boolElim
        (scrutineeIH substitution) (thenIH substitution)
        (elseIH substitution)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.natSucc (predecessorIH substitution)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.natElim
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.natRec
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.listCons
        (headIH substitution) (tailIH substitution)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.listElim
        (scrutineeIH substitution) (nilIH substitution)
        (consIH substitution)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.optionSome (valueIH substitution)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.optionMatch
        (scrutineeIH substitution) (noneIH substitution)
        (someIH substitution)
  | eitherInl valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.eitherInl (valueIH substitution)
  | eitherInr valueTerm valueIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.eitherInr (valueIH substitution)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.eitherMatch
        (scrutineeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | refl rawWitness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.refl (witnessIH substitution)
  | idJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.idJ
        (baseIH substitution) (witnessIH substitution)
  | modIntro inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.modIntro (innerIH substitution)
  | modElim inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.modElim (innerIH substitution)
  | subsume inner innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.subsume (innerIH substitution)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.intervalOpp (intervalIH substitution)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.intervalMeet
        (leftIH substitution) (rightIH substitution)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.intervalJoin
        (leftIH substitution) (rightIH substitution)
  | pathLam body bodyIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawPolyTerm.pathLam
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pathApp
        (pathIH substitution) (intervalIH substitution)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.glueIntro
        (baseIH substitution) (partialIH substitution)
  | glueElim gluedValue gluedIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.glueElim (gluedIH substitution)
  | transp path source pathIH sourceIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.transp
        (pathIH substitution) (sourceIH substitution)
  | hcomp sides cap sidesIH capIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.hcomp
        (sidesIH substitution) (capIH substitution)
  | oeqRefl witness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.oeqRefl (witnessIH substitution)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.oeqJ
        (baseIH substitution) (witnessIH substitution)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.oeqFunext (pointwiseIH substitution)
  | idStrictRefl witness witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.idStrictRefl (witnessIH substitution)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.idStrictRec
        (baseIH substitution) (witnessIH substitution)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivIntro
        (forwardIH substitution) (backwardIH substitution)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivApp
        (equivIH substitution) (argumentIH substitution)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.refineIntro
        (rawIH substitution) (proofIH substitution)
  | refineElim refinedValue refinedIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.refineElim (refinedIH substitution)
  | recordIntro firstField firstIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.recordIntro (firstIH substitution)
  | recordProj recordValue recordIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.recordProj (recordIH substitution)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.codataUnfold
        (initialIH substitution) (transitionIH substitution)
  | codataDest codataValue codataIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.codataDest (codataIH substitution)
  | sessionSend channel payload channelIH payloadIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.sessionSend
        (channelIH substitution) (payloadIH substitution)
  | sessionRecv channel channelIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.sessionRecv (channelIH substitution)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.effectPerform
        (operationIH substitution) (argumentsIH substitution)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.arrowCode
        (domainIH substitution) (codomainIH substitution)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact congrArg2 RawPolyTerm.piTyCode (domainIH substitution)
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact congrArg2 RawPolyTerm.sigmaTyCode (domainIH substitution)
        (RawPolyTerm.subst_pointwise
          (RawTermSubst.lift_toRawPolySubst_commute substitution) _)
  | productCode firstCode secondCode firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.productCode
        (firstIH substitution) (secondIH substitution)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.sumCode
        (leftIH substitution) (rightIH substitution)
  | listCode elementCode elementIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.listCode (elementIH substitution)
  | optionCode elementCode elementIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.optionCode (elementIH substitution)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.eitherCode
        (leftIH substitution) (rightIH substitution)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg3 RawPolyTerm.idCode
        (typeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivCode
        (leftIH substitution) (rightIH substitution)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.cumulUpMarker (innerIH substitution)
  | uaToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.uaToEquiv (proofIH substitution)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivApply
        (equivIH substitution) (argIH substitution)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.pathCompose
        (leftIH substitution) (rightIH substitution)
  | idToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg RawPolyTerm.idToEquiv (proofIH substitution)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.oeqTrans
        (firstIH substitution) (secondIH substitution)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro substitution
      simp only [RawTerm.subst, RawTerm.toRawPoly, RawPolyTerm.subst]
      exact congrArg2 RawPolyTerm.equivCompose
        (firstIH substitution) (secondIH substitution)

/-- Corollary: `subst0` (single-binder β-substitution) commutes with
`toRawPoly`.  Derived from the headline `subst_toRawPoly_commute` at
`RawTermSubst.singleton`. -/
theorem RawTerm.subst0_toRawPoly_commute {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) :
    (body.subst0 rawArg).toRawPoly =
      body.toRawPoly.subst0 rawArg.toRawPoly := by
  unfold RawTerm.subst0 RawPolyTerm.subst0
  rw [RawTerm.subst_toRawPoly_commute body (RawTermSubst.singleton rawArg)]
  apply RawPolyTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩     => rfl
  | ⟨_ + 1, _⟩ => rfl

end LeanFX2

/-! ## K11.13 Phase C-1 — reverse-direction rename commute.

The Phase A commute showed that applying a raw renaming commutes with
the `RawTerm → RawPolyTerm` direction of the bijection:
`(rawTerm.rename rho).toRawPoly = rawTerm.toRawPoly.rename rho`.

Phase C-1 (this section) ships the reverse:
`(polyTerm.rename rho).toRawTerm = polyTerm.toRawTerm.rename rho`.

## Why both directions

The typed `PolyTerm.rename` (Phase C-2, follow-up) has 11 raw-in-Ty
constructors whose typed signature embeds the inner subterm's
`RawPolyTerm` payload INSIDE the kernel `Ty` index via
`RawPolyTerm.toRawTerm` (because `Ty` itself is indexed by `RawTerm`,
not `RawPolyTerm`).  Specifically, ctors like `PolyTerm.appPi /
.pair / .snd / .boolElim / .refl / .oeqRefl / .idStrictRefl /
.refineIntro` carry kernel `Ty` indices of the form
`codomainType.subst0 domainType argumentPolyRaw.toRawTerm` — where
the recursive `PolyTerm.rename` call delivers a subterm at
`(argumentPolyRaw.rename rho).toRawTerm` while the outer ctor signature
demands `argumentPolyRaw.toRawTerm.rename rho`.  Phase C-1 is the
bridge that lets each raw-in-Ty cast use a single rewrite at the Ty
level rather than inlining the commute case-by-case.

## Proof template

Identical to Phase A: induct on `polyTerm` with `targetScope`
generalised so binder cases threaded through `rawRenaming.lift`; each
case discharges via `simp only [RawPolyTerm.rename,
RawPolyTerm.toRawTerm, RawTerm.rename]` plus `congrArg{,2,3}` over
the IHs.  Zero-axiom — uses only `congrArg` / `congr` from
Init.Prelude and the structural induction principle.

The naming-discipline difference from Phase A is the bookkeeping
order: induct on `RawPolyTerm` (not `RawTerm`), project via
`RawPolyTerm.toRawTerm` (not `RawTerm.toRawPoly`), and the cong helpers
build `RawTerm.X` targets (not `RawPolyTerm.X`). -/

namespace LeanFX2.Foundation.Polygraph

theorem RawPolyTerm.toRawTerm_rename_commute :
    ∀ {sourceScope targetScope : Nat}
      (polyTerm : RawPolyTerm sourceScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
        (polyTerm.rename rawRenaming).toRawTerm =
          polyTerm.toRawTerm.rename rawRenaming := by
  intro sourceScope targetScope polyTerm
  induction polyTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.lam (bodyIH rawRenaming.lift)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.app
        (functionIH rawRenaming) (argumentIH rawRenaming)
  | pair firstValue secondValue firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pair
        (firstIH rawRenaming) (secondIH rawRenaming)
  | fst pairTerm pairIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.fst (pairIH rawRenaming)
  | snd pairTerm pairIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.snd (pairIH rawRenaming)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.boolElim
        (scrutineeIH rawRenaming) (thenIH rawRenaming)
        (elseIH rawRenaming)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.natSucc (predecessorIH rawRenaming)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.natElim
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.natRec
        (scrutineeIH rawRenaming) (zeroIH rawRenaming)
        (succIH rawRenaming)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.listCons
        (headIH rawRenaming) (tailIH rawRenaming)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.listElim
        (scrutineeIH rawRenaming) (nilIH rawRenaming)
        (consIH rawRenaming)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.optionSome (valueIH rawRenaming)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.optionMatch
        (scrutineeIH rawRenaming) (noneIH rawRenaming)
        (someIH rawRenaming)
  | eitherInl valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.eitherInl (valueIH rawRenaming)
  | eitherInr valueTerm valueIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.eitherInr (valueIH rawRenaming)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.eitherMatch
        (scrutineeIH rawRenaming) (leftIH rawRenaming)
        (rightIH rawRenaming)
  | refl rawWitness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.refl (witnessIH rawRenaming)
  | idJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.idJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | modIntro inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.modIntro (innerIH rawRenaming)
  | modElim inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.modElim (innerIH rawRenaming)
  | subsume inner innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.subsume (innerIH rawRenaming)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.intervalOpp (intervalIH rawRenaming)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.intervalMeet
        (leftIH rawRenaming) (rightIH rawRenaming)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.intervalJoin
        (leftIH rawRenaming) (rightIH rawRenaming)
  | pathLam body bodyIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.pathLam (bodyIH rawRenaming.lift)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pathApp
        (pathIH rawRenaming) (intervalIH rawRenaming)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.glueIntro
        (baseIH rawRenaming) (partialIH rawRenaming)
  | glueElim gluedValue gluedIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.glueElim (gluedIH rawRenaming)
  | transp path source pathIH sourceIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.transp
        (pathIH rawRenaming) (sourceIH rawRenaming)
  | hcomp sides cap sidesIH capIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.hcomp
        (sidesIH rawRenaming) (capIH rawRenaming)
  | oeqRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.oeqRefl (witnessIH rawRenaming)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.oeqJ
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.oeqFunext (pointwiseIH rawRenaming)
  | idStrictRefl witness witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.idStrictRefl (witnessIH rawRenaming)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.idStrictRec
        (baseIH rawRenaming) (witnessIH rawRenaming)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivIntro
        (forwardIH rawRenaming) (backwardIH rawRenaming)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivApp
        (equivIH rawRenaming) (argumentIH rawRenaming)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.refineIntro
        (rawIH rawRenaming) (proofIH rawRenaming)
  | refineElim refinedValue refinedIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.refineElim (refinedIH rawRenaming)
  | recordIntro firstField firstIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.recordIntro (firstIH rawRenaming)
  | recordProj recordValue recordIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.recordProj (recordIH rawRenaming)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.codataUnfold
        (initialIH rawRenaming) (transitionIH rawRenaming)
  | codataDest codataValue codataIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.codataDest (codataIH rawRenaming)
  | sessionSend channel payload channelIH payloadIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sessionSend
        (channelIH rawRenaming) (payloadIH rawRenaming)
  | sessionRecv channel channelIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.sessionRecv (channelIH rawRenaming)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.effectPerform
        (operationIH rawRenaming) (argumentsIH rawRenaming)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.arrowCode
        (domainIH rawRenaming) (codomainIH rawRenaming)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.piTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sigmaTyCode
        (domainIH rawRenaming) (codomainIH rawRenaming.lift)
  | productCode firstCode secondCode firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.productCode
        (firstIH rawRenaming) (secondIH rawRenaming)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.sumCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | listCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.listCode (elementIH rawRenaming)
  | optionCode elementCode elementIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.optionCode (elementIH rawRenaming)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.eitherCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg3 RawTerm.idCode
        (typeIH rawRenaming) (leftIH rawRenaming) (rightIH rawRenaming)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivCode
        (leftIH rawRenaming) (rightIH rawRenaming)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.cumulUpMarker (innerIH rawRenaming)
  | uaToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.uaToEquiv (proofIH rawRenaming)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivApply
        (equivIH rawRenaming) (argIH rawRenaming)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.pathCompose
        (leftIH rawRenaming) (rightIH rawRenaming)
  | idToEquiv proofRaw proofIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact congrArg RawTerm.idToEquiv (proofIH rawRenaming)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.oeqTrans
        (firstIH rawRenaming) (secondIH rawRenaming)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro rawRenaming
      simp only [RawPolyTerm.rename, RawPolyTerm.toRawTerm, RawTerm.rename]
      exact LeanFX2.congrArg2 RawTerm.equivCompose
        (firstIH rawRenaming) (secondIH rawRenaming)

/-- Corollary: weakening commutes with `toRawTerm`. -/
theorem RawPolyTerm.weaken_toRawTerm_commute {scope : Nat}
    (polyTerm : RawPolyTerm scope) :
    polyTerm.weaken.toRawTerm =
      (polyTerm.toRawTerm : RawTerm scope).weaken :=
  RawPolyTerm.toRawTerm_rename_commute polyTerm RawRenaming.weaken

/-! ## K11.13 Phase C-1S — reverse-direction subst commute.

Mirrors Phase C-1's `RawPolyTerm.toRawTerm_rename_commute` for the
substitution direction.  Where Phase C-1 said
`(polyTerm.rename rho).toRawTerm = polyTerm.toRawTerm.rename rho`,
Phase C-1S says
`(polyTerm.subst sigma).toRawTerm = polyTerm.toRawTerm.subst sigma.toRawTermSubst`.

Needs a `RawPolyTermSubst → RawTermSubst` converter, then mirrors the
73-case structural induction of Phase C-1 with `subst` / `RawTerm.subst`
in place of `rename` / `RawTerm.rename`. -/

/-- Pointwise converter: a `RawPolyTermSubst` becomes a `RawTermSubst`
by projecting each substituent through `RawPolyTerm.toRawTerm`. -/
@[reducible] def RawPolyTermSubst.toRawTermSubst {source target : Nat}
    (substitution : RawPolyTermSubst source target) :
    RawTermSubst source target :=
  fun position => (substitution position).toRawTerm

/-- `lift` commutes with the cross-layer converter pointwise.  Succ
case uses Phase C-1's `RawPolyTerm.toRawTerm_rename_commute` to bridge
`(σ k).rename weaken |>.toRawTerm = (σ k).toRawTerm.rename weaken`. -/
theorem RawPolyTermSubst.lift_toRawTermSubst_commute
    {sourceScope targetScope : Nat}
    (substitution : RawPolyTermSubst sourceScope targetScope) :
    ∀ position,
      (substitution.lift position).toRawTerm =
        substitution.toRawTermSubst.lift position
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => by
      simp only [RawPolyTermSubst.toRawTermSubst, RawPolyTermSubst.lift,
                 RawTermSubst.lift]
      exact RawPolyTerm.toRawTerm_rename_commute
        (substitution ⟨k, Nat.lt_of_succ_lt_succ h⟩) RawRenaming.weaken

/-- K11.13 Phase C-1S headline: `RawPolyTerm.toRawTerm` commutes with
`RawPolyTerm.subst`.  73-case structural induction mirroring Phase C-1;
binder cases (lam, pathLam, piTyCode, sigmaTyCode) use the lift commute
to bridge `substitution.lift.toRawTermSubst` against
`substitution.toRawTermSubst.lift`. -/
theorem RawPolyTerm.toRawTerm_subst_commute :
    ∀ {sourceScope targetScope : Nat}
      (polyTerm : RawPolyTerm sourceScope)
      (substitution : RawPolyTermSubst sourceScope targetScope),
        (polyTerm.subst substitution).toRawTerm =
          polyTerm.toRawTerm.subst substitution.toRawTermSubst := by
  intro sourceScope targetScope polyTerm
  induction polyTerm generalizing targetScope with
  | var position => intro _; rfl
  | unit => intro _; rfl
  | lam body bodyIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawTerm.lam
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.app
        (functionIH substitution) (argumentIH substitution)
  | pair firstValue secondValue firstIH secondIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pair
        (firstIH substitution) (secondIH substitution)
  | fst pairTerm pairIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.fst (pairIH substitution)
  | snd pairTerm pairIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.snd (pairIH substitution)
  | boolTrue => intro _; rfl
  | boolFalse => intro _; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.boolElim
        (scrutineeIH substitution) (thenIH substitution)
        (elseIH substitution)
  | natZero => intro _; rfl
  | natSucc predecessor predecessorIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.natSucc (predecessorIH substitution)
  | natElim scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.natElim
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | natRec scrutinee zeroBranch succBranch
      scrutineeIH zeroIH succIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.natRec
        (scrutineeIH substitution) (zeroIH substitution)
        (succIH substitution)
  | listNil => intro _; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.listCons
        (headIH substitution) (tailIH substitution)
  | listElim scrutinee nilBranch consBranch
      scrutineeIH nilIH consIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.listElim
        (scrutineeIH substitution) (nilIH substitution)
        (consIH substitution)
  | optionNone => intro _; rfl
  | optionSome valueTerm valueIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.optionSome (valueIH substitution)
  | optionMatch scrutinee noneBranch someBranch
      scrutineeIH noneIH someIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.optionMatch
        (scrutineeIH substitution) (noneIH substitution)
        (someIH substitution)
  | eitherInl valueTerm valueIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.eitherInl (valueIH substitution)
  | eitherInr valueTerm valueIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.eitherInr (valueIH substitution)
  | eitherMatch scrutinee leftBranch rightBranch
      scrutineeIH leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.eitherMatch
        (scrutineeIH substitution) (leftIH substitution)
        (rightIH substitution)
  | refl rawWitness witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.refl (witnessIH substitution)
  | idJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.idJ
        (baseIH substitution) (witnessIH substitution)
  | modIntro inner innerIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.modIntro (innerIH substitution)
  | modElim inner innerIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.modElim (innerIH substitution)
  | subsume inner innerIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.subsume (innerIH substitution)
  | interval0 => intro _; rfl
  | interval1 => intro _; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.intervalOpp (intervalIH substitution)
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.intervalMeet
        (leftIH substitution) (rightIH substitution)
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.intervalJoin
        (leftIH substitution) (rightIH substitution)
  | pathLam body bodyIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := bodyIH substitution.lift
      rw [liftedCommute]
      exact congrArg RawTerm.pathLam
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pathApp
        (pathIH substitution) (intervalIH substitution)
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.glueIntro
        (baseIH substitution) (partialIH substitution)
  | glueElim gluedValue gluedIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.glueElim (gluedIH substitution)
  | transp path source pathIH sourceIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.transp
        (pathIH substitution) (sourceIH substitution)
  | hcomp sides cap sidesIH capIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.hcomp
        (sidesIH substitution) (capIH substitution)
  | oeqRefl witness witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.oeqRefl (witnessIH substitution)
  | oeqJ baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.oeqJ
        (baseIH substitution) (witnessIH substitution)
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.oeqFunext (pointwiseIH substitution)
  | idStrictRefl witness witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.idStrictRefl (witnessIH substitution)
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.idStrictRec
        (baseIH substitution) (witnessIH substitution)
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivIntro
        (forwardIH substitution) (backwardIH substitution)
  | equivApp equivTerm argument equivIH argumentIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivApp
        (equivIH substitution) (argumentIH substitution)
  | refineIntro rawValue predicateProof rawIH proofIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.refineIntro
        (rawIH substitution) (proofIH substitution)
  | refineElim refinedValue refinedIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.refineElim (refinedIH substitution)
  | recordIntro firstField firstIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.recordIntro (firstIH substitution)
  | recordProj recordValue recordIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.recordProj (recordIH substitution)
  | codataUnfold initialState transition initialIH transitionIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.codataUnfold
        (initialIH substitution) (transitionIH substitution)
  | codataDest codataValue codataIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.codataDest (codataIH substitution)
  | sessionSend channel payload channelIH payloadIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.sessionSend
        (channelIH substitution) (payloadIH substitution)
  | sessionRecv channel channelIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.sessionRecv (channelIH substitution)
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.effectPerform
        (operationIH substitution) (argumentsIH substitution)
  | universeCode innerLevel => intro _; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.arrowCode
        (domainIH substitution) (codomainIH substitution)
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact LeanFX2.congrArg2 RawTerm.piTyCode (domainIH substitution)
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      have liftedCommute := codomainIH substitution.lift
      rw [liftedCommute]
      exact LeanFX2.congrArg2 RawTerm.sigmaTyCode (domainIH substitution)
        (RawTerm.subst_pointwise
          (RawPolyTermSubst.lift_toRawTermSubst_commute substitution) _)
  | productCode firstCode secondCode firstIH secondIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.productCode
        (firstIH substitution) (secondIH substitution)
  | sumCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.sumCode
        (leftIH substitution) (rightIH substitution)
  | listCode elementCode elementIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.listCode (elementIH substitution)
  | optionCode elementCode elementIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.optionCode (elementIH substitution)
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.eitherCode
        (leftIH substitution) (rightIH substitution)
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg3 RawTerm.idCode
        (typeIH substitution) (leftIH substitution) (rightIH substitution)
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivCode
        (leftIH substitution) (rightIH substitution)
  | cumulUpMarker innerCodeRaw innerIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.cumulUpMarker (innerIH substitution)
  | uaToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.uaToEquiv (proofIH substitution)
  | equivApply equivRaw argRaw equivIH argIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivApply
        (equivIH substitution) (argIH substitution)
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.pathCompose
        (leftIH substitution) (rightIH substitution)
  | idToEquiv proofRaw proofIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact congrArg RawTerm.idToEquiv (proofIH substitution)
  | oeqTrans firstProof secondProof firstIH secondIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.oeqTrans
        (firstIH substitution) (secondIH substitution)
  | equivCompose firstEquiv secondEquiv firstIH secondIH =>
      intro substitution
      simp only [RawPolyTerm.subst, RawPolyTerm.toRawTerm, RawTerm.subst]
      exact LeanFX2.congrArg2 RawTerm.equivCompose
        (firstIH substitution) (secondIH substitution)

/-- Corollary: singleton substitution commutes with `toRawTerm`. -/
theorem RawPolyTerm.subst0_toRawTerm_commute {scope : Nat}
    (body : RawPolyTerm (scope + 1)) (rawArg : RawPolyTerm scope) :
    (body.subst (RawPolyTermSubst.singleton rawArg)).toRawTerm =
      body.toRawTerm.subst (RawTermSubst.singleton rawArg.toRawTerm) := by
  rw [RawPolyTerm.toRawTerm_subst_commute body
        (RawPolyTermSubst.singleton rawArg)]
  refine RawTerm.subst_pointwise ?_ body.toRawTerm
  intro position
  rcases position with ⟨n, hn⟩
  cases n with
  | zero => rfl
  | succ k => rfl

end LeanFX2.Foundation.Polygraph
