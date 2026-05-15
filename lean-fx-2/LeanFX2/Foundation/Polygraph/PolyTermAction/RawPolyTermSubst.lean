import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermRename

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermSubst

K11.13 Phase B — raw-layer substitution definitions.

* `RawPolyTermSubst` type, `.identity`, `.lift`, `.singleton`.
* `RawPolyTerm.subst` — the 73-case structural induction mirror of
  `RawTerm.subst`.  This is the heavy single-def slice: kept in its
  own module so `lake -j` can elaborate it independently of the
  surrounding commute proofs.
* `RawPolyTerm.subst0` — single-binder substitution shim.

## Root status

Zero-axiom (each match-case is constructor-for-constructor structural
recursion). -/

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
  | _, _, .transpFill path interval source, substitution =>
      .transpFill (path.subst substitution)
                  (interval.subst substitution)
                  (source.subst substitution)
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


end LeanFX2.Foundation.Polygraph
