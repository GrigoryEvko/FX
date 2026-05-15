import LeanFX2.Foundation.RawSubst.RenameLemmas

/-! # LeanFX2.Foundation.RawSubst.SubstDefs

Raw term substitution type, identity / lift / singleton / fromRenaming,
`RawTerm.subst` structural definition, and `RawTerm.subst0`
single-binder β-substitution.

## Root status

Layer 0 raw-syntax definitions; strict zero-axiom. -/

namespace LeanFX2

/-! ## Substitutions -/

/-- A raw term substitution: `Fin source → RawTerm target`. -/
@[reducible] def RawTermSubst (source target : Nat) : Type :=
  Fin source → RawTerm target

/-- Identity substitution: each position to its variable. -/
@[reducible] def RawTermSubst.identity {scope : Nat} : RawTermSubst scope scope :=
  fun position => RawTerm.var position

/-- Lift a substitution under a binder. -/
@[reducible] def RawTermSubst.lift {source target : Nat}
    (sigma : RawTermSubst source target) : RawTermSubst (source + 1) (target + 1)
  | ⟨0, _⟩      => RawTerm.var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename RawRenaming.weaken

/-- Single-binder substitution: position 0 → rawArg, position k+1 → var k.

This is the load-bearing β-reduction substitution.  In lean-fx-2 this
is the ONE singleton operation; there is NO `dropNewest` variant. -/
@[reducible] def RawTermSubst.singleton {scope : Nat}
    (rawArg : RawTerm scope) : RawTermSubst (scope + 1) scope
  | ⟨0, _⟩      => rawArg
  | ⟨k + 1, h⟩  => RawTerm.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Convert a rawRenaming to a substitution. -/
@[reducible] def RawRenaming.toSubst {source target : Nat}
    (rawRenaming : RawRenaming source target) : RawTermSubst source target :=
  fun position => RawTerm.var (rawRenaming position)

/-- Apply a substitution to a raw term. -/
def RawTerm.subst : ∀ {source target : Nat},
    RawTerm source → RawTermSubst source target → RawTerm target
  | _, _, .var position, sigma => sigma position
  | _, _, .unit, _ => .unit
  | _, _, .lam body, sigma => .lam (body.subst sigma.lift)
  | _, _, .app functionTerm argumentTerm, sigma =>
      .app (functionTerm.subst sigma) (argumentTerm.subst sigma)
  | _, _, .pair firstValue secondValue, sigma =>
      .pair (firstValue.subst sigma) (secondValue.subst sigma)
  | _, _, .fst pairTerm, sigma => .fst (pairTerm.subst sigma)
  | _, _, .snd pairTerm, sigma => .snd (pairTerm.subst sigma)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, sigma =>
      .boolElim (scrutinee.subst sigma)
                (thenBranch.subst sigma)
                (elseBranch.subst sigma)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, sigma => .natSucc (predecessor.subst sigma)
  | _, _, .natElim scrutinee zeroBranch succBranch, sigma =>
      .natElim (scrutinee.subst sigma)
               (zeroBranch.subst sigma)
               (succBranch.subst sigma)
  | _, _, .natRec scrutinee zeroBranch succBranch, sigma =>
      .natRec (scrutinee.subst sigma)
              (zeroBranch.subst sigma)
              (succBranch.subst sigma)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, sigma =>
      .listCons (headTerm.subst sigma) (tailTerm.subst sigma)
  | _, _, .listElim scrutinee nilBranch consBranch, sigma =>
      .listElim (scrutinee.subst sigma)
                (nilBranch.subst sigma)
                (consBranch.subst sigma)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, sigma => .optionSome (valueTerm.subst sigma)
  | _, _, .optionMatch scrutinee noneBranch someBranch, sigma =>
      .optionMatch (scrutinee.subst sigma)
                   (noneBranch.subst sigma)
                   (someBranch.subst sigma)
  | _, _, .eitherInl valueTerm, sigma => .eitherInl (valueTerm.subst sigma)
  | _, _, .eitherInr valueTerm, sigma => .eitherInr (valueTerm.subst sigma)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, sigma =>
      .eitherMatch (scrutinee.subst sigma)
                   (leftBranch.subst sigma)
                   (rightBranch.subst sigma)
  | _, _, .refl rawWitness, sigma => .refl (rawWitness.subst sigma)
  | _, _, .idJ baseCase witness, sigma =>
      .idJ (baseCase.subst sigma) (witness.subst sigma)
  | _, _, .modIntro inner, sigma => .modIntro (inner.subst sigma)
  | _, _, .modElim inner, sigma => .modElim (inner.subst sigma)
  | _, _, .subsume inner, sigma => .subsume (inner.subst sigma)
  -- D1.6 cubical interval + path
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp i, sigma => .intervalOpp (i.subst sigma)
  | _, _, .intervalMeet l r, sigma =>
      .intervalMeet (l.subst sigma) (r.subst sigma)
  | _, _, .intervalJoin l r, sigma =>
      .intervalJoin (l.subst sigma) (r.subst sigma)
  | _, _, .pathLam body, sigma =>
      .pathLam (body.subst sigma.lift)
  | _, _, .pathApp pathTerm intervalArg, sigma =>
      .pathApp (pathTerm.subst sigma) (intervalArg.subst sigma)
  | _, _, .glueIntro baseValue partialValue, sigma =>
      .glueIntro (baseValue.subst sigma) (partialValue.subst sigma)
  | _, _, .glueElim gluedValue, sigma => .glueElim (gluedValue.subst sigma)
  | _, _, .transp path source, sigma =>
      .transp (path.subst sigma) (source.subst sigma)
  | _, _, .hcomp sides cap, sigma =>
      .hcomp (sides.subst sigma) (cap.subst sigma)
  -- D1.6 observational + strict equality
  | _, _, .oeqRefl witness, sigma => .oeqRefl (witness.subst sigma)
  | _, _, .oeqJ baseCase witness, sigma =>
      .oeqJ (baseCase.subst sigma) (witness.subst sigma)
  | _, _, .oeqFunext pointwiseEquality, sigma =>
      .oeqFunext (pointwiseEquality.subst sigma)
  | _, _, .idStrictRefl witness, sigma =>
      .idStrictRefl (witness.subst sigma)
  | _, _, .idStrictRec baseCase witness, sigma =>
      .idStrictRec (baseCase.subst sigma) (witness.subst sigma)
  -- D1.6 type equivalence
  | _, _, .equivIntro fwd bwd, sigma =>
      .equivIntro (fwd.subst sigma) (bwd.subst sigma)
  | _, _, .equivApp equivTerm argument, sigma =>
      .equivApp (equivTerm.subst sigma) (argument.subst sigma)
  -- D1.6 refinement / record / codata
  | _, _, .refineIntro rawValue predicateProof, sigma =>
      .refineIntro (rawValue.subst sigma) (predicateProof.subst sigma)
  | _, _, .refineElim refinedValue, sigma => .refineElim (refinedValue.subst sigma)
  | _, _, .recordIntro firstField, sigma => .recordIntro (firstField.subst sigma)
  | _, _, .recordProj recordValue, sigma => .recordProj (recordValue.subst sigma)
  | _, _, .codataUnfold initialState transition, sigma =>
      .codataUnfold (initialState.subst sigma) (transition.subst sigma)
  | _, _, .codataDest codataValue, sigma => .codataDest (codataValue.subst sigma)
  -- D1.6 sessions, effects
  | _, _, .sessionSend channel payload, sigma =>
      .sessionSend (channel.subst sigma) (payload.subst sigma)
  | _, _, .sessionRecv channel, sigma => .sessionRecv (channel.subst sigma)
  | _, _, .effectPerform operationTag arguments, sigma =>
      .effectPerform (operationTag.subst sigma) (arguments.subst sigma)
  -- D1.6/A2: universeCode is scope-polymorphic — subst is identity
  -- on the inner-level payload (no Fin variables to substitute).
  | _, _, .universeCode innerLevel, _ =>
      .universeCode innerLevel
  -- CUMUL-2.1 per-shape type codes.
  | _, _, .arrowCode domainCode codomainCode, sigma =>
      .arrowCode (domainCode.subst sigma) (codomainCode.subst sigma)
  | _, _, .piTyCode domainCode codomainCode, sigma =>
      .piTyCode (domainCode.subst sigma) (codomainCode.subst sigma.lift)
  | _, _, .sigmaTyCode domainCode codomainCode, sigma =>
      .sigmaTyCode (domainCode.subst sigma) (codomainCode.subst sigma.lift)
  | _, _, .productCode firstCode secondCode, sigma =>
      .productCode (firstCode.subst sigma) (secondCode.subst sigma)
  | _, _, .sumCode leftCode rightCode, sigma =>
      .sumCode (leftCode.subst sigma) (rightCode.subst sigma)
  | _, _, .listCode elementCode, sigma =>
      .listCode (elementCode.subst sigma)
  | _, _, .optionCode elementCode, sigma =>
      .optionCode (elementCode.subst sigma)
  | _, _, .eitherCode leftCode rightCode, sigma =>
      .eitherCode (leftCode.subst sigma) (rightCode.subst sigma)
  | _, _, .idCode typeCode leftRaw rightRaw, sigma =>
      .idCode (typeCode.subst sigma) (leftRaw.subst sigma) (rightRaw.subst sigma)
  | _, _, .equivCode leftTypeCode rightTypeCode, sigma =>
      .equivCode (leftTypeCode.subst sigma) (rightTypeCode.subst sigma)
  -- CUMUL-2.6 cumulUpMarker arm.
  | _, _, .cumulUpMarker innerCodeRaw, sigma =>
      .cumulUpMarker (innerCodeRaw.subst sigma)
  -- D3.6-P1 uaToEquiv arm.
  | _, _, .uaToEquiv proofRaw, sigma =>
      .uaToEquiv (proofRaw.subst sigma)
  -- D3.6-P2 equivApply arm.
  | _, _, .equivApply equivRaw argRaw, sigma =>
      .equivApply (equivRaw.subst sigma) (argRaw.subst sigma)
  -- D3.6-S3 pathCompose arm.
  | _, _, .pathCompose leftPathRaw rightPathRaw, sigma =>
      .pathCompose (leftPathRaw.subst sigma) (rightPathRaw.subst sigma)
  -- D3.6-S4 idToEquiv arm.
  | _, _, .idToEquiv proofRaw, sigma =>
      .idToEquiv (proofRaw.subst sigma)
  -- D3.6-S5 oeqTrans arm.
  | _, _, .oeqTrans firstProof secondProof, sigma =>
      .oeqTrans (firstProof.subst sigma) (secondProof.subst sigma)
  -- D3.6-S5 equivCompose arm.
  | _, _, .equivCompose firstEquiv secondEquiv, sigma =>
      .equivCompose (firstEquiv.subst sigma) (secondEquiv.subst sigma)
  -- D2.5.6-Blocker-A transpFill arm.  Ternary atom-shape (no binder).
  | _, _, .transpFill pathTy currentInterval source, sigma =>
      .transpFill (pathTy.subst sigma)
                  (currentInterval.subst sigma)
                  (source.subst sigma)

/-- Single-variable substitution: substitute `rawArg` for var 0. -/
@[reducible] def RawTerm.subst0 {scope : Nat} (body : RawTerm (scope + 1))
    (rawArg : RawTerm scope) : RawTerm scope :=
  body.subst (RawTermSubst.singleton rawArg)

end LeanFX2
