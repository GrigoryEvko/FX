import LeanFX2.Foundation.RawTerm

/-! # LeanFX2.Foundation.RawSubst.RenameDefs

Raw renaming type, identity / lift / weaken / compose, `RawTerm.rename`
structural definition, and `RawTerm.weaken`.

## Root status

Layer 0 raw-syntax definitions. Strict zero-axiom. -/

namespace LeanFX2

/-! ## Renamings -/

/-- A raw rawRenaming: `Fin source → Fin target`. -/
@[reducible] def RawRenaming (source target : Nat) : Type := Fin source → Fin target

/-- Identity rawRenaming. -/
@[reducible] def RawRenaming.identity {scope : Nat} : RawRenaming scope scope :=
  fun position => position

/-- Lift rawRenaming under a binder: position 0 stays, others shift. -/
@[reducible] def RawRenaming.lift {source target : Nat}
    (rawRenaming : RawRenaming source target) : RawRenaming (source + 1) (target + 1)
  | ⟨0, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => Fin.succ (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Weakening rawRenaming: shift all positions by 1. -/
@[reducible] def RawRenaming.weaken {scope : Nat} : RawRenaming scope (scope + 1) :=
  fun position => Fin.succ position

/-- Compose two rawRenamings. -/
@[reducible] def RawRenaming.compose {scopeA scopeB scopeC : Nat}
    (firstRenaming : RawRenaming scopeA scopeB)
    (secondRenaming : RawRenaming scopeB scopeC) :
    RawRenaming scopeA scopeC :=
  fun position => secondRenaming (firstRenaming position)

/-- Apply a rawRenaming to a raw term. -/
def RawTerm.rename : ∀ {source target : Nat},
    RawTerm source → RawRenaming source target → RawTerm target
  | _, _, .var position, rawRenaming => .var (rawRenaming position)
  | _, _, .unit, _ => .unit
  | _, _, .lam body, rawRenaming => .lam (body.rename rawRenaming.lift)
  | _, _, .app functionTerm argumentTerm, rawRenaming =>
      .app (functionTerm.rename rawRenaming) (argumentTerm.rename rawRenaming)
  | _, _, .pair firstValue secondValue, rawRenaming =>
      .pair (firstValue.rename rawRenaming) (secondValue.rename rawRenaming)
  | _, _, .fst pairTerm, rawRenaming => .fst (pairTerm.rename rawRenaming)
  | _, _, .snd pairTerm, rawRenaming => .snd (pairTerm.rename rawRenaming)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, rawRenaming =>
      .boolElim (scrutinee.rename rawRenaming)
                (thenBranch.rename rawRenaming)
                (elseBranch.rename rawRenaming)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, rawRenaming => .natSucc (predecessor.rename rawRenaming)
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
      .listCons (headTerm.rename rawRenaming) (tailTerm.rename rawRenaming)
  | _, _, .listElim scrutinee nilBranch consBranch, rawRenaming =>
      .listElim (scrutinee.rename rawRenaming)
                (nilBranch.rename rawRenaming)
                (consBranch.rename rawRenaming)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, rawRenaming => .optionSome (valueTerm.rename rawRenaming)
  | _, _, .optionMatch scrutinee noneBranch someBranch, rawRenaming =>
      .optionMatch (scrutinee.rename rawRenaming)
                   (noneBranch.rename rawRenaming)
                   (someBranch.rename rawRenaming)
  | _, _, .eitherInl valueTerm, rawRenaming => .eitherInl (valueTerm.rename rawRenaming)
  | _, _, .eitherInr valueTerm, rawRenaming => .eitherInr (valueTerm.rename rawRenaming)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, rawRenaming =>
      .eitherMatch (scrutinee.rename rawRenaming)
                   (leftBranch.rename rawRenaming)
                   (rightBranch.rename rawRenaming)
  | _, _, .refl rawWitness, rawRenaming => .refl (rawWitness.rename rawRenaming)
  | _, _, .idJ baseCase witness, rawRenaming =>
      .idJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .modIntro inner, rawRenaming => .modIntro (inner.rename rawRenaming)
  | _, _, .modElim inner, rawRenaming => .modElim (inner.rename rawRenaming)
  | _, _, .subsume inner, rawRenaming => .subsume (inner.rename rawRenaming)
  -- D1.6 cubical interval + path
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp i, rawRenaming => .intervalOpp (i.rename rawRenaming)
  | _, _, .intervalMeet l r, rawRenaming =>
      .intervalMeet (l.rename rawRenaming) (r.rename rawRenaming)
  | _, _, .intervalJoin l r, rawRenaming =>
      .intervalJoin (l.rename rawRenaming) (r.rename rawRenaming)
  | _, _, .pathLam body, rawRenaming =>
      .pathLam (body.rename rawRenaming.lift)
  | _, _, .pathApp pathTerm intervalArg, rawRenaming =>
      .pathApp (pathTerm.rename rawRenaming) (intervalArg.rename rawRenaming)
  | _, _, .glueIntro baseValue partialValue, rawRenaming =>
      .glueIntro (baseValue.rename rawRenaming) (partialValue.rename rawRenaming)
  | _, _, .glueElim gluedValue, rawRenaming =>
      .glueElim (gluedValue.rename rawRenaming)
  | _, _, .transp path source, rawRenaming =>
      .transp (path.rename rawRenaming) (source.rename rawRenaming)
  | _, _, .hcomp sides cap, rawRenaming =>
      .hcomp (sides.rename rawRenaming) (cap.rename rawRenaming)
  -- D1.6 observational + strict equality
  | _, _, .oeqRefl witness, rawRenaming => .oeqRefl (witness.rename rawRenaming)
  | _, _, .oeqJ baseCase witness, rawRenaming =>
      .oeqJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .oeqFunext pointwiseEquality, rawRenaming =>
      .oeqFunext (pointwiseEquality.rename rawRenaming)
  | _, _, .idStrictRefl witness, rawRenaming =>
      .idStrictRefl (witness.rename rawRenaming)
  | _, _, .idStrictRec baseCase witness, rawRenaming =>
      .idStrictRec (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  -- D1.6 type equivalence
  | _, _, .equivIntro fwd bwd, rawRenaming =>
      .equivIntro (fwd.rename rawRenaming) (bwd.rename rawRenaming)
  | _, _, .equivApp equivTerm argument, rawRenaming =>
      .equivApp (equivTerm.rename rawRenaming) (argument.rename rawRenaming)
  -- D1.6 refinement, record, codata
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
  -- D1.6 sessions, effects
  | _, _, .sessionSend channel payload, rawRenaming =>
      .sessionSend (channel.rename rawRenaming) (payload.rename rawRenaming)
  | _, _, .sessionRecv channel, rawRenaming =>
      .sessionRecv (channel.rename rawRenaming)
  | _, _, .effectPerform operationTag arguments, rawRenaming =>
      .effectPerform (operationTag.rename rawRenaming)
                     (arguments.rename rawRenaming)
  -- D1.6/A2: universeCode is scope-polymorphic — rename is identity
  -- on the inner-level payload (no Fin variables to remap).
  | _, _, .universeCode innerLevel, _ =>
      .universeCode innerLevel
  -- CUMUL-2.1 per-shape type codes.
  | _, _, .arrowCode domainCode codomainCode, rawRenaming =>
      .arrowCode (domainCode.rename rawRenaming) (codomainCode.rename rawRenaming)
  | _, _, .piTyCode domainCode codomainCode, rawRenaming =>
      .piTyCode (domainCode.rename rawRenaming)
                (codomainCode.rename rawRenaming.lift)
  | _, _, .sigmaTyCode domainCode codomainCode, rawRenaming =>
      .sigmaTyCode (domainCode.rename rawRenaming)
                   (codomainCode.rename rawRenaming.lift)
  | _, _, .productCode firstCode secondCode, rawRenaming =>
      .productCode (firstCode.rename rawRenaming) (secondCode.rename rawRenaming)
  | _, _, .sumCode leftCode rightCode, rawRenaming =>
      .sumCode (leftCode.rename rawRenaming) (rightCode.rename rawRenaming)
  | _, _, .listCode elementCode, rawRenaming =>
      .listCode (elementCode.rename rawRenaming)
  | _, _, .optionCode elementCode, rawRenaming =>
      .optionCode (elementCode.rename rawRenaming)
  | _, _, .eitherCode leftCode rightCode, rawRenaming =>
      .eitherCode (leftCode.rename rawRenaming) (rightCode.rename rawRenaming)
  | _, _, .idCode typeCode leftRaw rightRaw, rawRenaming =>
      .idCode (typeCode.rename rawRenaming)
              (leftRaw.rename rawRenaming)
              (rightRaw.rename rawRenaming)
  | _, _, .equivCode leftTypeCode rightTypeCode, rawRenaming =>
      .equivCode (leftTypeCode.rename rawRenaming)
                 (rightTypeCode.rename rawRenaming)
  -- CUMUL-2.6 cumulUpMarker arm.
  | _, _, .cumulUpMarker innerCodeRaw, rawRenaming =>
      .cumulUpMarker (innerCodeRaw.rename rawRenaming)
  -- D3.6-P1 uaToEquiv arm.
  | _, _, .uaToEquiv proofRaw, rawRenaming =>
      .uaToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-P2 equivApply arm.
  | _, _, .equivApply equivRaw argRaw, rawRenaming =>
      .equivApply (equivRaw.rename rawRenaming) (argRaw.rename rawRenaming)
  -- D3.6-S3 pathCompose arm.
  | _, _, .pathCompose leftPathRaw rightPathRaw, rawRenaming =>
      .pathCompose (leftPathRaw.rename rawRenaming) (rightPathRaw.rename rawRenaming)
  -- D3.6-S4 idToEquiv arm.
  | _, _, .idToEquiv proofRaw, rawRenaming =>
      .idToEquiv (proofRaw.rename rawRenaming)
  -- D3.6-S5 oeqTrans arm.
  | _, _, .oeqTrans firstProof secondProof, rawRenaming =>
      .oeqTrans (firstProof.rename rawRenaming) (secondProof.rename rawRenaming)
  -- D3.6-S5 equivCompose arm.
  | _, _, .equivCompose firstEquiv secondEquiv, rawRenaming =>
      .equivCompose (firstEquiv.rename rawRenaming) (secondEquiv.rename rawRenaming)

/-- Single-binder weakening on a raw term. -/
@[reducible] def RawTerm.weaken {scope : Nat} (term : RawTerm scope) : RawTerm (scope + 1) :=
  term.rename RawRenaming.weaken

end LeanFX2
