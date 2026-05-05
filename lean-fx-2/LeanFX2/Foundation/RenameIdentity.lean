import LeanFX2.Foundation.Ty

/-! # Foundation/RenameIdentity — identity-renaming preserves terms

`RawTerm.rename ρ_id t = t` and `Ty.rename ρ_id T = T`: applying the
identity raw renaming is a no-op.  These are needed for any "identity"
proof at the typed Term level (e.g., `Term.rename id t ≅ t`), and
are foundational for canonical-form lemmas in elaboration / Algo.

## Why not in `Foundation/RawSubst.lean` / `Foundation/Ty.lean`?

These two files focus on the structural `rename` / `subst` definitions
plus the most-used commute lemmas.  Identity-specific lemmas are a
separate concern (they're used in elaboration + proof identity, not in
the kernel reduction itself).  Isolating them keeps the dependency
graph clean: this file ONLY adds rfl-projection identity laws, no new
kernel definitions.

## Lemma chain

1. `RawRenaming.identity_lift_pointwise` — id.lift agrees pointwise with id
2. `RawTerm.rename_identity` — RawTerm structural; uses lift_pointwise + rename_pointwise
3. `Ty.rename_identity` — Ty structural; uses RawTerm.rename_identity for `id` arm + lift_pointwise + Ty.rename_pointwise

Each is zero-axiom because it uses only structural recursion + pointwise
lemmas which are themselves zero-axiom.
-/

namespace LeanFX2

/-! ## RawRenaming.identity is pointwise-equal to its lift

`identity.lift` evaluates pattern-by-pattern on `Fin (n+1)`: position 0
goes to position 0, successor positions go to `Fin.succ` of the
identity at the predecessor.  Both reduce to the input position. -/

theorem RawRenaming.identity_lift_pointwise {scope : Nat} :
    ∀ position, (@RawRenaming.identity scope).lift position = position
  | ⟨0, _⟩     => rfl
  | ⟨_ + 1, _⟩ => rfl

/-! ## RawTerm.rename_identity

Structural induction: var case is rfl.  Binders use the lift_pointwise
lemma to bridge `body.rename identity.lift` to `body.rename identity`
via `RawTerm.rename_pointwise`. -/

theorem RawTerm.rename_identity {scope : Nat} :
    ∀ (term : RawTerm scope), term.rename RawRenaming.identity = term
  | .var _ => rfl
  | .unit => rfl
  | .lam body => by
      show (body.rename (@RawRenaming.identity scope).lift).lam = body.lam
      rw [RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) body,
          RawTerm.rename_identity body]
  | .app fnTerm argTerm => by
      show (fnTerm.rename _).app (argTerm.rename _) = (fnTerm.app argTerm)
      rw [RawTerm.rename_identity fnTerm, RawTerm.rename_identity argTerm]
  | .pair firstTerm secondTerm => by
      show (firstTerm.rename _).pair (secondTerm.rename _) = (firstTerm.pair secondTerm)
      rw [RawTerm.rename_identity firstTerm, RawTerm.rename_identity secondTerm]
  | .fst pairTerm => by
      show (pairTerm.rename _).fst = pairTerm.fst
      rw [RawTerm.rename_identity pairTerm]
  | .snd pairTerm => by
      show (pairTerm.rename _).snd = pairTerm.snd
      rw [RawTerm.rename_identity pairTerm]
  | .boolTrue => rfl
  | .boolFalse => rfl
  | .boolElim scrutinee thenBranch elseBranch => by
      show (scrutinee.rename _).boolElim (thenBranch.rename _) (elseBranch.rename _) =
           scrutinee.boolElim thenBranch elseBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity thenBranch,
          RawTerm.rename_identity elseBranch]
  | .natZero => rfl
  | .natSucc predecessor => by
      show (predecessor.rename _).natSucc = predecessor.natSucc
      rw [RawTerm.rename_identity predecessor]
  | .natElim scrutinee zeroBranch succBranch => by
      show (scrutinee.rename _).natElim (zeroBranch.rename _) (succBranch.rename _) =
           scrutinee.natElim zeroBranch succBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity zeroBranch,
          RawTerm.rename_identity succBranch]
  | .natRec scrutinee zeroBranch succBranch => by
      show (scrutinee.rename _).natRec (zeroBranch.rename _) (succBranch.rename _) =
           scrutinee.natRec zeroBranch succBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity zeroBranch,
          RawTerm.rename_identity succBranch]
  | .listNil => rfl
  | .listCons headTerm tailTerm => by
      show (headTerm.rename _).listCons (tailTerm.rename _) = headTerm.listCons tailTerm
      rw [RawTerm.rename_identity headTerm, RawTerm.rename_identity tailTerm]
  | .listElim scrutinee nilBranch consBranch => by
      show (scrutinee.rename _).listElim (nilBranch.rename _) (consBranch.rename _) =
           scrutinee.listElim nilBranch consBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity nilBranch,
          RawTerm.rename_identity consBranch]
  | .optionNone => rfl
  | .optionSome valueTerm => by
      show (valueTerm.rename _).optionSome = valueTerm.optionSome
      rw [RawTerm.rename_identity valueTerm]
  | .optionMatch scrutinee noneBranch someBranch => by
      show (scrutinee.rename _).optionMatch (noneBranch.rename _) (someBranch.rename _) =
           scrutinee.optionMatch noneBranch someBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity noneBranch,
          RawTerm.rename_identity someBranch]
  | .eitherInl valueTerm => by
      show (valueTerm.rename _).eitherInl = valueTerm.eitherInl
      rw [RawTerm.rename_identity valueTerm]
  | .eitherInr valueTerm => by
      show (valueTerm.rename _).eitherInr = valueTerm.eitherInr
      rw [RawTerm.rename_identity valueTerm]
  | .eitherMatch scrutinee leftBranch rightBranch => by
      show (scrutinee.rename _).eitherMatch (leftBranch.rename _) (rightBranch.rename _) =
           scrutinee.eitherMatch leftBranch rightBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity leftBranch,
          RawTerm.rename_identity rightBranch]
  | .refl rawWitness => by
      show (rawWitness.rename _).refl = rawWitness.refl
      rw [RawTerm.rename_identity rawWitness]
  | .idJ baseRaw witnessRaw => by
      show (baseRaw.rename _).idJ (witnessRaw.rename _) = baseRaw.idJ witnessRaw
      rw [RawTerm.rename_identity baseRaw, RawTerm.rename_identity witnessRaw]
  | .modIntro innerTerm => by
      show (innerTerm.rename _).modIntro = innerTerm.modIntro
      rw [RawTerm.rename_identity innerTerm]
  | .modElim innerTerm => by
      show (innerTerm.rename _).modElim = innerTerm.modElim
      rw [RawTerm.rename_identity innerTerm]
  | .subsume innerTerm => by
      show (innerTerm.rename _).subsume = innerTerm.subsume
      rw [RawTerm.rename_identity innerTerm]
  -- D1.6 cubical interval + path
  | .interval0 => rfl
  | .interval1 => rfl
  | .intervalOpp intervalTerm => by
      show (intervalTerm.rename _).intervalOpp = intervalTerm.intervalOpp
      rw [RawTerm.rename_identity intervalTerm]
  | .intervalMeet leftInterval rightInterval => by
      show (leftInterval.rename _).intervalMeet (rightInterval.rename _) =
           leftInterval.intervalMeet rightInterval
      rw [RawTerm.rename_identity leftInterval, RawTerm.rename_identity rightInterval]
  | .intervalJoin leftInterval rightInterval => by
      show (leftInterval.rename _).intervalJoin (rightInterval.rename _) =
           leftInterval.intervalJoin rightInterval
      rw [RawTerm.rename_identity leftInterval, RawTerm.rename_identity rightInterval]
  | .pathLam body => by
      show (body.rename (@RawRenaming.identity scope).lift).pathLam = body.pathLam
      rw [RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) body,
          RawTerm.rename_identity body]
  | .pathApp pathTerm intervalArg => by
      show (pathTerm.rename _).pathApp (intervalArg.rename _) =
           pathTerm.pathApp intervalArg
      rw [RawTerm.rename_identity pathTerm, RawTerm.rename_identity intervalArg]
  | .glueIntro baseValue partialValue => by
      show (baseValue.rename _).glueIntro (partialValue.rename _) =
           baseValue.glueIntro partialValue
      rw [RawTerm.rename_identity baseValue, RawTerm.rename_identity partialValue]
  | .glueElim gluedValue => by
      show (gluedValue.rename _).glueElim = gluedValue.glueElim
      rw [RawTerm.rename_identity gluedValue]
  | .transp pathTerm sourceTerm => by
      show (pathTerm.rename _).transp (sourceTerm.rename _) =
           pathTerm.transp sourceTerm
      rw [RawTerm.rename_identity pathTerm, RawTerm.rename_identity sourceTerm]
  | .hcomp sidesTerm capTerm => by
      show (sidesTerm.rename _).hcomp (capTerm.rename _) =
           sidesTerm.hcomp capTerm
      rw [RawTerm.rename_identity sidesTerm, RawTerm.rename_identity capTerm]
  -- D1.6 observational + strict equality
  | .oeqRefl witnessTerm => by
      show (witnessTerm.rename _).oeqRefl = witnessTerm.oeqRefl
      rw [RawTerm.rename_identity witnessTerm]
  | .oeqJ baseCase witness => by
      show (baseCase.rename _).oeqJ (witness.rename _) = baseCase.oeqJ witness
      rw [RawTerm.rename_identity baseCase, RawTerm.rename_identity witness]
  | .oeqFunext pointwiseEquality => by
      show (pointwiseEquality.rename _).oeqFunext = pointwiseEquality.oeqFunext
      rw [RawTerm.rename_identity pointwiseEquality]
  | .idStrictRefl witnessTerm => by
      show (witnessTerm.rename _).idStrictRefl = witnessTerm.idStrictRefl
      rw [RawTerm.rename_identity witnessTerm]
  | .idStrictRec baseCase witness => by
      show (baseCase.rename _).idStrictRec (witness.rename _) =
           baseCase.idStrictRec witness
      rw [RawTerm.rename_identity baseCase, RawTerm.rename_identity witness]
  -- D1.6 type equivalence
  | .equivIntro forwardFn backwardFn => by
      show (forwardFn.rename _).equivIntro (backwardFn.rename _) =
           forwardFn.equivIntro backwardFn
      rw [RawTerm.rename_identity forwardFn, RawTerm.rename_identity backwardFn]
  | .equivApp equivTerm argument => by
      show (equivTerm.rename _).equivApp (argument.rename _) =
           equivTerm.equivApp argument
      rw [RawTerm.rename_identity equivTerm, RawTerm.rename_identity argument]
  -- D1.6 refinement / record / codata
  | .refineIntro rawValue predicateProof => by
      show (rawValue.rename _).refineIntro (predicateProof.rename _) =
           rawValue.refineIntro predicateProof
      rw [RawTerm.rename_identity rawValue, RawTerm.rename_identity predicateProof]
  | .refineElim refinedValue => by
      show (refinedValue.rename _).refineElim = refinedValue.refineElim
      rw [RawTerm.rename_identity refinedValue]
  | .recordIntro firstField => by
      show (firstField.rename _).recordIntro = firstField.recordIntro
      rw [RawTerm.rename_identity firstField]
  | .recordProj recordValue => by
      show (recordValue.rename _).recordProj = recordValue.recordProj
      rw [RawTerm.rename_identity recordValue]
  | .codataUnfold initialState transition => by
      show (initialState.rename _).codataUnfold (transition.rename _) =
           initialState.codataUnfold transition
      rw [RawTerm.rename_identity initialState, RawTerm.rename_identity transition]
  | .codataDest codataValue => by
      show (codataValue.rename _).codataDest = codataValue.codataDest
      rw [RawTerm.rename_identity codataValue]
  -- D1.6 sessions, effects
  | .sessionSend channel payload => by
      show (channel.rename _).sessionSend (payload.rename _) =
           channel.sessionSend payload
      rw [RawTerm.rename_identity channel, RawTerm.rename_identity payload]
  | .sessionRecv channel => by
      show (channel.rename _).sessionRecv = channel.sessionRecv
      rw [RawTerm.rename_identity channel]
  | .effectPerform operationTag arguments => by
      show (operationTag.rename _).effectPerform (arguments.rename _) =
           operationTag.effectPerform arguments
      rw [RawTerm.rename_identity operationTag, RawTerm.rename_identity arguments]
  | .universeCode innerLevel => rfl
  -- CUMUL-2.1 per-shape type codes.
  | .arrowCode domainCode codomainCode => by
      show (domainCode.rename _).arrowCode (codomainCode.rename _) =
           domainCode.arrowCode codomainCode
      rw [RawTerm.rename_identity domainCode, RawTerm.rename_identity codomainCode]
  | .piTyCode domainCode codomainCode => by
      show (domainCode.rename _).piTyCode
             (codomainCode.rename (@RawRenaming.identity scope).lift) =
           domainCode.piTyCode codomainCode
      rw [RawTerm.rename_identity domainCode,
          RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) codomainCode,
          RawTerm.rename_identity codomainCode]
  | .sigmaTyCode domainCode codomainCode => by
      show (domainCode.rename _).sigmaTyCode
             (codomainCode.rename (@RawRenaming.identity scope).lift) =
           domainCode.sigmaTyCode codomainCode
      rw [RawTerm.rename_identity domainCode,
          RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) codomainCode,
          RawTerm.rename_identity codomainCode]
  | .productCode firstCode secondCode => by
      show (firstCode.rename _).productCode (secondCode.rename _) =
           firstCode.productCode secondCode
      rw [RawTerm.rename_identity firstCode, RawTerm.rename_identity secondCode]
  | .sumCode leftCode rightCode => by
      show (leftCode.rename _).sumCode (rightCode.rename _) =
           leftCode.sumCode rightCode
      rw [RawTerm.rename_identity leftCode, RawTerm.rename_identity rightCode]
  | .listCode elementCode => by
      show (elementCode.rename _).listCode = elementCode.listCode
      rw [RawTerm.rename_identity elementCode]
  | .optionCode elementCode => by
      show (elementCode.rename _).optionCode = elementCode.optionCode
      rw [RawTerm.rename_identity elementCode]
  | .eitherCode leftCode rightCode => by
      show (leftCode.rename _).eitherCode (rightCode.rename _) =
           leftCode.eitherCode rightCode
      rw [RawTerm.rename_identity leftCode, RawTerm.rename_identity rightCode]
  | .idCode typeCode leftRaw rightRaw => by
      show (typeCode.rename _).idCode (leftRaw.rename _) (rightRaw.rename _) =
           typeCode.idCode leftRaw rightRaw
      rw [RawTerm.rename_identity typeCode,
          RawTerm.rename_identity leftRaw,
          RawTerm.rename_identity rightRaw]
  | .equivCode leftTypeCode rightTypeCode => by
      show (leftTypeCode.rename _).equivCode (rightTypeCode.rename _) =
           leftTypeCode.equivCode rightTypeCode
      rw [RawTerm.rename_identity leftTypeCode, RawTerm.rename_identity rightTypeCode]
  -- CUMUL-2.6: cumulUpMarker — recurse on inner code raw.
  | .cumulUpMarker innerCodeRaw => by
      show (innerCodeRaw.rename _).cumulUpMarker = innerCodeRaw.cumulUpMarker
      rw [RawTerm.rename_identity innerCodeRaw]

/-! ## Ty.rename_identity

Structural induction over Ty.  The `id` ctor's arms (left/right
endpoints) are RawTerms, so they reduce via `RawTerm.rename_identity`. -/

theorem Ty.rename_identity {level scope : Nat} :
    ∀ (someType : Ty level scope),
      someType.rename RawRenaming.identity = someType
  | .unit => rfl
  | .bool => rfl
  | .nat  => rfl
  | .arrow domainType codomainType => by
      show (domainType.rename _).arrow (codomainType.rename _) =
           domainType.arrow codomainType
      rw [Ty.rename_identity domainType, Ty.rename_identity codomainType]
  | .piTy domainType codomainType => by
      show (domainType.rename _).piTy (codomainType.rename _) =
           domainType.piTy codomainType
      rw [Ty.rename_identity domainType,
          Ty.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) codomainType,
          Ty.rename_identity codomainType]
  | .sigmaTy firstType secondType => by
      show (firstType.rename _).sigmaTy (secondType.rename _) =
           firstType.sigmaTy secondType
      rw [Ty.rename_identity firstType,
          Ty.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) secondType,
          Ty.rename_identity secondType]
  | .tyVar _ => rfl
  | .id carrier leftEndpoint rightEndpoint => by
      show (carrier.rename _).id (leftEndpoint.rename _) (rightEndpoint.rename _) =
           carrier.id leftEndpoint rightEndpoint
      rw [Ty.rename_identity carrier,
          RawTerm.rename_identity leftEndpoint,
          RawTerm.rename_identity rightEndpoint]
  | .listType elementType => by
      show (elementType.rename _).listType = elementType.listType
      rw [Ty.rename_identity elementType]
  | .optionType elementType => by
      show (elementType.rename _).optionType = elementType.optionType
      rw [Ty.rename_identity elementType]
  | .eitherType leftType rightType => by
      show (leftType.rename _).eitherType (rightType.rename _) =
           leftType.eitherType rightType
      rw [Ty.rename_identity leftType, Ty.rename_identity rightType]
  | .universe universeLevel levelLe => rfl
  | .empty => rfl
  | .interval => rfl
  | .path carrier leftEndpoint rightEndpoint => by
      show (carrier.rename _).path (leftEndpoint.rename _) (rightEndpoint.rename _) =
           carrier.path leftEndpoint rightEndpoint
      rw [Ty.rename_identity carrier,
          RawTerm.rename_identity leftEndpoint,
          RawTerm.rename_identity rightEndpoint]
  | .glue baseType boundaryWitness => by
      show (baseType.rename _).glue (boundaryWitness.rename _) =
           baseType.glue boundaryWitness
      rw [Ty.rename_identity baseType, RawTerm.rename_identity boundaryWitness]
  | .oeq carrier leftEndpoint rightEndpoint => by
      show (carrier.rename _).oeq (leftEndpoint.rename _) (rightEndpoint.rename _) =
           carrier.oeq leftEndpoint rightEndpoint
      rw [Ty.rename_identity carrier,
          RawTerm.rename_identity leftEndpoint,
          RawTerm.rename_identity rightEndpoint]
  | .idStrict carrier leftEndpoint rightEndpoint => by
      show (carrier.rename _).idStrict (leftEndpoint.rename _) (rightEndpoint.rename _) =
           carrier.idStrict leftEndpoint rightEndpoint
      rw [Ty.rename_identity carrier,
          RawTerm.rename_identity leftEndpoint,
          RawTerm.rename_identity rightEndpoint]
  | .equiv domainType codomainType => by
      show (domainType.rename _).equiv (codomainType.rename _) =
           domainType.equiv codomainType
      rw [Ty.rename_identity domainType, Ty.rename_identity codomainType]
  | .refine baseType predicate => by
      show (baseType.rename _).refine (predicate.rename _) =
           baseType.refine predicate
      rw [Ty.rename_identity baseType,
          RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) predicate,
          RawTerm.rename_identity predicate]
  | .record singleFieldType => by
      show (singleFieldType.rename _).record = singleFieldType.record
      rw [Ty.rename_identity singleFieldType]
  | .codata stateType outputType => by
      show (stateType.rename _).codata (outputType.rename _) =
           stateType.codata outputType
      rw [Ty.rename_identity stateType, Ty.rename_identity outputType]
  | .session protocolStep => by
      show Ty.session (protocolStep.rename _) = Ty.session protocolStep
      rw [RawTerm.rename_identity protocolStep]
  | .effect carrierType effectTag => by
      show (carrierType.rename _).effect (effectTag.rename _) =
           carrierType.effect effectTag
      rw [Ty.rename_identity carrierType, RawTerm.rename_identity effectTag]
  | .modal modalityTag carrierType => by
      show Ty.modal modalityTag (carrierType.rename _) =
           Ty.modal modalityTag carrierType
      rw [Ty.rename_identity carrierType]

end LeanFX2
