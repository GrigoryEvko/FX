import LeanFX2.Confluence.RawCd.ArrowFamily
import LeanFX2.Confluence.RawCd.ModalAndRefine
import LeanFX2.Confluence.RawCd.RecordAndCodata
import LeanFX2.Confluence.RawCd.SigmaArms
import LeanFX2.Confluence.RawCd.BoolNatArms
import LeanFX2.Confluence.RawCd.ListOptionEitherArms
import LeanFX2.Confluence.RawCd.IdentityArms
import LeanFX2.Confluence.RawCd.CubicalAndEquiv

/-! # LeanFX2.Confluence.RawCd.Core

Main `RawTerm.cd` dispatcher — one short arm per RawTerm ctor.
Atomic ctors (var, unit, *True/False/Zero/Nil/None) → identity.
Cong ctors → recurse into subterms.  Redex-bearing ctors → dispatch
to the per-redex helper definitions in sibling sub-modules.

## Root status

Layer 2 confluence aggregator.  Consumed by `Confluence.RawCd` shim
and downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- Complete development on raw terms.  Maximal parallel reduct:
every visible redex contracts, every subterm is recursively
developed.  Zero axioms: full enumeration in every inner match
keeps Lean's match compiler from leaking propext.

Each redex-bearing case dispatches to a per-redex helper
(`cdAppCase`, `cdFstCase`, ..., `cdIdStrictRecCase`) — see comment at top.
This factoring keeps `unfold RawTerm.cd` cheap and confines the
55-arm inner match to one helper definition at a time, fitting the
200K-heartbeat budget enforced by simp's nested whnf. -/
def RawTerm.cd : ∀ {scope : Nat}, RawTerm scope → RawTerm scope
  | _, .var position => RawTerm.var position
  | _, .unit => RawTerm.unit
  | _, .lam body => RawTerm.lam (RawTerm.cd body)
  | _, .app functionTerm argumentTerm =>
      RawTerm.cdAppCase (RawTerm.cd functionTerm) (RawTerm.cd argumentTerm)
  | _, .pair firstValue secondValue =>
      RawTerm.pair (RawTerm.cd firstValue) (RawTerm.cd secondValue)
  | _, .fst pairTerm =>
      RawTerm.cdFstCase (RawTerm.cd pairTerm)
  | _, .snd pairTerm =>
      RawTerm.cdSndCase (RawTerm.cd pairTerm)
  | _, .boolTrue => RawTerm.boolTrue
  | _, .boolFalse => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      RawTerm.cdBoolElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd thenBranch) (RawTerm.cd elseBranch)
  | _, .natZero => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc (RawTerm.cd predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      RawTerm.cdNatElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd zeroBranch) (RawTerm.cd succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      RawTerm.cdNatRecCase (RawTerm.cd scrutinee)
        (RawTerm.cd zeroBranch) (RawTerm.cd succBranch)
  | _, .listNil => RawTerm.listNil
  | _, .listCons headTerm tailTerm =>
      RawTerm.listCons (RawTerm.cd headTerm) (RawTerm.cd tailTerm)
  | _, .listElim scrutinee nilBranch consBranch =>
      RawTerm.cdListElimCase (RawTerm.cd scrutinee)
        (RawTerm.cd nilBranch) (RawTerm.cd consBranch)
  | _, .optionNone => RawTerm.optionNone
  | _, .optionSome valueTerm => RawTerm.optionSome (RawTerm.cd valueTerm)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      RawTerm.cdOptionMatchCase (RawTerm.cd scrutinee)
        (RawTerm.cd noneBranch) (RawTerm.cd someBranch)
  | _, .eitherInl valueTerm => RawTerm.eitherInl (RawTerm.cd valueTerm)
  | _, .eitherInr valueTerm => RawTerm.eitherInr (RawTerm.cd valueTerm)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      RawTerm.cdEitherMatchCase (RawTerm.cd scrutinee)
        (RawTerm.cd leftBranch) (RawTerm.cd rightBranch)
  | _, .refl rawWitness => RawTerm.refl (RawTerm.cd rawWitness)
  | _, .idJ baseCase witness =>
      RawTerm.cdIdJCase (RawTerm.cd baseCase) (RawTerm.cd witness)
  | _, .modIntro innerTerm => RawTerm.modIntro (RawTerm.cd innerTerm)
  | _, .modElim innerTerm => RawTerm.cdModElimCase (RawTerm.cd innerTerm)
  | _, .subsume innerTerm => RawTerm.subsume (RawTerm.cd innerTerm)
  -- D1.6/D2.5: cubical interval + path; pathApp has betaPathApp.
  | _, .interval0 => RawTerm.interval0
  | _, .interval1 => RawTerm.interval1
  | _, .intervalOpp intervalTerm => RawTerm.intervalOpp (RawTerm.cd intervalTerm)
  | _, .intervalMeet leftInterval rightInterval =>
      RawTerm.intervalMeet (RawTerm.cd leftInterval) (RawTerm.cd rightInterval)
  | _, .intervalJoin leftInterval rightInterval =>
      RawTerm.intervalJoin (RawTerm.cd leftInterval) (RawTerm.cd rightInterval)
  | _, .pathLam body => RawTerm.pathLam (RawTerm.cd body)
  | _, .pathApp pathTerm intervalArg =>
      RawTerm.cdPathAppCase (RawTerm.cd pathTerm) (RawTerm.cd intervalArg)
  | _, .glueIntro baseValue partialValue =>
      RawTerm.glueIntro (RawTerm.cd baseValue) (RawTerm.cd partialValue)
  | _, .glueElim gluedValue => RawTerm.cdGlueElimCase (RawTerm.cd gluedValue)
  | _, .transp pathTerm sourceTerm =>
      -- D2.5.4-G: cdTranspCase fires β when developed path is
      -- `pathLam X.weaken` (constant path, body in image of weaken),
      -- otherwise plain transp cong.  The β-firing branch needs
      -- `RawStep.par.weaken_inv` (Phase G.0, shipped) to discharge
      -- cd_lemma's transpReflBeta arm via the developed path's body
      -- being preserved as a weakened term under par.
      RawTerm.cdTranspCase (RawTerm.cd pathTerm) (RawTerm.cd sourceTerm)
  | _, .hcomp sidesTerm capTerm =>
      RawTerm.hcomp (RawTerm.cd sidesTerm) (RawTerm.cd capTerm)
  -- D1.6: observational + strict equality (pure cong)
  | _, .oeqRefl witnessTerm => RawTerm.oeqRefl (RawTerm.cd witnessTerm)
  | _, .oeqJ baseCase witness =>
      RawTerm.oeqJ (RawTerm.cd baseCase) (RawTerm.cd witness)
  | _, .oeqFunext pointwiseEquality =>
      RawTerm.oeqFunext (RawTerm.cd pointwiseEquality)
  | _, .idStrictRefl witnessTerm => RawTerm.idStrictRefl (RawTerm.cd witnessTerm)
  | _, .idStrictRec baseCase witness =>
      RawTerm.cdIdStrictRecCase (RawTerm.cd baseCase) (RawTerm.cd witness)
  -- D1.6: type equivalence (pure cong)
  | _, .equivIntro forwardFn backwardFn =>
      RawTerm.equivIntro (RawTerm.cd forwardFn) (RawTerm.cd backwardFn)
  | _, .equivApp equivTerm argument =>
      RawTerm.equivApp (RawTerm.cd equivTerm) (RawTerm.cd argument)
  -- D1.6/D2.7: refinement, record, codata.  `refineElim` and
  -- `recordProj` carry raw β redexes; the rest are pure cong.
  | _, .refineIntro rawValue predicateProof =>
      RawTerm.refineIntro (RawTerm.cd rawValue) (RawTerm.cd predicateProof)
  | _, .refineElim refinedValue =>
      RawTerm.cdRefineElimCase (RawTerm.cd refinedValue)
  | _, .recordIntro firstField => RawTerm.recordIntro (RawTerm.cd firstField)
  | _, .recordProj recordValue =>
      RawTerm.cdRecordProjCase (RawTerm.cd recordValue)
  | _, .codataUnfold initialState transition =>
      RawTerm.codataUnfold (RawTerm.cd initialState) (RawTerm.cd transition)
  | _, .codataDest codataValue => RawTerm.cdCodataDestCase (RawTerm.cd codataValue)
  -- D1.6: sessions, effects (pure cong)
  | _, .sessionSend channel payload =>
      RawTerm.sessionSend (RawTerm.cd channel) (RawTerm.cd payload)
  | _, .sessionRecv channel => RawTerm.sessionRecv (RawTerm.cd channel)
  | _, .effectPerform operationTag arguments =>
      RawTerm.effectPerform (RawTerm.cd operationTag) (RawTerm.cd arguments)
  -- D1.6/A2: universeCode is atomic (no subterms to develop)
  | _, .universeCode innerLevel => RawTerm.universeCode innerLevel
  -- CUMUL-2.1 per-shape type codes (pure cong, no β rules — these
  -- are type-code values, recursing on subterms develops them under
  -- the binder where applicable).
  | _, .arrowCode domainCode codomainCode =>
      RawTerm.arrowCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .piTyCode domainCode codomainCode =>
      RawTerm.piTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .sigmaTyCode domainCode codomainCode =>
      RawTerm.sigmaTyCode (RawTerm.cd domainCode) (RawTerm.cd codomainCode)
  | _, .productCode firstCode secondCode =>
      RawTerm.productCode (RawTerm.cd firstCode) (RawTerm.cd secondCode)
  | _, .sumCode leftCode rightCode =>
      RawTerm.sumCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)
  | _, .listCode elementCode =>
      RawTerm.listCode (RawTerm.cd elementCode)
  | _, .optionCode elementCode =>
      RawTerm.optionCode (RawTerm.cd elementCode)
  | _, .eitherCode leftCode rightCode =>
      RawTerm.eitherCode (RawTerm.cd leftCode) (RawTerm.cd rightCode)
  | _, .idCode typeCode leftRaw rightRaw =>
      RawTerm.idCode (RawTerm.cd typeCode) (RawTerm.cd leftRaw) (RawTerm.cd rightRaw)
  | _, .equivCode leftTypeCode rightTypeCode =>
      RawTerm.equivCode (RawTerm.cd leftTypeCode) (RawTerm.cd rightTypeCode)
  -- CUMUL-2.6: cumulUpMarker recurses on inner code raw.
  | _, .cumulUpMarker innerCodeRaw =>
      RawTerm.cumulUpMarker (RawTerm.cd innerCodeRaw)
  -- D3.6-P1: uaToEquiv recurses on inner proof raw.
  | _, .uaToEquiv proofRaw =>
      RawTerm.uaToEquiv (RawTerm.cd proofRaw)
  -- D3.6-P2/S6: equivApply recurses on equiv and arg raws and
  -- dispatches through `cdEquivApplyCase` which fires the round-trip-β
  -- rule when the developed equiv is `uaToEquiv (oeqRefl _)`.
  -- Otherwise rebuilds plain `equivApply` cong.
  | _, .equivApply equivRaw argRaw =>
      RawTerm.cdEquivApplyCase (RawTerm.cd equivRaw) (RawTerm.cd argRaw)
  -- D3.6-S3: pathCompose recurses on left and right path raws.  Pure
  -- cong; the actual β rule fires through `cdTranspCase` when this
  -- pathCompose appears as the developed path of a transp.
  | _, .pathCompose leftPathRaw rightPathRaw =>
      RawTerm.pathCompose (RawTerm.cd leftPathRaw) (RawTerm.cd rightPathRaw)
  -- D3.6-S4: idToEquiv dispatches to `cdIdToEquivCase` so the
  -- identity-equivalence β rule fires when the developed proof is a
  -- syntactic refl.  D3.6-S5 extends `cdIdToEquivCase` with an
  -- oeqTrans arm that fires the compose-β rule.
  | _, .idToEquiv proofRaw =>
      RawTerm.cdIdToEquivCase (RawTerm.cd proofRaw)
  -- D3.6-S5: oeqTrans recurses on first and second proof raws.  Pure
  -- cong; the actual β rule fires through `cdIdToEquivCase` when this
  -- oeqTrans appears as the developed proof of an idToEquiv.
  | _, .oeqTrans firstProof secondProof =>
      RawTerm.oeqTrans (RawTerm.cd firstProof) (RawTerm.cd secondProof)
  -- D3.6-S5: equivCompose recurses on first and second equiv raws.
  -- Pure cong; this ctor is the contractum target of `idToEquivCompose`.
  | _, .equivCompose firstEquiv secondEquiv =>
      RawTerm.equivCompose (RawTerm.cd firstEquiv) (RawTerm.cd secondEquiv)

end LeanFX2
