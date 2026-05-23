import LeanFX2.Foundation.Polygraph.RawPolyTermFlat
import LeanFX2.Foundation.Polygraph.RawPolyTerm

/-! # `RawPolyTermFlat.toLegacy` — forward bijection to the 74-ctor mirror.

This file ships the forward direction of the polygraph-substrate
bijection: a 74-arm structural-recursive function mapping the
honest nested inductive `RawPolyTermFlat` to the legacy 74-ctor
mirror `RawPolyTerm`.

## Why a separate file

The bijection lives in its own file (rather than alongside the
substrate inductive in `RawPolyTermFlat.lean`) so the substrate file
remains a pure data declaration — anything wanting just the
substrate can import `RawPolyTermFlat` without dragging in the
legacy mirror.

## Bijection forward direction

For each `Generator` summand `gen_X`, we pattern-match on the
substrate's `mk` constructor together with its `children` list
shape (which is fully determined by `gen_X.binderShifts`) and
produce the corresponding `RawPolyTerm.X ...` term, recursing on
every child via `.toLegacy`.

The function is structurally recursive on `RawPolyTermFlat`: each
recursive call lands on a `head` field of a `RawPolyTermFlatChildren.cons`,
which is a strict subterm of the input `.mk` (head is a field of
cons, cons is a field of mk's children).

## The match shape per arity

* **Nullary** (var, unit, boolTrue/False, natZero, listNil,
  optionNone, interval0/1, universeCode):
  `.mk .gen_X payload .nil => .X payload`
  (payload is `Fin scope` for var, `Nat` for universeCode, `()`
  for the rest).
* **Unary** (lam, fst, snd, natSucc, optionSome, eitherInl/Inr,
  refl, modIntro/Elim/subsume, intervalOpp, glueElim, oeqRefl,
  oeqFunext, idStrictRefl, refineElim, recordIntro/Proj,
  codataDest, sessionRecv, listCode, optionCode, cumulUpMarker,
  uaToEquiv, idToEquiv):
  `.mk .gen_X () (.cons child .nil) => .X child.toLegacy`
* **Binary same-scope** (app, pair, listCons, idJ, intervalMeet/Join,
  pathApp, glueIntro, transp, hcomp, oeqJ, idStrictRec,
  equivIntro, equivApp, refineIntro, codataUnfold, sessionSend,
  effectPerform, arrowCode, productCode, sumCode, eitherCode,
  equivCode, equivApply, pathCompose, oeqTrans, equivCompose):
  `.mk .gen_X () (.cons a (.cons b .nil)) => .X a.toLegacy b.toLegacy`
* **Binary with binder** (piTyCode, sigmaTyCode):
  same as binary same-scope, but the second child lives at
  `scope + 1`; the substrate's binderShifts table already pins this.
* **Unary under binder** (lam, pathLam):
  `.mk .gen_X () (.cons body .nil) => .X body.toLegacy`
  where `body : RawPolyTermFlat (scope + 1)`; the substrate again
  pins the index.
* **Ternary** (boolElim, natElim, natRec, listElim, optionMatch,
  eitherMatch, idCode, transpFill):
  `.mk .gen_X () (.cons a (.cons b (.cons c .nil))) =>
    .X a.toLegacy b.toLegacy c.toLegacy`

## Zero-axiom discipline

Every arm enumerates the full match shape explicitly — no
wildcards.  Per the same propext-trap that bit `Generator.payload`
in the substrate ship, wildcards over the 74-ctor `Generator` cause
the match compiler to emit propext-using equation lemmas; full
enumeration keeps Lean in the closed-enum dispatch regime where
every arm is a concrete pattern.  The 74-line repetition is the
explicit price of zero-axiom hygiene. -/

namespace LeanFX2.Foundation.Polygraph

/-- Forward direction of the polygraph-substrate bijection.

Maps the honest nested `RawPolyTermFlat` to the legacy 74-ctor mirror
`RawPolyTerm` by pattern-matching the `Generator` tag and consuming
the children list per the per-generator shape. -/
def RawPolyTermFlat.toLegacy : {scope : Nat} → RawPolyTermFlat scope → RawPolyTerm scope
  -- Variable + unit
  | _, .mk .gen_var position .nil =>
      .var position
  | _, .mk .gen_unit () .nil =>
      .unit
  -- Function intro/elim
  | _, .mk .gen_lam () (.cons body .nil) =>
      .lam body.toLegacy
  | _, .mk .gen_app () (.cons fn (.cons arg .nil)) =>
      .app fn.toLegacy arg.toLegacy
  -- Pair intro/elim
  | _, .mk .gen_pair () (.cons first (.cons second .nil)) =>
      .pair first.toLegacy second.toLegacy
  | _, .mk .gen_fst () (.cons pair .nil) =>
      .fst pair.toLegacy
  | _, .mk .gen_snd () (.cons pair .nil) =>
      .snd pair.toLegacy
  -- Booleans
  | _, .mk .gen_boolTrue () .nil =>
      .boolTrue
  | _, .mk .gen_boolFalse () .nil =>
      .boolFalse
  | _, .mk .gen_boolElim () (.cons scrut (.cons thenBr (.cons elseBr .nil))) =>
      .boolElim scrut.toLegacy thenBr.toLegacy elseBr.toLegacy
  -- Naturals
  | _, .mk .gen_natZero () .nil =>
      .natZero
  | _, .mk .gen_natSucc () (.cons pred .nil) =>
      .natSucc pred.toLegacy
  | _, .mk .gen_natElim () (.cons scrut (.cons zeroBr (.cons succBr .nil))) =>
      .natElim scrut.toLegacy zeroBr.toLegacy succBr.toLegacy
  | _, .mk .gen_natRec () (.cons scrut (.cons zeroBr (.cons succBr .nil))) =>
      .natRec scrut.toLegacy zeroBr.toLegacy succBr.toLegacy
  -- Lists
  | _, .mk .gen_listNil () .nil =>
      .listNil
  | _, .mk .gen_listCons () (.cons headChild (.cons tailChild .nil)) =>
      .listCons headChild.toLegacy tailChild.toLegacy
  | _, .mk .gen_listElim () (.cons scrut (.cons nilBr (.cons consBr .nil))) =>
      .listElim scrut.toLegacy nilBr.toLegacy consBr.toLegacy
  -- Options
  | _, .mk .gen_optionNone () .nil =>
      .optionNone
  | _, .mk .gen_optionSome () (.cons val .nil) =>
      .optionSome val.toLegacy
  | _, .mk .gen_optionMatch () (.cons scrut (.cons noneBr (.cons someBr .nil))) =>
      .optionMatch scrut.toLegacy noneBr.toLegacy someBr.toLegacy
  -- Eithers
  | _, .mk .gen_eitherInl () (.cons val .nil) =>
      .eitherInl val.toLegacy
  | _, .mk .gen_eitherInr () (.cons val .nil) =>
      .eitherInr val.toLegacy
  | _, .mk .gen_eitherMatch () (.cons scrut (.cons leftBr (.cons rightBr .nil))) =>
      .eitherMatch scrut.toLegacy leftBr.toLegacy rightBr.toLegacy
  -- Identity types
  | _, .mk .gen_refl () (.cons witness .nil) =>
      .refl witness.toLegacy
  | _, .mk .gen_idJ () (.cons baseCase (.cons witness .nil)) =>
      .idJ baseCase.toLegacy witness.toLegacy
  -- Modal
  | _, .mk .gen_modIntro () (.cons inner .nil) =>
      .modIntro inner.toLegacy
  | _, .mk .gen_modElim () (.cons inner .nil) =>
      .modElim inner.toLegacy
  | _, .mk .gen_subsume () (.cons inner .nil) =>
      .subsume inner.toLegacy
  -- Cubical interval
  | _, .mk .gen_interval0 () .nil =>
      .interval0
  | _, .mk .gen_interval1 () .nil =>
      .interval1
  | _, .mk .gen_intervalOpp () (.cons inner .nil) =>
      .intervalOpp inner.toLegacy
  | _, .mk .gen_intervalMeet () (.cons left (.cons right .nil)) =>
      .intervalMeet left.toLegacy right.toLegacy
  | _, .mk .gen_intervalJoin () (.cons left (.cons right .nil)) =>
      .intervalJoin left.toLegacy right.toLegacy
  -- Cubical path
  | _, .mk .gen_pathLam () (.cons body .nil) =>
      .pathLam body.toLegacy
  | _, .mk .gen_pathApp () (.cons pathTerm (.cons intervalArg .nil)) =>
      .pathApp pathTerm.toLegacy intervalArg.toLegacy
  -- Cubical glue / transport / composition
  | _, .mk .gen_glueIntro () (.cons baseVal (.cons partialVal .nil)) =>
      .glueIntro baseVal.toLegacy partialVal.toLegacy
  | _, .mk .gen_glueElim () (.cons glued .nil) =>
      .glueElim glued.toLegacy
  | _, .mk .gen_transp () (.cons pathTerm (.cons source .nil)) =>
      .transp pathTerm.toLegacy source.toLegacy
  | _, .mk .gen_hcomp () (.cons sides (.cons cap .nil)) =>
      .hcomp sides.toLegacy cap.toLegacy
  -- Observational equality
  | _, .mk .gen_oeqRefl () (.cons witness .nil) =>
      .oeqRefl witness.toLegacy
  | _, .mk .gen_oeqJ () (.cons baseCase (.cons witness .nil)) =>
      .oeqJ baseCase.toLegacy witness.toLegacy
  | _, .mk .gen_oeqFunext () (.cons pointwise .nil) =>
      .oeqFunext pointwise.toLegacy
  -- Strict identity
  | _, .mk .gen_idStrictRefl () (.cons witness .nil) =>
      .idStrictRefl witness.toLegacy
  | _, .mk .gen_idStrictRec () (.cons baseCase (.cons witness .nil)) =>
      .idStrictRec baseCase.toLegacy witness.toLegacy
  -- Type equivalence
  | _, .mk .gen_equivIntro () (.cons fwdFn (.cons bwdFn .nil)) =>
      .equivIntro fwdFn.toLegacy bwdFn.toLegacy
  | _, .mk .gen_equivApp () (.cons equiv (.cons arg .nil)) =>
      .equivApp equiv.toLegacy arg.toLegacy
  -- Refinement
  | _, .mk .gen_refineIntro () (.cons val (.cons predProof .nil)) =>
      .refineIntro val.toLegacy predProof.toLegacy
  | _, .mk .gen_refineElim () (.cons refined .nil) =>
      .refineElim refined.toLegacy
  -- Record
  | _, .mk .gen_recordIntro () (.cons field .nil) =>
      .recordIntro field.toLegacy
  | _, .mk .gen_recordProj () (.cons recordVal .nil) =>
      .recordProj recordVal.toLegacy
  -- Codata
  | _, .mk .gen_codataUnfold () (.cons initState (.cons transition .nil)) =>
      .codataUnfold initState.toLegacy transition.toLegacy
  | _, .mk .gen_codataDest () (.cons codataVal .nil) =>
      .codataDest codataVal.toLegacy
  -- Sessions
  | _, .mk .gen_sessionSend () (.cons channel (.cons payload .nil)) =>
      .sessionSend channel.toLegacy payload.toLegacy
  | _, .mk .gen_sessionRecv () (.cons channel .nil) =>
      .sessionRecv channel.toLegacy
  -- Effects
  | _, .mk .gen_effectPerform () (.cons opTag (.cons args .nil)) =>
      .effectPerform opTag.toLegacy args.toLegacy
  -- Universe code (carries inner level Nat)
  | _, .mk .gen_universeCode innerLevel .nil =>
      .universeCode innerLevel
  -- Per-shape type codes (atom-shape)
  | _, .mk .gen_arrowCode () (.cons domain (.cons codomain .nil)) =>
      .arrowCode domain.toLegacy codomain.toLegacy
  -- Per-shape type codes (binder-shape) — codomain at scope+1
  | _, .mk .gen_piTyCode () (.cons domain (.cons codomain .nil)) =>
      .piTyCode domain.toLegacy codomain.toLegacy
  | _, .mk .gen_sigmaTyCode () (.cons domain (.cons codomain .nil)) =>
      .sigmaTyCode domain.toLegacy codomain.toLegacy
  -- More atom-shape codes
  | _, .mk .gen_productCode () (.cons first (.cons second .nil)) =>
      .productCode first.toLegacy second.toLegacy
  | _, .mk .gen_sumCode () (.cons left (.cons right .nil)) =>
      .sumCode left.toLegacy right.toLegacy
  | _, .mk .gen_listCode () (.cons element .nil) =>
      .listCode element.toLegacy
  | _, .mk .gen_optionCode () (.cons element .nil) =>
      .optionCode element.toLegacy
  | _, .mk .gen_eitherCode () (.cons left (.cons right .nil)) =>
      .eitherCode left.toLegacy right.toLegacy
  | _, .mk .gen_idCode () (.cons typeCode (.cons leftRaw (.cons rightRaw .nil))) =>
      .idCode typeCode.toLegacy leftRaw.toLegacy rightRaw.toLegacy
  | _, .mk .gen_equivCode () (.cons leftCode (.cons rightCode .nil)) =>
      .equivCode leftCode.toLegacy rightCode.toLegacy
  -- Cumulativity marker
  | _, .mk .gen_cumulUpMarker () (.cons innerCode .nil) =>
      .cumulUpMarker innerCode.toLegacy
  -- Univalence-to-equiv vocabulary
  | _, .mk .gen_uaToEquiv () (.cons proof .nil) =>
      .uaToEquiv proof.toLegacy
  | _, .mk .gen_equivApply () (.cons equiv (.cons arg .nil)) =>
      .equivApply equiv.toLegacy arg.toLegacy
  -- Composition vocabulary
  | _, .mk .gen_pathCompose () (.cons leftPath (.cons rightPath .nil)) =>
      .pathCompose leftPath.toLegacy rightPath.toLegacy
  | _, .mk .gen_idToEquiv () (.cons proof .nil) =>
      .idToEquiv proof.toLegacy
  | _, .mk .gen_oeqTrans () (.cons firstProof (.cons secondProof .nil)) =>
      .oeqTrans firstProof.toLegacy secondProof.toLegacy
  | _, .mk .gen_equivCompose () (.cons firstEquiv (.cons secondEquiv .nil)) =>
      .equivCompose firstEquiv.toLegacy secondEquiv.toLegacy
  -- Cubical fill operation
  | _, .mk .gen_transpFill () (.cons pathTy (.cons currentInterval (.cons source .nil))) =>
      .transpFill pathTy.toLegacy currentInterval.toLegacy source.toLegacy

end LeanFX2.Foundation.Polygraph
