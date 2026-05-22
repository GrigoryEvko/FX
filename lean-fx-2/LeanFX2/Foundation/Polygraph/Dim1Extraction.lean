import LeanFX2.Foundation.Polygraph.StepLabel
import LeanFX2.Foundation.Polygraph.ParallelPair

/-! # `Dim1Cell.toStepLabel?` — inverse extraction (K11.15)

K11.14 ships the forward map `StepLabel.toDim1Cell : StepLabel ->
PolyCell 1 0 0`.  This file ships the inverse: given an arbitrary
`PolyCell 1 0 0`, recover the `StepLabel` it encodes (if any).

The extraction is `Nat`-keyed dispatch over the `idx` field of the
cell's `PolyCell.arrow` constructor.  Returns `Option` because not
every `PolyCell 1 0 0` is in the image of `StepLabel.toDim1Cell` —
indices outside `[0, 109]` decode to `none`.

## Why `Option`?

The polygraph 1-cell type `PolyCell 1 0 0` carries an arbitrary
`Nat` index.  Only indices 0..109 correspond to FX `StepLabel`
generators; the rest are "foreign" cells from other polygraphs
(e.g. cells used by downstream consumers, K11.19 strategy cells,
or future kernel extensions adding new rewrite rules).
`fromIndex?` returns `none` on any out-of-range index — total
function with explicit `Option` boundary.

## Pairs with

* K11.16 — the per-ctor roundtrip theorem
  `Dim1Cell.toStepLabel? label.toDim1Cell = some label`,
  established as 110 `rfl` lemmas (one per `StepLabel` ctor).

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).

## Task anchor

K11.15 in the K-series build plan.  Direct downstream consumers:
K11.16 equivalence theorem, K11.19 strategy 3-cells reading
existing dim-1 cells back to typed rewrite-rule names.
-/

namespace LeanFX2.Foundation.Polygraph

/-- Decode a numeric index to a `StepLabel` if it falls in the
range 0..109.  Out-of-range indices yield `none`.  Total function
via explicit case-per-label + numeric wildcard default. -/
def StepLabel.fromIndex? : Nat → Option StepLabel
  | 0 => some StepLabel.appLeft
  | 1 => some StepLabel.appRight
  | 2 => some StepLabel.lamBody
  | 3 => some StepLabel.appPiLeft
  | 4 => some StepLabel.appPiRight
  | 5 => some StepLabel.lamPiBody
  | 6 => some StepLabel.pairRight
  | 7 => some StepLabel.fstCong
  | 8 => some StepLabel.sndCong
  | 9 => some StepLabel.betaApp
  | 10 => some StepLabel.betaAppPi
  | 11 => some StepLabel.betaFstPair
  | 12 => some StepLabel.betaSndPair
  | 13 => some StepLabel.boolElimScrutinee
  | 14 => some StepLabel.boolElimThen
  | 15 => some StepLabel.boolElimElse
  | 16 => some StepLabel.iotaBoolElimTrue
  | 17 => some StepLabel.iotaBoolElimFalse
  | 18 => some StepLabel.natSuccPred
  | 19 => some StepLabel.natElimScrutinee
  | 20 => some StepLabel.natElimZero
  | 21 => some StepLabel.natElimSucc
  | 22 => some StepLabel.iotaNatElimZero
  | 23 => some StepLabel.iotaNatElimSucc
  | 24 => some StepLabel.natRecScrutinee
  | 25 => some StepLabel.natRecZero
  | 26 => some StepLabel.natRecSucc
  | 27 => some StepLabel.iotaNatRecZero
  | 28 => some StepLabel.iotaNatRecSucc
  | 29 => some StepLabel.listConsHead
  | 30 => some StepLabel.listConsTail
  | 31 => some StepLabel.listElimScrutinee
  | 32 => some StepLabel.listElimNil
  | 33 => some StepLabel.listElimCons
  | 34 => some StepLabel.iotaListElimNil
  | 35 => some StepLabel.iotaListElimCons
  | 36 => some StepLabel.optionSomeValue
  | 37 => some StepLabel.optionMatchScrutinee
  | 38 => some StepLabel.optionMatchNone
  | 39 => some StepLabel.optionMatchSome
  | 40 => some StepLabel.iotaOptionMatchNone
  | 41 => some StepLabel.iotaOptionMatchSome
  | 42 => some StepLabel.eitherInlValue
  | 43 => some StepLabel.eitherInrValue
  | 44 => some StepLabel.eitherMatchScrutinee
  | 45 => some StepLabel.eitherMatchLeft
  | 46 => some StepLabel.eitherMatchRight
  | 47 => some StepLabel.iotaEitherMatchInl
  | 48 => some StepLabel.iotaEitherMatchInr
  | 49 => some StepLabel.idJBase
  | 50 => some StepLabel.idJWitness
  | 51 => some StepLabel.oeqJBase
  | 52 => some StepLabel.oeqJWitness
  | 53 => some StepLabel.oeqFunextPointwise
  | 54 => some StepLabel.idStrictRecBase
  | 55 => some StepLabel.idStrictRecWitness
  | 56 => some StepLabel.iotaIdJRefl
  | 57 => some StepLabel.iotaIdStrictRecRefl
  | 58 => some StepLabel.modIntroInner
  | 59 => some StepLabel.modElimInner
  | 60 => some StepLabel.betaModElimIntro
  | 61 => some StepLabel.subsumeInner
  | 62 => some StepLabel.pathLamBody
  | 63 => some StepLabel.pathAppPath
  | 64 => some StepLabel.pathAppInterval
  | 65 => some StepLabel.betaPathApp
  | 66 => some StepLabel.betaPathReflApp
  | 67 => some StepLabel.glueIntroBase
  | 68 => some StepLabel.glueIntroPartial
  | 69 => some StepLabel.glueElimValue
  | 70 => some StepLabel.betaGlueElimIntro
  | 71 => some StepLabel.intervalOppInner
  | 72 => some StepLabel.intervalMeetLeft
  | 73 => some StepLabel.intervalMeetRight
  | 74 => some StepLabel.intervalJoinLeft
  | 75 => some StepLabel.intervalJoinRight
  | 76 => some StepLabel.recordIntroField
  | 77 => some StepLabel.recordProjRecord
  | 78 => some StepLabel.betaRecordProjIntro
  | 79 => some StepLabel.refineIntroValue
  | 80 => some StepLabel.refineIntroProof
  | 81 => some StepLabel.refineElimValue
  | 82 => some StepLabel.betaRefineElimIntro
  | 83 => some StepLabel.codataUnfoldState
  | 84 => some StepLabel.codataUnfoldTransition
  | 85 => some StepLabel.codataDestValue
  | 86 => some StepLabel.betaCodataDestUnfold
  | 87 => some StepLabel.sessionSendChannel
  | 88 => some StepLabel.sessionSendPayload
  | 89 => some StepLabel.sessionRecvChannel
  | 90 => some StepLabel.effectPerformOperation
  | 91 => some StepLabel.effectPerformArguments
  | 92 => some StepLabel.transpPath
  | 93 => some StepLabel.transpSource
  | 94 => some StepLabel.transpReflBeta
  | 95 => some StepLabel.hcompSides
  | 96 => some StepLabel.hcompCap
  | 97 => some StepLabel.equivIntroHetForward
  | 98 => some StepLabel.equivIntroHetBackward
  | 99 => some StepLabel.equivAppEquiv
  | 100 => some StepLabel.equivAppArgument
  | 101 => some StepLabel.uaIntroHetWitness
  | 102 => some StepLabel.uaToEquivProof
  | 103 => some StepLabel.equivApplyEquiv
  | 104 => some StepLabel.equivApplyArgument
  | 105 => some StepLabel.cumulUpInner
  | 106 => some StepLabel.eqType
  | 107 => some StepLabel.eqArrow
  | 108 => some StepLabel.eqTypeHet
  | 109 => some StepLabel.eqArrowHet
  | 110 => some StepLabel.betaFunextReflApp
  | 111 => some StepLabel.transpReflBetaDeep
  | _ => none

/-- Extract the `StepLabel` encoded in a dim-1 polygraph cell at
the trivial boundary `(0, 0)`.  Returns `none` on cells whose `idx`
field falls outside the FX `Step` ctor range. -/
def Dim1Cell.toStepLabel? (cell : PolyCell 1 0 0) : Option StepLabel :=
  StepLabel.fromIndex? (cellIdx cell)

end LeanFX2.Foundation.Polygraph
