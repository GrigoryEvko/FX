import LeanFX2.Foundation.Polygraph.PolyCell

/-! # `StepLabel` — Burroni 1-polygraph generator labels for `Step`

A `StepLabel` is the Type-valued name of a rewrite-rule generator in
FX's reduction system.  Each constructor of `Step` (the Prop-valued
typed reduction relation in `Reduction/Step.lean`) corresponds to one
`StepLabel` ctor of the same name; the two layers are kept separate
on purpose so the labels live in `Type` (eligible for use as
`PolyCell` payload) while the typed witnesses stay in `Prop` (where
proof irrelevance + the rest of the reduction / confluence / SR
infrastructure already lives).

## Burroni-style layered presentation

Burroni 1993 §1.1 distinguishes:

* `X_1` — the *set* of dim-1 polygraph generators (Type, finitely
  many for FX: 110 generators, one per rewrite rule).
* The free 1-category over `X_1` — sequences of generators applied
  to terms, modelled here by the existing `Step.parStar` /
  `StepStar` machinery.
* Typed rewrite witnesses — `Step lhs rhs : Prop`.  Each typed
  witness internally names a generator (its ctor identifier IS a
  `StepLabel`) but does NOT carry it as data; the proof-irrelevance
  of `Prop` makes that link extra-syntactic.

K11.14 ships `X_1` and the `toDim1Cell` map.  K11.15 ships the
inverse extraction (Dim1Cell index back to `StepLabel`).  K11.16
ships the per-ctor `rfl`-equivalence theorems that make the
correspondence precise.

## Why not `Step.toDim1Cell : Step lhs rhs → PolyCell 1 0 0`?

Because `Step` lives in `Prop` and `PolyCell` lives in `Type`, and
Lean 4 forbids `Prop → Type` elimination outside of subsingletons.
The `StepLabel` indirection ships the same information at the
correct universe.

## Single-sorted polygraph: every generator emanates from vertex 0

FX's reduction relation is monomorphic at the polygraph-1-cell layer
— a single trivial dim-0 atom (`PolyCell.atom 0`) suffices as both
source and target of every generator.  The distinguishing data is
carried by the `idx : Nat` field of `PolyCell.arrow`, which equals
`StepLabel.index label`.

The downstream consumers (K11.15 / K11.16 / K11.17 / K11.19) only
need to recover `(label, source, target)` from a polygraph cell;
since `source = target = atom 0` is constant, that reduces to
recovering `label` from the `idx`, which is a partial function
(`Nat → Option StepLabel`) decoded by the K11.15 ticket.

## Index discipline

`StepLabel.index` assigns the canonical integer 0..109 to each label,
in the exact source-order of `Reduction/Step.lean`'s 110-ctor `Step`
inductive.  This makes the K11.16 equivalence theorem mechanical
(per-ctor `rfl`) and the K11.15 inverse a single `Nat`-keyed lookup.

## Root status

`FX-rich` (Layer P substrate underneath Foundation Layer 0).

## Task anchor

K11.14 in the K-series build plan.  Pairs with K11.15
`Dim1Cell.toStep` (inverse extraction), K11.16 `Step ⇌ Dim1Cell`
equivalence, K11.17 `cd_lemma.toDim2Cell` 2-cell embedding.
-/

namespace LeanFX2.Foundation.Polygraph

/-- One `StepLabel` constructor per `LeanFX2.Step.par` constructor.
Ctor names match `Step` ctor names character-for-character (source
order from `LeanFX2/Reduction/Step.lean`'s inductive declaration).
-/
inductive StepLabel : Type
  | appLeft
  | appRight
  | lamBody
  | appPiLeft
  | appPiRight
  | lamPiBody
  | pairRight
  | fstCong
  | sndCong
  | betaApp
  | betaAppPi
  | betaFstPair
  | betaSndPair
  | boolElimScrutinee
  | boolElimThen
  | boolElimElse
  | iotaBoolElimTrue
  | iotaBoolElimFalse
  | natSuccPred
  | natElimScrutinee
  | natElimZero
  | natElimSucc
  | iotaNatElimZero
  | iotaNatElimSucc
  | natRecScrutinee
  | natRecZero
  | natRecSucc
  | iotaNatRecZero
  | iotaNatRecSucc
  | listConsHead
  | listConsTail
  | listElimScrutinee
  | listElimNil
  | listElimCons
  | iotaListElimNil
  | iotaListElimCons
  | optionSomeValue
  | optionMatchScrutinee
  | optionMatchNone
  | optionMatchSome
  | iotaOptionMatchNone
  | iotaOptionMatchSome
  | eitherInlValue
  | eitherInrValue
  | eitherMatchScrutinee
  | eitherMatchLeft
  | eitherMatchRight
  | iotaEitherMatchInl
  | iotaEitherMatchInr
  | idJBase
  | idJWitness
  | oeqJBase
  | oeqJWitness
  | oeqFunextPointwise
  | idStrictRecBase
  | idStrictRecWitness
  | iotaIdJRefl
  | iotaIdStrictRecRefl
  | modIntroInner
  | modElimInner
  | betaModElimIntro
  | subsumeInner
  | pathLamBody
  | pathAppPath
  | pathAppInterval
  | betaPathApp
  | betaPathReflApp
  | betaFunextReflApp
  | glueIntroBase
  | glueIntroPartial
  | glueElimValue
  | betaGlueElimIntro
  | intervalOppInner
  | intervalMeetLeft
  | intervalMeetRight
  | intervalJoinLeft
  | intervalJoinRight
  | recordIntroField
  | recordProjRecord
  | betaRecordProjIntro
  | refineIntroValue
  | refineIntroProof
  | refineElimValue
  | betaRefineElimIntro
  | codataUnfoldState
  | codataUnfoldTransition
  | codataDestValue
  | betaCodataDestUnfold
  | sessionSendChannel
  | sessionSendPayload
  | sessionRecvChannel
  | effectPerformOperation
  | effectPerformArguments
  | transpPath
  | transpSource
  | transpReflBeta
  | hcompSides
  | hcompCap
  | equivIntroHetForward
  | equivIntroHetBackward
  | equivAppEquiv
  | equivAppArgument
  | uaIntroHetWitness
  | uaToEquivProof
  | equivApplyEquiv
  | equivApplyArgument
  | cumulUpInner
  | eqType
  | eqArrow
  | eqTypeHet
  | eqArrowHet
  | transpReflBetaDeep
  deriving Repr

/-- The canonical 0..109 index of a `StepLabel`, in source order of
`Reduction/Step.lean`'s `Step` inductive.  Total function via full
enumeration (no wildcards — propext-clean per the
`feedback_lean_match_propext_recipe.md` recipe). -/
def StepLabel.index : StepLabel → Nat
  | appLeft => 0
  | appRight => 1
  | lamBody => 2
  | appPiLeft => 3
  | appPiRight => 4
  | lamPiBody => 5
  | pairRight => 6
  | fstCong => 7
  | sndCong => 8
  | betaApp => 9
  | betaAppPi => 10
  | betaFstPair => 11
  | betaSndPair => 12
  | boolElimScrutinee => 13
  | boolElimThen => 14
  | boolElimElse => 15
  | iotaBoolElimTrue => 16
  | iotaBoolElimFalse => 17
  | natSuccPred => 18
  | natElimScrutinee => 19
  | natElimZero => 20
  | natElimSucc => 21
  | iotaNatElimZero => 22
  | iotaNatElimSucc => 23
  | natRecScrutinee => 24
  | natRecZero => 25
  | natRecSucc => 26
  | iotaNatRecZero => 27
  | iotaNatRecSucc => 28
  | listConsHead => 29
  | listConsTail => 30
  | listElimScrutinee => 31
  | listElimNil => 32
  | listElimCons => 33
  | iotaListElimNil => 34
  | iotaListElimCons => 35
  | optionSomeValue => 36
  | optionMatchScrutinee => 37
  | optionMatchNone => 38
  | optionMatchSome => 39
  | iotaOptionMatchNone => 40
  | iotaOptionMatchSome => 41
  | eitherInlValue => 42
  | eitherInrValue => 43
  | eitherMatchScrutinee => 44
  | eitherMatchLeft => 45
  | eitherMatchRight => 46
  | iotaEitherMatchInl => 47
  | iotaEitherMatchInr => 48
  | idJBase => 49
  | idJWitness => 50
  | oeqJBase => 51
  | oeqJWitness => 52
  | oeqFunextPointwise => 53
  | idStrictRecBase => 54
  | idStrictRecWitness => 55
  | iotaIdJRefl => 56
  | iotaIdStrictRecRefl => 57
  | modIntroInner => 58
  | modElimInner => 59
  | betaModElimIntro => 60
  | subsumeInner => 61
  | pathLamBody => 62
  | pathAppPath => 63
  | pathAppInterval => 64
  | betaPathApp => 65
  | betaPathReflApp => 66
  | glueIntroBase => 67
  | glueIntroPartial => 68
  | glueElimValue => 69
  | betaGlueElimIntro => 70
  | intervalOppInner => 71
  | intervalMeetLeft => 72
  | intervalMeetRight => 73
  | intervalJoinLeft => 74
  | intervalJoinRight => 75
  | recordIntroField => 76
  | recordProjRecord => 77
  | betaRecordProjIntro => 78
  | refineIntroValue => 79
  | refineIntroProof => 80
  | refineElimValue => 81
  | betaRefineElimIntro => 82
  | codataUnfoldState => 83
  | codataUnfoldTransition => 84
  | codataDestValue => 85
  | betaCodataDestUnfold => 86
  | sessionSendChannel => 87
  | sessionSendPayload => 88
  | sessionRecvChannel => 89
  | effectPerformOperation => 90
  | effectPerformArguments => 91
  | transpPath => 92
  | transpSource => 93
  | transpReflBeta => 94
  | hcompSides => 95
  | hcompCap => 96
  | equivIntroHetForward => 97
  | equivIntroHetBackward => 98
  | equivAppEquiv => 99
  | equivAppArgument => 100
  | uaIntroHetWitness => 101
  | uaToEquivProof => 102
  | equivApplyEquiv => 103
  | equivApplyArgument => 104
  | cumulUpInner => 105
  | eqType => 106
  | eqArrow => 107
  | eqTypeHet => 108
  | eqArrowHet => 109
  | betaFunextReflApp => 110
  | transpReflBetaDeep => 111

/-- The dim-1 polygraph cell witnessed by this rewrite-rule label.
Every label maps to `PolyCell.arrow (.atom 0) (.atom 0) (label.index)`
— single-sorted polygraph reading, where the only distinguishing data
across labels is the numeric index. -/
def StepLabel.toDim1Cell (label : StepLabel) : PolyCell 1 0 0 :=
  PolyCell.arrow (.atom 0) (.atom 0) label.index

end LeanFX2.Foundation.Polygraph
