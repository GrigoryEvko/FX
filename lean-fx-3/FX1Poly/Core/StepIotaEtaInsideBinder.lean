import FX1Poly.Core.StepEtaCriticalPairs
import FX1Poly.Core.StepRename

/-! # Foundation/PolyCell/Core/StepIotaEtaInsideBinder

Explicit coverage ratchet for the current iota-vs-eta-lambda
inside-binder critical-pair surface.

The proof-relevant diamond is generic:
`BetaEtaPairJoin.etaLamArbitraryUnderBinderCong` joins any beta+iota
`Step` that fires in the weakened function position of an eta-lambda
source.  This file records the finite iota side of that statement as
auditable data — a concrete 16-row guard instead of an implicit appeal
to the generic theorem.
-/

namespace FX1Poly.Core

-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation

/-- Current iota root rules, excluding beta from `RootStepKind`.

This is intentionally a separate finite catalog rather than a predicate
over `RootStepKind`: the coverage gate below should fail loudly when the
root-step table is extended without the iota/eta-lambda audit being
extended with it. -/
inductive IotaRootKind : Type where
  | boolTrue
  | boolFalse
  | fstPair
  | sndPair
  | natElimZero
  | natRecZero
  | listElimNil
  | optionMatchNone
  | optionMatchSome
  | eitherMatchInl
  | eitherMatchInr
  | natElimSucc
  | natRecSucc
  | listElimCons
  | idJRefl
  | idStrictRecRefl
  deriving DecidableEq

namespace IotaRootKind

/-- Complete current iota-root catalog. -/
def all : List IotaRootKind :=
  [ .boolTrue
  , .boolFalse
  , .fstPair
  , .sndPair
  , .natElimZero
  , .natRecZero
  , .listElimNil
  , .optionMatchNone
  , .optionMatchSome
  , .eitherMatchInl
  , .eitherMatchInr
  , .natElimSucc
  , .natRecSucc
  , .listElimCons
  , .idJRefl
  , .idStrictRecRefl
  ]

/-- Embed the iota-only catalog into the existing root-step catalog. -/
def toRootStepKind : IotaRootKind → RootStepKind
  | .boolTrue => .iotaBoolTrue
  | .boolFalse => .iotaBoolFalse
  | .fstPair => .iotaFstPair
  | .sndPair => .iotaSndPair
  | .natElimZero => .iotaNatElimZero
  | .natRecZero => .iotaNatRecZero
  | .listElimNil => .iotaListElimNil
  | .optionMatchNone => .iotaOptionMatchNone
  | .optionMatchSome => .iotaOptionMatchSome
  | .eitherMatchInl => .iotaEitherMatchInl
  | .eitherMatchInr => .iotaEitherMatchInr
  | .natElimSucc => .iotaNatElimSucc
  | .natRecSucc => .iotaNatRecSucc
  | .listElimCons => .iotaListElimCons
  | .idJRefl => .iotaIdJRefl
  | .idStrictRecRefl => .iotaIdStrictRecRefl

/-- Source-head generator for an iota root rule. -/
def sourceGenerator (iotaKind : IotaRootKind) : Generator :=
  RootStepKind.sourceGenerator iotaKind.toRootStepKind

theorem all_length :
    all.length = 16 := rfl

/-- The iota catalog is exactly the current root-step catalog after
dropping beta. -/
theorem all_maps_to_root_iotas :
    all.map toRootStepKind = RootStepKind.all.drop 1 := rfl

theorem all_sourceGenerators :
    all.map sourceGenerator =
      [ .gen_boolElim
      , .gen_boolElim
      , .gen_fst
      , .gen_snd
      , .gen_natElim
      , .gen_natRec
      , .gen_listElim
      , .gen_optionMatch
      , .gen_optionMatch
      , .gen_eitherMatch
      , .gen_eitherMatch
      , .gen_natElim
      , .gen_natRec
      , .gen_listElim
      , .gen_idJ
      , .gen_idStrictRec
      ] := rfl

end IotaRootKind

/-- Coverage state for one current iota root against eta-lambda.

There is only one live status in this task: each row is covered by the
generic inside-binder diamond.  Reserved and disjoint states belong to the
full matrix task, not to this 16-row eta-lambda slice. -/
inductive IotaEtaInsideBinderStatus : Type where
  | insideBinderDiamond
  deriving DecidableEq

namespace IotaEtaInsideBinderStatus

/-- Boolean view used by the audit gate. -/
def isCovered : IotaEtaInsideBinderStatus → Bool
  | .insideBinderDiamond => true

theorem insideBinderDiamond_isCovered :
    isCovered .insideBinderDiamond = true := rfl

end IotaEtaInsideBinderStatus

/-- One audited row in the current iota x eta-lambda coverage table. -/
structure IotaEtaInsideBinderCoverage where
  iotaKind : IotaRootKind
  etaKind : EtaStepKind
  status : IotaEtaInsideBinderStatus
  deriving DecidableEq

namespace IotaEtaInsideBinderCoverage

/-- The current eta-lambda row for one iota root kind. -/
def rowForIotaKind (iotaKind : IotaRootKind) :
    IotaEtaInsideBinderCoverage where
  iotaKind := iotaKind
  etaKind := .etaLam
  status := .insideBinderDiamond

/-- A row is complete exactly when it is an eta-lambda row with a covered
status. -/
def isComplete (coverageRow : IotaEtaInsideBinderCoverage) : Bool :=
  if coverageRow.etaKind = .etaLam then
    coverageRow.status.isCovered
  else
    false

theorem rowForIotaKind_isComplete (iotaKind : IotaRootKind) :
    isComplete (rowForIotaKind iotaKind) = true := by
  rfl

end IotaEtaInsideBinderCoverage

namespace IotaRootKind

/-- The 16-row current iota x eta-lambda coverage table. -/
def etaLamCoverageRows : List IotaEtaInsideBinderCoverage :=
  all.map IotaEtaInsideBinderCoverage.rowForIotaKind

/-- Build-time coverage bit: every eta-lambda inside-binder row is complete. -/
def etaLamCoverageComplete : Bool :=
  etaLamCoverageRows.all IotaEtaInsideBinderCoverage.isComplete

theorem etaLamCoverageRows_length :
    etaLamCoverageRows.length = 16 := rfl

theorem etaLamCoverageComplete_eq_true :
    etaLamCoverageComplete = true := rfl

theorem boolTrue_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .boolTrue).status =
      .insideBinderDiamond := rfl

theorem boolFalse_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .boolFalse).status =
      .insideBinderDiamond := rfl

theorem fstPair_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .fstPair).status =
      .insideBinderDiamond := rfl

theorem sndPair_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .sndPair).status =
      .insideBinderDiamond := rfl

theorem natElimZero_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .natElimZero).status =
      .insideBinderDiamond := rfl

theorem natRecZero_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .natRecZero).status =
      .insideBinderDiamond := rfl

theorem listElimNil_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .listElimNil).status =
      .insideBinderDiamond := rfl

theorem optionMatchNone_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .optionMatchNone).status =
      .insideBinderDiamond := rfl

theorem optionMatchSome_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .optionMatchSome).status =
      .insideBinderDiamond := rfl

theorem eitherMatchInl_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .eitherMatchInl).status =
      .insideBinderDiamond := rfl

theorem eitherMatchInr_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .eitherMatchInr).status =
      .insideBinderDiamond := rfl

theorem natElimSucc_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .natElimSucc).status =
      .insideBinderDiamond := rfl

theorem natRecSucc_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .natRecSucc).status =
      .insideBinderDiamond := rfl

theorem listElimCons_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .listElimCons).status =
      .insideBinderDiamond := rfl

theorem idJRefl_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .idJRefl).status =
      .insideBinderDiamond := rfl

theorem idStrictRecRefl_etaLam_status :
    (IotaEtaInsideBinderCoverage.rowForIotaKind .idStrictRecRefl).status =
      .insideBinderDiamond := rfl

end IotaRootKind

namespace Step

/-- Weakening is a special case of the beta+iota rename closure.

This is the proof-relevant commute lemma consumed by the inside-binder
eta-lambda diamond; it is intentionally stated for any `Step`, so the 16
iota rows above do not need brittle constructor-by-constructor copies. -/
theorem iotaEta_weakened_step {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (sourceStep : Step sourceTerm targetTerm) :
    Step (RawTerm.weaken sourceTerm) (RawTerm.weaken targetTerm) := by
  rw [RawTerm.weaken_eq_rename sourceTerm]
  rw [RawTerm.weaken_eq_rename targetTerm]
  exact Step.rename RawRenaming.weaken sourceStep

/-- The explicit inside-binder iota/eta-lambda diamond wrapper.

The left branch fires a beta+iota step inside the weakened function
position of the eta-lambda body; the right branch contracts eta-lambda at
the root.  The generic proof strengthens the updated under-binder target
and replays the step in the source scope. -/
theorem iotaEta_inside_etaLam_join {scope : Nat}
    {innerFunction : RawTerm scope}
    {updatedUnderBinder : RawTerm (scope + 1)}
    (underBinderStep :
      Step (RawTerm.weaken innerFunction) updatedUnderBinder) :
    BetaEtaPairJoin
      (Or.inl
        (Step.cong .gen_lam ()
          (StepChildren.here
            (parentScope := scope) (headShift := 1) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            (Step.cong .gen_app ()
              (StepChildren.here
                (parentScope := scope + 1) (headShift := 0)
                (restShifts := [0])
                ((.childCons RawTerm.newestVar .childNil) :
                  RawTermChildren [0] (scope + 1))
                underBinderStep)))))
      (Or.inr (Step.eta.etaLam innerFunction)) :=
  BetaEtaPairJoin.etaLamArbitraryUnderBinderCong underBinderStep

/-- Resolver-facing wrapper for any beta+iota step leaving an eta-lambda
source. -/
theorem iotaEta_etaLam_source_join {scope : Nat}
    {innerFunction leftReduct : RawTerm scope}
    (leftStep : Step (RawTerm.etaLamSource innerFunction) leftReduct) :
    BetaEtaPairJoin
      (Or.inl leftStep)
      (Or.inr (Step.eta.etaLam innerFunction)) :=
  BetaEtaPairJoin.etaLamLeftStep leftStep

/-- Audit bit exported under `Step` for the inside-binder eta-lambda coverage. -/
def iotaEta_inside_binder_complete : Bool :=
  IotaRootKind.etaLamCoverageComplete

theorem iotaEta_inside_binder_complete_eq_true :
    iotaEta_inside_binder_complete = true := rfl

end Step

end FX1Poly.Core
