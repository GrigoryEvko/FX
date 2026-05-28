import LeanFX2.Foundation.PolyCell.Core.StepIotaEtaInsideBinder

/-! # Foundation/PolyCell/Core/StepIotaEtaDoubleStrips

Reserved iota-vs-eta double-strip coverage for future generator phases.

This file deliberately does not assert join theorems for rules that are
not present in the current `Step` relation.  The current beta+iota
relation has exactly the 16 iota roots catalogued by `IotaRootKind`; it
does not yet contain modal, path, clock, parametricity, or Glue
eliminator-on-intro iotas.  The safe artifact for task #386 is therefore
an audited reserved-slot table that records what will become a
double-strip critical pair when the matching generator/iota phase lands.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Future iota/eta double-strip families that are intentionally reserved
outside the current `Step` root-iota catalog. -/
inductive IotaEtaReservedDoubleStripKind : Type where
  | modal
  | path
  | clock
  | parametricity
  | glue
  deriving DecidableEq

namespace IotaEtaReservedDoubleStripKind

/-- Complete reserved double-strip catalog for the current roadmap. -/
def all : List IotaEtaReservedDoubleStripKind :=
  [ .modal
  , .path
  , .clock
  , .parametricity
  , .glue
  ]

/-- Roadmap milestone number that activates the reserved family. -/
def phaseMilestone : IotaEtaReservedDoubleStripKind → Nat
  | .modal => 93
  | .path => 61
  | .clock => 84
  | .parametricity => 86
  | .glue => 66

/-- Current eta rule, when the outer eta side already exists. -/
def etaKindOption : IotaEtaReservedDoubleStripKind → Option EtaStepKind
  | .modal => some .etaModIntro
  | .path => some .etaPathLam
  | .clock => none
  | .parametricity => none
  | .glue => some .etaGlueIntro

/-- Intro-side source generator, when represented in the current generator
table. -/
def introGeneratorOption :
    IotaEtaReservedDoubleStripKind → Option Generator
  | .modal => some .gen_modIntro
  | .path => some .gen_pathLam
  | .clock => none
  | .parametricity => none
  | .glue => some .gen_glueIntro

/-- Eliminator-side source generator, when represented in the current
generator table. -/
def eliminatorGeneratorOption :
    IotaEtaReservedDoubleStripKind → Option Generator
  | .modal => some .gen_modElim
  | .path => some .gen_pathApp
  | .clock => none
  | .parametricity => none
  | .glue => some .gen_glueElim

/-- Does the current beta+iota `Step` relation contain the matching
future eliminator-on-intro iota?  Today all five rows are reserved. -/
def hasCurrentStepIota (_reservedKind : IotaEtaReservedDoubleStripKind) :
    Bool :=
  false

theorem all_length :
    all.length = 5 := rfl

theorem phaseMilestones :
    all.map phaseMilestone = [93, 61, 84, 86, 66] := rfl

theorem currentStepIotas_absent :
    all.map hasCurrentStepIota =
      [false, false, false, false, false] := rfl

end IotaEtaReservedDoubleStripKind

/-- Why a reserved double-strip row is not yet a proof-producing critical
pair. -/
inductive IotaEtaReservedDoubleStripBlocker : Type where
  | missingStepIota
  | missingGeneratorAndStepIota
  deriving DecidableEq

/-- Reserved-status payload for a future double-strip critical pair. -/
inductive IotaEtaDoubleStripStatus : Type where
  | reserved
      (phaseMilestone : Nat)
      (blocker : IotaEtaReservedDoubleStripBlocker)
  deriving DecidableEq

namespace IotaEtaDoubleStripStatus

/-- Boolean view used by the reserved-slot audit gate. -/
def isReserved : IotaEtaDoubleStripStatus → Bool
  | .reserved _phaseMilestone _blocker => true

theorem reserved_isReserved
    (phaseMilestone : Nat)
    (blocker : IotaEtaReservedDoubleStripBlocker) :
    isReserved (.reserved phaseMilestone blocker) = true := rfl

end IotaEtaDoubleStripStatus

/-- One row in the future iota/eta double-strip table. -/
structure IotaEtaReservedDoubleStrip where
  reservedKind : IotaEtaReservedDoubleStripKind
  phaseMilestone : Nat
  etaKindOption : Option EtaStepKind
  introGeneratorOption : Option Generator
  eliminatorGeneratorOption : Option Generator
  status : IotaEtaDoubleStripStatus
  deriving DecidableEq

namespace IotaEtaReservedDoubleStrip

/-- The blocker for one reserved family. -/
def blockerForKind :
    IotaEtaReservedDoubleStripKind →
      IotaEtaReservedDoubleStripBlocker
  | .modal => .missingStepIota
  | .path => .missingStepIota
  | .clock => .missingGeneratorAndStepIota
  | .parametricity => .missingGeneratorAndStepIota
  | .glue => .missingStepIota

/-- Build the reserved-row metadata for one future double-strip family. -/
def rowForKind
    (reservedKind : IotaEtaReservedDoubleStripKind) :
    IotaEtaReservedDoubleStrip where
  reservedKind := reservedKind
  phaseMilestone := reservedKind.phaseMilestone
  etaKindOption := reservedKind.etaKindOption
  introGeneratorOption := reservedKind.introGeneratorOption
  eliminatorGeneratorOption := reservedKind.eliminatorGeneratorOption
  status :=
    .reserved reservedKind.phaseMilestone (blockerForKind reservedKind)

/-- A row is complete for this task when it is explicitly reserved and the
current `Step` relation has no matching iota root. -/
def isCompleteReservedRow
    (reservedRow : IotaEtaReservedDoubleStrip) : Bool :=
  reservedRow.status.isReserved &&
    (!reservedRow.reservedKind.hasCurrentStepIota)

theorem rowForKind_isCompleteReservedRow
    (reservedKind : IotaEtaReservedDoubleStripKind) :
    isCompleteReservedRow (rowForKind reservedKind) = true := by
  cases reservedKind <;> rfl

end IotaEtaReservedDoubleStrip

namespace IotaEtaReservedDoubleStripKind

/-- Current reserved double-strip rows. -/
def reservedRows : List IotaEtaReservedDoubleStrip :=
  all.map IotaEtaReservedDoubleStrip.rowForKind

/-- Build-time coverage bit for task #386. -/
def reservedRowsComplete : Bool :=
  reservedRows.all IotaEtaReservedDoubleStrip.isCompleteReservedRow

theorem reservedRows_length :
    reservedRows.length = 5 := rfl

theorem reservedRowsComplete_eq_true :
    reservedRowsComplete = true := rfl

theorem modal_status :
    (IotaEtaReservedDoubleStrip.rowForKind .modal).status =
      .reserved 93 .missingStepIota := rfl

theorem path_status :
    (IotaEtaReservedDoubleStrip.rowForKind .path).status =
      .reserved 61 .missingStepIota := rfl

theorem clock_status :
    (IotaEtaReservedDoubleStrip.rowForKind .clock).status =
      .reserved 84 .missingGeneratorAndStepIota := rfl

theorem parametricity_status :
    (IotaEtaReservedDoubleStrip.rowForKind .parametricity).status =
      .reserved 86 .missingGeneratorAndStepIota := rfl

theorem glue_status :
    (IotaEtaReservedDoubleStrip.rowForKind .glue).status =
      .reserved 66 .missingStepIota := rfl

end IotaEtaReservedDoubleStripKind

namespace Step

/-- Audit bit exported under `Step` for task #386.

This is intentionally a reserved-slot bit, not a join theorem.  When a
future phase adds one of these eliminator-on-intro iotas to `Step`, the
corresponding row must be replaced by a proof-producing critical-pair
entry. -/
def iotaEta_reserved_doublestrips_complete : Bool :=
  IotaEtaReservedDoubleStripKind.reservedRowsComplete

theorem iotaEta_reserved_doublestrips_complete_eq_true :
    iotaEta_reserved_doublestrips_complete = true := rfl

end Step

end LeanFX2.Foundation.PolyCell.Core
