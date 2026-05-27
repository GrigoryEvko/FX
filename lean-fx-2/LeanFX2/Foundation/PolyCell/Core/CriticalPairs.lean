import LeanFX2.Foundation.PolyCell.Core.StepPreservesShape

/-! # Foundation/PolyCell/Core/CriticalPairs
    — M6 confluence scaffold, root-rule catalog

This file starts M6 (`Generator`-table critical-pair enumeration) with
the finite catalog of **root** reduction rules: beta plus the 16 iota
rules.  The uniform `Step.cong` rule is intentionally not represented
as a root rule here, because its branchings are indexed by a parent
generator and a child position.  Those child-position branchings are the
next M6 slice.

The important invariant of this slice is modest but real: the
non-congruence part of `Step` is now computably visible as data.  The
next confluence files can consume this catalog instead of rediscovering
which generator heads have root redexes.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Root reduction rules: every one-step `Step` constructor except the
uniform congruence rule.

There are 17 entries: beta plus 16 iota rules.  `Step.cong` is handled
separately because it is not tied to a fixed source-head generator; it
depends on a parent generator and a child position. -/
inductive RootStepKind : Type where
  | beta
  | iotaBoolTrue
  | iotaBoolFalse
  | iotaFstPair
  | iotaSndPair
  | iotaNatElimZero
  | iotaNatRecZero
  | iotaListElimNil
  | iotaOptionMatchNone
  | iotaOptionMatchSome
  | iotaEitherMatchInl
  | iotaEitherMatchInr
  | iotaNatElimSucc
  | iotaNatRecSucc
  | iotaListElimCons
  | iotaIdJRefl
  | iotaIdStrictRecRefl
  deriving DecidableEq

namespace RootStepKind

/-- The complete finite catalog of root reduction rules. -/
def all : List RootStepKind :=
  [ .beta
  , .iotaBoolTrue
  , .iotaBoolFalse
  , .iotaFstPair
  , .iotaSndPair
  , .iotaNatElimZero
  , .iotaNatRecZero
  , .iotaListElimNil
  , .iotaOptionMatchNone
  , .iotaOptionMatchSome
  , .iotaEitherMatchInl
  , .iotaEitherMatchInr
  , .iotaNatElimSucc
  , .iotaNatRecSucc
  , .iotaListElimCons
  , .iotaIdJRefl
  , .iotaIdStrictRecRefl
  ]

/-- The source-head generator for a root rule. -/
def sourceGenerator : RootStepKind → Generator
  | .beta => .gen_app
  | .iotaBoolTrue => .gen_boolElim
  | .iotaBoolFalse => .gen_boolElim
  | .iotaFstPair => .gen_fst
  | .iotaSndPair => .gen_snd
  | .iotaNatElimZero => .gen_natElim
  | .iotaNatRecZero => .gen_natRec
  | .iotaListElimNil => .gen_listElim
  | .iotaOptionMatchNone => .gen_optionMatch
  | .iotaOptionMatchSome => .gen_optionMatch
  | .iotaEitherMatchInl => .gen_eitherMatch
  | .iotaEitherMatchInr => .gen_eitherMatch
  | .iotaNatElimSucc => .gen_natElim
  | .iotaNatRecSucc => .gen_natRec
  | .iotaListElimCons => .gen_listElim
  | .iotaIdJRefl => .gen_idJ
  | .iotaIdStrictRecRefl => .gen_idStrictRec

/-- Does this root rule fire at the given source-head generator? -/
def hasSourceGenerator (rootKind : RootStepKind)
    (sourceGenerator : Generator) : Bool :=
  if rootKind.sourceGenerator = sourceGenerator then true else false

/-- Root rules whose source term has the requested head generator. -/
def forSourceGenerator (sourceGenerator : Generator) : List RootStepKind :=
  all.filter (fun rootKind => rootKind.hasSourceGenerator sourceGenerator)

/-- Root/root overlap classification.

This is intentionally only the root-rule part of M6.  Congruence
overlaps need a child-position shape and are represented in a later
slice. -/
inductive RootOverlapShape : Type where
  | sameRootRedex
  | sameGeneratorDifferentRootRedexes
  | differentRootGenerators
  deriving DecidableEq

/-- Classify a pair of root rules by source-head overlap. -/
def classifyRootOverlap
    (leftKind rightKind : RootStepKind) : RootOverlapShape :=
  if leftKind = rightKind then
    .sameRootRedex
  else if leftKind.sourceGenerator = rightKind.sourceGenerator then
    .sameGeneratorDifferentRootRedexes
  else
    .differentRootGenerators

/-- A finite root/root critical-pair entry.

The full M6 `CriticalPair` will add congruence branchings and diamond
filler templates.  This root entry is the non-congruence subcatalog
that those later entries compose with. -/
structure RootCriticalPair where
  leftKind : RootStepKind
  rightKind : RootStepKind
  overlapShape : RootOverlapShape
  deriving DecidableEq

/-- Build a root/root pair entry from two root kinds. -/
def mkRootCriticalPair
    (leftKind rightKind : RootStepKind) : RootCriticalPair where
  leftKind := leftKind
  rightKind := rightKind
  overlapShape := classifyRootOverlap leftKind rightKind

/-- Pair one left root rule against a finite right-rule list. -/
def pairLeftWithRightKinds (leftKind : RootStepKind) :
    List RootStepKind → List RootCriticalPair
  | [] => []
  | rightKind :: remainingRightKinds =>
      mkRootCriticalPair leftKind rightKind ::
        pairLeftWithRightKinds leftKind remainingRightKinds

/-- Cartesian product of two finite root-rule lists, with overlap
classification attached to each pair. -/
def pairsForKindLists :
    List RootStepKind → List RootStepKind → List RootCriticalPair
  | [], _ => []
  | leftKind :: remainingLeftKinds, rightKinds =>
      pairLeftWithRightKinds leftKind rightKinds ++
        pairsForKindLists remainingLeftKinds rightKinds

/-- Enumerate root/root pairs for two source-head generators. -/
def criticalPairsForSourceGenerators
    (leftGenerator rightGenerator : Generator) : List RootCriticalPair :=
  pairsForKindLists
    (forSourceGenerator leftGenerator)
    (forSourceGenerator rightGenerator)

theorem all_length :
    all.length = 17 := rfl

theorem forSourceGenerator_app :
    forSourceGenerator .gen_app = [.beta] := rfl

theorem forSourceGenerator_boolElim :
    forSourceGenerator .gen_boolElim =
      [.iotaBoolTrue, .iotaBoolFalse] := rfl

theorem forSourceGenerator_unit :
    forSourceGenerator .gen_unit = [] := rfl

theorem classifyRootOverlap_beta_beta :
    classifyRootOverlap .beta .beta = .sameRootRedex := rfl

theorem classifyRootOverlap_bool_iotas :
    classifyRootOverlap .iotaBoolTrue .iotaBoolFalse =
      .sameGeneratorDifferentRootRedexes := rfl

theorem classifyRootOverlap_beta_boolTrue :
    classifyRootOverlap .beta .iotaBoolTrue =
      .differentRootGenerators := rfl

end RootStepKind

namespace Generator

/-- Root/root critical pairs keyed by source-head generators.

This is the first, root-only part of M6.  It deliberately excludes
`Step.cong` branchings, which need a child-position index in addition
to the parent generator. -/
def rootCriticalPairs
    (leftGenerator rightGenerator : Generator) :
    List RootStepKind.RootCriticalPair :=
  RootStepKind.criticalPairsForSourceGenerators
    leftGenerator rightGenerator

/-- Decidable emptiness for the root/root critical-pair catalog. -/
def rootCriticalPairsEmptyDecision
    (leftGenerator rightGenerator : Generator) :
    Decidable (rootCriticalPairs leftGenerator rightGenerator = []) :=
  inferInstance

theorem rootCriticalPairs_app_app :
    rootCriticalPairs .gen_app .gen_app =
      [RootStepKind.mkRootCriticalPair .beta .beta] := rfl

theorem rootCriticalPairs_boolElim_boolElim_length :
    (rootCriticalPairs .gen_boolElim .gen_boolElim).length = 4 := rfl

theorem rootCriticalPairs_unit_app :
    rootCriticalPairs .gen_unit .gen_app = [] := rfl

/-- One child position of a generator, represented as computable data.

`childIndex` is zero-based.  `scopeShift` is copied from the matching
entry of `Generator.binderShifts`.  The pair is produced only by
`Generator.childPositions`, so consumers should treat this as the
computable projection of the generator table rather than arbitrary
user input. -/
structure ChildPosition where
  parentGenerator : Generator
  childIndex : Nat
  scopeShift : Nat
  deriving DecidableEq

/-- Enumerate child positions from a binder-shift list, threading the
zero-based child index explicitly. -/
def childPositionsFromShifts (parentGenerator : Generator) :
    Nat → List Nat → List ChildPosition
  | _, [] => []
  | childIndex, scopeShift :: remainingShifts =>
      { parentGenerator := parentGenerator
        childIndex := childIndex
        scopeShift := scopeShift } ::
        childPositionsFromShifts parentGenerator
          (childIndex + 1) remainingShifts

/-- The child-position table used by `Step.cong` branchings. -/
def childPositions (parentGenerator : Generator) : List ChildPosition :=
  childPositionsFromShifts parentGenerator 0 parentGenerator.binderShifts

/-- Orientation of a root/congruence branching in a local confluence
problem. -/
inductive RootCongruenceOrientation : Type where
  | rootLeftCongruenceRight
  | congruenceLeftRootRight
  deriving DecidableEq

/-- A root rule overlapping a `Step.cong` reduction under one child
position of the same parent generator.

This is still only a **schema** for M6.  The diamond filler for each
schema belongs to the later filler-template slice. -/
structure RootCongruenceBranching where
  rootKind : RootStepKind
  childPosition : ChildPosition
  orientation : RootCongruenceOrientation
  deriving DecidableEq

/-- Build both left/right orientations for one root rule and one child
position. -/
def rootCongruenceBranchingsForPosition
    (rootKind : RootStepKind) (childPosition : ChildPosition) :
    List RootCongruenceBranching :=
  [ { rootKind := rootKind
      childPosition := childPosition
      orientation := .rootLeftCongruenceRight }
  , { rootKind := rootKind
      childPosition := childPosition
      orientation := .congruenceLeftRootRight }
  ]

/-- Pair one root rule with all child positions of its source generator. -/
def rootCongruenceBranchingsForRoot
    (rootKind : RootStepKind) : List RootCongruenceBranching :=
  pairRootWithPositions rootKind (childPositions rootKind.sourceGenerator)
where
  pairRootWithPositions
      (rootKind : RootStepKind) : List ChildPosition →
      List RootCongruenceBranching
    | [] => []
    | childPosition :: remainingPositions =>
        rootCongruenceBranchingsForPosition rootKind childPosition ++
          pairRootWithPositions rootKind remainingPositions

/-- Enumerate all root/congruence branchings for a parent generator. -/
def rootCongruenceBranchings
    (parentGenerator : Generator) : List RootCongruenceBranching :=
  pairRootsWithPositions
    (RootStepKind.forSourceGenerator parentGenerator)
where
  pairRootsWithPositions : List RootStepKind →
      List RootCongruenceBranching
    | [] => []
    | rootKind :: remainingRootKinds =>
        rootCongruenceBranchingsForRoot rootKind ++
          pairRootsWithPositions remainingRootKinds

theorem childPositions_app :
    childPositions .gen_app =
      [ { parentGenerator := .gen_app, childIndex := 0, scopeShift := 0 }
      , { parentGenerator := .gen_app, childIndex := 1, scopeShift := 0 }
      ] := rfl

theorem childPositions_lam :
    childPositions .gen_lam =
      [ { parentGenerator := .gen_lam, childIndex := 0, scopeShift := 1 }
      ] := rfl

theorem childPositions_unit :
    childPositions .gen_unit = [] := rfl

theorem rootCongruenceBranchings_app_length :
    (rootCongruenceBranchings .gen_app).length = 4 := rfl

theorem rootCongruenceBranchings_boolElim_length :
    (rootCongruenceBranchings .gen_boolElim).length = 12 := rfl

theorem rootCongruenceBranchings_unit :
    rootCongruenceBranchings .gen_unit = [] := rfl

/-- Top-level M6 critical-pair schema.

This intentionally remains a **schema** datatype: it records which
finite branching family a later diamond filler must handle, but it does
not claim that the filler has been constructed. -/
inductive CriticalPair : Type where
  | rootRoot (rootPair : RootStepKind.RootCriticalPair)
  | rootCongruence (branching : RootCongruenceBranching)
  deriving DecidableEq

/-- Lift root/root entries into the top-level M6 critical-pair schema. -/
def criticalPairsFromRootPairs :
    List RootStepKind.RootCriticalPair → List CriticalPair
  | [] => []
  | rootPair :: remainingRootPairs =>
      CriticalPair.rootRoot rootPair ::
        criticalPairsFromRootPairs remainingRootPairs

/-- Lift root/congruence entries into the top-level M6 critical-pair
schema. -/
def criticalPairsFromRootCongruenceBranchings :
    List RootCongruenceBranching → List CriticalPair
  | [] => []
  | branching :: remainingBranchings =>
      CriticalPair.rootCongruence branching ::
        criticalPairsFromRootCongruenceBranchings remainingBranchings

/-- Unified computable critical-pair schema for a pair of source-head
generators.

The root/root component is always the finite cross-product from
`rootCriticalPairs`.  Root/congruence branchings are added only on the
same source-head generator, because `Step.cong` preserves the outer
generator and fires under one of that generator's child positions. -/
def criticalPairs (leftGenerator rightGenerator : Generator) :
    List CriticalPair :=
  criticalPairsFromRootPairs
    (rootCriticalPairs leftGenerator rightGenerator) ++
    if leftGenerator = rightGenerator then
      criticalPairsFromRootCongruenceBranchings
        (rootCongruenceBranchings leftGenerator)
    else
      []

/-- Decidable emptiness for the unified critical-pair schema. -/
def criticalPairsEmptyDecision
    (leftGenerator rightGenerator : Generator) :
    Decidable (criticalPairs leftGenerator rightGenerator = []) :=
  inferInstance

theorem criticalPairs_app_app_length :
    (criticalPairs .gen_app .gen_app).length = 5 := rfl

theorem criticalPairs_boolElim_boolElim_length :
    (criticalPairs .gen_boolElim .gen_boolElim).length = 16 := rfl

theorem criticalPairs_unit_app :
    criticalPairs .gen_unit .gen_app = [] := rfl

end Generator

end LeanFX2.Foundation.PolyCell.Core
