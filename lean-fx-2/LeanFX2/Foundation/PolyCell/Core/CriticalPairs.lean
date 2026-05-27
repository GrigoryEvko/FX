import LeanFX2.Foundation.PolyCell.Core.StepPreservesShape
import LeanFX2.Foundation.PolyCell.Core.StepStar

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

namespace Step

/-- `boolTrue` is a nullary constructor, not a redex source.  This
rules out root/congruence branchings that try to reduce the
`boolElim` scrutinee in the true-iota case. -/
theorem boolTrue_hasNoStep {scope : Nat} {target : RawTerm scope} :
    Not (Step ((.mkGen .gen_boolTrue () .childNil) : RawTerm scope) target) := by
  intro step
  cases step
  case cong childStep =>
    cases childStep

/-- `boolFalse` is a nullary constructor, not a redex source. -/
theorem boolFalse_hasNoStep {scope : Nat} {target : RawTerm scope} :
    Not (Step ((.mkGen .gen_boolFalse () .childNil) : RawTerm scope) target) := by
  intro step
  cases step
  case cong childStep =>
    cases childStep

/-- `natZero` is a nullary constructor, not a redex source. -/
theorem natZero_hasNoStep {scope : Nat} {target : RawTerm scope} :
    Not (Step ((.mkGen .gen_natZero () .childNil) : RawTerm scope) target) := by
  intro step
  cases step
  case cong childStep =>
    cases childStep

/-- `listNil` is a nullary constructor, not a redex source. -/
theorem listNil_hasNoStep {scope : Nat} {target : RawTerm scope} :
    Not (Step ((.mkGen .gen_listNil () .childNil) : RawTerm scope) target) := by
  intro step
  cases step
  case cong childStep =>
    cases childStep

/-- `optionNone` is a nullary constructor, not a redex source. -/
theorem optionNone_hasNoStep {scope : Nat} {target : RawTerm scope} :
    Not (Step ((.mkGen .gen_optionNone () .childNil) : RawTerm scope) target) := by
  intro step
  cases step
  case cong childStep =>
    cases childStep

end Step

/-- A concrete local one-step branching in the v2 reduction relation.

Unlike `Generator.CriticalPair`, this is proof-relevant: it stores the
actual source term, both one-step reducts, and the two `Step` witnesses.
M7's `cd_lemma` consumes branchings of this shape after dispatching
through the finite M6 schema. -/
structure LocalStepBranching {scope : Nat} where
  source : RawTerm scope
  leftReduct : RawTerm scope
  rightReduct : RawTerm scope
  leftStep : Step source leftReduct
  rightStep : Step source rightReduct

namespace LocalStepBranching

/-- The concrete same-root beta/beta branching.

This is the first proof-relevant instance corresponding to a concrete
`Generator.CriticalPair.rootRoot` entry (`gen_app` / beta against beta).
Both one-step paths contract the same beta redex to the same substitution
result. -/
def betaBeta {scope : Nat} (body : RawTerm (scope + 1))
    (arg : RawTerm scope) : LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_lam () (.childCons body .childNil))
        (.childCons arg .childNil))
  leftReduct := RawTerm.subst0 body arg
  rightReduct := RawTerm.subst0 body arg
  leftStep := Step.beta
  rightStep := Step.beta

/-- The concrete same-root bool-true iota branching.

Both one-step paths eliminate the same `boolElim boolTrue` redex and
select the then-branch. -/
def iotaBoolTrueSameRoot {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolTrue () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := thenBranch
  rightReduct := thenBranch
  leftStep := Step.iotaBoolTrue
  rightStep := Step.iotaBoolTrue

/-- The concrete same-root bool-false iota branching.

Both one-step paths eliminate the same `boolElim boolFalse` redex and
select the else-branch. -/
def iotaBoolFalseSameRoot {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolFalse () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := elseBranch
  rightReduct := elseBranch
  leftStep := Step.iotaBoolFalse
  rightStep := Step.iotaBoolFalse

/-- The concrete same-root first-projection iota branching. -/
def iotaFstPairSameRoot {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_fst ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := firstValue
  rightReduct := firstValue
  leftStep := Step.iotaFstPair
  rightStep := Step.iotaFstPair

/-- The concrete same-root second-projection iota branching. -/
def iotaSndPairSameRoot {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_snd ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := secondValue
  rightReduct := secondValue
  leftStep := Step.iotaSndPair
  rightStep := Step.iotaSndPair

/-- The concrete same-root `natElim` zero-case iota branching. -/
def iotaNatElimZeroSameRoot {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct := zeroBranch
  leftStep := Step.iotaNatElimZero
  rightStep := Step.iotaNatElimZero

/-- The concrete same-root `natRec` zero-case iota branching. -/
def iotaNatRecZeroSameRoot {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct := zeroBranch
  leftStep := Step.iotaNatRecZero
  rightStep := Step.iotaNatRecZero

/-- The concrete same-root `listElim` nil-case iota branching. -/
def iotaListElimNilSameRoot {scope : Nat}
    (nilBranch consBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listNil () .childNil)
        (.childCons nilBranch (.childCons consBranch .childNil)))
  leftReduct := nilBranch
  rightReduct := nilBranch
  leftStep := Step.iotaListElimNil
  rightStep := Step.iotaListElimNil

/-- The concrete same-root `optionMatch` none-case iota branching. -/
def iotaOptionMatchNoneSameRoot {scope : Nat}
    (noneBranch someBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionNone () .childNil)
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct := noneBranch
  rightReduct := noneBranch
  leftStep := Step.iotaOptionMatchNone
  rightStep := Step.iotaOptionMatchNone

/-- The concrete same-root `idJ` refl-case iota branching. -/
def iotaIdJReflSameRoot {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idJ ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct := baseCase
  leftStep := Step.iotaIdJRefl
  rightStep := Step.iotaIdJRefl

/-- The concrete same-root `idStrictRec` refl-case iota branching. -/
def iotaIdStrictRecReflSameRoot {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idStrictRec ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct := baseCase
  leftStep := Step.iotaIdStrictRecRefl
  rightStep := Step.iotaIdStrictRecRefl

/-- The concrete same-root `optionMatch` some-case iota branching. -/
def iotaOptionMatchSomeSameRoot {scope : Nat}
    (value noneBranch someBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons someBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons someBranch (.childCons value .childNil))
  leftStep := Step.iotaOptionMatchSome
  rightStep := Step.iotaOptionMatchSome

/-- The concrete same-root `eitherMatch` inl-case iota branching. -/
def iotaEitherMatchInlSameRoot {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons leftBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons leftBranch (.childCons value .childNil))
  leftStep := Step.iotaEitherMatchInl
  rightStep := Step.iotaEitherMatchInl

/-- The concrete same-root `eitherMatch` inr-case iota branching. -/
def iotaEitherMatchInrSameRoot {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons rightBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons rightBranch (.childCons value .childNil))
  leftStep := Step.iotaEitherMatchInr
  rightStep := Step.iotaEitherMatchInr

/-- The concrete same-root `natElim` succ-case iota branching. -/
def iotaNatElimSuccSameRoot {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natElim ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natElim ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  leftStep := Step.iotaNatElimSucc
  rightStep := Step.iotaNatElimSucc

/-- The concrete same-root `natRec` succ-case iota branching. -/
def iotaNatRecSuccSameRoot {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natRec ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natRec ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  leftStep := Step.iotaNatRecSucc
  rightStep := Step.iotaNatRecSucc

/-- The concrete same-root `listElim` cons-case iota branching. -/
def iotaListElimConsSameRoot {scope : Nat}
    (headValue tailValue nilBranch consBranch : RawTerm scope) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listCons ()
          (.childCons headValue (.childCons tailValue .childNil)))
        (.childCons nilBranch (.childCons consBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons consBranch (.childCons headValue .childNil)))
            (.childCons tailValue .childNil)))
        (.childCons
          (.mkGen .gen_listElim ()
            (.childCons tailValue
              (.childCons nilBranch (.childCons consBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons consBranch (.childCons headValue .childNil)))
            (.childCons tailValue .childNil)))
        (.childCons
          (.mkGen .gen_listElim ()
            (.childCons tailValue
              (.childCons nilBranch (.childCons consBranch .childNil))))
          .childNil))
  leftStep := Step.iotaListElimCons
  rightStep := Step.iotaListElimCons

/-- `boolElim boolTrue` and `boolElim boolFalse` are disjoint root
redex sources, so a true/false root-root branching is impossible. -/
theorem iotaBoolTrue_iotaBoolFalse_sourcesDisjoint {scope : Nat}
    (thenTrue elseTrue thenFalse elseFalse : RawTerm scope) :
    Not
      ((iotaBoolTrueSameRoot thenTrue elseTrue).source =
        (iotaBoolFalseSameRoot thenFalse elseFalse).source) := by
  intro sourceEquality
  dsimp [iotaBoolTrueSameRoot, iotaBoolFalseSameRoot] at sourceEquality
  cases sourceEquality

/-- `natElim natZero` and `natElim (natSucc _)` are disjoint root
redex sources, so a zero/succ root-root branching is impossible. -/
theorem iotaNatElimZero_iotaNatElimSucc_sourcesDisjoint {scope : Nat}
    (zeroBranch succBranch predecessor
      zeroBranchSucc succBranchSucc : RawTerm scope) :
    Not
      ((iotaNatElimZeroSameRoot zeroBranch succBranch).source =
        (iotaNatElimSuccSameRoot
          predecessor zeroBranchSucc succBranchSucc).source) := by
  intro sourceEquality
  dsimp [iotaNatElimZeroSameRoot, iotaNatElimSuccSameRoot] at sourceEquality
  cases sourceEquality

/-- `natRec natZero` and `natRec (natSucc _)` are disjoint root
redex sources, so a zero/succ root-root branching is impossible. -/
theorem iotaNatRecZero_iotaNatRecSucc_sourcesDisjoint {scope : Nat}
    (zeroBranch succBranch predecessor
      zeroBranchSucc succBranchSucc : RawTerm scope) :
    Not
      ((iotaNatRecZeroSameRoot zeroBranch succBranch).source =
        (iotaNatRecSuccSameRoot
          predecessor zeroBranchSucc succBranchSucc).source) := by
  intro sourceEquality
  dsimp [iotaNatRecZeroSameRoot, iotaNatRecSuccSameRoot] at sourceEquality
  cases sourceEquality

/-- `listElim listNil` and `listElim (listCons _ _)` are disjoint root
redex sources, so a nil/cons root-root branching is impossible. -/
theorem iotaListElimNil_iotaListElimCons_sourcesDisjoint {scope : Nat}
    (nilBranch consBranch headValue tailValue
      nilBranchCons consBranchCons : RawTerm scope) :
    Not
      ((iotaListElimNilSameRoot nilBranch consBranch).source =
        (iotaListElimConsSameRoot
          headValue tailValue nilBranchCons consBranchCons).source) := by
  intro sourceEquality
  dsimp [iotaListElimNilSameRoot, iotaListElimConsSameRoot] at sourceEquality
  cases sourceEquality

/-- `optionMatch optionNone` and `optionMatch (optionSome _)` are disjoint
root redex sources, so a none/some root-root branching is impossible. -/
theorem iotaOptionMatchNone_iotaOptionMatchSome_sourcesDisjoint
    {scope : Nat}
    (noneBranch someBranch value
      noneBranchSome someBranchSome : RawTerm scope) :
    Not
      ((iotaOptionMatchNoneSameRoot noneBranch someBranch).source =
        (iotaOptionMatchSomeSameRoot
          value noneBranchSome someBranchSome).source) := by
  intro sourceEquality
  dsimp [iotaOptionMatchNoneSameRoot, iotaOptionMatchSomeSameRoot]
    at sourceEquality
  cases sourceEquality

/-- `eitherMatch (eitherInl _)` and `eitherMatch (eitherInr _)` are
disjoint root redex sources, so an inl/inr root-root branching is
impossible. -/
theorem iotaEitherMatchInl_iotaEitherMatchInr_sourcesDisjoint
    {scope : Nat}
    (leftValue leftBranch rightBranch rightValue
      leftBranchRight rightBranchRight : RawTerm scope) :
    Not
      ((iotaEitherMatchInlSameRoot
          leftValue leftBranch rightBranch).source =
        (iotaEitherMatchInrSameRoot
          rightValue leftBranchRight rightBranchRight).source) := by
  intro sourceEquality
  dsimp [iotaEitherMatchInlSameRoot, iotaEitherMatchInrSameRoot]
    at sourceEquality
  cases sourceEquality

/-- Root `boolTrue` iota branching against congruence in the selected
then-branch.  The local diamond joins at the stepped then-branch. -/
def iotaBoolTrueThenCong {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolTrue () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := thenBranch
  rightReduct :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolTrue () .childNil)
        (.childCons steppedThenBranch (.childCons elseBranch .childNil)))
  leftStep := Step.iotaBoolTrue
  rightStep :=
    Step.cong .gen_boolElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_boolTrue () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons elseBranch .childNil) :
            RawTermChildren [0] scope)
          thenStep))

/-- Root `boolTrue` iota branching against congruence in the discarded
else-branch.  The local diamond joins immediately at the then-branch. -/
def iotaBoolTrueElseCong {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolTrue () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := thenBranch
  rightReduct :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolTrue () .childNil)
        (.childCons thenBranch (.childCons steppedElseBranch .childNil)))
  leftStep := Step.iotaBoolTrue
  rightStep :=
    Step.cong .gen_boolElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_boolTrue () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          thenBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            elseStep)))

/-- Root `boolFalse` iota branching against congruence in the discarded
then-branch.  The local diamond joins immediately at the else-branch. -/
def iotaBoolFalseThenCong {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolFalse () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := elseBranch
  rightReduct :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolFalse () .childNil)
        (.childCons steppedThenBranch (.childCons elseBranch .childNil)))
  leftStep := Step.iotaBoolFalse
  rightStep :=
    Step.cong .gen_boolElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_boolFalse () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons elseBranch .childNil) :
            RawTermChildren [0] scope)
          thenStep))

/-- Root `boolFalse` iota branching against congruence in the selected
else-branch.  The local diamond joins at the stepped else-branch. -/
def iotaBoolFalseElseCong {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolFalse () .childNil)
        (.childCons thenBranch (.childCons elseBranch .childNil)))
  leftReduct := elseBranch
  rightReduct :=
    .mkGen .gen_boolElim ()
      (.childCons
        (.mkGen .gen_boolFalse () .childNil)
        (.childCons thenBranch (.childCons steppedElseBranch .childNil)))
  leftStep := Step.iotaBoolFalse
  rightStep :=
    Step.cong .gen_boolElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_boolFalse () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          thenBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            elseStep)))

/-- Root `fst` iota branching against congruence in the selected first
pair component.  The local diamond joins at the stepped first component. -/
def iotaFstPairFirstCong {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_fst ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := firstValue
  rightReduct :=
    .mkGen .gen_fst ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons steppedFirstValue (.childCons secondValue .childNil)))
        .childNil)
  leftStep := Step.iotaFstPair
  rightStep :=
    Step.cong .gen_fst ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [])
        (.childNil : RawTermChildren [] scope)
        (Step.cong .gen_pair ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons secondValue .childNil) :
              RawTermChildren [0] scope)
            firstStep)))

/-- Root `fst` iota branching against congruence in the discarded second
pair component.  The local diamond joins immediately at the first
component. -/
def iotaFstPairSecondCong {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_fst ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := firstValue
  rightReduct :=
    .mkGen .gen_fst ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons steppedSecondValue .childNil)))
        .childNil)
  leftStep := Step.iotaFstPair
  rightStep :=
    Step.cong .gen_fst ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [])
        (.childNil : RawTermChildren [] scope)
        (Step.cong .gen_pair ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            firstValue
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              secondStep))))

/-- Root `snd` iota branching against congruence in the discarded first
pair component.  The local diamond joins immediately at the second
component. -/
def iotaSndPairFirstCong {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_snd ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := secondValue
  rightReduct :=
    .mkGen .gen_snd ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons steppedFirstValue (.childCons secondValue .childNil)))
        .childNil)
  leftStep := Step.iotaSndPair
  rightStep :=
    Step.cong .gen_snd ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [])
        (.childNil : RawTermChildren [] scope)
        (Step.cong .gen_pair ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            ((.childCons secondValue .childNil) :
              RawTermChildren [0] scope)
            firstStep)))

/-- Root `snd` iota branching against congruence in the selected second
pair component.  The local diamond joins at the stepped second component. -/
def iotaSndPairSecondCong {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_snd ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons secondValue .childNil)))
        .childNil)
  leftReduct := secondValue
  rightReduct :=
    .mkGen .gen_snd ()
      (.childCons
        (.mkGen .gen_pair ()
          (.childCons firstValue (.childCons steppedSecondValue .childNil)))
        .childNil)
  leftStep := Step.iotaSndPair
  rightStep :=
    Step.cong .gen_snd ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [])
        (.childNil : RawTermChildren [] scope)
        (Step.cong .gen_pair ()
          (StepChildren.there
            (parentScope := scope) (headShift := 0) (restShifts := [0])
            firstValue
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              secondStep))))

/-- Root `natElim natZero` iota branching against congruence in the
selected zero-branch. -/
def iotaNatElimZeroBranchCong {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons steppedZeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatElimZero
  rightStep :=
    Step.cong .gen_natElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natZero () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons succBranch .childNil) :
            RawTermChildren [0] scope)
          zeroStep))

/-- Root `natElim natZero` iota branching against congruence in the
discarded successor branch. -/
def iotaNatElimSuccBranchCong {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons steppedSuccBranch .childNil)))
  leftStep := Step.iotaNatElimZero
  rightStep :=
    Step.cong .gen_natElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natZero () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          zeroBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            succStep)))

/-- Root `natRec natZero` iota branching against congruence in the
selected zero-branch. -/
def iotaNatRecZeroBranchCong {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons steppedZeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatRecZero
  rightStep :=
    Step.cong .gen_natRec ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natZero () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons succBranch .childNil) :
            RawTermChildren [0] scope)
          zeroStep))

/-- Root `natRec natZero` iota branching against congruence in the
discarded successor branch. -/
def iotaNatRecSuccBranchCong {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct := zeroBranch
  rightReduct :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natZero () .childNil)
        (.childCons zeroBranch (.childCons steppedSuccBranch .childNil)))
  leftStep := Step.iotaNatRecZero
  rightStep :=
    Step.cong .gen_natRec ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natZero () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          zeroBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            succStep)))

/-- Root `natElim (natSucc predecessor)` iota branching against congruence
in the zero-branch.  The iota reduct contains the zero branch only inside the
recursive call, so the local diamond joins by stepping that recursive call. -/
def iotaNatElimSuccZeroBranchCong {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natElim ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons steppedZeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatElimSucc
  rightStep :=
    Step.cong .gen_natElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natSucc () (.childCons predecessor .childNil)) :
          RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons succBranch .childNil) :
            RawTermChildren [0] scope)
          zeroStep))

/-- Root `natElim (natSucc predecessor)` iota branching against congruence
in the successor branch.  The successor branch appears both as the app-chain
function and inside the recursive call. -/
def iotaNatElimSuccSuccBranchCong {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natElim ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons steppedSuccBranch .childNil)))
  leftStep := Step.iotaNatElimSucc
  rightStep :=
    Step.cong .gen_natElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natSucc () (.childCons predecessor .childNil)) :
          RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          zeroBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            succStep)))

/-- Root `natRec (natSucc predecessor)` iota branching against congruence in
the zero-branch. -/
def iotaNatRecSuccZeroBranchCong {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natRec ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons steppedZeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatRecSucc
  rightStep :=
    Step.cong .gen_natRec ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natSucc () (.childCons predecessor .childNil)) :
          RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons succBranch .childNil) :
            RawTermChildren [0] scope)
          zeroStep))

/-- Root `natRec (natSucc predecessor)` iota branching against congruence in
the successor branch. -/
def iotaNatRecSuccSuccBranchCong {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natRec ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons steppedSuccBranch .childNil)))
  leftStep := Step.iotaNatRecSucc
  rightStep :=
    Step.cong .gen_natRec ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_natSucc () (.childCons predecessor .childNil)) :
          RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          zeroBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            succStep)))

/-- Root `natElim (natSucc predecessor)` iota branching against congruence
inside the `natSucc` predecessor.  The predecessor occurs twice in the root
iota reduct: as the successor-branch argument and as the recursive-call
scrutinee. -/
def iotaNatElimSuccPredecessorCong {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natElim ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natElim ()
      (.childCons
        (.mkGen .gen_natSucc ()
          (.childCons steppedPredecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatElimSucc
  rightStep :=
    Step.cong .gen_natElim ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.childCons zeroBranch (.childCons succBranch .childNil)) :
          RawTermChildren [0, 0] scope)
        (Step.cong .gen_natSucc ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            predecessorStep)))

/-- Root `natRec (natSucc predecessor)` iota branching against congruence
inside the `natSucc` predecessor. -/
def iotaNatRecSuccPredecessorCong {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons
        (.mkGen .gen_app ()
          (.childCons succBranch (.childCons predecessor .childNil)))
        (.childCons
          (.mkGen .gen_natRec ()
            (.childCons predecessor
              (.childCons zeroBranch (.childCons succBranch .childNil))))
          .childNil))
  rightReduct :=
    .mkGen .gen_natRec ()
      (.childCons
        (.mkGen .gen_natSucc ()
          (.childCons steppedPredecessor .childNil))
        (.childCons zeroBranch (.childCons succBranch .childNil)))
  leftStep := Step.iotaNatRecSucc
  rightStep :=
    Step.cong .gen_natRec ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.childCons zeroBranch (.childCons succBranch .childNil)) :
          RawTermChildren [0, 0] scope)
        (Step.cong .gen_natSucc ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            predecessorStep)))

/-- Root `listElim listNil` iota branching against congruence in the
selected nil-branch. -/
def iotaListElimNilBranchCong {scope : Nat}
    {nilBranch steppedNilBranch consBranch : RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listNil () .childNil)
        (.childCons nilBranch (.childCons consBranch .childNil)))
  leftReduct := nilBranch
  rightReduct :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listNil () .childNil)
        (.childCons steppedNilBranch (.childCons consBranch .childNil)))
  leftStep := Step.iotaListElimNil
  rightStep :=
    Step.cong .gen_listElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_listNil () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons consBranch .childNil) :
            RawTermChildren [0] scope)
          nilStep))

/-- Root `listElim listNil` iota branching against congruence in the
discarded cons-branch. -/
def iotaListElimConsBranchCong {scope : Nat}
    {nilBranch consBranch steppedConsBranch : RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listNil () .childNil)
        (.childCons nilBranch (.childCons consBranch .childNil)))
  leftReduct := nilBranch
  rightReduct :=
    .mkGen .gen_listElim ()
      (.childCons
        (.mkGen .gen_listNil () .childNil)
        (.childCons nilBranch (.childCons steppedConsBranch .childNil)))
  leftStep := Step.iotaListElimNil
  rightStep :=
    Step.cong .gen_listElim ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_listNil () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          nilBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            consStep)))

/-- Root `optionMatch optionNone` iota branching against congruence in
the selected none-branch. -/
def iotaOptionMatchNoneBranchCong {scope : Nat}
    {noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionNone () .childNil)
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct := noneBranch
  rightReduct :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionNone () .childNil)
        (.childCons steppedNoneBranch (.childCons someBranch .childNil)))
  leftStep := Step.iotaOptionMatchNone
  rightStep :=
    Step.cong .gen_optionMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_optionNone () .childNil) : RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons someBranch .childNil) :
            RawTermChildren [0] scope)
          noneStep))

/-- Root `optionMatch optionNone` iota branching against congruence in
the discarded some-branch. -/
def iotaOptionMatchSomeBranchCong {scope : Nat}
    {noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionNone () .childNil)
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct := noneBranch
  rightReduct :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionNone () .childNil)
        (.childCons noneBranch (.childCons steppedSomeBranch .childNil)))
  leftStep := Step.iotaOptionMatchNone
  rightStep :=
    Step.cong .gen_optionMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_optionNone () .childNil) : RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          noneBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            someStep)))

/-- Root `optionMatch (optionSome value)` iota branching against
congruence inside the `optionSome` payload. -/
def iotaOptionMatchSomeValueCong {scope : Nat}
    {value steppedValue noneBranch someBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons someBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons steppedValue .childNil))
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftStep := Step.iotaOptionMatchSome
  rightStep :=
    Step.cong .gen_optionMatch ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.childCons noneBranch (.childCons someBranch .childNil)) :
          RawTermChildren [0, 0] scope)
        (Step.cong .gen_optionSome ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            valueStep)))

/-- Root `optionMatch (optionSome value)` iota branching against
congruence in the discarded none-branch. -/
def iotaOptionMatchSomeNoneBranchCong {scope : Nat}
    {value noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons someBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons steppedNoneBranch (.childCons someBranch .childNil)))
  leftStep := Step.iotaOptionMatchSome
  rightStep :=
    Step.cong .gen_optionMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_optionSome () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons someBranch .childNil) :
            RawTermChildren [0] scope)
          noneStep))

/-- Root `optionMatch (optionSome value)` iota branching against
congruence in the selected some-branch. -/
def iotaOptionMatchSomeSomeBranchCong {scope : Nat}
    {value noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons noneBranch (.childCons someBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons someBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_optionMatch ()
      (.childCons
        (.mkGen .gen_optionSome () (.childCons value .childNil))
        (.childCons noneBranch (.childCons steppedSomeBranch .childNil)))
  leftStep := Step.iotaOptionMatchSome
  rightStep :=
    Step.cong .gen_optionMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_optionSome () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          noneBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            someStep)))

/-- Root `eitherMatch (eitherInl value)` iota branching against congruence
inside the `eitherInl` payload. -/
def iotaEitherMatchInlValueCong {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons leftBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons steppedValue .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInl
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.childCons leftBranch (.childCons rightBranch .childNil)) :
          RawTermChildren [0, 0] scope)
        (Step.cong .gen_eitherInl ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            valueStep)))

/-- Root `eitherMatch (eitherInl value)` iota branching against congruence
in the selected left branch. -/
def iotaEitherMatchInlLeftBranchCong {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons leftBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons steppedLeftBranch (.childCons rightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInl
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_eitherInl () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons rightBranch .childNil) :
            RawTermChildren [0] scope)
          leftStep))

/-- Root `eitherMatch (eitherInl value)` iota branching against congruence
in the discarded right branch. -/
def iotaEitherMatchInlRightBranchCong {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons leftBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInl () (.childCons value .childNil))
        (.childCons leftBranch (.childCons steppedRightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInl
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_eitherInl () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          leftBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            rightStep)))

/-- Root `eitherMatch (eitherInr value)` iota branching against congruence
inside the `eitherInr` payload. -/
def iotaEitherMatchInrValueCong {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons rightBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons steppedValue .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInr
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.childCons leftBranch (.childCons rightBranch .childNil)) :
          RawTermChildren [0, 0] scope)
        (Step.cong .gen_eitherInr ()
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            valueStep)))

/-- Root `eitherMatch (eitherInr value)` iota branching against congruence
in the discarded left branch. -/
def iotaEitherMatchInrLeftBranchCong {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons rightBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons steppedLeftBranch (.childCons rightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInr
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_eitherInr () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          ((.childCons rightBranch .childNil) :
            RawTermChildren [0] scope)
          leftStep))

/-- Root `eitherMatch (eitherInr value)` iota branching against congruence
in the selected right branch. -/
def iotaEitherMatchInrRightBranchCong {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons leftBranch (.childCons rightBranch .childNil)))
  leftReduct :=
    .mkGen .gen_app ()
      (.childCons rightBranch (.childCons value .childNil))
  rightReduct :=
    .mkGen .gen_eitherMatch ()
      (.childCons
        (.mkGen .gen_eitherInr () (.childCons value .childNil))
        (.childCons leftBranch (.childCons steppedRightBranch .childNil)))
  leftStep := Step.iotaEitherMatchInr
  rightStep :=
    Step.cong .gen_eitherMatch ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0, 0])
        ((.mkGen .gen_eitherInr () (.childCons value .childNil)) :
          RawTerm scope)
        (StepChildren.there
          (parentScope := scope) (headShift := 0) (restShifts := [0])
          leftBranch
          (StepChildren.here
            (parentScope := scope) (headShift := 0) (restShifts := [])
            (.childNil : RawTermChildren [] scope)
            rightStep)))

/-- Root `idJ refl` iota branching against congruence in the selected
base-case child. -/
def iotaIdJBaseCaseCong {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idJ ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct :=
    .mkGen .gen_idJ ()
      (.childCons
        steppedBaseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftStep := Step.iotaIdJRefl
  rightStep :=
    Step.cong .gen_idJ ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0])
        ((.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil) : RawTermChildren [0] scope)
        baseStep)

/-- Root `idJ refl` iota branching against congruence inside the discarded
refl witness child. -/
def iotaIdJWitnessCong {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idJ ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct :=
    .mkGen .gen_idJ ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons steppedRawWitness .childNil))
          .childNil))
  leftStep := Step.iotaIdJRefl
  rightStep :=
    Step.cong .gen_idJ ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0])
        baseCase
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [])
          (.childNil : RawTermChildren [] scope)
          (Step.cong .gen_refl ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              witnessStep))))

/-- Root `idStrictRec refl` iota branching against congruence in the selected
base-case child. -/
def iotaIdStrictRecBaseCaseCong {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idStrictRec ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct :=
    .mkGen .gen_idStrictRec ()
      (.childCons
        steppedBaseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftStep := Step.iotaIdStrictRecRefl
  rightStep :=
    Step.cong .gen_idStrictRec ()
      (StepChildren.here
        (parentScope := scope) (headShift := 0) (restShifts := [0])
        ((.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil) : RawTermChildren [0] scope)
        baseStep)

/-- Root `idStrictRec refl` iota branching against congruence inside the
discarded refl witness child. -/
def iotaIdStrictRecWitnessCong {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    LocalStepBranching (scope := scope) where
  source :=
    .mkGen .gen_idStrictRec ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons rawWitness .childNil))
          .childNil))
  leftReduct := baseCase
  rightReduct :=
    .mkGen .gen_idStrictRec ()
      (.childCons
        baseCase
        (.childCons
          (.mkGen .gen_refl () (.childCons steppedRawWitness .childNil))
          .childNil))
  leftStep := Step.iotaIdStrictRecRefl
  rightStep :=
    Step.cong .gen_idStrictRec ()
      (StepChildren.there
        (parentScope := scope) (headShift := 0) (restShifts := [0])
        baseCase
        (StepChildren.here
          (parentScope := scope) (headShift := 0) (restShifts := [])
          (.childNil : RawTermChildren [] scope)
          (Step.cong .gen_refl ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [])
              (.childNil : RawTermChildren [] scope)
              witnessStep))))

end LocalStepBranching

/-- A concrete local diamond filler for one local one-step branching.

This is the proof-relevant version of the M6 "diamond filler template":
the join target is an actual raw term, and both sides are actual
`StepStar` chains into that join. -/
structure LocalDiamond {scope : Nat}
    (branching : LocalStepBranching (scope := scope)) where
  commonReduct : RawTerm scope
  leftChain : StepStar branching.leftReduct commonReduct
  rightChain : StepStar branching.rightReduct commonReduct

namespace LocalDiamond

/-- Same-reduct filler template.

When both one-step reductions produce the same reduct, the local
diamond closes immediately by reflexivity on both sides.  This covers
the same-root/same-rule branchings after the critical-pair dispatcher
has established that the two reducts are definitionally the same. -/
def sameReduct {scope : Nat} {source commonReduct : RawTerm scope}
    (leftStep : Step source commonReduct)
    (rightStep : Step source commonReduct) :
    LocalDiamond
      { source := source
        leftReduct := commonReduct
        rightReduct := commonReduct
        leftStep := leftStep
        rightStep := rightStep } where
  commonReduct := commonReduct
  leftChain := StepStar.refl commonReduct
  rightChain := StepStar.refl commonReduct

/-- Same-reduct filler from a propositional equality between the two
one-step reducts.

This is the form the critical-pair dispatcher will usually produce:
after case analysis it proves that the two reduct expressions are equal,
then this template transports the right chain and closes the diamond by
reflexivity. -/
def sameReductOfEq {scope : Nat}
    (branching : LocalStepBranching (scope := scope))
    (reductsEqual : branching.leftReduct = branching.rightReduct) :
    LocalDiamond branching := by
  cases branching
  cases reductsEqual
  exact sameReduct _ _

/-- Concrete beta/beta local diamond.

This is the first root/root critical-pair filler template: both sides
are the same beta contraction, so the join is the beta reduct itself. -/
def betaBeta {scope : Nat} (body : RawTerm (scope + 1))
    (arg : RawTerm scope) :
    LocalDiamond (LocalStepBranching.betaBeta body arg) :=
  sameReduct Step.beta Step.beta

/-- Concrete bool-true iota same-root local diamond. -/
def iotaBoolTrueSameRoot {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaBoolTrueSameRoot thenBranch elseBranch) :=
  sameReduct Step.iotaBoolTrue Step.iotaBoolTrue

/-- Concrete bool-false iota same-root local diamond. -/
def iotaBoolFalseSameRoot {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaBoolFalseSameRoot thenBranch elseBranch) :=
  sameReduct Step.iotaBoolFalse Step.iotaBoolFalse

/-- Concrete first-projection iota same-root local diamond. -/
def iotaFstPairSameRoot {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaFstPairSameRoot firstValue secondValue) :=
  sameReduct Step.iotaFstPair Step.iotaFstPair

/-- Concrete second-projection iota same-root local diamond. -/
def iotaSndPairSameRoot {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaSndPairSameRoot firstValue secondValue) :=
  sameReduct Step.iotaSndPair Step.iotaSndPair

/-- Concrete `natElim` zero-case iota same-root local diamond. -/
def iotaNatElimZeroSameRoot {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimZeroSameRoot zeroBranch succBranch) :=
  sameReduct Step.iotaNatElimZero Step.iotaNatElimZero

/-- Concrete `natRec` zero-case iota same-root local diamond. -/
def iotaNatRecZeroSameRoot {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecZeroSameRoot zeroBranch succBranch) :=
  sameReduct Step.iotaNatRecZero Step.iotaNatRecZero

/-- Concrete `listElim` nil-case iota same-root local diamond. -/
def iotaListElimNilSameRoot {scope : Nat}
    (nilBranch consBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaListElimNilSameRoot nilBranch consBranch) :=
  sameReduct Step.iotaListElimNil Step.iotaListElimNil

/-- Concrete `optionMatch` none-case iota same-root local diamond. -/
def iotaOptionMatchNoneSameRoot {scope : Nat}
    (noneBranch someBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchNoneSameRoot noneBranch someBranch) :=
  sameReduct Step.iotaOptionMatchNone Step.iotaOptionMatchNone

/-- Concrete `idJ` refl-case iota same-root local diamond. -/
def iotaIdJReflSameRoot {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaIdJReflSameRoot baseCase rawWitness) :=
  sameReduct Step.iotaIdJRefl Step.iotaIdJRefl

/-- Concrete `idStrictRec` refl-case iota same-root local diamond. -/
def iotaIdStrictRecReflSameRoot {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaIdStrictRecReflSameRoot baseCase rawWitness) :=
  sameReduct Step.iotaIdStrictRecRefl Step.iotaIdStrictRecRefl

/-- Concrete `optionMatch` some-case iota same-root local diamond. -/
def iotaOptionMatchSomeSameRoot {scope : Nat}
    (value noneBranch someBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchSomeSameRoot
        value noneBranch someBranch) :=
  sameReduct Step.iotaOptionMatchSome Step.iotaOptionMatchSome

/-- Concrete `eitherMatch` inl-case iota same-root local diamond. -/
def iotaEitherMatchInlSameRoot {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInlSameRoot
        value leftBranch rightBranch) :=
  sameReduct Step.iotaEitherMatchInl Step.iotaEitherMatchInl

/-- Concrete `eitherMatch` inr-case iota same-root local diamond. -/
def iotaEitherMatchInrSameRoot {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInrSameRoot
        value leftBranch rightBranch) :=
  sameReduct Step.iotaEitherMatchInr Step.iotaEitherMatchInr

/-- Concrete `natElim` succ-case iota same-root local diamond. -/
def iotaNatElimSuccSameRoot {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimSuccSameRoot
        predecessor zeroBranch succBranch) :=
  sameReduct Step.iotaNatElimSucc Step.iotaNatElimSucc

/-- Concrete `natRec` succ-case iota same-root local diamond. -/
def iotaNatRecSuccSameRoot {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecSuccSameRoot
        predecessor zeroBranch succBranch) :=
  sameReduct Step.iotaNatRecSucc Step.iotaNatRecSucc

/-- Concrete `listElim` cons-case iota same-root local diamond. -/
def iotaListElimConsSameRoot {scope : Nat}
    (headValue tailValue nilBranch consBranch : RawTerm scope) :
    LocalDiamond
      (LocalStepBranching.iotaListElimConsSameRoot
        headValue tailValue nilBranch consBranch) :=
  sameReduct Step.iotaListElimCons Step.iotaListElimCons

/-- Root `boolTrue` iota against congruence in the selected then-branch. -/
def iotaBoolTrueThenCong {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    LocalDiamond
      (LocalStepBranching.iotaBoolTrueThenCong
        (thenBranch := thenBranch)
        (steppedThenBranch := steppedThenBranch)
        (elseBranch := elseBranch)
        thenStep) := by
  dsimp [LocalStepBranching.iotaBoolTrueThenCong]
  exact
    { commonReduct := steppedThenBranch
      leftChain := StepStar.single thenStep
      rightChain := StepStar.single Step.iotaBoolTrue }

/-- Root `boolTrue` iota against congruence in the discarded else-branch. -/
def iotaBoolTrueElseCong {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    LocalDiamond
      (LocalStepBranching.iotaBoolTrueElseCong
        (thenBranch := thenBranch)
        (elseBranch := elseBranch)
        (steppedElseBranch := steppedElseBranch)
        elseStep) := by
  dsimp [LocalStepBranching.iotaBoolTrueElseCong]
  exact
    { commonReduct := thenBranch
      leftChain := StepStar.refl thenBranch
      rightChain := StepStar.single Step.iotaBoolTrue }

/-- Root `boolFalse` iota against congruence in the discarded then-branch. -/
def iotaBoolFalseThenCong {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    LocalDiamond
      (LocalStepBranching.iotaBoolFalseThenCong
        (thenBranch := thenBranch)
        (steppedThenBranch := steppedThenBranch)
        (elseBranch := elseBranch)
        thenStep) := by
  dsimp [LocalStepBranching.iotaBoolFalseThenCong]
  exact
    { commonReduct := elseBranch
      leftChain := StepStar.refl elseBranch
      rightChain := StepStar.single Step.iotaBoolFalse }

/-- Root `boolFalse` iota against congruence in the selected else-branch. -/
def iotaBoolFalseElseCong {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    LocalDiamond
      (LocalStepBranching.iotaBoolFalseElseCong
        (thenBranch := thenBranch)
        (elseBranch := elseBranch)
        (steppedElseBranch := steppedElseBranch)
        elseStep) := by
  dsimp [LocalStepBranching.iotaBoolFalseElseCong]
  exact
    { commonReduct := steppedElseBranch
      leftChain := StepStar.single elseStep
      rightChain := StepStar.single Step.iotaBoolFalse }

/-- Root `fst` iota against congruence in the selected first component. -/
def iotaFstPairFirstCong {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    LocalDiamond
      (LocalStepBranching.iotaFstPairFirstCong
        (firstValue := firstValue)
        (steppedFirstValue := steppedFirstValue)
        (secondValue := secondValue)
        firstStep) := by
  dsimp [LocalStepBranching.iotaFstPairFirstCong]
  exact
    { commonReduct := steppedFirstValue
      leftChain := StepStar.single firstStep
      rightChain := StepStar.single Step.iotaFstPair }

/-- Root `fst` iota against congruence in the discarded second component. -/
def iotaFstPairSecondCong {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    LocalDiamond
      (LocalStepBranching.iotaFstPairSecondCong
        (firstValue := firstValue)
        (secondValue := secondValue)
        (steppedSecondValue := steppedSecondValue)
        secondStep) := by
  dsimp [LocalStepBranching.iotaFstPairSecondCong]
  exact
    { commonReduct := firstValue
      leftChain := StepStar.refl firstValue
      rightChain := StepStar.single Step.iotaFstPair }

/-- Root `snd` iota against congruence in the discarded first component. -/
def iotaSndPairFirstCong {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    LocalDiamond
      (LocalStepBranching.iotaSndPairFirstCong
        (firstValue := firstValue)
        (steppedFirstValue := steppedFirstValue)
        (secondValue := secondValue)
        firstStep) := by
  dsimp [LocalStepBranching.iotaSndPairFirstCong]
  exact
    { commonReduct := secondValue
      leftChain := StepStar.refl secondValue
      rightChain := StepStar.single Step.iotaSndPair }

/-- Root `snd` iota against congruence in the selected second component. -/
def iotaSndPairSecondCong {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    LocalDiamond
      (LocalStepBranching.iotaSndPairSecondCong
        (firstValue := firstValue)
        (secondValue := secondValue)
        (steppedSecondValue := steppedSecondValue)
        secondStep) := by
  dsimp [LocalStepBranching.iotaSndPairSecondCong]
  exact
    { commonReduct := steppedSecondValue
      leftChain := StepStar.single secondStep
      rightChain := StepStar.single Step.iotaSndPair }

/-- Root `natElim natZero` iota against congruence in the selected
zero-branch. -/
def iotaNatElimZeroBranchCong {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimZeroBranchCong
        (zeroBranch := zeroBranch)
        (steppedZeroBranch := steppedZeroBranch)
        (succBranch := succBranch)
        zeroStep) := by
  dsimp [LocalStepBranching.iotaNatElimZeroBranchCong]
  exact
    { commonReduct := steppedZeroBranch
      leftChain := StepStar.single zeroStep
      rightChain := StepStar.single Step.iotaNatElimZero }

/-- Root `natElim natZero` iota against congruence in the discarded
successor branch. -/
def iotaNatElimSuccBranchCong {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimSuccBranchCong
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        (steppedSuccBranch := steppedSuccBranch)
        succStep) := by
  dsimp [LocalStepBranching.iotaNatElimSuccBranchCong]
  exact
    { commonReduct := zeroBranch
      leftChain := StepStar.refl zeroBranch
      rightChain := StepStar.single Step.iotaNatElimZero }

/-- Root `natRec natZero` iota against congruence in the selected
zero-branch. -/
def iotaNatRecZeroBranchCong {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecZeroBranchCong
        (zeroBranch := zeroBranch)
        (steppedZeroBranch := steppedZeroBranch)
        (succBranch := succBranch)
        zeroStep) := by
  dsimp [LocalStepBranching.iotaNatRecZeroBranchCong]
  exact
    { commonReduct := steppedZeroBranch
      leftChain := StepStar.single zeroStep
      rightChain := StepStar.single Step.iotaNatRecZero }

/-- Root `natRec natZero` iota against congruence in the discarded
successor branch. -/
def iotaNatRecSuccBranchCong {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecSuccBranchCong
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        (steppedSuccBranch := steppedSuccBranch)
        succStep) := by
  dsimp [LocalStepBranching.iotaNatRecSuccBranchCong]
  exact
    { commonReduct := zeroBranch
      leftChain := StepStar.refl zeroBranch
      rightChain := StepStar.single Step.iotaNatRecZero }

/-- Root `natElim (natSucc predecessor)` iota against congruence in the
zero-branch.  The join reduces the recursive call's zero-branch after the
root iota fires. -/
def iotaNatElimSuccZeroBranchCong {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimSuccZeroBranchCong
        (predecessor := predecessor)
        (zeroBranch := zeroBranch)
        (steppedZeroBranch := steppedZeroBranch)
        (succBranch := succBranch)
        zeroStep) := by
  dsimp [LocalStepBranching.iotaNatElimSuccZeroBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natElim ()
                (.childCons predecessor
                  (.childCons steppedZeroBranch
                    (.childCons succBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil))) :
                RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                (Step.cong .gen_natElim ()
                  (StepChildren.there
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [0, 0])
                    predecessor
                    (StepChildren.here
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0])
                      ((.childCons succBranch .childNil) :
                        RawTermChildren [0] scope)
                      zeroStep))))))
      rightChain := StepStar.single Step.iotaNatElimSucc }

/-- Root `natElim (natSucc predecessor)` iota against congruence in the
successor branch.  The successor-branch step must be replayed in the
app-chain head and in the recursive call. -/
def iotaNatElimSuccSuccBranchCong {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimSuccSuccBranchCong
        (predecessor := predecessor)
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        (steppedSuccBranch := steppedSuccBranch)
        succStep) := by
  dsimp [LocalStepBranching.iotaNatElimSuccSuccBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons steppedSuccBranch
                (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natElim ()
                (.childCons predecessor
                  (.childCons zeroBranch
                    (.childCons steppedSuccBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_natElim ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons predecessor .childNil) :
                    RawTermChildren [0] scope)
                  succStep))))
          (StepStar.single
            (Step.cong .gen_app ()
              (StepChildren.there
                (parentScope := scope) (headShift := 0) (restShifts := [0])
                ((.mkGen .gen_app ()
                  (.childCons steppedSuccBranch
                    (.childCons predecessor .childNil))) :
                  RawTerm scope)
                (StepChildren.here
                  (parentScope := scope) (headShift := 0) (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  (Step.cong .gen_natElim ()
                    (StepChildren.there
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0, 0])
                      predecessor
                      (StepChildren.there
                        (parentScope := scope) (headShift := 0)
                        (restShifts := [0])
                        zeroBranch
                        (StepChildren.here
                          (parentScope := scope) (headShift := 0)
                          (restShifts := [])
                          (.childNil : RawTermChildren [] scope)
                          succStep))))))))
      rightChain := StepStar.single Step.iotaNatElimSucc }

/-- Root `natRec (natSucc predecessor)` iota against congruence in the
zero-branch. -/
def iotaNatRecSuccZeroBranchCong {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecSuccZeroBranchCong
        (predecessor := predecessor)
        (zeroBranch := zeroBranch)
        (steppedZeroBranch := steppedZeroBranch)
        (succBranch := succBranch)
        zeroStep) := by
  dsimp [LocalStepBranching.iotaNatRecSuccZeroBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natRec ()
                (.childCons predecessor
                  (.childCons steppedZeroBranch
                    (.childCons succBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil))) :
                RawTerm scope)
              (StepChildren.here
                (parentScope := scope) (headShift := 0) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                (Step.cong .gen_natRec ()
                  (StepChildren.there
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [0, 0])
                    predecessor
                    (StepChildren.here
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0])
                      ((.childCons succBranch .childNil) :
                        RawTermChildren [0] scope)
                      zeroStep))))))
      rightChain := StepStar.single Step.iotaNatRecSucc }

/-- Root `natRec (natSucc predecessor)` iota against congruence in the
successor branch. -/
def iotaNatRecSuccSuccBranchCong {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecSuccSuccBranchCong
        (predecessor := predecessor)
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        (steppedSuccBranch := steppedSuccBranch)
        succStep) := by
  dsimp [LocalStepBranching.iotaNatRecSuccSuccBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons steppedSuccBranch
                (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natRec ()
                (.childCons predecessor
                  (.childCons zeroBranch
                    (.childCons steppedSuccBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_natRec ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_app ()
                (StepChildren.here
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [0])
                  ((.childCons predecessor .childNil) :
                    RawTermChildren [0] scope)
                  succStep))))
          (StepStar.single
            (Step.cong .gen_app ()
              (StepChildren.there
                (parentScope := scope) (headShift := 0) (restShifts := [0])
                ((.mkGen .gen_app ()
                  (.childCons steppedSuccBranch
                    (.childCons predecessor .childNil))) :
                  RawTerm scope)
                (StepChildren.here
                  (parentScope := scope) (headShift := 0) (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  (Step.cong .gen_natRec ()
                    (StepChildren.there
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0, 0])
                      predecessor
                      (StepChildren.there
                        (parentScope := scope) (headShift := 0)
                        (restShifts := [0])
                        zeroBranch
                        (StepChildren.here
                          (parentScope := scope) (headShift := 0)
                          (restShifts := [])
                          (.childNil : RawTermChildren [] scope)
                          succStep))))))))
      rightChain := StepStar.single Step.iotaNatRecSucc }

/-- Root `natElim (natSucc predecessor)` iota against congruence inside the
`natSucc` predecessor.  The join uses two steps after the root iota: one in
the successor-branch app argument, then one in the recursive call. -/
def iotaNatElimSuccPredecessorCong {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    LocalDiamond
      (LocalStepBranching.iotaNatElimSuccPredecessorCong
        (predecessor := predecessor)
        (steppedPredecessor := steppedPredecessor)
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        predecessorStep) := by
  dsimp [LocalStepBranching.iotaNatElimSuccPredecessorCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch
                (.childCons steppedPredecessor .childNil)))
            (.childCons
              (.mkGen .gen_natElim ()
                (.childCons steppedPredecessor
                  (.childCons zeroBranch
                    (.childCons succBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_natElim ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_app ()
                (StepChildren.there
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [0])
                  succBranch
                  (StepChildren.here
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [])
                    (.childNil : RawTermChildren [] scope)
                    predecessorStep)))))
          (StepStar.single
            (Step.cong .gen_app ()
              (StepChildren.there
                (parentScope := scope) (headShift := 0) (restShifts := [0])
                ((.mkGen .gen_app ()
                  (.childCons succBranch
                    (.childCons steppedPredecessor .childNil))) :
                  RawTerm scope)
                (StepChildren.here
                  (parentScope := scope) (headShift := 0) (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  (Step.cong .gen_natElim ()
                    (StepChildren.here
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0, 0])
                      ((.childCons zeroBranch
                        (.childCons succBranch .childNil)) :
                        RawTermChildren [0, 0] scope)
                      predecessorStep))))))
      rightChain := StepStar.single Step.iotaNatElimSucc }

/-- Root `natRec (natSucc predecessor)` iota against congruence inside the
`natSucc` predecessor. -/
def iotaNatRecSuccPredecessorCong {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    LocalDiamond
      (LocalStepBranching.iotaNatRecSuccPredecessorCong
        (predecessor := predecessor)
        (steppedPredecessor := steppedPredecessor)
        (zeroBranch := zeroBranch)
        (succBranch := succBranch)
        predecessorStep) := by
  dsimp [LocalStepBranching.iotaNatRecSuccPredecessorCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch
                (.childCons steppedPredecessor .childNil)))
            (.childCons
              (.mkGen .gen_natRec ()
                (.childCons steppedPredecessor
                  (.childCons zeroBranch
                    (.childCons succBranch .childNil))))
              .childNil))
      leftChain :=
        StepStar.trans
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons
                (.mkGen .gen_natRec ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil) :
                RawTermChildren [0] scope)
              (Step.cong .gen_app ()
                (StepChildren.there
                  (parentScope := scope) (headShift := 0)
                  (restShifts := [0])
                  succBranch
                  (StepChildren.here
                    (parentScope := scope) (headShift := 0)
                    (restShifts := [])
                    (.childNil : RawTermChildren [] scope)
                    predecessorStep)))))
          (StepStar.single
            (Step.cong .gen_app ()
              (StepChildren.there
                (parentScope := scope) (headShift := 0) (restShifts := [0])
                ((.mkGen .gen_app ()
                  (.childCons succBranch
                    (.childCons steppedPredecessor .childNil))) :
                  RawTerm scope)
                (StepChildren.here
                  (parentScope := scope) (headShift := 0) (restShifts := [])
                  (.childNil : RawTermChildren [] scope)
                  (Step.cong .gen_natRec ()
                    (StepChildren.here
                      (parentScope := scope) (headShift := 0)
                      (restShifts := [0, 0])
                      ((.childCons zeroBranch
                        (.childCons succBranch .childNil)) :
                        RawTermChildren [0, 0] scope)
                      predecessorStep))))))
      rightChain := StepStar.single Step.iotaNatRecSucc }

/-- Root `listElim listNil` iota against congruence in the selected
nil-branch. -/
def iotaListElimNilBranchCong {scope : Nat}
    {nilBranch steppedNilBranch consBranch : RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    LocalDiamond
      (LocalStepBranching.iotaListElimNilBranchCong
        (nilBranch := nilBranch)
        (steppedNilBranch := steppedNilBranch)
        (consBranch := consBranch)
        nilStep) := by
  dsimp [LocalStepBranching.iotaListElimNilBranchCong]
  exact
    { commonReduct := steppedNilBranch
      leftChain := StepStar.single nilStep
      rightChain := StepStar.single Step.iotaListElimNil }

/-- Root `listElim listNil` iota against congruence in the discarded
cons-branch. -/
def iotaListElimConsBranchCong {scope : Nat}
    {nilBranch consBranch steppedConsBranch : RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    LocalDiamond
      (LocalStepBranching.iotaListElimConsBranchCong
        (nilBranch := nilBranch)
        (consBranch := consBranch)
        (steppedConsBranch := steppedConsBranch)
        consStep) := by
  dsimp [LocalStepBranching.iotaListElimConsBranchCong]
  exact
    { commonReduct := nilBranch
      leftChain := StepStar.refl nilBranch
      rightChain := StepStar.single Step.iotaListElimNil }

/-- Root `optionMatch optionNone` iota against congruence in the
selected none-branch. -/
def iotaOptionMatchNoneBranchCong {scope : Nat}
    {noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchNoneBranchCong
        (noneBranch := noneBranch)
        (steppedNoneBranch := steppedNoneBranch)
        (someBranch := someBranch)
        noneStep) := by
  dsimp [LocalStepBranching.iotaOptionMatchNoneBranchCong]
  exact
    { commonReduct := steppedNoneBranch
      leftChain := StepStar.single noneStep
      rightChain := StepStar.single Step.iotaOptionMatchNone }

/-- Root `optionMatch optionNone` iota against congruence in the
discarded some-branch. -/
def iotaOptionMatchSomeBranchCong {scope : Nat}
    {noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchSomeBranchCong
        (noneBranch := noneBranch)
        (someBranch := someBranch)
        (steppedSomeBranch := steppedSomeBranch)
        someStep) := by
  dsimp [LocalStepBranching.iotaOptionMatchSomeBranchCong]
  exact
    { commonReduct := noneBranch
      leftChain := StepStar.refl noneBranch
      rightChain := StepStar.single Step.iotaOptionMatchNone }

/-- Root `optionMatch (optionSome value)` iota against congruence inside
the `optionSome` payload. -/
def iotaOptionMatchSomeValueCong {scope : Nat}
    {value steppedValue noneBranch someBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchSomeValueCong
        (value := value)
        (steppedValue := steppedValue)
        (noneBranch := noneBranch)
        (someBranch := someBranch)
        valueStep) := by
  dsimp [LocalStepBranching.iotaOptionMatchSomeValueCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons someBranch (.childCons steppedValue .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              someBranch
              (StepChildren.here
                (parentScope := scope) (headShift := 0) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                valueStep)))
      rightChain := StepStar.single Step.iotaOptionMatchSome }

/-- Root `optionMatch (optionSome value)` iota against congruence in the
discarded none-branch. -/
def iotaOptionMatchSomeNoneBranchCong {scope : Nat}
    {value noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchSomeNoneBranchCong
        (value := value)
        (noneBranch := noneBranch)
        (steppedNoneBranch := steppedNoneBranch)
        (someBranch := someBranch)
        noneStep) := by
  dsimp [LocalStepBranching.iotaOptionMatchSomeNoneBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons someBranch (.childCons value .childNil))
      leftChain :=
        StepStar.refl
          (.mkGen .gen_app ()
            (.childCons someBranch (.childCons value .childNil)))
      rightChain := StepStar.single Step.iotaOptionMatchSome }

/-- Root `optionMatch (optionSome value)` iota against congruence in the
selected some-branch. -/
def iotaOptionMatchSomeSomeBranchCong {scope : Nat}
    {value noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    LocalDiamond
      (LocalStepBranching.iotaOptionMatchSomeSomeBranchCong
        (value := value)
        (noneBranch := noneBranch)
        (someBranch := someBranch)
        (steppedSomeBranch := steppedSomeBranch)
        someStep) := by
  dsimp [LocalStepBranching.iotaOptionMatchSomeSomeBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons steppedSomeBranch (.childCons value .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons value .childNil) : RawTermChildren [0] scope)
              someStep))
      rightChain := StepStar.single Step.iotaOptionMatchSome }

/-- Root `eitherMatch (eitherInl value)` iota against congruence inside
the `eitherInl` payload. -/
def iotaEitherMatchInlValueCong {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInlValueCong
        (value := value)
        (steppedValue := steppedValue)
        (leftBranch := leftBranch)
        (rightBranch := rightBranch)
        valueStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInlValueCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons leftBranch (.childCons steppedValue .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              leftBranch
              (StepChildren.here
                (parentScope := scope) (headShift := 0) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                valueStep)))
      rightChain := StepStar.single Step.iotaEitherMatchInl }

/-- Root `eitherMatch (eitherInl value)` iota against congruence in the
selected left branch. -/
def iotaEitherMatchInlLeftBranchCong {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInlLeftBranchCong
        (value := value)
        (leftBranch := leftBranch)
        (steppedLeftBranch := steppedLeftBranch)
        (rightBranch := rightBranch)
        leftStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInlLeftBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons steppedLeftBranch (.childCons value .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons value .childNil) : RawTermChildren [0] scope)
              leftStep))
      rightChain := StepStar.single Step.iotaEitherMatchInl }

/-- Root `eitherMatch (eitherInl value)` iota against congruence in the
discarded right branch. -/
def iotaEitherMatchInlRightBranchCong {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInlRightBranchCong
        (value := value)
        (leftBranch := leftBranch)
        (rightBranch := rightBranch)
        (steppedRightBranch := steppedRightBranch)
        rightStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInlRightBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons leftBranch (.childCons value .childNil))
      leftChain :=
        StepStar.refl
          (.mkGen .gen_app ()
            (.childCons leftBranch (.childCons value .childNil)))
      rightChain := StepStar.single Step.iotaEitherMatchInl }

/-- Root `eitherMatch (eitherInr value)` iota against congruence inside
the `eitherInr` payload. -/
def iotaEitherMatchInrValueCong {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInrValueCong
        (value := value)
        (steppedValue := steppedValue)
        (leftBranch := leftBranch)
        (rightBranch := rightBranch)
        valueStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInrValueCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons rightBranch (.childCons steppedValue .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.there
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              rightBranch
              (StepChildren.here
                (parentScope := scope) (headShift := 0) (restShifts := [])
                (.childNil : RawTermChildren [] scope)
                valueStep)))
      rightChain := StepStar.single Step.iotaEitherMatchInr }

/-- Root `eitherMatch (eitherInr value)` iota against congruence in the
discarded left branch. -/
def iotaEitherMatchInrLeftBranchCong {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInrLeftBranchCong
        (value := value)
        (leftBranch := leftBranch)
        (steppedLeftBranch := steppedLeftBranch)
        (rightBranch := rightBranch)
        leftStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInrLeftBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons rightBranch (.childCons value .childNil))
      leftChain :=
        StepStar.refl
          (.mkGen .gen_app ()
            (.childCons rightBranch (.childCons value .childNil)))
      rightChain := StepStar.single Step.iotaEitherMatchInr }

/-- Root `eitherMatch (eitherInr value)` iota against congruence in the
selected right branch. -/
def iotaEitherMatchInrRightBranchCong {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    LocalDiamond
      (LocalStepBranching.iotaEitherMatchInrRightBranchCong
        (value := value)
        (leftBranch := leftBranch)
        (rightBranch := rightBranch)
        (steppedRightBranch := steppedRightBranch)
        rightStep) := by
  dsimp [LocalStepBranching.iotaEitherMatchInrRightBranchCong]
  exact
    { commonReduct :=
        .mkGen .gen_app ()
          (.childCons steppedRightBranch (.childCons value .childNil))
      leftChain :=
        StepStar.single
          (Step.cong .gen_app ()
            (StepChildren.here
              (parentScope := scope) (headShift := 0) (restShifts := [0])
              ((.childCons value .childNil) : RawTermChildren [0] scope)
              rightStep))
      rightChain := StepStar.single Step.iotaEitherMatchInr }

/-- Root `idJ refl` iota against congruence in the selected base case. -/
def iotaIdJBaseCaseCong {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    LocalDiamond
      (LocalStepBranching.iotaIdJBaseCaseCong
        (baseCase := baseCase)
        (steppedBaseCase := steppedBaseCase)
        (rawWitness := rawWitness)
        baseStep) := by
  dsimp [LocalStepBranching.iotaIdJBaseCaseCong]
  exact
    { commonReduct := steppedBaseCase
      leftChain := StepStar.single baseStep
      rightChain := StepStar.single Step.iotaIdJRefl }

/-- Root `idJ refl` iota against congruence inside the discarded refl
witness. -/
def iotaIdJWitnessCong {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    LocalDiamond
      (LocalStepBranching.iotaIdJWitnessCong
        (baseCase := baseCase)
        (rawWitness := rawWitness)
        (steppedRawWitness := steppedRawWitness)
        witnessStep) := by
  dsimp [LocalStepBranching.iotaIdJWitnessCong]
  exact
    { commonReduct := baseCase
      leftChain := StepStar.refl baseCase
      rightChain := StepStar.single Step.iotaIdJRefl }

/-- Root `idStrictRec refl` iota against congruence in the selected base
case. -/
def iotaIdStrictRecBaseCaseCong {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    LocalDiamond
      (LocalStepBranching.iotaIdStrictRecBaseCaseCong
        (baseCase := baseCase)
        (steppedBaseCase := steppedBaseCase)
        (rawWitness := rawWitness)
        baseStep) := by
  dsimp [LocalStepBranching.iotaIdStrictRecBaseCaseCong]
  exact
    { commonReduct := steppedBaseCase
      leftChain := StepStar.single baseStep
      rightChain := StepStar.single Step.iotaIdStrictRecRefl }

/-- Root `idStrictRec refl` iota against congruence inside the discarded
refl witness. -/
def iotaIdStrictRecWitnessCong {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    LocalDiamond
      (LocalStepBranching.iotaIdStrictRecWitnessCong
        (baseCase := baseCase)
        (rawWitness := rawWitness)
        (steppedRawWitness := steppedRawWitness)
        witnessStep) := by
  dsimp [LocalStepBranching.iotaIdStrictRecWitnessCong]
  exact
    { commonReduct := baseCase
      leftChain := StepStar.refl baseCase
      rightChain := StepStar.single Step.iotaIdStrictRecRefl }

end LocalDiamond

end LeanFX2.Foundation.PolyCell.Core
