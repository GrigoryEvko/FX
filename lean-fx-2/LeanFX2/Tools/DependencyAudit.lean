import Lean

/-! # Tools/DependencyAudit — fail-fast dependency audit commands

This module provides the build-failing audit primitive for the
zero-axiom policy.  `#print axioms` is still useful during local proof
work, but it only logs; `#assert_no_axioms` throws an elaboration error
when any axiom appears in the transitive dependency tree.

The traversal includes Lean core declarations by default.  That means
`propext`, `Quot.sound`, and `Classical.choice` are real failures, not
hidden stdlib noise.
-/

namespace LeanFX2.Tools

open Lean Elab Command

/-- Dependency-count statistics for one constant's transitive closure. -/
structure DependencyStats where
  axiomNames : Array Name := #[]
  theoremCount : Nat := 0
  definitionCount : Nat := 0
  inductiveCount : Nat := 0
  constructorCount : Nat := 0
  recursorCount : Nat := 0
  quotientCount : Nat := 0
  opaqueCount : Nat := 0
  deriving Inhabited, Repr

/-- Total number of classified constants in a dependency report. -/
def DependencyStats.totalCount (stats : DependencyStats) : Nat :=
  stats.axiomNames.size +
  stats.theoremCount +
  stats.definitionCount +
  stats.inductiveCount +
  stats.constructorCount +
  stats.recursorCount +
  stats.quotientCount +
  stats.opaqueCount

/-- Render a comma-separated list of names for error messages. -/
def formatNameList (names : Array Name) : String :=
  String.join (names.toList.map toString |>.intersperse ", ")

/-- Pretty-print one declaration's dependency statistics. -/
def DependencyStats.format (stats : DependencyStats) (targetName : Name) : String :=
  let axiomLine :=
    if stats.axiomNames.isEmpty then
      "axioms:       0"
    else
      s!"axioms:       {stats.axiomNames.size} [{formatNameList stats.axiomNames}]"
  s!"Dependency audit for '{targetName}':\n" ++
  s!"  {axiomLine}\n" ++
  s!"  theorems:     {stats.theoremCount}\n" ++
  s!"  definitions:  {stats.definitionCount}\n" ++
  s!"  inductives:   {stats.inductiveCount}\n" ++
  s!"  constructors: {stats.constructorCount}\n" ++
  s!"  recursors:    {stats.recursorCount}\n" ++
  s!"  quotients:    {stats.quotientCount}\n" ++
  s!"  opaques:      {stats.opaqueCount}\n" ++
  s!"  TOTAL:        {stats.totalCount}"

/-- Names below these roots can be omitted for exploratory reports.
`#assert_no_axioms` does not use this filter. -/
def isStdlibPlumbingName (someName : Name) : Bool :=
  someName.isInternal ||
  someName.getRoot == `Lean ||
  someName.getRoot == `Init ||
  someName.getRoot == `Std ||
  someName.getRoot == `IO

/-- References in the type and optional value of one constant. -/
def constantReferences (constantInfo : ConstantInfo) : NameSet :=
  let typeReferences :=
    constantInfo.type.foldConsts NameSet.empty (fun referencedName references =>
      references.insert referencedName)
  match constantInfo.value? with
  | some valueExpr =>
      valueExpr.foldConsts typeReferences (fun referencedName references =>
        references.insert referencedName)
  | none => typeReferences

/-- Push references that have not been seen yet onto the work queue. -/
def enqueueUnvisitedReferences
    (includeStdlib : Bool)
    (visitedNames : NameSet)
    (queuedNames : Array Name)
    (references : List Name) :
    NameSet × Array Name :=
  references.foldl
    (init := (visitedNames, queuedNames))
    (fun (visitedNames, queuedNames) referencedName =>
      if !includeStdlib && isStdlibPlumbingName referencedName then
        (visitedNames, queuedNames)
      else if visitedNames.contains referencedName then
        (visitedNames, queuedNames)
      else
        (visitedNames.insert referencedName, queuedNames.push referencedName))

/-- Worklist dependency traversal with an explicit fuel bound. -/
def collectDependenciesWithFuel
    (environment : Environment)
    (includeStdlib : Bool)
    (fuel : Nat)
    (visitedNames : NameSet)
    (queuedNames : Array Name) :
    NameSet :=
  match fuel with
  | 0 => visitedNames
  | remainingFuel + 1 =>
      match queuedNames.back? with
      | none => visitedNames
      | some currentName =>
          let remainingQueue := queuedNames.pop
          match environment.find? currentName with
          | none =>
              collectDependenciesWithFuel environment includeStdlib
                remainingFuel visitedNames remainingQueue
          | some constantInfo =>
              let references := (constantReferences constantInfo).toList
              let (visitedNames, queuedNames) :=
                enqueueUnvisitedReferences includeStdlib visitedNames
                  remainingQueue references
              collectDependenciesWithFuel environment includeStdlib
                remainingFuel visitedNames queuedNames

/-- Collect all transitive constant dependencies from a target name. -/
def collectDependencies
    (environment : Environment)
    (targetName : Name)
    (includeStdlib : Bool := true)
    (fuel : Nat := 10000) :
    NameSet :=
  collectDependenciesWithFuel environment includeStdlib fuel
    (NameSet.empty.insert targetName) #[targetName]

/-- Add one constant-info tag to an existing dependency-stat record. -/
def DependencyStats.addConstant
    (stats : DependencyStats)
    (constantName : Name)
    (constantInfo : ConstantInfo) :
    DependencyStats :=
  match constantInfo with
  | .axiomInfo _ =>
      { stats with axiomNames := stats.axiomNames.push constantName }
  | .thmInfo _ =>
      { stats with theoremCount := stats.theoremCount + 1 }
  | .defnInfo _ =>
      { stats with definitionCount := stats.definitionCount + 1 }
  | .inductInfo _ =>
      { stats with inductiveCount := stats.inductiveCount + 1 }
  | .ctorInfo _ =>
      { stats with constructorCount := stats.constructorCount + 1 }
  | .recInfo _ =>
      { stats with recursorCount := stats.recursorCount + 1 }
  | .quotInfo _ =>
      { stats with quotientCount := stats.quotientCount + 1 }
  | .opaqueInfo _ =>
      { stats with opaqueCount := stats.opaqueCount + 1 }

/-- Compute dependency statistics for a named constant. -/
def computeStats
    (environment : Environment)
    (targetName : Name)
    (includeStdlib : Bool := true) :
    DependencyStats :=
  let dependencies := collectDependencies environment targetName includeStdlib
  dependencies.toList.foldl
    (init := ({} : DependencyStats))
    (fun stats dependencyName =>
      match environment.find? dependencyName with
      | none => stats
      | some constantInfo => stats.addConstant dependencyName constantInfo)

/-- Development report: dependency stats excluding stdlib plumbing. -/
elab "#audit_dependencies " targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  if !environment.contains targetName then
    throwError "unknown constant in dependency audit: {targetName}"
  let stats := computeStats environment targetName (includeStdlib := false)
  logInfo (stats.format targetName)

/-- Full development report: dependency stats including Lean core. -/
elab "#audit_dependencies_full " targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  if !environment.contains targetName then
    throwError "unknown constant in dependency audit: {targetName}"
  let stats := computeStats environment targetName (includeStdlib := true)
  logInfo (stats.format targetName)

/-- Build-failing zero-axiom gate for one declaration. -/
elab "#assert_no_axioms " targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  if !environment.contains targetName then
    throwError "unknown constant in axiom audit: {targetName}"
  let stats := computeStats environment targetName (includeStdlib := true)
  if stats.axiomNames.isEmpty then
    logInfo m!"axiom audit ok: {targetName}"
  else
    throwError
      "axiom audit failed for {targetName}: {stats.axiomNames.size} axiom(s): {formatNameList stats.axiomNames}"

end LeanFX2.Tools
