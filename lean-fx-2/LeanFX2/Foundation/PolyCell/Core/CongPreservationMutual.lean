import LeanFX2.Foundation.PolyCell.Core.SubstPreservationMutual
import LeanFX2.Foundation.PolyCell.Core.Step

/-! # Foundation/PolyCell/Core/CongPreservationMutual
   — spine-level core for uniform congruence preservation

This file starts task #252 / M3.  The final endpoint is
`HasCertifiedCellDim0.preservedByCong`, the 18th structural SR arm.

This first layer avoids the Step/StepChildren circularity by
parameterizing the spine recursion over a sort-preserving cell-level
step preserver.  The recursive work over `StepChildren` is real and
generic: one `here` arm rebuilds the stepped head, and one `there`
arm rebuilds the unchanged head plus recursively-preserved tail.

The remaining M3 layer instantiates the parameter with the mutual
`Step` dispatcher (`beta`, `cong`, and the 16 iotas).
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Sort-preserving dim-0 cell preservation for one `Step`.

This is the exact-strength callback the spine congruence recursion
needs.  `HasCertifiedCellDim0` is sort-existential, which is too weak
for rebuilding a `CertifiedTermSpine`; the head position has a fixed
`ChildSpec.cellSort`, so the callback keeps the same sort index. -/
def StepCellPreserver (profile : PolyProfile) : Type :=
  {scope : Nat} → {sort : CellSort} →
  {source target : RawTerm scope} →
  PolyCell profile sort 0 scope CellBoundary.trivial
    (.termBase source) →
  Step source target →
  PolyCell profile sort 0 scope CellBoundary.trivial
    (.termBase target)

/-- Prop-packaged exact-sort dim-0 preservation for one `Step`.

This is the instantiable form for the final `Step` / `StepChildren`
mutual proof.  `Step` lives in `Prop`, so Lean should not be asked to
eliminate an arbitrary `Step` proof into the `Type` returned by
`StepCellPreserver`.  Instead the target cell is carried under an
existential in `Prop`, which is strong enough for the final
`HasCertifiedCellDim0` endpoint and for rebuilding spines inside a
Prop-valued proof. -/
def StepCellPreserverWitness (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {sort : CellSort}
    {source target : RawTerm scope},
    PolyCell profile sort 0 scope CellBoundary.trivial
      (.termBase source) →
    Step source target →
    ∃ _targetCell :
      PolyCell profile sort 0 scope CellBoundary.trivial
        (.termBase target),
      True

/-- Prop-packaged preservation of a certified child spine across a
`StepChildren` witness, assuming a sort-preserving preserver for the
single child step in the `here` case.

The `allChildrenDim0` hypothesis is the same profile invariant used by
the rename/subst mutual blocks: it collapses each child boundary to
`CellBoundary.trivial`, allowing the stepped head cell to be rebuilt by
`CertifiedTermSpine.consStep_dim0Trivial`.

Why existential-in-`Prop`, not a direct Type-valued function?
`StepChildren` itself is a `Prop`, and Lean correctly forbids eliminating
proofs into `Type`.  The final SR-cong endpoint is
`HasCertifiedCellDim0`, also a `Prop`, so this existential package is the
right elimination boundary. -/
theorem CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserver
    {profile : PolyProfile} {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (stepPreserver : StepCellPreserver profile)
    (childStep : StepChildren children children') :
    ∀ {childSpecs : List ChildSpec},
    (specShiftsMatch :
      childSpecs.map ChildSpec.scopeShift = binderShifts) →
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
    (sourceSpine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True := by
  refine StepChildren.rec
    (motive_1 := fun {_scope} _source _target _step => True)
    (motive_2 := fun {parentScope} {binderShifts} children children' _childStep =>
      ∀ {childSpecs : List ChildSpec},
      (specShiftsMatch :
        childSpecs.map ChildSpec.scopeShift = binderShifts) →
      (allChildrenDim0 :
        ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
      (sourceSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children) →
      ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ childStep
  all_goals try
    (intros
     exact True.intro)
  · intro _childParentScope _headShift _restShifts
      _headRaw _headRawAfter restRaws headStep _headStepMotive
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                  headDim0
                  (stepPreserver
                    (scope := _childParentScope + headSpec.scopeShift)
                    headCellDim0
                    headStep)
                  restSpine,
              True.intro⟩
  · intro _childParentScope _headShift _restShifts
      headRaw _restRaws _restRawsAfter restStep preservedRest
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let restChildrenDim0 :
                ∀ childSpec ∈ restSpecs, childSpec.cellDimension = 0 :=
              fun childSpec childSpecMem =>
                allChildrenDim0 childSpec
                  (List.mem_cons_of_mem headSpec childSpecMem)
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            obtain ⟨preservedRestSpine, _⟩ :=
              preservedRest
                (childSpecs := restSpecs)
                restShiftsEq
                restChildrenDim0
                restSpine
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                headDim0
                headCellDim0
                preservedRestSpine,
              True.intro⟩

/-- Parent-level congruence preservation, parameterized by the exact
cell-level step preserver used for the stepped child.

This packages the generic spine recursion back into
`HasCertifiedCellDim0` for the parent generator.  It is the non-circular
outer wrapper for the final `Step.cong` arm. -/
theorem HasCertifiedCellDim0.preservedByCong_via_stepPreserver
    {profile : PolyProfile} {scope : Nat}
    (stepPreserver : StepCellPreserver profile)
    {generator : Generator} {payload : generator.payload scope}
    {children children' : RawTermChildren generator.binderShifts scope}
    (childStep : StepChildren children children')
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children') := by
  cases sourceCert with
  | intro _sourceSort sourceCell =>
      cases sourceCell with
      | gen admission payloadEvidence childSpine =>
          obtain ⟨targetSpine, _⟩ :=
            CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserver
              (profile := profile)
              (stepPreserver := stepPreserver)
              (childStep := childStep)
              (childSpecs := generator.childSpecs)
              (Generator.childSpecs_scopeShifts_eq_binderShifts generator)
              (Generator.childSpecs_cellDimension_zero generator)
              (sourceSpine := childSpine)
          exact .intro generator.cellSort
            (PolyCell.gen
              admission
              payloadEvidence
              targetSpine)

/-- Prop-packaged preservation of a certified child spine across a
`StepChildren` witness, using a Prop-valued exact-sort step preserver.

This is the version the final M3 mutual proof can instantiate.  It
has the same spine recursion as
`exists_preservedByChildStep_via_stepPreserver`, but the `here` arm
obtains its stepped head cell from a Prop existential rather than
from a Type-valued function out of `Step`. -/
theorem CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
    {profile : PolyProfile} {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (stepPreserver : StepCellPreserverWitness profile)
    (childStep : StepChildren children children') :
    ∀ {childSpecs : List ChildSpec},
    (specShiftsMatch :
      childSpecs.map ChildSpec.scopeShift = binderShifts) →
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
    (sourceSpine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True := by
  refine StepChildren.rec
    (motive_1 := fun {_scope} _source _target _step => True)
    (motive_2 := fun {parentScope} {binderShifts} children children' _childStep =>
      ∀ {childSpecs : List ChildSpec},
      (specShiftsMatch :
        childSpecs.map ChildSpec.scopeShift = binderShifts) →
      (allChildrenDim0 :
        ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
      (sourceSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children) →
      ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ childStep
  all_goals try
    (intros
     exact True.intro)
  · intro _childParentScope _headShift _restShifts
      _headRaw _headRawAfter restRaws headStep _headStepMotive
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            obtain ⟨preservedHeadCell, _⟩ :=
              stepPreserver
                (scope := _childParentScope + headSpec.scopeShift)
                headCellDim0
                headStep
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                  headDim0
                  preservedHeadCell
                  restSpine,
              True.intro⟩
  · intro _childParentScope _headShift _restShifts
      headRaw _restRaws _restRawsAfter restStep preservedRest
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let restChildrenDim0 :
                ∀ childSpec ∈ restSpecs, childSpec.cellDimension = 0 :=
              fun childSpec childSpecMem =>
                allChildrenDim0 childSpec
                  (List.mem_cons_of_mem headSpec childSpecMem)
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            obtain ⟨preservedRestSpine, _⟩ :=
              preservedRest
                (childSpecs := restSpecs)
                restShiftsEq
                restChildrenDim0
                restSpine
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                  headDim0
                  headCellDim0
                  preservedRestSpine,
              True.intro⟩

/-- Parent-level congruence preservation, parameterized by the
Prop-valued exact-sort step preserver used for the stepped child. -/
theorem HasCertifiedCellDim0.preservedByCong_via_stepPreserverWitness
    {profile : PolyProfile} {scope : Nat}
    (stepPreserver : StepCellPreserverWitness profile)
    {generator : Generator} {payload : generator.payload scope}
    {children children' : RawTermChildren generator.binderShifts scope}
    (childStep : StepChildren children children')
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children') := by
  cases sourceCert with
  | intro _sourceSort sourceCell =>
      cases sourceCell with
      | gen admission payloadEvidence childSpine =>
          obtain ⟨targetSpine, _⟩ :=
            CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
              (profile := profile)
              (stepPreserver := stepPreserver)
              (childStep := childStep)
              (childSpecs := generator.childSpecs)
              (Generator.childSpecs_scopeShifts_eq_binderShifts generator)
              (Generator.childSpecs_cellDimension_zero generator)
              (sourceSpine := childSpine)
          exact .intro generator.cellSort
            (PolyCell.gen
              admission
              payloadEvidence
              targetSpine)

end LeanFX2.Foundation.PolyCell.Core
