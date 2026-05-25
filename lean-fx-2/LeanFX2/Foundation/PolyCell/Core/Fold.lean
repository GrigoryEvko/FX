import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# PolyTerm Fold / Catamorphism

The fold is the structural catamorphism for `PolyTerm`.  It gives one recursion
scheme over the five syntax constructors.

A PolyTermAlgebra specifies what to DO at each constructor.
PolyTerm.fold applies the algebra recursively = one generic operation.

Future rename/substitution/evaluation/complete-development operations should
be expressible as folds once their concrete algebras and generator dispatch are
defined.  This file currently provides the fold itself plus identity, id-map,
and count examples.

Reference target: polycell.md §4 + C.6 task description.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

universe u

/-- A PolyTerm algebra: interpretation of each constructor into a target type.
This is the "recipe" that fold follows — one case per structural constructor. -/
structure PolyTermAlgebra (profile : PolyProfile) (target : CellDim → Type u) where
  /-- How to interpret an atom (dim-0 generator). -/
  interpretAtom : (cellId : CellId) → (payload : Nat) → target 0

  /-- How to interpret a cell (dim-(n+1) generator). -/
  interpretCell : {dimension : CellDim} →
    (ruleId : CellId) → target dimension → target dimension → target (dimension + 1)

  /-- How to interpret vertical composition. -/
  interpretCompV : {dimension : CellDim} →
    target (dimension + 1) → target (dimension + 1) → target (dimension + 1)

  /-- How to interpret horizontal composition. -/
  interpretCompH : {dimension : CellDim} →
    target (dimension + 1) → target (dimension + 1) → target (dimension + 1)

  /-- How to interpret identity cells. -/
  interpretIdentity : {dimension : CellDim} →
    target dimension → target (dimension + 1)

/-- Recursively apply a `PolyTermAlgebra` to a `PolyTerm`. -/
def PolyTerm.fold {profile : PolyProfile} {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    {dimension : CellDim} :
    PolyTerm profile dimension → target dimension
  | .atom cellId payload => algebra.interpretAtom cellId payload
  | .cell ruleId source targetCell =>
      algebra.interpretCell ruleId (fold algebra source) (fold algebra targetCell)
  | .compV first second =>
      algebra.interpretCompV (fold algebra first) (fold algebra second)
  | .compH left right =>
      algebra.interpretCompH (fold algebra left) (fold algebra right)
  | .identity base =>
      algebra.interpretIdentity (fold algebra base)

/-- The identity algebra: fold with this = identity function. -/
def PolyTermAlgebra.identity (profile : PolyProfile) :
    PolyTermAlgebra profile (PolyTerm profile) where
  interpretAtom := .atom
  interpretCell := .cell
  interpretCompV := .compV
  interpretCompH := .compH
  interpretIdentity := .identity

/-- Fold with the identity algebra gives back the original term. -/
theorem PolyTerm.fold_identity {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile dimension) :
    PolyTerm.fold (PolyTermAlgebra.identity profile) term = term := by
  induction term with
  | atom _ _ => rfl
  | cell _ _ _ ihSource ihTarget =>
    show PolyTerm.cell _ (fold _ _) (fold _ _) = _
    rw [ihSource, ihTarget]
  | compV _ _ ihFirst ihSecond =>
    show PolyTerm.compV (fold _ _) (fold _ _) = _
    rw [ihFirst, ihSecond]
  | compH _ _ ihLeft ihRight =>
    show PolyTerm.compH (fold _ _) (fold _ _) = _
    rw [ihLeft, ihRight]
  | identity _ ihBase =>
    show PolyTerm.identity (fold _ _) = _
    rw [ihBase]

/-- Boundary slots are trivial at dimension 0 and optional lower-dimensional
endpoints at positive dimensions. -/
def PolyTerm.boundarySlot (profile : PolyProfile) : CellDim → Type
  | 0 => Unit
  | dimension + 1 => Option (PolyTerm profile dimension)

/-- Fold-carried structural boundary view.

The `term` field keeps the reconstructed syntax so boundary endpoints can be
reported without dependent pattern matching on the indexed `PolyTerm` itself. -/
structure PolyTermBoundaryView (profile : PolyProfile) (dimension : CellDim) where
  term : PolyTerm profile dimension
  sourceBoundary? : PolyTerm.boundarySlot profile dimension
  targetBoundary? : PolyTerm.boundarySlot profile dimension

/-- Algebra computing the syntax-preserving partial boundary view. -/
def PolyTermBoundaryView.algebra (profile : PolyProfile) :
    PolyTermAlgebra profile (PolyTermBoundaryView profile) where
  interpretAtom := fun cellId payload =>
    { term := .atom cellId payload
      sourceBoundary? := ()
      targetBoundary? := () }
  interpretCell := fun ruleId sourceView targetView =>
    { term := .cell ruleId sourceView.term targetView.term
      sourceBoundary? := some sourceView.term
      targetBoundary? := some targetView.term }
  interpretCompV := fun firstView secondView =>
    { term := .compV firstView.term secondView.term
      sourceBoundary? := firstView.sourceBoundary?
      targetBoundary? := secondView.targetBoundary? }
  interpretCompH := fun leftView rightView =>
    { term := .compH leftView.term rightView.term
      sourceBoundary? := none
      targetBoundary? := none }
  interpretIdentity := fun baseView =>
    { term := .identity baseView.term
      sourceBoundary? := some baseView.term
      targetBoundary? := some baseView.term }

/-- Compute the structural boundary view by folding over the five constructors. -/
def PolyTerm.boundaryView {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile dimension) : PolyTermBoundaryView profile dimension :=
  PolyTerm.fold (PolyTermBoundaryView.algebra profile) term

/-- The boundary view preserves the original syntax. -/
theorem PolyTerm.boundaryView_term_eq {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile dimension) :
    (PolyTerm.fold (PolyTermBoundaryView.algebra profile) term).term = term := by
  induction term with
  | atom _ _ => rfl
  | cell ruleId source target ihSource ihTarget =>
      change
        PolyTerm.cell ruleId
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) source).term
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) target).term =
          PolyTerm.cell ruleId source target
      rw [ihSource, ihTarget]
  | compV first second ihFirst ihSecond =>
      change
        PolyTerm.compV
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) first).term
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) second).term =
          PolyTerm.compV first second
      rw [ihFirst, ihSecond]
  | compH left right ihLeft ihRight =>
      change
        PolyTerm.compH
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) left).term
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) right).term =
          PolyTerm.compH left right
      rw [ihLeft, ihRight]
  | identity base ihBase =>
      change
        PolyTerm.identity
          (PolyTerm.fold (PolyTermBoundaryView.algebra profile) base).term =
          PolyTerm.identity base
      rw [ihBase]

/-- Known source boundary for a positive-dimensional structural cell.

This is partial because the current `compH` constructor has no mechanized Gray
boundary semantics yet.  Vertical composition projects the first known source;
this does not check the intermediate boundary equation. -/
def PolyTerm.source? {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile (dimension + 1)) :
    Option (PolyTerm profile dimension) :=
  term.boundaryView.sourceBoundary?

/-- Known target boundary for a positive-dimensional structural cell.

This is partial for the same reason as `source?`: horizontal composition waits
for the Gray boundary layer, and vertical composition does not validate the
middle boundary equation. -/
def PolyTerm.target? {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile (dimension + 1)) :
    Option (PolyTerm profile dimension) :=
  term.boundaryView.targetBoundary?

theorem PolyTerm.source?_cell {profile : PolyProfile} {dimension : CellDim}
    (ruleId : CellId) (source target : PolyTerm profile dimension) :
    (PolyTerm.cell (profile := profile) ruleId source target).source? =
      some source := by
  change some (PolyTerm.fold (PolyTermBoundaryView.algebra profile) source).term =
    some source
  rw [PolyTerm.boundaryView_term_eq source]

theorem PolyTerm.target?_cell {profile : PolyProfile} {dimension : CellDim}
    (ruleId : CellId) (source target : PolyTerm profile dimension) :
    (PolyTerm.cell (profile := profile) ruleId source target).target? =
      some target := by
  change some (PolyTerm.fold (PolyTermBoundaryView.algebra profile) target).term =
    some target
  rw [PolyTerm.boundaryView_term_eq target]

theorem PolyTerm.source?_compV {profile : PolyProfile} {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1)) :
    (PolyTerm.compV (profile := profile) first second).source? =
      first.source? := rfl

theorem PolyTerm.target?_compV {profile : PolyProfile} {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1)) :
    (PolyTerm.compV (profile := profile) first second).target? =
      second.target? := rfl

theorem PolyTerm.source?_compH {profile : PolyProfile} {dimension : CellDim}
    (left right : PolyTerm profile (dimension + 1)) :
    (PolyTerm.compH (profile := profile) left right).source? = none := rfl

theorem PolyTerm.target?_compH {profile : PolyProfile} {dimension : CellDim}
    (left right : PolyTerm profile (dimension + 1)) :
    (PolyTerm.compH (profile := profile) left right).target? = none := rfl

theorem PolyTerm.source?_identity {profile : PolyProfile} {dimension : CellDim}
    (base : PolyTerm profile dimension) :
    (PolyTerm.identity (profile := profile) base).source? =
      some base := by
  change some (PolyTerm.fold (PolyTermBoundaryView.algebra profile) base).term =
    some base
  rw [PolyTerm.boundaryView_term_eq base]

theorem PolyTerm.target?_identity {profile : PolyProfile} {dimension : CellDim}
    (base : PolyTerm profile dimension) :
    (PolyTerm.identity (profile := profile) base).target? =
      some base := by
  change some (PolyTerm.fold (PolyTermBoundaryView.algebra profile) base).term =
    some base
  rw [PolyTerm.boundaryView_term_eq base]

/-- A map algebra: transforms cellIds/ruleIds while preserving structure. -/
def PolyTermAlgebra.mapIds (profile : PolyProfile)
    (cellIdMap : CellId → CellId)
    (ruleIdMap : CellId → CellId)
    (payloadMap : CellId → Nat → Nat) :
    PolyTermAlgebra profile (PolyTerm profile) where
  interpretAtom := fun cellId payload => .atom (cellIdMap cellId) (payloadMap cellId payload)
  interpretCell := fun ruleId source target => .cell (ruleIdMap ruleId) source target
  interpretCompV := .compV
  interpretCompH := .compH
  interpretIdentity := .identity

/-- A counting algebra: counts total cells at each dimension. -/
def PolyTermAlgebra.count (profile : PolyProfile) :
    PolyTermAlgebra profile (fun _ => Nat) where
  interpretAtom := fun _ _ => 1
  interpretCell := fun _ sourceCount targetCount => 1 + sourceCount + targetCount
  interpretCompV := fun firstCount secondCount => firstCount + secondCount
  interpretCompH := fun leftCount rightCount => leftCount + rightCount
  interpretIdentity := fun baseCount => baseCount


end LeanFX2.Foundation.PolyCell.Core
