import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# PolyTerm Fold / Catamorphism — The Generic Operation Engine

The fold IS how generic rename/subst/evaluation work on PolyTerm.
Instead of inducting on 74+ constructors, operations induct on the
5 structural constructors with Generator-dispatch INSIDE atom/cell.

A PolyTermAlgebra specifies what to DO at each constructor.
PolyTerm.fold applies the algebra recursively = one generic operation.

rename = fold with a renaming algebra
subst  = fold with a substitution algebra
eval   = fold with an evaluation algebra
cd     = fold with a complete-development algebra

ALL of these are ONE function (fold) parameterized by different algebras.

Reference: polycell.md §4 + C.6 task description.
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

/-- THE FOLD: recursively apply a PolyTermAlgebra to a PolyTerm.
This is the single function that replaces all 74-arm structural inductions. -/
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
