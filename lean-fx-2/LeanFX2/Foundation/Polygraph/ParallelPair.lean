import LeanFX2.Foundation.Polygraph.PolyCell

/-! # `ParallelPair` predicate + per-stratum projections for `PolyCell`.

Given the intrinsic-parallelism encoding shipped by K11.1 — `PolyCell`
indexes on `(dim, sourceVtx, targetVtx)` so Burroni 1993 §1.1's
parallelism condition holds by the type indices — the predicate
`ParallelPair` is a `Prop`-witness that two cells live at the same
indexed family, and the projections extract source / target / numeric
handle per stratum.

The projection encoding follows the casesOn-with-index-equality recipe
in `feedback_lean_indexed_partial_match.md`: a partial match restricted
to one constructor on an indexed inductive leaks propext through the
auto-generated equation lemmas for the impossible-by-index cases.  The
fix is to take an explicit equality witness in the motive and discharge
the impossible cases with `Nat.noConfusion`, recovering the matched
case's payload via `Nat.succ.inj` + `▸`.
-/

namespace LeanFX2.Foundation.Polygraph

/-- Two polygraph cells are parallel when they inhabit the same
indexed family — same dimension, same dim-0 globular boundary.  The
intrinsic indexing of `PolyCell` enforces this at the type level
already; `ParallelPair` exposes the property as a `Prop` witness so
downstream constructions (K11.4 vertical composition, K11.6
interchange laws) can take it as an explicit hypothesis when their
inputs come from potentially-heterogeneous indexed families. -/
inductive ParallelPair :
    {firstDim firstSourceVtx firstTargetVtx
     secondDim secondSourceVtx secondTargetVtx : Nat} →
    PolyCell firstDim firstSourceVtx firstTargetVtx →
    PolyCell secondDim secondSourceVtx secondTargetVtx →
    Prop
  | introWitness {dim sourceVtx targetVtx : Nat}
                 (firstCell secondCell : PolyCell dim sourceVtx targetVtx) :
      ParallelPair firstCell secondCell

/-- A dim-0 atom's vertex.  Total function: `atom vtx`'s payload is
`vtx`, equal to both source and target indices. -/
def atomVertex {vertexIndex : Nat}
    (atomCell : PolyCell 0 vertexIndex vertexIndex) : Nat :=
  PolyCell.casesOn (motive := fun (someDim someSource someTarget : Nat)
                                   (_ : PolyCell someDim someSource someTarget) =>
                                  someDim = 0 →
                                  someSource = vertexIndex →
                                  someTarget = vertexIndex →
                                  Nat)
    atomCell
    (fun (vtx : Nat) _ _ _ => vtx)
    (fun {_innerSource _innerTarget} _arrowSource _arrowTarget _idx
         (impossibleEq : (1 : Nat) = 0) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {_innerDim _innerSource _innerTarget} _ _ _
         (impossibleEq : _ + 2 = 0) _ _ =>
      Nat.noConfusion impossibleEq)
    rfl rfl rfl

/-- Source of a dim-1 arrow: a dim-0 atom at the source vertex. -/
def arrowSource {sourceVtx targetVtx : Nat}
    (arrowCell : PolyCell 1 sourceVtx targetVtx) :
    PolyCell 0 sourceVtx sourceVtx :=
  PolyCell.casesOn (motive := fun (someDim someSource someTarget : Nat)
                                   (_ : PolyCell someDim someSource someTarget) =>
                                  someDim = 1 →
                                  someSource = sourceVtx →
                                  someTarget = targetVtx →
                                  PolyCell 0 sourceVtx sourceVtx)
    arrowCell
    (fun (_vtx : Nat) (impossibleEq : (0 : Nat) = 1) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {innerSource _innerTarget} sourceAtom _targetAtom _idx
         _dimEq (sourceEq : innerSource = sourceVtx) _targetEq =>
      sourceEq ▸ sourceAtom)
    (fun {_innerDim _innerSource _innerTarget} _ _ _
         (impossibleEq : _ + 2 = 1) _ _ =>
      Nat.noConfusion (Nat.succ.inj impossibleEq))
    rfl rfl rfl

/-- Target of a dim-1 arrow: a dim-0 atom at the target vertex. -/
def arrowTarget {sourceVtx targetVtx : Nat}
    (arrowCell : PolyCell 1 sourceVtx targetVtx) :
    PolyCell 0 targetVtx targetVtx :=
  PolyCell.casesOn (motive := fun (someDim someSource someTarget : Nat)
                                   (_ : PolyCell someDim someSource someTarget) =>
                                  someDim = 1 →
                                  someSource = sourceVtx →
                                  someTarget = targetVtx →
                                  PolyCell 0 targetVtx targetVtx)
    arrowCell
    (fun (_vtx : Nat) (impossibleEq : (0 : Nat) = 1) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {_innerSource innerTarget} _sourceAtom targetAtom _idx
         _dimEq _sourceEq (targetEq : innerTarget = targetVtx) =>
      targetEq ▸ targetAtom)
    (fun {_innerDim _innerSource _innerTarget} _ _ _
         (impossibleEq : _ + 2 = 1) _ _ =>
      Nat.noConfusion (Nat.succ.inj impossibleEq))
    rfl rfl rfl

/-- Source of a dim-`(dim+2)` cell: a dim-`(dim+1)` cell at the same
globular boundary. -/
def cellSource {dim sourceVtx targetVtx : Nat}
    (highCell : PolyCell (dim + 2) sourceVtx targetVtx) :
    PolyCell (dim + 1) sourceVtx targetVtx :=
  PolyCell.casesOn (motive := fun (someDim someSource someTarget : Nat)
                                   (_ : PolyCell someDim someSource someTarget) =>
                                  someDim = dim + 2 →
                                  someSource = sourceVtx →
                                  someTarget = targetVtx →
                                  PolyCell (dim + 1) sourceVtx targetVtx)
    highCell
    (fun (_vtx : Nat) (impossibleEq : (0 : Nat) = dim + 2) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {_innerSource _innerTarget} _sourceAtom _targetAtom _idx
         (impossibleEq : (1 : Nat) = dim + 2) _ _ =>
      Nat.noConfusion (Nat.succ.inj impossibleEq))
    (fun {innerDim innerSource innerTarget} subSource _subTarget _idx
         (dimEq : innerDim + 2 = dim + 2)
         (sourceEq : innerSource = sourceVtx)
         (targetEq : innerTarget = targetVtx) =>
      let innerDimEq : innerDim = dim := Nat.succ.inj (Nat.succ.inj dimEq)
      innerDimEq ▸ sourceEq ▸ targetEq ▸ subSource)
    rfl rfl rfl

/-- Target of a dim-`(dim+2)` cell. -/
def cellTarget {dim sourceVtx targetVtx : Nat}
    (highCell : PolyCell (dim + 2) sourceVtx targetVtx) :
    PolyCell (dim + 1) sourceVtx targetVtx :=
  PolyCell.casesOn (motive := fun (someDim someSource someTarget : Nat)
                                   (_ : PolyCell someDim someSource someTarget) =>
                                  someDim = dim + 2 →
                                  someSource = sourceVtx →
                                  someTarget = targetVtx →
                                  PolyCell (dim + 1) sourceVtx targetVtx)
    highCell
    (fun (_vtx : Nat) (impossibleEq : (0 : Nat) = dim + 2) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {_innerSource _innerTarget} _sourceAtom _targetAtom _idx
         (impossibleEq : (1 : Nat) = dim + 2) _ _ =>
      Nat.noConfusion (Nat.succ.inj impossibleEq))
    (fun {innerDim innerSource innerTarget} _subSource subTarget _idx
         (dimEq : innerDim + 2 = dim + 2)
         (sourceEq : innerSource = sourceVtx)
         (targetEq : innerTarget = targetVtx) =>
      let innerDimEq : innerDim = dim := Nat.succ.inj (Nat.succ.inj dimEq)
      innerDimEq ▸ sourceEq ▸ targetEq ▸ subTarget)
    rfl rfl rfl

/-- Numeric handle of any `PolyCell`: the `Nat` payload of its
constructor.  For `atom`, returns the vertex itself; for `arrow` and
`cell`, returns the explicit index argument.  Total over all
dimensions. -/
def cellIdx {dim sourceVtx targetVtx : Nat}
    (someCell : PolyCell dim sourceVtx targetVtx) : Nat :=
  PolyCell.casesOn (motive := fun _ _ _ _ => Nat)
    someCell
    (fun (vtx : Nat) => vtx)
    (fun _arrowSource _arrowTarget (idx : Nat) => idx)
    (fun _subSource _subTarget (idx : Nat) => idx)

end LeanFX2.Foundation.Polygraph
