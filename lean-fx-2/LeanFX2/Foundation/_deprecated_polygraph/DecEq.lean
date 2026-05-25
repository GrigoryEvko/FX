import LeanFX2.Foundation._deprecated_polygraph.ParallelPair

/-! # `DecidableEq (PolyCell dim sv tv)` — propext-free instance.

Auto-derived `DecidableEq` on `PolyCell` leaks `propext` through the
equation lemmas Lean generates for the partial-pattern dispatch on
over-constrained per-ctor indices.  See
`feedback_lean_indexed_deceq_propext.md` for the 18-attempt landscape.

The clean path: pure `PolyCell.casesOn` with index-equality witness
motive — same recipe as K11.2's projections, scaled to a binary
destructuring via dim-stratified dispatch + `Σ'`-typed decomposition
for the dim-`(n+2)` stratum so the motive never has to compose with
`cellSource` / `cellTarget` / `cellIdx` (which require fixed indices).

## Strategy

1. Three dim-stratified deciders:
   * `decEqAtDim0` — both cells forced to `atom sv` via uniqueness.
   * `decEqAtDim1` — both cells forced to `arrow (atom sv) (atom tv) idx`;
     compare idx.
   * `decEqAtDimSucc` — `Σ'`-typed decomposition extracts subSource/
     subTarget/idx; recurse on subcells, compare idx.
2. Three uniqueness / decomposition results via pure `casesOn`-with-
   witness:
   * `atom_unique_at_dim0` — every `PolyCell 0 sv sv = atom sv`.
   * `arrow_unique_at_dim1` — every `PolyCell 1 sv tv = arrow ...`.
   * `cell_decompose_at_dimSucc` — every `PolyCell (n+2) sv tv` admits
     a triple `(subSource, subTarget, idx)` with `cell = cell ...`.
3. Top-level `polyCellDecEqAt` dispatches on dim via `Nat`-pattern
   match (clean — `Nat` is a primitive inductive).

Verified zero-axiom via `#print axioms polyCellDecEqAt`. -/

namespace LeanFX2.Foundation._deprecated_polygraph

/-- Atom uniqueness at dim 0: every `PolyCell 0 sv sv` equals
`atom sv`.  Uses pure `PolyCell.casesOn` with index-equality witness
motive — impossible-by-index cases discharged via `Nat.noConfusion`. -/
theorem PolyCell.atom_unique_at_dim0 {sv : Nat}
    (someCell : PolyCell 0 sv sv) :
    someCell = PolyCell.atom sv :=
  PolyCell.casesOn
    (motive := fun (someDim someSource someTarget : Nat)
                   (theCell : PolyCell someDim someSource someTarget) =>
                ∀ (_dimEq : someDim = 0)
                  (_sourceEq : someSource = sv)
                  (_targetEq : someTarget = sv),
                  HEq theCell (PolyCell.atom sv))
    someCell
    (fun (vtx : Nat) _dimEq (vertexEq : vtx = sv) _targetEq =>
      vertexEq ▸ HEq.rfl)
    (fun _ _ _ (impossibleEq : (1 : Nat) = 0) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun _ _ _ (impossibleEq : _ + 2 = 0) _ _ =>
      Nat.noConfusion impossibleEq)
    rfl rfl rfl
  |> eq_of_heq

/-- Arrow uniqueness at dim 1: every `PolyCell 1 sv tv` equals
`arrow (atom sv) (atom tv) (cellIdx someCell)`. -/
theorem PolyCell.arrow_unique_at_dim1 {sv tv : Nat}
    (someCell : PolyCell 1 sv tv) :
    someCell =
      PolyCell.arrow (PolyCell.atom sv) (PolyCell.atom tv)
                     (cellIdx someCell) :=
  PolyCell.casesOn
    (motive := fun (someDim someSource someTarget : Nat)
                   (theCell : PolyCell someDim someSource someTarget) =>
                ∀ (_dimEq : someDim = 1)
                  (_sourceEq : someSource = sv)
                  (_targetEq : someTarget = tv),
                  HEq theCell
                    (PolyCell.arrow (PolyCell.atom sv) (PolyCell.atom tv)
                      (cellIdx theCell)))
    someCell
    (fun _ (impossibleEq : (0 : Nat) = 1) _ _ =>
      Nat.noConfusion impossibleEq)
    (fun {innerSource innerTarget} sourceAtom targetAtom _idx
         _dimEq (innerSourceEq : innerSource = sv) (innerTargetEq : innerTarget = tv) =>
      let atomSourceEq : sourceAtom = PolyCell.atom innerSource :=
        atom_unique_at_dim0 sourceAtom
      let atomTargetEq : targetAtom = PolyCell.atom innerTarget :=
        atom_unique_at_dim0 targetAtom
      atomSourceEq ▸ atomTargetEq ▸ innerSourceEq ▸ innerTargetEq ▸ HEq.rfl)
    (fun _ _ _ (impossibleEq : _ + 2 = 1) _ _ =>
      Nat.noConfusion (Nat.succ.inj impossibleEq))
    rfl rfl rfl
  |> eq_of_heq

/-- Decompose a dim-`(n+2)` cell: every such cell is built from a
sub-source, sub-target, and index via the `cell` constructor.

Uses pure `PolyCell.casesOn` with index-equality witness motive +
`HEq.rfl` in the `cell` arm after `▸` rewrites unify the inner indices
with `(n, sv, tv)`.  The motive does NOT reference `cellSource` /
`cellTarget` (which would require the bound `theCell` to live at fixed
indices — impossible inside the motive).

Declared `def` (not `theorem`) because the return type is `Σ'`, which
lives in `Type`, not `Prop`. -/
def PolyCell.cell_decompose_at_dimSucc {n sv tv : Nat}
    (someCell : PolyCell (n + 2) sv tv) :
    Σ' (subSource subTarget : PolyCell (n + 1) sv tv) (idx : Nat),
      someCell = PolyCell.cell subSource subTarget idx :=
  let decomposeWithHEq :
      Σ' (subSource subTarget : PolyCell (n + 1) sv tv) (idx : Nat),
        HEq someCell (PolyCell.cell subSource subTarget idx) :=
    PolyCell.casesOn
      (motive := fun (someDim someSource someTarget : Nat)
                     (theCell : PolyCell someDim someSource someTarget) =>
                  ∀ (_dimEq : someDim = n + 2)
                    (_sourceEq : someSource = sv)
                    (_targetEq : someTarget = tv),
                    Σ' (subSource subTarget : PolyCell (n + 1) sv tv)
                       (idx : Nat),
                      HEq theCell (PolyCell.cell subSource subTarget idx))
      someCell
      (fun _ (impossibleEq : (0 : Nat) = n + 2) _ _ =>
        Nat.noConfusion impossibleEq)
      (fun _ _ _ (impossibleEq : (1 : Nat) = n + 2) _ _ =>
        Nat.noConfusion (Nat.succ.inj impossibleEq))
      (fun {innerDim innerSource innerTarget} subSource subTarget idx
           (dimEq : innerDim + 2 = n + 2)
           (sourceEq : innerSource = sv)
           (targetEq : innerTarget = tv) =>
        let innerDimEq : innerDim = n :=
          Nat.succ.inj (Nat.succ.inj dimEq)
        innerDimEq ▸ sourceEq ▸ targetEq ▸
          ⟨subSource, subTarget, idx, HEq.rfl⟩)
      rfl rfl rfl
  ⟨decomposeWithHEq.1, decomposeWithHEq.2.1, decomposeWithHEq.2.2.1,
    eq_of_heq decomposeWithHEq.2.2.2⟩

/-- Decide equality at dim 0.  Both cells are forced to be
`atom sv` by atom-uniqueness; result is always `isTrue`. -/
def decEqAtDim0 {sv : Nat} (left right : PolyCell 0 sv sv) :
    Decidable (left = right) :=
  isTrue (by rw [PolyCell.atom_unique_at_dim0 left,
                 PolyCell.atom_unique_at_dim0 right])

/-- Decide equality at dim 1.  Reduce both cells to the canonical
arrow form, compare idx via `Nat.decEq`. -/
def decEqAtDim1 {sv tv : Nat} (left right : PolyCell 1 sv tv) :
    Decidable (left = right) :=
  match Nat.decEq (cellIdx left) (cellIdx right) with
  | isTrue idxEq => isTrue (by
      rw [PolyCell.arrow_unique_at_dim1 left,
          PolyCell.arrow_unique_at_dim1 right, idxEq])
  | isFalse idxNeq =>
    isFalse (fun cellsEq => idxNeq (congrArg cellIdx cellsEq))

/-- Decide equality at dim `n+2`.  Decompose both cells into
`(subSource, subTarget, idx)` triples; recurse on sub-cells; compare
idx via `Nat.decEq`.

Inversion for the `isFalse` arms relies on `cellSource` / `cellTarget`
/ `cellIdx` rfl-reducing on the `cell` ctor, plus `congrArg` to lift
the cell-level equality to the sub-cell / index level. -/
def decEqAtDimSucc {n sv tv : Nat}
    (recurseSubCell :
      ∀ {sv' tv' : Nat} (subLeft subRight : PolyCell (n + 1) sv' tv'),
        Decidable (subLeft = subRight))
    (left right : PolyCell (n + 2) sv tv) :
    Decidable (left = right) :=
  match PolyCell.cell_decompose_at_dimSucc left,
        PolyCell.cell_decompose_at_dimSucc right with
  | ⟨leftSubSource, leftSubTarget, leftIdx, leftIs⟩,
    ⟨rightSubSource, rightSubTarget, rightIdx, rightIs⟩ =>
    match recurseSubCell leftSubSource rightSubSource with
    | isFalse subSourceNeq =>
      isFalse (fun cellsEq => subSourceNeq (by
        have cellsCtorEq :
            PolyCell.cell leftSubSource leftSubTarget leftIdx =
            PolyCell.cell rightSubSource rightSubTarget rightIdx := by
          rw [← leftIs, ← rightIs]; exact cellsEq
        exact congrArg cellSource cellsCtorEq))
    | isTrue subSourceEq =>
      match recurseSubCell leftSubTarget rightSubTarget with
      | isFalse subTargetNeq =>
        isFalse (fun cellsEq => subTargetNeq (by
          have cellsCtorEq :
              PolyCell.cell leftSubSource leftSubTarget leftIdx =
              PolyCell.cell rightSubSource rightSubTarget rightIdx := by
            rw [← leftIs, ← rightIs]; exact cellsEq
          exact congrArg cellTarget cellsCtorEq))
      | isTrue subTargetEq =>
        match Nat.decEq leftIdx rightIdx with
        | isFalse idxNeq =>
          isFalse (fun cellsEq => idxNeq (by
            have cellsCtorEq :
                PolyCell.cell leftSubSource leftSubTarget leftIdx =
                PolyCell.cell rightSubSource rightSubTarget rightIdx := by
              rw [← leftIs, ← rightIs]; exact cellsEq
            exact congrArg cellIdx cellsCtorEq))
        | isTrue idxEq =>
          isTrue (by
            rw [leftIs, rightIs, subSourceEq, subTargetEq, idxEq])

/-- Decidable equality on `PolyCell dim sv tv` via dim-stratified
dispatch.  Pattern matching on `Nat` is propext-clean (primitive
inductive). -/
def polyCellDecEqAt : ∀ {dim sv tv : Nat}
    (left right : PolyCell dim sv tv), Decidable (left = right)
  | 0, _, _, left, right => by
    cases left
    cases right
    exact isTrue rfl
  | 1, _, _, left, right => decEqAtDim1 left right
  | _ + 2, _, _, left, right =>
    decEqAtDimSucc (fun {_ _} subLeft subRight =>
      polyCellDecEqAt subLeft subRight) left right

instance decEqPolyCell {dim sv tv : Nat} :
    DecidableEq (PolyCell dim sv tv) := polyCellDecEqAt

end LeanFX2.Foundation._deprecated_polygraph
