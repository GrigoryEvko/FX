import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# Propext-free `DecidableEq (PolyTerm profile dim)`

Auto-derived `DecidableEq` and naive `match a, b` both leak `propext` through the
equation lemmas Lean generates for the partial dispatch on the over-constrained
dimension index (`.atom` is impossible at `dim+1`, the others at `0`).

The clean path mirrors the deprecated Burroni-`PolyCell` recipe
(`_deprecated_polygraph/DecEq.lean`, #1747): a positive-dimension decomposition
built with pure `PolyTerm.casesOn` and an index-equality-witness motive, with
the impossible `.atom` constructor discharged via `Nat.noConfusion` and the
transport casts distributed through standalone `cast_*` lemmas (real
hypotheses, so `subst` reduces them to `rfl`).

Unlike the Burroni cells, `PolyTerm.compV`/`compH` compose SAME-dimension
children, so equality cannot recurse on the dimension; `decEq` recurses on
`PolyTerm.size` (well-founded), with child-size bounds recovered from the
decomposition's witnessing equality.

Verified zero-axiom via `#assert_no_axioms PolyTerm.decEq` in `AuditPolyCell`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Transport of a `cell` constructor through a successor-dimension equality
distributes onto its children.  Proved by `subst` of the inner equality, after
which proof irrelevance collapses the remaining cast to `rfl`. -/
theorem PolyTerm.cast_cell {profile : PolyProfile} {innerDim lowerDim : CellDim}
    (dimEq : innerDim + 1 = lowerDim + 1) (ruleId : CellId)
    (source target : PolyTerm profile innerDim) :
    dimEq ▸ PolyTerm.cell ruleId source target =
      PolyTerm.cell ruleId (Nat.succ.inj dimEq ▸ source)
        (Nat.succ.inj dimEq ▸ target) := by
  have innerDimEq : innerDim = lowerDim := Nat.succ.inj dimEq
  subst innerDimEq; rfl

/-- Transport of a `compV` constructor distributes onto its same-dimension
children. -/
theorem PolyTerm.cast_compV {profile : PolyProfile} {innerDim lowerDim : CellDim}
    (dimEq : innerDim + 1 = lowerDim + 1)
    (first second : PolyTerm profile (innerDim + 1)) :
    dimEq ▸ PolyTerm.compV first second =
      PolyTerm.compV (dimEq ▸ first) (dimEq ▸ second) := by
  have innerDimEq : innerDim = lowerDim := Nat.succ.inj dimEq
  subst innerDimEq; rfl

/-- Transport of a `compH` constructor distributes onto its same-dimension
children. -/
theorem PolyTerm.cast_compH {profile : PolyProfile} {innerDim lowerDim : CellDim}
    (dimEq : innerDim + 1 = lowerDim + 1)
    (left right : PolyTerm profile (innerDim + 1)) :
    dimEq ▸ PolyTerm.compH left right =
      PolyTerm.compH (dimEq ▸ left) (dimEq ▸ right) := by
  have innerDimEq : innerDim = lowerDim := Nat.succ.inj dimEq
  subst innerDimEq; rfl

/-- Transport of an `identity` constructor distributes onto its base child. -/
theorem PolyTerm.cast_identity {profile : PolyProfile}
    {innerDim lowerDim : CellDim} (dimEq : innerDim + 1 = lowerDim + 1)
    (base : PolyTerm profile innerDim) :
    dimEq ▸ PolyTerm.identity base =
      PolyTerm.identity (Nat.succ.inj dimEq ▸ base) := by
  have innerDimEq : innerDim = lowerDim := Nat.succ.inj dimEq
  subst innerDimEq; rfl

/-- A decomposition of a positive-dimensional raw cell into exactly one of the
four successor constructors, carrying the witnessing equality as data.  The
index `cell` is a free parameter (the constructors assert `cell = …`), so
matching never refines the dimension. -/
inductive PolyTerm.SuccShape (profile : PolyProfile) (lowerDim : CellDim) :
    PolyTerm profile (lowerDim + 1) → Type where
  | ofCell (ruleId : CellId) (source target : PolyTerm profile lowerDim)
      (cell : PolyTerm profile (lowerDim + 1))
      (isCell : cell = PolyTerm.cell ruleId source target) :
      PolyTerm.SuccShape profile lowerDim cell
  | ofCompV (first second : PolyTerm profile (lowerDim + 1))
      (cell : PolyTerm profile (lowerDim + 1))
      (isCompV : cell = PolyTerm.compV first second) :
      PolyTerm.SuccShape profile lowerDim cell
  | ofCompH (left right : PolyTerm profile (lowerDim + 1))
      (cell : PolyTerm profile (lowerDim + 1))
      (isCompH : cell = PolyTerm.compH left right) :
      PolyTerm.SuccShape profile lowerDim cell
  | ofIdentity (base : PolyTerm profile lowerDim)
      (cell : PolyTerm profile (lowerDim + 1))
      (isIdentity : cell = PolyTerm.identity base) :
      PolyTerm.SuccShape profile lowerDim cell

/-- Decompose any positive-dimensional raw cell into its `SuccShape`.

Pure `PolyTerm.casesOn` with an index-equality-witness motive; the `.atom` case
is discharged by `Nat.noConfusion` and each successor case witnesses its
constructor via the corresponding `cast_*` lemma. -/
def PolyTerm.succShape {profile : PolyProfile} {lowerDim : CellDim}
    (cell : PolyTerm profile (lowerDim + 1)) :
    PolyTerm.SuccShape profile lowerDim cell :=
  PolyTerm.casesOn
    (motive := fun (someDim : CellDim) (someCell : PolyTerm profile someDim) =>
      (dimEq : someDim = lowerDim + 1) →
        PolyTerm.SuccShape profile lowerDim (dimEq ▸ someCell))
    cell
    (fun _cellId _payload (dimEq : 0 = lowerDim + 1) =>
      Nat.noConfusion dimEq)
    (fun {innerDim} ruleId source target (dimEq : innerDim + 1 = lowerDim + 1) =>
      PolyTerm.SuccShape.ofCell ruleId (Nat.succ.inj dimEq ▸ source)
        (Nat.succ.inj dimEq ▸ target)
        (dimEq ▸ PolyTerm.cell ruleId source target)
        (PolyTerm.cast_cell dimEq ruleId source target))
    (fun {innerDim} first second (dimEq : innerDim + 1 = lowerDim + 1) =>
      PolyTerm.SuccShape.ofCompV (dimEq ▸ first) (dimEq ▸ second)
        (dimEq ▸ PolyTerm.compV first second)
        (PolyTerm.cast_compV dimEq first second))
    (fun {innerDim} left right (dimEq : innerDim + 1 = lowerDim + 1) =>
      PolyTerm.SuccShape.ofCompH (dimEq ▸ left) (dimEq ▸ right)
        (dimEq ▸ PolyTerm.compH left right)
        (PolyTerm.cast_compH dimEq left right))
    (fun {innerDim} base (dimEq : innerDim + 1 = lowerDim + 1) =>
      PolyTerm.SuccShape.ofIdentity (Nat.succ.inj dimEq ▸ base)
        (dimEq ▸ PolyTerm.identity base)
        (PolyTerm.cast_identity dimEq base))
    rfl

/-- `omega`-free `a < 1 + a`. -/
private theorem PolyTerm.lt_one_add (a : Nat) : a < 1 + a :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_of_eq (Nat.add_comm a 1))

/-- `omega`-free `a < 1 + a + b` (size bound for a first child). -/
private theorem PolyTerm.lt_one_add_add_left (a b : Nat) : a < 1 + a + b :=
  Nat.lt_of_lt_of_le (PolyTerm.lt_one_add a) (Nat.le_add_right (1 + a) b)

/-- `omega`-free `b < 1 + a + b` (size bound for a second child). -/
private theorem PolyTerm.lt_one_add_add_right (a b : Nat) : b < 1 + a + b :=
  Nat.add_right_comm 1 b a ▸ PolyTerm.lt_one_add_add_left b a

/-- A `SuccShape`'s recorded constructor equality bounds its children's size
below the decomposed cell — used to discharge well-founded recursion.  Proved
with core `Nat` lemmas (no `omega`/`simp`) to stay propext-free. -/
theorem PolyTerm.size_lt_of_isCell {profile : PolyProfile} {lowerDim : CellDim}
    {ruleId : CellId} {source target : PolyTerm profile lowerDim}
    {cell : PolyTerm profile (lowerDim + 1)}
    (isCell : cell = PolyTerm.cell ruleId source target) :
    source.size < cell.size ∧ target.size < cell.size := by
  subst isCell
  exact ⟨PolyTerm.lt_one_add_add_left source.size target.size,
    PolyTerm.lt_one_add_add_right source.size target.size⟩

theorem PolyTerm.size_lt_of_isCompV {profile : PolyProfile} {lowerDim : CellDim}
    {first second : PolyTerm profile (lowerDim + 1)}
    {cell : PolyTerm profile (lowerDim + 1)}
    (isCompV : cell = PolyTerm.compV first second) :
    first.size < cell.size ∧ second.size < cell.size := by
  subst isCompV
  exact ⟨PolyTerm.lt_one_add_add_left first.size second.size,
    PolyTerm.lt_one_add_add_right first.size second.size⟩

theorem PolyTerm.size_lt_of_isCompH {profile : PolyProfile} {lowerDim : CellDim}
    {left right : PolyTerm profile (lowerDim + 1)}
    {cell : PolyTerm profile (lowerDim + 1)}
    (isCompH : cell = PolyTerm.compH left right) :
    left.size < cell.size ∧ right.size < cell.size := by
  subst isCompH
  exact ⟨PolyTerm.lt_one_add_add_left left.size right.size,
    PolyTerm.lt_one_add_add_right left.size right.size⟩

theorem PolyTerm.size_lt_of_isIdentity {profile : PolyProfile}
    {lowerDim : CellDim} {base : PolyTerm profile lowerDim}
    {cell : PolyTerm profile (lowerDim + 1)}
    (isIdentity : cell = PolyTerm.identity base) :
    base.size < cell.size := by
  subst isIdentity
  exact PolyTerm.lt_one_add base.size

/-- Decide equality of two dim-0 raw cells (both forced to be atoms). -/
def PolyTerm.decEqDimZero {profile : PolyProfile}
    (left right : PolyTerm profile 0) : Decidable (left = right) := by
  cases left with
  | atom leftCellId leftPayload =>
    cases right with
    | atom rightCellId rightPayload =>
      exact
        match Nat.decEq leftCellId rightCellId,
            Nat.decEq leftPayload rightPayload with
        | isTrue hCellId, isTrue hPayload => isTrue (by rw [hCellId, hPayload])
        | isFalse hCellId, _ =>
            isFalse (fun cellsEq => hCellId (by injection cellsEq))
        | _, isFalse hPayload =>
            isFalse (fun cellsEq => hPayload (by injection cellsEq))

/-- Propext-free decidable equality on `PolyTerm profile dim`.

Dispatch on the dimension is a primitive `Nat` match.  At positive dimension
both cells are decomposed via `succShape`; the four diagonal pairs recurse on
children (well-founded on `PolyTerm.size`) and the twelve constructor mismatches
are rejected by `injection`. -/
def PolyTerm.decEq {profile : PolyProfile} :
    {dim : CellDim} → (left right : PolyTerm profile dim) →
      Decidable (left = right)
  | 0, left, right => PolyTerm.decEqDimZero left right
  | _ + 1, left, right =>
      match PolyTerm.succShape left, PolyTerm.succShape right with
      | .ofCell lRule lSrc lTgt _ lIs, .ofCell rRule rSrc rTgt _ rIs =>
          match Nat.decEq lRule rRule,
              PolyTerm.decEq lSrc rSrc, PolyTerm.decEq lTgt rTgt with
          | isTrue hRule, isTrue hSrc, isTrue hTgt =>
              isTrue (by rw [lIs, rIs, hRule, hSrc, hTgt])
          | isFalse hRule, _, _ =>
              isFalse (fun h => hRule (by rw [lIs, rIs] at h; injection h))
          | _, isFalse hSrc, _ =>
              isFalse (fun h => hSrc (by rw [lIs, rIs] at h; injection h))
          | _, _, isFalse hTgt =>
              isFalse (fun h => hTgt (by rw [lIs, rIs] at h; injection h))
      | .ofCompV lFst lSnd _ lIs, .ofCompV rFst rSnd _ rIs =>
          match PolyTerm.decEq lFst rFst, PolyTerm.decEq lSnd rSnd with
          | isTrue hFst, isTrue hSnd => isTrue (by rw [lIs, rIs, hFst, hSnd])
          | isFalse hFst, _ =>
              isFalse (fun h => hFst (by rw [lIs, rIs] at h; injection h))
          | _, isFalse hSnd =>
              isFalse (fun h => hSnd (by rw [lIs, rIs] at h; injection h))
      | .ofCompH lLeft lRight _ lIs, .ofCompH rLeft rRight _ rIs =>
          match PolyTerm.decEq lLeft rLeft, PolyTerm.decEq lRight rRight with
          | isTrue hLeft, isTrue hRight => isTrue (by rw [lIs, rIs, hLeft, hRight])
          | isFalse hLeft, _ =>
              isFalse (fun h => hLeft (by rw [lIs, rIs] at h; injection h))
          | _, isFalse hRight =>
              isFalse (fun h => hRight (by rw [lIs, rIs] at h; injection h))
      | .ofIdentity lBase _ lIs, .ofIdentity rBase _ rIs =>
          match PolyTerm.decEq lBase rBase with
          | isTrue hBase => isTrue (by rw [lIs, rIs, hBase])
          | isFalse hBase =>
              isFalse (fun h => hBase (by rw [lIs, rIs] at h; injection h))
      | .ofCell _ _ _ _ lIs, .ofCompV _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCell _ _ _ _ lIs, .ofCompH _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCell _ _ _ _ lIs, .ofIdentity _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompV _ _ _ lIs, .ofCell _ _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompV _ _ _ lIs, .ofCompH _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompV _ _ _ lIs, .ofIdentity _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompH _ _ _ lIs, .ofCell _ _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompH _ _ _ lIs, .ofCompV _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofCompH _ _ _ lIs, .ofIdentity _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofIdentity _ _ lIs, .ofCell _ _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofIdentity _ _ lIs, .ofCompV _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
      | .ofIdentity _ _ lIs, .ofCompH _ _ _ rIs =>
          isFalse (fun h => by rw [lIs, rIs] at h; injection h)
  termination_by dim left _right => left.size
  decreasing_by
    all_goals
      simp_wf
      first
        | exact (PolyTerm.size_lt_of_isCell lIs).1
        | exact (PolyTerm.size_lt_of_isCell lIs).2
        | exact (PolyTerm.size_lt_of_isCompV lIs).1
        | exact (PolyTerm.size_lt_of_isCompV lIs).2
        | exact (PolyTerm.size_lt_of_isCompH lIs).1
        | exact (PolyTerm.size_lt_of_isCompH lIs).2
        | exact PolyTerm.size_lt_of_isIdentity lIs

instance instDecidableEqPolyTerm {profile : PolyProfile} {dim : CellDim} :
    DecidableEq (PolyTerm profile dim) := PolyTerm.decEq

end LeanFX2.Foundation.PolyCell.Core
