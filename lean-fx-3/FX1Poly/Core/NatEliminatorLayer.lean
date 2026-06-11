import FX1Poly.Core.BoolEliminatorLayer

/-! # Foundation/PolyCell/Core/NatEliminatorLayer
   — full compositional layer for `gen_natElim` and `gen_natRec`

Sibling to `BoolEliminatorLayer`; the compositional layer for the
two natural-number eliminators (large-elim `natElim` and recursor
`natRec`), both now Phase-Z 4-child with a stored motive.

## Child layout (shared by both generators)

`(motive, zeroBranch, succBranch, scrutinee)` with `binderShifts
[1, 0, 2, 0]`: the motive is a term under ONE binder (at
`scope + 1`), the succBranch a term under TWO binders (at
`scope + 2`, with var 0 the inductive hypothesis and var 1 the
predecessor), and the scrutinee LAST.  Mirrors `listElim`'s Phase-Z
shape (`RemainingDim0Eliminators`) but with the deeper succ-branch
binder — natElim/natRec are the FIRST shift-2 admissions.

## Contents (per generator)

For each of `gen_natElim` and `gen_natRec`:

  * **Intro** (1 per generator): build HCC from 4 child cells.
  * **Projections** (4 per generator): motive / zeroBranch /
    succBranch / scrutinee.
  * **Rename probe + preservation** (2 per generator): the motive
    head renames under `RawRenaming.lift`, the succ-branch under
    `RawRenaming.lift (RawRenaming.lift …)`.
  * **Subst probe + preservation** (2 per generator): the motive
    under `RawTermSubst.lift`, the succ-branch under the
    double-lifted substitution.
  * **Subst0 probe + preservation** (2 per generator).

## Zero-axiom verification

Each declaration follows the Phase-Z 4-child template from
`listElim` (`RemainingDim0Eliminators`).  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## natElim — large elimination for naturals -/

/-- **Intro: natElim's structural admission from 4 child cells** (Phase-Z motive shape: arity 4,
`binderShifts = [1, 0, 2, 0]`, spine `(motive, zeroBranch, succBranch, scrutinee)` with the motive at
`scope + 1` and the succ-branch at `scope + 2`). -/
theorem HasCertifiedCellDim0.natElim
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 1)}
    {scrutineeTerm zeroBranchTerm : RawTerm scope}
    {succBranchTerm : RawTerm (scope + 2)}
    (motiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase motiveTerm))
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (zeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranchTerm))
    (succBranchCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase succBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_natElim ()
        (.childCons motiveTerm
          (.childCons zeroBranchTerm
            (.childCons succBranchTerm
              (.childCons scrutineeTerm .childNil))))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natElim
      (genPayloadEvidence (generator := .gen_natElim)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons zeroBranchCell
          (CertifiedTermSpine.cons succBranchCell
            (CertifiedTermSpine.cons scrutineeCell
              CertifiedTermSpine.nil)))))

/-- **Projection: `gen_natElim` → motive child's cert** (the head child, at `scope + 1`). -/
theorem HasCertifiedCellDim0.natElim_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_natElim` → zeroBranch child's cert** (child 1). -/
theorem HasCertifiedCellDim0.natElim_zeroBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natElim` → succBranch child's cert** (child 2, at `scope + 2`). -/
theorem HasCertifiedCellDim0.natElim_succBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) succBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natElim` → scrutinee child's cert** (the LAST child, child 3). -/
theorem HasCertifiedCellDim0.natElim_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_natElim`.**  The motive head child (binderShift `1`) renames under
`RawRenaming.lift rawRenaming`; the succ-branch (binderShift `2`) under the double-lifted renaming; the two
same-scope children under the plain `rawRenaming`. -/
theorem RawTerm.rename_natElim_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2)) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natElim ()
        (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming zeroBranchTerm)
            (.childCons
              (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) succBranchTerm)
              (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`natElim` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.natElim_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2))
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)))
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming zeroBranchTerm)))
    (renamedSuccBranchCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.rename_natElim_reduces]
  exact HasCertifiedCellDim0.natElim renamedMotiveCell renamedScrutineeCell
    renamedZeroBranchCell renamedSuccBranchCell

/-- **Probe: subst distributes over `gen_natElim`.**  The motive head child (binderShift `1`) substitutes under
`RawTermSubst.lift substitution`; the succ-branch (binderShift `2`) under the double-lifted substitution; the
two same-scope children under the plain `substitution`. -/
theorem RawTerm.subst_natElim_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2)) :
    RawTerm.subst substitution
        ((.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natElim ()
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)
          (.childCons (RawTerm.subst substitution zeroBranchTerm)
            (.childCons
              (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranchTerm)
              (.childCons (RawTerm.subst substitution scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`natElim` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.natElim_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2))
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution zeroBranchTerm)))
    (substSuccBranchCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.subst_natElim_reduces]
  exact HasCertifiedCellDim0.natElim substMotiveCell substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-- **Probe: subst0 distributes over `gen_natElim`.**  The cell lives at `scope + 1`, so its motive head child
lives at `scope + 2` (motive substitutes with the LIFTED singleton) and the succ-branch at `scope + 3` (under
the double-lifted singleton); the two same-scope children (at `scope + 1`) use `RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_natElim_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm zeroBranchTerm : RawTerm (scope + 1))
    (succBranchTerm : RawTerm (scope + 3)) :
    RawTerm.subst0
        ((.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_natElim ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)
          (.childCons (RawTerm.subst0 zeroBranchTerm rawArg)
            (.childCons
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) succBranchTerm)
              (.childCons (RawTerm.subst0 scrutineeTerm rawArg) .childNil))))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_natElim`** (Phase-Z motive shape: the motive head child substitutes
under the lifted singleton, the succ-branch under the double-lifted singleton). -/
theorem HasCertifiedCellDim0.subst0_natElim_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm zeroBranchTerm : RawTerm (scope + 1))
    (succBranchTerm : RawTerm (scope + 3))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substZeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 zeroBranchTerm rawArg)))
    (substSuccBranchCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst
          (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_natElim ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_natElim_reduces]
  exact HasCertifiedCellDim0.natElim substMotiveCell substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-! ## natRec — small recursor for naturals -/

/-- **Intro: natRec's structural admission from 4 child cells** (Phase-Z motive shape: arity 4,
`binderShifts = [1, 0, 2, 0]`, spine `(motive, zeroBranch, succBranch, scrutinee)` with the motive at
`scope + 1` and the succ-branch at `scope + 2`). -/
theorem HasCertifiedCellDim0.natRec
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 1)}
    {scrutineeTerm zeroBranchTerm : RawTerm scope}
    {succBranchTerm : RawTerm (scope + 2)}
    (motiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase motiveTerm))
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (zeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranchTerm))
    (succBranchCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase succBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_natRec ()
        (.childCons motiveTerm
          (.childCons zeroBranchTerm
            (.childCons succBranchTerm
              (.childCons scrutineeTerm .childNil))))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natRec
      (genPayloadEvidence (generator := .gen_natRec)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons zeroBranchCell
          (CertifiedTermSpine.cons succBranchCell
            (CertifiedTermSpine.cons scrutineeCell
              CertifiedTermSpine.nil)))))

/-- **Projection: `gen_natRec` → motive child's cert** (the head child, at `scope + 1`). -/
theorem HasCertifiedCellDim0.natRec_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_natRec` → zeroBranch child's cert** (child 1). -/
theorem HasCertifiedCellDim0.natRec_zeroBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natRec` → succBranch child's cert** (child 2, at `scope + 2`). -/
theorem HasCertifiedCellDim0.natRec_succBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) succBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natRec` → scrutinee child's cert** (the LAST child, child 3). -/
theorem HasCertifiedCellDim0.natRec_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm scope)
    (succBranchTerm : RawTerm (scope + 2))
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons motiveTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_natRec`.**  The motive head child (binderShift `1`) renames under
`RawRenaming.lift rawRenaming`; the succ-branch (binderShift `2`) under the double-lifted renaming; the two
same-scope children under the plain `rawRenaming`. -/
theorem RawTerm.rename_natRec_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2)) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natRec ()
        (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming zeroBranchTerm)
            (.childCons
              (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) succBranchTerm)
              (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`natRec` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.natRec_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2))
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)))
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming zeroBranchTerm)))
    (renamedSuccBranchCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.rename_natRec_reduces]
  exact HasCertifiedCellDim0.natRec renamedMotiveCell renamedScrutineeCell
    renamedZeroBranchCell renamedSuccBranchCell

/-- **Probe: subst distributes over `gen_natRec`.**  The motive head child (binderShift `1`) substitutes under
`RawTermSubst.lift substitution`; the succ-branch (binderShift `2`) under the double-lifted substitution; the
two same-scope children under the plain `substitution`. -/
theorem RawTerm.subst_natRec_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2)) :
    RawTerm.subst substitution
        ((.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natRec ()
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)
          (.childCons (RawTerm.subst substitution zeroBranchTerm)
            (.childCons
              (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranchTerm)
              (.childCons (RawTerm.subst substitution scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`natRec` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.natRec_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm zeroBranchTerm : RawTerm sourceScope)
    (succBranchTerm : RawTerm (sourceScope + 2))
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution zeroBranchTerm)))
    (substSuccBranchCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.subst_natRec_reduces]
  exact HasCertifiedCellDim0.natRec substMotiveCell substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-- **Probe: subst0 distributes over `gen_natRec`.**  The cell lives at `scope + 1`, so its motive head child
lives at `scope + 2` (motive substitutes with the LIFTED singleton) and the succ-branch at `scope + 3` (under
the double-lifted singleton); the two same-scope children (at `scope + 1`) use `RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_natRec_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm zeroBranchTerm : RawTerm (scope + 1))
    (succBranchTerm : RawTerm (scope + 3)) :
    RawTerm.subst0
        ((.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_natRec ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)
          (.childCons (RawTerm.subst0 zeroBranchTerm rawArg)
            (.childCons
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) succBranchTerm)
              (.childCons (RawTerm.subst0 scrutineeTerm rawArg) .childNil))))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_natRec`** (Phase-Z motive shape: the motive head child substitutes
under the lifted singleton, the succ-branch under the double-lifted singleton). -/
theorem HasCertifiedCellDim0.subst0_natRec_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm zeroBranchTerm : RawTerm (scope + 1))
    (succBranchTerm : RawTerm (scope + 3))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substZeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 zeroBranchTerm rawArg)))
    (substSuccBranchCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst
          (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_natRec ()
          (.childCons motiveTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_natRec_reduces]
  exact HasCertifiedCellDim0.natRec substMotiveCell substScrutineeCell
    substZeroBranchCell substSuccBranchCell

end FX1Poly.Core
