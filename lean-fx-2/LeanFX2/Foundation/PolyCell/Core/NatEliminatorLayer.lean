import LeanFX2.Foundation.PolyCell.Core.BoolEliminatorLayer

/-! # Foundation/PolyCell/Core/NatEliminatorLayer
   — full compositional layer for `gen_natElim` and `gen_natRec`

V2-L3.1 phase D step 24 (2026-05-27).  Sibling to step 23
(`BoolEliminatorLayer`); extends eliminator coverage to the two
natural-number eliminators (large-elim `natElim` and recursor
`natRec`), both 3-child same-scope.

## Child layout (shared by both generators)

`(scrutinee, zeroBranch, succBranch)` — same as boolElim's
`(scrutinee, thenBranch, elseBranch)` modulo names.  No binder
shifts (all children at same scope as parent).

## What this file ships (20 declarations)

For each of `gen_natElim` and `gen_natRec`, 10 declarations:

  * **Intro** (1 per generator): build HCC from 3 child cells.
  * **Projections** (3 per generator): scrutinee / zeroBranch /
    succBranch.
  * **Rename probe + preservation** (2 per generator).
  * **Subst probe + preservation** (2 per generator).
  * **Subst0 probe + preservation** (2 per generator).

## Coverage progress

| Surface                     | Generators                | Count |
|-----------------------------|---------------------------|-------|
| Term constructors           | var, unit, etc. (16)      | 16    |
| Pair eliminators            | fst, snd                  | 2     |
| Boolean eliminator          | boolElim                  | 1     |
| Nat eliminators (NEW)       | natElim, natRec           | 2     |
| **Total**                   |                           | **21** |

## Zero-axiom verification

Each declaration follows the proven 3-child template from
`BoolEliminatorLayer`.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## natElim — large elimination for naturals -/

/-- **Intro: natElim's structural admission from 3 child cells.** -/
theorem HasCertifiedCellDim0.natElim
    {profile : PolyProfile} {scope : Nat}
    {scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope}
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (zeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranchTerm))
    (succBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase succBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_natElim ()
        (.childCons scrutineeTerm
          (.childCons zeroBranchTerm
            (.childCons succBranchTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natElim
      (genPayloadEvidence (generator := .gen_natElim)
                           (scope := scope) ())
      (CertifiedTermSpine.cons scrutineeCell
        (CertifiedTermSpine.cons zeroBranchCell
          (CertifiedTermSpine.cons succBranchCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_natElim` → scrutinee child's cert.** -/
theorem HasCertifiedCellDim0.natElim_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_natElim` → zeroBranch child's cert.** -/
theorem HasCertifiedCellDim0.natElim_zeroBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natElim` → succBranch child's cert.** -/
theorem HasCertifiedCellDim0.natElim_succBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natElim ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) succBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_natElim`.** -/
theorem RawTerm.rename_natElim_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natElim ()
        (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
          (.childCons (RawTerm.rename rawRenaming zeroBranchTerm)
            (.childCons (RawTerm.rename rawRenaming succBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`natElim` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.natElim_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope)
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming zeroBranchTerm)))
    (renamedSuccBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))) := by
  rw [RawTerm.rename_natElim_reduces]
  exact HasCertifiedCellDim0.natElim renamedScrutineeCell
    renamedZeroBranchCell renamedSuccBranchCell

/-- **Probe: subst distributes over `gen_natElim`.** -/
theorem RawTerm.subst_natElim_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natElim ()
        (.childCons (RawTerm.subst substitution scrutineeTerm)
          (.childCons (RawTerm.subst substitution zeroBranchTerm)
            (.childCons (RawTerm.subst substitution succBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`natElim` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.natElim_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope)
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution zeroBranchTerm)))
    (substSuccBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))) := by
  rw [RawTerm.subst_natElim_reduces]
  exact HasCertifiedCellDim0.natElim substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-- **Probe: subst0 distributes over `gen_natElim`.** -/
theorem RawTerm.subst0_natElim_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_natElim ()
        (.childCons (RawTerm.subst0 scrutineeTerm rawArg)
          (.childCons (RawTerm.subst0 zeroBranchTerm rawArg)
            (.childCons (RawTerm.subst0 succBranchTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex: `(lam (.gen_natElim () [s, z, k])) outerArg →
    .gen_natElim () [subst0 s, subst0 z, subst0 k]`.** -/
theorem HasCertifiedCellDim0.subst0_natElim_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm (scope + 1))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substZeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 zeroBranchTerm rawArg)))
    (substSuccBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 succBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_natElim ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_natElim_reduces]
  exact HasCertifiedCellDim0.natElim substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-! ## natRec — small recursor for naturals -/

/-- **Intro: natRec's structural admission from 3 child cells.** -/
theorem HasCertifiedCellDim0.natRec
    {profile : PolyProfile} {scope : Nat}
    {scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope}
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (zeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranchTerm))
    (succBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase succBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_natRec ()
        (.childCons scrutineeTerm
          (.childCons zeroBranchTerm
            (.childCons succBranchTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_natRec
      (genPayloadEvidence (generator := .gen_natRec)
                           (scope := scope) ())
      (CertifiedTermSpine.cons scrutineeCell
        (CertifiedTermSpine.cons zeroBranchCell
          (CertifiedTermSpine.cons succBranchCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_natRec` → scrutinee child's cert.** -/
theorem HasCertifiedCellDim0.natRec_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_natRec` → zeroBranch child's cert.** -/
theorem HasCertifiedCellDim0.natRec_zeroBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) zeroBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_natRec` → succBranch child's cert.** -/
theorem HasCertifiedCellDim0.natRec_succBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_natRec ()
                (.childCons scrutineeTerm
                  (.childCons zeroBranchTerm
                    (.childCons succBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) succBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_natRec`.** -/
theorem RawTerm.rename_natRec_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natRec ()
        (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
          (.childCons (RawTerm.rename rawRenaming zeroBranchTerm)
            (.childCons (RawTerm.rename rawRenaming succBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`natRec` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.natRec_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope)
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming zeroBranchTerm)))
    (renamedSuccBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))) := by
  rw [RawTerm.rename_natRec_reduces]
  exact HasCertifiedCellDim0.natRec renamedScrutineeCell
    renamedZeroBranchCell renamedSuccBranchCell

/-- **Probe: subst distributes over `gen_natRec`.** -/
theorem RawTerm.subst_natRec_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_natRec ()
        (.childCons (RawTerm.subst substitution scrutineeTerm)
          (.childCons (RawTerm.subst substitution zeroBranchTerm)
            (.childCons (RawTerm.subst substitution succBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`natRec` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.natRec_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm sourceScope)
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substZeroBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution zeroBranchTerm)))
    (substSuccBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution succBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))) := by
  rw [RawTerm.subst_natRec_reduces]
  exact HasCertifiedCellDim0.natRec substScrutineeCell
    substZeroBranchCell substSuccBranchCell

/-- **Probe: subst0 distributes over `gen_natRec`.** -/
theorem RawTerm.subst0_natRec_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_natRec ()
        (.childCons (RawTerm.subst0 scrutineeTerm rawArg)
          (.childCons (RawTerm.subst0 zeroBranchTerm rawArg)
            (.childCons (RawTerm.subst0 succBranchTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex: `(lam (.gen_natRec () [s, z, k])) outerArg →
    .gen_natRec () [subst0 s, subst0 z, subst0 k]`.** -/
theorem HasCertifiedCellDim0.subst0_natRec_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (scrutineeTerm zeroBranchTerm succBranchTerm : RawTerm (scope + 1))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substZeroBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 zeroBranchTerm rawArg)))
    (substSuccBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 succBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_natRec ()
          (.childCons scrutineeTerm
            (.childCons zeroBranchTerm
              (.childCons succBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_natRec_reduces]
  exact HasCertifiedCellDim0.natRec substScrutineeCell
    substZeroBranchCell substSuccBranchCell

end LeanFX2.Foundation.PolyCell.Core
