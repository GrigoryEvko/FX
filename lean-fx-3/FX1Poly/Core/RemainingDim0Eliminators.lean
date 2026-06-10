import FX1Poly.Core.NatEliminatorLayer

/-! # Foundation/PolyCell/Core/RemainingDim0Eliminators
   — full compositional layer for `listElim`, `optionMatch`, `eitherMatch`

The 3-child same-scope eliminator family.  Sibling to
`BoolEliminatorLayer` and `NatEliminatorLayer`.

## Contents (31 declarations)

`gen_listElim` has landed its Phase-Z motive shape (arity 4, `binderShifts = [1, 0, 0, 0]`, spine
`(motive, nilBranch, consBranch, scrutinee)` with the motive a term under one binder), so it carries
11 declarations:

  * INTRO (1): build HCC from 4 child cells (the motive at `scope + 1` + 3 same-scope children).
  * 4 PROJECTIONS: motive (head) + 2 branches + scrutinee (last).
  * Rename probe + preservation (2) — the motive head child renames under `RawRenaming.lift`.
  * Subst probe + preservation (2) — the motive head child substitutes under `RawTermSubst.lift`.
  * Subst0 probe + preservation (2) — the motive head child under the lifted singleton.

`gen_optionMatch` / `gen_eitherMatch` remain 3-child same-scope, 10 declarations each.

Child layouts:
  * `listElim`:    `(motive, nilBranch, consBranch, scrutinee)`  — Phase-Z, motive at `scope + 1`
  * `optionMatch`: `(scrutinee, noneBranch, someBranch)`
  * `eitherMatch`: `(scrutinee, leftBranch, rightBranch)`

`optionMatch`/`eitherMatch` are 3-child same-scope (no binder shifts) — `listElim` now follows the
Phase-Z boolElim template (motive head child under one binder).  (`IdEliminatorLayer` carries the
full dim-0 coverage table.)

## Zero-axiom verification

Each declaration follows the 3-child template from
`BoolEliminatorLayer` / `NatEliminatorLayer`.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## listElim -/

/-- **Intro: listElim's structural admission from 4 child cells** (Phase-Z motive shape: arity 4,
`binderShifts = [1, 0, 0, 0]`, spine `(motive, nilBranch, consBranch, scrutinee)` with the motive a term
under one binder, at `scope + 1`). -/
theorem HasCertifiedCellDim0.listElim
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 1)}
    {scrutineeTerm nilBranchTerm consBranchTerm : RawTerm scope}
    (motiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase motiveTerm))
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (nilBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase nilBranchTerm))
    (consBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase consBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_listElim ()
        (.childCons motiveTerm
          (.childCons nilBranchTerm
            (.childCons consBranchTerm
              (.childCons scrutineeTerm .childNil))))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_listElim
      (genPayloadEvidence (generator := .gen_listElim)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons nilBranchCell
          (CertifiedTermSpine.cons consBranchCell
            (CertifiedTermSpine.cons scrutineeCell
              CertifiedTermSpine.nil)))))

/-- **Projection: `gen_listElim` → motive child's cert** (the head child, at `scope + 1`). -/
theorem HasCertifiedCellDim0.listElim_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listElim ()
                (.childCons motiveTerm
                  (.childCons nilBranchTerm
                    (.childCons consBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_listElim` → nilBranch child's cert** (child 1). -/
theorem HasCertifiedCellDim0.listElim_nilBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listElim ()
                (.childCons motiveTerm
                  (.childCons nilBranchTerm
                    (.childCons consBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) nilBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_listElim` → consBranch child's cert** (child 2). -/
theorem HasCertifiedCellDim0.listElim_consBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listElim ()
                (.childCons motiveTerm
                  (.childCons nilBranchTerm
                    (.childCons consBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) consBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_listElim` → scrutinee child's cert** (the LAST child, child 3). -/
theorem HasCertifiedCellDim0.listElim_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_listElim ()
                (.childCons motiveTerm
                  (.childCons nilBranchTerm
                    (.childCons consBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_listElim`.**  The motive head child (binderShift `1`) renames under
the LIFTED renaming `RawRenaming.lift rawRenaming`; the three same-scope children under the plain `rawRenaming`. -/
theorem RawTerm.rename_listElim_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_listElim ()
        (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming nilBranchTerm)
            (.childCons (RawTerm.rename rawRenaming consBranchTerm)
              (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`listElim` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.listElim_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm sourceScope)
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)))
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedNilBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming nilBranchTerm)))
    (renamedConsBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming consBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.rename_listElim_reduces]
  exact HasCertifiedCellDim0.listElim renamedMotiveCell renamedScrutineeCell
    renamedNilBranchCell renamedConsBranchCell

/-- **Probe: subst distributes over `gen_listElim`.**  The motive head child (binderShift `1`) substitutes
under the LIFTED substitution `RawTermSubst.lift substitution`; the three same-scope children under the plain
`substitution`. -/
theorem RawTerm.subst_listElim_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_listElim ()
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)
          (.childCons (RawTerm.subst substitution nilBranchTerm)
            (.childCons (RawTerm.subst substitution consBranchTerm)
              (.childCons (RawTerm.subst substitution scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`listElim` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.listElim_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm sourceScope)
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substNilBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution nilBranchTerm)))
    (substConsBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution consBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.subst_listElim_reduces]
  exact HasCertifiedCellDim0.listElim substMotiveCell substScrutineeCell
    substNilBranchCell substConsBranchCell

/-- **Probe: subst0 distributes over `gen_listElim`.**  The cell lives at `scope + 1`, so its motive head child
lives at `scope + 2`; under subst0 that motive substitutes with the LIFTED singleton
`RawTermSubst.lift (RawTermSubst.singleton rawArg)`, while the three same-scope children (at `scope + 1`) use
`RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_listElim_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_listElim ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)
          (.childCons (RawTerm.subst0 nilBranchTerm rawArg)
            (.childCons (RawTerm.subst0 consBranchTerm rawArg)
              (.childCons (RawTerm.subst0 scrutineeTerm rawArg) .childNil))))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_listElim`** (Phase-Z motive shape: the motive head child substitutes
under the lifted singleton). -/
theorem HasCertifiedCellDim0.subst0_listElim_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm nilBranchTerm consBranchTerm : RawTerm (scope + 1))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substNilBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 nilBranchTerm rawArg)))
    (substConsBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 consBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_listElim ()
          (.childCons motiveTerm
            (.childCons nilBranchTerm
              (.childCons consBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_listElim_reduces]
  exact HasCertifiedCellDim0.listElim substMotiveCell substScrutineeCell
    substNilBranchCell substConsBranchCell

/-! ## optionMatch -/

/-- **Intro: optionMatch's structural admission from 3 child cells.** -/
theorem HasCertifiedCellDim0.optionMatch
    {profile : PolyProfile} {scope : Nat}
    {scrutineeTerm noneBranchTerm someBranchTerm : RawTerm scope}
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (noneBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase noneBranchTerm))
    (someBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase someBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_optionMatch ()
        (.childCons scrutineeTerm
          (.childCons noneBranchTerm
            (.childCons someBranchTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_optionMatch
      (genPayloadEvidence (generator := .gen_optionMatch)
                           (scope := scope) ())
      (CertifiedTermSpine.cons scrutineeCell
        (CertifiedTermSpine.cons noneBranchCell
          (CertifiedTermSpine.cons someBranchCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_optionMatch` → scrutinee child's cert.** -/
theorem HasCertifiedCellDim0.optionMatch_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_optionMatch ()
                (.childCons scrutineeTerm
                  (.childCons noneBranchTerm
                    (.childCons someBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_optionMatch` → noneBranch child's cert.** -/
theorem HasCertifiedCellDim0.optionMatch_noneBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_optionMatch ()
                (.childCons scrutineeTerm
                  (.childCons noneBranchTerm
                    (.childCons someBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) noneBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_optionMatch` → someBranch child's cert.** -/
theorem HasCertifiedCellDim0.optionMatch_someBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_optionMatch ()
                (.childCons scrutineeTerm
                  (.childCons noneBranchTerm
                    (.childCons someBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) someBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_optionMatch`.** -/
theorem RawTerm.rename_optionMatch_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_optionMatch ()
        (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
          (.childCons (RawTerm.rename rawRenaming noneBranchTerm)
            (.childCons (RawTerm.rename rawRenaming someBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`optionMatch` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.optionMatch_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm sourceScope)
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedNoneBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming noneBranchTerm)))
    (renamedSomeBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming someBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))) := by
  rw [RawTerm.rename_optionMatch_reduces]
  exact HasCertifiedCellDim0.optionMatch renamedScrutineeCell
    renamedNoneBranchCell renamedSomeBranchCell

/-- **Probe: subst distributes over `gen_optionMatch`.** -/
theorem RawTerm.subst_optionMatch_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_optionMatch ()
        (.childCons (RawTerm.subst substitution scrutineeTerm)
          (.childCons (RawTerm.subst substitution noneBranchTerm)
            (.childCons (RawTerm.subst substitution someBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`optionMatch` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.optionMatch_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm sourceScope)
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substNoneBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution noneBranchTerm)))
    (substSomeBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution someBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))) := by
  rw [RawTerm.subst_optionMatch_reduces]
  exact HasCertifiedCellDim0.optionMatch substScrutineeCell
    substNoneBranchCell substSomeBranchCell

/-- **Probe: subst0 distributes over `gen_optionMatch`.** -/
theorem RawTerm.subst0_optionMatch_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_optionMatch ()
        (.childCons (RawTerm.subst0 scrutineeTerm rawArg)
          (.childCons (RawTerm.subst0 noneBranchTerm rawArg)
            (.childCons (RawTerm.subst0 someBranchTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_optionMatch`.** -/
theorem HasCertifiedCellDim0.subst0_optionMatch_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (scrutineeTerm noneBranchTerm someBranchTerm : RawTerm (scope + 1))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substNoneBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 noneBranchTerm rawArg)))
    (substSomeBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 someBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_optionMatch ()
          (.childCons scrutineeTerm
            (.childCons noneBranchTerm
              (.childCons someBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_optionMatch_reduces]
  exact HasCertifiedCellDim0.optionMatch substScrutineeCell
    substNoneBranchCell substSomeBranchCell

/-! ## eitherMatch -/

/-- **Intro: eitherMatch's structural admission from 3 child cells.** -/
theorem HasCertifiedCellDim0.eitherMatch
    {profile : PolyProfile} {scope : Nat}
    {scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm scope}
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (leftBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase leftBranchTerm))
    (rightBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase rightBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_eitherMatch ()
        (.childCons scrutineeTerm
          (.childCons leftBranchTerm
            (.childCons rightBranchTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_eitherMatch
      (genPayloadEvidence (generator := .gen_eitherMatch)
                           (scope := scope) ())
      (CertifiedTermSpine.cons scrutineeCell
        (CertifiedTermSpine.cons leftBranchCell
          (CertifiedTermSpine.cons rightBranchCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_eitherMatch` → scrutinee child's cert.** -/
theorem HasCertifiedCellDim0.eitherMatch_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_eitherMatch ()
                (.childCons scrutineeTerm
                  (.childCons leftBranchTerm
                    (.childCons rightBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_eitherMatch` → leftBranch child's cert.** -/
theorem HasCertifiedCellDim0.eitherMatch_leftBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_eitherMatch ()
                (.childCons scrutineeTerm
                  (.childCons leftBranchTerm
                    (.childCons rightBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) leftBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_eitherMatch` → rightBranch child's cert.** -/
theorem HasCertifiedCellDim0.eitherMatch_rightBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_eitherMatch ()
                (.childCons scrutineeTerm
                  (.childCons leftBranchTerm
                    (.childCons rightBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) rightBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_eitherMatch`.** -/
theorem RawTerm.rename_eitherMatch_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_eitherMatch ()
        (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
          (.childCons (RawTerm.rename rawRenaming leftBranchTerm)
            (.childCons (RawTerm.rename rawRenaming rightBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`eitherMatch` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.eitherMatch_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm sourceScope)
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedLeftBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming leftBranchTerm)))
    (renamedRightBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming rightBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))) := by
  rw [RawTerm.rename_eitherMatch_reduces]
  exact HasCertifiedCellDim0.eitherMatch renamedScrutineeCell
    renamedLeftBranchCell renamedRightBranchCell

/-- **Probe: subst distributes over `gen_eitherMatch`.** -/
theorem RawTerm.subst_eitherMatch_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_eitherMatch ()
        (.childCons (RawTerm.subst substitution scrutineeTerm)
          (.childCons (RawTerm.subst substitution leftBranchTerm)
            (.childCons (RawTerm.subst substitution rightBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`eitherMatch` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.eitherMatch_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm sourceScope)
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substLeftBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution leftBranchTerm)))
    (substRightBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution rightBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))) := by
  rw [RawTerm.subst_eitherMatch_reduces]
  exact HasCertifiedCellDim0.eitherMatch substScrutineeCell
    substLeftBranchCell substRightBranchCell

/-- **Probe: subst0 distributes over `gen_eitherMatch`.** -/
theorem RawTerm.subst0_eitherMatch_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_eitherMatch ()
        (.childCons (RawTerm.subst0 scrutineeTerm rawArg)
          (.childCons (RawTerm.subst0 leftBranchTerm rawArg)
            (.childCons (RawTerm.subst0 rightBranchTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_eitherMatch`.** -/
theorem HasCertifiedCellDim0.subst0_eitherMatch_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (scrutineeTerm leftBranchTerm rightBranchTerm : RawTerm (scope + 1))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substLeftBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 leftBranchTerm rawArg)))
    (substRightBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 rightBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_eitherMatch ()
          (.childCons scrutineeTerm
            (.childCons leftBranchTerm
              (.childCons rightBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_eitherMatch_reduces]
  exact HasCertifiedCellDim0.eitherMatch substScrutineeCell
    substLeftBranchCell substRightBranchCell

end FX1Poly.Core
