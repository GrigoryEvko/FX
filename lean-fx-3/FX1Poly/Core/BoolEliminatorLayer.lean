import FX1Poly.Core.PairEliminatorLayer

/-! # Foundation/PolyCell/Core/BoolEliminatorLayer
   — full compositional layer for `gen_boolElim`

Sibling to `PairEliminatorLayer`; extends eliminator coverage to
the 4-child boolean eliminator `gen_boolElim` in its Phase-Z motive
shape (arity 4, binderShifts `[1, 0, 0, 0]`, children
`(motive, thenBranch, elseBranch, scrutinee)` with the motive a term
under one binder, scrutinee LAST).

## What this file ships

11 declarations for `gen_boolElim`:

  * **Intro** (1): build `HCC (boolElim m t e s)` from
    `HCC m`, `HCC s`, `HCC t`, `HCC e`.
  * **Projections** (4): extract each child cert from the
    boolElim cert (motive / thenBranch / elseBranch / scrutinee).
  * **Rename probe + preservation** (2): distributivity + rebuild
    (the motive child renamed under the LIFTED renaming).
  * **Subst probe + preservation** (2): same under generic subst
    (the motive child substituted under the LIFTED substitution).
  * **Subst0 probe + preservation** (2): beta-redex compositional
    (the motive child substituted under the LIFTED singleton).

## Why boolElim matters for SR-cong

For `Step.cong` on `boolElim m t e s → boolElim m t e s'` (when
`s → s'`), the chain needs:
  1. PROJECTIONS: extract `m, s, t, e` certs from boolElim cert.
  2. STEP: `s → s'` preserves `HCC` via the step's SR arm.
  3. REBUILD: combine `HCC m`, `HCC s'`, `HCC t`, `HCC e` via the intro.

Same template for steps in the thenBranch or elseBranch position
(different projection chain but same shape).  The motive child is a
binder-shifted child (the `gen_lam` body template): its rename/subst
distribution carries the LIFTED renaming/substitution.

## Coverage progress

| Surface                  | Generators |
|--------------------------|------------|
| Term constructors        | var, unit, boolTrue/False, natZero, listNil, optionNone, app, pair, listCons, natSucc, optionSome, eitherInl/Inr, refl, lam (16) |
| Pair eliminators         | fst, snd (2) |
| Boolean eliminator       | boolElim (1, Phase-Z motive shape) |
| Total                    | **19**     |

## Zero-axiom verification

Each declaration follows the proven template from
`PairEliminatorLayer` extended to 3 children.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Intro -/

/-- **Intro: boolElim's structural admission from 4 child cells** (Phase-Z motive shape: the motive head child
lives at `scope + 1`, the three remaining children at the ambient `scope`). -/
theorem HasCertifiedCellDim0.boolElim
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 1)}
    {scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope}
    (motiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase motiveTerm))
    (scrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase scrutineeTerm))
    (thenBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase thenBranchTerm))
    (elseBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase elseBranchTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_boolElim ()
        (.childCons motiveTerm
          (.childCons thenBranchTerm
            (.childCons elseBranchTerm
              (.childCons scrutineeTerm .childNil))))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_boolElim
      (genPayloadEvidence (generator := .gen_boolElim)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons thenBranchCell
          (CertifiedTermSpine.cons elseBranchCell
            (CertifiedTermSpine.cons scrutineeCell
              CertifiedTermSpine.nil)))))

/-! ## Section 2 — Projections (4 children)

Phase-Z motive shape: the motive is the head child (drilled by `headAtDim0`, landing a cell at `scope + 1`);
the then- and else-branches stay at positions 1/2; the scrutinee moved to the LAST position (child 3), so its
projection drills three tails. -/

/-- **Projection: `gen_boolElim` → motive child's cert** (the head child, at `scope + 1`). -/
theorem HasCertifiedCellDim0.boolElim_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons motiveTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_boolElim` → thenBranch child's cert** (child 1). -/
theorem HasCertifiedCellDim0.boolElim_thenBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons motiveTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) thenBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_boolElim` → elseBranch child's cert** (child 2). -/
theorem HasCertifiedCellDim0.boolElim_elseBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons motiveTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) elseBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_boolElim` → scrutinee child's cert** (the LAST child, child 3). -/
theorem HasCertifiedCellDim0.boolElim_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons motiveTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm
                      (.childCons scrutineeTerm .childNil)))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.tail.headAtDim0 rfl⟩

/-! ## Section 3 — Rename reduction probe + preservation -/

/-- **Probe: rename distributes over `gen_boolElim`.**  The motive head child (binderShift `1`) renames under
the LIFTED renaming `RawRenaming.lift rawRenaming` — the `gen_lam` body-child template; the three same-scope
children rename under the plain `rawRenaming`. -/
theorem RawTerm.rename_boolElim_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_boolElim ()
        (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming thenBranchTerm)
            (.childCons (RawTerm.rename rawRenaming elseBranchTerm)
              (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`boolElim` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.boolElim_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope)
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift rawRenaming) motiveTerm)))
    (renamedScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming scrutineeTerm)))
    (renamedThenBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming thenBranchTerm)))
    (renamedElseBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming elseBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.rename_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim renamedMotiveCell renamedScrutineeCell
    renamedThenBranchCell renamedElseBranchCell

/-! ## Section 4 — Subst reduction probe + preservation -/

/-- **Probe: subst distributes over `gen_boolElim`.**  The motive head child (binderShift `1`) substitutes
under the LIFTED substitution `RawTermSubst.lift substitution`; the three same-scope children under the plain
`substitution`. -/
theorem RawTerm.subst_boolElim_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_boolElim ()
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)
          (.childCons (RawTerm.subst substitution thenBranchTerm)
            (.childCons (RawTerm.subst substitution elseBranchTerm)
              (.childCons (RawTerm.subst substitution scrutineeTerm)
                .childNil)))))
        : RawTerm targetScope) := rfl

/-- **`boolElim` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.boolElim_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 1))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope)
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift substitution) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution scrutineeTerm)))
    (substThenBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution thenBranchTerm)))
    (substElseBranchCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution elseBranchTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))) := by
  rw [RawTerm.subst_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim substMotiveCell substScrutineeCell
    substThenBranchCell substElseBranchCell

/-! ## Section 5 — Subst0 (beta-redex) reduction probe + preservation -/

/-- **Probe: subst0 distributes over `gen_boolElim`.**  The cell lives at `scope + 1`, so its motive head child
lives at `scope + 2`; under subst0 that motive substitutes with the LIFTED singleton
`RawTermSubst.lift (RawTermSubst.singleton rawArg)` (the `gen_lam` body-child template), while the three
same-scope children (at `scope + 1`) use `RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_boolElim_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_boolElim ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)
          (.childCons (RawTerm.subst0 thenBranchTerm rawArg)
            (.childCons (RawTerm.subst0 elseBranchTerm rawArg)
              (.childCons (RawTerm.subst0 scrutineeTerm rawArg) .childNil))))
        : RawTerm scope) := rfl

/-- **Beta-redex: `(lam (.gen_boolElim () [m, t, e, s])) outerArg →
    .gen_boolElim () [subst-lift m, subst0 t, subst0 e, subst0 s]`.** -/
theorem HasCertifiedCellDim0.subst0_boolElim_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 2))
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm (scope + 1))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton rawArg)) motiveTerm)))
    (substScrutineeCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 scrutineeTerm rawArg)))
    (substThenBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 thenBranchTerm rawArg)))
    (substElseBranchCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 elseBranchTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_boolElim ()
          (.childCons motiveTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm
                (.childCons scrutineeTerm .childNil)))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim substMotiveCell substScrutineeCell
    substThenBranchCell substElseBranchCell

end FX1Poly.Core
