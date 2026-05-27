import LeanFX2.Foundation.PolyCell.Core.PairEliminatorLayer

/-! # Foundation/PolyCell/Core/BoolEliminatorLayer
   — full compositional layer for `gen_boolElim`

V2-L3.1 phase D step 23 (2026-05-27).  Sibling to step 22
(`PairEliminatorLayer`); extends eliminator coverage to the
3-child boolean eliminator `gen_boolElim`.

## What this file ships

10 declarations for `gen_boolElim`:

  * **Intro** (1): build `HCC (boolElim s t e)` from
    `HCC s`, `HCC t`, `HCC e`.
  * **Projections** (3): extract each child cert from the
    boolElim cert (scrutinee / thenBranch / elseBranch).
  * **Rename probe + preservation** (2): distributivity + rebuild.
  * **Subst probe + preservation** (2): same under generic subst.
  * **Subst0 probe + preservation** (2): beta-redex compositional.

## Why boolElim matters for SR-cong

For `Step.cong` on `boolElim s t e → boolElim s' t e` (when
`s → s'`), the chain needs:
  1. PROJECTIONS: extract `s, t, e` certs from boolElim cert.
  2. STEP: `s → s'` preserves `HCC` via the step's SR arm.
  3. REBUILD: combine `HCC s'`, `HCC t`, `HCC e` via the intro.

Same template for steps in the thenBranch or elseBranch position
(different projection chain but same shape).

## Coverage progress

| Surface                  | Generators |
|--------------------------|------------|
| Term constructors        | var, unit, boolTrue/False, natZero, listNil, optionNone, app, pair, listCons, natSucc, optionSome, eitherInl/Inr, refl, lam (16) |
| Pair eliminators         | fst, snd (2) |
| Boolean eliminator (NEW) | boolElim (1) |
| Total                    | **19**     |

## Zero-axiom verification

Each declaration follows the proven template from
`PairEliminatorLayer` extended to 3 children.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Intro -/

/-- **Intro: boolElim's structural admission from 3 child cells.** -/
theorem HasCertifiedCellDim0.boolElim
    {profile : PolyProfile} {scope : Nat}
    {scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope}
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
        (.childCons scrutineeTerm
          (.childCons thenBranchTerm
            (.childCons elseBranchTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_boolElim
      (genPayloadEvidence (generator := .gen_boolElim)
                           (scope := scope) ())
      (CertifiedTermSpine.cons scrutineeCell
        (CertifiedTermSpine.cons thenBranchCell
          (CertifiedTermSpine.cons elseBranchCell
            CertifiedTermSpine.nil))))

/-! ## Section 2 — Projections (3 children) -/

/-- **Projection: `gen_boolElim` → scrutinee child's cert.** -/
theorem HasCertifiedCellDim0.boolElim_scrutinee_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons scrutineeTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) scrutineeTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_boolElim` → thenBranch child's cert.** -/
theorem HasCertifiedCellDim0.boolElim_thenBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons scrutineeTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) thenBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_boolElim` → elseBranch child's cert.** -/
theorem HasCertifiedCellDim0.boolElim_elseBranch_projection
    {profile : PolyProfile} {scope : Nat}
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_boolElim ()
                (.childCons scrutineeTerm
                  (.childCons thenBranchTerm
                    (.childCons elseBranchTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) elseBranchTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-! ## Section 3 — Rename reduction probe + preservation -/

/-- **Probe: rename distributes over `gen_boolElim`.** -/
theorem RawTerm.rename_boolElim_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_boolElim ()
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_boolElim ()
        (.childCons (RawTerm.rename rawRenaming scrutineeTerm)
          (.childCons (RawTerm.rename rawRenaming thenBranchTerm)
            (.childCons (RawTerm.rename rawRenaming elseBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`boolElim` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.boolElim_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope)
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
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))) := by
  rw [RawTerm.rename_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim renamedScrutineeCell
    renamedThenBranchCell renamedElseBranchCell

/-! ## Section 4 — Subst reduction probe + preservation -/

/-- **Probe: subst distributes over `gen_boolElim`.** -/
theorem RawTerm.subst_boolElim_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_boolElim ()
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_boolElim ()
        (.childCons (RawTerm.subst substitution scrutineeTerm)
          (.childCons (RawTerm.subst substitution thenBranchTerm)
            (.childCons (RawTerm.subst substitution elseBranchTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`boolElim` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.boolElim_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm sourceScope)
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
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))) := by
  rw [RawTerm.subst_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim substScrutineeCell
    substThenBranchCell substElseBranchCell

/-! ## Section 5 — Subst0 (beta-redex) reduction probe + preservation -/

/-- **Probe: subst0 distributes over `gen_boolElim`.** -/
theorem RawTerm.subst0_boolElim_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_boolElim ()
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_boolElim ()
        (.childCons (RawTerm.subst0 scrutineeTerm rawArg)
          (.childCons (RawTerm.subst0 thenBranchTerm rawArg)
            (.childCons (RawTerm.subst0 elseBranchTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex: `(lam (.gen_boolElim () [s, t, e])) outerArg →
    .gen_boolElim () [subst0 s, subst0 t, subst0 e]`.** -/
theorem HasCertifiedCellDim0.subst0_boolElim_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (scrutineeTerm thenBranchTerm elseBranchTerm : RawTerm (scope + 1))
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
          (.childCons scrutineeTerm
            (.childCons thenBranchTerm
              (.childCons elseBranchTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_boolElim_reduces]
  exact HasCertifiedCellDim0.boolElim substScrutineeCell
    substThenBranchCell substElseBranchCell

end LeanFX2.Foundation.PolyCell.Core
