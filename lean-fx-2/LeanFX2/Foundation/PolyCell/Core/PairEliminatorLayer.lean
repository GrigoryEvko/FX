import LeanFX2.Foundation.PolyCell.Core.HasCertifiedComposition
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedProjections
import LeanFX2.Foundation.PolyCell.Core.BetaRedexLeafPreservation
import LeanFX2.Foundation.PolyCell.Core.CompoundSubstPreservation

/-! # Foundation/PolyCell/Core/PairEliminatorLayer
   — full compositional layer for `gen_fst` and `gen_snd`

V2-L3.1 phase D step 22 (2026-05-27).  Extends the 16-generator
compositional surface to include the pair eliminators (`fst`/`snd`).
These are the FIRST eliminator generators to get full
intros + projections + preservations coverage.

## Why fst/snd matter for SR-cong

For Step.cong on `fst x → fst x'` (when `x → x'` via cong),
the SR-cong proof chain needs:

  1. **PROJECTION**: `HCC (fst x) → HCC x`
  2. **STEP preservation**: `HCC x` + step `x → x'` → `HCC x'`
  3. **REBUILD**: `HCC x'` → `HCC (fst x')` via the intro

Without intros/projections for fst, SR-cong for fst subterm steps
cannot close.  Same for snd.  This file ships both.

## What this file ships

For each of `gen_fst` and `gen_snd` (8 declarations each = 16 total):

  * **Intro**: build `HCC (.gen_X () [pair])` from `HCC pair`.
  * **Projection**: extract `HCC pair` from `HCC (.gen_X () [pair])`.
  * **Rename probe**: `rename ρ (.gen_X () [pair])
    = .gen_X () [rename ρ pair]` by `rfl`.
  * **Rename preservation**: `(renamed pair) cert` → `(renamed fst/snd) cert`.
  * **Subst probe**: same shape as rename probe.
  * **Subst preservation**: `(substituted pair) cert` → `(substituted fst/snd) cert`.
  * **Subst0 probe + preservation**: specialized to the beta-redex
    substitution.

## Coverage gap context

The existing 16-generator surface (var/unit/boolTrue/boolFalse/
natZero/listNil/optionNone + app/pair/listCons/natSucc/optionSome/
eitherInl/eitherInr/refl/lam) covers TERM CONSTRUCTORS but not
ELIMINATORS.  This file is the first step in extending coverage
to eliminators.  Future iterations can add `boolElim`, `natElim`,
`natRec`, `listElim`, `optionMatch`, `eitherMatch`, `idJ`,
`idStrictRec` following the same template.

## Zero-axiom verification

Spike (`Smoke/SpikeFstIntro.lean`, deleted) confirmed
`#print axioms HasCertifiedCellDim0.fstSpike` reports clean.
Each declaration follows the same recipe and is audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Intros (build HCC from pair cell) -/

/-- **Intro: fst's structural admission from pair cell.** -/
theorem HasCertifiedCellDim0.fst
    {profile : PolyProfile} {scope : Nat}
    {pairTerm : RawTerm scope}
    (pairCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase pairTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_fst ()
        (.childCons pairTerm .childNil)) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_fst
      (genPayloadEvidence (generator := .gen_fst)
                           (scope := scope) ())
      (CertifiedTermSpine.cons pairCell CertifiedTermSpine.nil))

/-- **Intro: snd's structural admission from pair cell.** -/
theorem HasCertifiedCellDim0.snd
    {profile : PolyProfile} {scope : Nat}
    {pairTerm : RawTerm scope}
    (pairCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase pairTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_snd ()
        (.childCons pairTerm .childNil)) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_snd
      (genPayloadEvidence (generator := .gen_snd)
                           (scope := scope) ())
      (CertifiedTermSpine.cons pairCell CertifiedTermSpine.nil))

/-! ## Section 2 — Projections (extract pair cert from fst/snd cert) -/

/-- **Projection: `gen_fst` → pair child's cert.** -/
theorem HasCertifiedCellDim0.fst_pair_projection
    {profile : PolyProfile} {scope : Nat}
    (pairTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_fst ()
                (.childCons pairTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) pairTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_snd` → pair child's cert.** -/
theorem HasCertifiedCellDim0.snd_pair_projection
    {profile : PolyProfile} {scope : Nat}
    (pairTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_snd ()
                (.childCons pairTerm .childNil)) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) pairTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-! ## Section 3 — Rename reduction probes -/

/-- **Probe: rename distributes over `gen_fst`.** -/
theorem RawTerm.rename_fst_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_fst ()
          (.childCons pairTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_fst ()
        (.childCons (RawTerm.rename rawRenaming pairTerm) .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_snd`.** -/
theorem RawTerm.rename_snd_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_snd ()
          (.childCons pairTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_snd ()
        (.childCons (RawTerm.rename rawRenaming pairTerm) .childNil))
        : RawTerm targetScope) := rfl

/-! ## Section 4 — Rename preservations (compositional) -/

/-- **`fst` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.fst_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (renamedPairCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming pairTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_fst ()
          (.childCons pairTerm .childNil))) := by
  rw [RawTerm.rename_fst_reduces]
  exact HasCertifiedCellDim0.fst renamedPairCell

/-- **`snd` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.snd_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (renamedPairCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming pairTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_snd ()
          (.childCons pairTerm .childNil))) := by
  rw [RawTerm.rename_snd_reduces]
  exact HasCertifiedCellDim0.snd renamedPairCell

/-! ## Section 5 — Subst reduction probes -/

/-- **Probe: subst distributes over `gen_fst`.** -/
theorem RawTerm.subst_fst_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (pairTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_fst ()
          (.childCons pairTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_fst ()
        (.childCons (RawTerm.subst substitution pairTerm) .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_snd`.** -/
theorem RawTerm.subst_snd_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (pairTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_snd ()
          (.childCons pairTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_snd ()
        (.childCons (RawTerm.subst substitution pairTerm) .childNil))
        : RawTerm targetScope) := rfl

/-! ## Section 6 — Subst preservations (compositional) -/

/-- **`fst` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.fst_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (substPairCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution pairTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_fst ()
          (.childCons pairTerm .childNil))) := by
  rw [RawTerm.subst_fst_reduces]
  exact HasCertifiedCellDim0.fst substPairCell

/-- **`snd` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.snd_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (substPairCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution pairTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_snd ()
          (.childCons pairTerm .childNil))) := by
  rw [RawTerm.subst_snd_reduces]
  exact HasCertifiedCellDim0.snd substPairCell

/-! ## Section 7 — Subst0 (beta-redex) reduction probes -/

/-- **Probe: subst0 distributes over `gen_fst`.** -/
theorem RawTerm.subst0_fst_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (pairTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_fst ()
          (.childCons pairTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_fst ()
        (.childCons (RawTerm.subst0 pairTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_snd`.** -/
theorem RawTerm.subst0_snd_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (pairTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_snd ()
          (.childCons pairTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_snd ()
        (.childCons (RawTerm.subst0 pairTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-! ## Section 8 — Subst0 preservations (beta-redex compositional) -/

/-- **Beta-redex: `(lam (.gen_fst () [pair])) outerArg →
    .gen_fst () [subst0 pair outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_fst_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (pairTerm : RawTerm (scope + 1))
    (substPairCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 pairTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_fst ()
          (.childCons pairTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_fst_reduces]
  exact HasCertifiedCellDim0.fst substPairCell

/-- **Beta-redex: `(lam (.gen_snd () [pair])) outerArg →
    .gen_snd () [subst0 pair outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_snd_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (pairTerm : RawTerm (scope + 1))
    (substPairCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 pairTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_snd ()
          (.childCons pairTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_snd_reduces]
  exact HasCertifiedCellDim0.snd substPairCell

end LeanFX2.Foundation.PolyCell.Core
