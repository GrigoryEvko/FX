import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Smoke.AuditMegaZ2B

/-! # AuditMegaZ5A1 — Zero-axiom audit for the
`ActsOnRawTermVarLifts` typeclass + 3 instances.

## What Z5.A.1 ships

Z5.A's `Term.act` recursion engine (yet to land) needs to traverse
closed-payload HoTT ctors (`Term.equivReflId`, `Term.funextRefl`,
etc.) whose RawTerm structure embeds `RawTerm.var ⟨0, _⟩` under
`Action.liftForRaw action`.  Z5.A's typeclass dispatch through
`RawTerm.act` cannot rewrite that closed payload to a
`rfl`-equivalent target without a reduction law for the var case
under `liftForRaw`.

Z5.A.1 ships the missing reduction laws as a NEW typeclass
`ActsOnRawTermVarLifts` with two fields:

* `liftForRaw_var_zero` — under any lifted action, position `0`
  resolves to `RawTerm.var ⟨0, _⟩` in the target's lifted scope.
* `liftForRaw_var_succ` — under any lifted action, position `k+1`
  resolves to `RawTerm.weaken (varToRawTerm action k)`.

Both laws hold by `rfl` for all three Containers that the Tier 3
framework currently ships (`RawRenaming`, `RawTermSubst`,
`Subst level`).  The instances ship `rfl`-bodied per-field.

## Files modified by Z5.A.1

* `Foundation/RawSubst.lean` — NEW `class ActsOnRawTermVarLifts` +
  NEW `instance : ActsOnRawTermVarLifts RawRenaming` +
  NEW `instance : ActsOnRawTermVarLifts RawTermSubst` (placed
  alongside the existing `ActsOnRawTermVar` instances).
* `Foundation/SubstActsOnTy.lean` — NEW `instance
  ActsOnRawTermVarLiftsOfSubst (level : Nat) : ActsOnRawTermVarLifts
  (Subst level)` (placed alongside the existing
  `ActsOnRawTermVarOfSubst` instance).

## Audit philosophy

Z5.A.1 is a CAPABILITY-EXPANDING refactor: it adds a new typeclass
without modifying any existing definition or theorem.  All three
instances ship by `rfl`, so the typeclass's content is purely
definitional.  This file gates:

1. The two `rfl` smokes per Container (var-zero + var-succ
   reductions hold definitionally).
2. Audit gates for the new typeclass + 3 instances.
3. Headliner regression: `subst_compatible_paired_allais` (Pattern
   3), the W8 confluence chain (cd_lemma / diamond / parStar
   confluence / canonical_form), Heterogeneous Univalence,
   Univalence, and `funext` — all must remain zero-axiom.
4. Z2.B / Z2.6 / Z2.A.1 / Z4.A downstream invariants — must stay
   clean since Z5.A.1 only adds, never modifies.
-/

namespace LeanFX2

-- ============================================================
-- Section 1: rfl smokes for `RawRenaming` — both fields hold by rfl
-- ============================================================

/-- `rfl` smoke (RawRenaming, var-zero): under `liftForRaw`,
position `0` lifts to `RawTerm.var ⟨0, _⟩` in the target's
lifted scope. -/
example {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someRenaming)
        (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
      = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
          RawTerm (targetScope + 1)) := rfl

/-- `rfl` smoke (RawRenaming, var-succ): under `liftForRaw`,
position `k+1` lifts to `RawTerm.weaken` of the renamed source. -/
example {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (predecessorIndex : Fin sourceScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someRenaming)
        ⟨predecessorIndex.val + 1,
          Nat.succ_lt_succ predecessorIndex.isLt⟩
      = RawTerm.weaken
          (ActsOnRawTermVar.varToRawTerm someRenaming
            predecessorIndex) := rfl

-- ============================================================
-- Section 2: rfl smokes for `RawTermSubst` — both fields hold by rfl
-- ============================================================

/-- `rfl` smoke (RawTermSubst, var-zero): under `liftForRaw`,
position `0` lifts to `RawTerm.var ⟨0, _⟩` in the target's
lifted scope. -/
example {sourceScope targetScope : Nat}
    (someSigma : RawTermSubst sourceScope targetScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someSigma)
        (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
      = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
          RawTerm (targetScope + 1)) := rfl

/-- `rfl` smoke (RawTermSubst, var-succ): under `liftForRaw`,
position `k+1` lifts to `RawTerm.weaken` of the substituted
source. -/
example {sourceScope targetScope : Nat}
    (someSigma : RawTermSubst sourceScope targetScope)
    (predecessorIndex : Fin sourceScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someSigma)
        ⟨predecessorIndex.val + 1,
          Nat.succ_lt_succ predecessorIndex.isLt⟩
      = RawTerm.weaken
          (ActsOnRawTermVar.varToRawTerm someSigma
            predecessorIndex) := rfl

-- ============================================================
-- Section 3: rfl smokes for `Subst level` — both fields hold by rfl
-- ============================================================

/-- `rfl` smoke (Subst level, var-zero): under `liftForRaw`, the
joint substitution's `forRaw` lifts position `0` to `RawTerm.var
⟨0, _⟩` in the target's lifted scope. -/
example {level sourceScope targetScope : Nat}
    (someSubst : Subst level sourceScope targetScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someSubst)
        (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
      = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
          RawTerm (targetScope + 1)) := rfl

/-- `rfl` smoke (Subst level, var-succ): under `liftForRaw`, the
joint substitution's `forRaw` lifts position `k+1` to
`RawTerm.weaken` of the substituted source. -/
example {level sourceScope targetScope : Nat}
    (someSubst : Subst level sourceScope targetScope)
    (predecessorIndex : Fin sourceScope) :
    ActsOnRawTermVar.varToRawTerm
        (Action.liftForRaw someSubst)
        ⟨predecessorIndex.val + 1,
          Nat.succ_lt_succ predecessorIndex.isLt⟩
      = RawTerm.weaken
          (ActsOnRawTermVar.varToRawTerm someSubst
            predecessorIndex) := rfl

-- ============================================================
-- Section 4: rfl smoke demonstrating closed-payload reduction
-- ============================================================
-- This is the load-bearing demonstration that Z5.A.1 unblocks
-- Z5.A's Term.act traversal of closed-payload HoTT ctors.  When
-- `RawTerm.act` encounters a `RawTerm.var ⟨0, _⟩` under a lifted
-- renaming, the var arm of `RawTerm.act` invokes
-- `ActsOnRawTermVar.varToRawTerm`; the typeclass field
-- `liftForRaw_var_zero` then rewrites the result back to
-- `RawTerm.var ⟨0, _⟩`.

/-- Smoke: `RawTerm.act (RawTerm.var ⟨0, _⟩) (Action.liftForRaw
rho)` reduces to `RawTerm.var ⟨0, _⟩`.  Demonstrates the
var-zero-under-lift discharge for `RawRenaming` Container. -/
example {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.act
        (RawTerm.var
          (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1)))
        (Action.liftForRaw someRenaming)
      = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
          RawTerm (targetScope + 1)) := by
  -- `RawTerm.act` reduces the var arm via `ActsOnRawTermVar.varToRawTerm`;
  -- the new typeclass instance discharges the reduction by `rfl`.
  exact ActsOnRawTermVarLifts.liftForRaw_var_zero someRenaming

/-- Smoke: same demonstration over `Subst level` Container.  The
joint substitution's `forRaw` discipline lets the var-zero-under-lift
reduction discharge by the `ActsOnRawTermVarLiftsOfSubst` instance. -/
example {level sourceScope targetScope : Nat}
    (someSubst : Subst level sourceScope targetScope) :
    RawTerm.act
        (RawTerm.var
          (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1)))
        (Action.liftForRaw someSubst)
      = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
          RawTerm (targetScope + 1)) := by
  exact ActsOnRawTermVarLifts.liftForRaw_var_zero someSubst

end LeanFX2

-- ============================================================
-- Section 5: Audit gates for the new typeclass + 3 instances
-- ============================================================
-- All three instances ship `rfl`-bodied; their #print axioms must
-- report "does not depend on any axioms".

-- The new typeclass itself.
#print axioms LeanFX2.ActsOnRawTermVarLifts

-- The three shipped instances (all rfl-bodied).
#print axioms LeanFX2.instActsOnRawTermVarLiftsRawRenaming
#print axioms LeanFX2.instActsOnRawTermVarLiftsRawTermSubst
#print axioms LeanFX2.ActsOnRawTermVarLiftsOfSubst

-- ============================================================
-- Section 6: Headliner regression — Pattern 3 + W8 confluence
-- ============================================================
-- Z5.A.1 must not regress the project's load-bearing zero-axiom
-- theorems.  Since the typeclass purely adds new fields without
-- modifying any existing definition, these should all stay clean.

-- Pattern 3 (CUMUL-1.7) — Allais ICFP'18 paired-env subst_compatible.
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais

-- W8 — typed Tait-Martin-Löf chain (cd_lemma / diamond / parStar /
-- canonical form).
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalForm

-- Heterogeneous Univalence (Phase 12.A.3 D3.6).
#print axioms LeanFX2.Univalence
#print axioms LeanFX2.UnivalenceHet

-- funext (Phase 12.A.3 D3.7).
#print axioms LeanFX2.funext

-- ============================================================
-- Section 7: Z2.A.1 / Z2.B / Z2.6 / Z4.A downstream regression
-- ============================================================
-- The Tier 3 prerequisite chain (Z1.A → Z1.B → Z2.A → Z2.A.1 →
-- Z2.B → Z2.6 → Z4.A → Z5.A.1) must stay zero-axiom.

-- Z2.A.1 alignment + bridge theorems.
#print axioms LeanFX2.ActsOnRawTermOfSubst
#print axioms LeanFX2.ActsOnRawTermVarOfSubst
#print axioms LeanFX2.RawTerm.act_eq_rename
#print axioms LeanFX2.RawTerm.act_eq_subst_forRaw

-- Z2.B Ty.act bridge theorems.
#print axioms LeanFX2.Ty.act_eq_rename
#print axioms LeanFX2.Ty.act_eq_subst
#print axioms LeanFX2.Ty.act_eq_weaken

-- Z2.6 Ty.act-layer infrastructure.
#print axioms LeanFX2.Ty.act_pointwise
#print axioms LeanFX2.Ty.act_compose
#print axioms LeanFX2.Ty.act_identity
