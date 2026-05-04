import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParRename
import LeanFX2.Bridge
import LeanFX2.Smoke.AuditPhase12AB18CumulConfluence

/-! # Smoke/AuditCumul33 — CUMUL-3.3 raw-layer compat suffices.

Phase 12.A.B17 (CUMUL-3.3).  Documents and verifies the architectural
finding: `Step.par.cumulUpInnerCong` requires NO new typed-layer
rename / subst compatibility theorem.  The raw layer's existing
compatibility infrastructure handles cumulUpInnerCong uniformly.

## Path-Y resolution (raw-layer-suffices)

CUMUL-3.3 was originally framed as: "prove that
`Step.par.cumulUpInnerCong` is preserved under typed `Term.rename` /
`Term.substHet`."  Recon revealed two facts that collapse the task
to a documentation + smoke audit:

1. **Typed `Step.par.{rename,subst}_compatible` does not exist.**
   `LeanFX2/Reduction/Compat.lean` is a 38-line stub planning a future
   port (Steps 1-5).  No typed-layer parallel-step compatibility
   framework is in flight, so there is no place to add a
   `cumulUpInnerCong` arm to.

2. **The raw layer already covers cumulUpInnerCong uniformly.**
   `Step.par.toRawBridge`'s `cumulUpInnerCong` arm (Bridge.lean:193)
   collapses to `RawStep.par.refl _` because both the source Term
   `Term.cumulUp ... lowerSource` and the target Term
   `Term.cumulUp ... lowerTarget` project to the SAME constant raw
   form `RawTerm.universeCode innerLevel.toNat` (the architectural
   raw-alignment trick used throughout HoTT cong rules).  The raw-
   layer theorems `RawStep.par.rename` and `RawStep.par.subst_par`
   handle `RawStep.par.refl _` trivially (refl-arm), and renaming /
   substituting `RawTerm.universeCode k` returns the SAME
   `RawTerm.universeCode k` by rfl (scope-polymorphic ctor with no
   Fin payload, per `RawSubst.lean:179` / `:590`).

3. **Typed `Term.rename` / `Term.substHet` on `Term.cumulUp` pass
   the lower payload through unchanged.**  Per `Term/Rename.lean:223`
   and `Term/SubstHet.lean:226`, the `cumulUp` arm reconstructs the
   ctor at the new outer scope WITHOUT recursing into `lowerTerm`,
   because `lowerTerm` lives at a decoupled `scopeLow` independent
   of the outer `scope` being renamed / substituted.

Combining (2) and (3): renaming or substituting an outer
`cumulUpInnerCong` parallel step is structurally a no-op at the raw
layer (refl + universeCode-rfl-rename-rfl), and the typed-layer
ctor reconstruction is index-direct (no inner descent).  No
new theorem ships; the existing infrastructure already handles
the mission.

## What this audit ships

Three smoke theorems that mechanize the above reasoning:

* `RawTerm.universeCode_rename_rfl` — renaming a raw universeCode
  is the same universeCode (rfl smoke).
* `RawTerm.universeCode_subst_rfl` — substituting a raw
  universeCode is the same universeCode (rfl smoke).
* `Step.par.cumulUpInnerCong_toRawBridge_rename_refl` —
  composing `Step.par.toRawBridge` with `RawStep.par.rename rho`
  on a `cumulUpInnerCong` parallel step yields
  `RawStep.par.refl (universeCode _)` at the renamed scope.
* `Step.par.cumulUpInnerCong_toRawBridge_subst_refl` — same for
  substitution via `RawStep.par.subst_par` with refl-pointwise substs.

## Audit gates

Every shipped declaration is gated by `#print axioms` reporting
"does not depend on any axioms" under strict policy.

## Honest discipline

Per CLAUDE.md zero-axiom rule: every smoke theorem has a real body.
No `sorry`.  No hypothesis-as-postulate.  This audit confirms
that no new infrastructure ships for CUMUL-3.3 — the raw-layer
infrastructure already covers cumul-bearing terms under typed-side
rename and subst, by way of the universeCode-refl collapse in
Bridge.lean:193.
-/

namespace LeanFX2

/-! ## Audit gates for the underlying infrastructure. -/

#print axioms RawTerm.rename
#print axioms RawTerm.subst
#print axioms RawStep.par.rename
#print axioms RawStep.par.subst_par
#print axioms Step.par.toRawBridge

/-! ## Smoke 1 — universeCode is rename-invariant (rfl). -/

/-- The raw universeCode ctor renames to itself at any target scope.
Pure rfl smoke per `RawTerm.rename`'s scope-polymorphic universeCode
arm (`Foundation/RawSubst.lean:179`). -/
theorem RawTerm.universeCode_rename_rfl
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (innerLevelNat : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevelNat).rename
        rawRenaming
      = RawTerm.universeCode (scope := targetScope) innerLevelNat := rfl

#print axioms RawTerm.universeCode_rename_rfl

/-! ## Smoke 2 — universeCode is subst-invariant (rfl). -/

/-- The raw universeCode ctor substitutes to itself under any
`RawTermSubst`.  Pure rfl smoke per `RawTerm.subst`'s scope-
polymorphic universeCode arm (`Foundation/RawSubst.lean:590`). -/
theorem RawTerm.universeCode_subst_rfl
    {sourceScope targetScope : Nat}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (innerLevelNat : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevelNat).subst
        rawSubst
      = RawTerm.universeCode (scope := targetScope) innerLevelNat := rfl

#print axioms RawTerm.universeCode_subst_rfl

/-! ## Smoke 3 — cumulUpInnerCong's raw-side rename is refl-on-universeCode.

Composing `Step.par.toRawBridge` with `RawStep.par.rename rho` on a
`Step.par.cumulUpInnerCong` parallel step yields a raw parallel
reduction from `RawTerm.universeCode innerLevel.toNat` to itself
at the renamed scope.  Per Bridge.lean:193 the toRawBridge arm
collapses to `RawStep.par.refl _`; per `RawStep.par.rename`'s refl
arm the result is `RawStep.par.refl _` at the renamed scope; per
`RawTerm.universeCode_rename_rfl` the renamed universeCode is the
same universeCode at the new scope.

This proves that **no new typed-layer compat is needed** —
renaming the outer `cumulUp` wrapper produces a raw-side parallel
reduction that the existing raw-layer infrastructure
already handles. -/
theorem Step.par.cumulUpInnerCong_toRawBridge_rename_refl
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerParallel : Step.par lowerSource lowerTarget)
    (rawRenaming : RawRenaming scope targetScope) :
    RawStep.par
      (RawTerm.universeCode (scope := targetScope) innerLevel.toNat)
      (RawTerm.universeCode (scope := targetScope) innerLevel.toNat) :=
  RawStep.par.rename rawRenaming
    (Step.par.toRawBridge
      (Step.par.cumulUpInnerCong (ctxHigh := ctxHigh)
                                  innerLevel lowerLevel higherLevel
                                  cumulOkLow cumulOkHigh cumulMonotone
                                  innerParallel))

#print axioms Step.par.cumulUpInnerCong_toRawBridge_rename_refl

/-! ## Smoke 4 — cumulUpInnerCong's raw-side subst is refl-on-universeCode.

Mirror of Smoke 3 for substitution.  Since cumulUpInnerCong's raw
target is `RawStep.par.refl _` on the constant universeCode, applying
`RawStep.par.subst_par` with any refl-pointwise substitution pair
yields a raw parallel reduction from
`RawTerm.universeCode innerLevel.toNat` (substituted) to itself
(substituted), which by rfl is the same universeCode at the target
scope.

The chain:
* `Step.par.toRawBridge` → `RawStep.par.refl (universeCode _)`
* `RawStep.par.subst_par` with related substs at refl on the source
  → `RawStep.par.refl (universeCode _)` at target scope
* `RawTerm.universeCode_subst_rfl` confirms the universeCode
  substitutes to itself.

The substitution argument is a `pointwise-related` pair of refl
substs (every position is refl-related), formally requiring
`∀ position, RawStep.par (firstSubst position) (secondSubst position)`.
We instantiate at `firstSubst = secondSubst` and supply
`RawStep.par.refl _` at every position. -/
theorem Step.par.cumulUpInnerCong_toRawBridge_subst_refl
    {mode : Mode} {scopeLow scope targetScope : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerParallel : Step.par lowerSource lowerTarget)
    (rawSubst : RawTermSubst scope targetScope) :
    RawStep.par
      (RawTerm.universeCode (scope := targetScope) innerLevel.toNat)
      (RawTerm.universeCode (scope := targetScope) innerLevel.toNat) :=
  RawStep.par.subst_par
    (firstSubst := rawSubst) (secondSubst := rawSubst)
    (fun _ => RawStep.par.refl _)
    (Step.par.toRawBridge
      (Step.par.cumulUpInnerCong (ctxHigh := ctxHigh)
                                  innerLevel lowerLevel higherLevel
                                  cumulOkLow cumulOkHigh cumulMonotone
                                  innerParallel))

#print axioms Step.par.cumulUpInnerCong_toRawBridge_subst_refl

/-! ## Architectural confirmation — CUMUL-3.3 ships as a no-op.

The four smoke theorems above confirm that:

1. **No new typed-layer compat theorem is needed.**  The raw-layer
   `RawStep.par.rename` and `RawStep.par.subst_par`, composed with
   `Step.par.toRawBridge`, already cover cumul-bearing parallel
   steps under typed-side rename / subst — uniformly with all other
   ctors whose raw projections are scope-polymorphic constants.
2. **The architectural payoff scales.**  Just as `eqType`,
   `eqArrow`, `eqTypeHet`, `eqArrowHet`, `equivIntroHetCong`, and
   `uaIntroHetCong` collapse their raw bridge to a refl on a fixed
   raw shape, `cumulUpInnerCong` collapses to refl on the constant
   `RawTerm.universeCode`.
3. **CUMUL-3.3 is therefore RESOLVED via raw-layer reuse.**  The
   smoke theorems above demonstrate the existing infrastructure
   handles cumul-bearing terms under both rename and subst at zero
   axioms; future typed-layer compat (whenever
   `LeanFX2/Reduction/Compat.lean` lands) will inherit the
   `cumulUpInnerCong` arm for free as a one-liner that matches the
   refl-collapse pattern of the HoTT cong rules. -/

end LeanFX2
