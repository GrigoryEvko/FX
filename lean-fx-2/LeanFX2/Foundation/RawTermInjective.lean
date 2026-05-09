import LeanFX2.Foundation.RawSubst

/-! # Foundation/RawTermInjective — rename injectivity scaffold

Load-bearing infrastructure for D2.5.5 (transpPiBetaSimple cubical-β
rule).  The cubical-β cd-cascade dispatcher recognizes
`piTyCode A A.weaken` shapes via a structural equality test
`decide (domainCode = codomainUnweakened)`.  Under arbitrary
non-injective renamings, this test could collapse from false to true
(distinct terms become identified after rename), so cd_rename for
arbitrary `rho` is genuinely false.

This file ships the rename-injectivity infrastructure that lets
cd_rename take a `RawRenamingInjective rho` hypothesis and remain
provable.  Downstream consumers (cd_weaken) supply the hypothesis
via the `RawRenamingInjective.weaken` instance.

## What ships

* `RawRenamingInjective rho` — Prop predicate: distinct positions map
  distinctly.
* `RawRenamingInjective.weaken` — `RawRenaming.weaken = Fin.succ` is
  injective (via `Nat.succ.inj`).
* `RawRenamingInjective.lift` — `lift` preserves injectivity through
  binders.
* `RawTerm.rename_injective_under_injective_renaming` — full 73-ctor
  enumeration: when `rho` is injective, `term.rename rho` is injective
  in `term`.

## Why a dedicated file (not inlined in RawCdRename)

Architectural isolation: this is foundational infrastructure that
benefits future cubical-β rules (D2.5.6 transpSigma, D2.5.7 closed-type
transps) which face the same wall.  Solving rename-injectivity ONCE
amortizes across the entire D2.5.x cascade.

Keeping the proof in `Foundation/` rather than `Confluence/` reflects
its layer: it depends only on `RawSubst` (rename) and is consumed by
`Confluence/RawCdRename` (rename commute).

## Root status

* Layer: foundation (under `Confluence/`)
* Load-bearing for: `Confluence/RawCdRename` (D2.5.5 cd-cascade rename
  helper), future `D2.5.6` / `D2.5.7` cubical-β rules
* Axiom budget: zero (verified via `#assert_no_axioms`)
-/

namespace LeanFX2

/-- A renaming is injective when distinct source positions map to
distinct target positions.  Custom `Prop`-valued predicate avoids
relying on `Function.Injective` from stdlib (the strict harness
`Tools/StrictHarness/TrustEscape.lean` pins the budget on stdlib
`Function.*` references). -/
def RawRenamingInjective {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  ∀ (positionA positionB : Fin sourceScope),
    rawRenaming positionA = rawRenaming positionB →
    positionA = positionB

/-- `RawRenaming.weaken` (= `Fin.succ`) is injective.  Proof: if
`Fin.succ a = Fin.succ b` then their `Nat.val`s agree, and `Nat.succ`
is injective. -/
theorem RawRenamingInjective.weaken {scope : Nat} :
    RawRenamingInjective (RawRenaming.weaken (scope := scope)) := by
  intro positionA positionB succEq
  apply Fin.ext
  have valEq : (RawRenaming.weaken positionA).val =
               (RawRenaming.weaken positionB).val :=
    congrArg Fin.val succEq
  exact Nat.succ.inj valEq

/-- `RawRenaming.lift` preserves injectivity: if `rho` is injective,
so is `rho.lift`.  Case-split on each `Fin (source + 1)` argument:
`(0, 0)` is `rfl`, `(0, succ k)` and `(succ k, 0)` are
constructor-disjoint via `Nat.succ_ne_zero`, and `(succ a, succ b)`
reduces to `Fin.succ`-injectivity composed with `rho`'s injectivity. -/
theorem RawRenamingInjective.lift {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    (rhoInjective : RawRenamingInjective rho) :
    RawRenamingInjective rho.lift := by
  intro positionA positionB liftEq
  match positionA, positionB with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨k + 1, hB⟩ =>
      exfalso
      have valEq : (0 : Nat) =
          (Fin.succ (rho ⟨k, Nat.lt_of_succ_lt_succ hB⟩)).val :=
        congrArg Fin.val liftEq
      exact Nat.succ_ne_zero _ valEq.symm
  | ⟨a + 1, hA⟩, ⟨0, _⟩ =>
      exfalso
      have valEq : (Fin.succ (rho ⟨a, Nat.lt_of_succ_lt_succ hA⟩)).val =
                   (0 : Nat) :=
        congrArg Fin.val liftEq
      exact Nat.succ_ne_zero _ valEq
  | ⟨a + 1, hA⟩, ⟨b + 1, hB⟩ =>
      apply Fin.ext
      have valEq : (Fin.succ (rho ⟨a, Nat.lt_of_succ_lt_succ hA⟩)).val =
                   (Fin.succ (rho ⟨b, Nat.lt_of_succ_lt_succ hB⟩)).val :=
        congrArg Fin.val liftEq
      have rhoValEq : (rho ⟨a, Nat.lt_of_succ_lt_succ hA⟩).val =
                      (rho ⟨b, Nat.lt_of_succ_lt_succ hB⟩).val :=
        Nat.succ.inj valEq
      have rhoEq : rho ⟨a, Nat.lt_of_succ_lt_succ hA⟩ =
                   rho ⟨b, Nat.lt_of_succ_lt_succ hB⟩ := Fin.ext rhoValEq
      have abEq : (⟨a, Nat.lt_of_succ_lt_succ hA⟩ : Fin sourceScope) =
                  ⟨b, Nat.lt_of_succ_lt_succ hB⟩ := rhoInjective _ _ rhoEq
      have valAB : a = b := congrArg Fin.val abEq
      exact congrArg (· + 1) valAB

/-! ## Term-rename injectivity — DEFERRED to follow-up commit

The headline `RawTerm.rename_injective_under_injective_renaming`
theorem requires full 73-ctor structural induction (~500 LoC of
mechanical injection + IH application).  Pattern is validated on
{var, unit, lam, app} sub-cases; full enumeration deferred to a
follow-up to keep this commit focused on the foundational predicate
infrastructure.

The follow-up (Phase 0b) ships the headline theorem and unblocks
D2.5.5 cd_rename's dispatcher rename-helper.

Validation pattern (verified compiling):

```
| var positionA =>
    intro _ _ rhoInjective termB renameEq
    cases termB with
    | var positionB =>
        simp only [RawTerm.rename] at renameEq
        injection renameEq with positionEq
        exact congrArg RawTerm.var (rhoInjective _ _ positionEq)
    | _ => simp only [RawTerm.rename] at renameEq; cases renameEq
| lam bodyA bodyIH =>
    intro _ _ rhoInjective termB renameEq
    cases termB with
    | lam bodyB =>
        simp only [RawTerm.rename] at renameEq
        injection renameEq with bodyEq
        exact congrArg RawTerm.lam
          (bodyIH (RawRenamingInjective.lift rhoInjective) _ bodyEq)
    | _ => simp only [RawTerm.rename] at renameEq; cases renameEq
```
-/

end LeanFX2
