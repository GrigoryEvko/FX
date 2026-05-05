/-! # Reduction/Compat — rename + subst compatibility

Renaming and substitution preserve every reduction relation:
* `Step` (single step)
* `Step.par` (parallel reduction)
* `StepStar` (multi-step) — via `mapStep`
* `Conv` (definitional conversion) — via `mapStep`

## The big simplification (from lean-fx)

In lean-fx, β-arms required a separate `RawConsistent` hypothesis
threaded through ~17 files because `Term.subst0_term` consulted the
raw side via a `forRaw` field that could be inconsistent with the
typed `forTy`.  In lean-fx-2, `RawTerm scope` is a Term type-level
index — every typed Term is automatically raw-consistent — so no
threading is needed.  Subst-compat proofs are ~30% smaller.

## Phase plan (this file is BEING BUILT, incrementally)

* Step 1 (cong-only Step.rename_compatible) — port all ~30 cong
  cases first, keeping β/ι behind helper lemmas.
* Step 2 (Term.rename_subst0_HEq) — the subst-rename commute lemma
  at the typed-Term level, needed for β cases.
* Step 3 (β/ι cases of Step.rename_compatible).
* Step 4 (Step.subst_compatible) — mirror via TermSubst.
* Step 5 (Step.par.rename_compatible / subst_compatible).
* Step 6 (StepStar / Conv corollaries via mapStep).
-/

namespace LeanFX2

end LeanFX2
