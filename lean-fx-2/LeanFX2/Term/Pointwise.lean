import LeanFX2.Term.Subst

/-! # Term/Pointwise — substitution pointwise & commute lemmas

Lemmas about how `Term.subst` and `Term.rename` interact when
substitutions are pointwise-equivalent or compose with each other.

## Contents

### Pointwise equivalence
* `Term.subst_HEq_pointwise` — if two TermSubsts agree pointwise
  (HEq) and their underlying Substs agree (Subst.equiv), then
  `Term.subst σ1 t HEq Term.subst σ2 t`
* `TermSubst.lift_HEq_pointwise` — lift preserves pointwise HEq

### Single-step lifts
* `Term.subst_par_pointwise` — Step.par on each position lifts to
  Step.par on the substituted term (used by ParRed compat)

### Commute laws (subst-rename, rename-subst, subst-subst, etc.)
* `Term.rename_subst_commute` — rename ∘ subst = subst ∘ rename (lifted)
* `Term.subst_rename_commute_HEq`
* `Term.rename_subst0` — single-binder variant
* `Term.subst_compose_HEq`

## Diff from lean-fx

lean-fx had these split across:
* `TermSubst/Pointwise.lean` (697 lines)
* `TermSubst/HEqCongr.lean` (725 lines)
* `TermSubst/Compose.lean` (555 lines)
* `TermSubst/Rename/{Identity,Compose,Pointwise}.lean`
* `TermSubst/Commute/{SubstRename,RenameSubst,Subst0Rename,Subst0Subst,SingletonRename}.lean`

= ~3000+ lines total, much of it HEq scaffolding for the toRaw-vs-
type-index disconnect.

In lean-fx-2, raw indices propagate through Term.subst/rename
automatically.  Most HEq lemmas collapse to `rfl` because the type
index does the work.  Target file size: ~300-500 lines.

## Dependencies

* `Term/Subst.lean`

## Downstream consumers

* `Reduction/Compat.lean` — Step compat proofs use these
* `Confluence/Cd.lean` — Term.cd's β-arms use subst0 commute laws
-/

namespace LeanFX2

end LeanFX2
