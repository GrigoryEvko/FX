import LeanFX2.Foundation.RawPartialRename.Function
import LeanFX2.Foundation.RawPartialRename.Strengthen
import LeanFX2.Foundation.RawSubst.SubstDefs
import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.TyStrengthen
import LeanFX2.Term.Bridge

/-! # Tools/Tactics/SimpStrip — bridge-rfl simp set

A curated `simp` lemma set that strips `Term.toRaw`-related casts
from goals.  Useful when proving Bridge theorems where multiple
`toRaw_<op>` rfls compose.

## The simp set

```lean
attribute [simp_strip] Term.toRaw_cast
attribute [simp_strip] Term.toRaw_rename     -- rfl
attribute [simp_strip] Term.toRaw_subst      -- rfl
attribute [simp_strip] Term.toRaw_subst0     -- rfl
attribute [simp_strip] Term.toRaw_var
attribute [simp_strip] Term.toRaw_lam
-- ... (all toRaw projections)
```

## Usage

```lean
example : (Term.lam body).toRaw.subst σ.forRaw = ... := by
  simp only [simp_strip]
  ...
```

## Why a separate simp set

`simp` with arbitrary lemmas can rewrite too aggressively, breaking
proofs.  A scoped set (`simp_strip`) only fires the rfl-collapsing
lemmas, keeping intent explicit.

## Dependencies

* `Term/ToRaw.lean`

## Downstream

* `Bridge.lean` — uses simp_strip to discharge rfl-equal raw forms
* `Reduction/Compat.lean`

## Implementation plan (Layer 12)

1. Define `simp_strip` attribute
2. Tag all toRaw_<op> lemmas
3. Smoke: trivial bridge proof closes via `simp only [simp_strip]`

Target: ~100 lines.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Local normalization macros

These are intentionally local `simp only` / `rw` shorthands.  They do not
register global simp attributes and they do not unfold recursive engines unless
the caller asks for that exact engine.
-/

macro "fx_simp_option_maps" : tactic =>
  `(tactic| simp only [Option.map, Option.mapTwo, Option.mapThree])

syntax "fx_simp_option_maps" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_option_maps $location) =>
      `(tactic| simp only [Option.map, Option.mapTwo, Option.mapThree] $location)

macro "fx_simp_raw_rename" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.rename])

syntax "fx_simp_raw_rename" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_rename $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.rename] $location)

macro "fx_simp_raw_partial_rename" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.partialRename?])

syntax "fx_simp_raw_partial_rename" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_partial_rename $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.partialRename?] $location)

macro "fx_simp_raw_partial_strengthen" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.partialStrengthen?])

syntax "fx_simp_raw_partial_strengthen" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_partial_strengthen $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.partialStrengthen?] $location)

macro "fx_simp_raw_subst" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.subst])

syntax "fx_simp_raw_subst" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_subst $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.subst] $location)

macro "fx_simp_raw_subst0" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.subst0])

syntax "fx_simp_raw_subst0" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_subst0 $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.subst0] $location)

macro "fx_simp_ty_rename" : tactic =>
  `(tactic| simp only [LeanFX2.Ty.rename])

syntax "fx_simp_ty_rename" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_ty_rename $location) =>
      `(tactic| simp only [LeanFX2.Ty.rename] $location)

macro "fx_simp_ty_partial_strengthen" : tactic =>
  `(tactic| simp only [LeanFX2.Ty.partialStrengthen?])

syntax "fx_simp_ty_partial_strengthen" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_ty_partial_strengthen $location) =>
      `(tactic| simp only [LeanFX2.Ty.partialStrengthen?] $location)

macro "fx_simp_term_to_raw" : tactic =>
  `(tactic|
    simp only [
      LeanFX2.Term.toRaw,
      LeanFX2.Term.toRaw_rename,
      LeanFX2.Term.toRaw_subst,
      LeanFX2.Term.toRaw_subst0
    ])

syntax "fx_simp_term_to_raw" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_term_to_raw $location) =>
      `(tactic|
        simp only [
          LeanFX2.Term.toRaw,
          LeanFX2.Term.toRaw_rename,
          LeanFX2.Term.toRaw_subst,
          LeanFX2.Term.toRaw_subst0
        ] $location)

macro "fx_rw_raw_rename_identity" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.rename_identity])

syntax "fx_rw_raw_rename_identity" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_rename_identity $location) =>
      `(tactic| rw [LeanFX2.RawTerm.rename_identity] $location)

macro "fx_rw_ty_rename_identity" : tactic =>
  `(tactic| rw [LeanFX2.Ty.rename_identity])

syntax "fx_rw_ty_rename_identity" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_rename_identity $location) =>
      `(tactic| rw [LeanFX2.Ty.rename_identity] $location)

macro "fx_rw_raw_weaken_rename_commute" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.weaken_rename_commute])

syntax "fx_rw_raw_weaken_rename_commute" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_weaken_rename_commute $location) =>
      `(tactic| rw [LeanFX2.RawTerm.weaken_rename_commute] $location)

macro "fx_rw_raw_weaken_rename_commute_symm" : tactic =>
  `(tactic| rw [← LeanFX2.RawTerm.weaken_rename_commute])

syntax "fx_rw_raw_weaken_rename_commute_symm"
    Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_weaken_rename_commute_symm $location) =>
      `(tactic| rw [← LeanFX2.RawTerm.weaken_rename_commute] $location)

macro "fx_rw_ty_weaken_rename_commute" : tactic =>
  `(tactic| rw [LeanFX2.Ty.weaken_rename_commute])

syntax "fx_rw_ty_weaken_rename_commute" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_weaken_rename_commute $location) =>
      `(tactic| rw [LeanFX2.Ty.weaken_rename_commute] $location)

macro "fx_rw_ty_weaken_rename_commute_symm" : tactic =>
  `(tactic| rw [← LeanFX2.Ty.weaken_rename_commute])

syntax "fx_rw_ty_weaken_rename_commute_symm"
    Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_weaken_rename_commute_symm $location) =>
      `(tactic| rw [← LeanFX2.Ty.weaken_rename_commute] $location)

macro "fx_rw_ty_subst0_rename_commute" : tactic =>
  `(tactic| rw [LeanFX2.Ty.subst0_rename_commute])

syntax "fx_rw_ty_subst0_rename_commute" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_subst0_rename_commute $location) =>
      `(tactic| rw [LeanFX2.Ty.subst0_rename_commute] $location)

macro "fx_rw_ty_subst0_rename_commute_symm" : tactic =>
  `(tactic| rw [← LeanFX2.Ty.subst0_rename_commute])

syntax "fx_rw_ty_subst0_rename_commute_symm"
    Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_subst0_rename_commute_symm $location) =>
      `(tactic| rw [← LeanFX2.Ty.subst0_rename_commute] $location)

end LeanFX2.Tools.Tactics
