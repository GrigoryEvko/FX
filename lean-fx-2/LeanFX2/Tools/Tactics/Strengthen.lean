import LeanFX2.Foundation.RawPartialRename.Strengthen
import LeanFX2.Foundation.RawPartialRename.UnweakenInversion
import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.TyStrengthen

/-! # Tools/Tactics/Strengthen

Strengthening and renaming-image proof shorthands.

These tactics are local wrappers around audited raw/type strengthening lemmas.
They do not register global simp rules and they do not unfold the recursive
partial-renaming engines unless the caller selects that exact rewrite.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Strengthen-after-weaken rewrites -/

macro "fx_rw_raw_strengthen_weaken" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.strengthen?_weaken])

syntax "fx_rw_raw_strengthen_weaken" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_strengthen_weaken $location) =>
      `(tactic| rw [LeanFX2.RawTerm.strengthen?_weaken] $location)

macro "fx_rw_raw_unweaken_weaken" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.unweaken?_weaken])

syntax "fx_rw_raw_unweaken_weaken" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_unweaken_weaken $location) =>
      `(tactic| rw [LeanFX2.RawTerm.unweaken?_weaken] $location)

macro "fx_rw_ty_strengthen_weaken" : tactic =>
  `(tactic| rw [LeanFX2.Ty.strengthen?_weaken])

syntax "fx_rw_ty_strengthen_weaken" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_strengthen_weaken $location) =>
      `(tactic| rw [LeanFX2.Ty.strengthen?_weaken] $location)

/-! ## Rename-image strengthening rewrites -/

macro "fx_rw_raw_partial_strengthen_rename_some" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.partialStrengthen?_rename_some])

syntax "fx_rw_raw_partial_strengthen_rename_some"
    Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_partial_strengthen_rename_some $location) =>
      `(tactic|
        rw [LeanFX2.RawTerm.partialStrengthen?_rename_some] $location)

macro "fx_rw_ty_partial_strengthen_rename_some" : tactic =>
  `(tactic| rw [LeanFX2.Ty.partialStrengthen?_rename_some])

syntax "fx_rw_ty_partial_strengthen_rename_some"
    Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_partial_strengthen_rename_some $location) =>
      `(tactic| rw [LeanFX2.Ty.partialStrengthen?_rename_some] $location)

/-! ## Identity-collapse rewrites -/

macro "fx_rw_raw_rename_identity_once" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.rename_identity])

syntax "fx_rw_raw_rename_identity_once" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_rename_identity_once $location) =>
      `(tactic| rw [LeanFX2.RawTerm.rename_identity] $location)

macro "fx_rw_ty_rename_identity_once" : tactic =>
  `(tactic| rw [LeanFX2.Ty.rename_identity])

syntax "fx_rw_ty_rename_identity_once" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_ty_rename_identity_once $location) =>
      `(tactic| rw [LeanFX2.Ty.rename_identity] $location)

/-! ## Pointwise strengthening witnesses -/

macro "fx_exact_drop_newest_injects_back" : tactic =>
  `(tactic| exact LeanFX2.PartialRawRenaming.dropNewest_renamingInjectsBack)

syntax "fx_exact_lift_injects_back " term : tactic
macro_rules
  | `(tactic| fx_exact_lift_injects_back $renamingInjectsBack) =>
      `(tactic|
        exact LeanFX2.PartialRawRenaming.lift_renamingInjectsBack
          $renamingInjectsBack)

end LeanFX2.Tools.Tactics
