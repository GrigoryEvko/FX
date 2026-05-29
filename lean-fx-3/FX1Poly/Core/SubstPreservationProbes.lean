import FX1Poly.Core.HasCertifiedIntros
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/SubstPreservationProbes — rename/subst leaf probes

V2-L3.1 phase D step 15 (2026-05-27).  Foundation work for the
subst/rename preservation mutual block that will eventually
unblock structural SR-beta + SR-cong.

## What this file ships

Small, focused theorems establishing that the fold-based
`RawTerm.rename` and `RawTerm.subst` operations on LEAF terms
(nullary generators) reduce by definitional equality to the
expected closed forms.  These probes are:

1. **Useful infrastructure** for the eventual mutual block —
   the leaf base cases of the inductive proofs.

2. **Documentation** of where `rfl` works and where it doesn't.
   If a fold reduces by `rfl` on a closed input, downstream
   proofs can use that reduction directly.  If not, the
   downstream proof needs a manual lemma about the fold's
   behavior on that input shape.

## Probes shipped

  * `rename_var_reduces` — `RawTerm.rename ρ (gen_var i nil)
    = gen_var (ρ i) nil`, by `rfl`.  Direct fold reduction.

  * `rename_unit_reduces` — same for `gen_unit ()`, by `rfl`.

  * `subst_var_zero_reduces` — `RawTerm.subst σ (gen_var 0 nil)
    = σ 0`, by `rfl`.  The subst container's variable bridge
    returns the substituent directly.

  * `subst_unit_reduces` — same for `gen_unit ()`, by `rfl`.

## Lifts of cell-level preservation lemmas

Combining these probes with the just-shipped intros from
`HasCertifiedIntros.lean` gives the SIMPLEST nontrivial pieces
of preservation:

  * `HasCertifiedCellDim0.var_preservedByRename` — var stays
    var after rename, certified via `HasCertifiedCellDim0.var`.
  * `HasCertifiedCellDim0.unit_preservedByRename` — unit stays
    unit after rename, certified via `HasCertifiedCellDim0.unit`.

These are STRUCTURALLY trivial (the renamed term is a nullary
gen-shape) but they confirm the proof template that will scale
to the full mutual block: extract via `cases`, reduce via the
fold's definitional behavior, reconstruct via the intro.

Subst-side analogs are conditional on σ producing certified
substituents — recorded here for the full block's design.

## What this file does NOT ship

The full `HasCertifiedCellDim0.preservedByRename` /
`preservedBySubst` mutual block remains pending — that
requires structural induction on the PolyCell + spine, which
is the substantial multi-iteration work.

These probes establish that the LEAF cases work; the
inductive cases over compound generators are the remaining
substance.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — rename reduces on nullary leaves -/

/-- **Probe: rename reduces on `gen_var`.**

`RawTerm.rename ρ (.mkGen .gen_var i .childNil)
  = .mkGen .gen_var (ρ i) .childNil`.

Closes by `rfl` if the fold's variable arm reduces (which it
does for `RawRenaming` via the `ActsOnRawTermVar` bridge).
This is the canonical "var renames to renamed-var" probe. -/
theorem RawTerm.rename_var_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (varIndex : Fin sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_var varIndex .childNil : RawTerm sourceScope) =
      (.mkGen .gen_var (rawRenaming varIndex) .childNil
        : RawTerm targetScope) := rfl

/-- **Probe: rename reduces on `gen_unit`.**

`RawTerm.rename ρ (.mkGen .gen_unit () .childNil)
  = .mkGen .gen_unit () .childNil` (at the target scope).

Closes by `rfl` via the canonical algebra's rebuild
on non-variable nullary generators. -/
theorem RawTerm.rename_unit_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_unit () .childNil : RawTerm targetScope) := rfl

/-! ## Section 2 — subst reduces on nullary leaves -/

/-- **Probe: subst on `gen_var` returns the substituent.**

`RawTerm.subst σ (.mkGen .gen_var i .childNil) = σ i`.

The `RawTermSubst`'s `ActsOnRawTermVar` bridge is direct
lookup, so the fold's var arm returns `σ i` verbatim.  Closes
by `rfl`. -/
theorem RawTerm.subst_var_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (varIndex : Fin sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_var varIndex .childNil : RawTerm sourceScope) =
      substitution varIndex := rfl

/-- **Probe: subst reduces on `gen_unit`.**

`RawTerm.subst σ (.mkGen .gen_unit () .childNil)
  = .mkGen .gen_unit () .childNil`.  Closed term ignores σ.
Closes by `rfl`. -/
theorem RawTerm.subst_unit_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_unit () .childNil : RawTerm targetScope) := rfl

/-! ## Section 3 — cell-level preservation: leaf cases

Combining Section 1 + the just-shipped intros from
`HasCertifiedIntros.lean` gives the simplest nontrivial pieces
of cell-level preservation: variable and unit stay structurally
admitted after renaming. -/

/-- **Cell-level: var preserved by rename.**

If `(gen_var i)` is structurally admitted at sourceScope, then
`rename ρ (gen_var i) = gen_var (ρ i)` is structurally admitted
at targetScope (by `HasCertifiedCellDim0.var`). -/
theorem HasCertifiedCellDim0.var_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (varIndex : Fin sourceScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_var varIndex .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_var_reduces rawRenaming varIndex]
  exact HasCertifiedCellDim0.var (rawRenaming varIndex)

/-- **Cell-level: unit preserved by rename.**

`rename ρ (gen_unit ()) = gen_unit ()`, certified via
`HasCertifiedCellDim0.unit`. -/
theorem HasCertifiedCellDim0.unit_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_unit_reduces rawRenaming]
  exact HasCertifiedCellDim0.unit

/-- **Cell-level: unit preserved by ANY subst.**

Closed terms are invariant under substitution; certified via
`HasCertifiedCellDim0.unit`. -/
theorem HasCertifiedCellDim0.unit_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_unit_reduces substitution]
  exact HasCertifiedCellDim0.unit

/-! ## Section 4 — additional nullary leaf reductions

Each of these proves `rename` (resp. `subst`) reduces to the same
closed-form leaf by `rfl`.  Same fold-arm pattern as `unit`. -/

/-- **Probe: rename reduces on `gen_boolTrue`.** -/
theorem RawTerm.rename_boolTrue_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_boolTrue () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_boolTrue () .childNil : RawTerm targetScope) := rfl

/-- **Probe: rename reduces on `gen_boolFalse`.** -/
theorem RawTerm.rename_boolFalse_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_boolFalse () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_boolFalse () .childNil : RawTerm targetScope) := rfl

/-- **Probe: rename reduces on `gen_natZero`.** -/
theorem RawTerm.rename_natZero_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_natZero () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_natZero () .childNil : RawTerm targetScope) := rfl

/-- **Probe: rename reduces on `gen_listNil`.** -/
theorem RawTerm.rename_listNil_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_listNil () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_listNil () .childNil : RawTerm targetScope) := rfl

/-- **Probe: rename reduces on `gen_optionNone`.** -/
theorem RawTerm.rename_optionNone_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_optionNone () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_optionNone () .childNil : RawTerm targetScope) := rfl

/-! ## Section 5 — additional cell-level leaf preservations

Combining the new probes with the corresponding intros from
`HasCertifiedIntros.lean`.  Each is a 2-tactic proof:
`rw [reduces]; exact intro`. -/

/-- **Cell-level: boolTrue preserved by rename.** -/
theorem HasCertifiedCellDim0.boolTrue_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_boolTrue () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_boolTrue_reduces rawRenaming]
  exact HasCertifiedCellDim0.boolTrue

/-- **Cell-level: boolFalse preserved by rename.** -/
theorem HasCertifiedCellDim0.boolFalse_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_boolFalse () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_boolFalse_reduces rawRenaming]
  exact HasCertifiedCellDim0.boolFalse

/-- **Cell-level: natZero preserved by rename.** -/
theorem HasCertifiedCellDim0.natZero_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natZero () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_natZero_reduces rawRenaming]
  exact HasCertifiedCellDim0.natZero

/-- **Cell-level: listNil preserved by rename.** -/
theorem HasCertifiedCellDim0.listNil_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_listNil () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_listNil_reduces rawRenaming]
  exact HasCertifiedCellDim0.listNil

/-- **Cell-level: optionNone preserved by rename.** -/
theorem HasCertifiedCellDim0.optionNone_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_optionNone () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.rename_optionNone_reduces rawRenaming]
  exact HasCertifiedCellDim0.optionNone

/-! ## Section 6 — subst reduces on the remaining closed nullary leaves

Mirrors Section 4 for the general substitution direction.  Each closed
leaf's payload is `()` (Unit), scope-invariant under `subst`'s
non-variable fold arm, so the fold rebuilds the same closed term at
the target scope.  All five close by `rfl`. -/

/-- **Probe: subst reduces on `gen_boolTrue`.**

Closed term; subst returns the same generator at the target scope. -/
theorem RawTerm.subst_boolTrue_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_boolTrue () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_boolTrue () .childNil : RawTerm targetScope) := rfl

/-- **Probe: subst reduces on `gen_boolFalse`.** -/
theorem RawTerm.subst_boolFalse_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_boolFalse () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_boolFalse () .childNil : RawTerm targetScope) := rfl

/-- **Probe: subst reduces on `gen_natZero`.** -/
theorem RawTerm.subst_natZero_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_natZero () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_natZero () .childNil : RawTerm targetScope) := rfl

/-- **Probe: subst reduces on `gen_listNil`.** -/
theorem RawTerm.subst_listNil_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_listNil () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_listNil () .childNil : RawTerm targetScope) := rfl

/-- **Probe: subst reduces on `gen_optionNone`.** -/
theorem RawTerm.subst_optionNone_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution
        (.mkGen .gen_optionNone () .childNil : RawTerm sourceScope) =
      (.mkGen .gen_optionNone () .childNil : RawTerm targetScope) := rfl

/-! ## Section 7 — cell-level subst preservation: remaining closed leaves

Combines Section 6 with the corresponding intros from
`HasCertifiedIntros.lean`.  Closes the leaf coverage so every nullary
generator has a `_preservedBySubst` lemma, mirroring the rename direction
shipped in Sections 3 and 5.  Each is a 2-tactic proof:
`rw [reduces]; exact intro`. -/

/-- **Cell-level: boolTrue preserved by ANY subst.** -/
theorem HasCertifiedCellDim0.boolTrue_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_boolTrue () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_boolTrue_reduces substitution]
  exact HasCertifiedCellDim0.boolTrue

/-- **Cell-level: boolFalse preserved by ANY subst.** -/
theorem HasCertifiedCellDim0.boolFalse_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_boolFalse () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_boolFalse_reduces substitution]
  exact HasCertifiedCellDim0.boolFalse

/-- **Cell-level: natZero preserved by ANY subst.** -/
theorem HasCertifiedCellDim0.natZero_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natZero () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_natZero_reduces substitution]
  exact HasCertifiedCellDim0.natZero

/-- **Cell-level: listNil preserved by ANY subst.** -/
theorem HasCertifiedCellDim0.listNil_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_listNil () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_listNil_reduces substitution]
  exact HasCertifiedCellDim0.listNil

/-- **Cell-level: optionNone preserved by ANY subst.** -/
theorem HasCertifiedCellDim0.optionNone_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_optionNone () .childNil : RawTerm sourceScope)) := by
  rw [RawTerm.subst_optionNone_reduces substitution]
  exact HasCertifiedCellDim0.optionNone

end FX1Poly.Core
