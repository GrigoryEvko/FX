import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Axis.Term.Action.Fold
import FX1Poly.Axis.Term.Core.RawTermFoldNonVarCommute
import FX1Poly.Axis.Term.Rename.RawTermRename
import FX1Poly.Axis.Term.Subst.RawTermSubst

/-! # FX1Poly/Typed/Cell/RawTermMorphismCell — the ONE raw-term morphism the cells act under

`RawTerm.rename` and `RawTerm.subst` are not two operations: both are literally
`fold GenAlgebra.canonical` at a different Container (`RawTermRename.lean:71`,
`RawTermSubst.lean:111`).  Axis already carries the abstraction that makes this
precise — a Container is a raw-term morphism exactly when it supplies

  * `LiftsRaw`          — how it crosses one binder (`LiftsRaw.lean:69`), and
  * `ActsOnRawTermVar`  — how it acts on a variable (`RawTermSubstDefs.lean:109`).

`fold` demands exactly those two (`Fold.lean:162-164`).  This file names that
pairing at the typed layer as `RawTerm.applyMorphism` and re-derives, ONCE and
generically, the closed-cell computation the formation-obligation push family
needs at BOTH Containers.

## What is genuinely shared, and what is genuinely not

The variable action is where rename and subst genuinely DIFFER, and
`ActsOnRawTermVar` is precisely the datum that records the difference:
renaming re-wraps the moved position as a variable
(`.mkGen .gen_var (rho pos) .childNil`, `RawTermSubstDefs.lean:123-125`) whereas
substitution returns an arbitrary term (`RawTermSubstDefs.lean:134-135`).  So
`rename_variableCell` / `subst_variableCell` are NOT a twin pair — they are the
two instances of that datum, and no generic subsumes them.  Everything CLOSED to
variables (a nullary cell such as `universeCodeCell`) is untouched by the
variable action, and is therefore genuinely shared: it is proved here once.

## Zero-axiom verification

`applyMorphism_universeCodeCell` reduces by `rfl`: the canonical fold rebuilds a
nullary non-variable cell, and the payload cast reduces definitionally at the
concrete `gen_universeCode` generator regardless of Container.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`,
`WellFounded.fix`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Cell/RawTermMorphismCell.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- ★ **The raw-term morphism action** — the ONE traversal `RawTerm.rename` and
`RawTerm.subst` both are.  A `Container` is a raw-term morphism when it knows how
to cross a binder (`LiftsRaw`) and how to act on a variable (`ActsOnRawTermVar`);
those are exactly `fold`'s two constraints, so this is `fold` at the canonical
(rebuild-`mkGen`) algebra with the Container left abstract.

`abbrev` (not `def`) so that `RawTerm.applyMorphism` is reducibly equal to each
twin: `RawTerm.rename` and `RawTerm.subst` are DEFEQ instances of it, pinned by
`rename_eq_applyMorphism` / `subst_eq_applyMorphism` below. -/
abbrev RawTerm.applyMorphism {Container : Nat → Nat → Type}
    [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    (morphism : Container sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm targetScope :=
  fold GenAlgebra.canonical morphism sourceTerm

/-- The raw-term morphism action on a children spine — the sibling of
`RawTerm.applyMorphism` through the children engine, of which
`RawTermChildren.rename` and `RawTermChildren.subst` are the two instances. -/
abbrev RawTermChildren.applyMorphism {Container : Nat → Nat → Type}
    [LiftsRaw Container] [ActsOnRawTermVar Container]
    {parentSourceScope parentTargetScope : Nat} {binderShifts : List Nat}
    (morphism : Container parentSourceScope parentTargetScope)
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren binderShifts parentTargetScope :=
  foldChildren GenAlgebra.canonical morphism children

/-- **The defeq pin (rename side)**: `RawTerm.rename` IS the morphism action at the
`RawRenaming` Container — held by `rfl`, so every generic morphism theorem lands on
the renaming twin's statement with no transport. -/
theorem rename_eq_applyMorphism {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming sourceTerm
      = RawTerm.applyMorphism rawRenaming sourceTerm :=
  rfl

/-- **The defeq pin (subst side)**: `RawTerm.subst` IS the morphism action at the
`RawTermSubst` Container — held by `rfl`. -/
theorem subst_eq_applyMorphism {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst substitution sourceTerm
      = RawTerm.applyMorphism substitution sourceTerm :=
  rfl

/-- The children-spine defeq pin (rename side). -/
theorem renameChildren_eq_applyMorphism {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (children : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.rename rawRenaming children
      = RawTermChildren.applyMorphism rawRenaming children :=
  rfl

/-- The children-spine defeq pin (subst side). -/
theorem substChildren_eq_applyMorphism {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (children : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.subst substitution children
      = RawTermChildren.applyMorphism substitution children :=
  rfl

/-- ★ **The closed universe-code cell is fixed by EVERY raw-term morphism.**  The
generic brick behind `rename_universeCodeCell` and `subst_universeCodeCell`: a
universe code is a nullary non-variable cell (`.mkGen .gen_universeCode _ .childNil`,
`CellConstructors.lean:38-40`), so the canonical fold rebuilds it unchanged whatever
the Container does to variables and binders.  Holds by `rfl` at the concrete
generator, exactly as each twin does. -/
theorem applyMorphism_universeCodeCell {Container : Nat → Nat → Type}
    [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    (morphism : Container sourceScope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.applyMorphism morphism (universeCodeCell levelExpr flag)
      = universeCodeCell levelExpr flag :=
  rfl

/-- The closed empty-type cell is fixed by every raw-term morphism — the nullary
sibling of `applyMorphism_universeCodeCell`. -/
theorem applyMorphism_emptyTypeCell {Container : Nat → Nat → Type}
    [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    (morphism : Container sourceScope targetScope) :
    RawTerm.applyMorphism morphism (emptyTypeCell (scope := sourceScope))
      = emptyTypeCell :=
  rfl

/-- ★ **A NON-VARIABLE cell's head generator is preserved by EVERY raw-term
morphism.**  The generic brick behind `RawTerm.rename_mkGen_of_ne_var` and
`RawTerm.subst_mkGen_of_ne_var` (`RawTermFoldNonVarCommute.lean`): both are this
lemma's two instantiations, since both are `fold` at the canonical algebra and
`fold_mkGen_of_ne_var` is already generic in the Container.  The morphism reaches
its variable action ONLY at `.gen_var`; away from it the canonical fold rebuilds
the same generator over transported children, whatever the Container does.

This is the exact boundary of the collapse: it says nothing about the variable
case, where `rename` and `subst` genuinely diverge (`ActsOnRawTermVar.varToRawTerm`
re-wraps a variable for `RawRenaming`, returns an ARBITRARY term for
`RawTermSubst`). -/
theorem RawTerm.applyMorphism_mkGen_of_ne_var {Container : Nat → Nat → Type}
    [LiftsRaw Container] [ActsOnRawTermVar Container]
    {sourceScope targetScope : Nat}
    (morphism : Container sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (children : RawTermChildren generator.binderShifts sourceScope) :
    RawTerm.applyMorphism morphism (.mkGen generator payload children) =
      .mkGen generator
        (Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope ▸ payload)
        (RawTermChildren.applyMorphism morphism children) := by
  rw [show RawTerm.applyMorphism morphism (RawTerm.mkGen generator payload children)
        = fold GenAlgebra.canonical morphism (.mkGen generator payload children) from rfl,
    fold_mkGen_of_ne_var GenAlgebra.canonical morphism hNotVar,
    GenAlgebra.canonical_algebra_eq_mkGen]

end FX1Poly.Typed
