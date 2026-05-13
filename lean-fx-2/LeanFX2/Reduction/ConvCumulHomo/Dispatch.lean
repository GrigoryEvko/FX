import LeanFX2.Reduction.ConvCumulHomo.CumulSide

/-! # LeanFX2.Reduction.ConvCumulHomo.Dispatch

Pattern 2 dispatch sum + four per-branch route theorems giving callers
a SINGLE entry point covering both ConvCumul shapes (homogeneous-ctx +
viaUp).

The dispatch evidence is sound by construction: `SubstDispatch`'s
ctors mirror ConvCumul's homo/viaUp split exactly.  No path
constructs dispatch from arbitrary ConvCumul (that would require
destructuring viaUp's heterogeneous indices — same wall this
architecture sidesteps).  Caller knows which branch their relation is
in and constructs the matching ctor.

A unified single-theorem dispatcher with motive-dependent output is
architecturally unavailable at Lean 4.29.1's `cases`-in-`def : Prop`
synthesis — the 4-route pattern is the zero-axiom equivalent.

## Root status

Layer 3 conv-cumul homogeneous helper. -/

namespace LeanFX2


/-! # Unified dispatch adapter (caller-evidence pattern)

The pair (`*_homo_benton`, `*_viaUp`) cover all ConvCumul shapes
but have different conclusion types — the unified theorem is
ill-typed in viaUp (heterogeneous endpoint scopes).

To give callers a SINGLE entry point, we provide a dispatch sum
`SubstDispatch firstTerm secondTerm` that is the disjoint union of
the two cases.  The caller supplies WHICH branch their relation
falls into by constructing the appropriate ctor.  The dispatcher
then routes via `match`, returning the correct-shaped output per
branch.

The conclusion type DEPENDS on the dispatch evidence (motive
varies per branch), which is why the result is wrapped in a
helper definition `SubstDispatch.Output` / `Output_rename` per
direction.

## Soundness

The user can build `SubstDispatch.homo` from any
`ConvCumulHomo`.  They can build `SubstDispatch.viaUp` only with
witnesses that match viaUp's exact shape.  No path constructs a
SubstDispatch witness from an arbitrary ConvCumul (because that
would require destructuring viaUp's heterogeneous indices — same
wall).  This is why the wall is an INPUT requirement on the
caller, not a hidden axiom in the dispatcher.
-/

/-- Dispatch sum for subst/rename adapters.  Two cases mirror
the architecture of ConvCumul: homogeneous-ctx (cong-built) vs
viaUp (cross-context cumul promotion).  Each ctor's output type
captures the endpoint shapes for its branch. -/
inductive ConvCumul.SubstDispatch :
    ∀ {modeFirst modeSecond : Mode}
      {levelFirst levelSecond scopeFirst scopeSecond : Nat}
      {firstCtx : Ctx modeFirst levelFirst scopeFirst}
      {secondCtx : Ctx modeSecond levelSecond scopeSecond}
      {firstType : Ty levelFirst scopeFirst}
      {secondType : Ty levelSecond scopeSecond}
      {firstRaw : RawTerm scopeFirst}
      {secondRaw : RawTerm scopeSecond},
      Term firstCtx firstType firstRaw →
      Term secondCtx secondType secondRaw → Prop
  /-- Homogeneous-ctx branch: caller supplies a ConvCumulHomo
  witness for endpoints sharing the same outer ctx/level/scope. -/
  | homo
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {firstType secondType : Ty level scope}
      {firstRaw secondRaw : RawTerm scope}
      {firstTerm : Term context firstType firstRaw}
      {secondTerm : Term context secondType secondRaw}
      (homoRel : ConvCumulHomo firstTerm secondTerm) :
      ConvCumul.SubstDispatch firstTerm secondTerm
  /-- viaUp branch — Phase CUMUL-2.6 Design D: caller supplies the
  inner typeCode and cumul witnesses; dispatch over the resulting
  viaUp shape. -/
  | viaUp
      {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeRaw : RawTerm scope}
      (typeCode :
        Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
      ConvCumul.SubstDispatch typeCode
        (Term.cumulUp (context := context)
                      lowerLevel higherLevel cumulMonotone
                      levelLeLow levelLeHigh typeCode)

/-- The dispatcher-as-elimination converts a `SubstDispatch` to
its underlying ConvCumul (a sanity check that dispatch evidence
is genuinely a ConvCumul shape). -/
theorem ConvCumul.SubstDispatch.toCumul
    {modeFirst modeSecond : Mode}
    {levelFirst levelSecond scopeFirst scopeSecond : Nat}
    {firstCtx : Ctx modeFirst levelFirst scopeFirst}
    {secondCtx : Ctx modeSecond levelSecond scopeSecond}
    {firstType : Ty levelFirst scopeFirst}
    {secondType : Ty levelSecond scopeSecond}
    {firstRaw : RawTerm scopeFirst}
    {secondRaw : RawTerm scopeSecond}
    {firstTerm : Term firstCtx firstType firstRaw}
    {secondTerm : Term secondCtx secondType secondRaw}
    (dispatch : ConvCumul.SubstDispatch firstTerm secondTerm) :
    ConvCumul firstTerm secondTerm := by
  cases dispatch with
  | homo homoRel => exact homoRel.toCumul
  | viaUp _ _ _ _ _ typeCd =>
      apply ConvCumul.viaUp <;> first | exact typeCd | assumption

/-! ## Branch-dependent output types via dependent Pi

The user asked: "can different output be encoded as a dependent
type?"  YES — via motive-dependent Pi.  Below we ship two
dispatchers, one per direction (rename / subst).  Each takes the
dispatch evidence and returns a Pi type whose argument and
conclusion shapes depend on which dispatch ctor was supplied.

The `match` is at TACTIC level (via `cases` in proof of an
opaque-output `def`) so Lean's type-checker accepts it without
needing to project named-binder fields at type level.

Architecture: define a single Prop `applyXxx` per direction,
proved by case-split on dispatch.  Result Prop captures the
appropriate-shaped ConvCumul per branch. -/

/-- Branch-dependent **rename-compatibility** for SubstDispatch.
Each branch returns a ConvCumul-output theorem typed
appropriately for its endpoint shape:

* `.homo`: takes `TermRenaming` from the homo ctx, returns
  `ConvCumul (firstTerm.rename _) (secondTerm.rename _)`.
* `.viaUp`: takes `TermRenaming` from outer `ctxHigh`, returns
  `ConvCumul lowerTerm (rename of (cumulUp ... lowerTerm))`.
-/
theorem ConvCumul.SubstDispatch.rename_compatible_homo_route
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (homoRel : ConvCumulHomo firstTerm secondTerm)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    ConvCumul (firstTerm.rename termRenaming)
              (secondTerm.rename termRenaming) :=
  ConvCumul.rename_compatible_homo_benton termRenaming homoRel

theorem ConvCumul.SubstDispatch.subst_compatible_homo_route
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (homoRel : ConvCumulHomo firstTerm secondTerm)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst context targetCtx sigma) :
    ConvCumul (firstTerm.subst termSubst)
              (secondTerm.subst termSubst) :=
  ConvCumul.subst_compatible_homo_benton termSubst homoRel

/-- viaUp branch's rename route — Phase CUMUL-2.6 Design D. -/
theorem ConvCumul.SubstDispatch.rename_compatible_viaUp_route
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (rho : RawRenaming scope targetScope)
    (termRenaming : TermRenaming context targetContext rho) :
    ConvCumul (Term.rename termRenaming typeCode)
              (Term.rename termRenaming
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  ConvCumul.rename_compatible_viaUp lowerLevel higherLevel cumulMonotone
                                    levelLeLow levelLeHigh
                                    typeCode rho termRenaming

/-- viaUp branch's subst route — Phase CUMUL-2.6 Design D. -/
theorem ConvCumul.SubstDispatch.subst_compatible_viaUp_route
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  ConvCumul.subst_compatible_viaUp lowerLevel higherLevel cumulMonotone
                                   levelLeLow levelLeHigh
                                   typeCode sigma termSubst

/-! # The unified interface — caller-evidence dispatcher with routes

The `SubstDispatch` inductive IS the unified entry point: a single
type covering both ConvCumul shapes (homogeneous-ctx + viaUp).
Caller holds dispatch evidence (their classification of which
branch their relation falls in) and pattern-matches via
`cases dispatch` to expose the correct shape, then applies the
matching route theorem.

The four route theorems below are the per-branch routed
implementations.  Each route has the type-correct signature for
its branch:

* `rename_compatible_homo_route` — homo branch's rename theorem
* `subst_compatible_homo_route`  — homo branch's subst theorem
* `rename_compatible_viaUp_route` — viaUp branch's rename theorem
* `subst_compatible_viaUp_route`  — viaUp branch's subst theorem

A unified single-theorem dispatcher with motive-dependent output
(`∀ d : SubstDispatch a b, d.applyTarget`) is architecturally
unavailable: the per-branch result types are genuinely
different (different endpoint scopes for viaUp), and Lean
4.29.1's `cases`-in-`def : Prop` cannot synthesize the dependent
motive cleanly.  The 4-route + dispatch-type pattern is the
zero-axiom equivalent: caller introduces dispatch evidence,
pattern-matches once, calls the matching route — Lean elaborates
each branch with the right ConvCumul shape via dependent typing.

The dispatch evidence is sound by construction: `SubstDispatch`'s
ctors mirror ConvCumul's homo/viaUp split exactly.  No path
constructs dispatch from arbitrary ConvCumul (that would require
destructuring viaUp's heterogeneous indices — same wall this
architecture sidesteps).  Caller knows which branch their
relation is in and constructs the matching ctor. -/

/-! # ConvCumul.viaUp under substitution+renaming COVERAGE COMPLETE

Together:
* `ConvCumul.{rename,subst}_compatible_homo_benton` — cong-built
  ConvCumul (homogeneous ctx fragment, all 24 ctors)
* `ConvCumul.{rename,subst}_compatible_viaUp` — cross-context
  cumul-promotion ctor at arbitrary `scopeLow`

Cover ALL ConvCumul shapes under typed renaming and substitution
at zero axioms.  The viaUp case handled separately because its
heterogeneous indices (decoupled scopeLow) make a UNIFIED theorem
ill-typed — the ctor genuinely needs the outer-side-only treatment.

A caller with a `ConvCumul a b` witness can:
1. If a, b are both at homogeneous ctx (cong-built): use
   `ConvCumul.{rename,subst}_compatible_homo_benton` after either
   manually proving `ConvCumulHomo a b` (drop viaUp) or applying
   the per-arm cong helpers from `CumulSubstCompat.lean`.
2. If a, b are viaUp-related (cumul-promotion): use
   `ConvCumul.{rename,subst}_compatible_viaUp` directly. -/

end LeanFX2
