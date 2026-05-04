import LeanFX2.Term.Act
import LeanFX2.Smoke.AuditMegaZ5A1

/-! # AuditMegaZ5A — Zero-axiom audit for Term.act.

## What Z5.A ships

Z5.A delivers `Term.act` — a typeclass-dispatched typed-Term action
engine that generalises `Term.rename` and `Term.subst` into a unified
operation parameterised by a `Container` with an `Action` instance.

Architectural choice: thin wrapper over the existing `Term.rename` /
`Term.subst` engines.  Each per-Container instance casts the result
type indices via the Z2.B bridges (`Ty.act_eq_rename` /
`Ty.act_eq_subst`) and the Z2.A.1 raw bridges (`RawTerm.act_eq_rename`
/ `RawTerm.act_eq_subst_forRaw`).  This delivers a unified `Term.act`
API while preserving existing infrastructure unchanged — the goal of
Tier 3 / MEGA-Z5.A.

## Files modified by Z5.A

* NEW `LeanFX2/Term/Act.lean` — `TermActCompat` typeclass + 2
  instances (`RawRenaming`, `Subst level`) + `Term.actRenaming` +
  `Term.actSubst` thin-wrapper engines.
* `LeanFX2.lean` — import line for `LeanFX2.Term.Act`.
* NEW `LeanFX2/Smoke/AuditMegaZ5A.lean` (this file).

## Audit philosophy

Z5.A is a CAPABILITY-EXPANDING refactor: it adds new definitions
(typeclass + instances + 2 wrapper engines) without modifying any
existing definition or theorem.  The wrappers delegate the recursion
to `Term.rename` / `Term.subst`, then cast via Z2.B / Z2.A.1 bridges
that are themselves zero-axiom.  This file gates:

1. The 2 cast-law instances (`TermActCompatOfRawRenaming`,
   `TermActCompatOfSubst`).
2. The 2 wrapper engines (`Term.actRenaming`, `Term.actSubst`).
3. Per-instance `rfl` smokes demonstrating `Term.actRenaming` /
   `Term.actSubst` reduce correctly on representative ctors.
4. The `Term.toRaw = rfl` invariant per smoke.
5. Headliner regression: `subst_compatible_paired_allais` (Pattern
   3), the W8 confluence chain, Heterogeneous Univalence,
   Univalence, and `funext` — all must remain zero-axiom.
6. Z2.B / Z2.6 / Z2.A.1 / Z4.A / Z5.A.1 downstream invariants — must
   stay clean since Z5.A only adds, never modifies.
-/

namespace LeanFX2

-- ============================================================
-- Section 1: rfl smoke — Term.actRenaming on Term.unit
-- ============================================================
-- The simplest case: Term.unit acts to Term.unit under any renaming.
-- Demonstrates that the wrapper composes its casts cleanly on a
-- leaf ctor.

/-- rfl smoke (RawRenaming, unit): renaming Term.unit produces Term.unit. -/
example {mode : Mode} {level scope targetScope : Nat}
    (sourceCtx : Ctx mode level scope)
    (targetCtx : Ctx mode level targetScope)
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    Term.actRenaming termRenaming
        (Term.unit (context := sourceCtx)) =
      ((Ty.act_eq_rename Ty.unit rho).symm ▸
         (RawTerm.act_eq_rename RawTerm.unit rho).symm ▸
           (Term.unit (context := targetCtx))) := by
  -- Both sides reduce to the same casted value.  HEq-shape
  -- alignment via rfl after the wrapper unfolds.
  rfl

-- ============================================================
-- Section 2: rfl smoke — Term.actRenaming on Term.boolTrue
-- ============================================================

/-- rfl smoke (RawRenaming, boolTrue): renaming Term.boolTrue stays
boolTrue.  Demonstrates the wrapper composes cleanly on another
leaf ctor. -/
example {mode : Mode} {level scope targetScope : Nat}
    (sourceCtx : Ctx mode level scope)
    (targetCtx : Ctx mode level targetScope)
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    Term.actRenaming termRenaming
        (Term.boolTrue (context := sourceCtx)) =
      ((Ty.act_eq_rename Ty.bool rho).symm ▸
         (RawTerm.act_eq_rename RawTerm.boolTrue rho).symm ▸
           (Term.boolTrue (context := targetCtx))) := by
  rfl

-- ============================================================
-- Section 3: rfl smoke — Term.actSubst on Term.unit
-- ============================================================

/-- rfl smoke (Subst, unit): substituting Term.unit produces
Term.unit.  Mirror of Section 1 over the Subst Container. -/
example {mode : Mode} {level scope targetScope : Nat}
    (sourceCtx : Ctx mode level scope)
    (targetCtx : Ctx mode level targetScope)
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    Term.actSubst termSubst
        (Term.unit (context := sourceCtx)) =
      ((Ty.act_eq_subst Ty.unit sigma).symm ▸
         (RawTerm.act_eq_subst_forRaw RawTerm.unit sigma).symm ▸
           (Term.unit (context := targetCtx))) := by
  rfl

-- ============================================================
-- Section 4: rfl smoke — Term.actSubst on Term.boolFalse
-- ============================================================

/-- rfl smoke (Subst, boolFalse): another leaf ctor over Subst. -/
example {mode : Mode} {level scope targetScope : Nat}
    (sourceCtx : Ctx mode level scope)
    (targetCtx : Ctx mode level targetScope)
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    Term.actSubst termSubst
        (Term.boolFalse (context := sourceCtx)) =
      ((Ty.act_eq_subst Ty.bool sigma).symm ▸
         (RawTerm.act_eq_subst_forRaw RawTerm.boolFalse sigma).symm ▸
           (Term.boolFalse (context := targetCtx))) := by
  rfl

-- ============================================================
-- Section 4.5: Term.toRaw invariant under Term.actRenaming / Term.actSubst
-- ============================================================
-- The toRaw projection IS the third Term index (Term.toRaw is
-- `@[reducible]` and just returns the implicit raw param).  Since
-- Term.actRenaming's output type has raw index `RawTerm.act raw
-- rho`, the projection is automatically that — by rfl.

/-- Term.toRaw invariant for Term.actRenaming on Term.unit.  The
projection equals `RawTerm.act RawTerm.unit rho`. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    (Term.actRenaming termRenaming
        (Term.unit (context := sourceCtx))).toRaw =
      RawTerm.act RawTerm.unit rho := rfl

/-- Term.toRaw invariant for Term.actSubst on Term.unit. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    (Term.actSubst termSubst
        (Term.unit (context := sourceCtx))).toRaw =
      RawTerm.act RawTerm.unit sigma := rfl

/-- Term.toRaw invariant for Term.actRenaming on Term.boolTrue. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    (Term.actRenaming termRenaming
        (Term.boolTrue (context := sourceCtx))).toRaw =
      RawTerm.act RawTerm.boolTrue rho := rfl

/-- Term.toRaw invariant for Term.actSubst on Term.boolFalse. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    (Term.actSubst termSubst
        (Term.boolFalse (context := sourceCtx))).toRaw =
      RawTerm.act RawTerm.boolFalse sigma := rfl

-- ============================================================
-- Section 5: type smoke — Term.actRenaming and Term.actSubst typecheck
-- ============================================================
-- Just verify the engines elaborate on their respective Containers
-- with a non-trivial ctor (Term.lam).  No `rfl` claim — only that
-- the result type is in the act-shape.

/-- Type smoke: Term.actRenaming on Term.lam produces a Term in the
act-shape.  Verifies the wrapper elaborates through a binder ctor. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons sourceCtx domainType) codomainType.weaken bodyRaw) :
    Term targetCtx (Ty.act (Ty.arrow domainType codomainType) rho)
                   (RawTerm.act (RawTerm.lam bodyRaw) rho) :=
  Term.actRenaming termRenaming (Term.lam body)

/-- Type smoke: Term.actSubst on Term.lam produces a Term in the
act-shape.  Mirror over the Subst Container. -/
example {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons sourceCtx domainType) codomainType.weaken bodyRaw) :
    Term targetCtx (Ty.act (Ty.arrow domainType codomainType) sigma)
                   (RawTerm.act (RawTerm.lam bodyRaw) sigma) :=
  Term.actSubst termSubst (Term.lam body)

end LeanFX2

-- ============================================================
-- Section 6: Audit gates for the new typeclass + 2 instances
-- ============================================================
-- The shipped declarations: TermActCompat typeclass + 2 instances
-- + 2 wrapper functions.  All must report "does not depend on any
-- axioms" under strict zero-axiom policy.

#print axioms LeanFX2.TermActCompat
#print axioms LeanFX2.TermActCompatOfRawRenaming
#print axioms LeanFX2.TermActCompatOfSubst
#print axioms LeanFX2.Term.actRenaming
#print axioms LeanFX2.Term.actSubst

-- ============================================================
-- Section 7: Headliner regression — Pattern 3 + W8 confluence
-- ============================================================
-- Z5.A must not regress the project's load-bearing zero-axiom
-- theorems.  The wrappers only call Term.rename / Term.subst, which
-- are unchanged; the Z2.B / Z2.A.1 bridges they cast through are
-- already zero-axiom (verified in AuditMegaZ5A1).  These should all
-- stay clean.

-- Pattern 3 (CUMUL-1.7) — Allais ICFP'18 paired-env subst_compatible.
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais

-- W8 — typed Tait-Martin-Löf chain.
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
-- Section 8: Z2.A / Z2.B / Z2.6 / Z4.A / Z5.A.1 chain regression
-- ============================================================
-- The Tier 3 prerequisite chain.  All entries must stay zero-axiom.

-- Z2.A.1 alignment + bridge theorems.
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

-- Z5.A.1 var-under-lift typeclass + 3 instances.
#print axioms LeanFX2.ActsOnRawTermVarLifts
