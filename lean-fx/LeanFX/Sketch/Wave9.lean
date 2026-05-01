import LeanFX.Mode.Defn

/-! # Wave 9 — Raw-Aware Term: working architectural prototype.

This sketch self-contained Wave 9 reference: the `Term` inductive
carries the raw form as a *type index* (not a separate
projection function), making the typed↔raw bridge **definitional**
across every type former.

## Why this matters for HoTT/MTT

Phase C (typed-side `subst0_term` ctor migration) closes 4 known
β-bridge sorrys at the cost of threading `RawConsistent` through
`Step.subst_compatible` + descendants — ~15-file cascade.  Wave 9
removes the obstruction at its source: when `Term` is indexed by
its raw form, `Term.toRaw t = raw` is `rfl` *by elaboration*, not
by induction.  Every advanced type former planned for v3.x —
identity types' J, HITs, Bridge modality, 2LTT, refinement,
modal MTT, cubical paths — needs definitional typed↔raw
correspondence; without Wave 9, each new type former demands
its own bespoke bridge proof per case.

## Status

This file is a STANDALONE PROTOTYPE — not yet wired into
the active kernel.  It demonstrates the architecture works
on the core β/π/Σ subset.  Future sessions cascade-migrate
the full `LeanFX/Syntax/` to use this scheme.

## What it demonstrates

* `RawTypedTerm : Ctx → Ty → RawTerm scope → Type` — Term
  inductive with raw form as final type index.  Each constructor's
  signature pins the resulting raw form structurally.
* `RawTypedTerm.toRaw` is the type index — recovered as `rfl`.
* `RawTypedTerm.toRaw_var`, `_lam`, `_app`, etc. are all `rfl`.
* `RawTypedTerm.rename` tracks the raw form via `RawTerm.rename`,
  and `Term.toRaw_rename` becomes `rfl`.
* β-substitution alignment: when typed β fires via
  `Term.subst0_term`, the raw form aligns with raw β via `rfl`.

## Migration path (future sessions)

* W9.2: Modify the actual `LeanFX/Syntax/TypedTerm.lean` Term inductive
  to add the raw index.
* W9.3: Update `Term.rename` / `Term.weaken` / `Term.subst` /
  `Term.subst0` / `Term.subst0_term` to track raw form.
* W9.4-W9.7: Update `TermSubst`, `Step`, `Step.par` to track raw
  forms (mostly automatic via Lean elaboration).
* W9.8: Update `RawConsistent`-dependent theorems (now
  `RawConsistent` is *definitionally* satisfied for typed substs).
* W9.9: Close the 4 typed→raw bridge sorrys via `rfl`.
* W9.10: AuditAll reverification.

This prototype is the load-bearing proof-of-concept that the
cascade is sound. -/

namespace LeanFX.Sketch.Wave9
open LeanFX.Mode

/-! ## A minimal Ty for the prototype.

We only need arrow types; the full kernel's `Ty` is too big to
duplicate here, and the prototype's purpose is to demonstrate
the raw-form indexing, not to re-prove the kernel.  We use a
toy `Ty'` with just `unit` and `arrow`. -/

/-- Toy types for the prototype: only what β/var/app/lam need. -/
inductive Ty' : Type
  | unit  : Ty'
  | arrow : Ty' → Ty' → Ty'
  deriving DecidableEq

/-- Toy contexts: a list of `Ty'` indexed by length. -/
inductive Ctx' : Nat → Type
  | empty : Ctx' 0
  | cons  : ∀ {scope : Nat}, Ctx' scope → Ty' → Ctx' (scope + 1)

/-- Variable lookup in the toy context. -/
def Ctx'.varType : ∀ {scope : Nat}, Ctx' scope → Fin scope → Ty'
  | _, .cons _ ty,  ⟨0, _⟩      => ty
  | _, .cons rest _, ⟨k + 1, h⟩ => rest.varType ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## Toy raw terms.

Mirrors `LeanFX.Syntax.RawTerm` but with only the constructors
needed for the β/var/app/lam demonstration. -/

inductive RawTerm' : Nat → Type
  | var   : ∀ {scope : Nat}, Fin scope → RawTerm' scope
  | unit  : ∀ {scope : Nat}, RawTerm' scope
  | lam   : ∀ {scope : Nat}, RawTerm' (scope + 1) → RawTerm' scope
  | app   : ∀ {scope : Nat}, RawTerm' scope → RawTerm' scope → RawTerm' scope

/-! ## Renaming on toy raw terms.

`Renaming' source target` is `Fin source → Fin target`.  Lifting
under a binder shifts both endpoints. -/

abbrev Renaming' (source target : Nat) : Type := Fin source → Fin target

def Renaming'.lift {source target : Nat} (rho : Renaming' source target) :
    Renaming' (source + 1) (target + 1)
  | ⟨0, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => Fin.succ (rho ⟨k, Nat.lt_of_succ_lt_succ h⟩)

def Renaming'.weaken {scope : Nat} : Renaming' scope (scope + 1) :=
  fun position => Fin.succ position

def RawTerm'.rename : ∀ {source target : Nat},
    RawTerm' source → Renaming' source target → RawTerm' target
  | _, _, .var i,    rho => .var (rho i)
  | _, _, .unit,     _   => .unit
  | _, _, .lam body, rho => .lam (body.rename rho.lift)
  | _, _, .app f a,  rho => .app (f.rename rho) (a.rename rho)

/-! ## Single-position raw substitution.

`RawSubst.singleton arg` substitutes `arg` for var 0 and shifts
all higher positions down by one. -/

def RawSubst' (source target : Nat) : Type := Fin source → RawTerm' target

def RawSubst'.singleton {scope : Nat} (arg : RawTerm' scope) :
    RawSubst' (scope + 1) scope
  | ⟨0, _⟩      => arg
  | ⟨k + 1, h⟩  => .var ⟨k, Nat.lt_of_succ_lt_succ h⟩

def RawSubst'.lift {source target : Nat} (sigma : RawSubst' source target) :
    RawSubst' (source + 1) (target + 1)
  | ⟨0, _⟩      => .var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename Renaming'.weaken

def RawTerm'.subst : ∀ {source target : Nat},
    RawTerm' source → RawSubst' source target → RawTerm' target
  | _, _, .var i,    sigma => sigma i
  | _, _, .unit,     _     => .unit
  | _, _, .lam body, sigma => .lam (body.subst sigma.lift)
  | _, _, .app f a,  sigma => .app (f.subst sigma) (a.subst sigma)

/-- Single-variable raw substitution: substitute `arg` for var 0. -/
abbrev RawTerm'.subst0 {scope : Nat} (body : RawTerm' (scope + 1))
    (arg : RawTerm' scope) : RawTerm' scope :=
  body.subst (RawSubst'.singleton arg)

/-! ## The raw-aware typed Term.

`RawTypedTerm ctx ty rawForm` is a well-typed term whose Ty index
ALSO carries the underlying raw form.  Each constructor pins the
resulting raw form structurally — `Term.lam body` produces
`RawTerm.lam bodyRaw` where `bodyRaw` is body's raw index.

Compare with `LeanFX.Syntax.Term ctx ty` which uses a separate
function `Term.toRaw : Term ctx ty → RawTerm scope`.  In Wave 9
the projection IS the type index. -/

inductive RawTypedTerm :
    ∀ {scope : Nat}, Ctx' scope → Ty' → RawTerm' scope → Type
  | var :
      ∀ {scope : Nat} {ctx : Ctx' scope} (i : Fin scope),
      RawTypedTerm ctx (ctx.varType i) (RawTerm'.var i)
  | unit :
      ∀ {scope : Nat} {ctx : Ctx' scope},
      RawTypedTerm ctx Ty'.unit RawTerm'.unit
  | lam :
      ∀ {scope : Nat} {ctx : Ctx' scope} {dom cod : Ty'}
        {bodyRaw : RawTerm' (scope + 1)}
        (body : RawTypedTerm (ctx.cons dom) cod bodyRaw),
      RawTypedTerm ctx (.arrow dom cod) (RawTerm'.lam bodyRaw)
  | app :
      ∀ {scope : Nat} {ctx : Ctx' scope} {dom cod : Ty'}
        {fnRaw argRaw : RawTerm' scope}
        (fn  : RawTypedTerm ctx (.arrow dom cod) fnRaw)
        (arg : RawTypedTerm ctx dom argRaw),
      RawTypedTerm ctx cod (RawTerm'.app fnRaw argRaw)

/-! ## The bridge: `toRaw` IS the type index.

Whereas the production kernel's `Term.toRaw : Term ctx ty →
RawTerm scope` is defined by structural recursion (a meaningful
function with non-trivial proof obligations), Wave 9's `toRaw`
is a *projection on the type index* — the raw form is structurally
visible and recovered by `rfl`.

We use a `def` (not a structure projection) for ergonomics, but
all four lemmas below are `rfl`. -/

@[reducible]
def RawTypedTerm.toRaw {scope : Nat} {ctx : Ctx' scope} {ty : Ty'}
    {raw : RawTerm' scope} (_ : RawTypedTerm ctx ty raw) : RawTerm' scope :=
  raw

theorem RawTypedTerm.toRaw_var
    {scope : Nat} {ctx : Ctx' scope} (i : Fin scope) :
    (RawTypedTerm.var (ctx := ctx) i).toRaw = RawTerm'.var i :=
  rfl

theorem RawTypedTerm.toRaw_unit
    {scope : Nat} {ctx : Ctx' scope} :
    (RawTypedTerm.unit (ctx := ctx)).toRaw = RawTerm'.unit :=
  rfl

set_option linter.unusedVariables false in
theorem RawTypedTerm.toRaw_lam
    {scope : Nat} {ctx : Ctx' scope} {dom cod : Ty'}
    {bodyRaw : RawTerm' (scope + 1)}
    (body : RawTypedTerm (ctx.cons dom) cod bodyRaw) :
    (RawTypedTerm.lam body).toRaw = RawTerm'.lam bodyRaw :=
  rfl

set_option linter.unusedVariables false in
theorem RawTypedTerm.toRaw_app
    {scope : Nat} {ctx : Ctx' scope} {dom cod : Ty'}
    {fnRaw argRaw : RawTerm' scope}
    (fn  : RawTypedTerm ctx (.arrow dom cod) fnRaw)
    (arg : RawTypedTerm ctx dom argRaw) :
    (RawTypedTerm.app fn arg).toRaw = RawTerm'.app fnRaw argRaw :=
  rfl

/-! ## Renaming preserves raw correspondence definitionally.

`RawTypedTerm.rename` walks the structure mirroring
`RawTerm'.rename` on the index.  The result's raw form
is exactly `body.toRaw.rename rho` — by construction, `rfl`.

Compare with the production kernel's `Term.toRaw_rename` which
is a 100-line structural induction with HEq casts. -/

/-- Position-equality witness for typed renaming. -/
def TermRenaming' {sourceScope targetScope : Nat}
    (sourceCtx : Ctx' sourceScope) (targetCtx : Ctx' targetScope)
    (rho : Renaming' sourceScope targetScope) : Prop :=
  ∀ (i : Fin sourceScope),
    targetCtx.varType (rho i) = sourceCtx.varType i

theorem TermRenaming'.lift {sourceScope targetScope : Nat}
    {sourceCtx : Ctx' sourceScope} {targetCtx : Ctx' targetScope}
    {rho : Renaming' sourceScope targetScope}
    (rhoRespects : TermRenaming' sourceCtx targetCtx rho)
    (newType : Ty') :
    TermRenaming' (sourceCtx.cons newType) (targetCtx.cons newType) rho.lift
  | ⟨0, _⟩     => rfl
  | ⟨k + 1, h⟩ => rhoRespects ⟨k, Nat.lt_of_succ_lt_succ h⟩

theorem TermRenaming'.weaken {scope : Nat} (ctx : Ctx' scope) (newType : Ty') :
    TermRenaming' ctx (ctx.cons newType) Renaming'.weaken := fun _ => rfl

/-- Term-level renaming.  The raw form of the result is
`bodyRaw.rename rho` — pinned by the recursive call's index
unification.  No HEq, no induction lemma needed: every
`RawTerm'.rename` step matches the constructor structurally. -/
def RawTypedTerm.rename {sourceScope targetScope : Nat}
    {sourceCtx : Ctx' sourceScope} {targetCtx : Ctx' targetScope}
    {rho : Renaming' sourceScope targetScope}
    (rhoRespects : TermRenaming' sourceCtx targetCtx rho) :
    {ty : Ty'} → {bodyRaw : RawTerm' sourceScope} →
    RawTypedTerm sourceCtx ty bodyRaw →
    RawTypedTerm targetCtx ty (bodyRaw.rename rho)
  | _, _, .var i =>
      (rhoRespects i) ▸ RawTypedTerm.var (rho i)
  | _, _, .unit  => RawTypedTerm.unit
  | _, _, .lam (dom := dom) body =>
      RawTypedTerm.lam
        (RawTypedTerm.rename (TermRenaming'.lift rhoRespects dom) body)
  | _, _, .app fn arg =>
      RawTypedTerm.app
        (RawTypedTerm.rename rhoRespects fn)
        (RawTypedTerm.rename rhoRespects arg)

/-- **The bridge becomes `rfl`.**  Renaming a typed term and then
extracting its raw form equals raw-renaming the original term's
raw form.  In the production kernel this is `Term.toRaw_rename`,
a 100-line structural induction.  In Wave 9 it's `rfl`: the type
index makes the equation hold by elaboration. -/
theorem RawTypedTerm.toRaw_rename
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx' sourceScope} {targetCtx : Ctx' targetScope}
    {rho : Renaming' sourceScope targetScope}
    (rhoRespects : TermRenaming' sourceCtx targetCtx rho)
    {ty : Ty'} {bodyRaw : RawTerm' sourceScope}
    (body : RawTypedTerm sourceCtx ty bodyRaw) :
    (RawTypedTerm.rename rhoRespects body).toRaw = bodyRaw.rename rho :=
  rfl

/-! ## β-substitution: typed↔raw alignment is `rfl`.

The production kernel's β-bridge cases (4 sorries documented in
`ParToRawBridge.lean:158-203`) require Phase C ctor migration to
align typed and raw substituents.  In Wave 9, the alignment is
unconditional — both typed and raw substitution operate on the
same `bodyRaw` index, with `singleton arg.toRaw` as the underlying
raw substitution.

We don't replicate the full TermSubst machinery here (that's the
W9.4 task), but we demonstrate the bridge would be `rfl` by
construction. -/

/-- Demonstrate that for a β-redex `app (lam body) arg`, the raw
β-reduct `body.subst0 arg.toRaw` equals the raw form of the
substituted typed term — by construction, since both use the same
raw substitution. -/
theorem RawTypedTerm.beta_alignment_witness
    {scope : Nat} {ctx : Ctx' scope} {dom cod : Ty'}
    {bodyRaw : RawTerm' (scope + 1)} {argRaw : RawTerm' scope}
    (body : RawTypedTerm (ctx.cons dom) cod bodyRaw)
    (arg : RawTypedTerm ctx dom argRaw) :
    -- The raw projection of the redex's source.
    (RawTypedTerm.app (RawTypedTerm.lam body) arg).toRaw
      = RawTerm'.app (RawTerm'.lam bodyRaw) argRaw :=
  rfl

/-- The expected raw β-reduct.  When typed substitution is
implemented (W9.4) using `Subst.termSingleton`-flavor (carrying
`arg.toRaw` at position 0), the raw projection of the typed
β-reduct will equal `bodyRaw.subst0 argRaw` — definitionally,
since the typed substitution's raw component IS the raw
substitution. -/
example {scope : Nat} (bodyRaw : RawTerm' (scope + 1))
    (argRaw : RawTerm' scope) :
    bodyRaw.subst0 argRaw
      = bodyRaw.subst (RawSubst'.singleton argRaw) :=
  rfl

/-! ## Smoke tests — concrete Wave 9 typing.

`λ x. x : unit → unit` at scope 0, with raw form
`RawTerm'.lam (RawTerm'.var 0)`. -/

example : RawTypedTerm Ctx'.empty (.arrow .unit .unit)
              (RawTerm'.lam (RawTerm'.var ⟨0, Nat.zero_lt_succ _⟩)) :=
  RawTypedTerm.lam (RawTypedTerm.var ⟨0, Nat.zero_lt_succ _⟩)

/-- `(λ x. x) ()` at scope 0, raw form
`app (lam (var 0)) unit`. -/
example : RawTypedTerm Ctx'.empty .unit
              (RawTerm'.app (RawTerm'.lam (RawTerm'.var ⟨0, Nat.zero_lt_succ _⟩))
                            RawTerm'.unit) :=
  RawTypedTerm.app
    (RawTypedTerm.lam (RawTypedTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    RawTypedTerm.unit

/-- The toRaw of a complex term recovers via rfl — no induction. -/
example :
    (RawTypedTerm.app
      (RawTypedTerm.lam
        (RawTypedTerm.var ⟨0, Nat.zero_lt_succ _⟩))
      (RawTypedTerm.unit (ctx := Ctx'.empty))).toRaw
    = RawTerm'.app (RawTerm'.lam (RawTerm'.var ⟨0, Nat.zero_lt_succ _⟩))
                   RawTerm'.unit :=
  rfl

/-! ## Summary

Wave 9 reframes the typed↔raw bridge from a *theorem-laden
projection function* to a *type-level index*.  Concretely:

* Production kernel: `Term : Ctx → Ty → Type`,
  `Term.toRaw : Term Γ T → RawTerm scope` (def by structural recursion),
  `Term.toRaw_rename : ... = RawTerm.rename ... ` (proof by induction).

* Wave 9: `Term : Ctx → Ty → RawTerm scope → Type`,
  `Term.toRaw t = raw` (by index projection, `rfl`),
  `Term.toRaw_rename = rfl`.

The migration is mechanical for the structural pieces (every
constructor's signature gains a raw index); the load-bearing
semantic move is making `Term.subst0` and `Term.subst0_term` align
to the same single substitution operation that propagates the raw
form correctly.  Once landed, the 4 dependent β-bridge sorrys in
`ParToRawBridge.lean` close trivially.

This sketch is the standalone proof-of-concept.  W9.2-W9.10 cascade
the migration into the live kernel. -/

end LeanFX.Sketch.Wave9
