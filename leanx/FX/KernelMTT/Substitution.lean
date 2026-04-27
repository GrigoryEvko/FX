import FX.KernelMTT.Term

/-!
# Typed shift and substitution (W3)

Operational primitives for the well-scoped `Term : Nat → Type`
of W2.  Every reduction in V1.5+ (β, η, ι, ν) bottoms out in
either a shift or a substitution; making them typed at the
context-size index removes a class of "out-of-range index"
checker obligations from the trusted layer.

## API

  * `Term.shift cut : Term n → Term (n+1)` — insert a fresh
    variable at position `cut`, shifting all `var k` with
    `k ≥ cut` up by one.  `Term.shift0` is the common case
    (cut at 0).
  * `Term.substAt k arg : Term (n+1) → Term n` — substitute
    `arg` for variable `k`, decrementing all higher indices by
    one.
  * `Term.subst body arg : Term n` — β-substitution
    `body[0 := arg]`, the canonical form for application
    reduction.

All three thread through `TermArgs` via mutual `shiftArgs` /
`substAtArgs` definitions (W2's mutual TermArgs is the carrier
for variable-arity arg lists; List (Term n) cannot be a nested
inductive parameter when `n` is local).

## Type-level enforced range

Pre-W3 the legacy kernel's shift / subst returned the same
`Term` type and relied on the checker to verify that no var
ended up out-of-range.  Post-W3:

  * `shift cut t` returns `Term (n+1)` — the resulting term has
    one more free variable slot.  Constructing a `var` with
    index `n+1` in the input is impossible (W2's `Fin n`), so
    the output's `Fin (n+1)` slots are always safely fillable.
  * `substAt k arg body` returns `Term n` — the body had `n+1`
    free vars, after substituting one we have `n`.  The `Fin n`
    discipline forces the implementation to handle the three
    cases (i < k, i = k, i > k) so the output index is in range.

A buggy substitution that put `var n` (out of range) into a
`Term n` would not type-check.

## What stays fragile

Mode coherence is still a checker invariant — `var m k` claims
"variable k has mode m", but W2 doesn't enforce that the mode
matches the binder at position k.  Substitution preserves
whatever modes are recorded; if the input was mode-incoherent,
the output will be too.

## Termination

`shift` and `substAt` recurse strictly on subterms, so
structurally terminate.  Marked `partial def` because the mutual
through `TermArgs` plus the index-varying recursion (binder
bodies live at `n+1` / `n+2`) is non-trivial for Lean's
termination checker.  Same boundary as `Term.structEq` and
`eraseCoercions`.

## Trust layer

`FX/KernelMTT/**` is UNTRUSTED scaffold.  Zero `sorry`, zero
new axioms.  Soundness of the operations is established at
runtime via the W3 tests in `tests/Tests/KernelMTT/
SubstitutionTests.lean`; mechanized correctness theorems
(preservation under β-reduction etc.) are V_meta scope.

## Cross-references

  * `FX/KernelMTT/Term.lean` — the well-scoped Term inductive
    these operations manipulate
  * `FX/Kernel/Substitution.lean` — legacy un-indexed shift /
    subst (returns same `Term` type, relies on checker)
  * `fx_design.md` §30.2 — kernel β/ι/ν reduction depends on
    these primitives
-/

namespace FX.KernelMTT
namespace Term

mutual

/-- Shift all variables with index `≥ cut` up by one in `t`,
    producing a term in the context extended by a fresh binder
    inserted at position `cut`.  Variables below `cut` are
    unchanged.

    When recursing under a binder (lam, pi, sigma, modElim), the
    body's context extends by one, so the call uses `cut + 1`
    inside binder bodies. -/
partial def shift {n : Nat} (cut : Nat) : Term n → Term (n+1)
  | .var m i =>
      if i.val < cut then
        .var m ⟨i.val, by omega⟩
      else
        .var m ⟨i.val + 1, by omega⟩
  | .app m f a =>
      .app m (shift cut f) (shift cut a)
  | .lam m g d b =>
      .lam m g (shift cut d) (shift (cut+1) b)
  | .pi m g d b e =>
      .pi m g (shift cut d) (shift (cut+1) b) e
  | .sigma m g d b =>
      .sigma m g (shift cut d) (shift (cut+1) b)
  | .type m l =>
      .type m l
  | .forallLevel m b =>
      .forallLevel m (shift cut b)
  | .const m name =>
      .const m name
  | .ind m name args =>
      .ind m name (shiftArgs cut args)
  | .ctor m name idx ts vs =>
      .ctor m name idx (shiftArgs cut ts) (shiftArgs cut vs)
  | .indRec m name mot ms tgt =>
      .indRec m name (shift cut mot)
        (shiftArgs cut ms) (shift cut tgt)
  | .coind m name args =>
      .coind m name (shiftArgs cut args)
  | .coindUnfold m name ts arms =>
      .coindUnfold m name
        (shiftArgs cut ts) (shiftArgs cut arms)
  | .coindDestruct m name idx tgt =>
      .coindDestruct m name idx (shift cut tgt)
  | .id m ty l r =>
      .id m (shift cut ty) (shift cut l) (shift cut r)
  | .refl m w =>
      .refl m (shift cut w)
  | .idJ m mot base eq =>
      .idJ m (shift cut mot) (shift cut base) (shift cut eq)
  | .hit m name args =>
      .hit m name (shiftArgs cut args)
  | .hitMk m name idx ts vs =>
      .hitMk m name idx (shiftArgs cut ts) (shiftArgs cut vs)
  | .hitRec m name mot dms pps tgt =>
      .hitRec m name (shift cut mot)
        (shiftArgs cut dms) (shiftArgs cut pps)
        (shift cut tgt)
  | .modIntro src tgt mod inner =>
      .modIntro src tgt mod (shift cut inner)
  | .modElim src tgt mod modT body =>
      .modElim src tgt mod
        (shift cut modT) (shift (cut+1) body)
  | .transport ep src =>
      .transport (shift cut ep) (shift cut src)
  | .coerceCell mod fr to inner =>
      .coerceCell mod fr to (shift cut inner)

/-- Pointwise `shift` over a `TermArgs n`, lifting it to
    `TermArgs (n+1)`. -/
partial def shiftArgs {n : Nat} (cut : Nat) :
    TermArgs n → TermArgs (n+1)
  | .nil       => .nil
  | .cons h t  => .cons (shift cut h) (shiftArgs cut t)

end

/-- Common-case shift at the outermost cut (cut = 0): all
    existing variables move up by one to make room for a fresh
    var 0.  The dual of `subst` at index 0. -/
abbrev shift0 {n : Nat} (t : Term n) : Term (n+1) :=
  shift 0 t

mutual

/-- Substitute `arg` for variable index `k` in `t : Term (n+1)`,
    producing a term in `Term n`.  Variables with index `< k`
    pass through unchanged; variables `> k` decrement by one
    (since the binding at `k` has been eliminated).

    When recursing under a binder, the substitution position
    rises by one (`k.succ`) and `arg` shifts by one
    (`shift0 arg`) to account for the new binding. -/
partial def substAt {n : Nat} (k : Fin (n+1)) (arg : Term n) :
    Term (n+1) → Term n
  | .var m i =>
      if hlt : i.val < k.val then
        .var m ⟨i.val, by omega⟩
      else if heq : i.val = k.val then
        arg
      else
        .var m ⟨i.val - 1, by omega⟩
  | .app m f a =>
      .app m (substAt k arg f) (substAt k arg a)
  | .lam m g d b =>
      .lam m g (substAt k arg d) (substAt k.succ (shift0 arg) b)
  | .pi m g d b e =>
      .pi m g (substAt k arg d) (substAt k.succ (shift0 arg) b) e
  | .sigma m g d b =>
      .sigma m g (substAt k arg d) (substAt k.succ (shift0 arg) b)
  | .type m l =>
      .type m l
  | .forallLevel m b =>
      .forallLevel m (substAt k arg b)
  | .const m name =>
      .const m name
  | .ind m name args =>
      .ind m name (substAtArgs k arg args)
  | .ctor m name idx ts vs =>
      .ctor m name idx
        (substAtArgs k arg ts) (substAtArgs k arg vs)
  | .indRec m name mot ms tgt =>
      .indRec m name (substAt k arg mot)
        (substAtArgs k arg ms) (substAt k arg tgt)
  | .coind m name args =>
      .coind m name (substAtArgs k arg args)
  | .coindUnfold m name ts arms =>
      .coindUnfold m name
        (substAtArgs k arg ts) (substAtArgs k arg arms)
  | .coindDestruct m name idx tgt =>
      .coindDestruct m name idx (substAt k arg tgt)
  | .id m ty l r =>
      .id m (substAt k arg ty)
        (substAt k arg l) (substAt k arg r)
  | .refl m w =>
      .refl m (substAt k arg w)
  | .idJ m mot base eq =>
      .idJ m (substAt k arg mot)
        (substAt k arg base) (substAt k arg eq)
  | .hit m name args =>
      .hit m name (substAtArgs k arg args)
  | .hitMk m name idx ts vs =>
      .hitMk m name idx
        (substAtArgs k arg ts) (substAtArgs k arg vs)
  | .hitRec m name mot dms pps tgt =>
      .hitRec m name (substAt k arg mot)
        (substAtArgs k arg dms) (substAtArgs k arg pps)
        (substAt k arg tgt)
  | .modIntro src tgt mod inner =>
      .modIntro src tgt mod (substAt k arg inner)
  | .modElim src tgt mod modT body =>
      .modElim src tgt mod
        (substAt k arg modT)
        (substAt k.succ (shift0 arg) body)
  | .transport ep src =>
      .transport (substAt k arg ep) (substAt k arg src)
  | .coerceCell mod fr to inner =>
      .coerceCell mod fr to (substAt k arg inner)

/-- Pointwise `substAt` over a `TermArgs (n+1)`, lowering it to
    `TermArgs n`. -/
partial def substAtArgs {n : Nat} (k : Fin (n+1)) (arg : Term n) :
    TermArgs (n+1) → TermArgs n
  | .nil       => .nil
  | .cons h t  => .cons (substAt k arg h) (substAtArgs k arg t)

end

/-- β-style substitution: `body[0 := arg]`.  The canonical form
    for reducing `(λ x. body) arg`.  `body` lives in the context
    extended by `x`'s binding (`Term (n+1)`); after substitution
    the result lives in the original context (`Term n`). -/
abbrev subst {n : Nat} (body : Term (n+1)) (arg : Term n) : Term n :=
  substAt ⟨0, by omega⟩ arg body

end Term
end FX.KernelMTT
