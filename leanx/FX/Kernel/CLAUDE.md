# FX.Kernel — module-local design notes

Design decisions in the kernel that aren't obvious from types
alone.  Consult alongside `SPEC.md` §6 and `fx_design.md` §31.
Root project `CLAUDE.md` covers cross-cutting invariants (zero
`sorry` in `FX/Kernel/**`, 33-axiom AXIOMS.md allowlist, axiom-
audit CI gate); this file covers in-kernel choices.

## Trust layer and invariants

`FX/Kernel/**` is the TRUSTED layer.  Two hard invariants
enforced by `scripts/axiom-audit.sh`:

  * Zero `sorry` in `FX/Kernel/**` and `FX/Metatheory/**`.
  * Every `axiom` declaration must appear in `AXIOMS.md`'s
    allowlist; no axioms outside `FX/Kernel/**`.

When modifying kernel code, both gates must stay green at the
commit boundary.  A proof that genuinely needs new axioms
requires an RFC per `AXIOMS.md` before landing.

## Name-indirection for inductive specs (A1)

`Term.ind typeName typeArgs` and `Term.ctor typeName index
typeArgs valueArgs` reference inductive specs BY NAME, not by
direct spec payload.  The `IndSpec` structure lives in
`Inductive.lean`; `Inductive.specByName?` resolves the name at
every typing/reduction site.

**Why name-indirection:** the alternative — embedding `IndSpec`
inside `Term` constructors — creates a mutual inductive
dependency between `Term` and `IndSpec`.  Lean 4 handles this
but `Repr`/`Inhabited` derivation becomes finicky, `structEq`
grows nontrivially, and every walker crosses the mutual
boundary.  Keeping the spec outside `Term` and looking it up by
name is what both Lean and Coq do internally.  Named
indirection keeps `Term` syntactically pure.

## Zero-arg fn Unit-Pi translation (§31.7 uniform)

Every surface `fn name() : T with eff = body` elaborates
uniformly to `λ (_ :_ghost Unit). body : Π (_ :_ghost Unit) →
T @ eff`.  Rationale: per §31.7 every fn is a Pi at the kernel
level, effects live on the Pi's return-effect field, and
evaluation fires effects at App sites — never at bare name
references.  A fn with no surface parameters would otherwise
have no Pi to hang its effect row on; injecting the ghost
Unit binder keeps the kernel shape uniform.

Mechanism:

  * `Elaborate.elabFnSignature` — when `params.isEmpty`,
    synthesizes `[(ParamMode.ghost, "_", Term.ind "Unit" [])]`
    plus `Scope.empty.push "_"`.  Downstream `piFromTerm` and
    `lamFromTerm` wrap body/type with that single binder.
  * `Elaborate.elabExpr` App case — when `callArgs.isEmpty`,
    synthesizes `Term.app fnTerm (Term.ctor "Unit" 0 [] [])`
    so `f()` fires the declared effect at the matching
    Pi-elim.
  * `EffectInference.termEffect` — `.const` case is uniformly
    `Tot`.  The old "non-Pi declared type implies reference-
    fires-effect" special case is gone.
  * `Eval.evalDecl` — takes a decl's `type` alongside `body`;
    for the Unit-domain Pi shape, applies `Unit.tt` before
    evaluating so CLI/test output shows the inner `T` instead
    of `<closure>`.

The synthetic binder is `Grade.ghost`, so it's grade-0
(erased per §1.5, zero runtime cost).  Test helpers in
`Tests.ElabSupport.evalZeroArgBody` apply the Unit argument
when presenting the "value of a zero-arg fn" to unary-Nat or
Bool readers.

Pinning tests: `tests/Tests/Elab/ElaborateTests.lean` asserts
the exact Term-level shape of a zero-arg fn's body + type.
A12 E044 tests in `AdtTests.lean` exercise effect flow through
the synthesized Unit-Pi end to end.

## Term.const + GlobalEnv (A11)

`Term.const name` is the kernel's recursion-knot-tying
primitive (§10.15 opaque-by-default body visibility).  A
declaration's body may mention its own name as `Term.const`
without requiring the body to be closed over a self binder.

Resolution is an environment lookup.  Typing consults
`GlobalEnv.lookupType?` for the declared type; evaluation
consults `GlobalEnv.lookupBody?` for the body.  Opaque by
default — `whnf` only delta-reduces when the decl is marked
`@[transparent]` (Q41/Q46) OR when the caller has added the
name to the env's `revealedNames` list (Q45 — §10.15 `reveal
f;` inside verify blocks).  `Term.normalize` and `Term.convEq`
thread the same `globalEnv` through all recursive calls
(Q41), so a reveal added via `env.withReveal "f"` is visible
for the entire reduction/conversion trace.

**`@[transparent]` vs `withReveal` — two paths, one lookup.**
`unfold?` returns `some body` when EITHER the decl's
`transparent` flag is `true` OR the name appears in
`revealedNames`.  The flag is persistent and published
(visible in `fxi dump --kernel`); the reveal list is a
local override that lives in the caller's env snapshot.
This keeps the audit trail clean: a release-mode caller
without any `reveal` directives sees the module's declared
opacity unchanged, while a verify block that reveals a name
gets local unfolding without mutating any declaration.

**Two-pass `checkFile` invariant** (Q12/Q33): the elaborator
registers ALL signatures in pass 1, then type-checks bodies in
pass 2.  Every body seen in pass 2 can reference any other
decl via `Term.const`, resolving forward refs without requiring
dependency-ordered declarations.  Tests in
`tests/Tests/Elab/CrossDeclTests.lean` pin the invariant.

## Wood-Atkey Lam rule (§27.1 bug defense)

The `Pi-intro` rule uses **context division** per Wood/Atkey
2022, NOT the broken Atkey 2018 rule.  `G/g, x :_g A |-^1 b :
B` divides the context by the binder's grade; for usage, `1/w
= 0` means linear bindings are erased when constructing
replicable closures.

The Atkey-2018 witness (`tests/Tests/Metatheory/
UnsoundnessCorpusTests.lean`) MUST fail to type-check.  If a
refactor accidentally swaps back to the broken rule, the
corpus test is the canary.

## Partial grade operations (Tier L)

`Grade.add` and `Grade.mul` return `Option Grade`.  Three
dimensions have PARTIAL parallel/sequential combine:

  * **Overflow** (dim 16): `wrap + trap` is incompatible.
  * **Representation** (dim 10): `repr(C) + repr(packed)` is
    incompatible.
  * **Clock** (dim 12): `sync(a) + sync(b)` with `a ≠ b` is a
    cross-domain error (CD001).

When any partial dim reports `none`, the aggregator's `add`/
`mul` propagate the failure — the whole grade vector becomes
`some`-or-`none`.  Callers encountering `none` report the
dimension-specific error code (T047, CD001, O_mix).

Tests in `tests/Tests/Kernel/GradeTests.lean` (partial-op
rejection suite, Q5) pin the behavior.

## Fuel-bounded reduction

`whnf` and `normalize` take a `fuel : Nat` budget.  `defaultFuel
= 4096` is the kernel one-size-fits-all (Q1).  Exceeding fuel
returns the term unchanged; the typing layer reports `R_fuel`.

**Do NOT** reference `4096` directly anywhere — always go
through `Term.defaultFuel` so future tuning is a single-line
change.  The constant is calibrated against the current M1/M2
test suite with ~20× headroom.

## Identity / Quotient iota patterns (A3, A4)

`idJStep?` and `quotLiftStep?` helpers drop arguments that are
PURELY TYPING OBLIGATIONS and don't appear on the reduct:

  * `idJStep?` takes `(base, eqProof)` — the motive is consumed
    by typing (§31 H.6 Id-J), never by reduction.
  * `quotLiftStep?` takes `(lifted, target)` — the respects-
    proof and stored relation are purely typing.

This is a general pattern for eliminator iota: strip
type-only-carried data from the reduction helper's signature.
The stuck-form Value constructors (`neutralIdJ`,
`neutralQuotLift`) DO carry everything, for pretty-printing.

## Coinductive ν pattern (A5)

`nuStep?` is the dual of `iotaStep?` for codata.  Signature
`(specName, destructorIndex, target) → Option Term`.  Same
defensive shape as `iotaStep?`:

  * Target isn't a `coindUnfold` → `none` (stuck).
  * Unfold-spec-name disagrees with destructor-spec-name →
    `none` (defensive against hand-built ill-typed terms; the
    typechecker is the real guard).
  * Destructor index out of bounds relative to the unfold's
    arm list → `none` (same defensive-against-ill-typed-input
    rationale).

`coindUnfold` stores `typeArgs` alongside `arms`.  The typeArgs
are consumed by typing (they determine the `coind typeName
typeArgs` type of the introduced value) and **discarded at
reduction time** — the reduct is `arms[destructorIndex]`
alone.  Same "strip type-only-carried data from the reduct"
pattern as `idJStep?` / `quotLiftStep?`.

Arms are branches (like `indRec` methods): per-observation
usage is `countVarAtJoinList` in `Substitution.countVarAt`.
Multi-observation linearity (firing both `head` and `tail` on
the same value) is bounded by the Size dimension (§6.3 dim 20)
at typing — out of scope for countVarAt at the reduction
layer.

## Pi-η in Conversion (A6)

η is a **convertibility** rule (not reduction) per Appendix
H.9.  Lives in `Conversion.convEq`, not `Reduction.whnf`.

The match priority is load-bearing: the `(lam, lam)` arm fires
before `(lam, _)` / `(_, lam)` η arms.  This keeps two lambdas
with differing annotations un-convertible (η doesn't bridge
grade or domain mismatches — soundness critical).

## Subtyping (A7)

`subOrConv` handles Appendix H.9 T-sub cases:

  * U-cumul: `Type<u> <: Type<v>` when `u ≤ v`
  * Pi: contra-domain + co-codomain (strict grade equality)
  * Sigma: covariant in both (strict grade equality)
  * convEq fallback: equal things are trivially subtypes

**Grade subsumption on Pi/Sigma binders is strict equality,
not ≤.**  §6.2's direction on Pi binders is subtle; deferred
as A7-followup until a worked-out Wood-Atkey example clarifies
the direction.  Changing this without that clarification risks
silent soundness holes.

## Reserved error codes for deferred work

Error codes reserved in kernel doc comments, not yet emitted:

  * **T117** — method/motive type doesn't match expected Pi
    chain (indRec, idJ).  Full shape check deferred to A10.
  * **T118** — Quot.lift respects/motive shape check.
    Deferred to A10.
  * **M012** — monotonic × concurrent without atomic.  §6.8
    dimension-composition rule.

When adding the promised check, consult these reservations
to keep error-code taxonomy consistent.
