# FX.Eval — module-local design notes

The untrusted interpreter layer.  `partial def` is permitted
here (per `SPEC.md` §2 — L3 untrusted).  Consult alongside
`FX/Kernel/CLAUDE.md` for kernel-side design; this file covers
evaluation-specific choices.

## Trust status

`FX/Eval/**` is UNTRUSTED.  Axioms are forbidden by the
audit script (no axioms outside `FX/Kernel/**`), but `sorry`
is not checked here — though the project style discourages
`sorry` everywhere.  `partial def` is used liberally for
reduction-unbounded operations; the kernel's fuel bound is
NOT mirrored in the evaluator.

## globalEnv threading — explicit argument, NOT closure-captured

`Interp.applyValue`, `iotaValue`, `buildIotaSpine`, `applyAll`,
`idJValue`, `quotLiftValue` all take `globalEnv` as their FIRST
positional argument.  This is deliberate, not cargo-cult.

**Rationale:** globals are module-wide, not lexically captured.
When a `Value.closure` is applied from a different evaluation
site, it sees the CALLER'S globals, not the globals at closure
creation time.

For single-file `fxi run`, the distinction is invisible (one
module → one globalEnv).  But it matters for:

  * **Recursive functions** — `double`'s body references
    `Term.const "double"`, which resolves against globalEnv at
    every recursive call.  If closures captured globals at
    creation, pass-1 placeholder bodies would leak into later
    evaluations.
  * **Future module system** — closures returned across module
    boundaries see the consuming module's environment.

`Value.closure` stores only `captured : List Value` (locals).
Never hard-code globalEnv inside a Value.  The mutual block
in `Interp.lean` threads `globalEnv` uniformly (Q19).

## Stuck-form Value constructors

Three "neutral" / "stuck" Value forms preserve elimination
shape for pretty-printing when reduction can't proceed:

  * `neutral head spine` — stuck free var applied to args
  * `neutralRec specName motive methods target` — stuck ind
    eliminator (iota target isn't a ctor)
  * `neutralIdJ motive base eq` — stuck J (eq isn't a reflVal)
  * `neutralQuotLift lifted respects target` — stuck Quot.lift
    (target isn't a quotMkVal)

**Why preserve the motive/respects/methods on the stuck form:**
the pretty-printer (`Pretty.lean`) uses them to render a
readable trace.  Reduction itself discards these fields per the
kernel iota pattern (motive, respects are typing-only
obligations — see `FX/Kernel/CLAUDE.md` "Identity / Quotient
iota patterns").

## Introduction Value forms

`Value.reflVal witness` (A3) and `Value.quotMkVal relation
witness` (A4) are introduction forms — they represent runtime
proofs of `Id T w w` and quotient classes `⟦w⟧_R`
respectively.

Pretty-printer renders `refl(v)` and `⟦v⟧` via `Eval/Pretty.
lean`'s arms.  The relation on `quotMkVal` is stored but not
consumed at reduction — it mirrors Lean 4's `Quot.mk r a`
where `r` is part of the value's identity.

## isCanonical audit

`Value.isCanonical` distinguishes fully-reduced values from
stuck forms.  Every new Value constructor added to the sum
MUST get an explicit arm in `isCanonical` — Lean's pattern
match is exhaustive, so omission fails the build.  Pretty-
printer's `pretty` match has the same contract (documented in
`Pretty.lean`'s top-level coverage-audit docstring).

Canonical: closure, piType, sigmaType, ctor, indType, universe,
idType, reflVal, quotType, quotMkVal.

Not canonical (stuck): neutral, neutralRec, neutralIdJ,
neutralQuotLift.

## `applyValue`'s fallback semantics

The last arm of `applyValue`:

```
| unexpectedHead, argValue =>
  .neutral 0 [unexpectedHead, argValue]
```

Catches values that shouldn't normally appear in function
position (reflVal, quotMkVal, indType, etc.).  On well-typed
input, this arm is unreachable.  On ill-typed kernel terms
(hand-built for tests, or elaborator bugs), the fallback
degrades gracefully to a neutral — the pretty-printer still
renders, no crash.  Degradation is visible, not silent.

## Eval vs whnf — different reduction policies

Two reducers exist:

  * **Kernel `Term.whnf` / `Term.normalize`** (fuel-bounded;
    opacity respects `@[transparent]`) — used by typing/
    conversion.  Opaque consts stay `Term.const`.
  * **Eval `Interp.eval`** (unbounded `partial def`;
    unconditional const unfold) — used by `fxi run`.  Every
    `const` body is evaluated regardless of transparency
    (opacity is an SMT / conversion discipline, not a runtime
    policy).

The asymmetry is intentional.  Document at the `const` case in
`Interp.lean` explains why runtime unfolds everything.

## Pretty-printer fast paths

`Value.pretty` has two fast paths for readable output:

  * `asNat?` — a `ctor "Nat" k _ _` chain terminating at
    `Nat.Zero` renders as the integer literal (so
    `Nat.succ (Nat.succ Nat.zero)` prints as `2`).
  * `asBool?` — `ctor "Bool" 0 []` prints `false`,
    `ctor "Bool" 1 []` prints `true`.

When adding prelude inductives with similar "natural"
rendering (e.g. Option, List in future), extend with more fast
paths rather than relying on the generic ctor fallback.
