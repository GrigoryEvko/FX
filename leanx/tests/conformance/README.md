# Conformance suite (G5)

A directory of Phase-2 `.fx` programs that the full compile pipeline
should accept without error.  Drives `fxi test tests/conformance/`
as a regression net over surface features.

## What's here

Each `.fx` file exercises one or more surface features.  Every file
should type-check under `fxi check` — failures in this directory
are regressions in the compiler, not test intent.

Feature map (one line per representative file):

  * `01_identity.fx`               — polymorphic identity
  * `02_nat_literal.fx`            — Nat.Zero / Nat.Succ construction
  * `03_bool_const.fx`             — Bool.True / Bool.False refs
  * `04_match_nat.fx`              — pattern match on Nat scrutinee
  * `05_match_bool.fx`             — pattern match on Bool scrutinee
  * `06_if_else.fx`                — if/else expression on Bool
  * `07_let_simple.fx`             — plain let-binding
  * `08_rec_double.fx`             — self-recursive fn with decreases
  * `09_rec_length.fx`             — list-style recursion (Nat as fuel)
  * `10_multi_decl.fx`             — two decls with cross-reference
  * `11_type_param.fx`             — `<a: type>` at definition site
  * `12_type_param_apply.fx`       — use a poly fn with named type arg
  * `13_named_args.fx`             — multi-arg call with named arguments
  * `14_effect_io.fx`              — `with IO` annotation on signature
  * `15_effect_alloc.fx`           — `with Alloc` annotation
  * `16_effect_multi.fx`           — `with IO, Alloc, Async` row
  * `17_prim_i64.fx`               — `i64` in signature position
  * `18_prim_u8.fx`                — `u8` signature
  * `19_prim_char.fx`              — `char` signature
  * `20_prim_string.fx`            — `string` signature
  * `21_zero_arg_fn.fx`            — `fn main() : T = ...` Unit-Pi shape
  * `22_nested_match.fx`           — match inside a match arm
  * `23_const_decl.fx`             — `const NAME : T = val;`
  * `24_val_decl.fx`               — `val name : T;` forward decl
  * `25_match_bind.fx`             — `Succ(p) => ...` binding capture
  * `26_user_enum.fx`              — user-defined enum (3 nullary ctors)
  * `27_user_payload.fx`           — user-defined ADT with payload ctor
  * `28_param_ctor.fx`             — parameterized ADT + ctor type-arg inference
  * `29_lam_wildcard.fx`           — wildcard lambda via expected-type threading
  * `30_lam_destructure.fx`        — destructuring lambda via expected-type threading
  * `31_record_literal.fx`         — record `type T { f: U; }` + literal + field access
  * `32_for_loop.fx`               — `for i in 0..n; ... end for;` desugaring
  * `33_m2_records_blocks.fx`     — M2 milestone: records + let + blocks composed end-to-end
  * `34_m3_match_rec_loops.fx`    — M3 milestone: pattern matching + recursion + for-loops
  * `35_copy_attribute.fx`        — Q54: `@[copy]` on a type decl admits multi-use at the kernel layer
  * `36_nat_multiuse.fx`          — Q55: prelude Nat marked `isCopy` → classical Peano `times` runs clean
  * `37_let_multiuse.fx`          — Q56: let-bound Nat inherits copy-grade → multi-reference admitted
  * `38_forward_type_ref.fx`      — Q59: fn signature references a type declared later in the file
  * `39_forward_fn_display.fx`    — Q60: zero-arg fn body forward-refs fn declared later, displays right
  * `40_dot_shorthand.fx`         — Q61: `.field` dot-shorthand in a higher-order fn-arg position (§4.2)
  * `41_pipe_and_dot.fx`          — Q62: `|>` pipe + `.field` dot-shorthand — canonical §4.2 pipeline idiom
  * `42_logical_ops.fx`           — Q63: logical `not`/`and`/`or` keywords + precedence (§2.6)
  * `43_dot_rule_25.fx`           — Q65: §4.2 rule 25 — multi-dot expressions lift to a single `fn(it) =>` sharing one implicit element
  * `44_is_ctor_test.fx`          — Q66: §2.6 `is` constructor-test operator, composed with `not`/`and`/`or`
  * `45_propositional.fx`         — Q67: §2.6 propositional `==>` (implies) and `<==>` (iff) — truth tables + classical tautology
  * `46_nat_eq.fx`                — Q68: §2.6 Nat `==` / `!=` via prelude-seeded `nat_eq` kernel fn (double-indRec)
  * `47_nat_order.fx`             — Q69: §2.6 Nat `<` / `<=` / `>` / `>=` via shared `nat_lt` prelude fn (arg-swap + `not` wrapping)
  * `48_nat_arith.fx`             — Q70: §2.6 Nat `+` / `-` / `*` via `nat_add` / `nat_sub` (saturating) / `nat_mul` prelude fns; distributivity check
  * `49_list_literal.fx`          — Q71: §3.7 list literals `[a, b, c]` — element type from expected Pi, `Cons`/`Nil` over prelude `List` spec; nested + computed items
  * `50_bool_eq.fx`               — Q72: §2.6 Bool `==` / `!=` — polymorphic dispatch (synthesis probe picks Bool vs Nat); Bool literals, logical-op results, comparison results all `==`-compatible
  * `51_nat_div_mod.fx`           — Q73: §2.6 Nat `/` / `%` — `nat_div` fuel-bounded helper + `b == 0 → 0` guard; `nat_mod` derived as `a - (a/b)*b`; Euclidean identity verified
  * `52_classic_algorithms.fx`    — Q74: factorial / fib / gcd / pow / even-odd composing Q68-Q73; canary for the Q74 interp bug (eager `indRec` method eval was hanging `if`-recursion with `gcd`)
  * `53_option_ctor.fx`           — Q75: `Option(T)` promoted from `experimentalSpecs` to `preludeSpecs`; `Option.None` / `Option.Some(x)` construction with expected-type threading (incl. nested `Option(Option(Nat))`); match on Option deferred (scope-typed limitation)
  * `54_option_match.fx`          — Q76: match on parameterized inductives via Scope type hints; fn-param scrutinees typed `Option(T)` recover typeArgs for the motive (`unwrap_or_zero`, `is_some`, `double_or_zero`, Option over Bool)
  * `55_option_let.fx`            — Q77: let-bound `Option(T)` values work as match scrutinees too — `pushWithType` extends to both block-form letStmt and expression-form letBind; nested `Option(Option(Nat))` via chained let+match
  * `56_option_nested_match.fx`   — Q78: match arm ctor-arg bindings register their substituted types in Scope via new `scopeAndDepthForCtorTyped`; enables nested `match outer; Some(inner) => match inner; ...; end match; end match;` idiom
  * `57_pair.fx`                  — Q79: `Pair(T, U)` two-parameter spec promoted to prelude; MkPair construction + projection via match, mixed-type pairs (Nat/Bool), nested `Pair(Pair(Nat, Nat), Bool)` — exercises `Term.substParams`'s multi-param reversal
  * `58_list_ops.fx`              — Q80: recursive match on `List(Nat)` composed across the Q75-Q79 chain — `list_length` / `list_sum` / `list_is_empty` / `list_head_or` / `list_contains` via `match xs; Nil => ...; Cons(h, t) => ...` with self-recursion through `t` (scope-typed `List(Nat)` via Q78)
  * `59_match_wildcard.fx`        — Q81: wildcard arm `_ => body` as catch-all in match; synthesizes per-ctor arms from a wildcard pattern so exhaustiveness check passes; covers Nat, Option, List, Pair, and a user-defined enum (color)
  * `60_match_var_catchall.fx`    — Q82: variable-pattern arm `n => body` as match catch-all — synthesizes ctor-pattern arms and wraps the body in a β-redex `(λ n : scrutineeType. body) (Ctor(args))` so the body sees the reconstructed ctor value; covers Nat (including body using the bound var), Option, List, and a user-defined enum; the kernel reduces the β-redex during whnf at zero cost beyond the iota step it was already doing
  * `61_match_guards.fx`          — Q83: guarded match arms — `ctor(...) if cond => body` compiles to `if guard; body else catchAllBody` via `Term.indRec "Bool" boolMotive [catchAll, primary] guardTerm`; guards allowed on ctor-specific arms only with a mandatory unguarded catch-all (wildcard or var-pattern) for fallthrough; covers Nat, Option (with var-pattern catch-all exercising Q82's β-redex underneath), user-enum; deferred: guards on catch-alls (need a second fallthrough layer)
  * `62_match_as_pattern.fx`      — Q84: `pat as name` bindings — top-of-arm `as` extracts scrutinee reconstruction into a named binding; `Pattern.asPattern` AST constructor, `parsePatternBase` + `as IDENT` postfix in parser, `stripArmAsPattern` helper threads the as-name through classification; ctor-specific `Succ(p) as whole` reuses Q82's β-redex (`(λ whole. body) (Succ p)`) so both `p` and `whole` are in scope; `_ as name` canonicalises to var-pattern catch-all `name`; composes with Q83 guards; nested-arg `as` (e.g., `Some(Cons(h,t) as inner)`) parsed but rejected at elab (future task)
  * `63_match_nested_destructure.fx` — Q85: nested ctor-arg destructuring — `Some(Cons(h, _)) => h` compiles via AST-level rewrite: `rewriteNestedArgs` (MatchHelpers.lean) replaces the nested position with a fresh `__nested_arg_i` binder and synthesizes an inner `match` with the nested pattern and the outer catch-all body as arms; the recursive `elabExpr`/`elabMatch` then processes the inner match through the full Q81-Q84 pipeline; guards move INTO the inner arm so bindings resolve; requires unguarded wildcard catch-all (var/as-pattern catch-all binds the scrutinee, unavailable inside the synth inner match); scope: one nested position per arm, multiple deferred

## Adding new files

New entries arrive as PRs.  Each new file should:

  1. Be named `NN_concise_name.fx` (two-digit prefix for ordering).
  2. Pass `fxi check PATH.fx` on master.
  3. Include a header comment naming the feature(s) exercised.
  4. Get a one-line entry in the table above.

Do NOT put programs that SHOULD fail in this directory — use
`tests/Tests/Elab/` for explicit-rejection tests with the Lean
`expectElabError` harness.

## Running the suite

```sh
fxi test tests/conformance/
```

or via the CI-gate wrapper:

```sh
bash scripts/conformance.sh
```

Exit 0 when every file passes.
