# FX Language Specification

FX is a dependently-typed language with a graded modal type
system.  Twenty-two graded dimensions compose pointwise on every
binding's grade vector, checked simultaneously by one kernel
parameterized by tier (§6.3).  The §6.8 collision catalog
(classified × Fail, borrow × Async, CT × Async, and so on) is the
finite set of dimension compositions the kernel rejects on
soundness grounds.  The same language describes ordinary FX code,
synthesizable hardware (`hardware fn` / `hardware module`
declarations producing Verilog), and the contracts that govern
data at every boundary between systems.

Every dimension defaults to the most restrictive setting.  The
programmer explicitly grants capabilities — duplication, mutation,
allocation, side effects, public exposure.  Unannotated code can
do almost nothing.  Annotated code can do exactly what was declared.
The source code is a complete capability manifest.


## 1. Introduction

### 1.1 The Twenty-Two Dimensions

Every value in FX carries properties along all applicable
dimensions.  Each dimension is a graded algebraic structure
(semiring / lattice / typestate / foundational / versioned)
checked by one kernel parameterized by tier (§6.3).  The
dimensions compose pointwise on the grade vector; the §6.8
collision catalog (classified × Fail, borrow × Async, CT × Async,
ghost × runtime, monotonic × concurrent, Staleness × CT,
Capability × Replay) is the set of compositions the kernel rejects —
they are not ad-hoc rules but missing edges in the mode theory,
surfaced at the source as compile errors.  The table below is the
canonical reference.

```
PROVABLE BY THE COMPILER

 #  Dimension        Tracks                          Default (restrictive)      Grant
 1  Type             what kind of data               required                   —
 2  Refinement       what constraints hold           none                       pre / post / { pred }
 3  Usage            how many times consumed         linear (exactly once)      affine / @[copy] / ghost
 4  Effect           what side effects occur         Tot (pure, terminating)    with IO / Alloc / ...
 5  Security         who can observe the value       classified                 unclassified / declassify
 6  Protocol         what message sequence           none                       session type
 7  Lifetime         how long the value is valid     explicit at every site     <r: region>, ref(r) T
 8  Provenance       where data originated           External at trust          source("x") / sanitize / validate
                                                     boundaries
 9  Trust            verification status of path     sorry                      proof / verified
10  Representation   memory layout                   opaque                     repr(C) / repr(packed)
11  Observability    whether traces reveal value     opaque / constant-time     transparent
12  Clock domain     which clock drives a signal     combinational              with Sync(clk)

PROVABLE BOUNDS (must be stated or marked unbounded)

13  Complexity       operation count                 must state or unbounded    cost O(n)
14  Precision        floating-point error bound      exact (lossless)           f32 / f64
15  Space            allocation bound                zero (stack only)          with Alloc(strategy)
16  Overflow         integer overflow behavior       arbitrary precision        with overflow(wrap)
17  FP order         evaluation order of floats      strict (deterministic)     with Reassociate

STRUCTURAL PROPERTIES

18  Mutation         what mutations are permitted    immutable                  ref mut / ref append
19  Reentrancy       whether fn may call itself      non-reentrant              rec / with Reentrant
20  Size             observation depth for codata    required on codata         sized s; / with Productive

EVOLUTION

21  Version          code identity across revisions  implicit version(1)         @[version(N)] + refines /
                                                                                 migration (§15)

ASYNC ADMISSION

22  Staleness        admission delay on async event  fresh (tau = 0)             with Stale(tau_max);
                                                                                 stale(t, tau) on values
```

Wall-clock concerns the kernel cannot statically prove (energy
consumption, latency bounds, hardware clock rate) are not built-in
dimensions.  They are stdlib-supplied user-defined dimensions
(§6.6) whose tracking is annotation-only — the compiler propagates
the declared bound through composition but cannot verify the
underlying physical claim.  Library: `Std.Budget` ships `Energy`,
`Latency`, `Power`, `WallClock` as user-defined Tier-S dimensions
ready to import.

Every annotation the type system uses is written explicitly at the
binding or call site.  FX has no implicit inference of kinds, lifetimes,
effect variables, lambda parameter types, let-binding types, grade
parameters, variance, numeric widening, or control-flow propagation.
Mechanical desugaring (pipe, dot-shorthand, elif merge, trailing
comma, f-string expansion) is preserved because it is syntactic
rewriting, not semantic inference.  This is the rigor-first rule;
see Appendix E.

Dimensions that cannot be proved by any compiler — wall-clock time,
energy consumption, hardware clock rate — are not in this table.
They exist as library-level phantom types for annotation and basic
consistency checking, but the compiler does not guarantee them.

### 1.2 Design Principles

FX is built on a short list of commitments.  Capabilities are denied
by default and granted explicitly in the signature.  Types are
expressions, checked bidirectionally against a small kernel calculus.
Behavior is defined at every reduction step.  The kernel is finite
and enumerable per definition.  Every annotation the type system
uses is written by the programmer at the binding or call site; the
elaborator never guesses a grade, an effect, a lifetime, or a kind.

**Capabilities in the signature.**  Every effect a function may
perform, every ownership mode on its parameters, every security
label it handles, every lifetime it depends on, and every
refinement it maintains is written in its signature.  `fn f() :
i64` has no effects, allocates nothing, mutates nothing, and takes
no ownership; `fn g(own x: handle, ref mut buf: buffer(u8)) : nat
with IO, Alloc, Fail(io_error)` says precisely what it does.  The
compiler verifies the body's behavior matches the signature — a
body that does more than the signature declares is a compile
error, not a warning (§9.1, §7.2).  Readers learn what a function
can do without reading its implementation.

**Linear tracking for resources and protocols.**  File handles,
sockets, locks, database transactions, and session channels are
linear values: each is consumed exactly once as it flows through
the program.  Using a consumed value is rejected at elaboration;
failing to consume a live value at a function boundary is
rejected at elaboration.  Resource cleanup on failing paths uses
`defer` and `errdefer` (§7.11), and §1.4 records the precise
scope of the resulting guarantees.

**Information flow typed end to end.**  Data is classified by
default and cannot flow to an unclassified output without an
explicit `declassify` invoking a named policy (§12.4).  Tainted
user input cannot reach a typed sink without passing through a
declared sanitizer (§12.3).  The `CT` effect (§12.5) additionally
forbids secret-dependent control flow for constant-time code.
Noninterference is a theorem of the type system, not a best
effort.

**Dependently typed, one grammar.**  Types and expressions share a
single grammar.  `list(i64)` is an application; `if platform.simd
>= 256; avx2_kernel else scalar_kernel end if` is a valid type
when `platform.simd` is known at compile time.  The parser does
not distinguish types from values — the type checker does, via
bidirectional elaboration into the kernel calculus of §30.  Value
parameters propagate into types (`array(f32, n)` where `n : nat`),
and types may appear at compile time where values usually go
(`comptime fn sizeof<a: type>() : nat`).

**Defined behavior, declared capabilities.**  Argument evaluation
is left-to-right.  `int` and `nat` never overflow but require
`with Alloc`; fixed-width integers follow the declared overflow
mode (`exact` with a fit proof, or `wrap` / `trap` / `saturate`
declared in the signature — see §3.1, §3.8).  Floating-point is
strict IEEE 754 unless `with Reassociate` is declared.  Sort is
stable unless `with Unstable` is requested.  Hash-map iteration
order depends on the map type (§3.12) and programs that rely on
an unordered map's order are rejected.  No reduction step has
undefined behavior; no compiler optimization silently changes the
observable result unless a relevant capability is granted.

**Finite kernel, enumerable trust.**  The language stands on ~33
kernel axioms (Appendix H): universes, dependent product and sum,
one identity type, quotients, graded binders for Wood-Atkey 2022
context division, and one emit-table axiom connecting atomic
source operations to per-architecture instruction sequences
(§20.5).  Every surface feature in §3 – §26 has a Kernel
Translation subsection reducing it to these axioms.  `fxc
--show-axioms` prints the transitive axiom dependency of any
definition plus any `sorry`, `axiom`, or SMT-oracle discharges
it relies on.  The trusted base is enumerable per-definition
rather than global.  Reference implementation in Lean 4 (§30.8).

**The compiler as a proof partner.**  Refinement predicates and
`pre`/`post`/`decreases` clauses are discharged by an SMT oracle
at elaboration time (§10).  When a proof fails, the diagnostic
names the goal, the facts in scope, the gap, and a concrete FX
fragment that would close it (§10.10).  `sorry` compiles in dev
and sketch, is rejected in release, and propagates trust level
`Sorry` through the call graph (§10.6).  Proof work is
incremental (§10.13) and stable across edits that do not touch
the public surface (§28.1).

### 1.3 Dimensions Composing in a Single Signature

A single function can exercise many dimensions simultaneously:

```
pub fn encrypt_and_send<a: type, r: region, eff: effect>(
  plaintext: buffer(u8) { length(plaintext) > 0 },
  secret ref(r) key: aes_key,
  ch: channel(send(encrypted: bytes); end),
) : unit with IO, Crypto, Async, eff
  pre valid_key(key);
  post _ => channel_completed(ch);
begin fn
  let ciphertext = aes_encrypt(plaintext, ref key);
  send(ch, encrypted: ciphertext);
end fn;
```

At this one site the compiler checks: the buffer's element type
is `u8` and its length is bounded below by the refinement (type +
refinement, dims 1–2); `plaintext` is consumed exactly once and
`key` is only borrowed (ownership, dim 3); the key's borrow does
not outlive region `r` (lifetime, dim 7); only `IO`, `Crypto`,
`Async`, and the caller-supplied row `eff` are performed (effects,
dim 4); the channel advances through `send → end` in exactly one
call (protocol, dim 6); the secret key cannot flow to an
unclassified channel payload (security, dim 5); and `valid_key`
holds at entry while `channel_completed(ch)` holds at return
(refinements + SMT).  Relaxing any one of these annotations either
rejects the program or weakens a guarantee the caller depends on.

### 1.4 What the Type System Checks

The following bug classes are eliminated, rejected, or made
visible at compile time.  Each row names the mechanism and the
precise scope of the guarantee.  Readers should take the table
literally: some rows are elaboration-level impossibilities,
others depend on the programmer maintaining refinements, and a
few are capability declarations that surface the bug class in
the signature rather than remove it.

```
Bug class             Mechanism                               Scope of guarantee
────────────────────  ─────────────────────────────────────── ──────────────────────────────
Buffer overflow       index refinement i < length(a) +         compile-time SMT proof;
                      SMT discharge at each index site         programmer must carry the
                                                               length refinement through
                                                               the data flow
Use-after-free        linear ownership — a consumed value is   elaboration; the unsafe
                      unbound in subsequent scope              program does not typecheck
Double free           linear — a second consume computes to    elaboration
                      grade 1 + 1 = w, rejected for linear
Null dereference      no null constructor; option(T) forces    elaboration; null literal
                      a pattern match                          does not parse
Uninitialized read    linear — every binding has an            elaboration
                      initializer at its introduction
Data race             linearity ensures at most one writer on  elaboration for non-atomic
                      non-atomic memory; atomic<T> is the      memory; §11.10 atomics
                      only source of shared mutable access     model for shared access
Typed resource leak   linear — every linear value must be      elaboration for linearly-
                      consumed at the function boundary        typed resources.  User-level
                                                               "resources" not expressed as
                                                               linear values are not tracked.
Secret in logs        classified-by-default flow analysis;     compile-time flow analysis;
                      flow to IO requires declassify with a    bypass only through a named,
                      named policy                             auditable policy
SQL injection         taint_class + compiler-required          elaboration; tainted value
                      sanitize step before a typed sink        cannot reach the typed sink
Deadlock              session types with priority; waiting     elaboration for session-typed
                      on a lower-priority channel while        channels.  Waits that are not
                      holding a higher-priority channel is     session-typed (mutexes across
                      rejected                                 arbitrary shared state) are
                                                               not covered by this
                                                               mechanism.
Integer overflow —    int and nat are arbitrary precision      never overflows; arithmetic
  unbounded           and never truncate                        runs in heap-allocated
                                                               bignum (requires with Alloc
                                                               and warns if unbounded)
Integer overflow —    overflow mode must be declared in the    compile-time SMT proof for
  fixed-width         signature: exact (compiler proves fit),  'exact'; wrap / trap /
                      wrap, trap, or saturate (behavior        saturate do precisely what
                      declared in the signature)               their name says — the bug
                                                               class is made visible in the
                                                               signature rather than
                                                               eliminated
Stack growth —        decreases clause proves the recursion    compile-time termination
  termination         reaches a base case                      proof; does not bound call
                                                               depth against the process
                                                               stack size
Stack growth —        Alloc(Stack, bound: N) bounds every      compile-time check against
  stack size          frame in the call tree to N bytes        the declared bound; opt-in
                                                               per §19.5 — not the default
FP non-determinism    strict IEEE 754 and exact decimal by      compile-time; reordering
                      default; Reassociate must be granted      requires the explicit
                                                                Reassociate grant before it
                                                                can occur
Undefined behavior    every kernel reduction is defined; no    elaboration; every FX
                      'unsafe' keyword, no type-system bypass  program's semantics is
                                                               derivable from the kernel
                                                               of §30
```

`unreachable` is a valid expression only where the compiler can
prove the branch dead; reachable `unreachable` is compile error
R006.  `sorry` and `axiom` are per-definition escape hatches
tracked in the trust dimension (§10.6); their use is enumerable
via `fxc --show-axioms` and blocked from release builds except
through the rules of §1.6.

### 1.5 Compile-Time Erasure

Most dimensions have zero runtime cost.  The compiler checks them
during compilation and removes them from the binary; only the
information needed for execution remains.

```
Erased (zero runtime cost)             Survives in binary
─────────────────────────────          ─────────────────────────────
Refinements                            Machine code
Usage grades                           Data tags (ADT discriminators)
Security labels                        Vtable pointers (§16.5 existentials)
Protocol states                        Effect operations (IO, alloc)
Lifetimes                              Memory layout (repr attributes)
Provenance                             Trust boundary validators
Trust levels                            (generated from §14 contracts
Observability markers                   at IO / FFI / deserialization
Clock domains                           boundaries)
Complexity bounds
Precision bounds
Space bounds
Version labels
```

Erasure composes with dead-effect elimination (§21.4): a program
that declares no `Network` effect never links the `Network`
service module, regardless of symbol reachability.

### 1.6 The Two-Tier Safety Model

FX has no `unsafe` keyword and no surface-level type-system bypass.
This is a deliberate choice, not an omission — the language
provides escape hatches but typed and per-definition, with the
trust dimension propagating the cost through the call graph.
Users coming from Rust or Haskell should read the rest of this
section before concluding that FX is unworkably strict.

**Sketch mode** (§22) is TypeScript-permissive.  Missing type
annotations are inferred with warnings.  Proof obligations become
runtime assertions.  Linear cleanup becomes runtime `drop`.
Effects are inferred from the body rather than declared on the
signature.  The result compiles to a bytecode VM with sub-100ms
startup.  Every FX construct is valid in sketch mode; the type
system is present but lenient.  This is the profile for
exploration, prototyping, data-science notebook work, and any
code that is not yet ready for release.

**Release mode** requires every reachable function to reach trust
level `Verified` except on paths explicitly marked `Assumed`.
`sorry` is rejected, refinements must be discharged, effects
declared on the signature must match the body, and every linear
binding must be consumed.  This is the profile for compiled
libraries and published packages.

**Per-definition escape hatches.**  Between the two tiers, three
constructs let the programmer deliberately relax guarantees with
auditable accounting:

 * `sorry` is a placeholder for an unfinished proof (§10.6).
   Compiles in sketch and dev.  A function containing `sorry`
   receives trust level `Sorry`; every transitive caller inherits
   that level.  Rejected in release builds.

 * `axiom` declares a mathematical assumption without proof.
   Compiles in every profile but appears in `fxc --show-axioms`
   output and propagates a non-`Verified` trust level through the
   call graph.  Useful for foundational lemmas, FFI bridges where
   the compiler cannot verify external behavior, and axiomatized
   hardware semantics.

 * `with Div` on a `rec` function declares possible
   non-termination, relaxing the requirement that every recursive
   function carry a `decreases` clause.  Compiles but propagates
   `Sorry` trust.

**Trust algebra.**  The trust dimension (Tier S, dim 9) is the
five-element lattice

```
T = {External, Assumed, Sorry, Tested, Verified}
External < Assumed < Sorry < Tested < Verified
par_T(t1, t2) = min(t1, t2)
seq_T(t1, t2) = min(t1, t2)
```

The escape hatches contribute as follows:

```
trust(`sorry`)             = Sorry
trust(`axiom name (...);`) = Assumed
trust(`with Div` rec fn)   = Sorry
```

For a function `f` with body `b`:

```
trust(f) = min(trust(b), min over symbols s used in b of trust(s))
```

Trust propagates as the minimum across the body's syntactic
content and across the call-graph closure.  Release builds
enforce `trust(f) >= Verified` for every reachable `f` except
those marked `@[trust_assumed("rationale")]`, which permits
`Assumed` if and only if the programmer documents a justification
string surfaced by `fxi --show-axioms`.

These are FX's answer to `unsafe`: typed, scoped to a single
definition, tracked in the trust dimension, surfaced in
diagnostics, and audited at package publish time (§25.11).  Agent-
written packages that introduce a new `axiom`, a new `Fail`
effect, or a new `Alloc` capability push those changes through
the §14.10 contract diff, which computes a semver bump and
surfaces the trust delta to downstream consumers.  Unverified
assumptions cannot ship silently into the supply chain.


## 2. Lexical Structure

### 2.1 Source Encoding

Source files use UTF-8 encoding.  The file extension is `.fx`.  One
file defines one module.  There are no separate interface files;
visibility is controlled by `pub` on declarations.

### 2.2 Identifiers

Identifiers match `[a-zA-Z_][a-zA-Z0-9_]*`.  Only ASCII is
permitted in identifiers, operators, and keywords.  Unicode is
allowed in string literals and comments.  The single quote `'` is
not an identifier character — it does not appear anywhere in FX.

The compiler enforces naming conventions:

```
PascalCase     types, constructors, modules, traits, effects,
               machine states.  UserRecord, Some, IO, Connected.

snake_case     functions, variables, fields, type parameters,
               effect variables.  is_open, host, a, eff.

SCREAMING_SNAKE  constants only.  MAX_RETRIES, RESET_VECTOR.
```

Backticks escape any token to an identifier: `` `fn` ``, `` `let` ``,
`` `match` `` are plain identifiers regardless of what the token
normally means.

### 2.3 Keywords

The following tokens are reserved and cannot be used as identifiers
without backtick escaping.

```
affine       and          as           assert       await
axiom        begin        bench        bisimulation break
by           calc         catch        class        code
comptime     const        continue     codata       contract
decreases    decorator    declassify   defer        dimension
drop         dual         effect       else         end
errdefer     exception    exists       exports      extern
false        fn           for          forall       ghost
handle       hint         if           impl         in
include      instance     is           label        layout
lemma        let          linear       machine      match
module       mut          not          open         or
own          post         pre          proof        pub
quotient     receive      rec          ref          refinement
return       sanitize     secret       select       self
send         session      sorry        spawn        taint_class
tainted      test         true         try          type
unfold       val          verify       while        with
where        yield
```

Total: 92 global keywords.

The following tokens are contextual keywords, meaningful only inside
specific syntactic constructs:

```
Inside machine blocks:
  state  transition  initial  terminal
  emits  on_event  on_signal  priority  concurrency  atomic
  idempotent  commutative  inverse  on_fail  after  cancels
  preempts  refinement  bisimulation  actor
  (temporal properties use assert with LTL operators from std/ltl;
   structural predicates live in std/machine_props — see §13.5)

Inside register state machines:
  driven_by  when

Inside contract blocks:
  version  migration  compatibility  access  format

Inside hardware blocks:
  hardware  wire  reg  rising  falling  stage  emit  stall
  flush  forward  redirect  pipeline  onehot  register_file

Inside register blocks:
  field  virtual
  RW  RO  WO  W1C  W1S  RC  RS  RSVD

Inside effect blocks:
  multishot  subsumes

Inside class blocks:
  law

Inside test blocks:
  case  expect_compile_error  expect_accepted  matches
  test_machine  test_contract
```

The `ref` keyword is the borrow-mode declarator only (§7).  Mutable
heap cells are constructed via the stdlib function `cell(initial)`
(§4.6) with `.get()` / `.set(v)` methods — `cell` is not a reserved
keyword, it lives in the prelude alongside `option`, `list`, `result`.
The `layout` keyword replaces the hardware-only use of `format` for
bit layouts (§18.1); the contract-block `format` keyword keeps its
serialization-binding meaning (§14.4).  Variants of test
(`test_theory`, `test_metatheory`) and module (`module type`,
`module functor`) close with `end test` and `end module` respectively;
the variant is distinguished by an attribute (§23.6, §5.5).  Algebraic
structures use `@[structure] class` (§16.6) rather than a separate
`structure` keyword.

### 2.4 Literals

Integer literals: `42`, `0xFF`, `0b1010`, `0o77`.  Underscores
separate digit groups: `1_000_000`, `0xFF_FF`.

Sized integer literals carry a suffix: `42u8`, `42i32`, `42u64`.
Without a suffix, integer literals have type `int` (arbitrary
precision).

Decimal literals: `3.14`, `1.0`, `19.99`.  Dotted numeric literals
are exact decimals by default — no floating-point rounding.
`0.1 + 0.2 == 0.3` is always true.  Fixed-width decimal suffixes:
`3.14d64` (64-bit, 16 digits), `3.14d128` (128-bit, 34 digits).

Float literals require an explicit suffix: `3.14f32`, `1.0f64`.
IEEE 754 floats are approximate — the suffix is the programmer's
acknowledgment that rounding may occur.

String literals: `"hello"`, `f"value is {x}"` (format string),
`r"raw\nstring"` (raw, no escape processing), `b"bytes"`
(byte string).  The double quote `"` is the only quote character
in FX.

**Multi-line strings.**  All four string forms (`"..."`, `f"..."`,
`r"..."`, `b"..."`) may contain literal newlines.  The newline is
preserved in the string value as `\n`.  Escape sequences (`\n`,
`\t`, `\\`, `\"`) still work inside regular and f-strings; raw
strings skip all escape processing.  An unterminated string —
EOF before the closing quote — is compile error T058.

```
let prose =
  "The quick brown fox
jumps over the lazy dog.";
// value: "The quick brown fox\njumps over the lazy dog."

let sql = f"select {cols}
from {table}
where {pred}";
// multi-line f-string: literal newlines preserved, {...} still interpolated
```

**Triple-quoted strings.**  For indented multi-line literals,
every string prefix supports a triple-quoted form — `"""..."""`,
`f"""..."""`, `r"""..."""`, `b"""..."""` — with automatic
whitespace stripping (fx_lexer.md §5.6): the first newline after
the opening triple quote is stripped, trailing whitespace before
the closing triple quote is stripped, and the minimum common
leading indentation across non-blank lines is subtracted from
every line.  This matches Swift and Python 3.6+ heredoc
ergonomics.

```
let query = f"""
  select {cols}
  from {table}
  where {pred}
""";
// value: "select id, name\nfrom users\nwhere active\n"
// (common two-space indent stripped)
```

**Nested f-strings forbidden.**  Inside an f-string's `{...}`
interpolation, another f-string literal `f"..."` is compile error
T059 (`nested f-string; bind to a variable first`).  Plain
double-quoted strings and other expressions are fine inside
`{...}`.  When you need compound interpolation, compute the inner
string separately:

```
// forbidden:
// let s = f"outer {f"inner {x}"}";

// correct:
let inner = f"inner {x}";
let s = f"outer {inner}";
```

Rationale: nested f-string parsing has fragile edge cases (Python
3.12's PEP 701 is an entire grammar change) and produces unreadable
code.  One level is always enough after a single `let` lift.

**Character literals.**  There are no single-quoted character
literals.  A string literal of grapheme length 1 coerces to
`char` when the surrounding context expects `char`:

```
let c : char = "a";               // ok: grapheme length 1
let c : char = "é";               // ok: one extended grapheme cluster
let c : char = "ab";              // error T056: multi-character in char context
let c : char = "";                // error T057: empty string in char context
```

f-strings never coerce to `char` (they always produce `string`).
Non-literal string values of length 1 do not auto-coerce; use
`s.to_char()` with `with Fail(NotASingleChar)` (stdlib §26.2).

Bit literals: the width of a bit literal equals its digit count
(leading zeros significant, underscores excluded).  `0b1010` is
`bits(4)`, `0b00001010` is `bits(8)`, `0b0000_1010` is `bits(8)`.
Type ascription or suffix overrides: `let x : bits(16) = 0b1010` and
`0b1010u16` both produce a 16-bit value, zero-extended.  A literal
whose digit count exceeds the ascribed width is compile error T051.
FX has no `Nb` prefix — width lives in the digits (for exact
intent) or in the type (for explicit width with zero-extension).

Boolean literals: `true`, `false`.

### 2.5 Comments

Line comments begin with `//` and extend to end of line.
Block comments use `/* ... */` and do not nest.
Documentation comments use `///` and attach to the following
declaration.

### 2.6 Operators and Logic Keywords

Arithmetic: `+`, `-`, `*`, `/`, `%`.
Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`.
Logical: `not` (prefix), `and` (infix), `or` (infix).  These are
keywords, not symbols.  There are no `!`, `&&`, `||` tokens.
`not` sits just above `and` in the precedence table — below every
comparison and every `is` test — so `not x is None` parses as
`not (x is None)` and `not x > 5` parses as `not (x > 5)`.
Bitwise: `&`, `|`, `^`, `~`, `<<`, `>>`.
Constructor test: `is` (infix keyword) — `x is Some` returns `bool`.
Pipe: `|>` (forward pipe).
Arrow: `->` (function type), `=>` (match arm / lambda body).
Range: `..` (exclusive), `..=` (inclusive).
Spread: `...` (rest/spread in list patterns, record literals, and
format bindings — see rules 16-17 below).
Dot: `.` (field access, method call).

Full precedence and associativity table: Appendix F.  Chained
comparison (`0 < x < 10`) is not a valid expression in FX — it is
compile error T050 with suggestion `0 < x and x < 10`.  Every
pairwise comparison must be written explicitly (rigor-first).

**Operator dispatch.**  Arithmetic and bitwise operators (`+`,
`-`, `*`, `/`, `%`, `&`, `|`, `^`, `~`, `<<`, `>>`) are compiler
intrinsics for the built-in numeric / `bool` / `bits(n)` / ternary
types only.  User types do not extend them; they use named
methods instead (§16.8, §16.11).  Comparison operators (`==`,
`!=`, `<`, `<=`, `>`, `>=`) dispatch through the stdlib `Eq` and
`Ord` type classes (§16.11); any type instancing those classes —
typically via `@[derive(Eq)]` or `@[derive(Ord)]` (§16.10) —
participates.  Boolean `not`, `and`, `or` and the constructor
test `is` are intrinsics.  The pipe `|>` is a syntactic desugar
per §4.2.  The range operators `..` and `..=` produce `range<T>`
values.

### 2.7 Disambiguation Rules

Every token has one meaning.  Every ambiguity is a compile error.

 1. Semicolon after conditions: `if cond;`, `while cond;`,
    `for x in xs;`, `match e;` — always required.

 2. Angle brackets introduce, parentheses apply:
    `fn map<a, b>(...)` introduces type parameters.
    `list(i64)` applies a type constructor.

 3. `->` is the function type arrow.  `fn(x) => body` is a lambda.

 4. Function bodies use `= expr;` for one-liners or
    `begin fn ... end fn;` for blocks.

 5. Pipe fills the unnamed parameter:
    `x |> f(a: v1)` fills the one unnamed parameter of `f`.

 6. Every statement and declaration ends with `;`.  No exceptions.
    Block functions use `return expr;` to mark the return value.

 7. Named definitions require typed closers (`end fn`, `end match`,
    `end type`).  Lambdas use bare `end`.

 8. Modes are prefix: `own x`, `ref x`, `ref mut x`, `affine x`.
    No mode annotation means linear (default).

 9. Effect names are PascalCase.  Effect variables are snake_case.

10. `not` is boolean negation (keyword, not symbol).  `and` / `or`
    are logical conjunction / disjunction (keywords, not symbols).
    Dereference is `x.get()`.  There are no `!`, `&&`, `||`
    tokens in FX.

11. Types are expressions.  No separate grammar.

12. `comptime` marks compile-time evaluation.  No `#if` / `#elif`.

13. Backticks escape any token to an identifier.

14. Mutation uses `.set(value)` on `cell` types (heap-allocated
    mutable cells created by `cell(initial)`, §4.6) and on `ref mut`
    borrows.  In `hardware` blocks, register updates use
    `.set(value)` on `reg` types.  There is no `:=` operator.

15. Bit-level layouts use the `layout` keyword (`layout R : bits(32)
    = { ... };`, §18.1).  Wire-format serialization bindings inside
    `contract` blocks use the `format` keyword (`format json { ... };`,
    §14.4).  The two keywords never collide.

16. `{ }` is record or block in software.  Bit concatenation uses
    the `bits { a, b }` prefix.  In `hardware` blocks, bare
    `{ a, b }` is bit concatenation.  Record and format update uses
    spread: `{ ...base, field: value }` updates `base` by overriding
    `field` — one syntax for §3.4 records, §14.4 format overrides,
    and any other named-field update.  The spread element must come
    first; subsequent fields override.

17. `with` has exactly one meaning: effect annotation after a return
    type (`fn f() : T with IO, Alloc`, §9.1).  Record update and
    format override use spread `{...}` (rule 16); contract
    inheritance uses `extends` (§14.9); handler composition uses
    `handle` (§9.6).  `with` no longer has position-dependent
    meanings.

18. Local `fn` inside a block is `Tot` by default and does not
    inherit the enclosing function's effects.

19. Contradictory dimensions are compile errors.

20. Contract versions inherit the underlying type's refinements.

21. Session branching on secret data is forbidden in CT context.

22. Clock connections are explicit.

23. ASCII only in code.

24. Naming conventions are compiler-enforced (§2.2).

25. `.field` without a left operand in function argument position
    is shorthand for `fn(it) => it.field`.

26. `ref` has one meaning: borrow mode on bindings (`ref x: T`
    shared borrow, `ref mut x: T` exclusive borrow, `ref(r) T` at
    the type-expression level attaches region `r`).  Heap-allocated
    mutable cells are constructed with `cell(initial)` and read /
    written through `.get()` / `.set(v)`.  `ref` and `cell` are
    distinct keywords with no overlapping syntactic position.

27. Region parameters use kind form: `<r: region>` at the definition
    site (§3.13), `ref(r) T` at the use site, `static` as the
    top-of-lattice region constant (§8.1).  FX has no apostrophe
    sigil; lifetimes live in the kind system alongside `type` and
    `nat`.  The single quote does not appear in any FX source
    position.

28. `as` has two uses, both introducing a new name for an existing
    thing: pattern-binding `pat as name` inside `match` arms (§4.3)
    and import aliasing `open Lib as L` / `include Lib as L` (§5.5).
    **FX has no type-cast operator and no expression-level type
    ascription.**  Every value conversion is a named function or
    constructor, so the cost is visible at the call site:

    * Numeric widening: `widen<T>(x)` (§3.8)
    * Numeric narrowing: `narrow<T>(x) with Fail(range_error)`
    * Existential pack: construct the `exists T. { ... }` record
      directly (§16.5) — the programmer writes out the vtable
    * Layout reinterpretation: `R(bits)` where `R` is a `layout`
      declaration — parallel to `cell(0)` for cells, `Some(x)` for
      options.  Zero-cost view, not a conversion.

    `expr as T` in expression position is compile error T052.  The
    suggestion depends on the source and target types: numeric →
    `widen`/`narrow`, existential → build the record (§16.5),
    layout → `R(...)`.  Type-ascription-in-expression `(expr : T)`
    does not parse — use one of the named forms, or ascribe at the
    binding (`let x : T = expr;`).


## 3. Types

FX has no separate grammar for types and expressions.  Every type
is an expression and every expression can appear in type position.
The type checker, not the parser, determines whether an expression
denotes a type or a value.

### 3.1 Primitive Types

```
i8  i16  i32  i64  i128  i256  i512  i1024    signed fixed-width
u8  u16  u32  u64  u128  u256  u512  u1024    unsigned fixed-width
isize  usize                                   platform pointer width
int                                            arbitrary-precision signed
nat                                            arbitrary-precision unsigned (int { x >= 0 })
bool                                           true or false
char                                           Unicode scalar value
string                                         UTF-8 text, grapheme-clustered
frac64   frac128  frac256                        exact rational (iN/iN pair)
frac                                           arbitrary-precision rational
decimal                                        exact decimal, arbitrary precision
dec32  dec64  dec96  dec128                     fixed-width exact decimal
dec256  dec512  dec1024                         wide fixed-width exact decimal
f32                                            IEEE 754 single-precision float
f64                                            IEEE 754 double-precision float
unit                                           the type with one value, written ()
never                                          the empty type — no values, subtype of everything
```

**Fixed-width integers** are the preferred types for all code.  They
compile to bare machine operations.  Widths up to 128 bits map to
hardware instructions on modern targets (x86 has 128-bit SSE, ARM
has 128-bit NEON).  Widths 256-1024 compile to multi-word
arithmetic with statically known register allocation — no heap, no
branching, fully unrolled.  These cover every practical use case
including cryptographic keys (256/512), hash states (256/512), and
RSA moduli (1024).

Each fixed-width type is a refinement alias with a representation
annotation.  `u8` is `nat { x < 256 }` with `repr(bits(8))`.
`i32` is `int { -2^31 <= x and x < 2^31 }` with `repr(bits(32))`.
The `with overflow(wrap)` annotation on a function permits wrapping
arithmetic on fixed-width types.

**Fixed-width exact decimals** follow IEEE 754-2008 decimal
arithmetic.  `dec96` is a sweet spot on x86 — it fits in a single
SSE register and runs roughly 4x faster than `dec128`.  Wider
decimals (256-1024) use multi-word arithmetic like wide integers.

```
Type     Significant digits    Storage     Notes
dec32    7                     32 bits     compact, low precision
dec64    16                    64 bits     general purpose
dec96    24                    96 bits     SSE fast path on x86
dec128   34                    128 bits    IEEE 754 decimal128
dec256   71                    256 bits    multi-word
dec512   143                   512 bits    multi-word
dec1024  287                   1024 bits   multi-word
```

**Fixed-width exact fractions** store a numerator/denominator pair
of signed integers, normalized to lowest terms after each operation.
`frac64` is a pair of `i32` values, `frac128` is `i64/i64`,
`frac256` is `i128/i128`.  All fraction arithmetic is closed —
`frac + frac = frac`, `frac / frac = frac`.  No precision loss.
Stack-allocated, zero heap.

```
Type      Components     Range
frac64    i32 / i32      ratios up to ~2 billion
frac128   i64 / i64      ratios up to ~9.2 * 10^18
frac256   i128 / i128    ratios up to ~1.7 * 10^38
```

Intermediate blowup: chaining fraction operations grows numerator
and denominator.  `a/b + c/d = (a*d + c*b) / (b*d)` — after N
additions on frac64, the denominator can need 32*N bits.  The
compiler tracks worst-case bit growth through the expression and
auto-widens: a chain of frac64 operations may compile internally
as frac128 or frac256, narrowing back at the end if the result
fits.  When the compiler cannot prove the result fits in any
fixed-width frac, it requires `with Alloc` for arbitrary-precision
`frac`.

```
let a : frac64 = frac64(3, 7);
let b : frac64 = frac64(2, 5);
let c = a + b;                    // c : frac64 = frac64(29, 35)
let d = c / frac64(1, 12);       // d : frac64 = frac64(348, 35)
```

`frac` (no width suffix) is arbitrary-precision — numerator and
denominator are `int`.  Requires `with Alloc`.  Warns N001 like
`int` and `nat`.

**`int` and `nat` are arbitrary-precision.**  They never overflow.
They use a heap-allocated bignum representation at runtime and
require `with Alloc` on any function that creates or computes with
them.  The compiler emits a warning when `int` or `nat` is used
without a refinement that bounds the range:

```
warning[N001]: unbounded 'int' has arbitrary-precision runtime cost
  fn add(a: int, b: int) : int = a + b;
             ^^^     ^^^    ^^^
  Consider: i64, or add pre -2^63 <= a + b and a + b < 2^63
  Unbounded int requires with Alloc (heap-allocated bignum).
```

When a refinement is provided that bounds the range, the compiler
selects the narrowest fixed-width type and the warning is
suppressed.  No `Alloc` needed — the value fits in registers:

```
fn add(a: int, b: int) : int
  pre -1000 <= a and a <= 1000;
  pre -1000 <= b and b <= 1000;
= a + b;
// No warning.  Compiler uses i16 or i32 internally.
// No Alloc needed — bounded int is stack-allocated.
```

**When to use `int`/`nat`:**
- Ghost/proof contexts (grade 0, erased — no runtime cost).
- Specifications (`pre`, `post`, `decreases` — compile-time only).
- Mathematical libraries where arbitrary precision is the point.
- Prototyping in sketch mode (warnings are non-fatal).

**When to use fixed-width types:**
- All runtime computation where bounds are known.
- Performance-critical code (zero overhead, no branching).
- Public API boundaries (callers see concrete width).
- Cryptographic code (constant-width, no timing variation).

**Literal resolution.**  An unsuffixed integer literal `42` has
type `int` by default.  When the context expects a fixed-width
type, the literal is resolved to that type at compile time — no
runtime cost, no warning.  The compiler checks that the literal
fits in the target type:

```
let x : u8 = 42;         // 42 fits in u8, no warning
let y : i32 = 1000000;   // fits in i32, no warning
let z = 42;              // z : int, triggers N001 warning
let w : u8 = 300;        // error: 300 does not fit in u8
```

**Decimal and float literal resolution.**  Dotted numeric
literals (`3.14`, `1.0`, `19.99`) are `decimal` by default
(arbitrary-precision, requires `Alloc`, N001 warning if no
refinement bounds the exponent range).  With an explicit suffix
they resolve to the suffixed type: `3.14d64`, `3.14d128`,
`3.14f32`, `1.0f64`.  When the context expects a fixed-width
decimal or float, the literal resolves at compile time, no
warning — the compiler checks the literal fits the target type's
precision range (T060 `literal exceeds target precision` if it
does not).

Cross-family resolution is explicit — never implicit:

```
let d : dec64 = 3.14;          // ok, decimal literal resolves to dec64
let f : f32  = 3.14;           // ERROR: decimal literal does NOT auto-resolve
                                //        to float (lossy boundary)
let f : f32  = 3.14f32;        // ok, explicit float literal
let f : f32  = to_float(3.14); // ok, explicit lossy conversion
```

Refinement-narrowed types further constrain literal fit.  `let x
: u8 { x < 100 } = 50;` compiles; `let x : u8 { x < 100 } = 150;`
is compile error R005 (`literal violates type refinement`).

### 3.2 Bit Vectors

```
bits(n)          n-bit unsigned value, width known at compile time
signed_bits(n)   n-bit signed value, two's complement
trits(n)         n-trit balanced ternary value, digits T(-1), 0, 1
```

Ternary values use balanced ternary: digit T represents -1, so
negation is just flipping T and 1.  Ternary literals use the `0t`
prefix: `0t10T` is the trit sequence 1, 0, -1.  Fixed-width
ternary types use suffixes: `t6`, `t12`, `t24`, `t48`.

Bit slicing extracts a contiguous range:

```
fn extract_opcode(insn: bits(32)) : bits(7) = insn[6:0];
```

Bit concatenation joins values:

```
fn pack(hi: bits(4), lo: bits(4)) : bits(8) = bits { hi, lo };
```

Bit literal width equals the digit count written after the base
prefix (underscores excluded, leading zeros significant).  `0b1010`
is `bits(4)`, `0b00001010` is `bits(8)`, `0b0000_1010` is `bits(8)`.
Type ascription or suffix overrides and zero-extends:
`let x : bits(16) = 0b1010` and `0b1010u16` both give a 16-bit
value; the four literal digits are zero-extended to width 16.
A literal whose digit count exceeds the ascribed width is compile
error T051 (`bit literal width exceeds ascribed type`).  There is
no separate `Nb` prefix — width is either written in the digits or
declared in the type.

### 3.3 Algebraic Data Types

Variant types enumerate a fixed set of constructors:

```
type color
  Red;
  Green;
  Blue;
end type;

type option<a: type>
  None;
  Some(a);
end type;

type shape
  Circle(radius: f64);
  Rect(w: f64, h: f64);
end type;
```

Each constructor is PascalCase.  Constructor payloads use `()` —
the same syntax as constructor application.  There is no `of`
keyword and no `|` bars.  Each constructor is its own line,
terminated by `;`.

### 3.4 Records

Record types group named fields:

```
type config {
  host: string;
  port: nat;
  tls: bool;
};
```

Record construction: `config { host: "localhost", port: 8080, tls: true }`.
Field access: `cfg.host`.
Record update: `{ ...cfg, port: 9090 }`.  The spread element must be
first; subsequent fields override.  `{ ...cfg }` alone is a copy.

Fields use `:` as separator in both type definitions and value
construction.  The `=` sign is never used for record fields.  The
spread `...` is the only way to build a new record from an existing
one; `with` is reserved for effect annotations (rule 17).

### 3.5 Codata

Codata types are defined by their destructors rather than their
constructors.  They represent potentially infinite structures
that the kernel renders productive-by-construction via the
`later` modality (§6.10, Appendix H.7b).
Every codata type carries a size parameter `s : size` at the
surface level (dimension 20, §6.3) bounding the depth at which
the value may be observed; the size is the surface presentation
of the kernel's clock-quantified Later count.

```
codata stream<a: type>
  fn head(self) : a;
  fn tail(self) : stream(a);
end codata;
```

A value of type `stream<s>(a)` can be observed up to depth `s`.
Observing `head` costs 0 size units; observing `tail` costs 1
and produces a `stream<s - 1>(a)`.  Size is explicit at every
use site — there is no inference (rigor-first, §1.1, Appendix
E).

Values of codata types are created with `unfold`.  Construction
requires the `Productive` effect capability and a `sized` clause
declaring the size parameter:

```
fn rec nats_from<s: size>(n: i64) : stream<s>(i64)
  with Productive;
  sized s;
= unfold<s>
    head => n;
    tail => nats_from<s>(n + 1);
  end unfold;
```

**Typing rule (G-Unfold).**  Inside an `unfold<s>` body:

 1. `s : size` must be in scope and `s >= 1`.
 2. `with Productive` must appear in the enclosing function's
    effect row.
 3. Every recursive reference to the value under construction
    must appear strictly inside the body of a destructor clause,
    and the reference must be at a size no greater than `s`
    (typically the same `s`, since the enclosing destructor call
    will consume one size unit when observed).
 4. Productivity is checked by typed elimination of the `later`
    modality: a recursive reference inside a destructor body
    typechecks at type `later(self)`, where `self` is the codata
    type, and the destructor produces the next state at type
    `self`.  The fix combinator `fix : (later(a) -> a) -> a`
    (Nakano LICS 2000, kernel axiom Appendix H.7b) admits the
    construction; references outside a destructor body have no
    `later` insulation and fail the typed productivity check
    (compile error G001).  This subsumes the older Coppo-Dezani
    syntactic-guardedness rule with a typed discipline that
    composes uniformly across multi-destructor codata
    (Abel-Pientka POPL 2013 lifted to Later).

**Kernel translation.**  `codata Self with destructors d_1: A_1, ..., d_n:
A_n` translates to a `Coind` form (Appendix H.5) whose
guardedness predicate is replaced by `later`-typing of recursive
references; the surface size parameter `s` is the count of `later`
steps the value is insulated under, and the clock `clk` in the
underlying `later(t)` is implicit at the codata declaration.  Multi-
clock quantification — `forall(clk: clock), t(clk)` per Atkey-McBride
ICFP 2013 — gives the closure under arbitrary observation depth that
`sized s; with Productive` denotes at the surface for `s = omega`.

`with Div` escapes the productivity check for genuinely non-
productive definitions, declaring possible divergence.  The
resulting value's size is bottom; observations may diverge.
Functions with `Div` instead of `Productive` carry trust level
`Sorry` (§1.6) and are rejected in release builds unless
`@[trust_assumed("rationale")]` claims `Assumed` with
justification.  Sessions in their final form (§11.21,
Pfenning-Toninho corecursion via Later) drop `with Div` entirely
because session protocols are productive by construction; codata
values that genuinely need divergence (e.g. unbounded search)
retain the escape.

Consuming codata at a finite depth uses inductive recursion on
the consumer side with a refinement linking observation depth
to the source's size:

```
fn take<a: type, s: size>(n: nat, src: stream<s>(a)) : list(a)
  decreases n;
  pre n <= s;
= if n == 0; []
  else [head(src), ...take<a, s - 1>(n - 1, tail(src))]
  end if;
```

The `decreases n` gives termination of the consumer; the `pre n
<= s` gives the size grade check; no single recursive function
is both inductive and coinductive.

Hardware signals (§18.10) are sized codata: a `reg` under
`on rising(clk)` is a stream at size `omega` (clocks tick
forever by assumption); the underlying `later(clk)` count is the
clock period in cycles.  Temporal logic operators (§13.18) desugar to
sized-stream quantification at the corresponding clock.

### 3.6 Tensors

Tensor types carry their element type and shape at the type level:

```
tensor(f32, [batch, seq, dim])
```

Shape parameters are natural numbers.  Shape arithmetic is computed
at compile time.  Operations that require compatible shapes fail at
compile time when the shapes do not match:

```
fn matmul<a: nat, b: nat, c: nat>(
  x: tensor(f32, [a, b]),
  y: tensor(f32, [b, c]),
) : tensor(f32, [a, c])
  with Alloc;
```

Broadcasting follows standard rules and is checked at compile time.
If shapes are not broadcastable, the compiler rejects the expression.

### 3.7 Quotient Types

A quotient type identifies values that are equivalent under a
declared relation:

```
quotient type rat = (int, int { x != 0 })
  by fn((a, b), (c, d)) => a * d == b * c;
```

The compiler verifies the relation is reflexive, symmetric, and
transitive.  All functions on the quotient type must respect the
equivalence: equal inputs must produce equal outputs.

**Syntax.**  A `quotient type` declaration introduces a new type
abstracting over an equivalence class:

```
quotient_decl =
    QUOTIENT TYPE lower_ident type_params? "=" type BY expr ";"
```

`quotient` is a keyword (Appendix A, 92 globals).

**Defining functions on a quotient.**  Functions on the quotient
are defined via the stdlib primitive `Quot.lift` (from kernel axiom
Quot-lift, Appendix H.7).  The obligation that the function
respects the equivalence is a compile-time SMT obligation
expressed as a `pre` clause, not a runtime proof argument:

```
fn Quot.lift<t: type, r: t -> t -> bool, u: type>(
    f: t -> u,
    q: Quot(t, r),
) : u
  pre forall(x: t, y: t), r(x, y) ==> f(x) == f(y);

pub fn denominator(q: rat) : int
  // representative (a, b) satisfies b != 0; every equivalent
  // representative does NOT have the same b — so denominator
  // is NOT a well-defined function on rat.  The following
  // `Quot.lift` fails the `pre` obligation: the compiler emits
  // R001 "precondition not satisfied — extracted function does
  // not respect the quotient equivalence."
= Quot.lift(fn((_, b)) => b, q);
```

To define a respecting function, operate on a canonical form.
For `rat`, reduce to lowest terms first:

```
pub fn reduced_denominator(q: rat) : int
= Quot.lift(fn((a, b)) => { let (_, b') = reduce(a, b); b' }, q);
// `reduce` returns the normalized representative; since all
// equivalent (a, b) pairs reduce to the same lowest-terms
// representative, this respects the equivalence and the
// `pre` obligation discharges.
```

**Elimination.**  `Quot.lift` is the only way to consume a
quotient value.  There is no pattern-match escape to the
underlying representative — that would break the abstraction
barrier.

**Kernel translation: quotient as HIT.**  The kernel (§30,
Appendix H.7) does not have a dedicated Quot family.  Instead,
quotient types are higher inductive types (HITs) — inductive
types extended with path constructors that identify values
otherwise distinct.  The translation:

```
quotient type T = U by fn(x, y) => R(x, y);

  -- lowers to (Appendix H.7 HIT primitive)

hit_spec(
  name: "T",
  data_ctors: [ ctor("class", types: [U], result: T) ],
  path_ctors: [ ctor("eq",
                     binders: [("x", U), ("y", U)],
                     hypotheses: [R(x, y)],
                     equation: id_eq(T, class(x), class(y))) ],
)
```

`Quot.lift f proof` reduces to the HIT recursor `T-rec` whose
data clause runs `f` on the underlying representative and whose
path clause discharges `proof` (the SMT obligation that `f`
respects `R`).  Quot.mk reduces to the data constructor `class`.
The three previous Quot axioms (Quot-form, Quot-mk, Quot-lift)
collapse into one HIT axiom; quotient round-trip and the
soundness of `Quot.lift` against the equivalence relation become
specific instances of the HIT recursor's path-clause discharge.

**Why HIT and not full HoTT.**  FX adopts HITs as a kernel
primitive but does not commit to full Cubical Type Theory
(Cohen-Coquand-Huber-Mörtberg TYPES 2015) — Cubical evaluation
roughly doubles kernel complexity and degrades SMT integration.
Modal univalence is restricted to the contract-boundary layer
(§14.2, Appendix H.7a) where the simpler equivalence transport
is sufficient for contract migration; the runtime-layer HIT
axiom suffices for quotient types and any other propositional-
equality-
witnessed quotient pattern.  Tan's no-Glue-path variant (MPRI M2
thesis 2025) is the operational model FX targets: cubical with
QITs and UIP, without the full Glue type machinery.

Note: the built-in `frac` types (§3.1) are the preferred way to
work with rationals.  Quotient types are the general mechanism;
`frac` is the specific optimized instance for rational arithmetic.

### 3.8 The Numeric Tower

**Fixed-width widening** (implicit, lossless):

```
Integers:
  u8 -> u16 -> u32 -> u64 -> u128 -> u256 -> u512 -> u1024 -> nat -> int
  i8 -> i16 -> i32 -> i64 -> i128 -> i256 -> i512 -> i1024 -> int
  uN -> iM   when M > N    (e.g., u32 -> i64)

Decimals:
  dec32 -> dec64 -> dec96 -> dec128 -> dec256 -> dec512 -> dec1024 -> decimal

Fractions:
  frac64 -> frac128 -> frac256 -> frac

Bit vectors:
  bits(n) -> bits(m)  when n <= m    (zero-extension)

Cross-family (lossless):
  iN -> frac(2*N)       integer to fraction (denominator = 1)
  fracN -> decimal       fraction to exact decimal (may need arbitrary precision)
```

Widening from any fixed-width type is explicit via `widen<T>(x)` at
every cross-width site.  FX performs no implicit numeric promotion.
Widening to an arbitrary-precision type (`int`, `nat`, `frac`,
`decimal`) is equally explicit and introduces heap allocation; the
compiler warns (N001) if the result is used in a context without
`with Alloc`.

There is no implicit coercion from decimal to float.  Going from
exact to approximate is a lossy operation and must be explicit:

```
let approx : f64 = to_float(exact_value);
```

**Narrowing** requires an explicit conversion that may fail.  The
enclosing function must declare `with Fail` to use narrowing
conversions:

```
fn convert(big: i64, wide: u32) : (u16, u8) with Fail(range_error)
begin fn
  let small : u16 = narrow(big);   // fail(OutOfRange) if big > 65535
  let tiny  : u8  = narrow(wide);  // fail(OutOfRange) if wide > 255
  return (small, tiny);
end fn;
```

**Cross-width arithmetic is explicit.**  FX performs no silent
promotion when two different fixed-width types appear in the same
arithmetic expression.  Every mixed-width site uses `widen<T>(x)`
(for provably lossless conversions) or `narrow<T>(x) with Fail(range_error)`
(for potentially lossy conversions):

```
let a : u8 = 200;
let b : u16 = 50000;
let c : u16 = widen<u16>(a) + b;          // explicit widening, u8 -> u16

let d : i32 = -100;
let b_as_i32 : i32 = widen<i32>(b);       // explicit widening, u16 -> i32
let e : i32 = b_as_i32 + d;

// Narrowing is explicit AND may fail:
let big : i64 = 200_000;
let small : u16 = narrow<u16>(big) with Fail(range_error);
```

`widen<T>(x)` is `@[copy]` and `Tot`; the compiler proves the
widening is lossless from the refinements on `T`.  Attempting
`widen<u8>(50000)` is a compile error.  Attempting to mix `u8` and
`u16` in a `+` without `widen` is error T043 (missing width marker).

### 3.9 The Never Type

`never` is the bottom type — no values, subtype of everything:

```
fn absurd<a: type>(x: never) : a = match x; end match;
```

It is the kernel empty inductive type (Ind with no constructors,
Appendix H.4).  `never` lives in `Std.Prelude` and is auto-imported.
Uses: divergent-function return type (`fn loop() : never with Div`),
exhaustiveness in irrefutable match, typing the else branch of
let-else (§4.6).

FX has no top type.  The three patterns that would reach for one
in other languages are each first-class constructs here:

 1. **Closed enums for tagged data.**  JSON, YAML, configuration
    files, message buses — the set of possible variants is fixed
    at compile time, so enumerate them:

    ```
    type JsonValue
      JNull;
      JBool(bool);
      JNumber(f64);
      JString(string);
      JArray(list(JsonValue));
      JObject(map(string, JsonValue));
    end type;
    ```

    Pattern match dispatches; the compiler checks exhaustiveness.

 2. **Contract decode at boundaries.**  When data crosses a
    boundary (network, disk, FFI), §14 contracts produce a
    concrete typed value with validators:
    `UserApi.decode(json, raw) : result(user, api_error)`.

 3. **Explicit existentials for opaque types with behavior.**
    When open-world polymorphism is required (plugin
    architectures, heterogeneous collections with shared methods),
    write the existential record directly (see §16.5):

    ```
    type Drawable = exists (T: type), {
      val: own T;
      draw: fn(ref T, ref Canvas) -> unit with UI;
    };
    ```

    The record's shape is the dispatch surface; no compiler-
    generated metadata.

Each pattern preserves §1.5 compile-time erasure — no runtime
type descriptor is carried.  Runtime polymorphism uses the
existential form of §16.5 exclusively; see that section for the
construction and elimination rules.

### 3.10 String Semantics

Strings are UTF-8 encoded and grapheme-clustered by default.
Three measurement units are available:

```
type string = string(Grapheme);       // default

fn length(s: string(Grapheme)) : nat;    // "cafe\u0301" -> 4
fn length(s: string(Codepoint)) : nat;   // "cafe\u0301" -> 5
fn length(s: string(Byte)) : nat;        // UTF-8 byte count
```

Conversion between units is explicit:

```
fn as_codepoints(s: string(Grapheme)) : string(Codepoint);
fn as_bytes(s: string(Codepoint)) : string(Byte);
```

Comparison on `string(Grapheme)` is NFC-normalized:
`"e\u0301" == "\u00E9"` is true.

**Composition.**  String operations are methods, not operators —
FX forbids operator overloading (§16.8).  Concatenation is
`s.concat(t)`; a list joins via `ss.join(sep)`.  Interpolation is
the canonical builder pattern: `f"Error {code}: {message}"` composes
arbitrary expressions into a single string.  No `+`, `++`, or `<>`
operator is defined for strings.  The full method inventory (concat,
split, replace, case conversion, substring, find, ...) ships in
stdlib §26.2 Text.

Floating-point types (`f32`, `f64`) are opt-in.  The default
fractional type is `decimal` (exact).  Use floats only when
IEEE 754 hardware acceleration is needed (graphics, physics
simulation, neural network inference) and rounding is acceptable.

Floating-point behavior beyond the default strict semantics is
controlled per-function:

```
with NaN(propagate)           NaN in any input -> NaN output
with Denormals(flush_to_zero) denormals become 0.0
with Rounding(toward_zero)    truncate instead of round
with FMA                      fused multiply-add (one rounding)
```

The default is strict IEEE 754: no NaN propagation (refinements
prevent NaN creation), denormals preserved, round-to-nearest-even,
separate mul and add.

### 3.12 Sort Stability and Collection Order

The default sort is stable (equal elements preserve input order).
Opt-in unstable sort allows faster algorithms:

```
fn sort<a: type>(xs: list(a)) : list(a) where Ord(a);           // stable
fn fast_sort<a: type>(xs: list(a)) : list(a) where Ord(a)
  with Unstable;                                            // unstable
```

Hash maps default to unordered iteration.  The compiler rejects
code that depends on iteration order for an unordered map:

```
type hash_map(k, v) = hash_map(k, v, order: Unordered);   // default
type ordered_map(k, v) = hash_map(k, v, order: Insertion); // ordered
type sorted_map(k, v) = hash_map(k, v, order: Sorted)
  where Ord(k);
```

### 3.13 Higher-Kinded Types

Type constructors have kinds.  `list` has kind `Type -> Type`.
Kind annotations are written on type parameters:

```
class Functor<f: Type -> Type>
  fn fmap<a: type, b: type>(g: a -> b, x: f(a)) : f(b);
end class;

class Monad<m: Type -> Type>
  fn pure<a: type>(x: a) : m(a);
  fn bind<a: type, b: type>(x: m(a), f: a -> m(b)) : m(b);
end class;
```

Every type parameter declares its kind explicitly.  FX does not
infer kinds from usage.  Omitting a kind is a compile error T044
(missing kind annotation).

**Applying higher-kinded types.**  A type of kind `Type -> Type`
is applied via the same parenthesized syntax as value-level
function application: `f(a)` where `f` has kind `Type -> Type`
and `a` has kind `Type` produces a type of kind `Type`.  Inside
the Functor class body, `f(a)` and `f(b)` are both well-formed
because `f` is a unary type constructor.

**No type-level lambdas.**  FX does not support type-level
lambdas (`\a => f(a, int)` as a partial type-constructor
application).  When a partial application is needed, introduce a
named type alias:

```
type pair_with_int<a: type> = pair(a, int);
// use pair_with_int as a Type -> Type constructor
```

**No associated types.**  Class type parameters carry the
necessary type information directly:

```
class Collection<c: Type -> Type, elem: type>
  fn empty() : c(elem);
  fn insert(x: elem, col: c(elem)) : c(elem);
end class;

// instead of Rust's trait Collection { type Item; fn insert(&mut self, x: Self::Item); }
```

This means type-class constraints often carry more parameters
than Rust/Haskell, but the explicit form is unambiguous and fits
the rigor-first principle (§1.1, Appendix E).

**No kind polymorphism beyond the binder.**  `<k: kind>` is not
a valid syntax — kinds are fixed at declaration.  If you need a
function that works over both `Type` and `Type -> Type`, split
into two declarations.  This mirrors Idris 2's pragmatic choice
and avoids the impredicativity issues PolyKinds introduces in
GHC.


## 4. Expressions

### 4.1 Function Application

All function calls use parentheses.  Juxtaposition application does
not exist.

Functions with one parameter use positional syntax:

```
let y = f(x);
let doubled = double(5);
```

Functions with more than one parameter require named arguments at
the call site.  Every argument is written as `name: value`:

```
let z = connect(host: "localhost", port: 8080);
let w = send(data: payload, over: conn);
```

This is mandatory, not optional.  There is no positional syntax for
multi-argument calls.  Call sites are self-documenting — you always
know what each argument means.

Arguments are evaluated left-to-right, always.  There is no
platform-dependent evaluation order.

**Default parameter values.**  A function parameter may declare a
default:

```
fn connect(host: string, port: nat = 443, timeout: nat = 30) : connection
  with IO, Fail(connect_error)
= ... ;

// Call sites may omit parameters with defaults:
connect(host: "localhost");                    // port=443, timeout=30
connect(host: "a", timeout: 5);                 // port=443
connect(host: "a", port: 8080, timeout: 5);    // all explicit
```

Defaults are evaluated **at the call site** in the caller's
context, not at the definition site.  A later parameter's default
may reference earlier parameters:

```
fn batch(size: nat, chunks: nat = size * 4) : queue(nat) = ... ;
batch(size: 10);                               // chunks = 40
batch(size: 10, chunks: 32);                   // explicit override
```

The default expression must type-check with only prior parameters
in scope; referencing a later parameter is compile error R002.
Defaults compose with named-argument syntax — the order of
evaluation is left-to-right by declaration order regardless of
argument syntax at the call site.

Implicit type arguments are passed with `#`:

```
None(#i64)                   // explicit type argument
identity(#string, value: "hello")  // explicit type + named arg
```

**Implicit argument resolution** is unification-only.  The
compiler fills each `#param` from the unification of the explicit
arguments' types against the parameter types.  When unification
cannot uniquely determine an implicit, it is compile error T047
(`ambiguous implicit type argument`) with a suggestion to pass
it explicitly.  FX has no type-class search a la Haskell, no
canonical structures a la Coq, no implicit conversions a la
Scala — implicits are purely for elision of redundant type
arguments, never for value-level lookup.  Deciding whether a
trait instance is in scope uses the §16.3 specificity lattice,
which is decidable and never backtracks.

```
fn empty<a: type>() : list(a) = [];
let xs = empty();                // T047: cannot infer a
let xs = empty(#i64);            // ok
let xs : list(i64) = empty();    // ok: a inferred from let-binding type
```

### 4.2 Pipes and Dot-Shorthand

The pipe operator passes a value through a chain of functions:

```
let result = items
  |> filter(.active and .age >= 18)
  |> map(.name)
  |> sort_by(.name)
  |> take(100);
```

A bare dot without a left operand in function-argument position
is shorthand for a one-parameter lambda whose body is the dot
expression applied to the parameter.  Both field access
(`.field`) and method call (`.method(args)`) are covered.  Multiple
dots in the same expression all refer to the same implicit
element:

```
.active                 desugars to   fn(it) => it.active
.age >= 18              desugars to   fn(it) => it.age >= 18
.active and .age >= 18   desugars to   fn(it) => it.active and it.age >= 18
.nested.field           desugars to   fn(it) => it.nested.field
.to_string()            desugars to   fn(it) => it.to_string()
.split(",")             desugars to   fn(it) => it.split(",")
.name.length()          desugars to   fn(it) => it.name.length()
```

The shorthand is valid in any function-argument position, not only
after `|>`:

```
filter(.active, users)                        // field
sort_by(.name, users)                         // field
find(.id == target, users)                    // comparison on field
items |> map(.to_string())                     // method
users |> filter(.email.ends_with("@acme"))    // method on field
```

When the shorthand does not fit — complex logic, multiple parameters,
no field access — use an explicit lambda:

```
pairs |> map(fn((a, b)) => a + b)
numbers |> map(fn(x) => x * x + 1)
```

### 4.3 Pattern Matching

The `match` expression dispatches on the structure of a value.  A
semicolon follows the scrutinee expression (rule 1):

```
fn describe(x: i32) : string
= match x;
    0 => "zero";
    1 => "one";
    n => f"number {n}";
  end match;
```

Patterns include: literals, constructors, wildcards (`_`), variable
bindings, tuple patterns, record patterns, spread patterns (`[h, ...t]`),
and `as` bindings.

```
match shape;
  Circle { radius: r } => 3.14159 * r * r;
  Rect { w, h } => w * h;
end match
```

Guards refine pattern arms:

```
match x;
  n if n > 0 => "positive";
  n if n < 0 => "negative";
  _ => "zero";
end match
```

The compiler checks exhaustiveness from the type's constructors
and the refinements in scope.

Matching on a linear value consumes it.  The bound variables in the
matched arm receive ownership of the corresponding parts (§7.5).

### 4.4 Conditionals

A semicolon follows the condition (rule 1):

```
if length(xs) > 0;
  head(xs)
else
  default_value
end if
```

Multi-branch:

```
if x > 0;
  "positive"
else if x < 0;
  "negative"
else
  "zero"
end if
```

When `if` is a tail expression of a block, it has no trailing `;`.
When it appears as a statement, it ends with `;`:

```
fn example() : unit
begin fn
  let label = if cond; "yes" else "no" end if;  // statement, ;
  print(label)                                    // tail, no ;
end fn;
```

**If-let destructuring.**  Every `if` condition may be replaced by
a `let pattern = expr` form.  The body runs iff the pattern
matches; pattern-bound names are in scope for that body only:

```
if let Some(v) = lookup(key);
  use(v)
else
  default_value
end if
```

Multiple branches can chain `else if let`:

```
if let Ok(data) = parse(raw);
  process(data)
else if let Err(NotFound) = parse(raw);
  fetch_remote(key)
else
  fail(Unrecognized)
end if
```

Kernel translation: desugars to a single-arm `match` with a
wildcard fall-through to the else branch (§4.3).  No new typing
rule; same rules as `match`.

### 4.5 Loops

For-loops iterate over a range or collection:

```
for i in 0..10;
  process(i);
end for;

for item in items;
  consume(item);
end for;

for (i, item) in items.enumerate();
  print(f"{i}: {item}");
end for;
```

While-loops:

```
while condition;
  step();
end while;
```

`break` exits the nearest enclosing loop.  `continue` skips to the
next iteration.  Both are statements terminated with `;`.

Range syntax:

```
0..10          // exclusive: 0, 1, ..., 9
0..=10         // inclusive: 0, 1, ..., 10
0..100 by 5    // stepped: 0, 5, 10, ..., 95
100..0 by -1   // reverse stepped: 100, 99, ..., 1
```

Range expressions are `range<T>` values where `T` is the element
type; any type implementing `Step` (stdlib trait — next/prev
operations) can be iterated.  `by` is a binary keyword binding
tighter than comparison and looser than additive operators; the
RHS is a step expression of type `T` (non-zero).

For-loop binders accept any irrefutable pattern — destructuring
tuples, records, and constructor fields with single arms is
supported:

```
for (k, v) in map.entries();
  print(f"{k} = {v}");
end for;

for User { name, age, .. } in users;
  print(f"{name} ({age})");
end for;
```

Refutable patterns (e.g., matching only a specific constructor
variant) are a compile error; use `match` inside the loop body or
`.filter` upstream.  Kernel translation: `for pattern in e; body
end for` desugars to `for __it in e; let pattern = __it; body end
for`, and then the inner `for` desugars to recursion / fold per
§6.9 kernel translation.

### 4.6 Let Bindings

`let` introduces a binding.  The binding is immutable by default.
Every let-binding carries its type — EITHER as an explicit ascription
on the binding OR from a synthesis-mode RHS that fully determines the
type without consulting any surrounding expectation:

```
let x : int = 42;                     // ascription on the binding
let y = 42i64;                         // synth — suffix gives the type
let z = widen<u64>(x);                 // synth — explicit type argument
let r = R(insn);                       // synth — layout constructor
let sorted = sort<i64>(data);          // synth — type args on the call
let (p : i64, q : i64) = split(items);
let config { host : string, port : nat, .. } = load_config();
```

**Synthesis-mode RHS** (type determined from the expression itself):
- literal with explicit suffix: `42u8`, `3.14f64`, `42i64`
- function call with all type arguments explicit: `f<T>(...)` or
  when `f`'s return type is concrete (`fn f() : string = ...`)
- named conversion constructor: `widen<T>(x)`, `narrow<T>(x)`,
  `R(bits)`, `cell(init)`
- field access on a typed binding: `x.field` when `x`'s type is known
- method call where the method's return type is concrete
- record construction with explicit constructor: `config { ... }`
- spread copy: `{ ...base }` takes `base`'s type

**Checking-mode RHS** (needs an expected type, MUST be ascribed on
the binding) — compile error T045 otherwise:
- unsuffixed numeric literal: `42` (defaults to `int`, N001 warning)
- empty collection: `[]`, `{}`
- constructor with no arguments: `None`
- polymorphic function call without explicit type args where the
  result would be ambiguous: `fn empty<a: type>() : list(a) = []`
  called as `empty()` (compile error T045 unless ascribed)

The rule is single-pass bidirectional: the checker either synthesizes
the RHS type directly (no binding ascription needed) or checks the
RHS against the binding's declared type.  This matches rigor-first —
the annotation is always explicit SOMEWHERE in the source, but doesn't
need to be duplicated on both the binding and the RHS.

Mutable heap cells use `cell`:

```
let counter : cell(int) = cell(0);
counter.set(counter.get() + 1);
```

`cell(initial)` allocates a mutable heap cell holding `initial`.
`x.get()` reads, `x.set(value)` writes — both are method calls on
`cell`, no special operators.  `cell` is linearly owned by its
binding; passing `cell(int)` to a function transfers ownership
unless the parameter is declared `ref cell(int)` (shared borrow) or
`ref mut cell(int)` (exclusive borrow).  The `ref` keyword is
purely a borrow-mode declarator (§7); it never constructs a cell.

Omitting the binding ascription on a checking-mode RHS is compile
error T045 (`let-binding type cannot be inferred`) — the diagnostic
names the RHS's checking-mode source (empty collection, unsuffixed
literal, polymorphic call) and suggests the explicit form.  The
rigor-first principle (§1.1, Appendix E) requires type information
to be explicit somewhere; synthesis-mode RHS already satisfies that
obligation, so the binding ascription is optional in that case.
No silent defaulting: an unsuffixed `42` in a checking-mode position
with no ascribed expected type is T045, not a silent fallback to
`int`.

**Discarding a value.**  The wildcard pattern `_` on the binding
position discards the value:

```
let _ = expensive_computation();       // discard result
let _ : SideEffect = build_index();     // discard, type-check only
```

This is just the standard pattern-let rule applied with a
wildcard pattern — `_` matches any value and binds nothing.  For
linear values the discard is a `drop` (see §7.1); for classified
+ linear it includes the automatic `secure_zero` (§12.7).

**Let-else.**  When the pattern is refutable (constructor match,
guard) and the else branch must diverge on mismatch:

```
fn process(opt: option(user)) : user_id with Fail(NotFound)
begin fn
  let Some(user) = opt else fail(NotFound);
  // user is in scope here as a bound user value
  return user.id;
end fn;
```

Kernel translation: `let pattern = expr else stmt;` desugars to a
two-arm match:

```
match expr;
  pattern => <continuation of this block>;
  _       => stmt                          // must have type 'never'
end match
```

The else statement's type must be `never` — it must diverge via
`fail`, `return`, `break`, `continue`, or a call with `: never`
return type.  Falling through the else branch is a compile error
T055 (`let-else branch must diverge; found type T`).  Ties into
the control-flow-effects discipline of §4.9: `fail` inside the
else adds `Fail(E)` to the enclosing function's effect row.

### 4.7 Blocks and Return

A `begin fn ... end fn` block groups statements.  Every statement
ends with `;`.  The `return` keyword marks the value produced by
the function.  There is no implicit tail expression — `return` is
always required in block-form functions:

```
fn process(x: i64) : i64
begin fn
  let a = x + 1;
  let b = a * 2;
  return b + 3;
end fn;
```

One-liner functions use `= expr;` and do not need `return`:

```
fn double(x: i64) : i64 = x * 2;
```

There is no early `return`.  Every block-form function has exactly
one `return` as its last statement before `end fn`.  Guard logic
uses `if`/`else` expressions or error effects (§9), not early
exit.  This guarantees one entry point and one exit point per
function, simplifying verification — the postcondition is checked
at exactly one location.

Local function declarations are permitted inside blocks:

```
fn outer(data: list(i64)) : list(i64)
begin fn
  fn double(x: i64) : i64 = x * 2;

  fn rec sum_positive(xs: list(i64), acc: i64) : i64
    decreases xs;
  = match xs;
      [] => acc;
      [h, ...t] => sum_positive(t, if h > 0; acc + h else acc end if);
    end match;

  let total = sum_positive(data, 0);
  return map(double, data);
end fn;
```

Local `fn` is `Tot` by default and does not inherit the enclosing
function's effects (rule 18).

### 4.8 Comprehensions

List comprehensions desugar to `filter` and `map`:

```
let squares = [x * x for x in 0..10];
let names = [u.name for u in users if u.active];
let pairs = [(x, y) for x in 0..5 for y in 0..5 if x != y];
```

Multiple `for` clauses are nested (outer-first).  Multiple `if`
clauses are conjunctive — a row passes only if every filter
holds.  The comprehension's grammar is given in fx_grammar.md
§6.4.

**FX has no dedicated database-query syntax.**  Multi-source
queries (LINQ-style `from u in users join p in posts on ...
where ... select ...`) are expressed as pipe chains over the
`Query` source type (§11.12):

```
let top_customers = db.table("sales")
  |> filter(.region == "EU" and .amount > 1000)
  |> group_by(.customer_id)
  |> map(fn((id, rows)) => (id, rows |> sum(.amount)))
  |> sort_by(.1)
  |> reverse()
  |> take(100);
```

The `Query(T)` source type defers execution until
`execute()`; the pipeline is a lazy plan the optimizer may
rewrite before execution (predicate pushdown, projection
pushdown, join reordering — §11.12).  No new syntax was added
because comprehensions and pipe chains cover the same semantic
space as LINQ without the language-level ceremony.

### 4.9 Error Handling

Errors are an effect.  `Fail` is a built-in effect provided by the
kernel (Appendix H.5 coinductive family — the Fail effect is
`effect Fail<E> { fn fail<A>(e: E) : A; }`).  A function that can
fail declares `with Fail(E)` in its effect row where `E` is the
error type.  The `fail(e)` operation aborts to the nearest handler
for the Fail effect (either a `try ... catch` block in the caller
or a top-level handler installed by the runtime).

`fail` is NOT a keyword — it is an operation name exported from
the kernel-provided Fail effect.  Users who shadow it locally
would need backtick-escaping to refer to the operation; normal
code always has `fail` in scope as part of the prelude.

**Typing rule for `fail`.**

```
fn fail<A: type, E: type>(e: E) : A with Fail(E)
```

The return type is universally quantified — `fail(e)` has type
`A` for whichever `A` the call site expects.  This matches the
operational semantics: `fail` never returns to the caller, so any
continuation type is satisfiable.

**Propagation is explicit** — every call to a function whose
effect row contains `Fail(E)` or `Exn(E)` requires either a `try`
prefix (to propagate) or a surrounding `try ... catch ... end try;`
block (to handle).  Calling such a function without either marker
is compile error E042 (missing control-flow marker).

**Kernel translation.**  `fail(e)` desugars to
`perform Fail.fail(e)` at the kernel level — a standard algebraic
effect operation.  `try expr` desugars to `perform Fail.propagate(
expr)` which the kernel handles as a monadic bind over the Fail
row.  `try ... catch ... end try` desugars to `handle { body }
with Fail { fail(e, k) => catch_body(e); return(v) => v }`.
Effect handlers (§9.6) are the general mechanism; `fail`/`try`/
`catch` are the surface syntax.

This is the rigor-first rule (§1.1, Appendix E) applied to
control-flow effects.  It splits effects into two classes:

 * **Control-flow effects** change where execution continues:
   `Fail`, `Exn`, `Yield` (in generators).  These require call-site
   markers so abort points are visible.
 * **Enabling effects** do not transfer control to a new point:
   `IO`, `Alloc`, `Read`, `Write`, `Async`, `Div`, `Ghost`.  These
   declare capabilities in the effect row and require no call-site
   marker.  (`await(e)` on an `Async` operation is already an
   explicit marker.)

```
fn fetch(id: i64) : raw_data with Fail(fetch_error), IO
begin fn
  let response : http_response = http_get(f"/api/{id}");
  if response.status != 200;
    fail(HttpError(response.status));
  end if;
  return response.body;
end fn;

fn parse(raw: raw_data) : parsed with Fail(parse_error)
begin fn
  let tokens : list(token) = tokenize(raw);
  if tokens is Empty;
    fail(EmptyInput);
  end if;
  return build_ast(tokens);
end fn;

fn fetch_and_parse(id: i64) : parsed with Fail(error), IO
begin fn
  let raw : raw_data = try fetch(id);       // explicit propagation
  let parsed : parsed = try parse(raw);     // explicit propagation
  return parsed;
end fn;
```

`try` has two forms:

 * **Prefix form**: `try expr` re-raises any `Fail`/`Exn` from `expr`
   into the enclosing function's effect row.  Usable anywhere an
   expression is expected.
 * **Block form**: `try stmts; ... catch arms end try;` handles the
   error at a boundary, removing the effect from the row below the
   block.

At the boundary where errors are handled, use the block form:

```
fn main() : unit with IO
begin fn
  try
    let data = fetch_and_parse(42);
    display(data);
  catch
    HttpError(code) => log(f"HTTP {code}");
    EmptyInput => log("empty response");
  end try;
end fn;
```

Error types are closed unions.  Every failure mode is named.  There
is no catch-all `error` type.  When composing errors from different
modules, declare a combined error type:

```
type my_error
  Fetch(fetch_error);
  Parse(parse_error);
end type;
```

The `Fail` effect tracks error types precisely.  A function with
`with Fail(parse_error)` can only produce parse errors.  A function
with `with Fail(my_error)` can produce any variant of `my_error`.
The compiler verifies that every `fail(e)` produces a value of the
declared error type.

**One `Fail` per signature.**  An effect row containing two or more
`Fail` effects — `with Fail(E1), Fail(E2)` — is compile error E045
(`redundant Fail effects; combine into a single Fail with a union
error type`).  The effect lattice (§9.3) normalizes them
internally to `Fail(E1 | E2)` when composing effects from multiple
call sites, but the surface annotation must carry a single
`Fail(T)` with `T` a named closed-union type.  This keeps signatures
and catch arms unambiguous — a caller sees one failure dimension,
one error type, one set of variants to dispatch on.

**Fail versus Exn.**  `Fail(E)` and `Exn` are both control-flow
effects (§4.9 classification) but serve different purposes.  Fail
is for typed, expected error paths — the error type E is part of
the function's API and the caller handles or propagates explicit
variants.  Exn is for untyped, abort-style runtime conditions that
have no typed error value: division by zero, assertion failure,
stack overflow, out-of-memory.  A function declaring `with Exn`
may panic to the top-level runtime, which runs the error formatter
service (§21.4) and terminates the thread.  Exn is not recovery-
oriented; a `try ... catch` block with an `Exn` pattern catches
the panic, but the conventional use of Exn is to propagate to
process termination rather than handle locally.  Releasable
libraries declare Fail for everything they expect to go wrong and
Exn only for conditions that represent a genuine program bug or
resource exhaustion.

### 4.10 Dot Syntax for Methods

`x.method(args)` is sugar for `Type.method(x, args)` where the
mode of `x` is determined by the method's `self` parameter:

```
conn.is_open()            // Connection.is_open(ref conn)
conn.set_timeout(5000)    // Connection.set_timeout(ref mut conn, 5000)
conn.close()              // Connection.close(own conn)
```

The resolution rules for dot syntax are defined in §16.3.

### 4.11 Control Flow as Effects

All control flow in FX derives from delimited continuations.  This
is not user-visible syntax — it is the semantic foundation:

```
return      abort to function boundary
break       abort to loop boundary
throw       abort to try/catch boundary
yield       suspend to handler
await       suspend to async scheduler
```

This means `return` inside a nested `if` works the same way
`throw` works inside a `try` — both are abort to a specific
delimiter.  The effect system tracks which delimiters are in scope.

### 4.12 Grammar Summary

Core expression grammar (simplified):

```
expr
  = expr PIPE_RIGHT expr                      // a |> f
  | FN LPAREN params RPAREN FAT_ARROW expr    // fn(x) => body
  | MATCH expr SEMI arms END MATCH            // match e; ... end match
  | IF expr SEMI expr ELSE expr END IF         // if c; t else f end if
  | FOR pat IN expr SEMI stmts END FOR         // for x in xs; ... end for
  | WHILE expr SEMI stmts END WHILE            // while c; ... end while
  | BEGIN stmts END                             // begin ... end
  | expr LPAREN args RPAREN                    // f(a, b)
  | expr DOT IDENT                              // x.field
  | expr DOT IDENT LPAREN args RPAREN          // x.method(args)
  | expr binop expr                             // a + b
  | PREFIX expr                                 // not x, ~x
  | LET pat EQ expr SEMI                        // let x = e;
  | expr DOT GET LPAREN RPAREN                 // x.get()
  | expr DOT SET LPAREN expr RPAREN             // x.set(v)
  | atom
  ;

atom
  = IDENT | UIDENT | literal | LPAREN expr RPAREN
  | LBRACKET exprs RBRACKET                    // [1, 2, 3]
  | LBRACKET expr FOR ... RBRACKET             // [x*x for x in 0..10]
  | HASH atom                                   // #a (implicit arg)
  | DOT IDENT                                   // .field (shorthand)
  ;

decl
  = PUB? FN REC? IDENT type_params? LPAREN params RPAREN
      COLON type effect_annot? spec_clauses? body SEMI
  | PUB? TYPE IDENT type_params? EQ type SEMI
  | PUB? TYPE IDENT type_params? LBRACE fields RBRACE SEMI
  | PUB? VAL IDENT COLON type SEMI
  | EFFECT UIDENT type_params? ops END EFFECT SEMI
  | MACHINE UIDENT machine_body END MACHINE SEMI
  | CONTRACT UIDENT FOR type contract_body END CONTRACT SEMI
  | IMPL type impl_body END IMPL SEMI
  | CLASS UIDENT type_params? class_body END CLASS SEMI
  | INSTANCE UIDENT FOR type instance_body END INSTANCE SEMI
  | MODULE IDENT SEMI
  | OPEN qualified_name SEMI
  | INCLUDE qualified_name SEMI
  ;

effect_annot
  = WITH effect_row
  ;

effect_row
  = UIDENT                                     // IO
  | IDENT                                       // eff (variable)
  | effect_row COMMA effect_row                 // IO, Async
  ;

spec_clauses
  = WHERE constraints SEMI
  | PRE expr SEMI
  | POST IDENT FAT_ARROW expr SEMI
  | DECREASES expr SEMI
  ;

body
  = EQ expr SEMI                                // = expr;
  | BEGIN FN stmts RETURN expr SEMI END FN SEMI    // begin fn ... return e; end fn;
  ;
```


## 5. Declarations and Modules

### 5.1 Function Declarations

A function has a name, optional type parameters, parameters,
return type, optional effect annotation, optional specification
clauses, and a body.

One-liner form:

```
fn add(a: i64, b: i64) : i64 = a + b;
```

Block form (every statement ends with `;`, `return` is required):

```
fn process(items: list(item)) : list(result) with IO
begin fn
  let transformed = map(transform, items);
  return filter(.valid, transformed);
end fn;
```

Type parameters are introduced with angle brackets at the
definition site (rule 2):

```
fn map<a: type, b: type>(f: a -> b, xs: list(a)) : list(b)
  decreases xs;
= match xs;
    [] => [];
    [h, ...t] => [f(h), ...map(f, t)];
  end match;
```

Effect annotations follow the return type with `with`:

```
fn read_file(path: string) : string with IO;
fn send(msg: packet) : unit with IO, Async;
fn loop() : never with Div;
```

No effect annotation means `Tot` — pure and terminating.

Specification clauses appear between the signature and the body:

```
fn sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);
  pre length(xs) > 0;
  post r => is_sorted(r);
  post r => is_permutation(xs, r);
  decreases length(xs);
begin fn
  ...
  return result;
end fn;
```

`where` introduces type class constraints.  `pre` states
preconditions on inputs.  `post r =>` states postconditions —
the identifier after `post` binds the return value (no magic
`result` name; the programmer chooses the binding).  Multiple
`post` clauses are verified independently.  `decreases` provides
the termination measure for recursive functions.

Clause ordering in a function signature:

```
fn name<type_params>(params) : return_type with effects
  where type_class_constraints;
  pre preconditions;
  post r => postconditions;
  decreases measure;
= body
proof
  proof_stmts
end proof;
```

All clauses and the `proof` block are optional.  When present,
they appear in this fixed order.  Misordering is a compile
error.  `with` attaches to the return type on the same line.
All other clauses are on subsequent lines, each terminated with
`;`.  The `proof` block (§10.17) attaches after the body and
discharges the function's `post` obligations from a ghost
context; its stmts run at elaboration, erased at codegen.

### 5.2 Recursive Functions

The `rec` modifier permits self-reference.  Every `rec` function
must have a `decreases` clause or declare `with Div`:

```
fn rec length<a: type>(xs: list(a)) : nat
  decreases xs;
= match xs;
    [] => 0;
    [_, ...t] => 1 + length(t);
  end match;
```

Mutual recursion uses `and`:

```
fn rec is_even(n: nat) : bool
  decreases n;
= n == 0 or is_odd(n - 1)
end fn
and is_odd(n: nat) : bool
  decreases n;
= n != 0 and is_even(n - 1)
end fn;
```

`pub` on the first function applies to all `and` clauses.  The
final `;` follows the last `end fn`.

### 5.3 Lambdas

Anonymous functions use `fn(params) => body`:

```
let double = fn(x: i64) => x * 2;
let add = fn(a: i64, b: i64) => a + b;
```

Destructuring in lambda parameters:

```
let get_name : (string, nat) -> string = fn((name: string, _age: nat)) => name;
let sum_pair : (i64, i64) -> i64       = fn((x: i64, y: i64)) => x + y;
```

Every lambda parameter carries its type.  FX does not infer lambda
parameter types from context.  Omitting a parameter type is compile
error T046 (missing lambda parameter type).  This follows the
rigor-first rule (§1.1, Appendix E).

### 5.4 Type Declarations

Simple alias:

```
type meters = f64;
type user_id = nat { x > 0 };
```

Variant type:

```
type option<a: type>
  None;
  Some(a);
end type;
```

Record type:

```
type connection {
  fd: i32;
  host: string;
  open: bool;
};
```

Variant with named-field payloads:

```
type expr
  Lit(value: int);
  Var(name: string);
  Add(left: expr, right: expr);
  Mul(left: expr, right: expr);
end type;
```

The `@[copy]` attribute marks a type as freely duplicable.  The
compiler verifies that all fields are also `@[copy]`:

```
@[copy]
type point { x: f64; y: f64 };
```

Types without `@[copy]` are linear by default — values must be
consumed exactly once.

### 5.5 Module System

Each `.fx` file defines one module.  The module name matches the
file path:

```
// Crypto/Aead.fx
module Crypto.Aead

open Std.Result;
open Std.Bytes;

pub fn encrypt(...) : ... with Crypto;
```

`pub` makes a declaration visible to importers.  Without `pub`,
declarations are module-private.

There are no global variables.  No top-level `let` bindings.
Module-scoped constants use `const`:

```
const MAX_RETRIES : u8 = 5;
const BUFFER_SIZE : u16 = 4096;
```

Constants are always compile-time evaluated.  A `const` may be
`pub` iff three conditions hold:

- The declared type is `@[copy]` (freely duplicable; no linear
  fields; no runtime-allocated components).
- The initializer expression is `comptime`-evaluable (no runtime
  computation).
- The initializer has effect `Tot` (no IO, no allocation, no
  divergence).

Under these conditions, `pub const NAME : T = expr;` is inlined
at each use site in consuming modules.  There is no shared
runtime memory location, no module-initialization ordering
dependency, and no hidden coupling between consumers.  Changing
the value is a contract diff (§14.10) and produces the computed
semver bump like any other public change.

```
pub const MAX_RETRIES : u8 = 5;          // ok: u8 is @[copy]
pub const PI : f64 = 3.14159265358979;   // ok: f64 is @[copy]
pub const GREETING : string = "Hello";   // ok: string is @[copy]
```

If any condition fails, `pub const` is rejected — the value is
runtime state disguised as a constant and must be exposed through
a `pub fn` with explicit effects:

```
// Rejected: buffer(u8) is not @[copy]; make_buffer is not Tot.
// pub const BUFFER : buffer(u8) = make_buffer(4096);

// Expose via a function so the Alloc effect is visible:
pub fn buffer() : buffer(u8) with Alloc = make_buffer(4096);
```

FX does not provide a `pub static` form (a shared runtime memory
location).  Runtime-shared state lives behind a function boundary
so its effects and allocation strategy are visible in the
signature.  The three conditions above make `pub const` exactly
the compile-time-inlined form; anything requiring runtime
presence goes through `pub fn`.

Functions are sealed — a function's behavior depends only on its
parameters and declared effects.  No ambient global state.

`open` brings a module's public declarations into scope.  `include`
re-exports them.

Scoped open limits the import to a block:

```
begin open Std.Math.Lemmas;
  lemma_div_mod(x, y);
end;
```

`val` provides a forward declaration when the body is not yet
available or in a separate module:

```
pub val sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);
```

`extern` declares functions implemented outside FX:

```
extern "C"
  fn malloc(size: nat) : own ptr(u8);
  fn free(own p: ptr(u8)) : unit;
end extern;
```

Module functors parameterize a module by another module:

```
module type Ordered
  type t;
  val compare : (t, t) -> ordering;
end module type;

module functor MakeSet(Elem: Ordered)
  type set = list(Elem.t);
  fn empty() : set = [];
  fn insert(x: Elem.t, s: set) : set;
end module functor;

module IntSet = MakeSet(struct
  type t = i64;
  let compare = i64_compare;
end struct);
```


## 6. The Graded Type System

FX's type system is a graded type theory built on the corrected
Atkey-Wood-McBride graded calculus (Atkey LICS 2018, Wood-Atkey
2022 Lam rule).  Twenty-two graded dimensions are instances of
one parameterized checking algorithm.  Each dimension provides a
graded algebraic structure (semiring, lattice, typestate,
foundational, or versioned — see §6.3) and the compiler runs the
same rules on all of them simultaneously.  The kernel
formalisation lives in `fx_modecat.md` as a multimodal type
theory instance (Gratzer-Kavvos-Nuyts-Birkedal LICS 2020;
canonicity proved by Gratzer LICS 2022); §6.0 below names the
four value categories the kernel partitions over and the rest of
the chapter focuses on the surface dimensions and how they
compose.  Collisions between dimensions appear as the §6.8
collision catalog — a finite list of compositions the kernel
rejects.

### 6.0 Value Categories

FX values live in one of four categories that determine which
dimensions apply, what's erased at codegen, and what the
elaborator may serialize across boundaries.  These categories
are NOT named programmer-facing modes — they're kernel-internal
distinctions exposed via existing surface constructs:

  * **Erased / proof-only**: bindings introduced with the `ghost`
    keyword (§7.1), proof-block content (§5.4 `proof_block`),
    refinement predicates, and specification clauses.  Erased at
    codegen per §1.5.  All twenty-two dimensions admit a
    grade-zero erased view via the 2LTT static-layer separation
    (§6.5, §30.12).
  * **Runtime-executing**: ordinary FX code — every `fn`, `let`,
    `match`, `if`, every type and value the programmer writes
    without a special declaration prefix.  This is the default
    and carries the full grade vector across all twenty-two
    dimensions.
  * **Synthesizable hardware**: bodies of `hardware fn` and
    `hardware module` declarations (§18.9–§18.11).  A restricted
    grade subset applies (clock, representation, precision,
    complexity); other dimensions (effects, allocation, async,
    arbitrary-precision arithmetic) are rejected at the
    `hardware` boundary by §18.8.
  * **Serialized boundaries**: payloads governed by `contract`
    declarations (§14) at network / DB / IPC interfaces.
    Two extra dimensions apply (format binding, version
    migration); the runtime grade is the post-decode view per
    §14.5.

The kernel formalises these four categories as the modes of an
MTT instance with cross-category morphisms (`ghost`/`erase` for
the proof boundary, `synth`/`observe` for the hardware boundary,
`serialize`/`parse` for the contract boundary).  The full
categorical apparatus, including the 2-cells encoding
subsumption rules and the absent 2-cells encoding §6.8 collisions,
is the subject of `fx_modecat.md` and Appendix H.7–H.7b; this
chapter and the rest of the spec do not name the categories
again, treating them as the implicit context of the surrounding
construct.

### 6.1 Resource Semirings

A resource semiring is a tuple `(R, +, *, 0, 1, <=)` where:

- `(R, +, 0)` is a commutative monoid (parallel use of a resource)
- `(R, *, 1)` is a monoid (sequential use)
- `*` distributes over `+`
- `0 * r = r * 0 = 0` (annihilation)
- `<=` is a preorder compatible with `+` and `*`

Each of the twenty-two dimensions instantiates a graded
algebraic structure along these lines (semiring for Tier S;
lattice for Tier L; typestate for Tier T; elaboration-discharged
for Tier F; lattice-with-adapter for Tier V — see §6.3).  The
product of all structures forms the grade vector that every
binding carries.

The usage semiring (dimension 3) is the central example:

```
+ |  0    1    w          * |  0    1    w
--+-----------            --+-----------
0 |  0    1    w          0 |  0    0    0
1 |  1    w    w          1 |  0    1    w
w |  w    w    w          w |  0    w    w
```

Grade `0` means absent (erased, ghost).  Grade `1` means linear
(used exactly once).  Grade `w` means unrestricted (used any number
of times).  The `+` operation models parallel use: using a linear
variable in both branches of an `if` yields `1 + 1 = w`, which is
a type error for a linear binding.

The security semiring (dimension 5):

```
+ |  unclassified    classified
--+----------------------------
u |  unclassified    classified
c |  classified      classified
```

Combining public and secret data yields secret data.  There is no
implicit downgrade path from classified to unclassified.

### 6.2 Typing Rules

The core judgment is `G |- e : A` with grade vector `p` tracking
resource usage across all dimensions.

**Variable.**  Using a variable costs 1 at that variable's position
and 0 everywhere else.

```
G, x :_r A |- x : A     grade: 0 everywhere, r at x
```

**Application.**  The cost of applying a function is the cost of
evaluating the function plus the argument's cost scaled by the
function's parameter grade.

```
G |-_p1 f : (x :_r A) -> B     G |-_p2 a : A
----------------------------------------------
G |-_(p1 + r * p2) f(a) : B[a/x]
```

**Let.**  The cost of a let-binding is the body's usage of the
bound variable times the cost of the bound expression, plus the
cost of the body.

```
G |-_p1 e : A     G, x :_r A |-_p2 body : B
---------------------------------------------
G |-_(r * p1 + p2) let x = e; body : B
```

**If.**  The condition's cost is added to the join of the two
branches.  The join is the worst case — a linear variable used in
both branches becomes unrestricted, which is a type error.

```
G |-_p0 cond : bool     G |-_p1 then : B     G |-_p2 else : B
---------------------------------------------------------------
G |-_(p0 + p1 \/ p2) if cond; then else end if : B
```

**Lambda (the corrected rule).**  FX uses the Wood/Atkey 2022
formulation with context division, not the broken Atkey 2018 rule:

```
G/p, x :_r A |-_1 b : B
------------------------
G |-_p fn(x) => b : (x :_r A) -> B
```

`G/p` denotes context division: each binding's grade is divided by
`p`, where `pi/p = max { d : d * p <= pi }`.  For the usage
semiring: `1/w = 0` (linear bindings are erased when constructing
a replicable lambda), `w/w = w`, `0/w = 0`, `pi/1 = pi`.

This rule prevents a linear variable from being captured in an
unrestricted closure body.  The broken Atkey 2018 rule would allow
`fn(own f: i64 -> i64) => fn(x) => f(f(x))` — using the linear
`f` twice inside a replicable closure.  The corrected rule rejects
this because `f` has grade `1` and `1/w = 0`, so `f` is not
available inside the closure body.

**Subsumption.**  Grade weakening: `r <= s` allows a value at
grade `r` to be used where grade `s` is expected.

### 6.3 The Twenty-Two Dimension Instances

The twenty-two dimensions in the table from §1.1 are not all
semirings.  The uniform-framework claim is that each dimension is
a **graded algebraic structure** satisfying a common checking-
kernel interface, and the kernel dispatches to one of five tiers
depending on the dimension's
structure.  The App/Let/If/Lam rules of §6.2 apply to every
dimension; the operations they invoke differ by tier.

**Kernel interface** (what every dimension provides):

```
ord_D        a preorder over grades (required for subsumption)
par_D        parallel combine (commutative monoid — used at if/match joins)
seq_D        sequential combine (monoid — used at Let and App)
valid_D      validity predicate (true for total dimensions; partial
             operations return None for invalid combinations)
```

**Tier classification of the twenty-two dimensions:**

```
Tier  Shape                      Dimensions                                Kernel dispatch
────  ─────────────────────────  ──────────────────────────────────────── ─────────────────
S     Commutative semiring       3 Usage, 4 Effect, 5 Security,           §6.2 rules apply
      (par = +, seq = *, 0 is    7 Lifetime, 8 Provenance, 9 Trust,       unchanged
       annihilator for seq)      11 Observability, 13 Complexity,
                                 14 Precision, 15 Space, 16 Overflow,
                                 17 FP order, 18 Mutation,
                                 19 Reentrancy, 20 Size, 22 Staleness
                                 = sixteen dimensions
L     Lattice with validity      10 Representation, 12 Clock domain,      §6.2 rules plus
      (par = join, seq = meet,   plus the Capability modality (§16.4,     valid_D check at
       validity rules out        cap-lattice on shareable tags)           every par and seq
       incompatible joins)                                                application
T     Typestate                  6 Protocol (including multiparty         §11 session
      (no par/seq — operations   session types and replay-tag             transition rules
       are transitions on state) refinement)                              dispatch
F     Foundational               1 Type, 2 Refinement                     bidirectional
      (discharged by                                                      elaboration +
       elaboration, not by                                                SMT; not grade
       grade arithmetic)                                                  arithmetic
V     Versioned                  21 Version                               §15.4 refinement /
      (lattice of version                                                 §15.6 migration
       labels with adapter                                                adapter resolution
       edges — no seq, only
       consistency check)
```

The product of all twenty-two grade vectors is checked at every
expression site.  Wall-clock concerns the kernel cannot
statically verify (energy consumption, latency bounds, hardware
clock rate) live as user-defined Tier-S dimensions in
`Std.Budget` rather than as kernel built-ins; see §6.6 for the
declaration mechanism.  Per-tier details follow.

**Dimension 1: Type.**  Tier F.  Checked by the standard bidirectional
type-checking algorithm.  Determines which grade elements are valid
for the other dimensions.

**Dimension 2: Refinement.**  Tier F.  Predicates collected during
elaboration, discharged by SMT.  Interact with grades through
dependent grades (§6.7) — a refinement can mention a grade variable
and vice versa.

**Dimension 3: Usage.**  Tier S.  The `{0, 1, w}` semiring described
in §6.1.  Maps to surface syntax: `own` = grade 1, `ref` = grade w,
`affine` = grade <= 1, `@[copy]` = grade w on the type, `ghost` =
grade 0.  Catches use-after-free (1 used as w), resource leaks (1 not
consumed to 0), and double-free (1 + 1 = w, rejected for linear
binding).

**Dimension 4: Effect.**  Tier S.  The set of effect labels ordered by
the subset relation.  `Tot` (empty set) is the zero.  Addition is set
union: `IO + Async = {IO, Async}`.  Multiplication is also union:
applying an effectful function to an effectful argument combines
their effects.  `Read <= Write` (Write implies Read).  Effects are
monotonic — once an expression has an effect, no subexpression can
remove it.

```
+ = union              * = union           0 = Tot (empty set)
Tot + e = e            Tot * e = e         1 = Tot
e + e = e              IO * Async = {IO, Async}
```

**Dimension 5: Security.**  Tier S.  Two-element lattice
`unclassified < classified`.  Addition is join (combining public
and secret yields secret).  Multiplication is also join for
non-zero grades: `classified * 1 = classified`, but
`classified * 0 = 0` (ghost computation on secret data is erased
and leaks nothing).

The compiler tracks the security grade of every value.  A function
whose return type is unclassified cannot depend on classified
inputs unless the body contains a `declassify` with an explicit
policy.  This is the noninterference property: varying classified
inputs does not vary unclassified outputs.

**Dimension 6: Protocol.**  Tier T.  Session type state is checked by
the §11 transition rules — no par/seq arithmetic applies because
protocol progression is not a commutative combination.  A channel
carries its current protocol state in its type; each send/receive
advances the state.  Using a channel after the protocol is complete
is a compile error — the channel has no valid next transition.
Multiparty sessions and projection follow §11.5.

**Dimension 7: Lifetime.**  Tier S.  Region variables.  The grade
records which region a reference belongs to.  The preorder is lifetime
outlives: `'a <= 'b` when `'a` outlives `'b`.  A reference with
a longer lifetime can be used where a shorter one is expected.
Lifetime parameters are explicit at every function, every let-binding
holding a reference, and every type application carrying a region.
FX does not infer lifetimes (rigor-first, §1.1 and Appendix E).

**Dimension 8: Provenance.**  Tier S.  A lattice of data origin labels:
`Source(name)`, `Derived(parent, transform)`, `Aggregated(list)`,
`Unknown`.  Addition merges provenance chains.  The preorder tracks
whether the provenance is known: `Source("x") <= Unknown`.  Functions
that require known provenance (`requires provenance != Unknown`)
reject untracked data.

**Dimension 9: Trust.**  Tier S.  The lattice `Verified > Tested > Sorry >
Assumed > External`.  Propagates as minimum through the call graph:
a function that calls anything with trust `Sorry` inherits trust
`Sorry`.  Addition is min.  Release builds require trust >= Verified
on all reachable code (except Assumed, which is tracked separately
for mathematical axioms).

**Dimension 10: Representation.**  Tier L.  Layout attributes
(`repr(C)`, `repr(packed)`, `repr(big_endian)`) form a lattice with
join = "coarsest compatible layout" and meet = "tightest compatible
layout".  `valid_Representation(join(a, b))` returns None when the
layouts are incompatible (e.g., `repr(packed)` and `repr(aligned(8))`
jointly over a non-aligned payload).  Incompatible joins are compile
error T047 (incompatible representation).

**Dimension 11: Observability.**  Tier S.  Two-element lattice
`opaque < transparent`.  In a `with CT` context, all values must
be opaque — their access pattern cannot depend on their content.
Addition is join: combining opaque and transparent yields opaque
(the more restrictive choice).  A `transparent` annotation is a
grant — it says "this value's access pattern may leak its content."

**Dimension 12: Clock domain.**  Tier L.  Grade is `combinational |
sync(clk_id)`.  Combinational is the unit — a combinational signal
can feed any domain.  Lattice operations:

```
par (join)   combinational \/ sync(c) = sync(c)
             sync(a) \/ sync(b)       = (if a == b) sync(a)
seq (meet)   combinational /\ r        = r
             sync(a) /\ sync(a)        = sync(a)
valid_Clock  sync(a) \/ sync(b), a != b  =>  None  (cross-domain error)
```

Cross-domain mixing without a synchronizer fails the validity check
and produces compile error CD001.  Explicit synchronizer via
`sync_2ff(x, from: clk_a, to: clk_b)` returns `valid`.

**Dimension 13: Complexity.**  Tier S.  Naturals with addition.
`0` = free.  `cost(f) + cost(g)` = combined cost.  The preorder:
`n <= m` when `n <= m`.  A function declared `cost O(n)` must have
all call paths bounded by O(n).  The compiler checks this by
summing the declared costs of called functions.  When cost is not
declared, the compiler requires `unbounded`.

**Dimension 14: Precision.**  Tier S.  Rational number tracking
floating-point error.  Propagation uses condition-number-aware
accumulation (Higham §3.3) rather than naive ULP addition — this
correctly handles catastrophic cancellation and matches FPTaylor's
treatment.  `exact` is grade 0 (no error); `precision(a + b)` is
bounded by `(|a| + |b|) / |a + b|` ULPs in the worst case.  The
compiler reports the accumulated precision at function boundaries.

**Dimension 15: Space.**  Tier S.  Natural numbers tracking allocation.
`0` = no allocation (stack only).  Each `Alloc` operation adds its
size.  The preorder: `n <= m` when `n <= m`.  A function declared
with `Alloc(Stack, bound: 4096)` must have all allocation paths
within 4096 bytes.

**Dimension 16: Overflow.**  Tier S.  Four-element set `{exact, wrap, trap,
saturate}` where `exact` is the bottom.  `exact <= wrap`,
`exact <= trap`, `exact <= saturate`.  The remaining three are
incomparable — mixing `wrap` and `trap` in the same expression is
a type error unless one is explicitly coerced.  `exact` means the
compiler must prove the result fits in the target width — if it
cannot, it is a compile error.  Functions using `int`/`nat`
(arbitrary precision) bypass overflow checking entirely because
the representation grows as needed, but require `with Alloc`.

**Dimension 17: FP order.**  Tier S.  Two-element set `{strict, reassociate}`.
`strict <= reassociate`.  Strict means left-to-right evaluation,
bit-identical results across platforms.  Reassociate permits the
compiler to reorder FP operations for SIMD.  A function declared
`with Reassociate` may produce different results on different
hardware.

**Dimension 18: Mutation.**  Tier S.  A lattice:
`immutable < append_only < monotonic < read_write`.  Immutable is
the default (no mutation at all).  `append_only` permits adding
to the tail, never removing or overwriting.  `monotonic` permits
changes that move forward in a declared partial order.
`read_write` permits any mutation.  The preorder: a less-mutable
binding can be used where a more-mutable one is expected, but not
vice versa.

**Dimension 19: Reentrancy.**  Tier S.  Two-element set
`{non_reentrant, reentrant}`.  `non_reentrant` is the default —
the compiler verifies that no call path from the function leads
back to itself.  `reentrant` (granted by `rec` or `with Reentrant`)
permits self-reference but mandates a termination proof
(`decreases` clause) or explicit `with Div`.

**Dimension 20: Size.**  Tier S.  Grade domain `omega + 1` (naturals
plus infinity).  Tracks observation depth for codata values (§3.5).
Semiring:

```
par (max)     max(a, b)          parallel observation — worst case
seq (+)       a + b truncated     sequential observation — chain depth
0             0                   fully observed (dual of linear 0)
1             1                   one destructor step (unit of seq)
omega         top                 unbounded observation
ord           standard numeric    0 < 1 < 2 < ... < omega
```

A `tail(x : stream<s>(a))` returns `stream<s - 1>(a)`; each
destructor call consumes one size unit.  Productive construction
via `unfold<s>` requires `with Productive` and guarded recursion
(see §3.5).  `with Div` escapes productivity at the cost of trust.

**Dimension 21: Version.**  Tier V.  Grade domain = lattice of
positive-integer version labels, extended with adapter edges
(§15.6).  Unlike Tier S dimensions this is not a commutative
semiring — version has no multiplicative composition, only a
consistency check at each expression site: if a producer at
`version(k)` flows to a consumer bound to `version(j)`, the
compiler looks for a `refines` proof or a declared `migration`
adapter between `k` and `j` (§15.4).  Absent either, compile
error V001 (`no adapter between versions`).  Subsumption:
`v1 <= v2` iff every obligation of a consumer at `v2` is
discharged by a producer at `v1` via refinement or adapter.
Implicit default is `version(1)`; `@[version(N)]` grants a
non-default label.  The grade is erased at runtime for code-
dispatch purposes (the compiler resolves which version runs at
build time per §15.8) but survives in the binary's symbol
table for multi-version coexistence.  This is the 21st dimension
and lives in its own tier because the lattice-with-adapter
structure does not fit the S/L/T/F shapes of §6.2.

**Dimension 22: Staleness.**  Tier S.  Grade domain `(N ∪ {∞}, min,
+, ∞, 0)`.  Tracks admission delay between event production and
event consumption — the load-bearing primitive for asynchronous
training, replicated systems, and any pipeline that admits
out-of-order events under bounded staleness.  Surface annotation
on values: `stale(t, tau)` is `t` at staleness grade `tau`; on
functions: `with Stale(tau_max)` declares the maximum admissible
staleness.  The semiring's parallel combiner is `min` (worst-case
freshness) and sequential combiner is `+` (delays accumulate
along a chain).  Identity `0` is "fresh"; the top element is "no
admission".  Staleness is a *step counter* — a logical delta the
producer and consumer agree on, not a wall-clock value — so the
kernel can discharge the canonical admission obligation
`pre eta * lambda_max(h) * tau <= critical;` (ASGD-style updates)
via SMT on dependent grades (§6.7).

**Wall-clock dimensions are not kernel built-ins.**  Energy,
Latency, Power, and analogous wall-clock concerns are not
provable by the compiler — they depend on hardware,
scheduling, and IO patterns the kernel does not model.  They
live as user-defined Tier-S dimensions shipped in `Std.Budget`
(§6.6 user-defined-dimension mechanism); the compiler propagates
declared bounds through composition but cannot verify the
underlying physical claim.  Annotations of the form `with
Energy(<= E)` or `with Latency(<= L)` are thus declarations of
intent surfaced in the signature, not kernel-discharged
guarantees, and consumers reading them should treat them as such.

### 6.3.1 Practical Grade Checking

The grade checker maintains a grade vector for each variable in
scope.  At each expression, it updates the vectors according to
the typing rules.  At the end of a function body, it verifies that
every linear variable (grade 1) has been reduced to grade 0
(consumed).

A concrete example:

```
fn process(handle: file_handle, ref config: settings) : string with IO
begin fn
  let content = read_all(ref handle);   // handle: 1 -> borrow (still 1)
  let name = config.host;               // config: w -> w (ref, unlimited)
  close(handle);                         // handle: 1 -> 0 (consumed)
  f"{name}: {content}"
end fn;
```

The grade vector for `handle` through the body:

```
Entry:                    handle = 1 (linear)
After read_all(ref):      handle = 1 (borrowed, not consumed)
After close(handle):      handle = 0 (consumed)
Exit check:               handle = 0  ok (linear fully consumed)
```

If the programmer writes `close(handle)` twice:

```
error[M001]: linear value 'handle' already consumed
  close(handle);
        ^^^^^^
  Previously consumed at line 3: close(handle)
  handle has type file_handle (linear, must be used exactly once)
```

If the programmer forgets `close`:

```
error[M002]: linear value 'handle' not consumed
  fn process(handle: file_handle, ...) : string
             ^^^^^^
  handle : file_handle must be consumed before function returns
  Suggestion: add close(handle) or drop(handle) before the return
```

The same mechanism handles all twenty-two dimensions
simultaneously.  For the security dimension: if `handle` were
`secret`, every expression using it would propagate the
`classified` grade, and returning the result to an unclassified
context would be caught.

### 6.4 Separation Logic as the Usage Grade

FX does not have a separate separation logic system.  Separation
logic is the usage grade — the separating conjunction `*` is the
`+` of the grade algebra.

The usage grade generalizes from the `{0, 1, w}` semiring to a
permission PCM (partial commutative monoid):

```
type permission
  = Frac of p: rational { 0 < p and p <= 1 }
  | Zero
  | Omega
  ;
```

Composition:

```
Frac(p) + Frac(q) = Frac(p + q)   when p + q <= 1
Frac(p) + Frac(q) = CONFLICT       when p + q > 1
Zero + x = x
Omega + Omega = Omega
```

The surface syntax maps to permissions:

```
own x       x at Frac(1)     full permission (read/write/free)
ref x       x at Frac(p<1)   fractional (shared read-only)
ref mut x   x at Frac(1)     full permission (exclusive read/write)
ghost x     x at Zero         erased (proof-only)
```

The frame rule is automatic.  When `swap(a, b)` requires `Frac(1)`
for both `a` and `b`, the caller's other resources at their own
fractions are the frame — untouched by the call.  If `a` and `b`
are the same location, `Frac(1) + Frac(1) > 1` and the compiler
rejects the call.

Fractional permissions enable concurrent sharing:

```
fn share<a: type>(own x: ptr(a)) : (ref ptr(a), ref ptr(a))
// Frac(1) -> Frac(0.5) + Frac(0.5)

fn unshare<a: type>(ref x1: ptr(a), ref x2: ptr(a)) : own ptr(a)
  pre same_origin(x1, x2);
// Frac(0.5) + Frac(0.5) -> Frac(1)
```

### 6.5 Ghost State and Custom PCMs

Ghost values live at the **Ghost mode** — the static layer of
two-level type theory (2LTT, Annenkov-Capriotti-Kraus-Sattler
MSCS 2023; §30.12, Appendix H).  Ghost mode admits classical
reasoning (excluded middle, choice, Hilbert ε) because its
content is erased at codegen and never observable at runtime;
the static-layer / dynamic-layer separation prevents classical
content from leaking into constructive Software code.  This
supersedes the previous "Zero permission" mechanism — ghost is
not a usage grade but a mode boundary, and the kernel's
Grade-zero axiom is correspondingly absent (Appendix H.11).

```
fn alloc_tracked<a: type>(init: a) : (own ptr(a), ghost invariant(ptr_valid))
begin fn
  let p = alloc(init);
  let inv = ghost_create(ptr_valid(p));
  (p, inv)
end fn;
```

The invariant is erased.  Zero cost.  But tracked in proofs.
Ghost state enables shared invariants for concurrency: multiple
threads access shared state if they all respect a ghost
invariant; the invariant lives at the proof-only layer, the
runtime implementation at the runtime layer, and the cross-layer
proof relating them is the `ghost ⊣ erase` adjunction's unit law
(§6.9).

**The 2LTT discipline.**  A program that uses excluded middle or
choice in a ghost binding cannot extract that binding to a
runtime value because the extraction would require a
constructive witness the static layer does not supply.  This is
the formal grounding of FX's three escape hatches (§1.6):
`sorry`, `axiom`, and `with Div` are all proof-only constructs
that propagate trust through the call graph (§10.6) — release
builds require `Verified` trust on every reachable runtime-layer
function, with `Assumed` permitted only via documented
`@[trust_assumed("rationale")]`.

Custom PCM resources extend the permission system with
domain-specific composition:

```
grade_dimension MonotonicCounter
  type grade = nat;
  val unit = 0;
  val op(a, b) = max(a, b);
  law commutative: forall(a: grade, b: grade), op(a, b) == op(b, a);
  law associative: forall(a: grade, b: grade, c: grade),
                     op(op(a, b), c) == op(a, op(b, c));
  law identity: forall(a: grade), op(unit, a) == a;
end grade_dimension;

fn increment(ghost ctr: MonotonicCounter, ref mut state: state) : unit
  post _ => ctr >= old(ctr);
```

The counter never decreases.  This is proved by the PCM laws.  The
pattern applies to append-only logs, CRDT counters, and monotonic
knowledge acquisition in caches.

### 6.6 User-Defined Grade Dimensions

Users define domain-specific dimensions in three forms.

**Semiring form** for Tier S commutative dimensions:

```
grade_dimension ApiBudget
  type grade = nat;
  val zero = 0;
  val one = 1;
  val add = (+);
  val mul = (*);
  val leq = (<=);
end grade_dimension;
```

The compiler verifies the semiring laws via SMT.

**Product form** when several Tier S budgets compose pointwise as
a single dimension (Latency × Energy × Bits × PeakBytes for
budget calibrators is the canonical case):

```
grade_dimension Budget
  product
    energy   : nat (max, +, 0, 0);
    latency  : nat (max, +, 0, 0);
    bits     : nat (max, +, 0, 0);
    peak_mem : nat (max, +, 0, 0);
  end product;
end grade_dimension;
```

The product semantics is pointwise: `(e_1, l_1, b_1, p_1) ⊕
(e_2, l_2, b_2, p_2) = (e_1 ⊕ e_2, l_1 ⊕ l_2, b_1 ⊕ b_2, p_1 ⊕
p_2)`.  Identity is the tuple of identities; subsumption is
pointwise.

**Lattice form** for Tier L dimensions (semilattice + optional
validity predicate, no multiplicative operation):

```
grade_dimension Consistency
  lattice
    elements: { Strong, BoundedStaleness(K: nat), CausalPrefix,
                ReadYourWrites, Eventual };
    join: ⊔;
    bottom: Eventual;
  end lattice;
end grade_dimension;

grade_dimension Representation
  lattice
    elements: { Native, C, Packed, BigEndian, Aligned(n: nat),
                Transparent };
    join: λ(a, b) ⇒ ...;
    bottom: Native;
    valid: λ(r) ⇒ ¬conflicting(r);
  end lattice;
end grade_dimension;
```

The optional `valid` predicate rejects invalid joins per the
§6.3 Tier L convention: composition fails when `valid_d(join(a,
b))` returns false.  User-defined dimensions participate in the
same grade-checking algorithm as the built-in twenty-two.

**Stdlib-shipped budget dimensions.**  Wall-clock concerns the
kernel cannot prove ship as user-defined dimensions in
`Std.Budget`.  The canonical declarations:

```
// Std.Budget — opt-in via 'open Std.Budget;'
grade_dimension Energy
  type grade = nat;             // joules / picojoules / etc.
  val zero = 0;
  val one  = 0;                  // additive identity for budget composition
  val add  = max;                // parallel: max budget across branches
  val mul  = (+);                 // sequential: sum along a chain
  val leq  = (<=);
end grade_dimension;

grade_dimension Latency
  type grade = nat;             // microseconds / cycles / etc.
  val zero = 0;
  val one  = 0;
  val add  = max;
  val mul  = (+);
  val leq  = (<=);
end grade_dimension;
```

Surface usage: `with Energy(<= 1_000_000), Latency(<= 250)`
declares per-function upper bounds.  The annotation propagates
through composition pointwise like any user-defined Tier-S
dimension; the compiler tracks the declared bound but does not
verify it against any hardware or runtime measurement — wall-
clock guarantees are an annotation discipline, not a kernel
proof obligation.  Builds that need empirical validation hook
into §23.5 benchmarks against declared budgets.

The same pattern declares `Power`, `WallClock`, `BitsTransferred`,
or any other resource the deployment cares to track without
inflating the kernel.

### 6.7 Dependent Grades

Because FX is dependently typed, grades can be terms:

```
fn take_n<a: type>(n: nat, xs: list(a)) : list(a)
  pre n <= length(xs);
```

The grade of `xs` depends on the runtime value `n`.  Grade
constraints involving runtime values are discharged by SMT.

**Typing rule (G-Dependent).**  For an operation `op : (x : T) →
S` whose grade vector `p` depends on the runtime value of `x`,
write the binding as `x :_p(x) T` and the typing rule for
application:

```
G ⊢_q1 f : Π (x :_p(x) T). S(x)     G ⊢_q2 a : T
─────────────────────────────────────────────────────────
G ⊢_(q1 + p(a) ⊗ q2) f a : S[a/x]
```

The substitution `p(a)` evaluates the grade-vector function `p`
at the runtime value `a`.  This entails: when `p(x) = c` is
constant, the rule reduces to the standard graded-application
rule with grade `c`; when `p(x)` depends on a runtime value, the
discharge is by SMT (Tier S commutative semiring obligations
have the form `r ≤_d s`); when `p(x)` involves a Tier T
typestate transition, the kernel checks whether the transition
fires successfully on the supplied initial state.

The most consequential application is the asynchronous-admission
gate for Staleness (dim 22): a function `merge_grad` taking a
stale gradient at grade `τ` requires the dependent-grade check
`η · λ_max(H) · τ ≤ critical`, where `η`, `λ_max`, `τ` are
runtime values and `critical` is a recipe-tier-determined
constant.  The SMT discharge is performed at the call site
before the function body is entered.

Grade parameters are written explicitly at every binding site.
FX does not infer grades from usage; the SMT solver discharges
stated constraints only.  Omitting a grade annotation where one
is required is compile error M003 (missing grade).  This follows
the rigor-first rule (§1.1, Appendix E).

### 6.8 Dimension Composition Rules

The twenty-two dimensions compose point-wise on the grade vector.
Most compositions follow mechanically from the per-dimension semirings,
lattices, typestates, and foundational rules of §6.3.  A finite
number of compositions express genuine soundness collisions — one
dimension's operations render another unsafe unless the programmer
explicitly acknowledges the interaction.  This section is the
canonical catalog.  Each rule carries a dedicated error code and
resolves a specific gap from `gaps.json`.

Rules are stated as guards on the rest of the type system: when
the guard condition holds, the program is compile error with the
named code.  All rules are checked at the site where the two
dimensions meet; no global analysis is required.

**I002 — classified × Fail (gap #102).**  Let `b` be a function
body whose `Fail(E)` sites produce error values containing
classified (`secret`-graded) data.  The declared effect row must
contain `Fail(secret E)`; declaring `Fail(E)` with a classified
payload is I002 (`error payload carries classified data; declare
'Fail(secret E)'`).  The `secret E` marker propagates through the
handler in the usual noninterference way: catch arms that observe
it inherit classified grade.  Rationale: a catch arm that logs the
error leaks the classification unless the row names it.  No
auto-classification — rigor-first requires the programmer to state
`secret`.  Jif and FlowCaml both treat exception payloads as
information-flow sources; FX makes the label explicit in the row.

**L002 — borrow × Async (gap #104).**  A borrow binding (shared
`ref x: T` or exclusive `ref mut x: T`) live at an `await(...)`
site is L002 (`borrow does not live long enough across suspension
— captured values must be 'own' or '@[copy]'`).  "Live at await"
uses the same liveness analysis as §6 grade checking.  Scoping the
borrow to before the await, or cloning via `@[copy]`, satisfies the
rule.  Rust enforces the same restriction via its future state
machine check; FX makes it a cross-dimension rule because the
underlying risk (the caller mutates or moves the referent during
suspension) is a consequence of async scheduling, not ownership
alone.

**E044 — CT × Async (gap #105).**  Declaring `with CT, Async` on
the same function is E044 (`constant-time and async are
incompatible — async scheduling introduces observable timing
variation`).  There is no refinement that permits the combination;
the two dimensions are contradictory.  CT-wasm, FaCT, and Jasmin
all operate on synchronous straight-line code for this reason.
Crypto functions that must appear to callers as async wrap a
synchronous CT core in an `await` at the boundary, keeping the CT
region sync-only.

**I003 — CT × Fail on secret (gap #106).**  Inside a `with CT`
function, `fail(e)` whose condition (the surrounding `if` or
`match` scrutinee) is classified is I003 (`fail on secret-dependent
condition violates CT — use constant-time select and deferred
fail`).  This specializes §12.5's general CT-branch rule to the
control-flow effect `Fail`: dispatching an exception exposes the
branch taken, which leaks the secret.  The remedy is to compute a
secret-independent result first (via `ct_select` or a masked
operation) and raise `fail` outside the secret region — or to
widen the function's effect row to drop CT.

**M012 — monotonic × concurrent (gap #108).**  A binding whose
mutation dimension (§6.3 dim 18) is `monotonic` or `append_only`
in a machine or module whose `concurrency` (§13.10) is not
`single_thread` and whose store is not `atomic(T)` is M012
(`monotonic update in concurrent context requires 'atomic(T)' or
'concurrency lock_free'`).  LVars (Kuper-Newton) and CvRDTs
formalize the safety condition: concurrent monotonic updates are
race-free when the underlying write is atomic (for scalars) or the
merge is commutative/associative/idempotent (for lattice state).
FX checks the atomic wrapper or lock-free concurrency declaration;
lattice merge is reserved for user-defined PCMs (§6.5).

**P002 — ghost × runtime conditional (gap #109).**  A ghost-graded
value (grade 0, erased) appearing as the scrutinee of a runtime
`if`, `while`, `match`, pattern guard, or array index is P002
(`ghost value in runtime position — ghost terms are erased and
have no runtime representation`).  The Tier F erasure rule
already blocks this at code generation; P002 is the user-facing
diagnostic emitted at the source site.  Ghost values may appear
in `pre`, `post`, `decreases`, `assert`, and inside `verify`
blocks — positions erased along with the proof.  F* `GTot`, Idris 2
multiplicity 0, and Agda `@0` all draw the same boundary; FX
names the rule so agents surface it directly instead of inferring
it from kind-checker failure.

**I004 — classified × async × session (gap #112).**  Sending a
classified value over a session channel from a `with Async`
context without `with CT` and without a `declassify` at the send
point is I004 (`classified data over async session may leak
timing — require 'with CT' or declassify at boundary`).  The
three-way collision is honest about a genuine limitation: even
well-typed session code can leak protocol state via send latency
when the data is secret.  The two valid responses are (a)
synchronous CT region at the send (consistent with E044 — the CT
region must not itself be async) or (b) explicit declassification
at the boundary per §12.4.  No silent allowance.  The academic
literature (Capecchi-Castellani-Dezani-Rezk 2014) leaves this
open; FX closes it conservatively at the cost of extra
ceremony.

**N002 — decimal × overflow(wrap) (gap #113).**  A function with
return type or parameter of exact decimal (`decimal`, `dec32`,
`dec64`, `dec96`, `dec128`, `dec256`, `dec512`, `dec1024`)
declaring `with overflow(wrap)` is N002 (`wrap overflow has no
meaning for exact decimal types — use trap, saturate, or widen`).
IEEE 754-2008 decimal arithmetic defines trap/round/saturate, not
wrap.  Arbitrary-precision `decimal` cannot overflow at all; its
overflow annotation is `exact`.  Fixed-width decimals require
`with overflow(trap)` or `with overflow(saturate)`.  Mixing with
`exact` requires a compiler-discharged proof that the result fits
— this is the §6.3 overflow preorder `exact <= trap`.

**L003 — borrow × spawn (gap #114).**  `spawn_in(group, closure)`
inside a `task_group fn(group) => ...` (§11.7) permits the
closure to capture borrows whose lifetime outlives the surrounding
group — the structured-concurrency invariant ensures all spawned
tasks complete before the `task_group` scope exits, so borrows
live long enough by construction.  This matches Rust's
`thread::scope` (scoped threads, stable 2022).  A bare
unscoped `spawn(closure)` requires every captured value to be
`own` or `@[copy]`; capturing any borrow from unscoped spawn is
L003 (`unscoped spawn cannot capture borrow — use task_group for
scoped spawn, or move ownership into the closure`).  The diagnostic
suggests the scoped alternative concretely.

**Composition with §7.11 defer, §12.7 secure zero, §9.3 effect
lattice.**  Three rules are reductions rather than new checks:

 * **session × Fail** (gap #103) reduces to G-Linear-Cleanup-On-Fail
   (§7.11, code M011) plus a new stdlib primitive
   `cancel(ch) : unit with Fail(Cancelled)`.  Session channels are
   linear (§11.3); an errdefer registering `cancel(ch)` near the
   channel acquisition site satisfies M011 and propagates a
   Cancelled message to the peer per the session type.  EGV
   (Fowler-Lindley-Morris-Decova, POPL 2019) formalizes the
   semantics.  No new error code — M011 covers the case once
   `cancel` is available.

 * **classified × linear × Fail** (gap #111) reduces to M011
   (defer/errdefer for linear) plus §12.7 secure zeroing on drop.
   The compiler emits `secure_zero(v); drop(v)` automatically when
   a classified-plus-linear binding leaves scope, including via
   Fail unwinding.  No new rule.  Example: an errdefer registering
   cleanup of a `secret linear aes_key` runs through §12.7 on
   every abort path.

 * **multiple Fail effects** (gap #110) follows from the §9.3
   effect lattice: `Fail(E1) \/ Fail(E2) = Fail(E1 | E2)`.  The
   function signature always names the full union; callers that
   handle one variant and propagate the other do so via standard
   row subtyping.  No collision — just algebra.

**S010 — Staleness × CT (gap #159).**  A function declared
`with CT` operating on a value of grade `Staleness(τ > 0)` is
S010 (`constant-time observation cannot be guaranteed when
freshness is checked at runtime`).  The constant-time discipline
requires execution time independent of input data, but a
positive staleness grade implies runtime branching on the
freshness check.  Suggested remedy: drop CT and accept the
non-constant-time path, or tighten the admission policy to
reject any `τ > 0` at the channel boundary so the runtime check
is unreachable.

**S011 — Capability × Replay (gap #161/#166).**  A capability
flowing into a replayable channel must itself carry a
replay-safe representation: the capability's identity is part of
the ordering log.  Capabilities backed by ephemeral resources
(file descriptors, GPU memory handles) cannot be replayed across
runs because their identity does not survive a fresh process —
S011 (`capability not replay-safe; declare '@[replay_stable]'
or use a content-addressed handle`).  Suggested remedy: declare
the capability `@[replay_stable]` so the runtime records a
stable name (typically a content-addressed handle) in the
replay log.

**Audit scope.**  The twelve rules above cover all collisions in
gaps.json (#102-114, #159, #161) that the initial review
identified as genuine two- or three-way soundness problems.  The
22-dimension space has `C(22, 2) = 231` pairs and
`C(22, 3) = 1540` triples; the remaining compositions either
reduce to existing infrastructure (lattice join, linearity,
typestate) or pose no collision (independent dimensions whose
product is a straight vector check).  Each rule corresponds to
a missing 2-cell in the §6.0 mode theory: adding a 2-cell admits
the composition; the absence of a 2-cell is exactly the
collision.  User-defined dimensions (e.g. `Std.Budget.Energy`,
`Std.Budget.Latency`) compose pointwise without participating
in this catalog — the kernel does not enforce stdlib dimensions
across other dimensions, since their content is annotation
rather than proven property.  Future soundness discoveries on
kernel-built-in dimensions are added here as numbered rules with
error codes in Appendix E.1, blocked by the known-unsoundness
corpus of §30.14 until resolved.

### 6.9 Boundary Semantics

Three boundaries between value categories carry runtime semantics
the kernel formalises (`fx_modecat.md` §3.5; Appendix H.7–H.7b).
Each is described in the chapter that introduces the surface
construct it governs:

  * **Erasure boundary** — `ghost` keyword binders (§7.1) and
    proof-block content (§5.4) are erased at codegen.  The kernel
    discipline is two-level-type-theory separation (§6.5,
    §30.12); the surface programmer sees only that ghost
    bindings have zero runtime cost and may carry classical
    reasoning the runtime layer rejects.
  * **Serialization boundary** — `contract` declarations (§14)
    govern decode / encode at boundaries to networks, databases,
    IPC, and disk.  The decode / encode pair is a roundtrip-
    correct adjunction per §14.5 — `C.encode` is the inverse of
    `C.decode` modulo invalid input.
  * **Hardware-synthesis boundary** — `hardware fn` /
    `hardware module` declarations (§18.9–§18.11) project FX
    code onto the synthesizable RTL subset.  The projection is
    one-way; reading hardware signals back into FX requires an
    explicit clock-domain-tagged observation per §18.10.

The §6.8 collision rules are decidable composition checks the
elaborator runs at every expression site.  The kernel-internal
2-cells encoding subsumption and the absent 2-cells encoding
collisions are spelled out in `fx_modecat.md`.

### 6.10 Kernel-Exposed Surface Names

Several kernel-level constructs are referenced by surface FX
under stdlib-shaped type names.  They are not stdlib libraries —
they are *kernel modalities* (Appendix H) made syntactically
ergonomic via type aliases the prelude exposes.  Listing them
here so it is clear they live in the kernel and not in §26
stdlib:

```
Surface form                   Kernel construct                  Defined in
────────────────────────────   ───────────────────────────────   ──────────────
later(t)                       next-tick guarded-recursion        Appendix H.7b
                                modality at the runtime layer
bridge(t)                      parametricity modality at the     Appendix H.7b
                                runtime layer
cap(c, t)                      capability modality at Tier L     §6.3 / §30.11
fix(f) : a                     productive fixed point combinator Appendix H.7b
   where f: later(a) -> a
next(x) : later(t)             lift a value to "available next   Appendix H.7b
   where x: t                   tick"
transport(e, x) : t_2          univalence transport at the        Appendix H.7a
   where e : equiv(t_1, t_2)    contract-boundary layer
   and   x : t_1
quotient type T = U by R       quotient via HIT                  §3.7
                                (data + path constructors)
ghost x: t                     erased / proof-only binding       §6.5 / §30.12
                                (2LTT static-layer view)
```

The PascalCase forms `Later`, `Bridge`, `Cap` that appear in
math-rule blocks (Appendix H) are the *names of the kernel
modalities* in typing-rule notation; the surface FX forms are
the lowercase type-application shapes above, which parse under
the existing grammar (§7 `app_type`).  Channel and machine
types (`channel(p_in, p_out, t)`, machine values) are kernel
translations of session and machine declarations, not
separately surfaced — see §11 and §13 for the surface
constructs and §30.10 for their kernel form.

These names are not redefinable by users — overriding any of
them in `Std.*` or in user code is compile error T067
(`reserved kernel-modality surface name`).  Stdlib
`Std.IxMonad`, `Std.Logic.Decidable`, `Std.Algebra` etc.
(catalogued in §26) provide ergonomic typeclass abstractions
over these primitives, but do not introduce their own
modalities — they live entirely in the derived layer.

The kernel exposes its modalities via these surface names so
programmers write ordinary FX code (`later(a)`, `bridge(t)`,
`cap(c, connection)`) while the elaborator dispatches the
names to the correct kernel rules in §30 and Appendix H.


## 7. Ownership

### 7.1 The Mode System

Every binding has a mode that governs how the value can be used.
The default is linear — every value must be consumed exactly once.
More permissive modes are granted explicitly.

```
Mode          Syntax       Uses      Can drop?   Can copy?
─────────     ─────────    ─────     ─────────   ─────────
Linear        (default)    once      no          no
Affine        affine       <= once   yes         no
Unrestricted  @[copy]      any       yes         yes
Shared ref    ref          any       yes         yes (read-only)
Exclusive ref ref mut      any       yes         no  (read-write)
```

Linear is the default for all types.  Types marked `@[copy]` on
their definition (integers, booleans, floats, `bits(n)`, small
structs with only `@[copy]` fields) automatically get unrestricted
mode on all their bindings.  Every other type is linear.

To explicitly discard a linear value: `drop(x)` or `let _ = x;`.

### 7.2 Owned Values

A parameter without a mode annotation takes ownership.  The value
must be consumed exactly once — passed to another function, returned,
or explicitly dropped.

```
fn process_file(handle: file_handle) : string with IO
begin fn
  let content = read_all(ref handle);
  close(handle);
  content
end fn;
```

`handle` is consumed by `close`.  Using it after `close` is a
compile error.  Not consuming it at all is a compile error.

### 7.3 Borrowed Values

`ref` is a shared borrow — read-only access that can be duplicated:

```
fn inspect(ref data: config) : string
= f"host={data.host}, port={data.port}";
```

`ref mut` is an exclusive borrow — read-write access, one holder:

```
fn increment(ref mut counter: i64) : unit
begin fn
  counter.set(counter.get() + 1);
end fn;
```

A value cannot have both `ref` and `ref mut` borrows simultaneously.
The compiler rejects overlapping mutable borrows.

### 7.4 Affine Values

`affine` means the value may be used at most once but dropping is
permitted.  This suits resources with destructors:

```
fn maybe_use(affine token: auth_token) : unit with IO
begin fn
  if should_proceed();
    consume_token(token);
  end if;
  // token dropped here if not used — destructor runs
end fn;
```

### 7.5 Pattern Matching and Ownership

Pattern matching consumes the scrutinee.  Bound variables in the
matched arm receive ownership of the corresponding parts.

```
fn close_pair(pair: (connection, connection)) : unit with IO
begin fn
  let (a, b) = pair;   // pair consumed; a and b are owned
  close(a);
  close(b);
end fn;
```

Matching on a borrow does not consume:

```
fn peek(ref xs: list(i64)) : option(i64)
= match xs;
    [] => None;
    [h, ..._] => Some(h);    // h is a copy (i64 is @[copy])
  end match;
```

Rules:
- `match x;` where `x` is linear: `x` consumed, arms own parts.
- `match x;` where `x` is `ref`: `x` borrowed, arms get `ref`.
- `match x;` where `x` is `@[copy]`: `x` copied, arms get copies.

### 7.6 Implicit Borrowing at Call Sites

When a function parameter is `ref`, the caller does not write
`ref` at the call site.  The compiler borrows automatically.
When a parameter has no mode annotation (linear), the caller
transfers ownership.

```
fn length(ref xs: list(i64)) : u64;
fn sort(xs: list(i64)) : list(i64);

let xs = make_list(10);
let n = length(xs);     // implicit borrow — xs survives
let ys = sort(xs);      // move — xs consumed
```

The callee's parameter mode determines what happens.  The caller
never annotates `ref` or `own` at the call site.

### 7.7 Context Splitting

When a function uses multiple owned values, the compiler splits the
context algebraically.  The semiring laws govern the split:

- `0 + 0 = 0` — unused in both branches: unused overall.
- `1 + 0 = 1` — used in one branch: used once.
- `1 + 1 = w` — used in both branches: error for linear values.

### 7.8 The @[copy] Propagation Rule

A type is `@[copy]` if and only if all of its components are
`@[copy]`.  The compiler checks this at the definition site:

```
@[copy]
type point { x: f64; y: f64 };       // ok: f64 is @[copy]

@[copy]
type color = Red | Green | Blue;      // ok: no payloads

@[copy]
type option<a: type>
  None;
  Some(a);
end type;
// option(i64) is @[copy]; option(connection) is linear.
```

### 7.9 Integration with Effects

Ownership and effects compose:

```
fn upload_and_close(conn: connection, ref data: buffer) : unit with IO
begin fn
  send(ref conn, data);    // borrow conn to send
  close(conn);              // consume conn
end fn;
```

The signature tells the caller everything: `conn` is consumed,
`data` is borrowed, the function performs IO, and it terminates.

### 7.10 Closure Capture and Ownership

When a lambda captures a variable from its enclosing scope, the
closure's mode depends on what it captures:

```
let x : i32 = 42;              // @[copy] — closure captures a copy
let f = fn(y) => x + y;        // f is @[copy] (captures only @[copy])
f(1); f(2);                     // can call multiple times

let conn : connection = open("host");  // linear
let g = fn() => close(conn);    // g is linear (captures linear conn)
g();                             // consumes g (and conn inside it)
// g();                          // error: g already consumed
```

A closure that captures a linear value is itself linear — it can be
called at most once, because calling it consumes the captured
resource.  A closure that captures only `@[copy]` values is
`@[copy]`.

This is what the Lam rule (§6.2) enforces: context division by the
lambda's grade erases linear bindings from replicable closures.

Borrowing in closures:

```
let config = load_config();
let get_host = fn() => config.host;   // borrows config (ref)
let host1 = get_host();
let host2 = get_host();               // ok: closure borrows, not owns
// config still alive
```

The compiler infers whether a closure borrows or moves each captured
variable based on how the closure uses it.  If the closure only
reads the variable, it borrows.  If it consumes the variable (passes
it to a function that takes ownership), it moves.

A closure's lifetime cannot outlive the borrows it holds:

```
fn make_printer(ref data: list(i64)) : fn() -> unit
= fn() => print(data);
// The returned closure borrows data.  The caller must ensure
// data outlives the closure.  On pub fn, the lifetime is explicit:
// fn make_printer<r: region>(ref(r) data: list(i64)) : fn() -> unit with r
```

### 7.11 Defer and ErrDefer

FX provides two cleanup statements scoped to the enclosing lexical
block (`begin` body, `try` body, `catch` arm, if-branch, match-arm,
loop body):

```
defer    expr;     runs expr at scope exit regardless of how the scope
                   exits (normal return, Fail propagation, Exn propagation)
errdefer expr;     runs expr at scope exit ONLY when the scope exits via
                   a Fail or Exn abort; does not run on normal return
```

Both fire in LIFO order at scope exit.  When both `defer` and
`errdefer` appear in the same scope and the scope exits via Fail or
Exn, all pending cleanups are interleaved by source declaration
order, reversed (LIFO) for execution.  On normal return, only
`defer` cleanups run.

```
fn with_file(path: string) : string with IO, Fail(io_error)
begin fn
  let handle : file_handle = try open(path);
  defer close(handle);                    // always runs at scope exit

  let content : string = try read_all(ref handle);
  let meta : string = try read_metadata(ref handle);
  return content ++ meta;
  // scope exit: close(handle) runs, consuming handle, on both the
  // normal-return path and any Fail-propagated path.
end fn;
```

**The partial-initialization pattern** uses `errdefer` when success
transfers the resource outward and failure must release a
partially-constructed object:

```
fn make_logged_connection(host: string, log_path: string)
    : own connection with IO, Fail(connect_error), Alloc
begin fn
  let log : file_handle = try open_for_append(log_path);
  errdefer close(log);
    // Cleans up the log on any Fail below.  On success, log
    // transfers into the connection via build_connection and is
    // consumed there — the errdefer does not run.

  let sock : socket = try open_socket(host);
  errdefer close_socket(sock);

  let conn : own connection = build_connection(sock, log);
  return conn;
  // Normal return: neither errdefer runs; sock and log are linearly
  // consumed by build_connection and now live inside conn.
end fn;
```

**Typing rules.**

```
Rule G-Defer:
  G |-_p expr : unit with e
  Fail(_) ∉ e     Exn(_) ∉ e            (defer body cannot itself fail)
  e ⊆ declared_effects(enclosing_fn)    (effect subset of enclosing)
  ────────────────────────────────────────────────────────────────
  G |-_p defer expr; : unit             registers expr for LIFO cleanup
                                         at every scope exit

Rule G-ErrDefer:
  G |-_p expr : unit with e
  Fail(_) ∉ e     Exn(_) ∉ e
  e ⊆ declared_effects(enclosing_fn)
  enclosing_fn's effect row contains Fail(_) or Exn(_)
      (errdefer is meaningless in a function that cannot fail)
  ────────────────────────────────────────────────────────────────
  G |-_p errdefer expr; : unit          registers expr for LIFO cleanup
                                         at Fail/Exn-aborted scope exits
                                         only
```

The no-Fail-in-defer restriction prevents double-fault during
unwinding.  If the programmer needs a potentially-failing cleanup
(e.g., `close(fd)` that can fail), they handle it inside the defer
body with an explicit `try ... catch ... end try;` block.  This
surfaces the second-level decision at the source site rather than
hiding it in the unwinding machinery.

**The linear-cleanup rule.**

```
Rule G-Linear-Cleanup-On-Fail:
  function body has Fail(_) or Exn(_) in its declared effect row
  for every Fail/Exn abort site F in the body
    (every `try` prefix, every fail(e) call, every explicit re-raise):
      for every linear binding r that is live at F per the standard
      §6 linearity flow analysis:
        ∃ defer or errdefer cleanup for r registered in a scope
        enclosing F
  ────────────────────────────────────────────────────────────────
  body type-checks for linear-on-fail cleanup; otherwise compile
  error M011 (linear value r may leak on Fail path at line L)
```

"Live at F" carries the content: `drop(r)` earlier in the body ends
r's liveness, so subsequent Fail sites have no obligation for r.
`defer drop(r)` keeps r live until scope exit but registers a
cleanup, so the rule is satisfied by the defer.  Both patterns are
valid:

```
// Pattern A — eager drop, r dead at later Fail sites:
let r : handle = try open(path);
// ... use r ...
drop(r);                           // r consumed here
let q : buffer = try allocate(n);  // Fail site; r not live, rule trivially met

// Pattern B — deferred cleanup, r live until scope exit:
let r : handle = try open(path);
defer close(r);                    // cleanup registered; r still live
let q : buffer = try allocate(n);  // Fail site; r live; defer satisfies rule
```

**Scope exit semantics.**

```
Exit path            defer runs?                    errdefer runs?
──────────────────  ─────────────────────────────  ─────────────────────────────
normal return        yes (LIFO)                     no
Fail(_) propagation  yes (LIFO, before propagate)   yes (interleaved LIFO with defer)
Exn(_) propagation   yes (same as Fail)             yes (same as Fail)
try...catch handles  no — scope didn't exit         no — scope didn't exit
  an inner Fail
break / continue     yes (loop body exit)           no (not a Fail/Exn)
Div (non-termination)no — scope never exits         no — scope never exits
                      (if eventually returns,
                       runs normally at that exit)
Async cancellation   yes (cancel raises a typed     yes (same)
                      Fail per §11.7)
```

The compiler checks the linear-cleanup rule as part of §6 grade
analysis.  The unwinding order is specified; the double-fault case
is prevented by the no-Fail-in-defer rule; cancellation is modeled
as a typed `Fail(Cancelled)` so async cleanup uses the same
mechanism.

**Return-expression ordering.**  On normal return, the return
expression evaluates in the exiting scope first (so `return
compute(x)` runs `compute(x)` to a value), then `defer`
cleanups run in LIFO order, then control transfers to the
caller with the already-computed return value.  A deferred
cleanup cannot observe or modify the returned value — the value
is already captured by the time defers run.  This matches Go,
Swift, and Zig semantics and is the one ordering that avoids
both the "defer runs before return computes" surprise and the
"defer can mutate return value" footgun.


## 8. Memory

### 8.1 Regions and Lifetimes

A region `r` represents a scope during which memory is valid.
References carry their region:

```
fn first<a: type, r: region>(xs: ref(r) list(a)) : ref(r) a
  pre length(xs) > 0;
= hd(xs);
```

`static` outlives all other lifetimes:

```
let greeting : ref(static, string) = "hello";
```

Lifetime subtyping: if `r1` outlives `r2`, then `ref(r1, T)` is a
subtype of `ref(r2, T)`.

Region-scoped allocation frees all allocations at once:

```
fn with_arena<a: type>(body: fn(r: region) -> a) : a
begin fn
  let r = new_region();
  let result = body(r);
  free_region(r);
  result
end fn;
```

Lifetime parameters are explicit at every site: every function that
takes or returns a reference, every let-binding holding a reference,
every type application carrying a region.  FX does not infer
lifetimes (rigor-first, §1.1 and Appendix E).  Omitting a lifetime
where a region-carrying value is bound is compile error L001
(missing lifetime annotation).

**Region block form.**  In addition to the `<r: region>`
parameter syntax used by `pub fn` declarations, FX provides a
kernel-level *region block* that opens a fresh region scope and
discharges every allocation made inside it at scope exit:

```
fn parse_with_arena<r: region>(input: ref string) : ast
  with Alloc(Region(r))
begin fn
  region r;
    let tokens = tokenize_into(r, input);
    let parsed = build_ast_into(r, ref tokens);
    return parsed.into_owned();    // copy out before region exits
  end region;
end fn;
```

`region r; ... end region;` opens the region scope for region
variable `r` (introduced via the surrounding `<r: region>`
parameter or via a fresh `<r: region>` introduced at the block
boundary).  Every value allocated at `Alloc(Region(r))` inside
the block is freed at `end region;`.  Values escaping the region
must be moved or copied to a longer-lived region before the
block exits — the compiler discharges the obligation statically
per §8.1's lifetime subtyping.

This is the kernel form for Tofte-Talpin region-based memory
management (Information and Computation 1997), generalizing the
`with_arena` library function of §8.2 with a kernel-level typing
rule rather than a library combinator: the compiler can
specialize allocations into a single bump pointer with a single
deallocation at scope exit, eliminating per-allocation overhead
while remaining type-safe.

The region form composes with the proof-only ghost layer (§6.0,
§6.5): ghost values logically annotate the region without occupying
runtime memory, so a region can carry both runtime data and
ghost invariants linking allocations.

(FX has no apostrophe sigil; region variables are ordinary
lower-identifier kind-`region` parameters, not `'r`-style
lifetimes — see §2.7 disambiguation rule 27.)

### 8.2 Allocation Strategies

FX has no garbage collector.  Every heap allocation has a determined
lifetime visible in the type, and the compiler picks the cheapest
strategy that satisfies it.

```
Strategy                When selected                      Cost
────────────────────    ─────────────────────────────      ──────────────────
Stack                   value does not escape function     zero
Region (bump)           group of values die together       O(1) alloc, O(1) free
Slab (per-type pool)    known compile-time size, escapes   O(1) alloc, O(1) free
Size-classed pool       runtime-determined size             O(1) amortized
Reference counting      explicitly shared, multiple owners  atomic inc/dec
```

The programmer can override the compiler's choice:

```
fn temporary_work<r: region>() : result with Alloc(Region(r));
fn small_buffer() : array(u8, 256) with Alloc(Stack);
fn shared_state() : rc(config) with Alloc(Rc);
```

Platform availability:

```
Platform    Available strategies
────────    ─────────────────────────────────────
x86/ARM     Stack, Region, Slab, Pool, Rc
GPU         Stack, Region
FPGA        Stack only
```

On constrained platforms, strategies that require heap are compile
errors.

### 8.3 The Proved Allocator

The allocator is written in FX.  It bootstraps from raw memory
pages (mmap on hosted systems, a fixed region on embedded targets)
and proves four properties:

Every returned pointer addresses memory that no other live pointer
addresses (no aliasing).  This composes with the linear type system:
the allocator produces `own` pointers and the type system tracks
them from there.

Returned memory is aligned per the type's requirement.

Freed memory can be reused without overlap.  Slab slots are either
in the free list or allocated, never both.

Thread safety.  Each thread has a local cache of slab pages and pool
size classes.  The global pool is accessed under a lock when the
local cache is empty or full.  The correctness proof shows that
every pointer issued by one thread's cache is disjoint from every
pointer issued by any other thread's cache.

The allocator is replaceable.  A user-provided allocator must
satisfy the same interface contract.

### 8.4 Representation Inference

The compiler picks the physical representation of every type based
on what the type system knows.  The programmer writes `repr(C)` or
`repr(packed)` only at FFI boundaries or to override the default.

**Tagged pointer packing.**  On 64-bit systems, the low 3 bits of
aligned pointers are zero and the top 16 bits of user-space
addresses are zero.  The compiler uses these bits for discriminator
tags.  `option(own T)` is one word — `None` is the null pointer.

**Niche optimization.**  When a type has impossible values (a
`nat { x > 0 }` is never zero, a `bits(3)` is never 8), the
compiler uses those values as discriminators for surrounding enums.
`option(nat { x > 0 })` uses zero for `None`.

**Bit packing.**  A record with fields `bits(3)`, `bits(5)`, `bool`,
`bits(7)` occupies 16 bits, not 4 bytes.

**Compressed pointers.**  Pointers into a region are stored as 32-bit
offsets from the region base, addressing 4 GB per region.  The cost
is one add per dereference; the savings are halved cache pressure
for pointer-heavy structures.

**Zero-sized types.**  Phantom types, unit fields, and markers take
zero bytes.

**Struct-of-arrays.**  When the compiler detects field-at-a-time
access patterns (from pipeline operations and dot-shorthand), it
may store a collection of records as parallel arrays of fields.
`users |> map(.name)` on a struct-of-arrays layout streams through
just the name array.  The programmer can override with `repr(AoS)`
or `repr(SoA)`.

**Hot/cold splitting.**  If a struct has frequently-accessed fields
and rarely-accessed fields, the compiler may split it into an inline
hot part and a pointer-chased cold part.

### 8.5 Memory Layout Control

Explicit layout annotations for FFI and wire formats:

```
type ip_header repr(C, packed, big_endian) {
  version: u4;
  ihl: u4;
  tos: u8;
  total_len: u16;
};
```

Layout modes:

```
repr(Native)       compiler chooses (default)
repr(C)            C-compatible layout
repr(packed)       no padding between fields
repr(aligned(n))   n-byte alignment
repr(big_endian)   multi-byte fields big-endian
repr(transparent)  same layout as the wrapped type
```


## 9. Effects

### 9.1 Effect Annotations

No effect annotation means `Tot` — pure and terminating.  Effects
are declared with `with` after the return type:

```
fn add(a: i64, b: i64) : i64 = a + b;                   // Tot
fn read(path: string) : string with IO = ...;            // IO
fn send(msg: packet) : unit with IO, Async = ...;        // IO + Async
fn loop() : never with Div = ...;                        // may diverge
```

Effects must be declared on all `pub fn` signatures.  The compiler
verifies that the body's effects are a subset of the declared
effects.  If a function body performs IO and the signature omits
`with IO`, that is a compile error — effects are never inferred
upward into the signature.

`rec` functions without a `decreases` clause must declare `with Div`.

Argument evaluation order is left-to-right, always.  `f(g(), h())`
evaluates `g()` then `h()` then calls `f`.

### 9.2 Effect Variables

Effect variables allow polymorphism over effects:

```
fn map<a: type, b: type, eff: effect>(f: a -> b with eff, xs: list(a)) : list(b) with eff
  decreases xs;
= match xs;
    [] => [];
    [h, ...t] => [f(h), ...map(f, t)];
  end match;
```

Every call to an effect-polymorphic function names its effect
argument explicitly.  FX does not infer effect variables from
usage.  Omitting an effect argument at a call site is compile
error E043 (missing effect argument):

```
let evens : list(i64) = filter<i64, Tot>(fn(x: i64) => x % 2 == 0, numbers);
let valid : list(i64) = filter<i64, {IO, DB}>(fn(x: i64) => db.check(x), items);
```

Effect row extension: `with eff, IO` means whatever `eff` is,
plus `IO`:

```
fn with_logging<a: type, eff: effect>(label: string, body: unit -> a with eff) : a with eff, IO
begin fn
  log(f"[{label}] starting");
  let result = body();
  log(f"[{label}] done");
  result
end fn;
```

### 9.3 The Effect Lattice

Effects form a bounded join-semilattice under set union:

```
Tot \/ e = e             Tot is the identity
e \/ e = e               idempotent
e1 \/ e2 = e2 \/ e1     commutative
Read <= Write            Write implies Read
```

Effect subtyping: `e1 <= e2` when `e1 \/ e2 = e2`.  A `Tot`
function can be used where `IO` is expected.  An `IO` function
cannot be used where `Tot` is expected.

**Effect row is a set, not a list.**  The comma-separated list in
`with e1, e2, eff, ...` denotes the set `{e1, e2} ∪ eff ∪ ...`.
Order is immaterial: `with IO, Async` and `with Async, IO`
denote identical effect rows.  Duplication collapses by
idempotence: `with IO, IO` is exactly `with IO`.  When an effect
variable `eff: effect` appears in the list, its contents union
with the explicit effects at elaboration time.  The `with` clause
is syntactically a list only for readability; semantically it is
a row-extension operator producing the union.

**`Fail` is unique per row.**  Two explicit `Fail` terms in the
same annotation — `with Fail(E1), Fail(E2)` — is compile error
E045 (see §4.9).  The lattice-level rule `Fail(E1) \/ Fail(E2)
= Fail(E1 | E2)` still applies when composing effects across
call sites, but a single source-level signature must name one
`Fail(T)` with a single error type.  This keeps `catch` arms
unambiguous and matches §4.9's closed-union-error-type rule.

**User-declared subsumption edges.**  An `effect` declaration
may state `subsumes OtherEffect;` to register a subtyping edge:
a value whose effect row contains this effect satisfies any
context expecting `OtherEffect`.  The edge is checked at the
effect declaration site (§9.5) and integrates into the lattice
subsumption check.  Attempting to use effect A where B is
expected without a declared `subsumes` edge (or built-in lattice
edge like `Read <= Write`) is compile error E046 (`effect A does
not satisfy B; no subsumption edge declared`).

### 9.4 Built-In Effects

```
Tot       pure, terminating (default)
Div       may diverge
Ghost     erased at runtime, checked at compile time
Exn       may raise exceptions
IO        general input/output
Alloc     may allocate heap memory
Read      may read from references/state
Write     may write to references/state (implies Read)
Async     may perform async operations
```

Parallelization rules derived from effects:

- `Tot` / `Ghost`: always safe to parallelize.
- `Read`: safe to parallelize (readers do not conflict).
- `Write`: requires exclusive access (ownership ensures this).
- `Alloc`: safe to parallelize (thread-local allocation).
- `IO`: must serialize or use channels.

### 9.5 User-Defined Effects

An effect declaration lists its operations:

```
effect State<s: type>
  fn get() : s;
  fn put(new_state: s) : unit;
end effect;

effect Reader<r: type>
  fn ask() : r;
end effect;

effect Exception<e: type>
  fn throw(err: e) : never;
end effect;

effect FileSystem
  fn read_file(path: string) : result(string, io_error);
  fn write_file(path: string, content: string) : result(unit, io_error);
  fn list_dir(path: string) : result(list(string), io_error);
end effect;
```

**Subsumption edges.**  An effect may declare a `subsumes` edge to
another effect, stating that this effect's capability contains the
other's — a value with this effect in its row satisfies any context
expecting the subsumed effect.  Edges compose: if A subsumes B and
B subsumes C, then A subsumes C.

```
effect Crypto
  fn sign(msg: bytes, key: secret) : signature;
  fn verify(msg: bytes, sig: signature, key: pubkey) : bool;
  subsumes IO;                       // Crypto may perform IO
end effect;

fn audit_log_sign(
  msg: bytes,
  key: secret,
) : signature with Crypto
begin fn
  log(f"signing {hash(msg)}");       // ok: Crypto subsumes IO
  sign(msg, key)
end fn;
```

A single declarative edge is enough — `A subsumes B` is the only
form needed.  There is no separate `degrades_to` inverse form;
the relation is directional by construction (`A subsumes B` is
not the same statement as `B subsumes A`; only one of them can
be declared).  The effect lattice (§9.3) composes user-declared
edges with built-in edges (`Read <= Write`, `Tot` is bottom) to
form the subtyping relation checked at every call site.

An instance declaration can include `subsumes` for a trait-bounded
effect context, though this is rarely needed — the built-in
composition rules cover typical cases.

### 9.6 Effect Handlers

A handler provides the implementation for an effect, removing it
from the type:

```
fn run_state<a: type, s: type, eff: effect>(init: s, body: unit -> a with State(s), eff) : (a, s) with eff
begin fn
  let state : cell(s) = cell(init);
  handle body()
    return x => (x, state.get());
    get(k) => k(state.get());
    put(new_s, k) => begin state.set(new_s); k(()) end;
  end handle
end fn;
```

The handler typing rule:

```
G |- body : A with <E | eff>
for each op_i in E:
  G, args_i, k_i : (ret_i -> B with eff) |- handler_i : B with eff
G |- return_handler : A -> B with eff
-----------------------------------------------------------
G |- handle body return ... op_i ... end handle : B with eff
```

If `body` has effect `<E | eff>` and the handler provides a clause
for every operation of `E`, the result has effect `eff`.  The
handler removes `E` from the effect row.  The continuation `k` in
each operation clause carries the remaining effect `eff` — it
resumes the body with `E` already handled.

The return clause transforms the body's result type `A` into the
handler's result type `B`.  All operation clauses and the return
clause must produce the same type `B` with the same effect `eff`.

**The return clause is optional.**  When omitted, the handler
uses the identity return clause `return x => x`.  This is the
common case for handlers that transform operations without
reshaping the body's return value:

```
// Explicit return clause:
handle body()
  return x => x;
  log(msg, k) => begin println(msg); k(()) end;
end handle

// Equivalent with implicit identity return:
handle body()
  log(msg, k) => begin println(msg); k(()) end;
end handle
```

When the handler needs to transform the result — wrapping it,
pairing with state, aggregating — the explicit `return` clause
supplies the transform.  The `run_state` example above pairs the
result with the final state; `run_all` (§9.7) wraps the result
in a list.

**Nested handlers handle innermost-first.**  When a body is
enclosed in multiple handlers, an effect operation performed in
the body is handled by the innermost lexically-enclosing handler
that provides a clause for that operation's effect.  Operations
of effects not covered by the innermost handler propagate
outward to the next enclosing handler:

```
fn pipeline() : i64 with eff
begin fn
  handle                                            // outer
    handle body()                                   // inner
      get(k) => k(0);                                // inner handles Reader
    end handle
    print(msg, k) => begin log(msg); k(()) end;    // outer handles Log
  end handle
end fn;
```

Inside `body`, a `Reader.get()` call is handled by the inner
handler and never reaches the outer.  A `Log.print(msg)` call is
not covered by the inner handler (which only clauses `get`) and
propagates to the outer, which handles it.  If both handlers
provided clauses for the same operation (e.g., both clauses
`get`), the inner handler runs and the outer never sees the op
unless the inner's continuation re-performs it.  This matches
Koka, Multicore OCaml, Effekt, and Frank.

The handler body's `return` (both the keyword and the handler
return clause) are distinct from a function body's `return`
statement — the parser disambiguates by context.  A handler
return clause appears only inside a `handle ... end handle` form;
a function return statement appears only inside `begin fn ... end
fn`.  They share the keyword because both name "produce the
final value" for their respective construct.

### 9.7 One-Shot and Multi-Shot Continuations

Handler continuations are one-shot (linear) by default.  They may
be called at most once, allowing the compiler to implement them as
direct jumps without heap allocation.

For effects that call the continuation multiple times, mark the
operation `multishot`:

```
effect Choice
  fn choose() : bool with multishot;
end effect;

fn run_all<a: type, eff: effect>(body: unit -> a with Choice, eff) : list(a) with eff
begin fn
  handle body()
    return x => [x];
    choose(k) => k(true) ++ k(false);
  end handle
end fn;
```

Multi-shot continuations require that all captured values are
`@[copy]`.

### 9.8 Generators

Generators are sugar over the `Yield` effect:

```
effect Yield<y: type>
  fn yield(value: y) : unit;
end effect;

fn fibonacci() : unit with Yield(i64), Div
begin fn
  let a : cell(i64) = cell(0);
  let b : cell(i64) = cell(1);
  while true;
    yield(a.get());
    let temp : i64 = a.get();
    a.set(b.get());
    b.set(temp + b.get());
  end while;
  return ();
end fn;

for fib in iterate(fibonacci);
  if fib > 1000; break end if;
  print(f"{fib} ");
end for;
```

### 9.9 Async and Await

`await` and `spawn` are operations of the `Async` effect:

```
fn fetch_data() : string with Async
begin fn
  let response = await(http_get("https://api.example.com"));
  response.body
end fn;
```

Task groups guarantee that all spawned tasks complete before the
group exits:

```
fn parallel_fetch(urls: list(string)) : list(response) with Async
begin fn
  task_group fn(group) =>
    let futures = urls |> map(fn(url) =>
      spawn_in(group, fn() => http_get(url))
    );
    futures |> map(await)
  end task_group
end fn;
```

### 9.10 Platform-Conditional Effects

Not all platforms support all effects:

```
Platform    Available effects
────────    ─────────────────────────────────────────────
x86/ARM     Tot, Div, Ghost, Exn, IO, Alloc, Read, Write, Async
GPU         Tot, Div, Alloc, Read, Write, Async
FPGA        Tot, Alloc(Stack), Read, Write
```

Code targeting constrained platforms that uses unavailable effects
is a compile error.

### 9.11 Coeffects as the Dual to Effects

Effects describe what a computation *does* — operations performed
against the world.  **Coeffects** describe what a computation
*needs from its context* — capabilities the surrounding scope must
provide before the computation can run.  Effects compose
sequentially as a graded monad; coeffects compose as a graded
*comonad* (Petricek-Orchard-Mycroft ICFP 2014, Choudhury-Krishnaswami
ICFP 2020, Gaboardi-Katsumata-Orchard ICFP 2016).

Three FX dimensions are coeffects rather than effects, and the
mode theory (§6.0) treats them under the dual modality
discipline:

  * **Lifetime** (dim 7) — the function's body needs the named
    region to be live; its effect is not "produces a region" but
    "consumes the property that the region exists during the call".
  * **Clock domain** (dim 12) — the body needs to be invoked
    inside a specific clock domain; the surrounding hardware module
    establishes the clock context.
  * **Reentrancy** (dim 19) — `non_reentrant` declares the body
    needs the property "no caller is already inside this function";
    the calling context establishes the absence of self-reference.

These are graded comonadic annotations.  A graded monad type —
written `indexed(e, a)` in spec prose — means "a computation
producing an `a` while performing effects bounded by `e`".  A
graded comonad type — written `coindexed(c, a)` — means "a
computation producing an `a` given a context bounded by `c`".
In arrow form: an effect is `a -> indexed(e, b)`, a coeffect is
`coindexed(c, a) -> b`.  At a function arrow
`coindexed(c, a) -> indexed(e, b)` the FX surface writes the
caller-side requirement (the coeffect side) and the callee-side
performance (the effect side) symmetrically using `with`
annotations.

**Surface unification with effects.**  FX uses a single `with`
clause for both effects and coeffects rather than separate syntax,
matching the unified graded-effect-and-coeffect calculus of
Gaboardi-Katsumata-Orchard.  The compiler distinguishes by
dimension: dim 4 (Effect) is a graded monad, dim 7 / 12 / 19
(Lifetime / Clock / Reentrancy) are graded comonads, and the
typing rules dispatch per dimension via §6.2 and §6.3.

**Composition rules.**  Coeffects compose by **meet** rather than
**join**: a function calling another function whose context
needs are stricter strengthens the caller's needs.  Sequential
composition of two coeffects is the **join of their requirements**
(both must be available), parallel composition is the **meet**
(only the common requirement remains).  This is the dual of the
effect lattice (§9.3) where sequential composition is union and
parallel composition is intersection.

**Why this matters at the kernel level.**  The dual presentation
removes the asymmetry that previously hid Lifetime, Clock, and
Reentrancy under the same Tier S mechanism as Effect.  Under
MTT, effects and coeffects are *adjoint modalities* — the unit
of the graded monad and the counit of the graded comonad relate
them, and the two compositions follow the dual-tier algebra
uniformly.  Consequence: per-mode 2-cell composition (§6.0) sees
effects and coeffects as one structural pattern, and the §6.8
collision catalog covers their interactions without per-pair
enumeration.

The surface-syntax discipline is unchanged.  The reframing is
internal: §6.3 dim 7 / 12 / 19 are now classified as Tier S
graded *comonads* rather than graded monads, and the typing
rules of §6.2 dispatch accordingly.


## 10. Verification

### 10.1 Refinement Types

A refinement type constrains a base type with a predicate:

```
type pos_int = int { x > 0 };
type bounded = nat { x < 256 };
type sorted_list<a: type> = list(a) { is_sorted(x) } where Ord(a);
```

The variable `x` in the refinement refers to the value being
refined.  Refinement predicates are checked at compile time by SMT
when possible and at trust boundaries by generated runtime
validators when not.

**Refinement on any type expression.**  A refinement attaches to
any type expression, not just primitive types.  Parameterized,
applied, and dependent types all support `T { pred }`:

```
list(i64) { length(x) > 0 }
map(k, v) { size(x) <= 256 }
tensor(f32, [batch, seq, dim]) { batch > 0 }
```

The implicit binder remains `x` — the value being refined.  Use
the named form `r: T { pred }` when the outer scope shadows `x`
or when the predicate reads better with an explicit name.

**Dependent return types — inline Pi form.**  For arrow types
whose return refers to a parameter, bind the result explicitly
via named refinement:

```
fn guess_bigger : (x: nat) -> r: nat { r > x };

fn take<a>(n: nat, xs: list(a)) : r: list(a) { length(r) == n }
  pre n <= length(xs);
```

In `(x: T) -> r: U { pred }`, the parameter name `x` is in scope
for the return type, and the refinement's local name `r` refers
to the returned value.  This is FX's surface syntax for
dependent function types (Pi); the kernel translates it to
`Π (x :_r T) → Σ (r :_1 U) × (pred)` per §30.2.  `post r =>` on
named `fn` declarations remains the primary form for
postconditions — the inline form is for function-typed values
and callback signatures where a `post` clause has no attachment
point.

### 10.2 Pre- and Postconditions

`pre` states preconditions on inputs.  `post r =>` states
postconditions — the identifier after `post` explicitly binds the
return value.  `decreases` provides the termination measure.

```
fn binary_search<a: type>(xs: list(a), target: a) : option(nat)
  where Ord(a);
  pre is_sorted(xs);
  post r => match r;
    Some(i) => i < length(xs) and index(xs, i) == target;
    None => not mem(target, xs);
  end match;
```

Multiple `post` clauses are verified independently.  When one
fails, the compiler reports which clause failed:

```
fn insert(t: bst, k: key, v: value) : bst
  post r => is_balanced(r);
  post r => is_sorted(r);
  post r => lookup(r, k) == Some(v);
```

**Two-state references in postconditions: `old(expr)`.**  In a
`post` clause, the identifiers in the parameter list refer to
the **entry-time** values of the parameters; `r` (or whatever
name the `post` clause introduces) refers to the return value.
When a function mutates state through a `ref mut` parameter, the
`post` clause observes the post-state of that reference — and
the programmer needs a way to reference the pre-state.

`old(expr)` is a spec-language built-in that evaluates `expr`
against the entry state of the function.  It is valid **only**
inside `post` and `invariant` clauses and inside `verify` blocks
operating on two-state machines:

```
fn increment(ref mut x: cell(i64)) : unit
  post _ => x.get() == old(x.get()) + 1;

fn push<a: type>(ref mut v: vector(a), item: a) : unit
  post _ => length(v) == old(length(v)) + 1;
  post _ => last(v) == Some(item);
```

`old` is not a keyword — it is a spec-language primitive in the
prelude.  Outside a `post` clause (or inside a `pre` clause, or
in runtime code), `old(expr)` is compile error R003 (`old() is
valid only in two-state specification contexts`).  The compiler
rewrites `old(expr)` to reference a snapshot captured at function
entry; for `ref mut` parameters the snapshot is the borrow's
pre-mutation state.

**Typing rule for `old`.**

```
Γ ⊢ e : T                         // in the function body state
Γ_entry ⊢ old(e) : T              // in two-state spec contexts;
                                   //   refers to Γ_entry variables
```

Ghost-graded; erased at compile time; zero runtime cost.

**Kernel translation.**  `old(expr)` desugars to `load_snapshot(
expr, __entry_state)` in the kernel; `__entry_state` is an
implicit ghost parameter added to every function that has a
`post`, `invariant`, or two-state `ref mut` obligation.  Eiffel
/ Dafny / SPARK semantics.

### 10.3 Verify Blocks

A `verify ... exports` block isolates proof work.  The `exports`
section declares which facts are visible to subsequent code:

```
fn merge_and_verify<a: type>(xs: list(a), ys: list(a)) : list(a)
  where Ord(a);
  pre is_sorted(xs) and is_sorted(ys);
  post r => is_sorted(r);
begin fn
  let result = merge_sorted(xs, ys);

  verify
    hint merge_preserves_sort(xs, ys);
    assert is_sorted(result);
  exports
    is_sorted(result);
  end verify;

  result
end fn;
```

**Exports semantics.**  Each item in the `exports` list must be a
boolean-valued proposition — type `bool`.  Ghost erasure (dim 9
Trust) ensures exports have no runtime cost regardless of
whether the predicate is itself a function call or a direct
expression.  The compiler treats these as
post-conditions of the verify block — facts that hold after the
block and are visible to subsequent proof obligations.  Facts
established *inside* the block (via `assert`, `hint`, or
intermediate lemma applications) but not listed in `exports`
are **scoped to the block**: they do not leak into the
surrounding context.  This matches Dafny's `assert P by { S }`
scoping discipline.

Non-proposition items (arbitrary expressions, bindings) in the
exports list are compile error R004 (`exports must be propositions;
found <type>`).  The verify block is a proof-isolation mechanism,
not a general scoping block; ordinary `begin ... end` groups
values and statements.

### 10.4 Assert and Guided Proofs

`assert P;` asks the compiler to prove `P` from context.
`assert P using lemma(args);` names the lemma to use:

```
assert is_sorted(merge(xs, ys))
  using merge_sorted_preserves_sort(xs, ys);
```

Multiple lemmas:

```
assert is_permutation(xs, result)
  using permutation_transitive(xs, left ++ right, result),
        split_at_permutation(xs, mid);
```

**Tactic form.**  `assert P by clause;` invokes a named tactic
or a hint block.  Named tactics are ordinary stdlib ghost
functions (`ring`, `linarith`, `omega`, `smt(...)`, etc.) —
not a separate DSL:

```
assert 2 * (x + y) == 2*x + 2*y by ring;
assert x <= x + y by linarith using y_nonneg(y);
assert P by smt(solver: z3, theories: [QF_NIA], timeout: 10s);
```

**Hint block form.**  For proofs that need several intermediate
steps, the Dafny-style hint block contains ordinary FX
statements:

```
assert is_sorted(merge(xs, ys)) by begin
  merge_preserves_length(xs, ys);    // lemma call — its post
                                      //   flows into context
  reveal merge;
  assert length(merge(xs, ys)) == length(xs) + length(ys);
end;
```

The block body is ordinary FX code — lemma applications,
nested asserts, `reveal`, calc chains, `let` bindings for
intermediate expressions — restricted at elaboration to ghost
grade and `Tot` effect.  No new tactic vocabulary; FX's own
statement grammar is the hint language.  Mutation, IO, and
runtime control flow inside a hint block are compile error
P007.

Inline `assert` discharges obligations at a specific point in
the function's execution.  For obligations about the final
return value, prefer a trailing `proof ... end proof` block
(§10.17) — the body stays focused on computation while the
post conditions are justified separately.

### 10.5 Calculational Proofs

`calc` blocks chain equational reasoning steps.  Each step
carries an optional `by clause` using the same `by_clause`
form as `assert` (§10.4) — a named tactic or a hint block:

```
calc
  a * (b + c)
  == a * b + a * c    by ring;
  == a * b + c * a    by begin
    comm_mul(a, c);                       // lemma call
  end;
  == c * a + a * b    by ring;
end calc;
```

Steps without a `by` clause must be discharged automatically
by the default SMT context (§10.16).

### 10.6 Sorry and Axiom

`sorry` is a placeholder for an unfinished proof.  It compiles in
development mode and is rejected in release builds.  When
encountered, the compiler outputs structured diagnostic information:

```
sorry at Hard.fx:4:3
  Goal:     is_sorted(sort(xs))
  Context:  xs : list(i64)  [parameter]
  Candidates:
    sort_sorts : forall(xs: list(i64)), is_sorted(sort(xs))  [exact match]
  Suggestion: sort_sorts(xs)
```

`axiom` declares a mathematical assumption.  It compiles in all
modes but is tracked in the trust dimension.  Axioms are for
foundational mathematics, not for code behavior:

```
@[provenance("Mathlib.Logic.FunctionExtensionality")]
axiom function_extensionality<a: type, b: type>(f: a -> b, g: a -> b)
  pre forall(x: a), f(x) == g(x);
  post _ => f == g;
```

**Axiom provenance.**  Every `axiom` declaration should carry
a `@[provenance("source")]` attribute citing the paper,
theorem name, or foundational category the axiom imports.
Missing provenance is warning W002 (`axiom missing
provenance`); release builds emit the warning but do not fail.
Workspace policy (§25.9) can escalate via
`require_axiom_provenance = true` in `policy.fxpolicy`, turning
W002 into a build-breaking error for the subtree.

Provenance strings are audit-aid, not a security guarantee —
they are not machine-verified and a malicious actor could
write any string.  Real safety comes from three composing
mechanisms: trust propagation through the call graph (below),
§25.11 supply-chain diff warning on new axioms at publish
time, and §25.9 workspace signing tying axiom introduction to
an authorized signer.  Provenance is the human-readable record
of which of those authorities vouches for the axiom.

Trust levels propagate as the minimum through the call graph.  A
function that calls anything with `sorry` has trust level `Sorry`.
Release builds require trust level `Verified` on all reachable code.

### 10.7 Proof Diagnostics

`#show` displays the proof state at a program point:

```
merge_sort_correct(left);
merge_sort_correct(right);
#show
// Known: is_sorted(merge_sort(left)), is_sorted(merge_sort(right))
// Goal:  is_sorted(merge_sort(xs))
```

`#plan` generates a proof skeleton from the goal structure:

```
#plan
lemma sort_correct<a: type>(xs: list(a))
  where Ord(a);
  post _ => is_sorted(sort(xs));
= sorry;
```

The compiler analyzes the function structure, decomposes the goal,
searches the lemma database, and outputs a skeleton with `sorry`
at the leaves.

**Proof-state schema.**  `#show`, `#plan`, and the agent-protocol
endpoint `GET /proof-state` (§24.7) return a single canonical
structure:

```
type ProofState = {
  known:      list(string);    // facts in scope at the program point
  goal:       string;          // the obligation to prove
  suggestion: option(string);  // compiler-generated next step, if any
};
```

`#show` prints the structure as text; `#plan` emits a proof
skeleton; `GET /proof-state` returns the same data as JSON.  One
schema, three consumers — agents use the REST endpoint, humans
read the inline text, tooling parses the JSON.

Built-in tactics for `by` clauses:

```
ring        equations in any ring
field       equations in any field
linarith    linear arithmetic over ordered rings
omega       Presburger arithmetic (integers, quantifier-free)
decide      decidable propositions
simp        rewriting with declared lemmas
norm_num    numeric evaluation (1 + 2 = 3)
assumption  close goal from context fact
decide      proof by reflection over decidable propositions
```

**The decide framework.**  For obligations that are *decidable*
in the constructive sense — bit-vector equalities, finite-set
membership, structural equality on `@[copy]` types, finite
quantifications — proof-by-reflection (Boutin TACS 1997, Geuvers-
Wiedijk-Zwanenburg TYPES 2002, de Moura-Ullrich CADE 2021) is
faster, more reliable, and produces certificates the SMT
oracle does not.  The stdlib `Std.Logic` module ships:

```
class Decidable<p: prop>
  fn decide_p() : either(p, not(p));
end class;

// stdlib instances (auto-derived for the decidable fragment)
instance Decidable for Eq(a, b)
  where Eq(t);                       // structural equality on @[copy] t

instance Decidable for member(x, finite_set)
  where Finite(finite_set);          // finite-set membership

instance Decidable for forall(i: nat { i < n }), p(i)
  where Decidable(p(i));             // bounded universal over decidable p
```

The `decide` tactic dispatches to the `Decidable` typeclass
instance for the goal proposition and discharges it
constructively.  For
performance-critical proofs the `native_decide` variant compiles
the decision procedure to native code at elaboration time,
running it once and caching the certificate.  Decidable proofs
are reproducible (no SMT randomness), bit-stable across compiler
revisions, and produce certificates that survive Z3 version
bumps — the SMT periphery (§10.16) is no longer the only path
for refinements that admit a constructive decision procedure.

### 10.8 Trust Boundaries

A trust boundary exists where an unrefined value meets a refined
context: IO output, FFI return, user input, deserialized data.  The
compiler classifies every value by origin:

```
Origin                         Properties proved
────────────────────────       ─────────────────
Literal / construction         full (known at compile time)
Verified function return       full (postcondition proved)
Pattern match branch           full (guard holds)
IO / FFI / deserialization     nothing
```

For decidable refinements at trust boundaries, the compiler
auto-generates runtime validators:

```
fn handle(req: request { 1 <= req.version and req.version <= 3 })
  : response with IO;
// Compiler generates: check version range, return error if invalid
```

Runtime checks exist at exactly two places: trust boundaries (where
unproven data enters the verified world) and external interactions
(where the program talks to unverified systems).  Everywhere else,
the compiler proved it.

### 10.9 Refinement Inference

The compiler automatically proves refinements that follow from
arithmetic, pattern matching, and just-called postconditions:

```
// Automatic:
assert 2 + 3 == 5;                                    // arithmetic
let sorted = sort(xs); assert is_sorted(sorted);       // postcondition
match xs; [] => assert length(xs) == 0; end match;    // pattern

// Manual (needs a lemma name):
assert is_sorted(rev(sort(xs)));    // needs rev_sorted lemma
assert exists x. pred(x);           // needs a witness
```

### 10.10 Compiler Error Structure

Every compiler error follows a fixed structure:

```
error[CODE]: one-line summary at FILE:LINE:COL

  SOURCE_LINE
  ^^^^^^^^^ underline

  Goal:    what the compiler needs
  Have:    what facts are available
  Gap:     what is missing

  Suggestion:
    concrete FX code to fix the problem

  [--explain CODE for full documentation]
```

Error code taxonomy:

```
T0xx    type errors
R0xx    refinement errors (pre/postcondition, decreases, assert)
E0xx    effect errors
M0xx    mode/ownership errors
S0xx    session type errors
I0xx    information flow errors
P0xx    proof errors (timeout, unknown, fuel)
N0xx    precision errors
W0xx    warnings
```

Every suggestion is valid FX code, not a vague hint.

### 10.11 Specification Validation

The compiler validates specifications before attempting proofs:

```
warning: specification may be vacuously true
  fn find(xs, pred) : option(a)
    post r => match r; None => true; ...
  The None case has no constraint.  Function could always return None.

warning: specification is unrealizable
  post r => is_permutation(xs, r) and length(r) > length(xs);
  Contradictory: permutation preserves length.

warning: specification weaker than implementation
  post r => r >= 0;
  Implementation guarantees: r >= 0 and (r == x or r == -x).
```

### 10.12 Proof Stability and Budgets

The compiler tracks verification time per obligation across runs.
Obligations taking more than 80% of the timeout are flagged:

```
warning[W001]: unstable proof at line 34 (4.8s / 5.0s timeout)
```

Budget mode gives best-effort results within a time limit:

```bash
$ fxc verify --budget 30s Module.fx
  [  2.1s] fn merge_sort       ok
  [ 12.8s] lemma perm_trans    ok
  [ 10.2s] fn complex_fn       partial (4/7 obligations)
  [BUDGET] 2/3 fully verified. 1 partial.
```

### 10.13 Incremental Verification

Each `;` is an implicit verification checkpoint.  Each
`verify...exports` block is an explicit one.  When the source is
edited, only checkpoints affected by the edit are re-verified:

```
Re-verifying merge_sort after edit at line 10...
  [1/4] checkpoint line 7   CACHED
  [2/4] checkpoint line 9   RE-VERIFY (0.2s)
  [3/4] verify block 15-20  CACHED
  [4/4] postcondition        CACHED
Total: 0.2s (vs 3.1s full)
```

### 10.14 Additional Proof Tools

Counterexample generation: when a refinement check fails, the
compiler shows a concrete witness from the SMT model:

```
error[R001]: precondition not satisfied
  index(filtered, original_idx)
  Cannot prove: original_idx < length(filtered)
  Counterexample: xs=[1,2,3], pred=fn(x)=>x>1,
    filtered=[2,3] (length 2), original_idx=2
```

Lemma database search:

```bash
$ fxc search "is_sorted(append(_, _))"
  sorted_append : is_sorted(xs) -> is_sorted(ys) -> ... -> is_sorted(append(xs,ys))
```

Proof obligation tree: when a postcondition fails, shows which
branches of the proof tree pass and which fail.

Proof diff: when an edit breaks a previously-passing proof, shows
what changed and why.

Automatic lemma extraction: when Z3 proves the same fact repeatedly,
the compiler suggests extracting it as a named lemma.

Proof minimization: after verification passes, the compiler checks
for redundant hints and suggests removing them.

Specification coverage analysis:

```bash
$ fxc coverage --spec Map.fx
  fn insert: 2/3 properties specified (missing: preserves other keys)
  Overall: 40% specification coverage
```

### 10.15 Body Visibility

By default, a function's body is opaque to the SMT solver.  A
caller's proof obligations see only the callee's signature —
pre/post/effects/modes — as axioms.  The body is used to verify
the function itself, then sealed against downstream proofs.

```
pub fn sort<a>(xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r) and is_permutation(xs, r);
= ... quicksort ...;

pub fn caller(xs: list(i64)) : list(i64)
  post r => is_sorted(r);
= sort(xs);
// caller's proof uses sort's postcondition as an axiom.
// Rewriting sort from quicksort to merge sort invalidates
// nothing downstream — caller never saw the body.
```

This differs from F*, Dafny, Lean, and Coq, which default to
transparent (the prover sees function bodies).  FX's opaque
default is chosen for three reasons:

 1. **Proof stability.**  Rewriting an opaque function's body
    cannot destabilize a caller's proof — the caller never saw
    the body.  Transparent-by-default systems routinely suffer
    downstream proof invalidation from unrelated body edits
    (Mariposa, CMU 2024).

 2. **Cache keys.**  Incremental verification (§10.13) keys on
    callees' signature hashes, not body hashes.  Editing a body
    invalidates that function's own proof only, not its callers'.

 3. **Modular reasoning.**  A module's verification depends only
    on its imports' signatures.  Blast radius is bounded by
    public surface (§28.1), independent of implementation
    complexity.

Two attributes control body visibility and inlining:

```
@[transparent]
fn small(x: i64) : i64 = x + 1;
// Body visible to SMT in callers' proofs.  Use for small pure
// helpers, inductive definitions, and lemma carriers where the
// body IS the specification.

@[no_inline]
fn cold_path(x: i64) : i64 = ... large body ... ;
// Compiler never inlines, even in release.  Use for large
// bodies where inlining would bloat binary size or thrash the
// instruction cache, and for functions that must appear in
// stack traces verbatim (profiling signatures, crash reports).
```

SMT opacity and codegen inlining are orthogonal.  The release
profile inlines aggressively by default; the debug profile
disables all inlining to preserve frame pointers, accurate stack
traces, and step-through debugging.

```
Attribute / profile            SMT sees body   Release inlines   Debug inlines
──────────────────────────     ─────────────   ───────────────   ─────────────
(default)                      no              yes               no
@[transparent]                 yes             yes               no
@[no_inline]                   no              no                no
@[transparent] @[no_inline]    yes             no                no
```

The debug profile sets `inline = false` globally in §25.12 profile
configuration, overriding the release default so every function
boundary survives into the binary.  `@[no_inline]` honors both
profiles — once a function is declared never-inline, it stays
that way across release and debug so stack traces and profiler
signatures are stable across build configurations.

Inside a `verify ... exports` block (§10.3), the `reveal f;`
directive locally unfolds an opaque function for the duration of
that block only.  Facts derived from the unfolded body do not
escape the block unless listed in `exports`:

```
verify
  reveal helper;
  assert helper(x) == x + 1;
exports
  /* body facts do NOT escape; only explicitly exported
     assertions are visible to surrounding code */;
end verify;
```

**`reveal` unfolds exactly one level.**  If `helper` is defined
in terms of `inner_helper`, revealing `helper` makes
`helper`'s body visible but leaves `inner_helper` opaque; calls
to `inner_helper` inside `helper`'s body remain specification-
only.  For deeper reveals, write multiple statements:

```
verify
  reveal outer;
  reveal inner_1;
  reveal inner_2;
  assert ...;
end verify;
```

One level matches Lean 4's `simp only [f]` and Dafny's
`reveal f()`.  FX does not ship a fuel / ifuel mechanism
(F*-style global unfold depth) because each reveal is an
explicit, auditable decision visible in the source — an agent
reading the verify block sees precisely which definitions are
in scope.

The distinction between SMT opacity and codegen inlining matters:
a function can be opaque for verification (spec suffices for
callers' proofs) while still being aggressively inlined for
performance.  The backend optimizer treats all functions as
inlining candidates regardless of SMT visibility.  The two
concerns are independent and resolved by separate attributes.

### 10.16 SMT Context

The compiler discharges refinement obligations, `pre`/`post`
clauses, `decreases` termination, and `assert` statements to an
SMT oracle at elaboration time.  This section states which
theories the oracle operates over so implementers and agents
can predict what will discharge automatically and what needs a
manual hint.

**Default theory set:**

```
QF_UFLIA  uninterpreted functions + linear integer arithmetic
QF_BV     fixed-width bit vectors (§18 hardware, §3.2 bits(n))
QF_NRA    nonlinear real arithmetic (§3.1 frac, §3.8 ratios)
QF_FP     IEEE 754 floating point (§3.11 precision dimension)
+ bounded quantifiers with E-matching triggers
```

**User-defined spec functions** in refinements are axiomatized
by default: the compiler emits the function's declared
signature and `post` clauses as SMT axioms without exposing the
body.  For goals that require body-level reasoning, mark the
definition `@[reflect]`; the compiler then encodes the body
into the SMT context (refinement reflection, Liquid Haskell /
F* style).  Reflection can blow up query size; it is opt-in per
definition.

```
@[reflect]
ghost fn is_sorted<a: type>(xs: list(a)) : bool
  where Ord(a);
= match xs;
    [] => true;
    [_] => true;
    [x, y, ...rest] => x <= y and is_sorted([y, ...rest]);
  end match;
```

**Per-obligation escape hatch.**  When the default context fails
to discharge a specific obligation, a `by smt(...)` tactic call
overrides:

```
assert P by smt(solver: z3, theories: [QF_NIA], timeout: 30s);
```

Arguments are named.  `solver` defaults to `z3`; `cvc5` is
available on targets that ship it.  `theories` extends the
default set for this obligation only.  `timeout` overrides the
§10.12 global budget.

**Solver choice.**  Z3 is the default.  The solver binary path
is declared in workspace config (§25.3); solver version is
recorded in the §10.13 proof cache key so changing Z3 versions
invalidates cached proofs.

**Higher-order ghost state via Iris-grade BI.**  §6.4 declares
"separation logic IS the usage grade" — true for the affine
fragment.  Higher-order ghost state (step-indexed propositions,
named monoid-valued ghosts, labeled invariants) requires labeled
Bunched Implications per Iris (Jung-Krebbers-Birkedal et al. JFP
2018, Liu et al. OOPSLA 2025 quantified underapproximation,
Spies et al. OOPSLA 2025 Nola later-free ghost state).  These
patterns are FX's mechanism for non-trivial concurrent
invariants — "the sum of these counters equals N", "this lock's
guard holds invariant I across all critical sections", "the
liveness of process P implies the liveness of process Q".

The kernel treatment lives in `FX/Kernel/Bi/`: `emp`, `*`, `-*`
(separating implication), named monoid composition, labeled
bunches.  Verification via `verify { ... } exports { ... }`
discharges BI obligations through an Iris-style proof mode.
Decidable BI fragments shortcut to SMT; non-decidable ones
require explicit proof terms.

The §6.4 fractional permission PCM is the leaf instance of this
machinery; the BI module generalizes to any user-defined PCM
(§6.5 Custom PCMs) plus step-indexed predicates for liveness
arguments (§11.18 safety levels live++ and beyond).

### 10.17 Organizing Proof Work

Function bodies that mix computation with detailed proof steps
become hard to read — readers who want to understand the
algorithm have to scan past verification scaffolding.  FX
provides two mechanisms that keep the two concerns visibly
separate.

**Convention: hoist proof chains into lemmas.**  Proof work
that does not reference local execution state should live in a
named lemma, called at the obligation site.  The body stays
focused on computation; the lemma call is a single line that
discharges its declared postconditions into the caller's
context:

```
// Before: verify block inside body
fn binary_search(xs: list(nat), target: nat) : option(nat)
  pre is_sorted(xs);
  post r => ...;
begin fn
  let mid = length(xs) / 2;
  verify
    reveal length;
    assert mid < length(xs) using div_le(length(xs), 2);
    assert is_sorted(take(mid, xs)) using sorted_prefix(xs, mid);
  exports
    mid < length(xs);
    is_sorted(take(mid, xs));
  end verify;
  ...
end fn;

// After: lemma hoisted
lemma bs_mid_bounds(xs: list(nat), mid: nat)
  pre is_sorted(xs) and mid == length(xs) / 2;
  post _ => mid < length(xs) and is_sorted(take(mid, xs));
= sorry;

fn binary_search(xs: list(nat), target: nat) : option(nat)
  pre is_sorted(xs);
  post r => ...;
begin fn
  let mid = length(xs) / 2;
  bs_mid_bounds(xs, mid);          // one line; discharges both facts
  ...
end fn;
```

The lemma's declared `post` flows into the caller's proof
context at the call site — the same mechanism as any function
postcondition.  Match Dafny and F* idiom.  Use this as the
default for proof work that doesn't need to reference the
body's intermediate locals.

**Proof blocks: discharging post conditions after the body.**
Proof work that belongs to the function — but doesn't need to
interleave with computation — attaches to the function via an
optional `proof ... end proof` block placed after the body:

```
fn sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r) and is_permutation(xs, r);
= quicksort(xs)
proof
  assert is_sorted(quicksort(xs))    using quicksort_sorts(xs);
  assert is_permutation(xs, quicksort(xs)) using quicksort_perm(xs);
end proof;
```

Block form is analogous:

```
fn tricky(xs: list(nat)) : list(nat)
  post r => is_sorted(r);
begin fn
  let stage_1 = transform(xs);
  return finalize(stage_1);
end fn
proof
  assert is_sorted(finalize(transform(xs))) using
    transform_preserves_sort,
    finalize_keeps_sort;
end proof;
```

**Semantics.**  The proof block runs in a ghost context after
the function body produces its return value.  In scope:

 * every function parameter at entry state (use `old(p)` for
   pre-mutation state of `ref mut` parameters, plain `p` for
   post-mutation state, §10.2)
 * the return value, bound by whatever identifier the `post`
   clause introduces (typically `r` or `_`; if no `post` binder
   exists, the default name `result` is available)
 * public symbols in scope of the enclosing module

Not in scope: local `let` bindings from inside the body.  They
go out of scope at return; if the proof needs to reference
intermediate values, compute them at the module level, name
them via auxiliary lemmas, or keep the proof inline via
`assert` / `verify` blocks inside the body.

**Statements allowed in a proof block:**

```
assert_stmt                (§10.4 — all forms)
lemma_call ";"             (discharges the lemma's post into context)
REVEAL lower_ident ";"     (one-level unfold per §10.15)
verify_expr ";"            (nested verify...exports for structure)
calc_expr ";"              (calculational proof, §10.5)
```

All statements must have effect `Tot` and ghost grade.
Mutation, IO, runtime control flow (`if`, `for`, `while`,
`return`, `break`, `continue`), and side-effecting function
calls are compile error P007 (`proof block requires ghost/Tot
content`).

**Erasure.**  Proof blocks erase at codegen (§1.5).  The binary
contains no trace of them.  Edits to a proof block invalidate
only that function's proof cache entry (§10.13) — the signature
is unchanged, so downstream callers stay CACHED.

**Interaction with inline `assert`.**  Inline asserts inside
the body discharge obligations at a specific point in the
body's execution and are the right choice when P depends on
local intermediate state.  Proof blocks discharge obligations
about the body's final state.  Use both together: inline for
facts about intermediate execution, proof block for facts
about the return value or entry-state parameters.  The two
compose without conflict — obligations that remain open after
the body are sent to the proof block's context.


## 11. Protocols and Concurrency

### 11.1 Session Types

A session type describes a communication protocol as a type.  Each
step in the protocol is a send, receive, branch, or recursive call:

```
type request_protocol = session
  send(request: http_request);
  receive(response: http_response);
end session;

type auth_protocol = session
  send(credentials: (string, string));
  branch
    success => receive(token: auth_token); end;
    failure => receive(reason: string); end;
  end branch;
end session;

type stream_protocol<a: type> = session rec Loop;
  branch
    next => receive(item: a); Loop;
    done => end;
  end branch;
end session;
```

### 11.2 Duality

Every session type has a dual.  If one endpoint follows `S`, the
other follows `dual(S)`:

```
dual(send(T).S)     = receive(T).dual(S)
dual(receive(T).S)  = send(T).dual(S)
dual(S1 + S2)       = dual(S1) & dual(S2)     (select <-> branch)
dual(S1 & S2)       = dual(S1) + dual(S2)     (branch <-> select)
dual(rec X. S)      = rec X. dual(S)
dual(end)           = end
```

Creating a channel produces a pair with dual types:

```
let (client_ch, server_ch) = new_channel(request_protocol);
// client_ch : channel(request_protocol)
// server_ch : channel(dual(request_protocol))
```

### 11.3 Using Channels

```
fn make_request(ch: channel(request_protocol), req: http_request)
  : http_response with Async
begin fn
  send(ch, request: req);
  receive(ch)
end fn;

fn handle_request(ch: channel(dual(request_protocol)))
  : unit with Async, IO
begin fn
  let req = receive(ch);
  let resp = process(req);
  send(ch, response: resp);
end fn;
```

Channels are linear.  Sending consumes the send permission and
advances the channel to the next protocol state.  Using a channel
after the protocol is complete is a compile error.

**Per-dimension grade flow at session events.**  Send and receive
update the channel's grade vector dimension-by-dimension, not just
the Protocol typestate.  This single rule subsumes what manual
realizations realize through three separate payload markers
(Transferable, Borrowed, Returned) and ~600 lines of template
machinery.

```
G-Session-Send:

  G ⊢_p_v v : T
  G, ch :_p_ch channel(send(payload: T); K) ⊢ ch : channel(...)
  ─────────────────────────────────────────────────────────────────
  G, ch :_p_ch' channel(K) ⊢ send(ch, payload: v) : unit
                            @ Async + Fail(Cancelled)

  where, for each dimension d in {1..24}:

    p_ch'.d = transition_d(p_ch.d, send_event(p_v.d))

  per tier:

    Tier S commutative semiring:
        p_ch'.d = p_ch.d ⊞_d p_v.d
        (parallel composition: the channel acquires the
         payload's grade)

    Tier L lattice:
        p_ch'.d = p_ch.d ⊔_d p_v.d
        if valid_d(p_ch.d ⊔_d p_v.d) = true
        otherwise compile error CD001 (or analogous)

    Tier T typestate (dim 6 Protocol):
        p_ch'.6 = K
        (advance per the protocol's typestate)

    Tier F (dim 1 Type, dim 2 Refinement):
        no grade-vector update; payload type is substituted into K

    Tier V (dim 21 Version):
        p_ch'.21 = adapter_resolve(p_ch.21, p_v.21)
        if no adapter, compile error V001
```

**G-Session-Recv** is the dual rule: the receiver's grade vector
updates by the same per-dimension composition, except that for
the Usage dimension (dim 3) the composition is *subtraction* of
the consumed permission from the sender's vector and *addition*
to the receiver's vector — the CSL frame rule restated for
session boundaries.  Soundness preserves the association
invariant of Hou-Yoshida-Kuhn 2024 (Theorem 5.8) and is
mechanized in the smpst-sr-smer Coq port (ITP 2025) lifted to
Lean 4.

The rule subsumes three payload patterns that other systems
realize manually:

  * **Transferable**: payload at Usage grade 1; sender loses
    Frac(1), receiver gains Frac(1).  CSL ownership transfer.
  * **Borrowed**: payload at Usage grade ω with a Lifetime grade
    scoped to the next session step.  Sender retains, receiver
    gains a step-scoped read view.
  * **Returned**: dual of Transferable on a previously-borrowed
    payload; receiver gains the full permission back.

All three are particular configurations of `p_v` flowing through
G-Session-Send; no new types are needed.

**Cancellation.**  The stdlib primitive
`cancel(ch) : unit with Fail(Cancelled)` terminates a session
channel mid-protocol, propagating a `Cancelled` message to the
peer per the session type.  It is the canonical cleanup used with
`defer`/`errdefer` (§7.11) to satisfy the linear-cleanup-on-fail
rule (M011) when a function owning an in-flight channel may abort:

```
let ch : channel(request_protocol) = new_client_channel(req_addr);
errdefer cancel(ch);
send(ch, request: req);
let resp : http_response = receive(ch);
return resp;
// normal path: channel complete, cancel never runs
// fail path: cancel propagates Cancelled to peer, consuming ch
```

Semantics follow Exceptional GV (Fowler, Lindley, Morris, Decova,
POPL 2019): the peer observes a typed `Cancelled` message at the
earliest point the session type permits, and both endpoints are
consumed linearly.  No silent channel abandonment — §6.8's I004
and M011 rules together ensure every linear channel has a named
termination path on every abort.

### 11.3.1 Replay-Ordering Refinement on Async Sessions

Asynchronous sessions admit nondeterministic event interleaving
— gradient arrivals from peer workers, spot evictions, channel
reconnects.  For bit-exact reproducibility (replay debugging,
crash recovery, deterministic distributed training) the channel
type carries a *replay tag* that names a content-addressed
ordering log:

```
type async_grad_protocol<replay: replay_tag> = session
  rec Loop;
    receive(grad: stale(gradient_payload, tau),
            ord:  ordering_event(replay));
    branch
      admit  => commit(grad, replay.record(ord)); Loop;
      reject => Loop;
    end branch;
  end session;
```

The `ordering_event(replay)` payload carries a content-addressed
event identifier (step, source, vector clock per dim 7 Lifetime,
staleness tag per dim 22, event kind, content hash) that is
appended to the named replay log.  The session-typed contract
guarantees that the recorded event sequence — together with the
seed — reproduces the channel's behavior bit-exactly on a future
run.

**Per-dimension assignment.**  The replay tag lives in dim 8
Provenance.  The channel's Provenance grade evolves per
Send/Recv:

```
send/receive an OrderingEvent e:
    p_ch'.8 = p_ch.8 ⊕ Provenance(replay_log_id, hash(e))
```

The lattice is the standard provenance lattice extended with
named content-addressed log identifiers.  Replay reads events in
their recorded total order; the read is a typestate advance on a
separate replay-state dimension that lives inside the runtime,
not the kernel.

**Composition with Staleness.**  When the replayable channel
carries a `stale(t, tau)` payload, the grade vector composes per
G-Session-Send: the channel acquires both the staleness grade
and the provenance update in one event.  The combined invariant
is the ASGD admission gate
`eta * lambda_max(h) * tau <= critical` discharged via §6.7
dependent-grade SMT plus replay correctness.

**Soundness.**  The replay-extended preservation theorem
guarantees that for every well-typed program P with replay log
L, replaying P with L reproduces the trajectory of P
bit-exactly.

### 11.4 Branching and Selection

The branching side offers alternatives.  The selecting side picks one:

```
fn login_client(ch: channel(auth_protocol), user: string, pass: string)
  : result(auth_token, string) with Async
begin fn
  send(ch, credentials: (user, pass));
  match receive_branch(ch);
    success => Ok(receive(ch));
    failure => Err(receive(ch));
  end match
end fn;

fn login_server(ch: channel(dual(auth_protocol)))
  : unit with Async, IO
begin fn
  let (user, pass) = receive(ch);
  if verify_credentials(user, pass);
    select(ch, success);
    send(ch, token: generate_token(user));
  else
    select(ch, failure);
    send(ch, reason: "invalid credentials");
  end if
end fn;
```

### 11.5 Multiparty Sessions

Protocols with more than two participants use global session types.
Each participant sees a projected view:

```
type auction = global_session
  Bidder -> Auctioneer : bid(amount: i64);
  Auctioneer -> Bidder : result(won: bool);
  Auctioneer -> Observer : log(entry: string);
end global_session;
```

**Census polymorphism.**  When the role count is itself a
parameter (collective operations, distributed consensus, batched
broadcasts), the `global_session` declaration takes a kind-`nat`
role-count parameter and the body is implicitly quantified over
the role index variable:

```
global_session collective<n: nat>
  Worker[i] -> Coordinator : update(grad: gradient) for i in 0..n;
  Coordinator -> Worker[i] : aggregate(weights: weights) for i in 0..n;
end global_session;
```

The census-polymorphic projection theorem (Bates-Kashiwa-Jafri-
Shen-Kuper-Near PLDI 2025) guarantees that every well-formed
parametric global type has a uniform per-role projection that
type-checks for any concrete `n >= 1`.  Multiply-located values
(values held at a set of roles) participate in independent
linearity checks per role; the conclave construction handles
conditionals whose guards are located only at a subset.

### 11.6 Ownership Through Channels

Sending an owned value transfers ownership to the receiver:

```
fn send_buffer(ch: channel(send(buf: buffer); end), data: buffer)
  : unit
begin fn
  send(ch, buf: data);
  // data consumed — ownership transferred through channel
end fn;
```

### 11.7 Task Groups

Task groups guarantee that all spawned tasks complete before the
group exits.  No orphan tasks, no dangling futures:

```
fn parallel_process(items: list(work_item)) : list(result) with Async
begin fn
  task_group fn(group) =>
    let futures = items |> map(fn(item) =>
      spawn_in(group, fn() => process(item))
    );
    futures |> map(await)
  end task_group
end fn;
```

### 11.8 Parallel Map

Pure functions can be parallelized automatically.  The effect system
proves safety:

```
fn parallel_map<a: type, b: type>(f: a -> b, xs: list(a)) : list(b) with Async
begin fn
  task_group fn(group) =>
    xs |> map(fn(x) => spawn_in(group, fn() => f(x)))
       |> map(await)
  end task_group
end fn;
```

The type of `f` is `a -> b` — no effects, pure.  Parallel execution
is indistinguishable from sequential execution because `f` has no
side effects.

The source type determines parallelism.  `.par()` converts a list
to a parallel source:

```
let result = items.par() |> map(transform) |> filter(.valid) |> sum();
// compiler verifies: transform and .valid are Tot
```

### 11.9 Select

Wait on multiple channels simultaneously:

```
fn router(ch1: receiver(request), ch2: receiver(request), done: receiver(unit))
  : unit with Async
begin fn
  while true;
    select
      msg from ch1 => handle_request(msg);
      msg from ch2 => handle_request(msg);
      _ from done => break;
      timeout 5000 => log("idle");
    end select;
  end while
end fn;
```

### 11.10 Memory Model

FX has only one source of shared mutable memory: the atomic types.
Every other binding is either linear (exclusive ownership per §7)
or shared-immutable (`ref T` holds no writable permission).  This
design collapses the memory-model question to one sub-question:
what does a concurrent access to `atomic<T>` observe?

The answer is defined operationally by the per-architecture emit
tables of §20.5.  The source types and orderings below are chosen
so that the compiler can always pick a correct instruction sequence
from those tables on every supported target.

**Atomic types.**

```
atomic<T>         where T : @[copy] and sizeof(T) ∈ {1, 2, 4, 8}
                  single-word atomic; portable across all targets;
                  default ordering SeqCst.

atomic_wide<T>    where T : @[copy] and sizeof(T) = 16 and alignof(T) = 16
                  double-word atomic; requires hardware support
                  (x86-64 CMPXCHG16B or arm64 CASP); compile error
                  on targets without double-word atomics.

seqlock<T>        where T : @[copy]
                  arbitrary-size shared state via version-counter
                  protocol; portable across all targets; reads may
                  retry under contention; writes require exclusive
                  access (ref mut self).

atomic_counter<T> where T : @[copy] and T is an integer type
                  relaxed-by-design counter for statistics, flags,
                  and approximate counts; compiles to unfenced
                  loads/stores on every target; only supports
                  load / fetch_add / fetch_sub; no Ord parameter.
```

**Operations on atomic<T>.**

```
load(@Ord) : T                            read current value
store(@Ord, new_value: T) : unit          write new value
swap(@Ord, new_value: T) : T              write and return old
fetch_add(@Ord, delta: T) : T             add and return old (integer T)
fetch_sub(@Ord, delta: T) : T             sub and return old (integer T)
fetch_and(@Ord, mask: T) : T              and and return old (integer T)
fetch_or(@Ord, mask: T) : T               or and return old (integer T)
fetch_xor(@Ord, mask: T) : T              xor and return old (integer T)
cas(@Ord, expected: T, desired: T)        compare-and-swap;
      : (T, bool)                          (new_val, succeeded)
cas_weak(@Ord, expected: T, desired: T)   may spuriously fail on
      : (T, bool)                          LL/SC targets; caller retries
```

Every method takes an ordering annotation; default is `@SeqCst`
when the annotation is omitted.

**Ordering annotations.**

```
@Relaxed    no ordering; value only guaranteed to be a value that
            was written by some thread at some point
@Acquire    this load orders subsequent accesses after it (load only)
@Release    this store orders prior accesses before it (store only)
@AcqRel     combined (RMW only)
@SeqCst     sequential consistency; participates in a total order
            with every other @SeqCst operation in the program
```

The constraint on which orderings are valid per operation:

```
load: @Relaxed, @Acquire, @SeqCst
store: @Relaxed, @Release, @SeqCst
RMW (swap, fetch_*, cas): @Relaxed, @Acquire, @Release, @AcqRel, @SeqCst
```

Using an invalid combination (e.g., `load(@Release)`) is compile
error T053 (`invalid ordering for operation`).

**Fence.**

```
fence(@Ord)    process-wide memory barrier
               @Acquire, @Release, @AcqRel, @SeqCst
```

A fence with no associated data operation; used for protocols that
establish ordering without a specific atomic load/store (rare).

**Default ordering is sequential consistency.**

`atomic_cell.load()` without an ordering argument is
`atomic_cell.load(@SeqCst)`.  This matches Java `volatile`, Go
atomic, and Rust's default for portable correctness.  On x86-64,
SeqCst loads are a single MOV; on ARM64, a single LDAR; on RV64,
three instructions.  Weaker orderings are a performance knob, not
a correctness requirement.

**Source-level DRF-SC.**

Because the only shared mutable state is `atomic<T>` /
`atomic_wide<T>` / `atomic_counter<T>` / `seqlock<T>`, the
source-level semantics is straightforward: sequential consistency
on every atomic access, under the usual interleaving semantics of
threads.  The full source semantics is:

 1. Non-atomic reads and writes are ordered by program order within
    a thread.  Linearity (§7) ensures no two threads can
    simultaneously access a non-atomic binding.
 2. `@SeqCst` atomic operations participate in a single total order
    consistent with program order on each thread.
 3. `@Acquire` and `@Release` operations establish happens-before
    edges per the standard release-consistency rules.
 4. `@Relaxed` operations guarantee only that each access observes
    a value that was written to that location by some earlier
    write (per-location coherence), inheriting the hardware's
    no-thin-air property (§20.5).

**Theorem (DRF-reject).** Every well-typed FX program is free of
data races on non-atomic memory.  Proof sketch: a race requires
two concurrent accesses to the same memory with at least one
write.  Linearity (§7) forbids two threads from holding `own T`
or `ref mut T` to the same memory simultaneously.  `ref T` is
read-only, so concurrent reads don't race.  The only multi-writer
or writer+reader case is `atomic<T>` and relatives, where the
operation is itself the synchronization.  Therefore no race can
arise outside the atomic operations.

**Example — publish-subscribe with SeqCst default.**

```
fn publisher(data: atomic<i64>, flag: atomic<bool>) : unit
begin fn
  data.store(42);            // @SeqCst default
  flag.store(true);          // @SeqCst default
  return ();
end fn;

fn subscriber(flag: atomic<bool>, data: atomic<i64>) : option(i64)
= if flag.load();            // @SeqCst default
    Some(data.load())
  else
    None
  end if;
```

This works correctly on all targets.  The compiler may downgrade
the stores to Release and the loads to Acquire via §21.2 auto-sync
inference, since the pattern matches the standard publish-subscribe
idiom — but the source is already correct.

**Example — relaxed counter for statistics.**

```
fn bump_request_count(ctr: atomic_counter<u64>) : unit
begin fn
  ctr.fetch_add(1);          // relaxed; no ordering, no fence
  return ();
end fn;
```

`atomic_counter<T>` is sugar for `atomic<T>` operations pinned to
`@Relaxed`; the compiler emits plain LOCK XADD on x86, LDADD on
arm64, AMOADD on rv64 — no fence.  Use when the counter is only
read for reporting, not for control flow.

**What about the old MemoryOrder effect?**

Earlier drafts of this section used `with MemoryOrder(data: Release,
flag: Release)` as an effect annotation.  That syntax is removed in
favor of per-operation @Ord arguments, which are more local,
composable with pipelines, and match the operational semantics
(orderings are per-access, not per-function).  See the lowering in
§20.5 for how each @Ord maps to instructions.

### 11.11 Deadlock Freedom

Session types with priority annotations guarantee deadlock freedom.
The compiler rejects programs that wait on a lower-priority channel
while holding a higher-priority one:

```
type two_channel = session
  @[priority(1)] send(data: buffer);
  @[priority(2)] receive(ack: bool);
end session;
```

### 11.12 Pipeline Execution Modes

The same pipeline syntax works across different execution modes.
The source type determines how the pipeline executes:

```
Source type        Mode        Execution
─────────────     ─────────   ────────────────────────────
list(T)           eager       each step executes immediately
Query(T)          lazy        builds plan, execute() runs it
Stream(T)         streaming   one element at a time, backpressure
list(T).par()     parallel    distributes across cores (requires Tot)
tensor(T).gpu()   GPU         compiled to GPU kernel
```

**Eager** — in-memory, immediate execution:

```
let result = items |> filter(.active) |> map(.score) |> sum();
// one fused pass, no intermediate lists, SIMD where possible
```

Pipeline fusion: adjacent `map`, `filter`, `map` operations fuse
into a single pass with no intermediate allocations.  Linear types
prove the intermediates are consumed once, making fusion safe.

**Lazy** — deferred execution with optimizable plan:

```
let plan = db.table("sales")
  |> filter(.amount > 1000 and .region == "EU")
  |> map(.customer_name)
  |> sort_by(.customer_name)
  |> take(100);
// plan : Query(string) — nothing executed yet

let result = plan.execute();
// optimizer may generate:
//   SELECT customer_name FROM sales
//   WHERE amount > 1000 AND region = 'EU'
//   ORDER BY customer_name LIMIT 100
```

The optimizer rewrites the plan before execution: predicate
pushdown, projection pushdown, join reordering.

**Streaming** — one element at a time with backpressure:

```
let processed = event_source
  |> filter(.kind == Click)
  |> buffer(1000, overflow: block)
  |> map(.transform)
  |> window(1.minute)
  |> aggregate(count);
```

Overflow strategies for bounded buffers:

```
buffer(n, overflow: block)          producer waits when full
buffer(n, overflow: drop_newest)    discard newest on overflow
buffer(n, overflow: drop_oldest)    discard oldest on overflow
buffer(n, overflow: spill(path))    write to disk when full
buffer(n, overflow: error)          return Err when full
```

**GPU** — from source type:

```
let result = gpu_data |> map(.value * weight + bias) |> reduce(add);
// compiled to GPU kernel; requires numeric types, no IO
```

**Distributed** — partitioned across nodes:

```
let counts = documents
  |> flat_map(tokenize)
  |> group_by_key()
  |> reduce_by_key(add);
// MapReduce execution; contracts ensure serialization at shuffle
```

### 11.13 Design choices

The session-type literature ranges over five orthogonal
questions, and a published result fixes an answer to each.
FX's answers are stated here so later subsections can cite
them by name and the transfer from theory to language is
explicit.

**Participants.**  FX supports sessions with any fixed
number of participants.  Binary sessions (two endpoints,
dual types) are adequate for request-response channels and
one-to-one message queues, but most protocols that arise in
practice — collective operations, distributed consensus,
coordinated lifecycle events — are genuinely N-party.  The
multiparty discipline follows Honda-Yoshida-Carbone 2008
(Honda-JACM16 for the revision).  Roles enter the grammar
as kind-`role` parameters on the session declaration and
carry through to projection (§11.16).

**Channel semantics.**  Sends enqueue into a buffered
channel and return control to the sender; receives dequeue
and may block when the queue is empty.  Every channel in FX
carries a compile-time capacity.  This matters for two
reasons.  First, every reduction rule that moves messages
between the sender's local type and the queue is finite —
the queue type σ has bounded length (§11.15), and balanced+
well-formedness (PMY25 Def 6.1) is guaranteed by
construction rather than checked at each site.  Second,
subtyping on bounded buffers is decidable for the
properties FX cares about; subtyping on unbounded buffers
is not (Lange-Yoshida 2017; Bravetti-Carbone-Zavattaro
2018).

**Specification style.**  Some protocols have a natural
global description — all participants agree on the ordering
of events, and the specification reads left-to-right as a
sequence of message exchanges.  Others do not, either
because there are only two endpoints and duality (§11.2) is
all the structure required, or because no single role knows
the full sequence in advance.  FX admits both.  A session
declared with `global_session<…>` is projected per role at
elaboration; a session declared with `session` and dual
endpoints is checked locally without projection.

**Failure model.**  Every session is crash-stop.
Participants may die at any point, and surviving participants
detect the failure at a typed protocol position and handle
it in a named crash branch.  Byzantine failures — a
participant lying about its protocol state — are out of
scope; authentication is the job of §14 contracts together
with the underlying transport's cryptographic layer.  The
rules follow BSYZ22 for the synchronous case and BHYZ23 for
the asynchronous unavailable-queue extension.  Every
session declaration names a reliability set, and every
`offer` receiving from a role outside that set carries a
mandatory `Crash<p>` branch (§11.21).

**Decidability.**  Precise asynchronous subtyping is
undecidable in general.  FX accepts a bounded-depth
approximation with default depth 64, overridable per
declaration via `@[subtype_depth(N)]`.  Every relation the
compiler accepts is sound; some sound relations the bounded
check cannot resolve get conservatively rejected.  An
engineer hitting a false rejection either widens the depth,
falls back to Gay-Hole synchronous subtyping (§11.19), or
restructures the protocol.  The bounded decision procedure
follows Cutner-Yoshida-Vassor 2022.

The intersection of these five choices — multiparty,
asynchronous with bounded buffers, mixed top-down and
bottom-up, crash-stop, decidable with a depth bound — is
the cell covered by PMY25 (async MPST with precise
subtyping), BHYZ23 (async crash-stop), GPPSY23 (precise
async subtyping via SISO decomposition), HYK24 (the
association invariant), SY19 (parametric safety), and
Gay-Hole 2005 (synchronous subtyping).  Every theorem from
those sources transfers to FX modulo the frontier items of
§11.26.

### 11.14 Well-formedness

A session type is well-formed when three syntactic
conditions hold, all decidable at compile time.  Violation
is error S001.

Recursion must be guarded.  Every `continue` appears
syntactically inside a `loop`, and the body of any `loop`
makes observable progress — that is, the spine from loop
entry to a `continue` passes through at least one send,
receive, select, offer, or end.  A bare `continue` at the
top level is rejected; so is a loop whose body is
immediately a `continue` with no intervening event.  The
discipline is Coppo-Dezani guardedness (§3.5) lifted to
sessions and enforced by the kernel's Coind-ν check
(Appendix H.5) at translation time (§11.24).

Labels in every `select`, `offer`, and `branch` block are
pairwise distinct.  Two branches with the same label in the
same choice are rejected at S002.

The en-route message count between every sender-receiver
pair is bounded — this is balanced+ well-formedness per
PMY25 Def 6.1.  Because every channel in FX carries a
compile-time capacity (§11.15), balanced+ holds by
construction for any single declared channel.  Violations
can arise only when two independently well-formed
sub-protocols are composed (§11.22) and their queue
disciplines fail to mesh; the compiler re-verifies balanced+
at every composition site.

Duality preserves well-formedness.  The equivalence of the
first two conditions under the dual operation is structural
(send ↔ recv, select ↔ offer do not change guardedness or
label distinctness); balanced+ is preserved because dual
swaps sender-receiver pairs without changing their queue
disciplines.  The Lean-level proof lives in
`FX/Derived/Session/Binary.lean`.

### 11.15 Asynchronous semantics

A synchronous session rendezvous at every event: the sender
blocks until the receiver consumes.  FX's channels do not
work that way.  A send enqueues into a buffered channel and
returns to the sender immediately; a receive dequeues and
blocks only when the queue is empty.  The typing discipline
needs three additions to handle the buffer cleanly.

First, the buffer itself carries a type.  The queue type σ
is a finite right-appended sequence of pending messages,
each tagged with its sender, recipient, label, and payload
type:

```
σ ::= ε
    | σ · (p → q, m(P))
```

A queue type is bounded when the length has a compile-time
upper bound.  Every channel in FX declares a capacity when
it is created, so every queue type that appears in typing
contexts is bounded.  An attempt to declare an unbounded
channel is compile error S003.

Second, the typing context carries per-channel queues
alongside per-participant local types:

```
Γ ::= Γ, (s[p] : T)          local type for role p in session s
    | Γ, σ[p, q]             queue type for the p→q channel in s
    | ∅
```

This separation is what makes asynchrony non-blocking at
the type level.  A send event reduces Γ in two places: it
advances p's local type past the `Send<…>` constructor, and
it appends the payload to σ[p, q].  The matching receive
event, when it eventually fires, advances q's local type
past the `Recv<…>` and dequeues the head of σ[p, q].  The
two halves of a communication no longer have to occur at
the same reduction step.

Third, the global-type level needs a representation for
"committed but not yet consumed."  The en-route transmission
`p ⇝_m q : {m_i(P_i) . G_i}` (PMY25 §3) models exactly this:
p has sent m, the message is in transit, and the global
state cannot advance further along the static G until q
receives.  En-route transmissions appear only in runtime
global types, never in the surface `global_session<…>`
declaration.  When q receives, the en-route node resolves,
and G_i becomes the new global state.  PMY25 Thm 12
establishes that runtime global types with en-route
transmissions preserve association (§11.17) over the
corresponding static G's reduction.

The well-formedness condition for this machinery is
balanced+ (PMY25 Def 6.1): for every reachable runtime
state and every pair (p, q), the en-route count between
them is bounded by a finite number.  Balanced+ is strictly
stronger than the classical balanced condition (which
bounds active participants per reachable state), and it is
the invariant that makes precise async subtyping sound.  In
FX balanced+ is not a separate check: the capacity declared
at channel creation bounds the en-route count directly, so
any well-formed session declaration is balanced+ by
construction.  Composition across protocols can still
produce ill-formed queue arrangements, and the compiler
re-verifies balanced+ at every composition site (§11.22).

Bounded buffers are load-bearing for decidability.  With
unbounded queues, async subtyping is undecidable in general
(Lange-Yoshida 2017).  With bounded buffers, subtyping
queries become model-checking problems on finite-state
labeled transition systems, and the bounded-depth
approximation of §11.20 stays sound.

### 11.16 Multiparty — global types and projection

Section §11.5 sketched the multiparty case; this section
gives the full global-type grammar and the projection rules
from Honda-Yoshida-Carbone 2008 (revised Honda-JACM16),
with the merge operation refined per HYK24.  The form is

```
G ::= end
    | p → q : { m_i(P_i) . G_i  |  i ∈ I }
    | μt . G
    | t
    | Stop(p)
    | p → q : crash . G
```

The transmission node `p → q : {m_1(P_1) . G_1, m_2(P_2) .
G_2}` reads "p sends q a message with label m_1 carrying
payload P_1 and the protocol continues as G_1, or p sends
m_2 with P_2 and continues as G_2."  The choice is local to
p; q and any other roles discover which branch was taken by
receiving the label.  `Stop(p)` is a runtime marker
indicating that p has crashed, and the crash-detection node
`p → q : crash . G` handles q's observation of that crash.

Projection extracts the local type for each role.  The
rules are

```
end ↾ p = end

(p → q : { m_i(P_i) . G_i }) ↾ p
  = select<Branch<m_i, send<P_i, G_i ↾ p>>…>

(p → q : { m_i(P_i) . G_i }) ↾ q
  = offer<Branch<m_i, recv<P_i, G_i ↾ q>>…>

(p → q : { m_i(P_i) . G_i }) ↾ r      (r ≠ p, q)
  = merge{G_i ↾ r : i ∈ I}

(μt.G) ↾ p = loop<G ↾ p>
t ↾ p = continue

Stop(p) ↾ p = Stop
Stop(p) ↾ q (q ≠ p) continues, possibly with crash branches
```

The merge operation (Honda-JACM16 Def 3.3) handles the case
where the projecting role is neither sender nor receiver at
a choice point.  Plain merging requires the branches to
project identically: the third party cannot observe the
choice, so its local type must agree across branches.  This
is simple and always sound, but it rejects protocols where
the third party could distinguish branches later through
subsequent communication.  Coinductive full merging (PMY25
Def 4.3) admits the broader class — branches may diverge
structurally if a later communication lets the role
reconcile them.

FX uses plain merging by default; it is conservative and
predictable.  A session declaration annotated
`@[merge(full)]` opts into coinductive full merging, which
admits more protocols but produces less transparent errors
when the admission fails.  Plain-merge failures are reported
at S007 with the diverging role named.

The well-formedness conditions on G are the obvious ones:
every `t` occurs under an enclosing `μt.G`, recursion is
guarded by at least one communication event in the body,
and labels are distinct within their choice.  Violation is
S008.  Surface-to-G parsing is covered by fx_grammar.md
§5.15.

Role names enter the grammar through the kind system.  A
session declared `<Alice: role, Bob: role, Charlie: role>`
treats each role as a kind-`role` parameter, reusing the
scoping infrastructure of §3.13 without new machinery.
Projections and the per-role local types are produced at
elaboration time; the grade vector and linearity checks of
§11.25 operate on those projected types, not on G
directly.

### 11.17 Association

Association is the invariant that ties a typing context Δ to
a global type G when FX is reasoning top-down.  It
generalizes the classical consistency condition of
Honda-JACM16 to admit subtype-refined local implementations,
and it is the invariant that subject reduction preserves.

Scalas-Yoshida 2019 introduced a parametric typing
judgment `Θ · Γ ⊢ P with φ(Γ)` that unified several earlier
soundness results under one safety predicate φ.  Hou-Yoshida-
Kuhn 2024 showed that the subject-reduction proofs SY19
built on classical "consistency" were not preserved under
full merging, and that the correct invariant is association.
Pischke-Masters-Yoshida 2025 extended the notion to the
asynchronous case with queue types.  FX adopts the HYK24 /
PMY25 formulation:

```
Δ ⊑_s G  iff
  (1) dom(Δ) = { s[p] : p ∈ roles(G) }
  (2) ∀ p ∈ roles(G):  Δ(s[p])  ⩽  G↾p
```

The domain of Δ matches the roles of G, and each local type
Δ(s[p]) is a subtype of G's projection onto p.  Subtype,
not equal — the implementation may refine each role's view
via synchronous subtyping (§11.19) or precise async
subtyping (§11.20) as long as the refinement is sound.  The
wider slot is what distinguishes association from classical
consistency: consistency demanded exact equality with the
projections, which rejects implementations that safely
refine the projected shape.

The preservation theorem (HYK24 Thm 5.8) states that
association survives reduction: if Δ ⊑_s G and Δ reduces to
Δ' by some event α, there exists G' with Δ' ⊑_s G' and G
reducing to G' by the same event.  Every step of the
implementation corresponds to a step of the specification,
and the association link is maintained.

The payoff is that G's properties transfer directly to the
implementation.  A programmer who writes a global type G,
verifies that G satisfies the desired φ (§11.18), and
establishes association once does not need to re-prove φ
for the associated implementation.  The safety, deadlock-
freedom, liveness, and crash-safety properties of G carry
over.

Association is not required for every protocol.  When no
natural global type exists — a binary channel with dual
endpoints is the common case — bottom-up reasoning suffices:
write Γ with its per-role local types, pick φ, verify φ(Γ)
directly on the LTS.  Both paths are first-class.  A session
declared with `global_session<…>` triggers the association
check at elaboration; a session declared with `session` and
dual endpoints is checked locally without invoking G or
projection.  Association also composes with subtyping: if
Γ_1 ⊑ G_1 and Γ_2 ⊑ G_2 with disjoint session tags, then
Γ_1 ∘ Γ_2 ⊑ G_1 ⊕ G_2 for the parallel composition of
global types (§11.22).

### 11.18 Safety levels

The parametric safety predicate φ from SY19 admits seven
canonical instantiations, each captured as a modal μ-calculus
formula on the labeled transition system derived from the
typing context.  The seven levels, in increasing strength:

```
safe     νZ. (∀α: [α]Z)
         Every reachable communication event is well-typed.
         No label or payload mismatch ever appears on any
         trace.

df       νZ. (⟨⟩Z ∨ atEnd)
         Deadlock-free.  From every reachable state, the
         protocol can either make further progress or is
         already at End.

term     μZ. atEnd ∨ (∀α: [α]Z)
         Every fair path terminates at End.

nterm    νZ. ¬atEnd ∧ ⟨⟩Z
         Never reaches End and always has a reduction.
         Useful for serving loops that run indefinitely.

live     νZ. [pendingIO]⟨α⟩ Z
         Every pending input or output eventually fires.

live+    live, subject to fair scheduling.
         Pending I/O fires given a fair scheduler.

live++   live, under any scheduling.
         Pending I/O fires regardless of scheduler, including
         adversarial.
```

All seven are decidable on finite-state Γ, and FX's Γ is
finite by construction: participants are bounded (§11.13),
recursion is guarded (§11.14), and queues are capacity-
bounded (§11.15).  Model-checking μ-calculus formulas on
finite labeled transition systems runs in PSPACE in the
formula and polynomial time in the LTS.  For small Γ the
elaborator checks the formula directly; for larger Γ the
check is dispatched to an external μ-calculus verifier (see
§10.16 for the offline-verification story).

The choice of φ is per-session, not global.  A protocol
with only a one-shot request-response loop typically wants
`safe ∧ live+ ∧ term`.  A long-running service loop wants
`safe ∧ nterm`.  A distributed consensus protocol wants
`df ∧ live+ ∧ crash-safe(R)`.  A constant-time protocol
carrying secret payloads wants `safe ∧ live++` to rule out
scheduling-dependent timing.  The session declaration
states the chosen φ explicitly; without an annotation, the
compiler picks a default based on the session's declared
effect row (`with Async` gets `df ∧ live+`, for example).

Compound predicates compose via conjunction, and the
standard conjuncts (safe, df, live+, live++, crash-safe,
associated) compose under all the session combinators of
§11.22 — the composed system satisfies the intersection of
its parts' predicates given the disjointness conditions
detailed there.

User-defined φ is a first-class mechanism.  A programmer
writes a custom safety formula as a ghost function taking
Γ's LTS and returning `Prop`, annotates the session with
`verify <formula>`, and the compiler model-checks it
alongside the standard levels.  The formula erases at code
generation per §1.5, so custom safety properties cost
nothing at runtime, and the compile-time cost scales with
the formula's verification complexity.

Seven levels rather than fewer is the right granularity
because each captures an operational guarantee that
distributed-system engineering cares about distinguishing.
Levels beyond `live++` either require timed session types
(§11.26.4) or are decidably equivalent to `live++` on
finite-state systems, so the hierarchy does not extend
usefully further within the untimed fragment FX
specifies.
don't deadlock" (df).  FX uses all seven; §11.26's table
lists which channel gets which.

**Why more levels don't help.**  Levels beyond live++
(liveness with bounded response time, fairness-with-quantitative
rate, and so on) are either out of scope (need timed
protocols — Bocchi-Yang-Yoshida 2014, deferred to §11.26.4)
or decidably equivalent to live++ in finite-state systems.
The seven-level hierarchy is complete for untimed finite-
state MPST.

### 11.19 Synchronous subtyping — Gay-Hole 2005

Subtyping captures safe substitution: if T ⩽ T', replacing
a T'-typed participant with a T-typed one preserves the
protocol's correctness.  The relation is the heart of
protocol evolution (§15.4 `refines`) and the refinement of
abstract specifications into concrete implementations.

**Gay-Hole 2005 synchronous subtyping ⩽**, six structural
rules under rendezvous semantics:

```
 end  ⩽  end

 send<P₁, T₁>  ⩽  send<P₂, T₂>        when P₁ ⩽ P₂ and T₁ ⩽ T₂
                                        (covariant both)

 recv<P₁, T₁>  ⩽  recv<P₂, T₂>        when P₂ ⩽ P₁ and T₁ ⩽ T₂
                                        (contravariant on payload)

 select<B₁…>  ⩽  select<B₂…>           when every B₁ has a matching
                                        B₂ with compatible types
                                        (subtype has ⊆ labels —
                                         narrower choice)

 offer<B₁…>  ⩽  offer<B₂…>             when every B₂ has a matching
                                        B₁ with compatible types
                                        (subtype has ⊇ labels —
                                         broader offer)

 loop<T₁>  ⩽  loop<T₂>                 when T₁ ⩽ T₂ under the
                                        coinductive hypothesis that
                                        the outer loops are related

 Stop  ⩽  T  (for every T)             A crashed endpoint vacuously
                                        inhabits anything.
```

Decidability follows from coinductive simulation: the
checker walks T and T' in lockstep, memoizes the visited
pairs, and closes at guarded fixed points.  Cost is linear
in the size of the two types with memoization.

FX invokes ⩽ wherever a session-typed value is passed to a
context expecting a different, usually more abstract,
session type.  Four sites matter in practice.  Function-
argument passing accepts a caller's channel of type T
where T' is expected when T ⩽ T'.  Protocol versioning per
§15.4 uses ⩽ as part of the four `refines` obligations to
establish that v2 can substitute for v1.  Existential
packaging of a concrete T_0 into `exists T. {…}` requires
T_0 ⩽ T for the packed type to satisfy its declared
signature.  Foreign-function-interface boundaries check
that the adapter-exposed session is a subtype of the
canonical session the FX side expects.

On rejection the compiler reports which rule failed and,
for the coinductive case, the cycle that prevented closure.
The error is S015 with the offending combinator pair and
the structural mismatch named.

### 11.20 Precise asynchronous subtyping

Asynchrony admits message reorderings that the synchronous
rules reject.  A send to q can be anticipated past a receive
from r ≠ q without breaking the protocol: the send enters
q's queue, and the receive from r completes independently.
Gay-Hole's relation forbids such reorderings because it was
designed for rendezvous semantics.  The precise async
relation ⩽_a admits every sound reordering and no unsound
one; GPPSY23 Theorem 7.1 established that ⩽_a is the unique
sound and complete refinement for bounded-buffer asynchronous
sessions.

The decision procedure works by SISO (single-input,
single-output) tree decomposition.  A SISO tree has no
`select` and no `offer` — every step is a concrete send or
receive on a specific channel.  A session type T decomposes
into a finite forest of SISO trees, one per path through T's
choice points.  On SISO trees the refinement relation ⊑ is
defined by six rules:

```
 [ref-in]      recv<P, W>  ⊑  recv<P', W'>    when P ⩽ P' and W ⊑ W'
 [ref-out]     send<P, W>  ⊑  send<P', W'>    when P ⩽ P' and W ⊑ W'
 [ref-A]       recv<P₁, …>·A ⊑ A·recv<P₂, …>  anticipate a recv past
                                                a sequence A of recvs
                                                from other participants
 [ref-B]       send<P₁, …>·B ⊑ B·send<P₂, …>  anticipate a send past
                                                a sequence B of recvs
                                                and sends-to-others
 [ref-end]     end  ⊑  end
 [ref-subsort] S  <:  S'                       value-type subsorting
```

[ref-A] and [ref-B] are the rules that encode which I/O
reorderings preserve async safety.  An A-sequence contains
only receives from participants different from the one
whose receive is being anticipated; a B-sequence contains
receives from any participant and sends to participants
different from the target of the anticipated send.  The
different-participant side condition is what rules out
reorderings that would introduce protocol mismatches.

The relation on full types is defined from the SISO forest:
T ⩽_a T' iff every SISO tree in the decomposition of T is
related by ⊑ to some SISO tree in the decomposition of T'.
Equivalently, every concrete path through T refines some
path through T'.

General ⩽_a is undecidable (Bravetti-Carbone-Zavattaro 2018;
Lange-Yoshida 2017), but the undecidable cases are exotic.
Most protocols that arise in practice admit a bounded-depth
decision procedure along the lines of Cutner-Yoshida-Vassor
2022.  FX bounds the SISO expansion at a compile-time depth
D, defaulting to 64 and overridable on a per-session basis
via `@[subtype_depth(N)]`.  Any subtype relation provable
within depth D is accepted; deeper relations either demand a
raised depth, an explicit proof via a `verify` block
(§10.3), or a structural rewrite of the protocol.  Protocols
with very wide fan-out or deep staging may need a depth
beyond the default, and the session declaration states the
requirement locally.

When SISO expansion exhausts its fuel without a decision,
the compiler reports S017, names the SISO path that was the
blocker, and suggests the available remedies: raise the
depth, fall back to synchronous ⩽ (§11.19), or restructure
the protocol so its refinement obligations land within the
bounded fragment.  For protocols that need a decision
beyond what the compiler can dispatch inline, the
verification toolchain emits the query to an external μ-
calculus solver, caches the resulting certificate keyed by
the session's content hash, and consults the cache on
subsequent compiles.  The cache key prevents stale
certificates from surviving a protocol edit.

Soundness is preserved unconditionally.  FX accepts only
relations it can prove within depth D, and every accepted
relation is sound.  The bounded approximation may
conservatively reject sound relations that need more depth
than it can afford, but no accepted program is unsafe on
account of subtyping approximation.

### 11.21 Crash-stop

Participants die, networks partition, peers become
unreachable.  A session type discipline that handles
failures only through runtime exceptions does not compose
with the rest of the language: exceptional control flow
becomes invisible to the type system and the obligation to
clean up falls to the programmer.  FX lifts failure into
the protocol itself.  The synchronous rules come from BSYZ22
and the asynchronous extension from BHYZ23; together they
extend the session calculus with three pieces.

The first is the `Stop` local type.  A participant whose
local type has reduced to `Stop` has no remaining protocol
obligations; any attempt to send to them fails, and any
attempt to receive from their queue returns a crash
indication.  Because `Stop` admits no outgoing transitions,
`Stop ⩽ T` holds for every T (the Gay-Hole rule of §11.19):
a crashed endpoint vacuously inhabits any protocol, since
it will never observe T's continuations.

The second is the crash label.  Inside an `offer<…>` that
receives from a peer p, an additional branch
`Branch<Crash<p>, T>` specifies what to do when the runtime
detects that p has crashed.  The branch fires on any
condition that constitutes crash detection for the
underlying transport — transport-level completion errors,
confirmed-dead signals from a membership protocol, missed
heartbeats, or an explicit `cancel(ch)` call per §11.3.
The crash branch is syntactically mandatory whenever the
`offer` receives from a role outside the reliability set;
omitting it is error S009.

The third is the unavailable-queue marker ⊘ (BHYZ23 §4.2).
When a peer crashes mid-protocol, the asynchronous queue
addressed to that peer transitions to ⊘, and subsequent
sends into ⊘ are silently dropped.  The model reflects
transport-level behavior in which bytes sent to a dead peer
leave the sender but never reach the recipient — the
protocol observes the drop as a typed event rather than as
a silent data loss.

Each session declaration names a reliability set R ⊆ Roles.
Roles in R are assumed not to crash during the protocol;
roles outside R may.  Typical choices: R = ∅ for peer-to-
peer communications where any participant may fail; R =
{all roles} for channels confined to a single trust domain
where a failure takes the whole domain down together;
R = {leader} for consensus-mediated protocols where the
current leader is assumed reliable within a commit and a
new election re-establishes the protocol on leader death.
The session declaration states R explicitly; the type
checker uses it to decide which `offer` branches must carry
`Crash<p>` handlers.

A safety predicate φ (§11.18) is crash-aware when it
admits R as a parameter, treats `Stop`, ⊘, and crash
labels as first-class events in the LTS, and is preserved
under the three crash reduction rules: the crash event
moves a role's local type to `Stop`, the dead-peer queue
transitions to ⊘, and messages still in transit to a
crashed peer are discarded.  BSYZ22 and BHYZ23 establish
safety, deadlock-freedom, and liveness preservation under
crash-aware φ.  FX packages these as the compound predicate
`is_crash_safe(Γ, R)` and includes it as a conjunct of
every session's chosen φ.

Crash-stop integrates with the existing Fail effect (§9)
rather than adding a new runtime primitive.  A peer crash
observed inside a crash branch may transition into a Fail
effect row, propagating to the nearest handler through the
same machinery that handles explicit `fail(e)` calls.  This
keeps the surface ergonomics uniform — a `try ... catch`
that handles `Fail(PeerCrashed)` composes naturally with
the protocol's declared crash branches.

Crash-stop does not cover Byzantine failures — peers that
lie about their protocol state, replay attacks, link-level
corruption between live peers, or any form of adversarial
behavior.  Those concerns are out of scope for the session
type layer; authentication and message integrity are the
job of §14 contracts and the transport's cryptographic
layer.  The session calculus assumes honest-but-fallible
participants.

### 11.22 Compositionality

Session types, typing contexts, global types, queue types,
safety predicates, reliability sets, and the Usage grade's
permission structure all compose.  A system built from
well-typed subsystems is itself well-typed, provided the
subsystems' compatibility conditions hold.  This is the
property that lets the language scale: protocol correctness
for a system of many channels is verified as the conjunction
of per-channel correctness plus local compatibility checks,
not as a monolithic proof over the entire composite.

Four primary combinators cover the common cases.

Sequential composition `T ; S` runs T to its End and then
runs S.  Every End occurrence in T is replaced by S's
starting state; T's reduction graph is followed by S's,
with T's exit feeding S's entry.  The compatibility
condition is that T's exit permissions subsume S's entry
permissions.  The compositionality theorem reads: if Γ_T ⊢
P_T : T with φ_T and Γ_S ⊢ P_S : S with φ_S, then Γ_T ∘ Γ_S
⊢ P_T ; P_S : T ; S with φ_T ∧ φ_S.

Parallel composition `T ∥ S` runs the two protocols
simultaneously on disjoint resources.  The compatibility
conditions are the three disjointness requirements: the
domains of the two contexts, their Usage-grade permission
sets, and their σ-channel endpoints must pairwise not
overlap.  Under those conditions, the same theorem as
before holds with Γ_T ∪ Γ_S in place of Γ_T ∘ Γ_S.  This is
the concurrent separation logic frame rule lifted from
memory regions to protocol-typed channels: disjoint contexts
interleave without interference and each subsystem's
invariants survive into the composite.

Choice composition `T ⊕ S` picks T or S based on a condition
external to the protocols themselves.  The compatibility
condition is that T and S start from the same roles with
compatible initial states.  The composed type holds φ_T when
the condition is true and φ_S when it is false; both
obligations are discharged per branch.  This form is
distinct from `select<Branch<L_1, T>, Branch<L_2, S>>`, which
is an internal choice at a specific protocol state.

Delegation transfers one session's endpoint through another
session.  The owner of a T-endpoint can send T as a message
payload on an S-channel whose next event is `Send<T, K>`;
the receiver gains the T-endpoint and may thereafter use it
per T's dual.  The compatibility conditions are that the
carrier S has a matching delegation point, the sender owns
the T-endpoint, and the receiver's corresponding `Recv<T,
K'>` matches T's dual.  Delegation preserves all of T's
properties — safety, liveness, association, crash handling,
Usage-grade balance — as long as S itself is well-typed.
The discipline comes from Honda 1998's original throw/catch
rule.

Four derived combinators build on the primaries.  The
higher-order combinator admits sessions that carry other
sessions as payloads, making delegation first-class (§11.23).
The content-addressed quotient T/≈ compares messages up to
content-hash equivalence, permitting deduplication without
observable protocol-level difference.  The timed combinator
`T under Budget` attaches a latency budget that composes
additively in sequence and maximally in parallel or choice;
see §11.26.4.  The checkpointed combinator `T with rollback
to CP` records protocol state at a marked point and restores
it on rollback, used for speculative execution and
transaction-style protocols; see §11.26.2.

The general compositionality theorem states that two
well-typed subsystems compose into a well-typed composite
whose safety predicate is the conjunction of the components'
predicates plus any combinator-specific obligation:

```
 Γ_1 ⊢ P_1 : T_1 with φ_1(Γ_1)
 Γ_2 ⊢ P_2 : T_2 with φ_2(Γ_2)
 compatibility for combinator ⊙
 ─────────────────────────────────────────────────────
 Γ_1 ⊙ Γ_2 ⊢ P_1 ⊙ P_2 : T_1 ⊙ T_2
                     with (φ_1 ∧ φ_2 ∧ φ_⊙)(Γ_1 ⊙ Γ_2)
```

The combinator-specific term φ_⊙ is usually trivial because
the disjointness conditions already carry the hard part of
the argument.  The theorem is proved for each primary
combinator: sequential by protocol-level continuation,
parallel by the CSL frame rule, choice by disjunction
preservation, delegation by Honda's throw/catch.

Several corollaries follow.  Subtyping composes
contextually: T_1 ⩽ T_1' and T_2 ⩽ T_2' imply T_1 ⊙ T_2 ⩽
T_1' ⊙ T_2' for every primary combinator, by structural
induction.  Association composes under parallel with
disjoint session tags: Γ_1 ⊑_s G_1 and Γ_2 ⊑_s G_2 imply
Γ_1 ∘ Γ_2 ⊑_s (G_1 ∥ G_2), which is HYK24's preservation
theorem extended to composed contexts.  Crash-safety
composes with intersection of reliability sets: the
composite is as reliable as the least-reliable subsystem.
Permission balance composes under disjoint Usage-grade sets,
which is the original CSL frame rule (§6.4) restated for
session channels.

Not every safety predicate composes under every combinator.
The practically useful conjunctions — safe, df, live+,
live++, crash-safe, Usage-balanced, associated — compose
under all four primary combinators given the disjointness
conditions.  `nterm` does not compose sequentially (the
first subsystem never reaches End, so S never starts) but
does compose parallelly.  `term` requires all branches to
terminate: both sides of a parallel composition, and every
branch of a choice.

Four things do not compose cleanly.  Byzantine failures
require cryptographic authentication and are handled at §14
contracts and the transport layer.  Shared mutable state
outside the Usage discipline violates disjointness; §1.2's
axioms rule it out.  Unbounded recursion breaks
decidability, rejected at well-formedness.  Temporal
composition across disjoint scheduling domains requires a
shared clock that session types do not model; see §11.26.4.

### 11.23 Higher-order sessions

DGS12 §5 / Mostrous-Yoshida 2015.  A session can carry other
sessions as payloads: `Send<Channel<T>, K>`.  The sender
owns a T-endpoint; sending it on a K-carrier transfers the
T-endpoint to the receiver, who may then use it per T's
dual.  This is delegation (§11.22) made first-class.

Two application patterns cover most higher-order uses in
practice.  Cross-layer protocol nesting encodes a transport
stack whose lower layers deliver bytes for higher-layer
sessions: the outer session's payload type is declared as
`OpaqueProtocol<InnerSessionType>`, and the outer session
verifies only length, integrity, and encryption while the
inner verifies protocol structure.  Endpoint transfer
handles the case where a session is established by one
participant and handed to another — a dispatcher accepts a
request, opens a downstream session, and delegates the
downstream endpoint to a worker for the reply path.  Both
patterns reduce to the same typing rule:

```
Γ, (s₁[Alice] : Send<Channel<T>, K>), (s₂[Alice] : T) ⊢ Alice
 ─────────────────────────────────────────────────────────────
 after Alice sends the s₂-endpoint on s₁:
Γ, (s₁[Alice] : K), (s₂[Alice] : End) ⊢ Alice
```

Alice's s₂-endpoint is consumed by the send; the Usage
grade at the binding transitions from 1 to 0, so Alice
cannot double-send.  The linearity enforcement is the same
rule that catches use-after-free of file handles and sockets.

The compatibility condition is that the carrier delivers
reliably or reports its failures.  The session calculus can
compose outer properties with inner properties only when
message loss on the carrier either does not happen or
produces a typed event the inner session can react to.
Every transport FX supports at the session layer satisfies
this condition, typically via the carrier's own crash branch
(§11.21).

Higher-order sessions are specifically about channels
carrying channels.  They are not a mechanism for sending
functions — that is ordinary value passing through a lambda
payload — and they are not a mechanism for dynamically
rebinding a session type at runtime.  FX's type system is
decidable and static; the session types carried as payloads
are known at elaboration, and the receiver's continuation
type is determined by the carrier's declaration.

### 11.24 Kernel translation — CoindSpec encoding

Every surface session construct in §11.1-§11.23 reduces to
terms in the kernel of §30.  This section states the
translation.  UNTRUSTED (L3 per SPEC.md §5) — the kernel
sees only the translated `Coind` terms; the load-bearing
soundness is the CoindSpec linear-codata discipline
(Appendix H.5).

**Session type T translates to a CoindSpec with destructors
per T's shape.**  The destructors name the valid "next
moves" and advance the Protocol grade (dim 6, Tier T) to
the continuation's session type.

  * `End` lowers to a `coind_spec(name: "__session_end",
    params: [], destructors: [])` with no valid next moves;
    the channel is consumed.
  * `Stop` lowers to a `coind_spec(name: "__session_stop",
    params: [], destructors: [destructor("observe_crash",
    result_type: coind_ref("Fail", [PeerCrashed]))])` whose
    only move is to observe the crash, producing a `Fail`.
  * `Send(p, k)` lowers to a destructor `send_advance:
    self -> (payload: p) -> channel(k)` where `channel(k)`
    is the translation of `k`.
  * `Recv(p, k)` lowers to a destructor `recv_advance:
    self -> sigma(payload: p, next: channel(k))` — returns
    the payload plus the continuation channel.
  * `Select(b_1, ..., b_k)` lowers to k destructors, one
    per label: `sel_m_i: self -> channel(b_i.body)`.
  * `Offer(b_1, ..., b_k)` lowers to a single destructor
    `receive_branch: self -> ind(b_1.label | ... |
    b_k.label, body_i)` whose inductive dispatches to the
    chosen body.
  * `Loop(t)` lowers to a `coind_spec` that refers to itself
    via `Term.coind(self_name, params)`; Coind-nu (Appendix
    H.5) guardedness is automatic because every destructor
    path passes through at least one send/recv/end/stop.
  * `Continue` is the self-reference inside the loop, the
    same `Term.coind(self_name, params)` reference.

**Grade propagation at destructor application.**  Every
destructor call on a channel is a kernel `Coind-elim` step
(Appendix H.5).  The grade vector updates per the §6.2 App
rule:

  * **Usage (dim 3)**: channel at grade 1 → channel' at
    grade 1 (one linear consumed, one produced).  Double
    consumption rejected.
  * **Effect (dim 4)**: each send/recv adds Async (or IO for
    cross-node).  Fail added when stepping into a crash
    branch.
  * **Protocol (dim 6, Tier T)**: typestate advances from
    T to K per the destructor.
  * **Security (dim 5)**: payload's classification propagates
    to the channel's returned state.
  * **Complexity (dim 13)**: cost(send) + cost(recv)
    accumulates per the send/recv pair's declared cost.

No new kernel axiom needed.  The 23-axiom allowlist (Appendix
H) remains intact; §11 session types are a derivation from
Coind-form/elim + Later guarded recursion + existing grade rules.

**Duality as a kernel function.**  `dual : SessionType →
SessionType` is a total function over the session-type
syntax, implemented in `FX/Derived/Session/Binary.lean` and
proved involutive (`dual ∘ dual = id`, Honda 1998).  At
`new_channel<P>()` the kernel minces the CoindSpec pair
`(Coind "__session_chan_P" [], Coind "__session_chan_dualP"
[])` where the dualP spec is automatically derived.

**Linearity enforcement** is the Usage grade's job (dim 3).
Channel bindings are grade 1; each destructor call consumes
the old binding and produces a new one at the continuation's
grade.  No runtime ownership-tracking primitive — the grade
check at kernel elaboration time is sufficient.

Session types, their CoindSpec translations, the Protocol
grade, and the association checks all erase at code
generation per §1.5.  The runtime binary contains only the
underlying transport operations — the instruction sequences
that actually move bytes between participants.  The
protocol discipline exists entirely at compile time, and
§21 describes the erasure step that removes it before
codegen.

### 11.25 Integration with the grade vector

Session types are not a framework bolted onto the rest of
the language.  They are a specific instantiation of FX's
22-dimension multimodal graded type theory (§6), using dimensions that
existed before sessions were added.  A channel of session
type T carries a full grade vector, and the rules of §6.2
applied pointwise to each dimension recover the
session-safety properties of the preceding subsections.

The dimensions map onto session-type roles as follows.  The
Type dimension (1) sees the channel's kernel type, a
`Coind` form built from the translation of §11.24.
Refinement (2) propagates payload predicates — a channel
declared `Send<P { pred }, K>` narrows the set of values P
can carry.  Usage (3) enforces linearity: a channel binding
is grade 1, consumed at each destructor application, and
cannot be annotated `@[copy]`; double-use is caught by the
same rule that catches double-close of a file handle.
Effect (4) carries `Async` when the channel crosses threads,
`IO` when it crosses processes or nodes, and `Fail(E)` when
a crash branch propagates the failure upward.  Security (5)
tracks the classification of payloads; the rule from §6.8
(I004) handles the cross of classified data with async
channels.  Protocol (6), the Tier T typestate dimension, is
the session-type state itself; its value advances on every
destructor.  Lifetime (7) ties the channel's region
parameter to its payload's lifetime.  Provenance (8) and
Trust (9) propagate through the channel the same way they
propagate through any data flow.  Representation (10) binds
through the contract layer when the channel crosses a wire
boundary.  Observability (11) enforces constant-time
protocols by forbidding secret-dependent selections.
Complexity (13) sums send and receive costs along a
protocol's path; Space (15) is bounded by the queue
capacity.  Reentrancy (19) is non-reentrant by default,
with `loop` the sanctioned construct for recursion.  Size
(20) bounds destructor-chain depth for the sized-codata
interpretation.  Version (21) participates through §15
`refines`.  Precision (14), FP-order (17), and Overflow
(16) are not specific to session types; payload arithmetic
uses the same rules as elsewhere.  Clock-domain (12)
matters only for hardware session types that cross clock
boundaries.

The Tier T Protocol dimension (§6.3) is the load-bearing
piece.  Tier T has no par/seq arithmetic — its operations
are transitions on state, not commutative or associative
combinations.  Session types are Tier T's canonical
instance: each session-type state is a grade value, and the
valid next moves are the destructor signatures of the
translated `CoindSpec`.  Using a channel at a state with no
outgoing destructor for the attempted operation is a
grade-check failure at §6.2's App rule, reported by the
same mechanism that rejects any other grade-vector
violation.  Session types introduce no new rule — they
introduce a specific grade-algebra instance that the
existing rule handles.

Compositionality of session types (§11.22) follows from
pointwise composition of grade vectors.  Disjointness at
the Usage dimension is the CSL frame rule.  Disjointness at
the Protocol dimension is parallel session composition.
Disjointness at the Effect dimension preserves effect
inclusion across the composed row.  Because the grade
vector's individual dimensions are pointwise independent,
the three disjointness conditions reduce to the same
check the kernel already performs at every expression site.

The practical consequence is that a programmer using FX
does not need to learn session types as a separate theory.
The programmer learns the graded type vector, the
parametric safety predicate φ, the Usage grade's linearity
discipline, and the Protocol grade's typestate discipline —
all of which exist independently of session types.  A
session declaration is the point where these pieces
crystallize into a named pattern the kernel translates via
§11.24.  The kernel checks the resulting grade vector with
the same rules it uses for linear file handles, graded
lambdas, effect rows, and security propagation.  This
uniformity is the design commitment of §1.1 and §6.3, and
session types honor it rather than contradict it.

The implementation surface divides cleanly.  The linear
resource discipline, the parametric φ check on the grade
vector, Protocol typestate tracking, and effect-integrated
crash propagation are native parts of the kernel from the
underlying type theory.  The `Coind` family that supplies
the state space for each session type, and the kernel
subtyping relation extended with the Gay-Hole rules of
§11.19, are kernel extensions whose axioms sit within the
33-entry allowlist of Appendix H.  The binary combinator
syntax, the queue-type extension to Γ, global types and
projection, the association check, the crash-stop
machinery, the pattern library, and the precise-async
subtyping procedure live in the derived layer under
`FX/Derived/Session/`.  Choreographic projection is
deferred to a later revision.

### 11.26 Frontier items

Six protocol patterns arise in practice that the
§11.1-§11.25 machinery does not cleanly subsume.  Each has
a workaround that preserves soundness within the covered
fragment while admitting the pattern at the surface; formal
incorporation into the core calculus is deferred.

Dynamic participant sets are the first open case.  The
multiparty calculus fixes the participant set at protocol
declaration, and Deniélou-Yoshida 2011 describes a dynamic
extension, but that extension has not been combined with
precise async subtyping, crash-stop, and bounded queue
types in a single published result.  FX handles the
pattern at the type level by declaring a static upper bound
on the participant count; the runtime-active set is a
refinement of that bound, and membership events are first-
class protocol transitions:

```
type dynamic_collective<N_max: nat { N_max <= 1024 }> =
  session
    membership_frozen(active: set(role_id) { |active| <= N_max });
    loop
      branch
        broadcast(payload: T) => ... ;
        member_join(new_id: role_id)
          => membership_frozen(active: active ∪ {new_id}) ;
        member_leave(id: role_id)
          => membership_frozen(active: active \ {id}) ;
        member_die(id: role_id)
          => membership_frozen(active: active \ {id}) ;
      end branch
    end loop
  end session;
```

The `membership_frozen` event acts as a protocol checkpoint;
between checkpoints the active set is fixed, and all peers
agree on the set by the time the next operation fires.  A
formal incorporation of dynamic membership with the other
three extensions is future research.

Speculative sessions with rollback are the second open
case.  A speculative execution's draft-verify-accept flow
is a session with a rollback edge to a saved checkpoint on
reject.  Transactional session types (Vieira-Parreaux-
Wasowicz 2008) handle rollback, but not alongside
multiparty, asynchrony, and crash-stop.  FX supplies the
pattern through the checkpointed combinator from §11.22:

```
type speculative = session
  rec Step;
    checkpointed begin
      send(candidates: array(T, N));
      receive_branch;
        accept_all    => ... Step;
        accept_prefix => receive(accepted: nat { accepted < N });
                         rollback Step;
        reject        => rollback Step;
      end branch
    end checkpointed
  end rec
end session;
```

Each iteration establishes a checkpoint at loop entry; the
rollback branch restores the protocol state to that
checkpoint.  The runtime serializes session state at the
checkpoint and restores it on rollback.  Soundness is
argued by reduction to a synchronous two-state protocol;
mechanized proof is deferred.

Persistent sessions across crashes are the third case.  A
session that must logically span a crash of one of its
participants — a long-running service that checkpoints its
progress and resumes on a replacement node — is not in
mainstream MPST.  FX admits the pattern through a
`@[persistent]` annotation that injects an implicit
"load checkpoint and resume" branch at every Fail site in
the session's local types:

```
@[persistent(interval: 1000.steps)]
type durable = session ... end session;
```

Runtime Fail detection invokes a rollback to the most recent
checkpoint and replays from there.  The pattern reduces to
crash-stop plus an explicit checkpoint-load rule.  The
external storage integration sits at the application level
and is not part of the session kernel.

Timed sessions are the fourth case.  Some protocols carry
latency budgets — a request-response that must complete
within a specific deadline, or a synchronization event that
must fire within a window.  Bocchi-Yang-Yoshida 2014
formalizes timed session types, but the construction has
not been combined with the decidable fragment FX covers.
The current workaround is a phantom latency-class wrapper
on the session type, `HotSession<Budget>(S)`, with the
budget checked at runtime through the bench harness of
§23.5 rather than at compile time.  Surface syntax:

```
type fast_request =
  HotSession<300.microseconds>(session ... end session);
```

The wrapper is documentation plus a runtime assertion; a
compile-time timing proof is not part of the current
calculus.

Content-addressed protocol deduplication is the fifth case.
Two sessions transmitting identical payloads can share the
delivery: the recipient's state transition depends only on
the payload's content hash, and if the recipient already
has the content cached, the wire transfer elides.  The
quotient operator T/≈ from §11.22 expresses this at the
type level, but its soundness composition with crash-stop
has not been formally established.  The surface pattern is:

```
type deduped_publish = session
  send(data: ContentAddressed<Bytes>);
  receive(ack);
end session;
```

A `Send<ContentAddressed<T>, K>` is semantically equivalent
to `Send<T, K>` except that the transport is free to
deliver the payload by reference rather than by value when
the recipient has the content available.  The soundness
argument reduces to the observation that the recipient's
observable behavior depends only on content.

Cross-language session boundaries are the sixth case.  When
a session crosses the FX boundary to a language with a
weaker type system, the compile-time subtype check cannot
verify the external side's conformance.  The workaround has
two pieces.  At the boundary the compiler generates a
runtime session-type validator: incoming messages are
checked against the declared session type, and a protocol
violation raises `Fail(ProtocolViolation)`.  At the build
level, an external-language adapter must carry a proof
token generated offline by the verification toolchain and
signed by an authorized signer per §25.9; the compiler
accepts the external type as a subtype of the FX-side type
only when the token is present and verified.  Formalizing
proof-token-mediated cross-language subtyping is deferred.

---

Frontier items are documented here; their FX workarounds
make §11.26-cited protocols expressible today with the
understanding that a fully principled solution is pending.
Each workaround preserves the soundness of the fragment it
covers; the workaround's limitation is that it rejects some
protocols a fully-formalized theory would accept.

### 11.27 Error codes

S0xx error codes raised by the session-type layer:

```
S001  session type ill-formed (unguarded Continue or duplicate labels)
S002  duplicate label in select/offer/branch
S003  channel declared without capacity (required for balanced+ async)
S004  dual mismatch — channel endpoints are not dual types
S005  channel used after protocol complete (End state)
S006  channel used in wrong protocol state
S007  projection branches do not merge (plain merging failed;
        use @[merge(full)] or restructure)
S008  global type ill-formed (ungarded recursion variable)
S009  Offer from unreliable peer missing Crash<Peer> branch
S010  Stop from unreliable peer ill-formed (Stop ⩽ T always)
S011  queue capacity exceeded — session would violate balanced+
S012  session type with no valid projection for some role
S013  association check failed — Δ is not a subtype of G's projection
S014  session composition incompatible (disjointness violated)
S015  session type T is not a subtype of T' (sync Gay-Hole)
S016  session subtyping sides have different participant sets
S017  precise-async subtype undecidable within depth D
        — widen @[subtype_depth(N)] or restructure
S018  delegation violates linearity (sender loses endpoint,
        receiver gains — check Usage grade)
S019  higher-order carrier unreliable — cannot verify inner session
S020  timed session budget exceeded along some path
S021  content-addressed send: payload not @[copy] + content-hashable
```

Each error carries the §10.10 diagnostic structure (Goal /
Have / Gap / Suggestion).  Suggestions offer concrete FX code
rewrites; Crash-branch-missing for an unreliable peer (S009)
suggests the exact `Branch<Crash<Peer>, recovery_body>`
addition.

### 11.28 The compile-time contract

A session-typed channel of declared type T in context
(Γ, R, G) satisfies the compile-time contract when every
conjunct below holds:

```
is_well_formed(T)                   §11.14
is_balanced_plus(σ_c, capacity(c))  §11.15
G implies is_associated(Γ, G, s)    §11.17
is_subtype(T_impl, T_declared)      §11.19 or §11.20
is_safe(Γ)                          §11.18
is_df(Γ)                            §11.18
is_live_plus(Γ)                     §11.18
is_crash_safe(Γ, R)                 §11.21
is_usage_balanced(Γ, P_init)        §6.4
per-channel-φ conjuncts             as declared
```

The compiler discharges each conjunct once per channel
declaration.  A failure at any point triggers the
diagnostic of §11.27 and the compiler suggests a rewrite.
Every channel that passes the full set is first-class
within FX's graded type theory: its properties transfer to
every implementation that satisfies the declared session
type, and further use of that channel in other contexts
composes via the theorems of §11.22.

Session-typed message passing is one axis of FX's
concurrency story.  The remaining subsections above —
§11.10 memory model, §11.11 deadlock freedom, §11.12
pipeline execution modes — address shared-state
concurrency, which is orthogonal to session-typed
communication and governed by separate rules in the kernel.

### 11.29 Linear Corecursion via Pfenning-Toninho

The Curry-Howard correspondence between session types and
intuitionistic linear logic (Caires-Pfenning CONCUR 2010, Wadler
ICFP 2012) is the foundational discipline; FX additionally
adopts Pfenning-Toninho 2017 *linear corecursion in session-
typed processes* as the productive-by-construction discipline
for infinite session protocols.  The combination delivers a
key property: **session protocols cannot diverge — `with Div`
is unavailable on session-typed channels.**

The mechanism is the typed `later`-elimination of Appendix H.7b
lifted to the linear setting.  A recursive session protocol at
depth `n` is constructed via
`fix : (later(channel(s)) -> channel(s)) -> channel(s)` where
each unfolding consumes one `later` step on the recursive channel
reference.  The kernel's productivity check (§3.5
G-Unfold lifted to sessions) demands that every recursive
reference appear under a destructor — i.e. inside a send,
receive, branch, offer, or end — which the Later insulation
enforces typed-correctly.

Surface impact: the previous `with Div` escape on session
types (§11.21 crash-stop, §11.24 kernel translation) is
removed.  Long-running session loops are productive by
construction; a session whose body fails the productivity
check is a compile error rather than a `with Div`-tagged
escape with `Sorry` trust.

```
type stream_reader<a: type> = session
  rec Loop;
    branch
      next => receive(item: a); Loop;
      done => end;
    end branch;
  end session;
// Loop's recursive reference is under 'receive' →
// productivity holds via Later elimination at 'receive'.
// No `with Div` needed.
```

For genuine non-terminating workloads where productive-by-
construction is impossible (event loops without typed structure,
adversarially-driven I/O), the `Div` effect remains available
on non-session-typed code (§9.4) with the standard `Sorry`
trust propagation (§1.6).

### 11.30 Composable Lock-Free Concurrency via Reagents

Lock-free data structures (SpscRing, MpscRing, MpmcRing,
ChaseLevDeque, AtomicSnapshot, …) are composable via the
**reagent calculus** (Turon PLDI 2012, OCaml Multicore `kcas`
ecosystem; verified via Cosmo concurrent separation logic for
Multicore OCaml, POPL 2021).  FX ships the calculus as
`Std.Concurrent.Reagent`:

```
// Std.Concurrent.Reagent
type reagent<a: type, b: type>;        // a non-blocking transformation

fn pure<a: type, b: type>(f: a -> b) : reagent(a, b);

fn upd<a: type, b: type, c: type>(cell: atomic(c),
                                   f: (c, a) -> (c, b))
   : reagent(a, b);

fn cas<a: type>(cell: atomic(a),
                expected: a,
                desired: a) : reagent(unit, bool);

// combinators
fn seq<a: type, b: type, c: type>(r1: reagent(a, b),
                                   r2: reagent(b, c))
   : reagent(a, c);

fn choice<a: type, b: type>(r1: reagent(a, b),
                             r2: reagent(a, b))
   : reagent(a, b);

fn pair<a: type, b: type, c: type, d: type>(r1: reagent(a, b),
                                             r2: reagent(c, d))
   : reagent((a, c), (b, d));
```

Each reagent execution wraps in an atomic transaction (k-CAS
via the `kcas` library); composition is sequential `>>>`,
choice `<+>`, conjunction `<*>`, atomic primitive `upd`.  Every
lock-free idiom in the stdlib (Treiber stack, Michael-Scott
queue, Hazard-pointer publication, RCU read-side critical
sections) is a reagent composition with verified correctness
through Iris-grade BI (§10.16) — programmers don't write the
fragile CAS loops by hand.

The kernel sees reagents as ordinary stdlib types built over
the §11.10 atomic operations; no new typing rule needed.  The
Cosmo proof discipline lives in `FX/Derived/Reagent/` as
mechanized Lean theorems.

### 11.31 Causal Ordering via Vector Clocks

Distributed-coordination programs need to compare event
orderings without a global clock.  FX provides vector clocks
and hybrid logical clocks (Lamport CACM 1978, Mattern 1989,
Kulkarni-Demirbas-Madappa-Avva-Leone OPODIS 2014) as kernel-
recognized types in `Std.Time.Causal`:

```
// Std.Time.Causal
type vector_clock<n: nat>;                                 // n participants
type hybrid_logical_clock;                                  // physical + logical pair

fn happens_before<n: nat>(a: vector_clock(n),
                          b: vector_clock(n)) : bool;       // partial order
fn concurrent<n: nat>(a: vector_clock(n),
                      b: vector_clock(n)) : bool;           // not (a <= b or b <= a)
fn merge<n: nat>(a: vector_clock(n),
                 b: vector_clock(n)) : vector_clock(n);     // pointwise max
fn tick<n: nat>(self: nat { self < n },
                clock: vector_clock(n)) : vector_clock(n);  // bump self's slot
```

The `happens_before` predicate is **decidable** (§10.7 decide
framework): for finite `n`, the vector_clock lattice is finite-
order decidable structurally.  A `decide` tactic discharges
happens-before obligations without SMT, producing reproducible
certificates.

Kernel-level integration: `vector_clock(n)` participates in the
Lifetime modality (§6.3 dim 7) — causal ordering refines
reference validity scope.  A reference acquired before event
`e` cannot be used in a context whose vector clock claims `e`
happens-before the reference acquisition; the §6.0 Lifetime
coeffect (§9.11) enforces the constraint at the kernel typing
rule.

The replay-ordering refinement (§11.3.1) carries vector_clock
payloads in its OrderingEvent records — events are totally
ordered within a single replay log via the recorded sequence,
but across logs the partial order is the vector_clock happens-
before relation.

```
session async_grad_protocol<replay: replay_tag, n: nat> = session
  rec Loop;
    receive(grad: Stale(gradient_payload, tau),
            ord:  ordering_event(replay, vector_clock(n)));
    branch
      admit  => commit(grad, replay.record(ord)); Loop;
      reject => Loop;
    end branch;
  end session;
```


## 12. Information Flow

### 12.1 Security Labels

Data is classified by default.  It cannot flow to unclassified
outputs without explicit action.

```
fn process_payment(
  secret card: string,
  unclassified amount: i64,
) : receipt with IO
begin fn
  // log(card);  -- compile error: secret -> IO (unclassified)

  let hash = sha256(ref card);   // hash is also secret

  let last_four = declassify(
    substr(card, len: 4),
    policy: CardDisplay,
  );

  receipt { amount, card_suffix: last_four }
end fn;
```

The three security keywords:
- `secret` — explicit high-security label.
- `unclassified` — explicitly safe to expose.
- (no annotation) — classified by default.  Cannot flow to IO, logs,
  or any unclassified output.

### 12.2 Information Flow Rules

The type system enforces noninterference: changing secret inputs
does not change unclassified outputs.

Implicit flows through control structure are tracked:

```
fn blocked(secret flag: bool) : i32
begin fn
  // compile error: branch on secret controls unclassified result
  // if flag; 1 else 0 end if;

  let secret result = if flag; 1 else 0 end if;  // ok: result is secret
  declassify(result, policy: FlagPolicy)
end fn;
```

Flow rules: secret data can flow to more-secret contexts (upgrading)
but never to less-secret contexts (downgrading) without `declassify`.

### 12.3 Taint Tracking

Taint labels track data from untrusted sources.  Each taint class
is independent:

```
taint_class SQLi;
taint_class XSS;
taint_class PathTraversal;

fn handle_request(tainted(SQLi, XSS) input: string) : response with IO
begin fn
  let sql_safe = sanitize(SQLi, input, escaper: escape_sql);
  // sql_safe still has XSS taint

  let html_safe = sanitize(XSS, input, escaper: escape_html);
  // html_safe still has SQLi taint

  let fully_safe = sanitize(SQLi, sanitize(XSS, input,
    escaper: escape_html), escaper: escape_sql);
  // fully_safe has no taint
end fn;
```

Custom taint classes: `taint_class SSRF;`, `taint_class LogInjection;`.

### 12.4 Declassification

Declassification is controlled by a policy that names the principal,
describes what is being exposed, and optionally enables audit logging:

```
@[declassification_policy]
type CardDisplay
  allows: secret -> unclassified;
  principal: "payment_service";
  what: "last 4 digits of card number";
  audit: true;
end type;

let visible = declassify(last_four, policy: CardDisplay);
```

### 12.5 Constant-Time Execution

The `CT` effect is a 2-hyperproperty (Clarkson-Schneider 2008,
Antonopoulos et al. PLDI 2017): for all input pairs
`(p_1, p_2): inputs`, the timing-projected traces
`trace(prog, p_1)` and `trace(prog, p_2)` agree under the
secret-independent observation equivalence.  It decomposes into
three component disciplines:

  * **CT_branch** — no secret-dependent control flow (rules out
    `if` / `match` on secret-graded scrutinees).
  * **CT_access** — no secret-dependent memory access (rules out
    array indexing where the index is secret-graded; cache-timing
    side channels).
  * **CT_operation** — no variable-time operations on secret
    values (FP, division, table lookups; ARM DIT mode handles
    the last when available).

The compound `with CT` is `CT_branch ∧ CT_access ∧ CT_operation`.
A function may declare partial CT when one component is
genuinely unrelated to the secret-dependent surface:

```
fn cmp_first_n_bytes(secret a: bytes, secret b: bytes, n: nat) : bool
  with CT(branch, operation), Read;
  // CT(access) NOT claimed: indexing into a, b at runtime depends
  // on n; n is not secret, so this is safe; but the type system
  // does NOT make a CT(access) claim.
```

Examples:

```
fn ct_select(secret cond: bool, a: u64, b: u64) : u64
  with CT
= let mask : u64 = 0u64 - widen<u64>(cond);
  (a & mask) | (b & ~mask);

// compile error: branch depends on secret
fn bad(secret x: u64, secret y: u64) : u64 with CT
= if x > y; x else y end if;
// error[CT001]: branch condition depends on secret value
```

CT and verification compose:

```
fn aes_encrypt(secret key: aes_key, ref plaintext: block) : block
  with CT
  post r => aes_spec(key, plaintext, r);
```

**Hyperproperty annotations.**  Following Clarkson-Schneider, a
function declares a k-safety obligation as an ordinary `lemma`
quantified over k input copies; the compiler discharges it via
the Bridge modality (parametricity) when the quantifiers bind
parametrically, or via SMT relational verification otherwise.
For the `auth` example, 2-safety noninterference is stated as:

```
fn auth(secret pwd: hash, attempt: hash) : bool with CT;

lemma auth_noninterference(p: hash, q: hash, t: hash) :
        prop
  = (auth(p, t).public) == (auth(q, t).public);
```

The lemma's universally quantified statement covers all three
hashes; the compiler treats it as a 2-safety hyperproperty
because two `auth` calls with different `pwd` values must agree
on the public projection.  Generalized noninterference and
program refinement are k-forall l-exists hyperproperties
(Beutner-Finkbeiner CAV 2022).  The §6.0 Bridge modality makes
noninterference for polymorphic operations a free theorem
(Algehed-Bernardy ICFP 2019).

### 12.6 Logging Safety

Under classified-by-default, secret data flowing to log output is
automatically a compile error:

```
fn process(user: user_record) : response with IO
begin fn
  // log(f"Processing {user}");  -- compile error: classified -> IO
  log(f"Processing user_id={user.id}");  // ok: id is unclassified
end fn;
```

### 12.7 Secure Memory Zeroing

When a linear value containing classified data is consumed, the
compiler inserts a secure zeroing operation before deallocation:

```
fn process_key(key: secret aes_key) : hash
begin fn
  let result = sha256(ref key);
  drop(key);  // compiler inserts: secure_zero(key); then free(key)
  result
end fn;
```

No programmer annotation is needed.  Classified + linear = zeroed
on drop.

### 12.8 Faceted Values

Strict noninterference (§12.2) rejects every flow from secret
inputs to public outputs.  Where empirical practice (Quan, Duke
ECOOP 2024) reports a 90% reduction in spurious violations under
relaxed semantics, FX provides the faceted-values mechanism
(Austin-Flanagan POPL 2012) as the type-theoretic alternative: a
value carries both a public view and a secret view, and
operations propagate both in parallel.

```
type Faceted<a: type> {
  public: a;
  secret: a;
};

fn make_facet<a: type>(p: a, s: secret a) : Faceted<a>;
fn observe<a: type>(view: { L | H }, f: Faceted<a>) : a;
fn declassify_facet<a: type>(f: Faceted<a>, policy: P) : a;
```

The public view is observable at low security; the secret view
at high security; observation at the wrong level is a compile
error.  Operations on `Faceted<a>` evaluate both views in
parallel and propagate per-view results.

**Soundness via parametricity.**  Termination-insensitive
noninterference for the faceted fragment is a theorem provable
inside FX via the §6.0 Bridge modality:

```
forall(pub_in: input_t,
       sec_in_1: secret(input_t),
       sec_in_2: secret(input_t)),
  prog(pub_in, sec_in_1).public == prog(pub_in, sec_in_2).public
```

A polymorphic function over Faceted values must produce a
Faceted value whose public component is parametric in the secret
components — exactly the Algehed-Bernardy ICFP 2019 free
theorem.

Per-policy declassification (`declassify_facet`) operates per
named policy rather than per value, matching the §12.4
declassification discipline.


## 13. State Machines

The `machine` construct is where all of FX's capabilities converge.
A machine declaration defines states with typed data, transitions
with guards and effects, and properties the compiler verifies.  The
current state is tracked in the type — invalid transitions are
compile errors.

### 13.1 Declaration

```
machine ConnectionState
  state Disconnected;
  state Connecting of { host: string; attempt: nat };
  state Connected of { socket: socket_handle };
  state Error of { last_error: connect_error; retries: nat };

  transition connect : Disconnected -> Connecting
    requires valid_host(host);
  transition established : Connecting -> Connected;
  transition retry : Connecting -> Connecting
    requires attempt < MAX_RETRIES;
    ensures new.attempt == old.attempt + 1;
  transition fail : Connecting -> Error;
  transition recover : Error -> Connecting
    requires retries < MAX_RETRIES;
  transition close : Connected -> Disconnected;

  initial Disconnected;
  terminal Disconnected;
end machine;
```

Usage — the state is tracked in the type:

```
fn connect_to(host: string) : ConnectionState(Connected) with IO
begin fn
  let conn = ConnectionState.new();           // Disconnected
  let conn = conn.connect(host: host, attempt: 0);  // Connecting
  let conn = conn.established(socket: tcp_connect(host));  // Connected
  conn
end fn;
```

Calling a transition that is invalid from the current state is a
compile error:

```
fn bad(conn: ConnectionState(Disconnected)) : unit
begin fn
  conn.close();   // error: no transition close from Disconnected
end fn;
```

### 13.2 Transition Modifiers

```
requires P            guard — transition enabled iff P holds
ensures Q             postcondition — Q holds after transition fires
with E                effect — transition performs effect E
inverse t'            verified reverse — t; t' restores original state
timeout d -> S        time-triggered fallback
retry n strategy      repeated attempt with backoff
atomic                all-or-nothing execution
idempotent(key: k)    safe to repeat (dedup by key)
commutative           order-independent concurrent firing
monotonic             forward-only in state ordering
emits Event(data)     produces event for other machines
on_fail mode          failure handling (Recoverable / Critical / Atomic)
```

Multiple modifiers compose on a single transition:

```
transition increment : Value -> Value
  ensures new.n == old.n + 1;
  with IO;
  idempotent(key: request_id);
  commutative;
  monotonic;
```

### 13.3 Inverse Transitions

An `inverse` pairs a transition with its reverse.  The compiler
proves that the composition restores the original state:

```
machine BankTransfer
  state Initiated of { amount: i64; from: account; to: account };
  state Debited of { amount: i64; from: account; to: account };
  state Credited of { amount: i64; from: account; to: account };
  state Complete;

  transition debit : Initiated -> Debited with IO
    ensures from.balance == old.from.balance - amount;
    inverse restore_debit : Debited -> Initiated
      ensures from.balance == old.from.balance + amount;

  transition credit : Debited -> Credited with IO
    ensures to.balance == old.to.balance + amount;
    inverse restore_credit : Credited -> Debited
      ensures to.balance == old.to.balance - amount;

  transition finalize : Credited -> Complete;

  initial Initiated;
  terminal Complete;
end machine;
```

If `credit` fails at runtime, the compiler knows the compensation
chain: `restore_debit`.  The chain is derived from inverse
declarations, not manually coded.

**Interaction with `errdefer` in transition bodies.** A transition
whose action body uses local `defer` or `errdefer` statements
(§7.11) is unwound in this order on Fail/Exn:

 1. The local defers and errdefers inside the transition body run
    first, in LIFO order within the body.
 2. Then the inverse compensation chain declared on the enclosing
    machine runs, walking back to the state at which the failed
    transition started.

The rationale is that errdefer handles resources acquired by the
transition itself (local scope), while `inverse` handles the
machine-level state change.  Local cleanup finishes before
machine-level compensation because the inverse transition may need
a consistent local state to operate.

### 13.4 Composition

Six operations combine machines.

**Product** — parallel, independent:

```
machine SystemMonitor = HealthCheck * MetricsCollection * AlertManager;
```

State is the product of component states.  Transitions interleave.

**Synchronized product** — parallel with sync points:

```
machine Device = DataPath *sync(pause, resume) ControlPath;
```

Components synchronize on named events.

**Sequence** — one then another:

```
machine Pipeline = Parse >> Validate >> Transform >> Store;
```

Terminal data of the first feeds initial data of the second.

**Choice** — one of several:

```
machine Payment =
  match method;
    Card => CardPayment;
    Bank => BankTransfer;
  end match;
```

**Loop** — repeat:

```
machine Batch = ProcessItem *{ while queue_not_empty };
```

**Nest** — hierarchical:

```
machine Driver
  state Running of { sub: RunningSubState };

  machine RunningSubState
    state Idle;
    state Processing of { job: job_handle };
    transition start_job : Idle -> Processing;
    transition complete : Processing -> Idle;
    initial Idle;
    terminal Idle;
  end machine;

  transition suspend : Running -> Suspended
    requires sub.state is Idle;
end machine;
```

### 13.5 Properties

Properties are ordinary `assert` statements (§10.4) in the machine
body.  A property is a formula in past-free propositional LTL over
the machine's execution trace, represented as a sized codata stream
(§3.5, size dimension 20 per §6.3).  Four LTL primitives live in
the standard library module `std/ltl`; there are no new keywords
and no new grammar productions.

```
// After: open std/ltl;
//
// G<M: machine>(phi) : Prop<omega, State(M)>  — globally
// F<M: machine>(phi) : Prop<omega, State(M)>  — finally
// X<M: machine>(phi) : Prop<omega, State(M)>  — next step
// phi U psi         : Prop<omega, State(M)>   — strong until
```

`G`, `F`, `X`, `U` are ordinary FX functions imported from
`std/ltl`.  They are defined as sized codata over the machine's
trace and type-check under §3.5's `with Productive` + guarded
recursion rules.  Weak until (`W`) and bounded-future operators are
library-level additions, not primitives.  Write `G(phi) or (phi U
psi)` for weak until and `exists n : nat { n <= d }. phi_at(n, t)`
for a bounded future — both are explicit rather than sugared,
following the rigor-first rule (§1.1, Appendix E).

**Past operators live in `std/ltl/past`** as a separate library:
`P` (previously), `S` (since), `H` (historically), `Y`
(yesterday).  Opt-in via `open std/ltl/past;`.  Formulas
containing past operators lift out of the past-free fragment —
they are no longer decidable by Vardi-Wolper automaton product
(§13.5 decidability table) and discharge via semi-decidable SMT
instead, with the timing cost this implies.

For most use cases a ghost monotonic history variable keeps the
property in the decidable fragment:

```
// Semi-decidable past (library):
open std/ltl/past;
assert G(modified ==> P(reset));

// Decidable ghost history (recommended):
ghost reset_happened : atomic(bool);
invariant modified ==> reset_happened.load();
assert G(modified ==> reset_happened.load());
```

The library form is ergonomic when past reasoning is
occasional; the ghost form is preferred for properties that
drive release-grade verification.

Structural predicates are library functions in `std/machine_props`:

```
fn deadlock_free<M: machine>(m: M) : Prop<omega, State(M)>;
fn deterministic<M: machine>(m: M) : Prop<omega, State(M)>;
fn bounded_size<M: machine>(m: M, n: nat) : Prop<omega, State(M)>;
fn reachable<M: machine>(m: M, s: State(M)) : Prop<omega, State(M)>;
```

Fairness assumptions are library predicates used via implication —
there is no `fair_leads_to` or `progress` sugar:

```
fn weak_fair<M: machine>(t: transition(M)) : Prop<omega, State(M)>;
fn strong_fair<M: machine>(t: transition(M)) : Prop<omega, State(M)>;
```

Example — the ConnectionState machine of §13.1 with its properties
stated uniformly via `assert`:

```
machine ConnectionState
  open std/ltl;
  open std/machine_props;

  state Disconnected;
  state Connecting of { host: string; attempt: nat };
  state Connected of { socket: socket_handle };
  state Error of { last_error: connect_error; retries: nat };

  transition connect     : Disconnected -> Connecting;
  transition established : Connecting -> Connected;
  transition retry       : Connecting -> Connecting;
  transition fail        : Connecting -> Error;
  transition recover     : Error -> Connecting;
  transition close       : Connected -> Disconnected;

  initial  Disconnected;
  terminal Disconnected;

  // Safety: once Connected, eventually reach Disconnected
  assert G(state is Connected ==> F(state is Disconnected));

  // No orphan Connecting states
  assert G(state is Connecting ==> F(state is Connected or state is Error));

  // Fairness-conditional liveness
  assert weak_fair(close) ==> G(state is Connected ==> F(state is Disconnected));

  // Structural guarantees
  assert deadlock_free(self);
  assert deterministic(self);
end machine;
```

Discharge strategy depends on the state space:

```
Machine shape                             Discharge mechanism          Decidability
───────────────────────────────────────   ───────────────────────────  ──────────────
finite states, no parameters              Vardi-Wolper Büchi           decidable,
                                           automaton product           PSPACE in
                                           (§23.3 machine tests        formula
                                            run exactly this)
parameterized, bounded at comptime        comptime unrolling to each   decidable,
                                           concrete bound              polynomial
parameterized with declared cutoff        symmetry reduction per       decidable
  @[cutoff(n)]                             Emerson-Kahlon 2003         modulo
                                                                       cutoff proof
infinite state, invariant supplied        user `assert always I;`      semi-
                                           + SMT per §10               decidable
infinite state, no invariant              rejected: compile error      n/a
                                           M020 (property undecidable
                                           without @[cutoff] or
                                           inductive invariant)
```

Rigor-first rule: when decidability depends on a fact the compiler
cannot derive, the programmer supplies it explicitly — via
`@[cutoff(n)]` for parameterized machines, a named inductive
invariant for infinite-state cases, or an explicit fairness
assumption in the formula.  The compiler never guesses at the
fragment.

**`@[cutoff(n)]` in v1: user-asserted, Assumed trust.**  The
v1 compiler accepts `@[cutoff(n)]` at face value: it runs
bounded verification at N participants and trusts the cutoff
claim, propagating trust level `Assumed(cutoff_claim)` through
every consumer.  Release builds require acknowledgement via
`@[trust_assumed("cutoff proof via <reference>")]` on a
consuming function, forcing the programmer to name the
authority behind the cutoff (paper, theorem, internal
justification).  The trust_assumed string propagates through
§25.11 supply-chain diff so downstream consumers see who
vouches for the cutoff.  A stdlib catalog of verified cutoff
templates (Emerson-Kahlon 2003 rendezvous, Abdulla et al.
WSTS, Bloem-Jacobs-Khalimov-Konnov-Rubin-Veith-Widder
threshold automata) is planned for v2; templates there upgrade
`Assumed` to `Verified` automatically when the machine matches
the template's signature.  For v1 properties that must reach
Verified trust, supply an inductive invariant instead of
relying on a cutoff.

### 13.6 Refinement

When a specification machine and an implementation machine exist,
the compiler proves the implementation is correct:

```
refinement RequestImpl refines RequestSpec
  via fn(impl_state) => match impl_state;
    Waiting => Waiting;
    CheckCache | Processing | Retrying(_) => Processing;
    CacheHit(r) | Done(r) => Done(response: r);
  end match;
end refinement;
```

Every implementation path maps to a valid specification path.
Caching, retries, and logging are invisible implementation details.

### 13.7 Grade Propagation Through Paths

The graded type system (§6) applies to machine paths.  A transition
is a function from state to state and the App rule `p1 + r * p2`
governs the cost.  A path accumulates grades by summing across
transitions.

```
machine Pipeline
  state A of { x: resource };     // x at grade 1
  state B of { x: resource };     // x still at grade 1
  state C;                         // x consumed, grade 0

  transition step1 : A -> B with IO;   // x passed through
  transition step2 : B -> C;           // x consumed
end machine;
// Path A -> C: x starts at 1, ends at 0 (consumed once).
// Effect: IO (from step1).
```

At terminal states, the compiler verifies that all linear resources
have grade 0.

Refinements accumulate through paths: each transition guard that
was satisfied becomes a known fact in subsequent states.

Effect composition through paths follows the join semilattice.  The
function running a machine needs effects equal to the join of all
possible paths.

### 13.8 Machines and the Twenty-Two Dimensions

Each dimension applies to machine state and transitions.  Rather
than listing each dimension separately, the pattern is uniform: the
dimension's semiring governs how values of that dimension compose
through paths.

Usage tracks resource ownership through states.  Effects accumulate
as the join of all transitions.  Security labels propagate through
state data and the compiler proves no secret leaks across states.
Complexity bounds sum across transitions to give path costs.
Mutation direction constrains which transitions can modify state
fields.  Reentrancy defaults to non-reentrant (a transition cannot
trigger another on the same instance).  Clock domains attach to
states in hardware machines and cross-domain transitions require
synchronizers.

### 13.9 Parameterized Machines

```
machine Queue<a: type, depth: nat>
  state Empty;
  state Partial of { items: array(a, depth); count: nat { count < depth } };
  state Full of { items: array(a, depth) };

  transition enqueue : (Empty | Partial) -> (Partial | Full)
    requires state is not Full;
  transition dequeue : (Partial | Full) -> (Empty | Partial)
    requires state is not Empty;

  initial Empty;
end machine;
```

Type parameters follow function type parameter rules.  Value
parameters must be `comptime`-evaluable.

### 13.10 Concurrency Models

A machine declares how it handles concurrent access:

```
concurrency single_thread;    // default — compile error on concurrent access
concurrency exclusive;        // mutex serialization
concurrency lock_free;        // CAS-based, requires all transitions atomic
concurrency tick_atomic;      // per-tick batch, requires all transitions commutative
```

### 13.11 External Events and Inter-Machine Communication

Externally triggered transitions:

```
on_event remote_close : Connected -> Disconnected;
on_event timeout : Connected -> Disconnected;
```

Every `on_event` must declare behavior for every state (handle,
ignore, or error).

Transitions emit events for other machines:

```
transition fire : Ready -> Firing
  emits Fired(position, direction);
```

Signals from child to parent:

```
on_signal child.Completed(result) => handle_result(result);
```

Interlocks: one machine's state constrains another's transitions:

```
transition launch : Countdown -> Launched
  requires safety.state is Armed;
```

### 13.12 Machine Transformers

Transformers take a machine and produce a new machine with
additional behavior:

```
intercept(M, before, after)    wrap transitions with hooks
guard(M, predicate)            add preconditions to transitions
effect(M, handler)             add an effect to transitions
monitor(M, observer)           observe without changing behavior
restrict(M, predicate)         remove transitions matching predicate
extend(M, states, transitions) add new states and transitions
```

Practical cross-cutting concerns as transformer compositions:

```
machine LoggedOrder = intercept(OrderFlow,
  before: fn(t, from, _) => log(f"[Order] {from} --{t}-->"),
  after: fn(t, _, to, _) => log(f" {to}"),
);

machine SecureOrder = guard(OrderFlow,
  fn(t, _, _) => current_user.has_permission(t),
);

machine ResilientOrder = OrderFlow *sync(fail) FailureCounter;

machine ProductionOrder =
  OrderFlow
  |> guard(permission_check)
  |> intercept(logger)
  |> monitor(metrics);
```

### 13.13 Machine Collections

Dynamic sets of machines created and destroyed at runtime:

```
type machine_set(M);

fn spawn(ref mut set: machine_set(M), data: M.initial_data) : machine_id;
fn destroy(ref mut set: machine_set(M), id: machine_id) : unit;
fn get(ref set: machine_set(M), id: machine_id) : option(ref M(*));
fn query(ref set: machine_set(M), pred: M(*) -> bool) : list(machine_id);
fn for_each(ref mut set: machine_set(M), f: fn(ref mut M(*)) -> unit) : unit;
```

Machines in a collection are linear — `spawn` creates, `destroy`
consumes.  A machine must be in a terminal state to be destroyed.
Dropping the collection destroys all contained machines.

### 13.14 Actors

Each actor is a machine processing typed messages.  The compiler
verifies exhaustive message handling per state:

```
actor UserSession
  machine State
    state LoggedOut;
    state LoggedIn of { user: user; last_active: timestamp };
    state Idle of { user: user; idle_since: timestamp };
  end machine;

  receive Login(credentials) when LoggedOut => login(credentials);
  receive Request(data) when LoggedIn => handle_request(data);
  receive Tick when LoggedIn => check_idle_timeout();
  receive Tick when Idle => check_session_timeout();
  // compile error if any (message, state) pair is unhandled
end actor;
```

### 13.15 Timed Transitions and Priority

Transitions that fire after a duration:

```
transition timeout : Waiting -> Error
  after 30 seconds;

transition heartbeat : Active -> Active
  after 5 seconds;
  cancels timeout;
```

`after` durations are measured in logical ticks for reproducibility.
Wall-clock durations convert to ticks via the system tick rate.

Priority for real-time scheduling:

```
machine CriticalHandler
  priority 0;     // highest — runs first, preempts lower
end machine;

machine BackgroundTask
  priority 10;    // lower — yields to higher
end machine;
```

Preemption relationships form a DAG (no circular preemption).

### 13.16 Transition Failure Model

What happens when a guard passes but the action fails:

```
transition send_data : Connected -> Connected
  with IO;
  on_fail Recoverable => stay;
  // machine stays in current state, caller gets error

transition init_hw : Probed -> Initialized
  with IO;
  on_fail Critical => goto Error;
  // machine moves to error state

transition write_both : Active -> Active
  with IO;
  on_fail Atomic => rollback;
  // undo partial work via inverse chain
```

`on_fail` is mandatory for transitions with effects.  Pure
transitions cannot fail.

### 13.17 Cross-Machine Invariants

Properties spanning multiple machines, verified after every
transition in any participant:

```
invariant player_count_stable(ref world: machine_set(PlayerState))
  : count(world, fn(p) => p.state is Alive)
  + count(world, fn(p) => p.state is Dead)
  == INITIAL_PLAYER_COUNT;

invariant consistent_balance(ref ledger: Ledger, ref accounts: machine_set(Account))
  : ledger.total == sum(accounts, fn(a) => a.balance);
```

### 13.18 Temporal Logic for Hardware

Hardware signals are sized codata (§3.5) at size `omega` — a
clocked register stream produces an observation every rising clock
edge, forever.  Temporal properties over hardware are LTL formulas
over these sized streams, using the same `std/ltl` primitives
(`G`, `F`, `X`, `U`) as machine properties in §13.5.  There is no
separate hardware temporal logic; `machine` and `hardware` share
the same four operators.

```
open std/ltl;

lemma mutual_exclusion(ref circuit: arbiter)
  ensures G(popcount(circuit.grant) <= 1);

lemma liveness(ref circuit: handshake)
  ensures G(circuit.req ==> F(circuit.ack));
```

The grounding via sized codata is formal, not metaphorical: each
destructor step on the signal stream corresponds to one clock
cycle; `G` quantifies over the `omega` stream of cycles; `F`
searches for a witness cycle.  Productivity of the hardware-signal
codata (`with Productive` per §3.5) is exactly the forward-progress
requirement for hardware — combinational cycles fail the size-grade
check and are rejected at compile time.

Discharge follows §13.5's decidability table.  Bounded hardware
properties (finite state space, finite register widths) go to
bounded model checking via Vardi-Wolper.  Unbounded properties over
parameterized hardware (buses of arbitrary width, for instance)
require user-supplied inductive invariants or `@[cutoff(n)]`
annotations per §13.5.

### 13.19 Bisimulation

For proving that an implementation simulates a specification:

```
bisimulation codegen_correct
  relates R: asm_state -> source_state -> bool;
  initial: R(asm_init(compiled), source_init(program));
  step: forall(sa: asm_state, ss: source_state),
          R(sa, ss) ==> R(asm_step(sa), source_eval(ss));
end bisimulation;
```

Bisimulation is the proof technique for hardware verification
(RTL simulates ISA), compiler verification (compiled code simulates
source), and protocol verification (implementation simulates
session type).

### 13.20 Snapshots and Atomic Chains

Machine state can be saved and restored:

```
let snapshot = m.snapshot();
// ... tentative work ...
let m = snapshot.restore();
```

Multi-machine atomic chains: either all transitions succeed or all
are rolled back via inverses:

```
atomic
  inventory.remove(slot: 3);
  weapon.reload(ammo: item);
end atomic;
```

### 13.21 Observable State

```
let current = m.state;
let available = m.available_transitions();
let can_submit = m.can_transition(submit);
```

`m.state` borrows the machine for reading without consuming it.
For REST APIs, `available_transitions()` generates HATEOAS links.
For UIs, it determines which buttons are enabled.

### 13.22 Machines and UI

A UI is a pure function from machine state to view.  The compiler
verifies that every state has a rendering (exhaustive match) and
that the available transitions correspond to enabled UI actions.

```
machine ShoppingApp
  state Browse of { catalog: ref catalog; cart: cart };
  state ProductDetail of { product: product; cart: cart };
  state Cart of { items: list(cart_item) };
  state Checkout of {
    items: list(cart_item) { length(items) > 0 };
    shipping: option(address);
    payment: option(payment_method);
  };
  state Processing;
  state Confirmation of { order: confirmed_order };
  state Error of { from_state: ShoppingAppState; error: app_error };

  transition view_product : Browse -> ProductDetail;
  transition add_to_cart : ProductDetail -> Browse
    ensures new.cart == old.cart.add(product);
  transition view_cart : Browse -> Cart;
  transition begin_checkout : Cart -> Checkout
    requires length(items) > 0;
  transition set_shipping : Checkout -> Checkout
    ensures new.shipping == Some(addr);
  transition set_payment : Checkout -> Checkout
    ensures new.payment == Some(method);
  transition place_order : Checkout -> Processing
    requires shipping is Some and payment is Some;
  transition order_confirmed : Processing -> Confirmation;
  transition back : (ProductDetail | Cart | Checkout) -> Browse;
  transition dismiss_error : Error -> from_state;

  initial Browse;
  terminal Confirmation;

  // UX guarantees — compiler PROVES:
  always (state is not (Confirmation | Processing))
    ==> can_transition(back) or can_transition(dismiss_error);
  // user can always go back

  unreachable (state is Checkout and length(items) == 0);
  // cannot checkout with empty cart

  unreachable (state is Processing
    and (shipping is None or payment is None));
  // cannot charge without address and payment

  (state is Error) leads_to (state is not Error);
  // every error is recoverable

  reachable Confirmation from Browse;
  // purchase path exists
end machine;
```

Rendering:

```
fn render(state: ShoppingApp(*)) : view
= match state;
    Browse(catalog, cart) => browse_view(ref catalog, ref cart);
    ProductDetail(product, cart) => product_view(ref product, ref cart);
    Cart(items) => cart_view(ref items);
    Checkout(items, shipping, payment) => checkout_view(
      ref items, ref shipping, ref payment,
      submit_enabled: shipping is Some and payment is Some,
    );
    Processing => loading_view();
    Confirmation(order) => confirmation_view(ref order);
    Error(_, error) => error_view(ref error);
  end match;
// exhaustive: every state has a view, no blank screens
```

Available transitions drive the UI:

```
fn render_buttons(state: ShoppingApp(*)) : list(button)
= state.available_transitions()
  |> map(fn(t) => button { label: t.name, enabled: true, action: trigger(t) });
```

For REST APIs, the same mechanism generates HATEOAS links:

```
fn api_response(state: OrderMachine(*)) : json
= json {
    state: state.name(),
    data: state.data(),
    links: state.available_transitions()
      |> map(fn(t) => link { rel: t.name, href: f"/orders/{id}/{t.name}" }),
  };
```

### 13.23 Event Sourcing

With `@[event_sourced]`, the compiler generates event types and
replay logic from the machine declaration:

```
@[event_sourced]
machine BankAccount
  state Active of { balance: i64 };
  state Frozen of { balance: i64; reason: string };
  state Closed;

  transition deposit : Active -> Active
    ensures new.balance == old.balance + amount;
  transition withdraw : Active -> Active
    requires amount <= balance;
  transition freeze : Active -> Frozen;
  transition close : (Active | Frozen) -> Closed
    requires balance == 0;

  initial Active(balance: 0);
  terminal Closed;
end machine;
```

The compiler generates: the event type (`Deposit(amount) |
Withdraw(amount) | Freeze(reason) | ...`), the `apply_event`
function, the `rebuild` function that folds over an event log,
and a proof that `rebuild(events) == live_state`.

### 13.24 Machines as IxMonad

State machines are not a separate calculus — they are an
**indexed-monad** instance (§30.10).  Every transition `t :
S_in -> S_out` is an `ibind` step in the IxMonad whose state
set is the machine's enumeration of states.  Sessions, machines,
transactions, and mutex blocks share this single calculus:

```
instance IxMonad for Machine<S_in, S_out, T>
  fn ireturn<S, a>(x: a) : Machine<S, S, a> = ...;
  fn ibind<S_in, S_mid, S_out, a, b>(
      m: Machine<S_in, S_mid, a>,
      f: a -> Machine<S_mid, S_out, b>,
  ) : Machine<S_in, S_out, b> = ...;
end instance;
```

Sequential composition of two transitions is `ibind`; choice is
`match` over the source state; product machines (§13.4 `*`)
correspond to IxMonad pair composition.  Machine refinement
(§13.6) is preservation of the IxMonad's per-state semantics
under a state-mapping homomorphism.  Bisimulation (§13.19)
follows from the LICS 2025 effectful-Mealy bisimulation result
lifted to IxMonad laws (Bonchi-Di Lavore-Román, CALCO 2025).

Practical implications:

  * A compiler that has implemented IxMonad already has machine
    typing for free — the per-machine kernel rule is a single
    instance-derivation step.
  * Generic combinators over IxMonad (transformers, monad
    transformers, lifting) apply to machines automatically:
    `LoggedOrder = intercept(OrderFlow, before, after)` is an
    IxMonad transformer composition.
  * The same mechanism unifies sessions and machines at the
    kernel level — `session<P_in, P_out>` and `Machine<S_in,
    S_out>` differ only in their state-set parameter.


## 14. Contracts

A contract governs how a type behaves when it crosses a boundary.
Types define structure.  Formats define encoding.  Machines define
behavior.  Contracts are the rules for data crossing boundaries
between independently-evolving systems.

A boundary is anywhere two systems meet: client and server (network),
application and database (persistence), CPU and device (MMIO),
module and module (API surface), version N and version N+1 (time).
At every boundary: what is the data shape, how is it encoded, is
it valid, who can access what, what if the other side is older,
what if it fails.

### 14.1 Contract Declaration

```
contract UserApi for UserRecord

  version 1 { id: nat; name: string; email: string };
  version 2 { id: nat; name: string; email: string; role: Role }
    migration add role default User;
  version 3 = UserRecord
    migration add created default epoch;

  compatibility {
    v1 -> v2 : backward;
    v2 -> v3 : backward;
    v3 -> v1 : not_compatible;
  };

  access id      : read_only;
  access role    : requires auth(Admin);
  access created : read_only;

  format json {
    id      : "id" as number;
    name    : "name" as string;
    email   : "email" as string;
    role    : "role" as string_enum;
    created : "created_at" as string_iso8601;
  };

  format protobuf {
    id      : 1 as uint64;
    name    : 2 as string;
    email   : 3 as string;
    role    : 4 as enum;
    created : 5 as google_protobuf_timestamp;
  };

  errors {
    InvalidEmail(string);
    NameTooLong(max: nat, actual: nat);
    Unauthorized;
    VersionMismatch(expected: nat, got: nat);
  };

  invariant name.length > 0;
  invariant role == Admin ==> email.ends_with("@company.com");

end contract;
```

A type can have multiple contracts for different boundaries:

```
contract UserStorage for UserRecord
  access id    : write_once auto_increment;
  access email : unique;

  format sql {
    table "users";
    id      : integer primary_key;
    name    : varchar(255) not_null;
    email   : varchar(255) not_null unique;
    role    : varchar(20) not_null default 'User';
    created : timestamp not_null default now();
  };
end contract;

contract UserEvent for UserRecord
  format protobuf {
    id: 1 as uint64; name: 2 as string;
    email: 3 as string; role: 4 as enum;
    created: 5 as google_protobuf_timestamp;
  };
end contract;
```

### 14.2 Versioning and Migration

Each version defines the shape of the data at that point.
Migrations define transforms between versions.  The compiler
proves each migration is total — every valid input maps to a valid
output.

```
contract OrderContract for OrderRecord
  version 1 { id: nat; items: list(item); total: money };
  version 2 { id: nat; items: list(item); total: money;
               tax: money; status: OrderStatus }
    migration 1 -> 2 {
      add tax default 0;
      add status default Pending;
    };
  version 3 { id: nat; items: list(item); subtotal: money;
               tax: money; total: money; status: OrderStatus;
               region: Region }
    migration 2 -> 3 {
      rename total -> subtotal;
      add total computed subtotal + tax;
      add region default Region.Unknown;
    };
end contract;
```

Migration operations and their compatibility:

```
add F default D          backward compatible
remove F                 forward only
rename F -> G            migration required
alter F : T1 -> T2       migration required
add computed F = expr    backward compatible
reorder fields           backward compatible
```

**Migration as transport along a Wire-mode equivalence.**  A
migration is operationally a generated function `migrate :
v_k → v_{k+1}` proved total, but the deeper semantics is
**transport along a univalence equivalence at the Wire mode**
(§6.0, Appendix H.7a).  Each contract version `v_k` is a type
at `Wire`; each migration is an equivalence
`v_k ≃ v_{k+1}` whose forward function is the migration
itself, backward function is the inverse migration (when
declared `backward` in the compatibility matrix), and unit /
counit witness round-trip:

```
let equivalence_v_k_v_kplus1 : equiv(v_k, v_kplus1) =
  equiv {
    forward:  migrate_v_k_to_v_kplus1,
    backward: migrate_v_kplus1_to_v_k,        // when bidirectional
    unit:     fn(x: v_k)     => backward(forward(x)) == x,
    counit:   fn(y: v_kplus1) => forward(backward(y)) == y,
  };
```

Modal univalence at Wire (kernel axiom Appendix H.7a) gives
`Id (Type @ Wire) v_k v_{k+1}` from this equivalence; the
**transport** primitive `transport e x : v_{k+1}` then runs
the migration *and computes* — `transport (refl v_k) x` reduces
to `x`, `transport (e_k_to_kplus1) x` reduces to
`migrate_v_k_to_v_kplus1(x)` per the equivalence's forward
function.

```
let user_v1 : UserApi.v1 = decode_v1(raw);
let user_v2 : UserApi.v2 = transport UserApi.eq_v1_v2 user_v1;
// transport β-reduces to migrate_v1_v2(user_v1)
```

**Why this matters.**  The version-compatibility matrix
(`v1 -> v2 : backward`, etc., §14.1) becomes derivable from
the equivalence rather than separately declared: a migration
admits a backward direction iff the equivalence is *bidirectional*,
which the compiler verifies from the migration body's structure.
Round-trip laws fall out of the equivalence axioms; the
generated `C.migrate(val, from, to)` operation (§14.5) is just
the transport call composed with explicit version arguments;
contract refinement (§14.10's automatic version computation)
becomes a check on the equivalence's properties (preserves
required fields → MAJOR safe; adds optional fields →
MINOR).

The contract-boundary-restricted univalence (§6.9, Appendix H.7a)
keeps the discipline practical: contract migration is the one
place the type theory needs propositional equality on types as a
first-class object, and restricting it to the contract boundary
avoids cubical-evaluation overhead on the runtime hot path.

### 14.3 Access Mode Algebra

Access modes generalize across all domains — hardware registers,
database columns, API fields, configuration:

```
ReadWrite               unrestricted
ReadOnly                writes rejected
WriteOnly               reads rejected (passwords, keys)
WriteOnce               write once, then read-only
AppendOnly              add only, never remove
Monotonic of order      value only increases in partial order
Guarded of predicate    write requires predicate to hold
Unique                  globally unique across instances
RuntimeConst            set at init, immutable after
HotReload               changeable at runtime without restart
Ephemeral               valid for one use, consumed on read
AutoIncrement           system-assigned (databases)
Deprecated of version   accessible but warns about removal
W1C  W1S  RC  RSVD     hardware register modes (§18.3)
```

The compiler checks access rules at every boundary crossing.

### 14.4 Format Bindings

Formats define encoding rules.  Contracts bind formats to types:

```
format json_defaults
  nat       -> number;
  string    -> string;
  bool      -> boolean;
  option(T) -> nullable(T);
  list(T)   -> array(T);
  enum      -> string;
  timestamp -> string_iso8601;
  money     -> string_decimal;
end format;

contract MyApi for MyRecord
  format json = { ...json_defaults,
    created : "created_at",
    role    : lowercase
  };
end contract;
```

Format override uses the same spread syntax as record update
(rule 16, §3.4).  `{...base, field: value}` takes `base`'s bindings
and overrides the named fields.  Left-to-right: later fields
override earlier.  There is no `with` form for format override —
`with` is reserved for effect annotations (rule 17).

### 14.4.1 WIT Lowering (WebAssembly Component Model)

The Wire-mode `serialize ⊣ parse` adjunction (§6.9) has a
canonical operational target: WebAssembly Interface Types
(WIT), the language-agnostic IDL of the WebAssembly Component
Model.  WIT-typed FX modules interoperate with Rust, Go,
JavaScript, Python on equal footing through the Component
Model's canonical ABI.

A contract opts in via `format wit;`:

```
contract UserApi for UserRecord
  version 1 { id: nat; name: string; email: string };
  format wit;
end contract;
```

The compiler emits a WIT specification per contract:

```wit
package fx:user-api@1.0.0;

interface user-api {
  record user {
    id: u64,
    name: string,
    email: string,
  }
  decode: func(raw: list<u8>) -> result<user, decode-error>;
  encode: func(value: user) -> list<u8>;
  variant decode-error {
    invalid-utf8,
    schema-mismatch,
    field-missing(string),
  }
}
```

**Lowering rules** (FX type → WIT type):

```
nat ≤ 256 ↦ u8;     nat ≤ 2^16 ↦ u16;  nat ≤ 2^32 ↦ u32;  nat ≤ 2^64 ↦ u64
i8/i16/i32/i64    ↦ s8/s16/s32/s64
string            ↦ string
bool              ↦ bool
list(T)           ↦ list<T'> where T' is the lowering of T
option(T)         ↦ option<T'>
result(T, E)      ↦ result<T', E'>
record { f: T }   ↦ record { f: T' }
variant V(T) | W  ↦ variant { v(T'), w }
```

A type that has no WIT lowering (arbitrary-precision `int`,
function value, higher-rank polymorphic type) requires explicit
projection to a finite-width approximation declared by the
contract author.

**Soundness.**  The WIT lowering is sound when the canonical-ABI
encoding round-trips: encode then decode is the identity on
well-formed values, and decode then encode is the identity on
well-formed bytes.  This is the *unit law of the serialize/parse
adjunction* (§6.9) instantiated at WIT.  The compiler-generated
validators (§14.5) witness the law for FX-typed values.

**Async crossing.**  WASI 0.3 native async makes FX's `Async`
effect a peer of WASI's async type.  An FX function with
`with Async` that crosses a WIT boundary lowers to an async
WIT signature:

```wit
decode-stream: async func(raw: stream<list<u8>>) -> result<user, decode-error>;
```

The Async effect's grade arithmetic composes with the WIT async
machinery; the contract still witnesses the round-trip law per
event.

Cross-language consumers generate FX-shaped bindings via
`wit-bindgen`; the FX side requires no language-specific tooling.

### 14.5 Generated Operations

From one contract declaration, the compiler generates:

```
C.decode(fmt, raw) : result(T, C.errors)     deserialize + validate
C.encode(fmt, val) : bytes                     serialize
C.validate(val) : result(T, C.errors)         check constraints
C.migrate(val, from, to) : result(T, error)   version transform
C.compatible(v1, v2) : compatibility           version compatibility
C.project(fmt) : schema                        external schema (OpenAPI, DDL, .proto)
```

### 14.6 Contracts and Effects

Effects that cross boundaries (IO, DB, Network, MMIO) trigger
contract enforcement.  Uncontracted data at a boundary is a compile
error:

```
fn handle_request(raw: bytes) : bytes with Fail(api_error), IO
begin fn
  let user = UserApi.decode(json, raw);
  // compiler generates: deserialize + validate + access check + version migrate

  UserStorage.insert(db, user);
  // compiler generates: parameterized INSERT, auto_increment excluded

  UserEvent.emit(bus, UserCreated(user));
  // compiler generates: protobuf serialize

  Ok(UserApi.encode(json, user))
end fn;
```

### 14.7 Contracts and Machines

Machine state data governed by contracts evolves via migration:

```
machine OrderFlow
  state Draft of { order: OrderRecord version 1 };
  state Submitted of { order: OrderRecord version 2 };

  transition submit : Draft -> Submitted
    // data migrates v1 -> v2 via OrderContract.migration(1, 2)
    ensures order.status == Pending;
end machine;
```

Event sourcing with contracts: replaying old events applies contract
migrations automatically.

### 14.8 Contracts and Sessions

Session messages carry contracted data:

```
session PurchaseProtocol
  send(request: PurchaseRequest via PurchaseApi);
  branch
    approved => receive(confirmation: Confirmation via PurchaseApi); end;
    declined => receive(reason: Decline via PurchaseApi); end;
  end branch;
end session;
```

Every message is serialized according to the named contract's format,
validated on receive, and version-negotiated at session establishment.

### 14.9 Contract Inheritance

```
contract BaseEntity for T
  access id      : write_once auto_increment;
  access created : write_once;
  access updated : auto_managed;
end contract;

contract UserStorage for UserRecord
  extends BaseEntity;
  access email : unique;
  format sql extends sql_base { ... };
end contract;
```

### 14.10 Automatic Version Computation

The compiler computes the semantic version from the contract diff
when publishing a package (§25.6).  The rules:

```
Removed symbol                    MAJOR
Added symbol                      MINOR
requires strengthened              MAJOR
requires weakened                  MINOR
ensures strengthened               MINOR
ensures weakened                   MAJOR
Effect added to function           MAJOR
Effect removed from function       MINOR
Required field added               MAJOR
Optional field added               MINOR
```

The direction rules follow subtyping: contravariant on inputs
(weaker precondition is safe), covariant on outputs (stronger
postcondition is safe).


## 15. Code Versioning and Migration

Versions solve the Theseus ship problem for code.  When a module
evolves — its algorithm changes, its spec strengthens, its
interface reshapes — callers should not have to migrate in
lockstep.  Old and new implementations coexist, each with a
verified spec, and callers migrate independently while the
compiler verifies adapters that bridge the versions.  The effort
to evolve a library used by fifty modules is O(new version), not
O(fifty callers).

This chapter defines the mechanism.  It reuses §13 machines for
migration tracking, §14 contracts for data crossing versions,
§10 verification for adapter correctness, and §6 graded types to
carry a value's version through the program.  No new proof
theory.  The contract system (§14.10) already versions data;
this chapter versions the code that produces and consumes it.

### 15.1 The Refactoring Nightmare

Three patterns exhaust current industry practice and all three
cost O(existing callers) in coordination.

Big-bang rewrite.  Replace v1 atomically.  Every caller must
update in the same commit.  A missed case ships a regression.
Viable for small teams and breaks at scale.

Strangler fig.  Ship v2 alongside v1, gradually redirect
callers, eventually remove v1.  The programmer maintains both
implementations by hand, tracks which callers have migrated,
and verifies compatibility with test suites.  Coordination
overhead scales with caller count.

Feature flags.  Compile v2 behind a flag enabled per
deployment.  Produces a combinatorial matrix of live code paths
and a long-lived flag that rots.

FX collapses all three into one mechanism: versioned
declarations with compiler-verified refinement or named
migration.  v1 and v2 both exist in the source.  Callers bind
to whichever spec they rely on.  The compiler proves v2 refines
v1 or a named migration bridges them.  Callers migrate at their
own pace and the compiler tracks progress as a machine (§15.9)
that provably terminates with no caller lost.

### 15.2 Version as a Grade

The version label is a grade dimension — the 21st, joining the
twenty of §6.3 to form the full grade vector.  Unlike the Tier S
semirings and Tier L lattices, Version lives in its own Tier V
(§6.3): it has no multiplicative composition, only a consistency
check at each site resolved through adapter resolution (§15.4
refines, §15.6 migration).  The grade is erased at codegen — by
§15.8 the compiler resolves a single concrete version per
symbol — but the lattice-with-adapter structure is checked
during elaboration.

The typing rule extends §6.2's Let:

```
G |-_p1 e : T @ version(k)    G, x :_r T @ version(k) |-_p2 body : S
---------------------------------------------------------------------
G |-_(r * p1 + p2) let x = e; body : S
```

A value produced at version k flows to a consumer at version k.
If producer and consumer bind to different versions, the
compiler looks for a verified adapter (§15.6); absent one, the
program is rejected.  This is Lambda VL's version coeffect
(Tanabe et al., 2021-2023) adapted to FX's 22-dimension vector.

Version composes pointwise with the other dimensions.  A
linear, IO-performing, classified, version(2) value satisfies a
consumer iff every dimension aligns or adapters bridge the
mismatches.  The full grade vector is twenty-two wide.

### 15.3 Versioned Function Declarations

Every function carries a version label.  Declarations without
an explicit label are implicitly `@[version(1)]`:

```
fn sort<a>(xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r) and is_permutation(xs, r);
= ... merge sort ... ;
// implicitly @[version(1)]
```

A new version reuses the name with an explicit version
attribute and declares its relationship to the prior version:

```
fn sort<a> @[version(2)] (xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r) and is_stable(r)
            and is_permutation(xs, r);
= ... stable merge sort ... ;

refines sort@2 sort@1;
```

Rules:

 1. Version numbers are positive integers, monotonically
    increasing with no gaps.  `@[version(3)]` without a prior
    `@[version(2)]` is a compile error.
 2. All declared versions compile and ship — the binary contains
    every live version, subject to the dead-version GC of
    §15.12.
 3. Spec-hash identity (§10.15) is computed per version.  Two
    implementations of `sort@1` with identical pre/post/effects/
    modes have the same spec hash and are interchangeable
    implementations; callers bind to the hash, not the body.
 4. Versions attach to declarations, not modules.  A module may
    hold `sort@1`, `parse@1-3`, and `validate@1` with
    independent histories.

### 15.4 Refinement Between Versions

The `refines` declaration asserts that v2 is a behavioral
subtype of v1.  The compiler discharges four obligations via
§10 verification:

```
refines sort@2 sort@1;

//   1. pre_v1(args)      ==> pre_v2(args)        (inputs contravariant)
//   2. post_v2(args, r)  ==> post_v1(args, r)    (outputs covariant)
//   3. effects(v2) ⊆ effects(v1)                  (capabilities narrowed)
//   4. modes(v2) relaxes modes(v1)                (caller gives up less)
```

When all four obligations hold, v2 is a drop-in replacement.
The compiler emits an implicit identity adapter; callers bound
to v1's spec automatically dispatch to v2's implementation with
zero source-level change at the call site.

The refinement check reuses the SMT machinery of §10.1-§10.2,
respects §10.15's opaque-by-default function boundaries (the
bodies of v1 and v2 are not visible to each other's caller
proofs), and is subject to §10.12 proof-stability tracking.
Refinement between `@[transparent]` functions additionally
exposes bodies for cross-version inductive proof.

When `refines` is omitted, v2 stands alone with no declared
relation to v1.  Callers bound to v1 do not automatically use
v2; they require a named migration (§15.6) or an explicit
upgrade.

### 15.5 The Per-Dimension Compatibility Table

For each grade dimension, the compatibility table lists which
changes count as refinement (free migration) versus which
require a named adapter or break compatibility.  The compiler
iterates this table when discharging the four obligations of
`refines`.

```
Dim  Name              Refinement (v2 replaces v1)        Requires adapter
───  ─────────────     ─────────────────────────────      ────────────────────────
 1   Type              identical signature                 signature reshape
 2   Refinement        pre weakened, post strengthened     pre strengthened,
                                                            post weakened
 3   Usage             own → ref, linear → affine,         affine → linear,
                       ref mut → ref                        ref → own
 4   Effect            effects narrowed                    effects widened
 5   Security          labels preserved                    unclassified → classified
                                                            requires declassify policy
 6   Protocol          covariant branches, contravariant   new required message steps,
                       selects (Gay-Hole subtyping)         incompatible dual
 7   Lifetime          v2 requires ≤ v1 required            v2 requires > v1 required
 8   Provenance        known preserved                     Source → Unknown
 9   Trust             Verified ≥ Tested ≥ Sorry            any drop rejected
10   Representation    identical layout                     layout changed
11   Observability     transparent → opaque                opaque → transparent
                       (more protective)                    (leaks more)
12   Clock domain      identical domain only               any cross-domain change
                                                            (synchronizer required)
13   Complexity        tighter bound                       looser bound
14   Precision         tighter error bound                 looser error bound
15   Space             allocates less                       allocates more
                       (Heap → Region → Stack)              (Stack → Region → Heap)
16   Overflow          wrap → exact if provable             exact → wrap (regression)
                                                            or added Fail effect
17   FP order          reassociate → strict                 strict → reassociate
                       (more deterministic)                 (loses bit-identical)
18   Mutation          read_write → immutable              immutable → read_write
                       (function does less to value)        (function now mutates)
19   Reentrancy        reentrant → non-reentrant           non-reentrant → reentrant
20   Version           label assignment only               —
```

Rule summary: v2 refines v1 iff, for every dimension, v2's
annotation sits at or below v1's annotation in that dimension's
preorder.  "Below" means weaker precondition, stronger
postcondition, fewer effects, less restrictive mode.

Per-dimension diff reports are available via the agent protocol
(§24); `GET /freedom?symbol=sort` enumerates which dimensions
are currently relaxable without breaking callers.

### 15.6 Adapters

When v2 is not a refinement of v1 — a new required parameter
appeared, the return type reshaped, a new error variant was
introduced — the compiler cannot emit an identity adapter.  A
named `migration` declaration provides the bridge:

```
migration parse @1 -> @2 (raw: string) : result(ast, parse_error)
= try Ok(parse@2(raw)) catch e => Err(e) end try;
```

The migration declaration has the same grammar as a function
(`name (params) : type = body;`) plus the `@1 -> @2` version
pair.  The compiler discharges one obligation: the migration's
observable behavior satisfies v1's specification given v2's
actual behavior.

Three adapter classes are compiler-synthesized automatically
without any `migration` declaration:

 1. **Identity adapter.**  v2 refines v1 per §15.4.  The adapter
    is the identity function and is emitted silently.

 2. **Default-filling adapter.**  v2 adds a parameter with a
    compile-time default:
    ```
    fn connect @[version(1)] (host: string) : conn with IO;

    fn connect @[version(2)] (host: string, timeout: nat = 30)
      : conn with IO;

    refines connect@2 connect@1;
    // Compiler synthesizes:
    //   adapter (host: string) : conn with IO
    //   = connect@2(host: host, timeout: 30);
    ```

 3. **Mode-relaxing adapter.**  v2 accepts a weaker mode (e.g.,
    `ref x: T` where v1 took `own x: T`).  Callers of v1 gave
    up ownership; converting ownership to a borrow is always
    safe.  The identity adapter suffices.

All other diff shapes — return type reshape, new required
parameter without default, effect widening, session protocol
extension, machine state split — require a named migration.
The compiler verifies the migration's correctness; it does not
write the body.

### 15.7 Interoperability with Contracts and Machines

Versioned code and versioned data cross boundaries together.

**Data crossing version boundaries.**  When a v2 function is
called with data produced by v1 code, the data flows through a
§14.2 contract migration.  If `UserRecord` has contract versions
1 and 2 and a caller produces v1 data while the callee expects
v2, the compiler inserts `UserApi.migrate(user, from: 1, to: 2)`
at the boundary.  The migration was proved total at contract
declaration time; its insertion is mechanical.

**Machine state crossing version boundaries.**  A versioned
machine uses §13.6's state-mapping refinement:

```
machine OrderFlow @[version(2)]
  state Draft;
  state PendingReview;
  state Approved;
  state Complete;

  migration from @1 via fn(state) => match state;
    Draft => Draft;
    Submitted => PendingReview;
    Complete => Complete;
  end match;

  // Compiler verifies:
  //   - mapping is total over v1 states;
  //   - every v2 invariant holds after migration of each v1 state.
end machine;
```

Live machine instances in v1's `Submitted` state can be migrated
to v2's `PendingReview` at runtime.  Mid-transition migration —
an instance between begin and end of a v1 transition — requires
a **quiescent state** reached by pausing new transitions, or an
explicit **rendezvous point** declared in the machine.  Arbitrary
mid-transition migration is a research-level gap (§15.15).

**Session protocol evolution.**  Adding protocol steps requires
identifying **safe migration points** — protocol states where
both v1 and v2 agree on the next expected message.  This analysis
is preliminary in §11.5.  v1 sessions already past a fork must
complete under v1; new sessions begin under v2.

### 15.8 Version Resolution and Binding

Callers bind to a versioned symbol in one of three styles:

```
// Style 1: pin to a specific version
open Lib @ version(2);
// Consumer uses Lib's symbols at version 2.  If Lib ships v3,
// this consumer is unaffected until it opts in.

// Style 2: spec binding — bind to the latest version whose
// specification refines the consumer's requirement
open Lib where post includes is_sorted;
// Compiler picks the latest version of each Lib symbol whose
// postcondition implies is_sorted(r).  Auto-upgrades when a
// compatible newer version ships.

// Style 3: unversioned (default)
open Lib;
// Equivalent to binding to the latest version that refines
// every earlier version the consumer transitively uses.
```

The resolution algorithm extends §25.5 Minimal Version Selection
with channel and spec constraints:

 1. For each imported symbol, collect all versions across the
    channels allowed by the active profile (§25.12).
 2. Filter by the binding constraint (pin, spec-match, or
    latest-compatible).
 3. Select the maximum version that satisfies the consumer's
    spec requirement and refines or adapts every older version
    the consumer transitively uses.
 4. If no version satisfies, emit a diagnostic naming the
    unsatisfied consumer, the failing version, and the specific
    obligation that could not be discharged.

The resolved version is recorded in `fx.lock` alongside content
hash, trust level, effect summary, and channel tag.

### 15.9 Migration as a Machine

Migration progress from v1 to v2 is itself a state machine.
The compiler generates one automatically for every pair
`@k -> @k+1` where `refines` or `migration` has been declared:

```
machine Migration
  state NotStarted of { v1_callers: nat; v2_callers: nat };
  state InProgress of { v1_callers: nat; v2_callers: nat };
  state Complete;

  transition begin : NotStarted -> InProgress;

  transition migrate_caller : InProgress -> InProgress
    ensures new.v1_callers == old.v1_callers - 1;
    ensures new.v2_callers == old.v2_callers + 1;

  transition finish : InProgress -> Complete
    requires v1_callers == 0;

  initial NotStarted;
  terminal Complete;

  always v1_callers + v2_callers == initial_total;
  eventually Complete;
end machine;
```

`initial_total` is a compiler-computed ghost value capturing the
number of callers at migration start.  The `always` invariant
preserves the sum across every transition — no caller is lost or
duplicated.  The `eventually Complete` property discharges when
the migration is well-formed: every caller can reach the
destination version via refinement or proved adapter, and no
caller is pinned to the source version forever except by
explicit policy.

Progress is queryable via the agent protocol (§24):

```
GET /migration/sort@1->@2
{ "state": "InProgress", "v1_callers": 3, "v2_callers": 44,
  "progress_pct": 93.6,
  "blockers": ["ModuleX pinned to @version(1) via explicit policy"] }
```

### 15.10 Spec-First Evolution

Sometimes the implementation has always exceeded its documented
spec.  Strengthening the spec then requires zero code change.
The compiler detects this via an extension of §10.11 spec
validation:

```
// v1 shipped with a weak postcondition:
fn sort @[version(1)] (xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r);   // stability not claimed
= merge_sort_body;           // but implementation IS stable

// v2 strengthens the spec and reuses v1's body:
fn sort @[version(2)] (xs: list(a)) : list(a)
  where Ord(a);
  post r => is_sorted(r) and is_stable(r);
= merge_sort_body;

refines sort@2 sort@1;
// Compiler: "verifying sort@2 body against strengthened spec...
//            satisfied.  free upgrade; no implementation change."
```

The agent-facing preview:

```
POST /spec-upgrade/preview
{ "symbol": "sort", "new_post": "is_sorted(r) and is_stable(r)" }

{ "current_impl_satisfies": true,
  "callers_affected": 0,
  "code_change_required": false,
  "suggested_action": "declare @[version(2)] reusing current body,
                        add refines @2 @1" }
```

When the existing implementation fails the strengthened spec,
the response includes a counter-example and the concrete code
change required.  Either way, evolution is compiler-guided
from the spec side first.

### 15.11 Test Inheritance

Tests declared against a specification apply to every
implementation satisfying that specification.  When v2 refines
v1, v2 automatically inherits v1's property tests:

```
property sort_preserves_length(xs: list(nat))
= length(sort(xs)) == length(xs);

// The property body references `sort`, which resolves per §15.8
// to the currently-bound version.  When sort@2 ships and refines
// sort@1, the property automatically tests sort@2 without any
// re-declaration.  Inheritance flows through spec-bind
// resolution, not through a new attribute.
```

The `test_migration` keyword generates adapter correctness
tests automatically from the version pair:

```
test_migration sort @1 -> @2
  @[samples(10000)]
  // Auto-generated: for random inputs, run both versions,
  // verify each satisfies its declared spec, verify the v1
  // spec holds on v2's output (refinement), verify the
  // migration-adapter and v2-direct paths produce
  // v1-spec-equivalent outputs.
end test_migration;
```

For named-adapter migrations, `test_migration` additionally
fuzzes the adapter: generate v1 inputs, compute v1 output,
compute v2 output through the adapter, compare for v1-spec
equivalence.

### 15.12 Deprecation, Sunset, and Dead Version GC

Versions signal lifecycle via attributes:

```
fn parse @[version(1)]
  @[deprecated(replacement: parse@2,
                rationale: "v2 validates syntax")]
  (raw: string) : result(ast, error)
= ... ;

fn parse @[version(2)] (raw: string) : ast with Fail(error)
= ... ;

migration parse @1 -> @2 (raw: string) : result(ast, error)
= try Ok(parse@2(raw)) catch e => Err(e) end try;
```

`@[deprecated]` emits a warning at each call site until that
caller migrates.  `@[sunset]` adds a compile-time deadline:

```
fn parse @[version(1)]
  @[sunset(deadline: "2026-09-01", replacement: parse@2)]
  (raw: string) : result(ast, error)
= ... ;

// Before 2026-09-01: warning at call sites.
// On or after 2026-09-01: error at call sites.
// Preview: fxc check --as-of 2026-09-01
//   reports every site that will fail on the deadline.
```

Dead version detection runs continuously.  A version with zero
callers across all channels is eligible for removal:

```
$ fxc gc-versions --dry-run
  sort@1:     0 callers, safe to remove
  parse@1:    2 callers remaining (ModuleX, ModuleY)
  OrderFlow@1: 0 live instances, safe to remove

$ fxc gc-versions --apply
  Removed sort@1, OrderFlow@1 from src/ and fx.lock.
  Contract UserApi migration 1->2 retained (used by parse@1).
```

Removal is rejected if any reference remains unresolved, any
machine instance is not quiescent, or any retained version
still depends on an adapter through the to-be-removed version.

### 15.13 Performance Regression Across Versions

Functional correctness is not the only property worth comparing
across versions.  A v2 that is provably correct but three
times slower on large inputs is a non-functional regression.
The `bench_migration` keyword generates comparative benchmarks:

```
bench_migration sort @1 -> @2
  @[sizes(100, 1000, 10000, 100000)]
  @[samples(50)]
  // Auto-generated: run both versions on identical inputs at
  // each declared size, report median/p95/p99, allocations,
  // and cache behavior per version.
end bench_migration;
```

Output:

```
bench_migration sort@1 vs sort@2:
  size     100: v1    2.3µs   v2    2.5µs   +8.7%    ok
  size    1000: v1     34µs   v2     36µs   +5.9%    ok
  size   10000: v1    520µs   v2    540µs   +3.8%    ok
  size  100000: v1    8.1ms   v2   22.0ms   +172%    REGRESSION
  Declared complexity on both versions: O(n log n).
  Observed super-linear growth on v2 indicates the declared
  cost is violated in practice.
```

When the complexity dimension (§6.3 dim 13) is declared, the
benchmark also verifies that empirical growth matches the
declared asymptotic class.  Mismatch is a compile warning, not
merely a benchmark failure.

### 15.14 Trust and Channel Propagation

The version dimension composes with the trust dimension (§6.3
dim 9, §10.6) and the deployment-mode surface (§25.1).

**Trust.**  A caller's trust is the minimum across its
transitive dependencies at their resolved versions.  Upgrading
a dependency from `Tested` to `Verified` automatically upgrades
consumers whose own trust was capped by that dependency:

```
GET /health/trust-upgrades
[
  { "symbol": "acme/auth.login",
    "old_trust": "Tested",
    "new_trust": "Verified",
    "cause": "std/sort@3 proved (previously Tested)" }
]
```

This creates a network effect: every proof shipped in the
ecosystem raises the trust of every transitive consumer without
any local work.

**Channel.**  Version resolution respects the active profile's
channel list (§25.12).  A stable-only profile will not resolve to
experimental versions even if they exist.  A package whose only
migration path passes through an experimental version is blocked
from stable adoption until the intermediate version graduates.

### 15.15 Limitations and Future Work

Versioning evolves specs; it does not repair misaligned
requirements.  The following remain out of scope.

 1. **Wrong specs from the start.**  If v1's postcondition
    failed to capture the real requirement, strengthening to v2
    does not rescue callers who relied on v1's behavior beyond
    its declared spec.  The mechanism evolves specifications; it
    does not detect that a specification was always wrong.

 2. **External non-FX dependencies.**  C libraries, POSIX system
    calls, hardware revisions via non-FX drivers — none carry
    FX's version coeffect.  Crossing into an external dependency
    is a trust boundary (§10.8); version information terminates
    at that boundary.

 3. **Live machine-state migration at non-quiescent points.**
    Migrating an in-flight transition mid-step requires a
    rendezvous protocol not specified in this chapter.
    Production implementations use pause → migrate → resume
    with a quiescent state explicitly declared.

 4. **Session migration across incompatible protocol states.**
    Where v1 and v2 disagree on the next expected message,
    sessions past the fork must complete under v1.  Safe
    migration point analysis for session types is a
    research-level gap (§11.5).

 5. **Behavioral regression within the declared spec.**  v2
    satisfies v1's spec but regresses in a dimension not
    captured by the spec — timing variance, cache locality,
    binary size, memory fragmentation.  §15.13 detects common
    cases but cannot prove absence across all inputs.

 6. **Parallel version development.**  Branching versions (v2
    and v3 descending independently from v1, later merged into
    v4 refining both) is plausible under the lattice structure
    but merge semantics and adapter composition for version
    DAGs are deferred to future work.

 7. **Cross-language version boundaries.**  FFI to C, interop
    with Rust or Python via shims, WebAssembly imports — none
    track version coeffects.  The version dimension terminates
    at the FX boundary and becomes opaque on the other side.


## 16. The Object Model

FX has no classes and no inheritance.  It has `impl` blocks for
method grouping, type classes for interfaces, existentials for
runtime polymorphism, and a resolution lattice that eliminates
ambiguity.

### 16.1 impl Blocks

An `impl` block groups methods for a type.  An instance method
takes `self` as its leading parameter with an explicit mode; a
static method has no `self` parameter.

```
impl Connection

  fn connect(host: string, port: nat) : Connection with IO
  begin fn
    let fd = tcp_connect(host, port);
    Connection { fd, open: true, host }
  end fn;

  fn is_open(ref self) : bool = self.open;

  fn set_timeout(ref mut self, ms: nat) : unit with IO
  = setsockopt(self.fd, SO_TIMEOUT, ms);

  fn close(self) : unit with IO
  = shutdown(self.fd);

  fn default_port() : nat = 443;   // static — no self

end impl;
```

Methods with `ref self` borrow shared.  Methods with `ref mut self`
borrow exclusively.  Methods with `self` (no mode) take ownership
and consume the value.  Methods with `affine self` may be consumed
at most once but also may be dropped.  Methods without `self` are
static — called as `Connection.default_port()` rather than
`conn.default_port()`.

**`self` is untyped in source.**  The compiler infers the type of
`self` from the enclosing `impl T`, `instance Trait for T`, or
`class Trait<T>` block.  Writing `fn is_open(ref self: Connection) ...`
inside `impl Connection` is compile error T064 (`self carries the
type of the enclosing block; explicit self type is redundant`).
The `self` keyword is a method parameter name only — using it as a
parameter name in a regular function (outside any of the three
method-defining block forms), as a let-binding name, or as a record
field is also T064.  When an ordinary identifier spelled `self` is
genuinely needed, backtick-escape it (`` `self` ``); see §2.3.

**Builder pattern methods.**  Methods that chain (§16.9) use
`self` (consuming) and return a new value of the same type.  FX
does not permit the `ref mut self -> ref mut Self` builder form:
methods declared as taking `ref mut self` must not return a mutable
borrow of `self`, because chained borrows across method calls
require lifetime annotations that are notoriously confusing for
agent-generated code and for human reviewers.  A `ref mut self`
method that returns `ref mut Self` is compile error M013
(`ref-mut-self method must not return ref mut Self; rewrite as
own-self builder or split into two calls`).

### 16.2 Dot Syntax

`x.method(args)` is sugar for `Type.method(x, args)`.  The self
mode determines what happens to the caller's value:

```
conn.is_open();            // borrows — conn survives
conn.set_timeout(5000);    // borrows mutably — conn survives
conn.close();              // takes ownership — conn consumed
```

### 16.3 The Resolution Lattice

When `x.method()` is called, the compiler resolves through a
specificity lattice.  First match at the most specific level wins:

```
Level 0: impl T                      T's own methods (always wins)
Level 1: instance Trait for T        explicit trait implementation
Level 2: class default fn            trait's default method
```

If two traits define the same method name and `T` implements both,
`x.method()` is a compile error.  The programmer qualifies:
`Trait1.method(x)`.

Resolution has no runtime-dispatch level.  When runtime
polymorphism over an open set of types is required, the programmer
constructs an `exists T. { ... }` record explicitly (§16.5) and
calls the record's fields directly — `widget.draw(ref canvas)`
reads `draw` from the record.  Method resolution remains fully
static and decidable.

### 16.4 Type Classes

```
class Printable<T: type>
  fn to_string(ref self: T) : string;
  fn print(ref self: T) : unit with IO
  = print_line(self.to_string());   // default method
end class;

class Eq<T: type>
  fn eq(ref self: T, ref other: T) : bool;
  fn neq(ref self: T, ref other: T) : bool
  = not self.eq(other);
end class;

instance Printable for Connection
  fn to_string(ref self) : string
  = f"Connection({self.host}, fd={self.fd})";
end instance;
```

`where` clauses constrain type parameters on functions:

```
fn sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);

fn show_all<a: type>(xs: list(a)) : string
  where Show(a), Eq(a);
```

They also constrain instance declarations when the type being
instanced is parameterized (the parameterized instance depends on
its element satisfying the same trait):

```
instance Ord for Tree<a>
  where Ord(a);
  fn compare(ref self, ref other: Tree<a>) : ordering
  = match (self, other);
      (Leaf(x), Leaf(y))         => Ord.compare(x, y);
      (Node(lx, rx), Node(ly, ry)) =>
        match Ord.compare(lx, ly);
          Equal => Ord.compare(rx, ry);
          other => other;
        end match;
      ...
    end match;
end instance;
```

The `where` clause on an instance is part of the instance's
resolution signature: the compiler selects this `Ord for Tree<a>`
instance only at call sites where the surrounding context
establishes `Ord(a)`.  Constrained instances are standard in
Haskell, Rust, and Scala 3; without them, parameterized instances
cannot recurse through their element type.

**Default method bodies.**  A class declaration may provide a
default implementation for a method; instances that do not
override the method inherit the default.  The `print` method of
`Printable` above has a default body composing `to_string` and
`print_line`; an instance need only implement `to_string` and
gets `print` for free.  The default body is type-checked against
the declared signature at the class-declaration site.  An abstract
method — signature only, no body — is a method that every instance
must implement.

Coherence rules: one instance per `(Trait, Type)` pair globally.
Instances must be declared where the trait or the type lives
(orphan rule).  FX does not support specialization: there is no
`instance Ord for list<int>` that overrides `instance Ord for
list<a>`.  The `where`-constrained instance is selected when its
constraint matches; if the constraint does not match, the
resolution fails with a concrete diagnostic.

### 16.5 Existentials

FX has exactly one surface syntax for runtime polymorphism:
explicit existential records built on the kernel Sigma type
(Appendix H.3).  The programmer writes the record of value +
methods directly, making the dispatch surface visible at the
definition site.

An existential type pairs a packed concrete type `T` with a
record of operations that close over `T`:

```
type Closeable = exists (T: type), {
  val:   own T;
  close: fn(own T) -> unit with IO;
};

type Drawable = exists (T: type), {
  val:    own T;
  draw:   fn(ref T, ref Canvas) -> unit with UI;
  handle: fn(ref mut T, Event) -> unit with UI;
};
```

The record's fields are the vtable — there is no separate
compiler-generated dispatch table.  Each field names one method
with its full signature (mode on `T`, parameters, return type,
effects).  Readers see the full contract; reviewers see the exact
method set; verifiers see the exact types.

**Construction.**  Build the record directly, supplying both the
value and the method bundle:

```
fn pack_conn(c: own Connection) : Closeable
= Closeable { val: c, close: Connection.close };

let cs : Closeable = pack_conn(open("host"));
```

Method references (like `Connection.close`) have the signature
`fn(own Connection) -> unit with IO`, which unifies with the
existential's `fn(own T) -> unit with IO` field when `T` is
instantiated to `Connection`.

**Consumption.**  Call the record's fields directly:

```
fn close_all(items: list(Closeable)) : unit with IO
= for item in items;
    item.close(item.val)
  end for;
```

There is no special method-call syntax.  `item.close` loads the
function pointer out of the record; `item.close(item.val)` calls
it with the packed value.  Runtime representation: one pointer
per method field plus the value itself (inline if small, boxed
otherwise).  Layout is under the programmer's control.

**Multi-method and composition.**  An existential can expose any
number of methods by adding fields to the record.  When several
capabilities are needed together, name every method in the
record:

```
type ReadableCloseable = exists (T: type), {
  val:   own T;
  read:  fn(ref mut T, ref mut buffer(u8), nat)
           -> nat with IO, Fail(io_error);
  close: fn(own T) -> unit with IO;
};
```

Composition is by field aggregation, not by trait union — each
existential is a concrete record type.  A stdlib-provided
`Closeable` and a user-written `Drawable` share no structure; if
you want both in the same collection, define a joint existential
that lists every field.

**Kernel translation.**  `exists (T: type), { f1: T1; ...; fn: Tn; }`
desugars to `Σ (T : Type<0>) × Σ (f1 : T1) × ... × Σ (fn : Tn) × unit`
per Appendix H.3.  Construction uses Σ-intro for each nested
pair; consumption uses Σ-elim to project the fields.  Sigma is
erased-zero at runtime like any other record — no type
descriptor is carried, preserving §1.5 compile-time erasure.

**Named existentials.**  For common cases, name the existential
once in stdlib and reuse the alias so the construction site is
short:

```
// in Std.Io
pub type Closeable = exists (T: type), { val: own T;
    close: fn(own T) -> unit with IO };

// at use sites
let handles : list(Closeable) = ...;
```

### 16.4.1 Reach Modality on Container Kinds

A type-class type parameter may carry a *reach capability* —
the upper bound on the capabilities of values stored inside the
container type.  This formalizes `cap(Linear, container(t))` with
inner-element capability constraint and the analogous nested-
capability patterns that hand-rolled permission tags previously
realized:

```
class Container<rcap_c: cap, container_kind: type -> type>
  fn empty<element: type>() : container_kind(element)
    where Capabilities(element) <= rcap_c;
  fn push<element: type>(x: element,
                          container: container_kind(element))
        : container_kind(element)
    where Capabilities(element) <= rcap_c;
  fn pop<element: type>(container: container_kind(element))
        : option(element)
    where Capabilities(element) <= rcap_c;
end class;
```

The reach `rcap_c` is a grade in the Capability modality (§6.3
Tier L; lattice `(power_set(NamedCaps), subset, union, empty)`
with shareability validity predicate).  Element constraints
flow as `where Capabilities(element) <= rcap_c`.  At an instance
declaration, the reach is instantiated to the specific
capability set the instance commits to:

```
instance Container<rcap_c = {Linear, ResourceTag},
                   container_kind = list> for ListImpl
  fn empty<element: type>() : list(element) = ...;
  ...
end instance;
```

**Subsumption.**  An instance with broader capability `c_2` is a
subtype of one with narrower `c_1` when `c_1 <= c_2`: the broader
set permits more elements, and any element satisfying the
narrower constraint also satisfies the broader.

**Composition with linearity.**  A `cap(Linear, container(t))` on
a container with reach including only Linear capabilities is
well-typed — the container preserves the inner Linear discipline.
Push/pop signatures preserve linearity through the container:
`pop` returns `option(element)` where `element` is the element
type with its full capability spectrum.

The reach mechanism is the kind-level instantiation of the
Capability modality (§6.3 dim-cap, §6.6 user-defined Tier L
discipline) — no new kernel rule, just a uniform application of
graded modality intro/elim per §6.2.

### 16.6 Algebraic Structure Intrinsics

Algebraic structures — monoid, group, ring, lattice, and so on — are
ordinary FX type classes (§16.4) marked with the `@[structure]`
attribute so the compiler treats their `law` clauses as
optimization-relevant rather than documentation.  There is no
separate `structure ... end structure` block form; `@[structure]
class` is the canonical form and reuses the full grammar of
§16.4.

```
@[structure]
class CommMonoid<t: type>
  val zero: t;
  fn add(ref self: t, ref other: t) : t;
  law left_identity  : forall(x: t),                add(zero, x) == x;
  law right_identity : forall(x: t),                add(x, zero) == x;
  law associativity  : forall(x: t, y: t, z: t),    add(add(x, y), z) == add(x, add(y, z));
  law commutativity  : forall(x: t, y: t),          add(x, y) == add(y, x);
end class;
```

`law` is a class-body-only form (§5.13) introducing a proposition
the compiler verifies against each instance via SMT at the instance
declaration site.  An instance that fails a law is compile error
P006 (`law declared in class not satisfied by instance`) with the
counterexample model produced by the solver.

Optimizations enabled by verified laws:

```
CommMonoid fold     ->  parallel reduction (split list anywhere)
Ring expressions    ->  factoring (a*b + a*c -> a*(b+c))
Lattice with top    ->  short-circuit (a \/ top = top)
Idempotent op       ->  deduplication in parallel execution
Monotonic fold       ->  incremental update on append
```

The compiler does not attempt these optimizations unless the
corresponding `@[structure]` class has been instanced for the
relevant type.  A user type that "happens to be a monoid" but never
instances `CommMonoid` receives no such rewrites — the law is
knowledge the type system has, not an implicit inference it
performs.

Structure hierarchy (stdlib-provided, in `Std.Algebra`):

```
Semigroup -> Monoid -> CommMonoid -> Group -> AbelianGroup
                                       |
                                    Semiring -> Ring -> CommRing -> Field

PartialOrder -> TotalOrder -> Lattice -> BoundedLattice
```

Each entry in the hierarchy is an `@[structure] class` extending
its parent with additional operations and laws.  A type instancing
a lower entry automatically satisfies all the parent entries by
the type-class subclass relation.

**Reversibility laws.**  Beyond the closure-under-operation laws
(left/right identity, associativity, commutativity), the
`@[structure]` discipline recognizes `inverse_left` and
`inverse_right` for monoids that admit subtraction:

```
@[structure]
class ReversibleCommMonoid<t: type>
  val zero: t;
  fn add(ref self: t, ref other: t) : t;
  fn sub(ref self: t, ref other: t) : t;
  law left_identity   : forall(x: t),             add(zero, x) == x;
  law right_identity  : forall(x: t),             add(x, zero) == x;
  law associativity   : forall(x: t, y: t, z: t), add(add(x, y), z) == add(x, add(y, z));
  law commutativity   : forall(x: t, y: t),       add(x, y) == add(y, x);
  law inverse_left    : forall(x: t, y: t),       sub(add(x, y), y) == x;
  law inverse_right   : forall(x: t, y: t),       sub(add(x, y), x) == y;
end class;
```

The two new laws state that subtracting a previously-added
element restores the prior state.  Combined with commutativity
this yields the full Abelian-group structure: every element `x`
has a unique inverse `-x = sub(zero, x)` such that `add(x, -x) =
zero`.  The compiler uses the reversibility laws to enable
incremental-merge optimizations and to validate retraction
operations (e.g. orthogonal-delta merging for ML weight
retraction under GDPR).

Stdlib instance: `ReversibleCommMonoid for OrthogonalDelta<axis,
T>` witnesses orthogonal-delta merging (Modular Delta Merging
with Orthogonal Constraints, arXiv:2507.20997) — `add` is the
sum of orthogonal projections, `sub` is the projection
subtraction.  SMT discharges all six laws at instance declaration
site (P006 on failure).

Composition with linearity is orthogonal: reversible operations
on linear values consume both arguments and produce a linear
result; on `@[copy]` values they admit arbitrary use.

### 16.6.1 CRDT Class Hierarchy

CRDT convergence is a property of join-semilattice structure
with monotonic updates.  The discipline ships as an
`@[structure] class` hierarchy in `Std.Distributed.CRDT`:

```
@[structure]
class Lattice<t: type>
  val bottom: t;
  fn join(ref self: t, ref other: t) : t;
  law associativity : forall(x: t, y: t, z: t), join(join(x, y), z) == join(x, join(y, z));
  law commutativity : forall(x: t, y: t),       join(x, y) == join(y, x);
  law idempotence   : forall(x: t),             join(x, x) == x;
  law identity      : forall(x: t),             join(bottom, x) == x;
end class;

class CvRDT<t: type> where Lattice(t)
  // state-based CRDT — convergence by monotonic join
end class;

class MonotonicCounter<t: type> where Lattice(t)
  fn increment(self: t, n: nat) : t;
  law monotone : forall(x: t, n: nat), join(x, increment(x, n)) == increment(x, n);
end class;
```

Stdlib instances cover `lww_register(t)`, `or_set(t)`,
`pn_counter(t)`, the BloomL prefix lattice, and the standard
Shapiro CRDT catalog.  Each instance's laws are SMT-checked at
declaration site.  Compositions: products of CRDTs are CRDTs;
maps to CRDTs are CRDTs; sequential prefixes form the BloomL
prefix lattice.

The Bridge modality (§6.0) gives free convergence proofs for
polymorphic CRDT operations: a function generic over `Lattice(t)`
that respects the join cannot produce a non-converging output —
parametric convergence theorems land for free.

### 16.7 Variance

Every type parameter declares its variance explicitly.  FX does not
infer variance from usage (rigor-first, §1.1 and Appendix E).  Three
variance markers are available; omission is compile error T048
(missing variance annotation):

```
type list<+a: type>           // covariant: list(cat) <: list(animal)
type consumer<-a: type>       // contravariant: consumer(animal) <: consumer(cat)
type cell<=a: type>           // invariant (read and write both)
```

Use `=` prefix for invariant type parameters.  `+` is covariant, `-`
is contravariant, `=` is invariant.  The compiler verifies the
declaration against actual usage: declaring `+a` but using `a` in a
contravariant position is compile error T049 (variance declaration
violated).

### 16.8 What FX Does Not Have

```
Feature                    Why excluded                     Use instead
─────────────────────────  ──────────────────────────────  ──────────────────
class Dog extends Animal   coupling, fragile base class     composition
virtual methods            implicit runtime dispatch         exists record (§16.5)
trait object dispatch      hidden vtable layout              exists record (§16.5)
universal top type         runtime type descriptor           closed enum or contract (§3.9)
protected fields           leaky encapsulation              module pub/private
abstract class             half-object half-interface       type class
multiple inheritance       diamond problem                  multiple type classes
implicit constructors      hidden code execution            fn new() : T
implicit destructors       hidden order-dependent code      own self + linear drop
operator overloading       unreadable code                  named methods
implicit this mutation     silent aliased mutation          explicit ref mut self
null                       billion dollar mistake           option(T)
runtime type tests         type-unsafe                      pattern match on enum
friend classes             encapsulation violation           module visibility
implicit conversions       silent bugs                      explicit narrow/widen
template metaprogramming   error messages, compile times    comptime + staging
syntax macros              "what language is this?"          comptime code generation
custom operators           unreadable in unfamiliar code    named functions
```

### 16.9 The Builder Pattern

Methods that take `self` (consuming) and return the same type
enable chaining.  Each method call consumes the old value and
produces a new one.  This is the only builder form FX supports
(§16.1 forbids `ref mut self -> ref mut Self`):

```
impl HttpRequest
  fn get(url: string) : HttpRequest
  = HttpRequest { method: GET, url, headers: [], body: None };

  fn header(self, key: string, value: string) : HttpRequest
  = { ...self, headers: [(key, value), ...self.headers] };

  fn body(self, data: bytes) : HttpRequest
  = { ...self, body: Some(data) };

  fn send(self) : result(HttpResponse, HttpError) with IO
  = http_execute(self);
end impl;

let response = HttpRequest.get("https://api.example.com")
  .header("Authorization", f"Bearer {token}")
  .body(payload)
  .send();
```

Each intermediate `HttpRequest` value is linear and immediately
consumed by the next method in the chain.  The compiler generates
in-place update where possible (the value flows through the chain
as unique-owner, so mutating the record's fields in place is
sound); the observable semantics are "one new value per method",
but the runtime cost is the same as imperative mutation.  This is
the one place FX systematically hides mutation behind immutable
semantics — it is sound because linearity guarantees a single
owner.

### 16.10 Derivable Traits

The `@[derive(...)]` attribute on a type declaration instructs
the compiler to generate a standard instance of one or more
derivable traits.  The catalog is a closed, stdlib-fixed set —
user packages cannot add new derivable traits.  This is
deliberate: a `@[derive(X)]` that dispatches to user-written
code generation is hidden code that ships with a package and
cannot be audited from the use site.  The five stdlib derives
cover the structural cases that are unambiguous from a type's
shape.

```
Trait       Generates                                    Requires
─────────   ──────────────────────────────────────────   ───────────────────
Eq          fn eq(ref self, ref other) : bool            Eq on every field
Ord         fn compare(ref self, ref other) : ordering   Ord on every field
            + eq / neq / lt / le / gt / ge from compare
Show        fn to_string(ref self) : string              Show on every field
Hash        fn hash(ref self, ref mut h: hasher) : unit  Hash on every field
Default     fn default() : Self                           Default on every field
```

**Usage:**

```
@[derive(Eq, Ord, Hash)]
type point { x: i64; y: i64 };

@[derive(Show, Default)]
type config { host: string; port: nat; tls: bool };
```

**Parameterized types require explicit bounds.**  When a derived
trait depends on a type parameter satisfying the same trait,
the programmer must state the bound in a `where` clause on the
type declaration.  The compiler does not auto-add bounds —
rigor-first applies (§1.1, Appendix E):

```
// Correct:
@[derive(Eq, Ord)]
type pair<a: type>
  where Eq(a), Ord(a);
  { x: a; y: a };

// Compile error T065 ('derived trait requires explicit where bound'):
@[derive(Eq)]
type pair<a: type> { x: a; y: a };
```

The diagnostic for T065 proposes the specific bound to add.

**What's not derivable.**  The catalog omits several commonly-
seen derives from other languages because FX has dedicated
mechanisms for each:

- **Copy** — use the `@[copy]` attribute (§5.4), which is
  checked at the type-definition site, not at a separate derive.
- **Send** / **Sync** — FX does not have these traits.  Thread
  safety follows from ownership modes (§7) plus the Alloc
  effect; the type system already tracks what is shared and
  what is not.
- **Arbitrary** (property-based-test generator) — use
  `@[arbitrary]` per §23.2 with a custom generator when the
  automatic shrink strategy is insufficient.
- **Serialize** / **Deserialize** — use contracts (§14) with
  declared `format` bindings.  Contracts carry version migration
  and are first-class for cross-boundary data.

**No user-defined derives.**  `@[derive(MyCustom)]` where
`MyCustom` is not one of the five stdlib traits is compile error
T066 (`unknown derivable trait; derive catalog is fixed by
stdlib`).  Custom code generation uses `comptime` (§17.1)
explicitly at the call site, where its presence and effect are
visible to readers.  A decorator (§17.3) can wrap an individual
function; a comptime function can emit boilerplate.  Neither
hides codegen behind a type-level attribute.

### 16.11 Operator Dispatch

Arithmetic operators — `+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`,
`~`, `<<`, `>>` — are compiler intrinsics defined only for
built-in numeric types, `bool`, `bits(n)`, `signed_bits(n)`, and
`trits(n)`.  They do not dispatch through a type class and user
types cannot extend them.  A user type representing a matrix, a
vector, or a fraction uses named methods (`Matrix.add(a, b)`,
`a.add(b)`, or `a |> Matrix.add(b)`) instead of overloaded `+`.
This is consistent with §16.8's "no operator overloading" rule.
The rationale is readability under an LLM-first primary-user
constraint: `a + b` must not perform IO, allocate, fail, or
take a lock; reading an arithmetic expression is a local
operation with known effects.  A named method is explicit about
its capabilities via its declared effect row.

**Comparison operators are an exception.**  `==`, `!=`, `<`,
`<=`, `>`, `>=` dispatch through the stdlib `Eq` and `Ord` type
classes.  A user type implementing `Eq` (typically via
`@[derive(Eq)]`) gets `==` and `!=`.  A type implementing `Ord`
gets `<`, `<=`, `>`, `>=`.  Equality and ordering are structural
enough that forcing `Ord.lt(a, b)` throughout the language would
regress readability without capability gain — the `Eq` and `Ord`
classes have no effects beyond `Tot`, so a comparison is always
pure.

**`is` tests** (`x is Some`) are not operators in the dispatch
sense: they test a constructor tag directly, have no class
dispatch, and compile to a discriminator load.

The full operator-to-mechanism map:

```
Operator          Mechanism                     Extensible?
───────────       ───────────────────────────   ────────────────────
+ - * / %         arithmetic intrinsic           no (built-in
                                                 numeric types only)
& | ^ ~ << >>     bitwise intrinsic              no (bits(n) /
                                                 signed_bits(n) /
                                                 trits(n) only)
== !=              Eq class dispatch             yes (via derive
                                                 or manual instance)
< <= > >=          Ord class dispatch             yes (via derive
                                                 or manual instance)
and or not         boolean intrinsic              no
is                 constructor-tag test           no
..  ..=            range intrinsic                no (produces
                                                 range<T>)
|>                pipe (syntactic desugar)       no
.field / .method   projection / method call      no (resolved
                                                 per §16.3)
```

Attempting to implement `Add` on a user type (or implementing a
trait named `Add` that mimics overloading) is not a compile
error — the class exists and an instance can be declared — but
the `+` operator still dispatches to the arithmetic intrinsic.
There is no way to make `a + b` call a user-defined method.

### 16.12 Profunctor Optics

Lenses, prisms, traversals, folds, getters, setters, isomorphisms,
and affine traversals share one algebraic foundation: profunctor
optics (Riley 2018, Pickering-Gibbons-Wu POPL 2018).  Every
"view into a structure" pattern is an `Optic c s t a b` for a
profunctor constraint `c`.  Composition is function composition;
the meet of profunctor constraints handles per-instance
composition.

Stdlib module `Std.Optics` ships the algebra:

```
class Profunctor<p: type -> type -> type>
  fn dimap<s: type, t: type, a: type, b: type>(
        f: s -> a, g: b -> t, x: p(a, b)) : p(s, t);
end class;

class Strong<p: type -> type -> type> where Profunctor(p)
  fn first<a: type, b: type, c: type>(
        x: p(a, b)) : p((a, c), (b, c));
end class;

class Choice<p: type -> type -> type> where Profunctor(p)
  fn left<a: type, b: type, c: type>(
        x: p(a, b)) : p(either(a, c), either(b, c));
end class;

type optic_lens<s: type, t: type, a: type, b: type> =
  forall(p: type -> type -> type), Strong(p) ==> p(a, b) -> p(s, t);

type optic_prism<s: type, t: type, a: type, b: type> =
  forall(p: type -> type -> type), Choice(p) ==> p(a, b) -> p(s, t);

type optic_affine<s: type, t: type, a: type, b: type> =
  forall(p: type -> type -> type),
    Strong(p) and Choice(p) ==> p(a, b) -> p(s, t);

type optic_iso<s: type, t: type, a: type, b: type> =
  forall(p: type -> type -> type), Profunctor(p) ==> p(a, b) -> p(s, t);
```

**Subsumption.**  `optic_lens` is included in `optic_affine` is
included in `optic_iso` (the constraint relaxes from Strong via
both-Strong-and-Choice to bare Profunctor); `optic_prism` is
included in `optic_affine` similarly; an isomorphism is both a
lens and a prism.  The
profunctor-representation theorem (Boisseau-Gibbons ICFP 2018)
gives the factorization `(s -> r) × (r × b -> t)` for every
optic.

**Composition** is ordinary function composition: composing an
optic constrained by `c_1` with one constrained by `c_2` yields
an optic whose constraint is the meet `c_1 and c_2` (taking the
stronger of the two profunctor requirements).

A lens composed with a prism is an affine traversal (the meet
of `Strong` and `Choice`).

The hand-rolled view types programmers reach for in other
languages — scoped-view, timeline-slice, read-view, borrowed
projections — collapse into stdlib instances of the optic class
hierarchy.


## 17. Compile-Time Evaluation

### 17.1 comptime

`comptime` marks an expression, function, or block for evaluation
during compilation.  The same syntax as runtime code, evaluated at
compile time:

```
comptime fn array_size<a: type>() : nat = sizeof(a) * 1024;

comptime begin
  let table = generate_lookup_table(256);
end;

fn matmul(a: matrix(f64, n, m), b: matrix(f64, m, p)) : matrix(f64, n, p)
begin fn
  comptime if platform.simd_width >= 512;
    avx512_matmul(a, b)
  else if platform.simd_width >= 256;
    avx2_matmul(a, b)
  else
    naive_matmul(a, b)
  end if
end fn;
```

If a `comptime` expression cannot be evaluated at compile time, it
is a compile error.

**Comptime is pure.**  Comptime evaluation runs with effect row
`Tot` plus compiler-internal allocation (invisible at runtime).
It may:

 * perform arithmetic, string, and data-structure computation
 * call other comptime functions transitively
 * read constants and declared types in the current compilation
   unit
 * read target-property values exposed by `std/platform`
   (`platform.simd_width`, `platform.bits`, `platform.target`,
   etc.)
 * unfold itself via §30.2 kernel normalization, giving
   dependent types that depend on comptime values their fully-
   resolved shape at elaboration

It may not:

 * perform any IO — no file access, no network, no stdin/stdout,
   no environment variables, no clock, no randomness
 * call any function whose effect row contains anything other
   than `Tot`
 * use unbounded recursion without a `decreases` clause

The discipline is what §25.5 supply-chain defenses rely on: a
package cannot execute arbitrary code at install or build time
because comptime cannot touch the filesystem or network.  This
rules out the xz-utils attack surface by construction.

**Asset embedding** (Zig `@embed_file` use case) goes through
the workspace manifest (§25.3), not through comptime IO.  Assets
are declared in `package.fx.toml` with a content hash and read
at compile time via the stdlib primitive `asset(name) : bytes`,
whose implementation the build driver fills in with already-
resolved bytes.  Hermetic by construction: the asset hash is
part of the build cache key (§25.10).

**Dependent types over comptime values** are normalized at
elaboration via the same §30.2 kernel reduction that evaluates
`comptime` expressions.  A function `fn f<n: nat>(x: array(i64, n))`
applied at a call site where `n = comptime compute_size()` has
its type normalized during elaboration.  When `n` is a runtime
value, the type involves a §6.7 dependent grade and SMT
discharges obligations over it.

### 17.2 Staged Programming

`code(T)` is the type of a program fragment that, when executed,
produces a value of type `T`.  Quote `` `(expr) `` lifts an
expression.  Splice `~expr` inserts code:

```
fn gen_power(n: nat) : code(i64 -> i64)
  decreases n;
begin fn
  if n == 0;
    `( fn(x) => 1 )`
  else
    let rest = gen_power(n - 1);
    `( fn(x) => x * (~rest)(x) )`
  end if
end fn;

comptime let power5 = run(gen_power(5));
// power5 is fn(x) => x * x * x * x * x * 1  — fully unrolled
```

Staged programming subsumes macro-like code generation:

```
comptime fn compile_regex(pattern: string) : code(string -> bool)
begin fn
  let nfa = parse_regex(pattern);
  gen_nfa_matcher(nfa)
end fn;

comptime let match_email = run(compile_regex(r"^[a-z]+@[a-z]+\.[a-z]+$"));
```

### 17.3 Decorators

Decorators are type-safe function transformers:

```
@[decorator]
fn cached<a: type, b: type>(f: a -> b) : a -> b
begin fn
  let cache : cell(map(a, b)) = cell(empty_map());
  return fn(x: a) => match Map.find(cache.get(), x);
    Some(v) => v;
    None => begin
      let result : b = f(x);
      cache.set(Map.add(cache.get(), x, result));
      result
    end;
  end match;
end fn;

@[cached]
fn fibonacci(n: nat) : nat
  decreases n;
= if n <= 1; n else fibonacci(n - 1) + fibonacci(n - 2) end if;
```

Decorators compose: `@[cached, retry(3)]` applies right-to-left.
A decorator is a function annotated with `@[decorator]`; there is
no separate `decorator ... end decorator` block (eliminated with
§2.3's contextual keyword cleanup).

### 17.4 Custom Attributes

Attributes are pure metadata.  They never change parsing or type
checking.  They are read by `comptime` code generators:

```
@[route("GET", "/api/users")]
pub fn get_users() : list(user) with IO, DB;

@[table("users"), index("email")]
type User { id: nat; name: string; email: string };

@[json(rename_all: "camelCase")]
type ApiResponse { user_name: string; created_at: timestamp };
```

Code compiles with or without custom attributes.  No attribute can
make invalid code compile or valid code fail.

### 17.5 Physical Units

Named dimension algebra at the type level:

```
dimension Length;
dimension Time;
dimension Mass;

type meters       = qty(Length);
type seconds      = qty(Time);
type velocity     = qty(Length / Time);
type acceleration = qty(Length / Time^2);
type force        = qty(Mass * Length / Time^2);

fn kinetic_energy(m: qty(Mass), v: velocity) : qty(Mass * Length^2 / Time^2)
= 0.5 * m * v * v;
```

The dimension algebra is computed at compile time.  Runtime
representation is bare `f64` — zero overhead.  Mismatched dimensions
are compile errors:

```
// let bad = (5.0 : meters) + (3.0 : seconds);
// error: qty(Length) + qty(Time): incompatible dimensions
```

### 17.6 Codata Operations

Consuming codata values:

```
fn take<a: type>(n: nat, s: stream(a)) : list(a)
  decreases n;
= if n == 0; []
  else [head(s), ...take(n - 1, tail(s))]
  end if;

fn zip_with<a: type, b: type, c: type>(f: (a, b) -> c, s1: stream(a), s2: stream(b)) : stream(c)
= unfold
    head => f(head(s1), head(s2));
    tail => zip_with(f, tail(s1), tail(s2));
  end unfold;
```

### 17.7 Hygiene and Term Reflection

Comptime code-generation primitives that introduce new bindings
do so hygienically: every binding introduced by a comptime
function or staged quote is α-renamed at expansion time so no
binding captures a binding visible at the call site.  The
discipline is automatic; programmers writing comptime code use
ordinary identifiers and the compiler tracks each binding's
expansion context (its "color" in Racket terminology).

```
comptime fn for_loop<a: type>(start: code(a), end: code(a),
                              body: code(a) -> code(unit)) : code(unit)
= `(let i = start;
    while i < end;
      body(i);
      i = i + 1;
    end while;)`
```

The `i` introduced by this comptime function is α-renamed on
each expansion; a caller passing a `body` whose own scope
references `i` does not collide with the macro's `i`.  Hygiene
is unconditional — there is no opt-out, and there is no
unhygienic reflection primitive.  When a programmer needs to
share a name across the macro/caller boundary, the caller
passes the name as a `code(...)` argument; the macro never
synthesizes a name visible to the caller.

**Term reflection.**  Beyond write-only staging (`code(T)`
generation), comptime exposes read-only introspection of the
kernel-elaborated structure of a term:

```
comptime fn term_structure<T: type>(t: code(T)) : code_structure;
comptime fn pattern_match_on<T: type>(t: code(T),
                                       patterns: list(...)) : ...;
```

`code_structure` is the standard kernel-term ADT (lambdas,
applications, constructor calls, projections, literals)
restricted to the canonical fragment.  These primitives are
the building blocks of tactic-style code: `simp`, `omega`,
`decide`, and other proof-search tactics are implemented as
comptime functions consuming `code_structure` and producing
new `code(...)` values.

Reflection is read-only at the kernel level: a comptime
function can inspect a term's structure but cannot bypass the
type system to construct ill-typed terms.  Every output
`code(T)` is type-checked at the splice site by the standard
kernel rules.


## 18. Bit-Level Types and Hardware

### 18.1 Bit Layouts

A `layout` declares a named bit-field arrangement within a `bits(n)`
value.  Fields are listed MSB-first with their widths.  The compiler
computes positions and generates extraction and insertion logic.
`layout` is the hardware-side keyword for bit arrangements; it never
collides with the contract-side `format` keyword (§14.4) which
declares wire-format serialization bindings.

```
layout R : bits(32) = {
  funct7 : 7;       // [31:25]
  rs2    : 5;       // [24:20]
  rs1    : 5;       // [19:15]
  funct3 : 3;       // [14:12]
  rd     : 5;       // [11:7]
  opcode : 7;       // [6:0]
};

layout B : bits(32) = {
  imm_12   : 1;
  imm_10_5 : 6;
  rs2      : 5;
  rs1      : 5;
  funct3   : 3;
  imm_4_1  : 4;
  imm_11   : 1;
  opcode   : 7;

  virtual imm : bits(13) = bits { imm_12, imm_11, imm_10_5, imm_4_1, 1b0 };
};
```

Virtual fields reassemble scattered bits automatically.  Dot access
on a layout-cast `bits(n)` compiles to wire selection — zero gates,
zero runtime cost:

```
let insn : bits(32) = fetch(pc);
let r = R(insn);
r.opcode              // bits(7)
r.rd                  // bits(5)

let b = B(insn);
b.imm                 // bits(13) — scattered bits reassembled
```

### 18.2 Bit Pattern Matching

Match on layout fields in pattern position:

```
fn decode(insn: bits(32)) : decoded
= match insn;
    R { opcode: 0b0110011, funct3: 0b000, funct7: 0b0000000 }
      => ADD(rd: .rd, rs1: .rs1, rs2: .rs2);
    R { opcode: 0b0110011, funct3: 0b000, funct7: 0b0100000 }
      => SUB(rd: .rd, rs1: .rs1, rs2: .rs2);
    I { opcode: 0b0010011, funct3: 0b000 }
      => ADDI(rd: .rd, rs1: .rs1, imm: sign_extend(.imm));
    B { opcode: 0b1100011, funct3: 0b000 }
      => BEQ(rs1: .rs1, rs2: .rs2, offset: sign_extend(.imm));
    _ => ILLEGAL;
  end match;
```

The `.field` syntax inside a format match accesses the matched
format's field.  The compiler verifies: matched constant fields
uniquely identify the format (no overlapping patterns).

### 18.3 Register Access Modes

Each field in a hardware register has an access mode governing
read/write semantics.  Violating the mode is a compile error.

```
RW           read-write (standard)
RO           read-only (writes rejected by compiler)
WO           write-only (reads rejected by compiler)
W1C          write-1-to-clear (writing 1 clears the bit)
W1S          write-1-to-set (writing 1 sets; hardware self-clears)
RC           read-to-clear (reading consumes the value — linear read)
RS           read-to-set
RSVD         reserved (must write 0, reads return 0)
```

```
register_file DeviceRegs at base
  reg int_status : bits(32) at 0x20
    field rx_done    : bit(0) RC;
    field tx_done    : bit(1) RC;
    field error      : bit(2) W1C;
    field reserved   : bits(31:4) RSVD;
  end reg;
end register_file;
```

RC bits: reading consumes the information (the hardware clears the
bit on read).  The compiler treats RC reads as linear operations.
W1C bits: the compiler generates the correct write pattern — writing
1 to the target bit, 0 to all others (not read-modify-write).
RSVD bits: writing non-zero is a compile error.

### 18.4 Cross-Register Dependencies

64-bit values split across 32-bit registers, fields whose valid
values depend on other registers, and required write ordering:

```
register_file DmaEngine at base
  reg dma_addr_hi : bits(32) at 0x10 WO;
  reg dma_addr_lo : bits(32) at 0x14 WO;

  virtual dma_addr : bits(64) = bits { dma_addr_hi, dma_addr_lo }
    write_order hi then lo;

  reg dma_len : bits(32) at 0x18 RW
    where dma_len <= 0xFFFF;
    where dma_addr.aligned(dma_len);

  reg dma_ctrl : bits(32) at 0x1C
    field start : bit(0) WO
      requires dma_addr != 0;
      requires dma_len > 0;
  end reg;
end register_file;
```

### 18.5 Register State Machines

The combination of register values defines the device state:

```
register_file UsbPort at base
  reg portsc : bits(32) at 0x00
    field connect  : bit(0) RO;
    field enable   : bit(1) RW;
    field suspend  : bit(2) RW;
    field reset    : bit(4) RW;
    field power    : bit(12) RW;
  end reg;

  machine PortState driven_by portsc
    state Unpowered    when not power;
    state Disconnected when power and not connect;
    state Connected    when power and connect and not enable and not reset;
    state Resetting    when power and connect and reset;
    state Enabled      when power and connect and enable and not suspend;
    state Suspended    when power and connect and enable and suspend;

    Unpowered -> Disconnected    = portsc.power.set(1);
    Connected -> Resetting       = portsc.reset.set(1);
    Resetting -> Enabled         = portsc.reset.set(0); after 10ms;
    Enabled -> Suspended         = portsc.suspend.set(1);

    initial Unpowered;
  end machine;
end register_file;
```

The compiler proves via bit-vector SMT (QF_BV): state predicates
are mutually exclusive and exhaustive, every transition produces a
valid bit pattern, and no register write creates an undefined state.

### 18.6 SMT Decidability

Bit-vector arithmetic is decidable in SMT.  Every bit-field
refinement, cross-field dependency, register state predicate, format
pattern exhaustiveness check, and virtual field reassembly is
automatically provable.  No fuel, no tactics, no manual lemmas.
The compiler dispatches to the bit-vector solver and always gets a
definitive answer.

### 18.7 Clock Domains

The `Sync(clk)` effect tracks which clock drives a signal.  Mixing
signals from different clocks without a synchronizer is a compile
error:

```
fn good(x: bits(8) with Sync(clk_a)) : bits(8) with Sync(clk_a) = x + 1;

fn bad(x: bits(8) with Sync(clk_a)) : bits(8) with Sync(clk_b) = x + 1;
// error: clock domain crossing without synchronizer
```

The clock domain semiring: `combinational * sync(c) = sync(c)`,
`sync(a) * sync(b) = CROSS_DOMAIN_ERROR` when `a != b`.

Explicit synchronizer:

```
let synced = sync_2ff(x, from: clk_a, to: clk_b);
```

### 18.8 The Synthesizable Subset

A `hardware` module restricts its body to constructs that map to
gates:

```
Synthesizable                Non-synthesizable
─────────────────            ─────────────────
Tot (combinational)          Div (unbounded loops)
Sync(clk) (sequential)       IO
bits(n) types                Alloc
Bounded loops (for 0..n)     Exn
format types                 String, list
machine with Sync            Arbitrary-precision int
```

### 18.9 Combinational Modules

A `hardware fn` is a pure function on bits.  It synthesizes to
combinational logic:

```
hardware fn alu<w: nat>(a: bits(w), b: bits(w), op: bits(4))
  : (result: bits(w), flags: bits(4))
= let result = match op;
    0x0 => a + b;
    0x1 => a - b;
    0x2 => a & b;
    0x3 => a | b;
    0x4 => a ^ b;
    _ => 0;
  end match;
  let flags = bits {
    result == 0,
    carry_out(a, b, op),
    overflow_detect(a, b, result, op),
    result[w - 1],
  };
  (result, flags);
```

### 18.10 Sequential Logic

The `on rising(clk)` block creates clocked register updates:

```
hardware module shift_register<w: nat> with Sync(clk, reset)
  reg data : bits(w) = 0;

  on rising(clk)
    if reset; data.set(0)
    else data.set(bits { data[w - 2 : 0], serial_in })
    end if;
  end on;

  let out = data;
end hardware module;
```

`let` outside `on rising` creates wires (combinational).  `.set()`
inside `on rising` creates register updates (sequential).

### 18.11 Pipeline Sugar

```
pipeline rv64 with Sync(clk, reset)

  stage fetch
    let insn = imem.read(pc);
    emit insn, pc;
  end stage;

  stage decode
    let d = decode(insn);
    let a = rf.read(d.rs1);
    let b = rf.read(d.rs2);
    stall when prev.is_load and prev.rd in [d.rs1, d.rs2];
    emit d, a, b;
  end stage;

  stage execute
    let result = alu(a, b, d.alu_op);
    let branch = eval_branch(d, result);
    flush fetch, decode when branch.taken;
    emit result, d;
  end stage;

  stage memory
    let mem_result = match d.mem;
      Load(w) => dmem.read(result, width: w);
      Store(w) => begin dmem.write(result, b, width: w); result end;
      None => result;
    end match;
    emit mem_result, d;
  end stage;

  stage writeback
    rf.write(d.rd, mem_result, en: d.writes_rd and d.rd != 0);
  end stage;

end pipeline;
```

The compiler generates: pipeline registers between stages, forwarding
muxes, stall logic, flush logic, and valid-bit tracking.  The
compiler verifies: every data hazard is handled, forwarding produces
correct values, stalls do not lose instructions, and the pipeline
refines the ISA specification.

### 18.12 ISA Specification and Refinement

The ISA is a `Tot` function — the golden reference:

```
fn step(s: arch_state) : arch_state
= let insn = fetch(s.mem, s.pc);
  execute(s, decode(insn));

fn execute(s: arch_state, d: decoded) : arch_state
= match d;
    ADD(rd, rs1, rs2) =>
      s |> write_rd(rd, s.x[rs1] + s.x[rs2]) |> advance_pc(4);
    BEQ(rs1, rs2, off) =>
      s |> advance_pc(if s.x[rs1] == s.x[rs2]; off else 4 end if);
    ILLEGAL => trap(s, cause: IllegalInstruction);
  end match;
```

The pipeline is verified against the ISA via a refinement proof:

```
refinement pipeline_correct
  spec = arch_state.step;
  impl = rv64_pipeline;

  via fn(pipe) => arch_state {
    x:   pipe.rf.regs,
    pc:  committed_pc(pipe),
    mem: pipe.dmem,
  };

  property correspondence :
    forall(p: pipeline_state),
      commits(tick(p)) ==>
        abstract(tick(p)) == step(abstract(last_commit(p)));
end refinement;
```

Extraction to Verilog/VHDL: `fxc --target verilog module.fx`.

**Bisimulation as univalence transport.**  Under the §6.0 value-
category framing, the ISA spec is an ordinary `Tot` FX function
and the pipeline is a `hardware module` declaration (§18.10);
the `synth` boundary carries the abstract-to-concrete
relationship and observational equivalence between the
pipeline's commit stream and the ISA's step function lifts to a
**modal univalence** at the synth boundary.

Specifically: `observe(rv64_pipeline)` maps the RTL's committed-
cycle stream to an FX `arch_state` stream.  The bisimulation
declared in §13.19 between this stream and `arch_state.step`'s
output stream is an equivalence on the runtime layer, witnessed
by the refinement's `correspondence` property; that equivalence
transported back
along synth gives `synth(arch_state.step) ≃ rv64_pipeline` at
Hardware.

The practical consequence: once the equivalence is established,
**transport along it preserves all properties automatically**.
Performance-counter reasoning, instruction-level interrupts,
exception precision, memory-coherence protocols — every property
proved at the ISA level transports to the pipeline implementation
without re-proof.  This is the smpst-sr-smer ITP 2025 technique
(parameterized coinduction on infinite trees) generalized to
hardware-software co-design.

Compared to the previous "bisimulation as invariant chain"
discipline (§13.19 base form), univalence transport collapses N
per-property invariants into one equivalence proof.  The chain-
of-invariants form remains available as a derived discipline
when the equivalence is too expensive to prove globally.

### 18.13 Hardware-Software Co-Verification

The same `register_file` definition is used by the RTL (hardware),
the ISA spec (semantics), and the driver (software).  One definition,
three consumers.  Changing the register layout produces compile
errors in all three simultaneously.

### 18.14 Compilation Model

```
FX construct                  Hardware
──────────────────────────    ────────────────────
let x = a + b;               adder + wires
if sel; a else b end if       2:1 mux
match on bits(n)              mux tree / decoder
reg x : bits(n) = 0;         n flip-flops with reset
on rising(clk) x.set(e);     register update
layout L : bits(n)            wire selection (zero gates)
machine with Sync(clk)        FSM (one-hot or binary)
pipeline                      pipeline regs + hazard logic
for i in 0..n                 n copies (unrolled)
comptime if                   conditional generate
bits { a, b }                 wire concatenation (zero gates)
x[7:0]                        wire selection (zero gates)
```


## 19. Systems Programming

### 19.1 Execution Context as Effects

The execution context is an effect hierarchy.  Calling a function
that requires a less-restricted context from a more-restricted
context is a compile error:

```
HardIRQ < SoftIRQ < Dispatch < Passive
```

`HardIRQ` is most restricted: no sleeping, no mutexes, only
spinlocks with interrupts disabled, only atomic allocation.
`Passive` is least restricted: can sleep, take mutexes, page fault.

```
fn irq_handler(ref mut dev: DeviceState) : irq_return
  with HardIRQ, MMIO
begin fn
  let status = dev.regs.int_status.read();
  dev.regs.int_status.set(status);
  if status.rx_done; napi_schedule(ref dev.napi) end if;
  IRQ_HANDLED

  // mutex_lock(ref dev.lock);
  // error: mutex_lock requires Passive, called in HardIRQ
end fn;
```

### 19.2 DMA as Linear Ownership

DMA means hardware reads/writes memory directly.  The type system
tracks CPU vs device ownership:

```
fn start_rx(ref mut dev: DeviceState, buf: dma_buf(packet)) : dma_token
  with DMA, MMIO
begin fn
  let phys = dma_map_single(ref buf, direction: FromDevice);
  dev.regs.dma_addr.set(phys);
  dev.regs.ctrl.dma_start.set(1);
  dma_token.new(buf, phys)
  // buf consumed — CPU cannot access it while DMA active
end fn;

fn complete_rx(token: dma_token) : dma_buf(packet)
  with DMA
begin fn
  dma_unmap_single(token.phys, direction: FromDevice);
  token.reclaim()
  // CPU gets ownership back
end fn;
```

### 19.3 Driver Lifecycle Machines

Every resource acquired during initialization has an `inverse` for
cleanup.  The compiler generates cleanup paths for every possible
failure point:

```
machine NvmeDriver
  state Probed of { pci: pci_device };
  state BarMapped of { pci: pci_device; regs: NvmeRegs };
  state AdminReady of { pci: pci_device; regs: NvmeRegs;
                         admin: QueuePair };
  state Running of { /* all resources */ };
  state Removed;

  transition map_bars : Probed -> BarMapped with Passive, MMIO
    inverse unmap_bars;
  transition setup_admin : BarMapped -> AdminReady with Passive, DMA
    inverse teardown_admin;
  transition start : AdminReady -> Running with Passive, MMIO
    inverse stop;
  transition remove : * -> Removed with Passive, MMIO;

  initial Probed;
  terminal Removed;

  always (state is Removed) ==>
    pci_released and dma_freed and irqs_disabled;
end machine;
```

The `remove` transition from any state: the compiler generates the
compensation chain from inverse declarations.  From `Running`:
`stop`, `teardown_admin`, `unmap_bars`.  From `AdminReady`:
`teardown_admin`, `unmap_bars`.

### 19.4 Lock Ordering

```
lock_order SpinIRQ < DeviceLock < SubsystemLock < GlobalLock;

fn safe(ref dev: Device, ref subsys: Subsystem) : unit with Passive
begin fn
  let _g1 = spin_lock_irq(ref dev.lock);
  let _g2 = mutex_lock(ref subsys.lock);
  // ok: DeviceLock < SubsystemLock
end fn;

// error: SubsystemLock acquired before DeviceLock
// fn bad() = begin fn mutex_lock(subsys); spin_lock(dev); end fn;
```

### 19.5 Stack Budgets

```
fn irq_handler(ref mut dev: DeviceState) : irq_return
  with HardIRQ, MMIO, Alloc(Stack, bound: 2048)
begin fn
  // compiler verifies: all frames in call tree <= 2048 bytes
end fn;
```

### 19.6 Inline Assembly

```
fn read_msr(msr: bits(32)) : bits(64) with Privileged
begin fn
  asm x86_64
    "rdmsr"
    in ecx = msr;
    out eax -> lo : bits(32);
    out edx -> hi : bits(32);
    clobbers none;
  end asm;
  bits { hi, lo }
end fn;
```

### 19.7 Address Space Types

Distinct types prevent mixing address spaces:

```
type phys_addr = bits(64);
type virt_addr = bits(64);
type bus_addr = bits(64);

fn ioremap(phys: phys_addr, size: nat) : virt_addr with MMU;
fn phys_to_bus(phys: phys_addr) : bus_addr with IOMMU;
```

### 19.8 NVMe Queue Pair

A detailed example of linear ownership in driver I/O paths:

```
module QueuePair<depth: nat>
  where depth > 0 and is_power_of_2(depth);

  sq_buf : dma_buf(array(NvmeCmd, depth));
  cq_buf : dma_buf(array(NvmeCpl, depth));
  sq_tail : bits(log2(depth)) = 0;
  cq_head : bits(log2(depth)) = 0;
  tracker : array(option(pending_io), depth);

  fn submit(ref mut self, cmd: NvmeCmd, io: pending_io,
            ref mut regs: NvmeRegs) : result(unit, QueueFull)
    with MMIO
  begin fn
    if self.is_full(); return Err(QueueFull) end if;
    self.sq_buf[self.sq_tail].set(cmd);
    self.tracker[self.sq_tail].set(Some(io));
    // io consumed — moved into tracker
    self.sq_tail.set((self.sq_tail.get() + 1) % depth);
    regs.sq_doorbell(self.qid).set(widen<bits(32)>(self.sq_tail.get()));
    Ok(())
  end fn;

  fn complete(ref mut self, ref mut regs: NvmeRegs)
    : list((NvmeCpl, pending_io))
    with MMIO
  begin fn
    let results = [];
    while self.cq_buf[self.cq_head].phase == self.cq_phase;
      let cpl = self.cq_buf[self.cq_head];
      let io = self.tracker[cpl.cid].take();
      // .take() returns owned pending_io, replaces with None
      // compile error if already None (double completion)
      results.set([(cpl, io), ...results.get()]);
      self.cq_head.set((self.cq_head.get() + 1) % depth);
      if self.cq_head.get() == 0; self.cq_phase.set(not self.cq_phase.get()) end if;
    end while;
    if not is_empty(results);
      regs.cq_doorbell(self.qid).set(widen<bits(32)>(self.cq_head.get()));
    end if;
    rev(results)
  end fn;
end module;
```

Linear tracking guarantees: every submitted command is eventually
completed (linear value leak = compile error), no double completion
(`.take()` on consumed slot = compile error), DMA buffers not freed
while device owns them.

### 19.9 WiFi Connection State Machine

```
machine WifiConnection for dev: WifiDevice
  state Disconnected;
  state Scanning of { results: list(scan_result) };
  state Authenticating of { bss: bss_info };
  state Handshake of { bss: bss_info; ptk: option(secret ptk_data) };
  state Connected of { bss: bss_info; secret keys: key_set };

  transition scan : Disconnected -> Scanning with IO;
  transition auth : Disconnected -> Authenticating with IO;
  transition auth_ok : Authenticating -> Handshake
    on_event FwNotify.AuthOK;
  transition install_keys : Handshake -> Connected
    requires ptk is Some;
    with IO;
  transition disconnect : Connected -> Disconnected
    // keys consumed — classified data securely erased
  transition link_lost : Connected -> Disconnected
    on_event FwNotify.LinkLost;

  initial Disconnected;

  always (state is Connected) ==> keys_installed(dev.fw);
  always (state is Disconnected) ==> not keys_installed(dev.fw);
end machine;
```

Crypto keys exist in firmware only when connected.  The `disconnect`
transition consumes the key set (linear + classified = secure
erasure on drop).

### 19.10 C Interop

FX kernel modules produce standard object files:

```
@[abi(C, linux_kernel)]
@[link_section(".init.text")]
pub fn init_module() : i32 with Passive, IO
begin fn
  let r = pci_register_driver(ref my_driver_ops);
  if r < 0; r else 0 end if
end fn;

extern "C" fn printk(fmt: ptr(u8)) : i32;
extern "C" fn kmalloc(size: nat, flags: gfp_t) : ptr(u8);
```

Same calling convention as C.  Same object files.  Links with GCC
output.  One driver at a time — the rest of the kernel stays C.

### 19.11 Allocation in Context

The effect determines which allocation flags are valid:

```
fn alloc_in_process() : page with Passive, Alloc(Kernel);
// Passive -> may sleep -> GFP_KERNEL

fn alloc_in_irq() : page with HardIRQ, Alloc(Atomic);
// HardIRQ -> cannot sleep -> GFP_ATOMIC

// error: Alloc(Kernel) requires Passive
// fn bad() : page with HardIRQ, Alloc(Kernel);
```


## 20. Compilation Pipeline

FX compiles through four binary intermediate representations.
Source is the only human-readable artifact.  Each layer carries
specific information that the next layer consumes.

### 20.1 The Four Layers

```
Layer    Ext     Represents                          Key property
─────   ─────   ──────────────────────────────────  ─────────────────────
FX      .fx     full language, 22 dimensions         human-readable
FXCore  .fxc    typed, monomorphic, SSA              types guide lowering
FXLow   .fxl    flat, virtual registers               target-independent
FXAsm   .fxa    target instructions, physical regs   one step from encoding
Object  .o      raw instruction bytes                 linker input
```

All intermediate formats are binary with a magic number, checksum,
and compact encoding.  To inspect: `fxc dump --core module.fxc`.

### 20.2 FX to FXCore: Verification and Erasure

This is where 90% of the compiler's intelligence lives.

**Parse and desugar.**  Source text becomes AST.  Desugaring
normalizes syntax: dot-shorthand to lambdas, `x.method(args)` to
`Type.method(x, args)`, `for` to fold, `|>` to application,
comprehensions to filter/map.

**Elaborate and verify.**  All twenty-two dimensions checked.  Type
inference, usage grade checking, effect checking, security label
checking, ownership and borrow checking, session protocol checking,
machine property verification, SMT verification of refinements and
bit-level constraints, contract migration totality.

**Monomorphize.**  Generic functions instantiated at concrete types:
`map<i64, string>` becomes `map_i64_string`.

**Compile constructs.**  Machines become state enums and dispatch
functions.  Contracts become validator/serializer/deserializer
functions.  `impl` blocks become namespaced top-level functions.

**Erase.**  Refinements, security labels, protocol states,
provenance, trust levels, observability markers, complexity bounds,
precision bounds, space bounds, clock domains, usage grades,
mutation markers, reentrancy annotations — all removed.  Drop calls
inserted where linear values leave scope.  `secure_zero` calls
inserted before drop for classified data.  Volatile markers inserted
for MMIO accesses.  Trust boundary validators inserted from
contracts.

**High-level optimize.**  Inlining, pipeline fusion, deforestation,
constant propagation, dead code elimination, CSE,
defunctionalization, contract validator elision for internal
boundaries.

### 20.3 FXCore to FXLow: Type-Directed Lowering

Types are consumed at this layer.  Structured data becomes flat
memory.  FXCore carries full type information; FXLow has only
sized values and explicit memory operations.

**FXCore operations** (~50 total):

```
Arithmetic:    IAdd, ISub, IMul, IDiv, IMod, INeg
               FAdd, FSub, FMul, FDiv, FNeg, FSqrt
               BAdd, BSub, BMul (bits(n) arithmetic)
Comparison:    ICmp, FCmp, BCmp (returns bool)
Logical:       And, Or, Not, Xor
Bitwise:       BAnd, BOr, BXor, BNot, BShl, BShr, BAshr
               BConcat, BSlice, BZeroExt, BSignExt
Conversion:    IntToFloat, FloatToInt, Narrow, Widen, BitCast
Control:       If, Match, Call, TailCall, Return
Binding:       Let, LetRec
Allocation:    Alloc(strategy, size, align), Free(strategy, ptr)
Memory:        Load(ptr, offset, type), Store(ptr, offset, value, type)
Linear:        Drop(ptr, destructor), SecureZero(ptr, size)
               Move(src), Clone(src)
Data:          Construct(tag, fields), Project(value, field_index)
               Tuple(values), TupleProj(tuple, index)
Closure:       MakeClosure(fn_ptr, captures), CallClosure(closure, args)
               ClosureEnvProj(closure, index)
Effect:        Perform(effect_op, args), Handle(body, handlers)
Atomic:        AtomicLoad, AtomicStore, AtomicCAS, Fence
Ghost:         GhostCreate, GhostConsume (erased — zero-cost)
Contract:      Validate(contract, raw), Encode(contract, value)
               Decode(contract, raw)
```

Each FXCore operation carries: monomorphic type of every operand,
linearity annotation (own/ref/ghost), region annotation for
allocations, effect set, and source location for debug info.

**FXLow operations** (~100 total):

```
Arithmetic:    IAdd, ISub, IMul, IDiv, IMod (sized: i8..i64)
               FAdd, FSub, FMul, FDiv (f32, f64)
               VecAdd, VecSub, VecMul, VecDiv (SIMD: width × lanes)
Memory:        Load(dst, base, offset, width)
               Store(base, offset, src, width)
               StackAlloc(size, align), FrameSlot(index)
               RegionBump(region_id, size, align)
               SlabAlloc(type_id), SlabFree(type_id, ptr)
               PoolAlloc(size), PoolFree(size, ptr)
Control:       Branch(cond, true_block, false_block)
               Jump(block), Switch(value, cases, default)
               Call(fn, args), IndirectCall(fn_ptr, args), Return(value)
Conversion:    Trunc, ZExt, SExt, FPExt, FPTrunc, BitCast
Sync:          Fence(ordering), AtomicLoad(dst, addr, ordering)
               AtomicStore(addr, src, ordering)
               AtomicCAS(dst, addr, expected, new, succ_ord, fail_ord)
               LockAcquire(lock_id), LockRelease(lock_id)
Linear:        Drop(ptr, destructor_fn), SecureZero(ptr, size)
SSA:           Phi(block_value_pairs)
```

FXLow values are virtual registers with explicit bit widths.  No
types remain — just sized values.  But the sizes are exact because
they were computed from types in FXCore.

**The lowering transforms:**

ADTs become tagged memory:

```
type shape
  Circle(radius: f64);
  Rect(w: f64, h: f64);
end type;
// Circle: [tag:u8=0][pad:7][radius:f64]     = 16 bytes
// Rect:   [tag:u8=1][pad:7][w:f64][h:f64]   = 24 bytes
// Union:  max(16, 24) = 24 bytes per value
```

Pattern matches become decision trees, then branches.  Closures
become structs (captured values) plus function pointers:

```
// FXCore:
let offset = 10;
let f = fn(x) => x + offset;
f(42)

// FXLow:
v_closure = StackAlloc(16, align: 8)
Store(v_closure, 0, fn_anon_17, i64)      // function pointer
Store(v_closure, 8, v_offset, i64)        // captured variable
v_fn = Load(v_closure, 0, i64)
v_cap = Load(v_closure, 8, i64)
v_result = IndirectCall(v_fn, [const_i64(42), v_cap])
```

Allocation strategies resolve to concrete calls.  Linear drops
become `Drop` + `SecureZero` + `Free` sequences.  Synchronization
operations (§21.2) are inserted at this stage based on the
happens-before analysis from FXCore.

### 20.4 FXLow to FXAsm: Instruction Selection and Register Allocation

Each FXLow operation maps to target instructions via the ISA
semantics module:

```
FXLow                    x86_64
────────────────────     ──────────────────────
IAdd(dst, a, b, i64)    ADD dst, b
IMul(dst, a, b, i64)    IMUL dst, b
FAdd(dst, a, b, f64)    VADDSD dst, a, b
VecAdd(dst, a, b, f32, 8)  VADDPS ymm_dst, ymm_a, ymm_b
Load(dst, base, off)    MOV dst, [base + off]
Call(dst, fn, args)      MOV rdi, a0; CALL fn; MOV dst, rax
```

SIMD width resolved here based on target feature flags.

Register allocation: liveness analysis, interference graph, graph
coloring (or linear scan for fast compilation).  Spills go to stack.
Linearity improves liveness precision — a consumed value's register
is freed at the consumption point, not at the last possible use.

Frame layout: return address, saved registers, local stack slots,
spill slots, outgoing call arguments, alignment padding.

### 20.5 Atomic Instruction Selection

Atomic operations (§11.10) compile to a fixed instruction sequence
per target.  The mapping is not a suggestion to a backend — it is
the operational semantics of atomic operations in FX.  A program's
observable concurrent behavior is determined by (1) the formal ISA
memory model of the target (see Appendix G), and (2) the per-
(operation, ordering, width) emit sequence below.

Because the compiler controls source-to-bytes translation end to
end — no LLVM, no speculation across atomics — the source
semantics are the worst-case envelope across supported targets.
A program that is DRF-SC at the source is DRF-SC on every target
by construction of the emit table.

`fxc dump --atomics M.fx` prints the exact instruction sequence
emitted for every atomic access in module M, per target.  This
is the audit trail for CT crypto and lock-free data structures.

#### 20.5.1 Supported targets and baselines

```
Target      Baseline ISA          Atomics
─────────   ──────────────────   ────────────────────────────────
x86-64      Intel 64 (SSE2+)     native 1/2/4/8 byte; CMPXCHG16B
                                 for 16 byte
arm64       ARMv8.1-A (LSE)      native 1/2/4/8 byte via LSE;
                                 CASP for 16 byte
rv64        RV64GC + Zaamo       native 4/8 byte; 1/2 byte via
                                 mask-CAS loop (Zabha optional);
                                 16 byte via seqlock fallback
mips64      MIPS64r2              native 4/8 byte via LL/SC;
                                 1/2 byte via mask-CAS loop
```

Pre-LSE ARMv8.0 is available only under profile `embedded_arm64`
with explicit opt-in; baseline ARM64 requires LSE.  RV64 with
Zacas (single-instruction CAS) is supported as an optimization;
baseline uses LR/SC loops for CAS.  RV64 with Zabha (byte/half
atomics) is supported as an optimization; baseline uses mask-CAS
for 1/2-byte atomics.  MIPS64 is a legacy target available only
under profile `legacy_mips`.

#### 20.5.2 Load and store

```
atomic<T>::load(@Ord) where sizeof(T) ∈ {1, 2, 4, 8}

@Ord        x86-64              arm64           rv64              mips64
─────────   ──────────────────  ────────────   ────────────────  ─────────────
Relaxed     MOV r, [m]          LDR r, [m]      LD r, o(m)        LD r, o(m)
Acquire     MOV r, [m]          LDAR r, [m]     LD; FENCE R,RW    LD; SYNC 16
SeqCst      MOV r, [m]          LDAR r, [m]     FENCE RW,RW;      SYNC 0; LD;
                                                LD; FENCE R,RW    SYNC 0
```

On x86-64, every aligned MOV of word size or smaller is atomic by
ISA guarantee (SDM vol.3 §8.1.1), and TSO gives Acquire and
SeqCst for free on loads.  On arm64 ARMv8.1+, LDAR is RCsc —
load-acquire that participates in a multi-copy-atomic ordering
across cores, which is exactly SeqCst for loads.  On rv64, the
ISA Manual Table A.6 specifies the explicit fence sequence for
SeqCst loads.

```
atomic<T>::store(@Ord) where sizeof(T) ∈ {1, 2, 4, 8}

@Ord        x86-64              arm64           rv64              mips64
─────────   ──────────────────  ────────────   ────────────────  ─────────────
Relaxed     MOV [m], r          STR [m], r      SD r, o(m)        SD r, o(m)
Release     MOV [m], r          STLR [m], r     FENCE RW,W; SD    SYNC 17; SD
SeqCst      XCHG [m], r         STLR [m], r     AMOSWAP.D.AQRL    SYNC 0; SD;
                                                x0, r, (m)        SYNC 0
```

On x86-64 we emit XCHG for SeqCst stores rather than MOV+MFENCE;
the Intel Optimization Manual §3.4.2.2 recommends XCHG as slightly
faster on Skylake-and-later.  On arm64, STLR is RCsc and suffices
for SeqCst without a following DMB.  On rv64, AMOSWAP with AQRL
gives one-instruction SeqCst store when Zaamo is present; baseline
falls back to the fence-bracketed SD sequence.

Sub-word loads and stores (u8, i8, u16, i16) emit width-appropriate
mnemonics (MOVZX, LDRB, LBU, LB; STRB, SB).  Natural alignment is
required; enforced via type layout.

#### 20.5.3 Atomic read-modify-write

```
atomic<T>::fetch_add(@Ord, delta) where sizeof(T) ∈ {4, 8}

@Ord        x86-64                   arm64 (LSE)        rv64 (Zaamo)
─────────   ──────────────────────   ────────────────   ─────────────────
Relaxed     LOCK XADD [m], r         LDADD r1, r0, [m]   AMOADD.D
Acquire     LOCK XADD [m], r         LDADDA              AMOADD.D.AQ
Release     LOCK XADD [m], r         LDADDL              AMOADD.D.RL
AcqRel      LOCK XADD [m], r         LDADDAL             AMOADD.D.AQRL
SeqCst      LOCK XADD [m], r         LDADDAL             AMOADD.D.AQRL
```

All @Ord values on x86-64 compile to the same sequence: LOCK is a
full fence, so every LOCK-prefixed RMW is simultaneously Acquire,
Release, AcqRel, and SeqCst.  The @Ord annotation is still
meaningful for portability (the source code runs correctly on all
targets) and for the auto-sync optimizer (§21.2).

On arm64 LSE, the suffix letters encode ordering: A = acquire,
L = release, AL = acq+rel.  No DMB needed — LSE atomics provide
the requested ordering in-instruction.

On rv64 with Zaamo, the .AQ/.RL/.AQRL suffixes on the AMO encode
ordering directly.  Baseline RV64G (without Zaamo) uses an LR/SC
loop with explicit fences.

Equivalent tables hold for `fetch_sub` (negated delta on x86,
LDADD/AMOADD with negated on arm/rv), `fetch_and` (LOCK AND,
LDCLR inverted, AMOAND), `fetch_or` (LOCK OR, LDSET, AMOOR),
`fetch_xor` (LOCK XOR, LDEOR, AMOXOR).

```
atomic<T>::swap(@Ord, new_value)

@Ord        x86-64              arm64 (LSE)          rv64 (Zaamo)
─────────   ──────────────      ──────────────      ─────────────────
Relaxed     XCHG [m], r         SWP r1, r0, [m]      AMOSWAP.D
Acquire     XCHG [m], r         SWPA                AMOSWAP.D.AQ
Release     XCHG [m], r         SWPL                AMOSWAP.D.RL
AcqRel      XCHG [m], r         SWPAL               AMOSWAP.D.AQRL
SeqCst      XCHG [m], r         SWPAL               AMOSWAP.D.AQRL
```

XCHG on x86-64 is implicitly LOCK-prefixed on a memory operand —
@Ord is free.

#### 20.5.4 Compare-and-swap

```
atomic<T>::cas(@Ord, expected, desired) -> (T, bool)
   where sizeof(T) ∈ {4, 8}

@Ord        x86-64                    arm64 (LSE)     rv64 (Zacas)     rv64 (no Zacas)
─────────   ──────────────────────    ─────────────   ───────────────  ──────────────────
Relaxed     LOCK CMPXCHG [m], r       CAS r1, r0,     AMOCAS.D         LR.D / SC.D loop
                                      [m]
Acquire     LOCK CMPXCHG [m], r       CASA            AMOCAS.D.AQ      LR.D.AQ / SC.D
Release     LOCK CMPXCHG [m], r       CASL            AMOCAS.D.RL      LR.D / SC.D.RL
AcqRel      LOCK CMPXCHG [m], r       CASAL           AMOCAS.D.AQRL    LR.D.AQ / SC.D.RL
SeqCst      LOCK CMPXCHG [m], r       CASAL           AMOCAS.D.AQRL    LR.D.AQ / SC.D.RL
```

x86-64 expected is in RAX (compiler-managed); result in RAX with
ZF.  All orderings identical at emit because LOCK is full fence.

On rv64 without Zacas, the LR/SC loop is:

```
; atomic<u64>::cas(AcqRel, m, expected, desired) without Zacas:
1:  LR.D.AQ   t0, (m)
    BNE       t0, expected, 2f
    SC.D.RL   t1, desired, (m)
    BNEZ      t1, 1b        ; retry on SC failure
2:  ; t0 = original value; bool = (t0 == expected)
```

`cas_weak` on rv64 without Zacas omits the retry — the caller
wraps in their own retry loop.  This is the right primitive for
lock-free data structures where each retry attempt may want to
re-read inputs.

#### 20.5.5 Fences

```
fence(@Ord) — process-wide memory barrier

@Ord        x86-64           arm64           rv64            mips64
─────────   ────────────     ──────────     ────────────    ─────────
Acquire     (compiler        DMB ISHLD       FENCE R,RW      SYNC 16
             barrier only;
             no instruction)
Release     (compiler        DMB ISHST       FENCE RW,W      SYNC 17
             barrier only)
AcqRel      (compiler        DMB ISH         FENCE RW,RW     SYNC 0
             barrier only)
SeqCst      MFENCE           DMB ISH         FENCE RW,RW     SYNC 0
```

"Compiler barrier only" means the FX IR disallows reordering
memory operations across the fence, but no CPU instruction is
emitted.  On x86 TSO, program order is preserved for all
load/load, load/store, and store/store combinations, so
Acquire/Release/AcqRel fences need no CPU instruction.

#### 20.5.6 Double-word (128-bit) atomics

```
atomic_wide<T>::load/store/swap/cas(@Ord)
   where sizeof(T) = 16 and alignof(T) = 16

            x86-64                         arm64 (LSE)             rv64
─────────   ──────────────────────────    ──────────────────     ─────────────
load        LOCK CMPXCHG16B with          LDP (or LDXP/STXP      (not available;
            expected = desired            pair) with DMB for SC   use seqlock<T>)
store       LOCK CMPXCHG16B in CAS loop   STXP in CAS loop        (not available)
swap        LOCK CMPXCHG16B in CAS loop   CASP                    (not available)
cas         LOCK CMPXCHG16B                CASP                    (not available)
```

`atomic_wide<T>` compiles only on targets that support it.  On
rv64 without AMOCAS.Q (not yet ratified), instantiating
`atomic_wide<T>` is compile error T054 with suggestion to use
`seqlock<T>` or enable a future Zacas-Q target feature.

CMPXCHG16B has a fixed register assignment: expected in RDX:RAX,
desired in RCX:RBX, memory operand in any addressing mode.  CASP
requires consecutive even-odd register pairs.  The compiler
handles the register dance; source code is arch-independent.

#### 20.5.7 Portable fallback: seqlock<T>

For values larger than the largest hardware atomic, or for targets
lacking double-word atomics, FX provides `seqlock<T>` for any
`T : @[copy]`.  The sequence-lock protocol (Linux kernel uses
this for seqcount/seqlock):

```
seqlock<T> implementation (portable across all targets):

  struct { counter: atomic<u64>; data: T; }

  write(new_value):
    old = counter.load(@Relaxed)
    counter.store(old + 1, @Relaxed)         ; mark odd = writing
    fence(@Release)
    data = new_value
    fence(@Release)
    counter.store(old + 2, @Relaxed)         ; mark even = done

  read() : T:
    loop:
      c1 = counter.load(@Acquire)
      if c1 is odd: retry                    ; writer in progress
      copy = data                             ; non-atomic bytewise copy
      fence(@Acquire)
      c2 = counter.load(@Relaxed)
      if c1 != c2: retry                     ; write happened during read
      return copy
```

`seqlock<T>` is always available regardless of target or T's size.
It requires `T : @[copy]` because the read performs a bytewise
copy that may be invalidated by a concurrent write — linear T
would lose ownership tracking across the potential retry.  For
linear values, use `exclusive_access<T>` (mutex-based, deferred
to Std.Sync), which enforces single-thread access with real linear
semantics.

**The portability rule.**

```
sizeof(T) <= word_size(target)      → atomic<T>       always works
sizeof(T) = 2 * word_size(target)   → atomic_wide<T>  if target supports
                                    → seqlock<T>      always fallback
sizeof(T) > 2 * word_size(target)   → seqlock<T>      only option
```

Enforced at type-check time.  `atomic_wide<T>` on an unsupporting
target produces T054 with a concrete suggestion.

#### 20.5.8 Per-arch constraint summary

```
Feature                     x86-64  arm64   rv64       mips64
─────────────────────────   ──────  ──────  ────────   ────────
atomic<T>, T ≤ 8 byte       ✓       ✓       ✓          ✓
atomic<T>, T = 1,2 byte     ✓       ✓       mask loop  mask loop
                                              (native
                                               with
                                               Zabha)
atomic<T>, T = 4,8 byte     ✓       ✓       ✓          ✓
atomic_wide<T>, T = 16      ✓       ✓       seqlock    N/A
CAS single-instruction      ✓       ✓       Zacas      LL/SC
                                              only
RMW single-instruction      ✓       LSE      Zaamo      LL/SC
Release fence cost          0       1 instr  1 instr    1 instr
SeqCst load cost            1 instr 1 instr  3 instr    3 instr
SeqCst store cost           1 instr 1 instr  1 instr    3 instr
SeqCst RMW cost             1 instr 1 instr  1 instr    5+ instr
```

**Portable source, optimal emit.**  Every program using
`atomic<T>` with default `@SeqCst` compiles to correct code on
every target; the compiler picks the best instruction sequence
from the tables above.  Programmers tune per-arch via source-
level `@Relaxed` / `@Acquire` / etc. at the access site, not via
per-arch conditionals.

**Arch-specific intrinsics** for the small minority needing
precise control live in `Std.Arch.X86`, `Std.Arch.Arm64`,
`Std.Arch.Rv64` with typed wrappers around individual
instructions (`mfence`, `dmb_ish`, `fence_rw_rw`, `xchg`, `cas16`,
`rdtsc`, `cntvct`, `rdcycle`).  Using an arch-specific intrinsic
restricts the enclosing function to that arch; building for a
different target produces compile error P003 (`arch intrinsic
incompatible with build target`).

### 20.6 FXAsm to Object: Encoding

One-pass encoding of target instructions to bytes.  The encoding
uses the format types from §18.1, verified:
`decode(encode(insn)) == insn` for every instruction.

Output: ELF (Linux), Mach-O (macOS), PE (Windows).

### 20.7 ISA Formalization

Each target ISA is an FX module defining machine state and
instruction semantics:

```
module Isa.X86_64

type State = {
  gpr   : array(bits(64), 16);
  xmm   : array(bits(256), 16);
  flags : Flags;
  rsp   : bits(64);
  rip   : bits(64);
  mem   : bits(64) -> bits(8);
};

fn execute(s: State, insn: Insn) : State
= match insn;
    Add(dst, Reg(src)) =>
      let result = s.gpr[dst] + s.gpr[src];
      { s with gpr[dst]: result,
               flags: arith_flags(s.gpr[dst], s.gpr[src], result),
               rip: s.rip + encoded_length(insn) };
    Call(target) =>
      let rsp_new = s.rsp - 8;
      { s with rsp: rsp_new,
               mem: write_qword(s.mem, rsp_new, s.rip + encoded_length(insn)),
               rip: target };
    Ret =>
      { s with rip: read_qword(s.mem, s.rsp),
               rsp: s.rsp + 8 };
  end match;
```

The same module serves three purposes: codegen verification (the
selected instruction sequence computes the same result as the FXLow
operation), hardware verification (§18.12), and optimizer instruction
rewriting (peephole rules proved equivalent via ISA semantics).

Microarchitecture cost models are separate modules providing
latency and throughput per instruction for specific processors.
They guide instruction scheduling without affecting correctness.

**Sail import.**  For ISAs whose authoritative golden model is
maintained in Sail (Armstrong et al. POPL 2019) — the official
executable model used by RISC-V International, ARM Morello, and
the CHERIoT line — FX consumes the Sail spec directly rather
than redefine its semantics:

```
@[from_sail("riscv")]
hardware module rv64
  // ISA semantics imported from sail-riscv golden model;
  // exposed as types in this hardware module's body
  fn execute(state: arch_state, insn: bits(32)) : arch_state
    with Sync(clk);
end hardware module;
```

The compiler generates the FX-side bindings from the Sail spec at
build time (Sail's Lean / Rocq / Isabelle backends supply the
underlying definitions).  Updates to the Sail spec — a new RISC-V
extension, a Morello revision — are absorbed by re-running the
importer.

The CHERIoT-Ibex methodology (arXiv:2502.04738, Feb 2025) is the
canonical proof template: an FX `hardware module` is verified to
refine its imported Sail spec via the §13.6 / §18.12
`refinement` declaration, with observational correctness as the
property — the stream of memory interactions matches the Sail
spec when started in the same initial state.

### 20.8 End-to-End Correctness

The composition of per-layer correctness theorems:

```
theorem compiler_correct :
  forall(program: source, input: bytes),
    well_typed(program) ==>
    observable(run_binary(compile(program), input))
      == observable(evaluate(program, input));
```

The proof chains simulation relations:

```
evaluate(P, I)
  == eval_fxcore(erase(elaborate(P)), I)       // erase_correct
  == eval_fxlow(lower(erase(...)), I)          // lower_correct
  == eval_fxasm(select(alloc(lower(...))), I)  // select_correct + alloc_correct
  == run_bytes(encode(select(...)), I)         // encode_correct
  == run_binary(compile(P), I)                 // definition
```

**Verified-compilation precedent.**  The simulation-chain
discipline above tracks the model of CompCert (Leroy CACM 2009;
within 16% of GCC -O2 on KV3 VLIW, 12% on ARM, 30% on RISC-V at
recent benchmarks) and CakeML (Tan et al. ICFP 2016, JFP 2019;
end-to-end verified ML compiler in HOL4 with verified
bootstrapping).  Each layer admits a local correctness proof
and the composition is the master theorem.  The realistic upper
bound on what verified compilation costs in optimization quality
is the CompCert performance result; FX expects a similar
performance budget at mature optimization.

**Promising 2.0 source semantics for atomics.**  The atomic
operations of §11.10 and per-arch emit table of §20.5 follow
Promising 2.0 (Lee-Cho-Lahav-Vafeiadis-Dreyer PLDI 2020) as the
operational semantics for the source-level model.  A thread can
*promise* to execute a write `w` in the future, allowing other
threads to read from `w` out of order; the promise must be
eventually fulfilled, and the certification step structurally
forbids out-of-thin-air values.  An FX program using only
`@SeqCst` atomics is sequentially consistent on every supported
architecture (the standard DRF-SC theorem); a program using
weaker orderings is governed by the per-arch emit table, with
Promising 2.0 as the upper bound on observable behaviors.


## 21. Optimization

### 21.1 Pipeline Fusion

Adjacent `map`, `filter`, `map` operations on eager sources fuse
into a single pass with no intermediate allocations.  Linear types
prove the intermediates are consumed once, making fusion safe:

```
// source:
data |> map(.score + 1) |> filter(fn(x) => x > 0) |> map(.value * 2)

// fused:
data |> fused(fn(it) =>
  let s = it.score + 1;
  if s > 0; Some(it.value * 2) else None end if)
```

### 21.2 Automatic Synchronization Inference

Every atomic operation (§11.10) has a source-level `@Ord`
annotation with default `@SeqCst`.  The compiler may emit a
sequence corresponding to a **weaker** ordering when it can prove
via happens-before analysis that the stronger ordering is already
established by program structure.  The downgrade is an
optimization — observable behavior is preserved because the emit
table (§20.5) guarantees each weaker ordering is correct whenever
the happens-before precondition holds.

**Downgrade lattice** (permitted transformations, always from
source to emitted):

```
Source      May emit
─────────   ──────────────────────────────
SeqCst      AcqRel, Acquire, Release, Relaxed
AcqRel      Acquire, Release, Relaxed
Acquire     Relaxed
Release     Relaxed
Relaxed     (no downgrade)
```

**Downgrade conditions** (any one sufficient per atomic access):

 1. **Channel-established ordering.** The access is dominated by
    a channel send or receive (§11.3) that already establishes
    the required happens-before edge.  Send-receive pairs carry
    implicit Release-Acquire ordering (the emit table for channel
    operations includes the appropriate fences).
 2. **Join-point ordering.** The access is dominated by a task
    group join (§11.7) or a prior RMW on the same cell — both
    are synchronization points.
 3. **Data-independent use.** The loaded value only feeds into
    logging, statistics, or debug output (no subsequent dependent
    memory access).  Load may downgrade to Relaxed.
 4. **No cross-thread read before join.** The stored value is not
    subsequently read on any thread before a joinpoint.  Store
    may downgrade to Relaxed.
 5. **Single-threaded execution.** No `spawn` is reachable from
    the enclosing scope.  All atomic ops downgrade to Relaxed.

**The @[no_downgrade] escape.**  An access annotated
`@[no_downgrade]` pins the source ordering — the compiler emits
the exact sequence corresponding to the source `@Ord` per
§20.5.  This is the required annotation for constant-time crypto
code (§12.5) where emitted instruction sequences must be timing-
uniform across inputs.

```
@[no_downgrade]
let k = key_slot.load(@SeqCst);
// compiler emits:
//   x86-64: MOV r, [m]            (still SC on x86 TSO)
//   arm64:  LDAR r, [m]            (RCsc SC)
//   rv64:   FENCE RW,RW; LD; FENCE R,RW
// even if program structure would allow downgrade to Relaxed
```

**Non-atomic synchronization.**  Beyond atomic downgrade, the
compiler also handles:

**No fence needed.** If linearity + channel semantics already
serialize the access, the compiler emits nothing (not even a
compiler barrier).  Linear values transferred through channels
are the textbook case — the send on one side and receive on the
other establish the required happens-before via the channel's
own atomic state, which is already in the emit table.

**Atomic RMW pattern detection.** If the programmer writes
`let old = ctr.load(); ctr.store(old + 1);` on an atomic cell,
the compiler recognizes the read-modify-write and rewrites to
`ctr.fetch_add(1, @AcqRel)` — one atomic instead of a racy
load-then-store pair (which would be rejected anyway because
the pair isn't atomic against concurrent writers).

**Lock-free pattern detection.** Common lock-free idioms
(Treiber stack push, M&S queue enqueue, Hazard-pointer
publishes) are recognized and lowered to the canonical verified
sequence from the standard library, avoiding the hand-rolled
version's potential bugs.  The compiler does not synthesize new
lock-free algorithms — it only recognizes the ones the stdlib
has verified templates for.

**Mutex versus atomic.** When mutual exclusion is needed over a
multi-step operation (not expressible as a single RMW), the
programmer explicitly uses `mutex<T>` from Std.Sync.  The compiler
does not silently insert locks; if a race is detected, it is a
compile error, not an automatic mutex insertion.

**Audit via fxc dump.**  `fxc dump --atomics module.fxc`  shows
every atomic access with its source `@Ord`, the downgrade
decision (or @[no_downgrade] pin), and the emitted instruction
sequence per target.  This is the trace security auditors,
concurrent-code reviewers, and LLM-generated-code inspectors
work from.

### 21.3 Aggressive Optimization

Under `--release=aggressive` or `@[optimize(aggressive)]`, the
compiler spends more time for faster output.  It treats refinement
types as optimization input — tighter specifications produce faster
code.

**Superoptimization.**  For small kernels (loop bodies, comparison
chains, bit manipulation), the compiler tries all instruction
sequences up to a bounded length and keeps the shortest that
computes the same result.  Equivalence is checked via SMT over the
ISA semantics.  Refinements reduce the input space, making the
search tractable.

**Whole-program specialization.**  The compiler looks at how each
function is actually called and generates specialized versions for
the specific refinements at each call site.  If `sort` is always
called with lists of length <= 64, a version using insertion sort
with no heap allocation is generated.

**Verified loop transformations.**  Tiling for cache hierarchy
(tile size computed from known array dimensions and cache line
size).  Fusion of adjacent producer-consumer loops (linearity proves
the intermediate is consumed once).  Vectorization (Tot + contiguous
array = no aliasing, no side effects).  Parallelization (Tot +
disjoint regions = safe to split across cores).

**Data structure selection from refinements.**

```
Refinement                       General       Replacement
───────────────────────────────  ────────────  ──────────────
map(K, V) where K: nat { <256 } hash map      direct array
set(nat { <64 })                 hash set      bits(64) bitmask
list(T) { length <= 8 }         linked list   inline array
queue(T) { length <= N }        linked list   ring buffer
option(nat { >0 })              tagged union   zero = None
string { length <= 23 }         heap string   inline SSO
```

**Partial evaluation.**  When arguments are known at compile time
(literals, `comptime` values, refinements narrowing to one value),
the compiler evaluates the parts that depend on them and leaves the
rest as runtime code.

**Rewrite templates.**  A database of pattern/replacement pairs
where each replacement is proved equivalent.  The compiler matches
user code against the database and substitutes faster
implementations.  Templates ship with the compiler and are
extensible by library authors.

**Refinement suggestions.**  The compiler reports which refinements
would enable blocked optimizations:

```
"adding pre length(items) <= 4096 enables stack allocation
 (avoids 3 heap allocations per call)"
"adding overflow(wrap) enables single imul instead of checked multiply"
"key type nat { <256 } allows replacing hash map with direct array"
```

**Compile time budget.**  `fxc build --release=aggressive --budget 5m`
prioritizes optimizations by expected payoff within the time limit.

**E-graph extraction via SmoothE.**  Equality-saturation rewrites
(superoptimization, peephole, vectorization) extract an optimal
expression from an e-graph against a cost function.  Traditional
ILP-based extraction (egg) requires linear cost functions —
`cost(e_1 ∪ e_2) = cost(e_1) + cost(e_2)`, additive
decomposition.  Real per-vendor cost models are non-linear:

```
cost(kernel) = predicted_cycles + α · ULP_drift + β · binary_size
```

ULP drift and binary size compose multiplicatively across kernel
composition, not additively, making ILP a non-starter at scale.
FX's optimizer adopts SmoothE (Cai-Yang-Deng-Zhang ASPLOS 2025
Best Paper), a differentiable, GPU-accelerated extraction
algorithm supporting non-linear cost functions, with reported
8-37× speedup over ILP.  GPU acceleration is optional; small
e-graphs use a CPU-bound fallback.  ILP remains available as a
verified-cost-function fallback for workloads that need
deterministic extraction without GPU dependency.

### 21.4 Binary Size

FX has no mandatory runtime.  The binary contains service modules
only for the effects the program declares.

```
Effect            Service module              Size
───────────────   ────────────────────────    ──────
(none / Tot)      nothing                     0
IO                syscall wrappers            ~200 bytes
Alloc(Stack)      nothing                     0
Alloc(Region)     region bump allocator       ~500 bytes
Alloc(Slab)       slab allocator              ~2 KB
Alloc(Pool)       size-class pool             ~3 KB
Alloc(Rc)         refcount operations         ~500 bytes
Exn               error formatter             ~1 KB
Async             task scheduler              ~4 KB
```

Fixed overhead per binary: ELF header (64 bytes), program header
(56 bytes), entry point wrapper (~50 bytes).

Direct syscall emission — `print("Hello")` compiles to a `write`
syscall instruction, not a call into libc.  No libc, no PLT, no
GOT, no dynamic linker.

Graduated sizes:

```
Program                     Size
──────────────────────────  ─────────
Hello world                 ~250 bytes
Bare-metal LED blink        ~40 bytes
CLI argument parser         ~2 KB
Key-value store (memory)    ~8 KB
HTTP echo server            ~15 KB
JSON API server             ~40 KB
Full web service + DB       ~200 KB
```

Effect-driven linking: if no function in the reachable call graph
has a given effect, the service module for that effect is excluded
regardless of the symbol reference graph.

For embedded targets, the profile can specify `format = "bin"` (raw
binary, no ELF), `runtime = false` (no service modules), and
`max_flash = N` (error if binary exceeds limit).

### 21.5 Tail Call Guarantee

`rec` functions default to requiring tail calls.  Non-tail recursion
must opt in explicitly:

```
fn rec traverse<a: type, b: type>(xs: list(a), acc: list(b)) : list(b)
  decreases xs;
  with TailCall;       // default for rec — error if call not in tail position
= match xs;
    [] => acc;
    [h, ...t] => traverse(t, [f(h), ...acc]);
  end match;

fn rec tree_map<a: type, b: type>(node: tree(a)) : tree(b)
  decreases node;
  with StackRecursion;  // explicit: uses O(depth) stack
= match node;
    Leaf(v) => Leaf(f(v));
    Node(l, r) => Node(tree_map(l), tree_map(r));
  end match;
```

### 21.6 Memoization and Idempotency

Cache semantics as an explicit property:

```
fn generate_nonce() : bits(128) with IO, NeverMemoize;
// caching would reuse nonces — catastrophic for crypto
// compiler prevents any memoization wrapper

fn fib(n: nat) : nat with Memoize;
// declaring memoizability = declaring referential transparency
```

Idempotency for distributed systems:

```
fn create_order(order: order_data) : order_id
  with IO, Idempotent(key: order.client_id);
// second call with same key is a no-op returning same result

fn increment(ref counter: atomic(i64)) : unit
  with Commutative;
// concurrent increments produce same result in any order

fn migrate(ref mut db: database) : unit with IO
  with Reversible(undo: rollback_migration);
  post _ => schema(db) == v2_schema;
// compiler verifies: migrate; rollback = identity
```

### 21.7 Partial Failure Semantics

```
fn write_all(fd: file_handle, data: ref bytes) : unit
  with IO, Atomic;
// all bytes written or error — no partial writes

fn write_partial(fd: file_handle, data: ref bytes) : nat
  with IO, Partial;
  post r => r <= length(data);
// may write fewer bytes — returns count written
```


## 22. Sketch Mode

FX's activation energy is high — the compiler demands types, modes,
and effects before running anything.  Sketch mode eliminates the
up-front cost.  Same syntax, same parser, but the compiler infers
everything it can, converts compile-time checks to runtime checks,
and runs code on a bytecode VM with sub-100ms startup.  When the
code matures, `fxc annotate` upgrades it to typed FX.

### 22.1 The Sketch Profile

Sketch mode is a project profile (§27), not a dialect.  Every
sketch-mode program is valid FX.

```toml
[profile]
mode = "sketch"
```

Sketch mode performs basic type checking but defers all proof
obligations to runtime assertions and relaxes ownership, effects,
security, and other dimensions to warnings.  The result is
comparable to TypeScript in strictness: structural type errors are
caught, everything else is flagged but allowed.

**Fatal in sketch mode** (code is nonsense, rejected):

Core type checking:
- Type mismatch between unrelated types (`string` where `int`)
- Undefined variable, function, type, module, constructor
- Wrong number of arguments to function
- Wrong argument names (named arg doesn't match parameter)
- Duplicate definition in same scope
- Recursive type without indirection (infinite size)
- Kind mismatch (`nat` where `type` expected in type params)
- Applying a non-function (`42(x)`)
- Accessing a field that doesn't exist on the type
- Constructor applied with wrong number of fields

Syntax and structure:
- Parse errors
- Mismatched typed closers (`begin fn ... end match`)
- Missing `return` in block function
- Missing `;` on a statement
- Invalid characters in identifiers (non-ASCII, tick)
- Unterminated string, comment, backtick
- `pub const` (always illegal)
- Top-level `let` (always illegal)
- `pre`/`post`/`decreases` in wrong order

Module system:
- Circular module dependency
- Module not found on `open`/`include`
- Duplicate module declaration

**Warning in sketch mode** (allowed, flagged for release):

Dimension 1 — Type (partial relaxation):
- Missing type annotation on `pub fn` params or return — infer, warn
- Missing kind annotation on type params — infer, warn
- Implicit numeric widening (`u8` to `u32`) — allow, warn
- Implicit numeric narrowing (`i32` to `i16`) — allow, warn "may lose data"
- `decimal` where `f64` expected or vice versa — allow, warn "precision change"
- `int` where fixed-width expected — allow, warn "may overflow"
- `f64` where `decimal` expected — allow, warn "exact to approximate"

Dimension 2 — Refinement:
- `pre` clause not proved — becomes runtime assertion, warn
- `post` clause not proved — becomes runtime assertion after return, warn
- `assert` not proved by SMT — becomes runtime assertion, warn
- Refinement on function parameter not checked at call site — runtime check, warn
- Index might be out of bounds — runtime check, warn
- Division where divisor might be zero — runtime check, warn
- Refinement type narrowing not proved — runtime check, warn

Dimension 3 — Usage/Ownership:
- Linear value used twice — warn "double use"
- Linear value not consumed — warn "resource not consumed, may leak"
- Linear value used after move — warn "use after move"
- Affine value used twice — warn "affine used twice"
- `@[copy]` on type with non-copy fields — warn, allow in sketch
- Borrowing while mutable borrow exists — warn "aliased mutable borrow"
- Moving out of borrowed context — warn

Dimension 4 — Effect:
- Missing effect annotation — infer from body, warn
- Calling effectful function from declared-pure context — warn "effect mismatch"
- Effect not in platform's available set — warn
- Handler doesn't cover all operations — warn "incomplete handler"

Dimension 5 — Security:
- Classified data flowing to IO/log — warn "information flow violation"
- Classified data in format string — warn
- Branch on classified value in non-CT context — warn
- Missing `declassify` — warn "needs explicit declassification"
- Tainted data reaching untainted sink — warn "needs sanitize"

Dimension 6 — Protocol/Session:
- Channel used after protocol complete — warn "channel exhausted"
- Wrong message type on channel — warn "protocol violation"
- Missing dual check on channel pair — warn
- Session branching on secret data — warn

Dimension 7 — Lifetime/Region:
- Reference outlives its data — warn "dangling reference"
- Borrow escapes scope — warn "borrow escapes"
- Missing lifetime annotation on `pub fn` — infer, warn

Dimension 8 — Provenance:
- Unknown provenance data where known required — warn
- Provenance chain broken — warn

Dimension 9 — Trust:
- `sorry` in code — warn "proof placeholder"
- `axiom` usage — warn "assumed, not proved"
- Calling `sorry`-tainted function — warn "trust level: sorry"
- Trust level below `Verified` — warn

Dimension 10 — Representation:
- `repr(C)` on type with non-C-compatible fields — warn
- Missing `repr` where FFI expects it — warn
- Packed representation with alignment issues — warn

Dimension 11 — Observability/CT:
- Branch on secret-graded value — warn "CT violation"
- Secret-dependent array index — warn "timing side channel"
- Variable-time operation on secret — warn

Dimension 12 — Clock domain:
- Mixing signals from different clocks without synchronizer — warn
- Combinational loop — warn

Dimension 13 — Complexity:
- Declared cost exceeded by call tree — warn "complexity exceeds bound"
- Missing complexity annotation where required — warn
- `unbounded` not declared — warn

Dimension 14 — Precision:
- Float operation accumulates error beyond declared bound — warn
- Mixing `decimal` and `f64` without explicit conversion — warn

Dimension 15 — Space:
- Allocation exceeds declared stack bound — warn
- Heap allocation in stack-only context — warn

Dimension 16 — Overflow:
- Fixed-width arithmetic without overflow annotation — warn
- Mixing `wrap` and `trap` overflow modes — warn

Dimension 17 — FP order:
- `Reassociate` on computation requiring deterministic results — warn

Dimension 18 — Mutation:
- Mutating an immutable binding — warn "mutation of immutable"
- Append on non-append-only collection — warn
- Non-monotonic update on monotonic field — warn

Dimension 19 — Reentrancy:
- Recursive call without `rec` keyword — warn "undeclared recursion"
- Recursive function without `decreases` — warn "no termination proof"
- Mutual recursion without `and` — warn

Named arguments:
- Positional args for multi-param function — warn

Patterns:
- Non-exhaustive match — warn, runtime error if unmatched case hit
- Overlapping/redundant patterns — warn "unreachable pattern"

Naming conventions:
- `snake_case` where `PascalCase` expected — warn
- `PascalCase` where `snake_case` expected — warn
- Non-SCREAMING_SNAKE const — warn

Code quality:
- Unused variable — warn
- Unused import — warn
- Shadowed variable — warn
- Dead code after unconditional return/fail — warn
- Empty match arm body — warn

Machine properties:
- `deadlock_free` not proved — warn
- `reachable`/`always`/`never` not proved — warn
- Transition guard not proved — runtime check, warn

Contract checks:
- Migration not proved total — warn
- Compatibility matrix not verified — warn
- Format binding incomplete — warn
- Access mode violation — warn

Hardware-specific:
- Synthesizability violation (IO in hardware block) — warn
- Pipeline hazard unresolved — warn
- Register access mode violation (write to RO) — warn

Class/instance:
- Coherence violation (duplicate instance) — warn
- Orphan instance — warn
- Missing method in instance — warn
- Law not verified — warn

Convenience relaxations:
- Mutable references without ceremony: `let x = 5; x = 10;`
  works — compiler silently wraps in `ref`, warns.
- A prelude: common types and functions in scope without imports.

**Silent in sketch mode** (completely ignored):

- Full SMT proof discharge — proofs are runtime assertions
- Termination proof checking — `decreases` ignored
- Trust level propagation and enforcement
- Proof stability tracking (timing budgets)
- Spec validation (vacuous/unrealizable spec detection)
- Automatic lemma extraction suggestions
- Proof minimization suggestions
- Specification coverage analysis
- Fuel/ifuel SMT tuning
- Cross-module axiom consistency deep check

At the end of compilation, the compiler produces a summary:

```
Sketch report for Module.fx:
  12 functions compiled
  0 fatal errors
  23 warnings:
    8 type annotations (auto-inferred)
    5 effect annotations (auto-inferred)
    4 ownership violations (relaxed)
    3 security flow warnings
    2 non-exhaustive patterns
    1 sorry placeholder
  To upgrade: fxc annotate Module.fx
```

### 22.2 The Bytecode VM

Sketch mode compiles to bytecode: parse, infer, emit, run.  No
monomorphization, no native codegen, no SMT.  The VM is stack-based
and simple.  Startup under 100ms for any file under 10K lines.

The bytecode file (`.fxb`) is cached.  On repeat runs with unchanged
source (content hash check), the compiler loads cached bytecode in
under 10ms.

The VM loads native-compiled modules as shared objects and calls
into them via the platform calling convention.  Sketch code runs as
bytecode; stdlib and pre-compiled dependencies run as native code.
The boundary is invisible to the programmer.

Three execution modes:

```
fxc run --sketch file.fx
  Default.  Sketch code is bytecode.  Imports use native when
  available.  Native calls appear in traces as single events.

fxc run --sketch --trace-module Std.List file.fx
  Selective deep tracing.  The named module is forced to bytecode
  for full trace visibility.

fxc run --sketch --full-vm file.fx
  Full bytecode.  Every module including stdlib is interpreted.
  Much slower but leaves no trace blind spots.
```

### 22.3 Record and Replay

The VM records every step.  The recording saves to an `.fxr` file.
From the recording, execution can resume at any bytecode instruction,
not just designated checkpoints.

The recording stores:

The effect log — every IO operation and its result.  On replay,
recorded results are returned instead of performing real IO.  Pure
native calls are re-executed (same result by definition); effectful
native calls are replayed from the log.

A snapshot index — periodic snapshots of full VM state (value stack,
call stack, heap) with bytecode offset and source line.

The instruction trace — every bytecode instruction with operands
and results.

To resume at an arbitrary point, the VM loads the nearest earlier
snapshot and replays forward.

```bash
# Run with recording
$ fxc run --record experiment.fx
# Crashes at line 437 — saves experiment.fxr

# Resume at the crash point
$ fxc replay experiment.fxr --at-crash
[experiment.fx:437] let item = items[idx];
  items : list(item) { length == 5 }
  idx : nat = 7
  ERROR NEXT: index 7 out of bounds

fx> idx
7 : nat
fx> items |> map(.id)
[42, 17, 99, 3, 55]

# Rewind 50 instructions
fx> :rewind 50
[experiment.fx:430] let idx = compute_index(batch, offset);
  batch = 3, offset = 4, idx = 7
```

### 22.4 Mid-Program Interactivity

`inspect;` pauses execution and drops into a REPL:

```
fn train(ref mut model: Model, data: DataLoader) : f32
begin fn
  for epoch in 0..100;
    let loss = train_epoch(ref mut model, ref data);
    if epoch % 10 == 0; inspect end if;
  end for;
  evaluate(ref model, ref data)
end fn;
```

At `inspect`:

```
[inspect at train.fx:6, epoch=10, loss=0.342]
fx> model.layers[0].weight |> stats()
mean=0.001, std=0.023, min=-0.12, max=0.09
fx> :continue
```

For agents, the non-interactive equivalent is `checkpoint`:

```
checkpoint(f"epoch_{epoch}.fxr");
```

The agent loads the checkpoint with
`fxc replay epoch_40.fxr --eval "expression"`.

### 22.5 Traces

The trace reconstructor reads the `.fxr` instruction log and
produces a readable listing where every function call is inlined,
every loop iteration listed, every intermediate value shown with
its inferred type.

```bash
$ fxc trace --full experiment.fx
```

```
[1] let users = load_csv("users.csv");
    users : list(user_record) { length == 10842 }
          @ own, IO, classified, provenance: Source("users.csv")

[2] let active = users |> filter(.active);
    active : list(user_record) { length == 6203 }
           @ own, Tot, classified
    users : CONSUMED

[3] let names = active |> map(.name);
    names : list(string) { length == 6203 }
          @ own, Tot, classified
    active : CONSUMED
```

Verbosity levels: `--values` (values only), default (types and
values), `--full` (all 22 dimensions), `--show mode,security`
(specific dimensions).

### 22.6 Concurrent Traces

Concurrent traces use the `.fxt` binary format — timestamped events
tagged with thread/task ID and Lamport clock.

Event record (64 bytes):

```
timestamp:   u64     Lamport clock value
thread_id:   u32     thread/task identifier
event_type:  u8      instruction | spawn | join | send | recv |
                     lock_acq | lock_rel | fence | atomic |
                     inspect | checkpoint | crash
source_line: u32
bytecode_pc: u32
data_offset: u32     offset into variable-length data section
data_length: u16
```

Events with equal timestamps on different threads are genuinely
concurrent — no ordering exists between them.

Rendering views:

```bash
$ fxc trace --thread worker-1 file.fxt     # per-thread timeline
$ fxc trace --columns file.fxt             # multi-column interleaving
$ fxc trace --interactions file.fxt        # sync points only
$ fxc trace --shared-state file.fxt        # every shared variable access
$ fxc trace --async file.fxt              # coroutine suspend/resume
$ fxc trace --races file.fxt             # potential data races
$ fxc trace --deadlocks file.fxt         # lock cycles
$ fxc trace --stats file.fxt             # aggregate statistics
```

### 22.7 Hot Reload

In the REPL or at an `inspect` breakpoint, editing source files
and typing `:reload` recompiles changed functions to bytecode and
patches the VM's function table.  Existing data stays in memory.

```
fx> let data = expensive_load("big.csv")     // 30 seconds
fx> process(data)                             // wrong results
// ... edit process() ...
fx> :reload
Reloaded: process (signature unchanged)       // 50ms
fx> process(data)                             // fixed, no re-load
```

If a reloaded function's inferred type changed in a way that
conflicts with live values, the VM warns and offers to discard
affected bindings.

For pre-compiled native modules, `:reload` picks up new artifacts
from the build cache.  Edit the library, `fxc build` it in another
terminal, `:reload` in the REPL.

### 22.8 The Gradient

```
sketch              normal              aggressive
──────────────────  ──────────────────  ──────────────────
infer all types     annotate signatures annotate refinements
runtime checks      compile-time checks compile-time proofs
mutable by default  immutable default   tight specifications
bytecode VM         native binary       native + superopt
100ms startup       seconds compile     minutes compile
```

Transition:

```bash
$ fxc annotate src/experiment.fx
  14 annotations needed:
    line 5:  fn process(data) -> fn process(data: list(user)) : list(string)
    line 12: let x = 5; x = 10 -> let x : cell(int) = cell(5); x.set(10)
  3 refinements suggested:
    line 5:  pre length(data) > 0
  2 linearity opportunities:
    line 30: conn never used after line 35 -> make own

$ fxc annotate --apply    // insert all suggestions
```

**Agent-readable output.**  `fxc annotate --format=json` emits
the same suggestions as a structured document for consumption
by the agent protocol (§24); it is also served by
`POST /annotate` on the daemon:

```json
{
  "file": "src/experiment.fx",
  "suggestions": [
    { "line": 5, "col": 10,
      "kind": "type_annotation",
      "before": "fn process(data)",
      "after":  "fn process(data: list(user)) : list(string)",
      "applicability": "machine_applicable",
      "rationale": "inferred from body usage" },
    { "line": 12, "col": 3,
      "kind": "mutable_binding",
      "before": "let x = 5; x = 10",
      "after":  "let x : cell(int) = cell(5); x.set(10)",
      "applicability": "machine_applicable" },
    { "line": 5, "col": 1,
      "kind": "refinement",
      "before": "fn process(data: list(user)) : list(string)",
      "after":  "fn process(data: list(user)) : list(string)\n  pre length(data) > 0;",
      "applicability": "has_placeholders",
      "rationale": "inferred from all observed call sites" }
  ]
}
```

`applicability` follows rustfix's graded scale:
`machine_applicable` (safe to auto-apply), `has_placeholders`
(requires review), `maybe_incorrect` (suggestion only).  Text
output groups suggestions by category; JSON enumerates each
with full location + applicability so an agent can filter,
reorder, and apply selectively via `POST /edit`.


## 23. Testing

FX has six built-in test constructs.  They are language keywords,
not library macros.  The compiler understands them, verifies their
properties, and generates efficient test runners.

### 23.1 Unit Tests

```
test user_creation
  let user = create_user("Alice", 30);
  assert user.name == "Alice";
  assert user.age == 30;
end test;

test connection_lifecycle with IO
  let conn = Connection.connect("localhost", 8080);
  defer conn.close();
  assert conn.is_open();
end test;
```

Assertions: `assert expr;`, `assert expr == expected;`,
`assert_err expr is Variant;`, `assert_raises ExnType { body };`,
`assert_within(tolerance) a b;`.

Tests with effects declare them explicitly: `test name with IO, DB`.

### 23.2 Property-Based Tests

Properties are ordinary boolean-returning functions marked with
the `@[property]` attribute.  The test runner invokes them with
generated inputs; failing cases shrink to minimal
counterexamples.

```
@[property]
fn sort_preserves_length(xs: list(nat)) : bool
  = length(sort(xs)) == length(xs);

@[property]
fn sort_is_sorted(xs: list(nat)) : bool
  = is_sorted(sort(xs));

@[property]
fn reverse_involution(xs: list(nat)) : bool
  = reverse(reverse(xs)) == xs;
```

Property functions reuse the fn grammar — no new declaration
form, no new keyword.  The `@[property]` attribute signals to
the test runner that inputs should be generated and the body
invoked as a test.  Configurable with `@[samples(10000)]` and
`@[max_size(1000)]` alongside `@[property]`.

Custom generators for domain-specific types:

```
@[arbitrary]
instance Arbitrary for UserRecord
  fn arbitrary(ref rng: Rng) : UserRecord
  begin fn
    UserRecord {
      id: rng.nat_range(1, 1000000),
      name: rng.string_alpha(1, 50),
      email: rng.string_matching(r"[a-z]+@[a-z]+\.[a-z]+"),
      role: rng.choose([Admin, User, Guest]),
    }
  end fn;
end instance;
```

### 23.3 Machine Tests

```
test_machine ConnectionState
end test_machine;
```

The compiler explores all reachable states, tests all transitions,
verifies all invariants at every state, and checks deadlock freedom.
For parameterized machines: `@[depth_range(1, 16)]`.  For
infinite-state machines: `@[bound(100)]` with `@[induction]`.

### 23.4 Contract Tests

```
test_contract UserApi format json
end test_contract;
```

Tests round-trip (encode, decode, compare), version migration
(generate random old-version data, migrate, validate), invalid input
(random bytes produce typed errors, not crashes), and access rules.

Multi-format: `test_contract UserApi format json, protobuf`.
Version matrix: `test_contract OrderContract compatibility`.

### 23.5 Benchmarks

```
bench sort_10k
  let data = random_array(nat, 10000);
  sort(data)
end bench;

bench sort_comparison
  @[compare]
  let data = random_array(nat, 10000);
  case "merge_sort" = merge_sort(data);
  case "quick_sort" = quick_sort(data);
end bench;
```

Output: median, p95, p99, allocations, throughput.  Regression
detection: `fxc test --bench --save-baseline` then
`fxc test --bench --compare-baseline`.

### 23.6 Type Theory Tests

Smoke tests for the type system itself.  Every known type theory
bug from the published literature becomes a permanent test.

```
test_theory reject_qtt_lam_linear
  expect_compile_error """
    fn higher_order(f: i64 -> i64) : i64 -> i64 =
      fn(x: i64) => f(f(x));
  """
  matches "linear value 'f' used multiple times";
end test_theory;

test_theory reject_secret_to_io
  expect_compile_error """
    fn leak(secret tok: Token) : unit with IO =
      log(f"token={tok.value}");
  """
  matches "classified value flows to unclassified output";
end test_theory;

test_theory accept_fractional_split
  expect_accepted """
    fn parallel_read(buf: buffer) : (i64, i64) =
      let (r1, r2) = split_ref(buf);
      (read(r1), read(r2));
  """;
end test_theory;
```

Property-based metatheory fuzzing:

```
test_metatheory preservation
  @[samples(100000)]
  @[max_depth(10)]
  forall e: well_typed_term, t: type.
    typing(empty_env, e, t) ==>
    forall e'. beta_step(e) == Some(e') ==>
    typing(empty_env, e', t);
end test_metatheory;
```

The fuzzer generates random well-typed terms via bidirectional
generation, checks preservation/progress on each, and shrinks
counterexamples.  A single corpus regression blocks all releases.

### 23.7 Doctests

Code examples inside `///` documentation comments are extracted,
compiled, and run as tests.  Matches Rust's `cargo test --doc`.
Fenced blocks marked ` ```fx ` become tests named `_doctest_<hash>`
and are invoked by `fxc test --doc`.

```
/// Parse a hex color string into a Color.
///
/// ```fx
/// let c = parse_color("#ff0000");
/// assert c == Color.RGB(r: 255, g: 0, b: 0);
///
/// let e = parse_color("not hex");
/// assert_err e is InvalidFormat;
/// ```
pub fn parse_color(s: string) : result(color, parse_error)
  with Tot = ... ;
```

**Fence modifiers:**

 * ` ```fx ` — compile and run as a test
 * ` ```fx,ignore ` — compile only, do not run (useful for
   examples requiring external state)
 * ` ```fx,should_fail ` — expect a compile error (for examples
   that demonstrate the type system rejecting a bug)
 * ` ``` ` (no language tag) — plain documentation, not extracted

**Hidden preamble.**  Lines prefixed with `// hidden: ` inside
a fence are included in the compiled test but not shown in
rendered documentation, letting examples start at the
interesting line:

```
/// ```fx
/// // hidden: let conn = Connection.connect("localhost", 443);
/// conn.set_timeout(5000);
/// ```
```

Doctests inherit the enclosing module's imports; they compile
under the same profile as the surrounding code.  Failing
doctests fail the release build, giving the same rot-resistance
guarantee as Rust's stdlib.

### 23.8 Running Tests

```bash
$ fxc test                   # all tests (unit, property, machine, etc.)
$ fxc test --doc             # only doctests (§23.7)
$ fxc test --unit            # only unit tests
$ fxc test --property        # only property tests
$ fxc test --machine         # only machine tests
$ fxc test --bench           # only benchmarks
$ fxc test --theory          # only type theory tests
$ fxc test sort_*            # by name pattern
$ fxc test --jobs 8          # parallel execution
$ fxc test --format json     # machine-readable output
```

Tests are stripped from release builds.


## 24. Compiler Agent Protocol

The FX compiler runs as a persistent HTTP daemon.  Agents interact
via structured REST calls — no text parsing, no cold startup per
invocation.

### 24.1 REST Daemon

```bash
$ fxc serve --port 9100
```

The daemon loads the project once, keeps elaborated state in memory,
watches files for changes, and serves queries with warm incremental
checking.  Cold startup: 2-5 seconds.  Warm recheck after a
one-line edit: 50-200ms.

The root endpoint self-describes all available operations:

```
GET /

{
  "fx": "1.0",
  "project": "acme/auth",
  "modules": 42,
  "endpoints": {
    "project":     "GET  /project",
    "modules":     "GET  /modules",
    "module":      "GET  /modules/{name}",
    "symbol":      "GET  /symbol/{qualified_name}",
    "type_at":     "GET  /type-at?file=&line=&col=",
    "search":      "GET  /search?name=&type=&goal=",
    "completions": "GET  /completions?file=&line=&col=",
    "check":       "POST /check",
    "errors":      "GET  /check/{id}/errors",
    "auto_fix":    "POST /check/{id}/auto-fix",
    "what_if":     "POST /what-if",
    "edit":        "POST /edit",
    "suggestions": "GET  /check/{id}/suggestions",
    "proof_state": "GET  /proof-state?file=&fn=&line=",
    "health":      "GET  /health",
    "impact":      "GET  /impact?symbol=",
    "rename":      "POST /rename",
    "extract_fn":  "POST /extract-fn",
    "dead_code":   "GET  /dead-code",
    "dep_graph":   "GET  /dependency-graph",
    "coverage":    "GET  /coverage?kind="
  }
}
```

### 24.2 Discovery

```
GET /symbol/Auth.login

{
  "name": "Auth.login",
  "kind": "fn",
  "location": { "file": "src/Auth.fx", "line": 15 },
  "signature": "(credentials: Credentials) : result(Token, AuthError) with IO, Async",
  "effects": ["IO", "Async"],
  "pre": ["valid_credentials(credentials)"],
  "post": ["Ok?(result) ==> valid_token(result.value)"],
  "trust": "Verified",
  "called_by": ["Api.Handler.login_handler"],
  "calls": ["Auth.Token.create", "Db.Users.find_by_username"]
}

GET /search?name=sort

[
  { "name": "Std.List.sort", "kind": "fn",
    "signature": "list(a) -> list(a) where Ord(a)" },
  { "name": "Std.Array.sort_by", "kind": "fn",
    "signature": "array(a, n) -> (a -> a -> Ordering) -> array(a, n)" }
]

GET /search?goal=is_sorted(append(_, _))

[
  { "name": "sorted_append", "kind": "lemma",
    "statement": "is_sorted(xs) -> is_sorted(ys) -> ... -> is_sorted(append(xs, ys))",
    "match": "exact" }
]
```

### 24.3 The Check/Fix Cycle

```
POST /check { "scope": "src/Auth.fx" }

{
  "id": "c_001",
  "status": "errors",
  "phases": {
    "parse": "ok", "names": "ok",
    "types": { "root": 2, "cascade": 3, "auto_fixable": 1 },
    "modes": "blocked", "effects": "blocked", "verify": "blocked"
  }
}
```

Errors are reported by phase.  Later phases are blocked until
earlier ones are clean.  The agent processes one phase at a time.

```
POST /check/c_001/auto-fix   // fix trivial issues (imports)

GET /check/c_002/errors?root=true
// returns root errors with concrete fix diffs

POST /what-if { "check": "c_002", "apply_fixes": ["fix_001"] }
// predicts whether the fix works without writing files

POST /edit { "apply_fixes": ["fix_001"], "recheck": true }
// applies fixes and returns new check result
```

Every error has a `fix` field with a stable ID and concrete edit
diffs the agent can apply via `/edit`.

### 24.4 Suggestions

Beyond errors, the daemon suggests improvements on compiling code:

```
GET /check/{id}/suggestions

[
  { "kind": "effect_narrowing",
    "message": "fn validate declares with IO but body is pure",
    "fix": { "id": "sug_001", "edits": [...] } },
  { "kind": "pipeline_sugar",
    "message": "fn(u) => u.active can be .active",
    "fix": { "id": "sug_002", "edits": [...] } },
  { "kind": "stronger_spec",
    "message": "implementation proves is_permutation but spec doesn't require it",
    "fix": { "id": "sug_003", "edits": [...] } },
  { "kind": "parallel_opportunity",
    "message": "transform is Tot — .par() would parallelize safely" }
]
```

Suggestion categories: ownership/mode, specification, sugar/style,
effects, types/contracts, performance, security.

Filter: `?kind=security`, `?severity=warn`, `?file=src/Auth.fx`.

### 24.5 Refactoring

```
POST /rename
{ "old": "Auth.login", "new": "Auth.authenticate" }
// returns: edits across all files, preview check, contract impact

POST /extract-fn
{ "file": "src/Auth.fx", "start_line": 20, "end_line": 28 }
// returns: extracted function with inferred spec, call site replacement

POST /inline
{ "symbol": "Auth.helper" }
// returns: inlined call sites, removed definition
```

All refactorings return preview edits.  The agent reviews and
applies with `POST /edit`.

### 24.6 Analysis

```
GET /health
{ "modules_ok": 38, "modules_errors": 3, "sorry_count": 4,
  "unstable_proofs": [{ "fn": "merge_perm", "time_ms": 4800, "timeout_ms": 5000 }] }

GET /impact?symbol=Auth.login
{ "direct_callers": 2, "transitive_callers": 12,
  "affected_tests": ["test_login"], "affected_contracts": ["AuthApi"] }

GET /dead-code
{ "unused_pub_fn": [...], "unused_imports": [...], "unreachable_branches": [...] }

GET /coverage?kind=spec
{ "total_pub_fn": 120, "with_post": 85, "no_spec": [...], "coverage_pct": 71 }
```

### 24.7 Proof Assistance

```
GET /proof-state?file=src/Sort.fx&fn=merge_sort&line=22

{
  "known": [
    "xs : list(a)", "length(xs) > 1",
    "is_sorted(merge_sort(left))", "is_sorted(merge_sort(right))"
  ],
  "goal": "is_sorted(merge_sort(xs))",
  "suggestion": "assert ... using merge_sorted_preserves_sort(...)"
}

POST /proof-plan
{ "file": "src/Sort.fx", "fn": "sort_correct" }
// returns: obligations, strategies, and a proof skeleton
```

### 24.8 Iterative Session Example

A fresh agent assigned to "add token refresh to acme/auth":

```
# 1. Orient
GET /                              # discover endpoints
GET /modules/Auth                  # understand module structure
GET /symbol/Auth.login             # read existing API

# 2. Write the new function (agent uses its file-edit tools)

# 3. Check
POST /check { "scope": "src/Auth.fx" }
# -> 3 errors (1 auto-fixable import, 2 type mismatches)

# 4. Auto-fix trivial issues
POST /check/c_001/auto-fix
# -> import added, 2 errors remain

# 5. Get errors with fix diffs
GET /check/c_002/errors?root=true
# -> e_T042: wrong return type (fix: wrap in Ok)
# -> e_R101: missing precondition (fix: add assert)

# 6. Preview
POST /what-if { "check": "c_002", "apply_fixes": ["fix_001", "fix_002"] }
# -> predicted: ok, 0 remaining

# 7. Apply and recheck
POST /edit { "apply_fixes": ["fix_001", "fix_002"], "recheck": true }
# -> all phases ok

# 8. Check for suggestions
GET /check/c_003/suggestions
# -> "fn refresh declares with IO but body is pure — remove"
# -> "missing post — implementation proves valid_token(result)"

# 9. Apply suggestions
POST /edit { "apply_fixes": ["sug_001", "sug_002"], "recheck": true }

# 10. Verify impact
GET /impact?symbol=Auth.refresh
# -> "new function — AuthAPI contract: MINOR version bump"

# 11. Check health
GET /health
# -> trust: Verified, 0 sorry, 0 errors
```

Twelve calls.  From "I know nothing" to "feature complete, verified,
contract-compatible."  Total compiler time: roughly 2 seconds.

### 24.9 CLI Fallback

For agents without HTTP:

```bash
$ fxc check --agent Auth.fx

PHASE parse OK
PHASE types ERRORS root=2 auto_fixable=1
ERROR T042 src/Auth.fx:15:10 root
  expected result(Token, AuthError), got Token
  FIX src/Auth.fx:28 "  token" -> "  Ok(token)"
SUGGEST src/Users.fx:22 sugar
  filter(fn(u) => u.active) -> filter(.active)
```

### 24.10 Daemon Lifecycle

The daemon watches files via OS notifications.  Changed files are
incrementally rechecked in background.  Read-only queries are served
concurrently.  Mutation queries are serialized per file.  Multiple
agents share the warm state.

Check IDs are snapshots.  File changes invalidate affected IDs.
Querying a stale ID returns `{ "status": "stale" }`.

`fxc serve` can expose both REST and LSP on different ports from
the same warm compiler state.


## 25. Distribution

FX programs ship in three deployment modes that share identical
kernel semantics (§30), identical type-system rules (§6), and
identical trust model (§10.6).  The modes differ only in the
infrastructure a project's dependencies pass through: a Solo
project uses none; a Workspace aggregates multiple packages under
one FX-native build driver; a Public-registry package crosses an
organization boundary with signed attestations and a transparency
log.  Every `.fx` file compiles identically under every mode —
there is no mode-specific dialect.  An agent emitting FX code
does not need to know which mode will receive it.

### 25.1 Deployment Modes

**Mode S — Solo.**  One project, one `package.fx.toml`, with
dependencies by filesystem path, git URL, or a chosen public
registry.  No signing required, no registry server required, no
network required after the first fetch populates the local
content-addressed cache.  The intended audience is a single
developer, a student, a small research project, or any scope
that does not justify workspace infrastructure.

**Mode W — Workspace.**  Multiple packages under one
`fx.workspace.toml` at a shared root.  The workspace has a shared
build driver (`fxc workspace`), a shared content-addressed cache,
a shared trust policy, and a shared signing configuration.  This
mode scales from a five-developer team to a ten-thousand-developer
monorepo with the same mechanism — the distinction is policy
tightness and the size of the directory tree, not the build
system.  The workspace is FX-native; it does not integrate with,
layer over, or depend on Bazel, Buck2, Pants, CMake, Make,
cargo, `go build`, Gradle, sbt, or any other build tool.

**Mode P — Public.**  The full publication pipeline: namespace
verification, transparency log, Ed25519 signatures, immutable
publication, Sigstore-style attestations.  Target audience:
open-source libraries, the standard library, and any package
crossing an organization boundary to consumers the author does
not personally know.

**Mode composition.**  A project uses multiple modes simultaneously
by category of dependency.  The common case: a Workspace consumes
its stdlib from Mode P, its internal libraries from Mode W (the
same workspace), and a colleague's helper from Mode S (a git URL
or local path).  The consumer's manifest states the mode per
dependency and the resolver applies each mode's rules
independently.

**Transitions.**  Solo graduates to Workspace by running
`fxc init --workspace` at the project root, which creates
`fx.workspace.toml`, initializes `.fx/trust/`, and migrates the
existing package into the workspace layout.  A workspace package
graduates to Public by running `fxc publish`, which checks the
stricter public-channel requirements (trust tier, attestations,
namespace verification, transparency-log inclusion) before
releasing.  There is no reverse migration pressure — a package
may remain at any mode indefinitely.

### 25.2 Mode S: Solo Projects

```
~/projects/myapp/
├── package.fx.toml
├── src/
│   └── main.fx
└── fx.lock
```

The manifest declares the package and its dependencies:

```toml
[package]
name      = "myapp"
namespace = "alice"                          # optional in Mode S
version   = "0.1.0"
fx        = ">= 1.0"

[dependencies]
"std/list"  = "2.1"                           # from public registry
"std/http"  = "1.4"
"helper"    = { path = "../helpers" }         # local sibling
"crypto"    = { git = "https://github.com/...",
                rev = "a3f2d9" }              # git dep pinned by rev
```

Path dependencies resolve by filesystem reference and pin by
content hash in `fx.lock`.  Git dependencies clone once into the
content-addressed cache at `~/.fx-cache/`, pin by the resolved
commit hash, and thereafter resolve offline.  Public-registry
dependencies follow the rules of §25.4.  The `namespace` field is
optional in Mode S because a Solo project does not publish
anywhere; including it does no harm and is encouraged for
projects planning to graduate to Workspace or Public.

`fxc archive` produces a reproducible tarball containing the
source, the lockfile, and the transitive closure of path/git
dependencies at their pinned commits.  A collaborator receiving
the tarball runs `fxc restore` and obtains a byte-identical
build tree.  No registry participation is required for
peer-to-peer sharing.

Trust model in Mode S is self-assessed.  `fxc build` reports the
aggregate trust level of the resulting binary — counting
transitive `sorry`, `axiom`, and `with Div` occurrences — but
does not gate on any particular level.  The binary's trust
metadata can be inspected after the fact via `fxc trust-report`.

### 25.3 Mode W: Workspaces

A workspace is a directory tree rooted at `fx.workspace.toml`,
containing multiple packages that share infrastructure.  It is
FX's answer to both the team-scale shared codebase and the
enterprise-scale monorepo — the same mechanism at different
scales of policy and directory tree.

```
acme/                              # workspace root
├── fx.workspace.toml              # workspace configuration
├── fx.lock                        # cross-workspace lockfile
├── third_party/                   # vendored external deps
│   └── std-1.8/                   # Mode P dep vendored into the tree
├── security/
│   ├── policy.fxpolicy            # per-directory policy (§25.9)
│   ├── OWNERS                     # signing authority
│   └── crypto/
│       ├── package.fx.toml        # package declares its module
│       └── src/
├── products/
│   ├── gmail-frontend/
│   │   ├── package.fx.toml
│   │   └── src/
│   └── experimental-ml/
│       ├── policy.fxpolicy        # relaxed policy for experimental code
│       ├── package.fx.toml
│       └── src/
└── .fx/
    ├── cache/                     # content-addressed build cache
    ├── trust/                     # signing keys, OIDC config
    │   ├── alice.pub
    │   └── policy.toml            # org-wide trust policy
    └── config.toml                # cache location, remote cache URL
```

**Module identity.**  Within a workspace a module is identified by
its directory path relative to the workspace root, preceded by
`//`.  The package at `acme/security/crypto/` is referenced as
`//security/crypto`.  Imports use this syntax:

```
open //security/crypto;
open //products/gmail-frontend;
```

Path-style references carry no version because the workspace is
the version source — the git or VCS commit is the version of
every package in the workspace simultaneously.  Cross-workspace
imports revert to the named-namespace form of Mode P
(`acme/auth`).

**Workspace manifest:**

```toml
[workspace]
root    = "."
members = ["security/**", "products/**", "third_party/*"]
exclude = ["products/experimental-ml/vendor/*"]

[workspace.cache]
local  = ".fx/cache"
remote = "https://cache.acme.internal/fx/"

[workspace.policy]
default_file = ".fx/policy.toml"
inherit      = true                 # subdirectory policies inherit

[workspace.signing]
pki      = "sigstore"               # or "pkcs11", "ssh", "custom"
oidc_url = "https://oidc.acme.internal"
```

**Build driver.**  `fxc workspace build //products/gmail-frontend/...`
compiles the selected subtree.  The driver walks the module
dependency graph, parallelizes across the configured job count,
and consults the content-addressed cache at each step.  Cache
hits return immediately; cache misses invoke the compiler and
populate the cache.  Artifacts land in a workspace-local
`.fx/out/` tree, never in the source tree.

**Hermetic build.**  Nothing outside the workspace root is read at
build time.  External FX dependencies are vendored into
`third_party/`.  External non-FX dependencies (C libraries,
hardware specification files, protobuf schemas) are declared as
`fx_external` entries in the manifest with a trust level and a
responsible-signer identity; the build treats them as opaque
inputs with their declared trust metadata.  A build that attempts
to fetch from the network fails unless the cache explicitly
permits network resolution for an identified dependency.

**Verification-aware incremental rebuild.**  §10.13 specifies that
each `;` is a verification checkpoint.  The workspace driver
exploits this at the function level: editing one function's body
re-verifies only that function's proof obligations plus the
obligations of direct callers when the callee's signature
changed.  Proofs whose dependencies are unchanged remain valid
without re-invoking the SMT oracle.  This is tighter than the
module-level incrementality of conventional build systems and is
unique to FX's graded kernel.

**Offline operation.**  `fxc workspace build --offline` succeeds
if every required artifact is present in the local cache; it
fails loudly if any artifact is missing, never silently fetching.
`fxc workspace prefetch` populates the cache from the remote cache
and external dependencies without invoking the compiler.  The pair
supports air-gapped deployment: prefetch on a connected machine,
transfer the cache over any medium (USB drive, write-once
optical media, one-way data diode), build offline in the isolated
environment.

### 25.4 Mode P: Public Registry

Mode P is the publication pipeline for packages crossing
organization boundaries to audiences the author does not know.
It subsumes the Mode W workspace model — a published package is
always extracted from some workspace — and adds namespace
verification, transparency log, author signatures, and third-party
audit signatures.

**Package identity.**  `namespace/name`.  Namespaces are verified
at registration through one of three mechanisms: a DNS TXT record
on a domain under the namespace owner's control; a verified
GitHub / GitLab / Forgejo organization; or an X.509 certificate
from an allowed certificate authority.  `std/` is reserved for
the standard library maintained by the FX project.

**Publication** consists of tagging a workspace package version,
generating the content-addressed archive, signing with the
author's Ed25519 key (or a Sigstore-issued short-lived
certificate), uploading to the registry, and appending an entry
to the public transparency log (Merkle tree, independently
witnessed, append-only).  Published packages are immutable.
Yanking marks a version as withdrawn while leaving it downloadable
by hash.  The version timeline is append-only, enabling third
parties to reproduce any historical build.

**Three security concerns kept separate:**

- **Discovery** — what packages exist.  Registry index, replicated
  to mirrors.
- **Storage** — where the source is.  Content-addressed by
  BLAKE3-256 (§25.10).  Any server returning content matching the
  hash is accepted.
- **Trust** — is this untampered.  Author signatures, a transparency
  log, and optional third-party audit signatures.

**Attestations.**  Each published version ships with zero or more
`.fxa` attestation files carrying signed claims about the code.
The package author signs one attestation automatically at publish
time; third-party auditors — security firms, academic reviewers,
downstream consumers who verified code they use — may add
attestations without the author's cooperation via the transparency
log.  Consumer policy (§25.9) determines which signatures are
required for a given trust tier.

### 25.5 Version Resolution and Lock Files

Resolution is deterministic across all three modes.  Given
identical manifests and identical lockfile state, two machines
produce identical resolved dependency trees.

**Minimal Version Selection.**  For each package, collect the
minimum version required by any constraint in the reachable
graph; select the maximum of those minimums.  The algorithm runs
in O(n) in the number of packages, requires no SAT solver, and
produces a single deterministic answer without backtracking.
Contract compatibility (§14.10) adds a refinement check: the
resolved version's contracts must refine what the consumer
expects; otherwise the resolution fails with a diagnostic naming
the incompatibility.

**Lock file** (`fx.lock`) records the resolved version of every
transitive dependency along with its content hash, declared
effect set, declared trust level, and the signer identity
attesting to that trust level.  The lockfile is committed to
source control.  Running `fxc build` with a committed lockfile
reproduces the same binary on any machine that can resolve the
artifacts (which requires either a populated cache or network
access to the registry).

```toml
# fx.lock excerpt
[[package]]
name       = "std/http"
version    = "2.3.1"
hash       = "blake3-256:a9f2c8..."
effects    = ["Tot", "IO", "Async", "Alloc", "Network"]
trust      = "Verified"
signed_by  = ["std-maintainers", "trail-of-bits-audit-2025-Q4"]
```

**Lock-file upgrades** are explicit: `fxc update` regenerates
`fx.lock` with the latest allowed versions per the manifest
constraints.  The command prints a diff and requires confirmation
before committing.  Continuous-integration configurations
typically forbid automated `fxc update` and accept lockfile
changes only via reviewed pull requests.

### 25.6 Automatic Version Computation

The compiler computes the semantic version of a new release from
the contract diff (§14.10) between its current source and its
previous published version.  The author reviews and confirms:

```bash
$ fxc publish

  Previous: 2.1.0
  Contract diff: fn refresh ADDED, field scope ADDED (optional)
  Computed: 2.2.0 (MINOR — backward compatible)
  Publish acme/auth 2.2.0? [y/N]
```

Overstating (forcing MAJOR when MINOR suffices) is allowed;
understating (forcing PATCH when MINOR or MAJOR is required by
the diff) is rejected by the registry at publish time.
Auto-generated changelog and migration guides accompany every
MAJOR bump.

### 25.7 Polyglot Interop via Artifacts

Organizations with existing C/C++/Rust/Go/Java/Python build
systems consume FX as they would any third-party prebuilt
library: via standard artifact formats and header files.  FX
never integrates with, ships plugins for, or layers on top of
Bazel, Buck2, Pants, CMake, Make, cargo, Gradle, sbt, or any
other external build system.  The interop boundary is at the
artifact, not at the build configuration.

**Emit formats** selected via `fxc build --emit=...`:

```
--emit=static_lib   → libfoo.a  + foo.h + foo.manifest.json
--emit=shared_lib   → libfoo.so / foo.dll / foo.dylib + header + manifest
--emit=object       → foo.o (raw object file, linker-ready)
--emit=wasm         → foo.wasm + foo.wit (WASM Component Model interface)
--emit=binary       → foo (standalone native executable)
```

The `@[abi(C)] pub fn` attribute (§19.10) marks a function for
inclusion in the exported ABI.  The generated header declares
C-level signatures; function names, argument and return types
are mangled per platform conventions unless `@[export("name")]`
overrides.

**The manifest** (`foo.manifest.json`) records the information
that would otherwise be lost crossing the artifact boundary —
the information a trust-aware consumer might act on, even if an
ABI-only consumer ignores it:

```json
{
  "fx_version": "1.0.3",
  "package":    "acme/crypto",
  "version":    "2.1.0",
  "emit":       "static_lib",
  "abi":        "c",
  "symbols": [
    { "name":          "aes_encrypt",
      "c_signature":   "void aes_encrypt(const uint8_t*, size_t, ...)",
      "fx_signature":  "fn aes_encrypt(ref k: aes_key, ...) : ... with CT",
      "trust":         "Verified",
      "effects":       ["CT", "Read"] }
  ],
  "trust_aggregate": {
    "level":       "Verified",
    "sorry_count": 0,
    "axiom_count": 1,
    "axioms": [
      { "name":        "acme/crypto.hw_rng_is_uniform",
        "signer":      "acme/security-review",
        "attestation": "nist-sp-800-90a" }
    ]
  },
  "build": {
    "hash":         "blake3-256:...",
    "timestamp":    "2026-04-15T14:03:00Z",
    "reproducible": true
  }
}
```

Security pipelines that consume SBOM formats (SPDX, CycloneDX)
read the FX manifest and surface trust-dimension information in
their dashboards.  ABI-only consumers treat the manifest as
optional metadata.  Either path is supported without FX-side
tooling.

**ABI versioning.**  The manifest's `abi` field tracks a stable
ABI version per FX compiler release.  Consumers built against
`abi: c` version 1 continue to link against FX libraries built
with compatible ABI versions without rebuilding.  Breaking ABI
changes advance the version and require consumer rebuilds; the
`fxc abi-compat` tool verifies a library's exported symbols match
a consumer's expectations before linking.

### 25.8 Staged Migration from Legacy

An organization adopting FX inside an existing codebase proceeds
through five stages, each a stable operating point with no
downstream pressure to advance.  The stages describe a typical
trajectory; an organization may halt at any stage indefinitely.

**Stage 1 — Island.**  A single FX module inside an existing
codebase.  The package lives under its own `package.fx.toml`
at an appropriate directory.  FX builds to a static library; the
host build system consumes it as it would any other third-party
`.a` file.  No workspace, no trust policy, no registry.  Typical
motivation: replacing one hot-path C module with FX for
constant-time correctness, or introducing a verified parser where
the existing one has had CVEs.  The Linux kernel's adoption of
Rust for individual drivers (Rust-for-Linux, 2022 onward) is the
canonical prior-art trajectory for this stage.

**Stage 2 — Archipelago.**  Several FX modules spread across the
codebase, unified under one `fx.workspace.toml` at the root of
the FX subset, sharing a cache, a trust policy, and a signing
configuration.  The host build system remains the top-level
orchestrator; each FX package exports its library artifact to the
host.  Typical scope: FX owns security-critical subsystems
(crypto, serialization, parsers), the host owns application
logic.

**Stage 3 — Symbiosis.**  Major subsystems are FX.  The FX
workspace is a peer to the legacy build, not a subordinate.
Trust policy tightens: the security team owns `//security/*`,
product teams own `//products/*`, experimental code lives at
`//experimental/*` under a relaxed policy file.  Engineers prefer
FX for new work because the cache and verification-aware
incrementality are faster than the legacy build — not because of
mandate.

**Stage 4 — Inversion.**  New services are FX-native.  Legacy
modules continue to compile via the legacy system but are
declared in the FX workspace as `fx_external` dependencies, so
`fxc workspace` orchestrates the end-to-end build.  CI runs
`fxc workspace build`, which subcontracts to legacy builders for
non-FX inputs.

**Stage 5 — Pure.**  No legacy build system remaining.  The FX
workspace is the monorepo.  Security audits run via
`fxc audit //...`.  The organization has fully internalized the
trust model.

Each stage permits the sketch/release partition of §22 to
coexist in the same tree: experimental code under a relaxed
policy file compiles in sketch mode while the rest of the
workspace requires release-mode verification.  Sketch and release
coexist at the directory level, not at the compiler-invocation
level.

### 25.9 Workspace Policy and Signing

A policy file (`policy.fxpolicy`) in any directory of a workspace
constrains what the code in that directory and its subtree may
do.  Policies inherit from parent to child: a subdirectory may
tighten its ancestor's constraints but cannot loosen them.  The
policy language reuses FX's expression grammar; there is no
separate DSL to learn.

```
policy {
  trust_floor       = Verified;
  allowed_effects   = [Tot, CT, Alloc(Stack), Read];
  forbidden_effects = [Network, FFI];
  max_sorry         = 0;
  max_axioms        = 3;
  required_signers  = [@security-team, @crypto-audit];
  consumable_from   = ["//products/*", "//security/*"];
};
```

**Three signer roles** carry distinct semantic weight:

- **Author.**  The individual developer who wrote the code.
  Signs their commit or their attestation.  Accountable for the
  code's correctness to the extent they can be.
- **Owner.**  The directory owner per the `OWNERS` file.  Signs
  on behalf of team accountability.  Typically a team key held
  in rotation, often implemented via a Sigstore group identity or
  an HSM-backed key shared among owners.
- **Auditor.**  A third-party reviewer — internal security team,
  external auditing firm, downstream consumer who independently
  verified the code.  Signs independently without the author's or
  owner's cooperation.

Consumer policy specifies which role combinations are required
at which trust tier.  A typical configuration for a
security-critical library:

```
required_signers_for = {
  trust_Verified = [author, owner, auditor];    # all three
  trust_Tested   = [author, owner];             # author + team
  trust_Sorry    = [author];                    # author only
};
```

**Corporate PKI integration.**  FX speaks standard signing
protocols; it does not invent key infrastructure:

- **Sigstore** (Fulcio, Rekor, Cosign) for OIDC-issued short-lived
  certificates from GitHub Actions, GitLab CI, Google Cloud, or a
  self-hosted OIDC provider.  This is the default and preferred
  path for most organizations.
- **PKCS#11** for hardware security modules — AWS CloudHSM, Azure
  Key Vault, Google Cloud HSM, YubiHSM, on-premises HSMs.
- **SSH signing keys** (`git config gpg.format ssh`) for individual
  developer signing from untrusted laptops.
- **WebAuthn / FIDO2** (YubiKey, Google Titan, Apple Touch ID)
  for interactive signing at release time.
- **PIV smart cards** (US Government HSPD-12, CAC for military,
  NATO equivalents) for defense and government deployments.

An organization's existing identity system is the signer identity.
Attestations are formatted per the in-toto ITE-4 specification
and logged in Sigstore Rekor or an internal transparency log.

**Policy is code.**  `policy.fxpolicy` files are parsed by `fxc`,
version-controlled alongside source, reviewed in pull requests,
and checked at every build.  Policy violations fail the build at
elaboration time with a diagnostic naming the specific constraint,
the offending declaration, and the directory whose policy forbids
it.

### 25.10 Reproducibility and Distributed Builds

Content-addressed artifacts and hermetic builds combine to make
reproducibility a theorem rather than an aspiration.  Given
identical source, compiler version, profile, and dependency
closure, FX produces byte-identical compilation artifacts on any
host supporting the target architecture.

**Hash scheme.**  BLAKE3-256 hashes every artifact: `.fxc`
(FXCore IR), `.fxl` (FXLow IR), `.fxa` (attestation), `.o` /
`.a` / `.so` / `.wasm`, and the final binary.  The cache key for
each artifact is
`BLAKE3(source bytes ∥ compiler version ∥ build profile ∥ dep closure hash)`.
BLAKE3 is chosen over SHA-256 for throughput — modern CPUs
process BLAKE3 at roughly 6 GB/s against SHA-256's 500 MB/s,
which matters at workspace scale.  SHA-256 remains available for
interop with transparency logs that have not migrated.

**Remote cache protocol.**  `fxc workspace --remote-cache=<url>`
consults an HTTP object store for cache entries.  The protocol is
minimal:

```
GET  /artifact/blake3-256:<hex>          → 200 + body, or 404
HEAD /artifact/blake3-256:<hex>          → 200 or 404
PUT  /artifact/blake3-256:<hex>          → 204 (auth per policy)
```

Any static file server, S3-compatible blob store, JFrog
Artifactory, Sonatype Nexus, Google Cloud Storage bucket,
Cloudflare R2, or plain nginx can serve this protocol.  No
dedicated cache server is required; no FX-specific API is imposed
on the server.

**Vendoring.**  `fxc workspace vendor --into=./third_party/`
flattens every remote dependency into the workspace tree,
switching resolution from network to filesystem.  Mandatory for
fully hermetic builds in Mode W; strongly recommended for
releases that must reproduce on air-gapped networks.  The vendor
layout preserves content-addressing: every vendored artifact
retains its hash in the lockfile.

**Offline build.**  `fxc workspace build --offline` consults only
the local cache and vendored tree; network access is rejected by
the build driver.  A build succeeds iff all required artifacts
are present in the cache or vendor tree.  `fxc workspace prefetch`
is the dual operation: populate the cache from remote sources
without invoking the compiler.  The typical air-gapped flow is
`prefetch` on a connected machine, physical transfer,
`build --offline` on the isolated machine.

**Determinism theorem.**  For a fixed FX compiler version and
target architecture, the function
`compile(source, profile, dep_closure) → artifact_bytes` is pure.
Timestamps are taken from `SOURCE_DATE_EPOCH` per the Reproducible
Builds convention.  Paths in debug information are relative to
the workspace root.  Randomness sources (for example,
symbol-mangling salts) are derived from the content hash rather
than from system entropy.  The Reproducible Builds project
maintains a test suite against which FX compliance regressions
can be detected.

**Cache entries carry trust.**  Each cache entry records the
trust tier and attestation signatures of the artifact.  A
consumer with a release-grade policy rejects cached artifacts
whose trust tier falls below its requirement, even on a cache
hit.  Cache-poisoning attacks must break both the content hash
(cryptographically hard) and the transparency log (independently
witnessed); the cache is not a trust anchor by itself.

### 25.11 Supply Chain Defenses

FX's distribution model structurally eliminates several classes
of supply-chain attack.  The defenses compose across all three
deployment modes.

**No build scripts.**  The attack vector that compromised xz-utils
in 2024 — a malicious `configure` script modifying the build —
does not exist.  Code generation uses `comptime` (§17.1) running
in a sandbox with no IO, no network, and no filesystem access.
A package cannot execute arbitrary code at install or build time.

**Effect transparency.**  A package that secretly adds `IO`,
`Network`, `Alloc`, or `FFI` effects changes its contract (§14);
the contract diff changes its semver; the semver change surfaces
in the consumer's lockfile update review.  An agent publishing a
package cannot hide new capabilities behind a patch bump.

**Classified-by-default.**  Exfiltrating environment variables,
credentials, or user data to a network endpoint requires a
`declassify` with a named policy (§12.4).  The declassification
is visible in the source, searchable across a codebase, and
auditable in the attestation.

**No raw pointer access.**  Patching function pointers at runtime
— the technique underlying many exploits of dynamic languages —
is not expressible in FX.  All pointer access passes through
`own` / `ref` / `ref mut` mode checks.

**Audit tooling:**

```bash
$ fxc diff-audit fx.lock.old fx.lock.new
  ADDED: sketchy/helper 0.1.0
    Effects:  Tot, IO, Network          warning: new network access
    Trust:    Tested (2 sorry)          warning: lowers project trust
    Signers:  @sketchy-org               unknown signer
    Axioms:   1 (rng_is_uniform)        unattested axiom
```

A release pipeline typically rejects `fxc diff-audit` outputs
containing new unattested effects, new sorry-tainted dependencies,
or new axioms without an auditor signature.

### 25.12 Project Profiles

A profile restricts FX for a project.  Profiles never extend the
language — they only reject constructs that would otherwise be
accepted.  Multiple profiles nest: a workspace-wide profile
applies to every package in the workspace; a package-level
profile tightens further; a policy file (§25.9) tightens at
directory granularity.

```toml
[profile]
name                   = "embedded_driver"
allowed_effects        = ["Tot", "IO", "MMIO", "DMA", "HardIRQ"]
alloc                  = "stack_and_region"
max_stack_per_function = 4096
overflow_default       = "trap"
sorry                  = "error"             # forbid sorry
ffi                    = "forbidden"          # no extern "C"
```

Module-level pragmas tighten (never loosen) the enclosing
profile:

```
module CriticalHandler
  pragma max_stack(2048);
  pragma effects(Tot, HardIRQ, MMIO);
```

Every `.fx` file parses identically regardless of profile (see
§25.13).  Profiles constrain what the elaborator accepts, never
what the parser accepts.

### 25.13 The No-Dialect Rule

FX has no syntax extensions, no custom operators, no custom
keywords, no `#lang` directives, no compiler plugins that change
parsing or type checking, no implicit conversions, and no template
metaprogramming.  Code generation uses `comptime` (§17.1) in a
sandbox with no IO.  Type-level abstraction uses type classes
(§16.4) and decorators (§17.3).  Domain-specific requirements are
served by contracts (§14), machines (§13), and the twenty-two-
dimension type system itself.

Every `.fx` file parses identically under every FX tool —
compiler, formatter, linter, language server — without knowledge
of the project's configuration, profile, or workspace.  There is
no dialect barrier between projects, teams, or organizations.  A
library written for an embedded profile parses the same as a
library written for a cloud service; only what the elaborator
accepts differs.  This is the property that makes a single
standard library possible across the domain archetypes of §29
(hardware, drivers, networking, database, image, tensor).


## 26. Standard Library

### 26.1 Why a Large Standard Library

The case against large standard libraries is real.  Python's urllib
was deprecated for urllib2 which was deprecated for urllib3 while
the third-party requests library became what everyone actually used.
Java's Date class was replaced by Calendar which was replaced by
java.time, and all three still exist.  In every mainstream language,
the stdlib accumulates mistakes it cannot clean up because removing
anything breaks existing code in ways nobody can predict.

The case for a large standard library is also real.  When every
project picks different libraries for HTTP, JSON, database access,
and date handling, the language fragments into dialects.  New users
spend their first week learning which libraries to trust.  Agents
must be trained on each one.  Code review requires documentation for
libraries nobody has seen before.

FX can ship a large stdlib where other languages cannot because of
three properties those languages lack.

**Contract-verified evolution.**  Every public API in stdlib is part
of a contract (§14).  Every change to a contract has a compiler-
computed minimum version bump (§14.10).  Evolving a stdlib module
has a defined cost that scales with the actual changes, not with
the size of the ecosystem.  Additive changes (new functions, new
optional fields) ship as minor bumps.  Breaking changes ship as
major bumps alongside the old version, with compiler-generated
migration guides.  This is not free, but it is possible — more than
most languages can claim.

**Effect-driven tree shaking.**  The compiler knows which effects
each stdlib module requires.  `std/http` uses `Network` and `Alloc`.
`std/json` uses only `Alloc`.  `std/list` is pure.  A program that
does not declare `Network` cannot import `std/http`, and nothing
from it appears in the binary.  The size of the binary is bounded
by the modules actually reachable given the program's effects.  A
50-module stdlib has zero cost for a program that uses 5 of them.

**Profile-based restriction replaces no_std.**  An embedded profile
that restricts allocation to stack transitively excludes any stdlib
module that requires heap.  The distinction is continuous, not
binary: which modules are accessible depends on which effects the
profile allows.  A Cortex-M profile gets `std/list`, `std/option`,
`std/bits`, and anything pure.  It does not get `std/http` or
`std/postgres`.  No separate embedded ecosystem needed.

### 26.2 Module Catalog

Data formats: JSON, YAML, TOML, CSV, XML, MessagePack, Protocol
Buffers, CBOR.  All share the contract-based API — switching from
JSON to MessagePack is a one-line change.

Text: regex (with verified bounds on matching time), Unicode
primitives, Markdown, templating, diff/patch.

Time: dates, durations, timezones (full IANA database), formatting,
calendar arithmetic.

Cryptography: SHA-2, SHA-3, BLAKE3, ChaCha20-Poly1305, AES-GCM,
Ed25519, X25519, RSA, TLS 1.3, X.509 parsing.  All verified,
all constant-time.

Networking: HTTP/1.1 and HTTP/2, WebSocket, gRPC, DNS, QUIC, raw
sockets.

Database clients: PostgreSQL, SQLite, Redis.  Contract-based
drivers with compile-time schema checking.

Storage/compression: tar, zip, gzip, zstd, lz4, brotli.

Image codecs: PNG, JPEG, WebP, AVIF.  Verified decoders where
buffer overflows are structurally impossible.

Numerics: shape-typed tensors, BLAS bindings, FFT, statistics,
random number generators.

Parsing: the verified parser combinator framework.

System: filesystem, process spawning, threads, environment, CLI
argument parsing, signal handling.

Observability: structured logging, distributed tracing, metrics.

Mathematics: formalized algebra, analysis, number theory, topology
(ported from Lean 4's Mathlib).

**Type-theoretic infrastructure modules.**  These ship with the
stdlib because they are referenced from kernel-level constructs
across the spec; downstream packages compose against them
without reinventing the algebra.

```
Std.Algebra
  // class names; full kind-annotated signatures in §16.6
  Semigroup, Monoid, CommMonoid, Group, AbelianGroup
  Semiring, Ring, CommRing, Field
  Lattice, BoundedLattice, DistributiveLattice, BooleanAlgebra
  PartialOrder, TotalOrder
  ReversibleCommMonoid, OrthogonalDelta
  // each class carries @[structure] laws checked by SMT

Std.Optics
  // §16.12 — profunctor-encoded modular data accessors
  Profunctor, Strong, Choice, Wander
  Optic, Lens, Prism, AffineTraversal, Iso, Traversal, Fold, Setter

Std.IxMonad
  // §30.10 — single class IxMonad<f: (idx, idx, type) -> type>
  IxMonad
  // instances: channel, machine, tx, mutex, stm,
  //            reader, writer, state — sessions, machines,
  //            transactions, locks are all instances

Std.Logic
  // §10.7 decide framework + §16.10 derivable traits
  Decidable
  Eq, Ord, Hash, Show, Default
  decide, native_decide, by_contradiction, by_cases

Std.Concurrent.Reagent
  // §11.30 lock-free composition
  reagent                                       // type constructor
  pure, upd, cas, swap, seq, choice, pair       // combinators
  // verified instances: Treiber stack, Michael-Scott queue,
  //                     hazard-pointer publish, RCU read-side

Std.Time.Causal
  // §11.31 causal ordering
  vector_clock, hybrid_logical_clock            // type constructors
  happens_before, concurrent, merge, tick       // operations

Std.Distributed.CRDT
  // §16.6.1 CRDT class hierarchy
  CvRDT, MonotonicCounter                       // classes
  lww_register, or_set, pn_counter, g_counter   // type constructors
  // BloomL prefix lattice + CRDT product/map composition

Std.Compute.Replay
  // §11.3.1 async replay
  replay_log, ordering_event                    // type constructors
  // content-addressed event log with vector_clock payloads

Std.Budget
  // §6.6 user-defined Tier-S dimensions; annotation-only,
  // not kernel-enforced
  Energy, Latency, Power, WallClock, BitsTransferred

Std.Net.Wit
  // §14.4.1 WIT lowering for WebAssembly Component Model
  decode_component, encode_component
  // interop with Rust / Go / JS / Python

Std.Sync
  // standard concurrency primitives layered over §11.10 atomics
  mutex, rw_lock, semaphore, barrier, once_lock, exclusive_access
```

(Kernel modalities — `later`, `bridge`, `cap`, `fix`, `next`,
`transport` — are surface names exposed by the kernel itself,
not stdlib modules; see §6.10 for the full list and Appendix H
for the corresponding axioms.  The `ghost` keyword is also a
kernel-exposed binding mode, not a stdlib type.)

The reason this infrastructure ships in stdlib rather than
ecosystem packages: the type-class abstractions (IxMonad, optics,
Decidable, CRDT, reagents) are referenced from typing rules and
spec sections.  Putting them in a third-party package would
create a circular dependency between language semantics and an
external version-managed artifact.  Stdlib `Std.*` modules ship
at the same version as the compiler.

### 26.3 Behavior, Not Implementation

This is the single most important rule for a stdlib that people use
rather than replace.

C++ got this wrong with `std::unordered_map`.  The standard specifies
that iterators remain valid after insertion, which forces node-based
storage, which forces pointer chaining, which forces every lookup to
chase pointers through the heap.  Google's `absl::flat_hash_map` is
2-5x faster because it uses open addressing with SIMD probing, but
it cannot be `std::unordered_map` because it invalidates iterators
on insert.  The standard locked the interface to a specific
implementation strategy and cannot change it.  Every major company
ships its own hash map because the standard one is slow and
unfixable.

The same pattern repeats: `std::list` is always heap-allocated nodes
because the interface guarantees O(1) splice.  The allocator is a
template parameter that infects the type — `vector(int, A)` and
`vector(int, B)` are different types, so every function becomes a
template, compile times explode, and error messages become
unreadable.

FX avoids this.  `map(K, V)` promises insert, lookup, delete,
iterate.  It does not promise iterator stability, node-based
storage, or specific layout.  The compiler picks the implementation:

```
map(nat { x < 256 }, Config)          direct array (O(1) lookup)
map(string, Record) with 12 entries   flat sorted array
map(string, Record) with 1M entries   Swiss Table
```

The user writes `map` in all three cases.  If the user later widens
the key refinement, the compiler switches implementations
automatically.

The allocator is not in the type.  `list(int)` is `list(int)`
regardless of whether memory comes from a slab, a region, or the
stack.  The allocator is an effect (`with Alloc(strategy)`) and a
profile setting.  Two functions that take `list(int)` interoperate
without template parameterization.

Evolution is mechanical: contracts (§14) track behavior, not
implementation.  The stdlib can swap hash map implementations across
compiler releases without breaking any consumer, because the
contract says "insert, lookup, delete" and the implementation is
the compiler's business.

If a user genuinely needs iterator stability (rare — it comes from
a C++ era of manual iterator management), they use
`stable_map(K, V)` which makes the tradeoff explicit.  The default
`map` makes no such promise and is fast.


## 27. Reference Implementations

Six reference implementations ship alongside the compiler, each
targeting a domain where the language's properties provide concrete
advantages over existing tools.

### 27.1 fx-chip

A verified RISC-V core (RV64GC).  The ISA is a total function over
architectural state.  A five-stage pipeline implements it.  A
refinement proof (§18.12) connects the two.  Target: boot Linux on
an FPGA with every instruction commit formally proven to match the
specification.

### 27.2 fx-driver

Linux kernel drivers in FX.  The execution context effect hierarchy
(§19.1) prevents sleeping-in-interrupt bugs.  Linear DMA tracking
(§19.2) prevents use-while-device-owns-buffer bugs.  Machine-based
driver lifecycles (§19.3) generate cleanup chains automatically.
Initial targets: e1000 NIC, NVMe block driver, XHCI USB host.

### 27.3 fx-net

A verified TCP/IP stack with formal compliance to RFC 793/9293.
Session types for protocol states.  Linear packet buffers for
zero-copy.  Contracts for wire formats.  Targets: UDP, TCP without
congestion control, then Cubic, TLS 1.3, HTTP.

### 27.4 fx-db

A SQL database, starting at SQLite scale and growing to PostgreSQL
scale.  Machines for transaction state with inverse chains for
abort.  Write-ahead log as a linear monotonic structure.  Query plan
correctness as a refinement proof.

The type system enables intra-query parallelism that the originals
lack: stages of a query plan that access disjoint pages run
concurrently with the compiler proving they do not conflict.

### 27.5 fx-image

Image loading, saving, and filtering.  Format declarations (§18.1)
for codec parsing — length fields carry refinements that bound every
buffer access.  Buffer overflows, integer overflow in size
calculations, and use-after-free in codec parsers are structurally
impossible.  Targets: PNG, JPEG, WebP, AVIF.

### 27.6 fx-numeric

Shape-typed tensors, BLAS bindings, autodiff via staged programming
(§17.2), GPU dispatch via `.gpu()` source type.  Shape mismatches
caught at compile time.  Target: inference for small language models
(Llama 7B) with compile-time shape checking throughout.


## 28. Scaling Properties

### 28.1 Bounded Blast Radius

A well-typed edit that compiles cannot silently break anything
outside its public surface.  Specifically:

A module `M` has the same type errors after an edit to upstream
module `U` unless `U` changed its public declarations.  Private
changes upstream do not affect `M`.

A function `f` has the same proof obligations after an edit unless
`f`'s signature or the signatures of the functions it calls changed.

Previously proved properties stay proved.  The type checker does not
lose facts when code is added.

The trust level of a module does not decrease unless a `sorry`,
`axiom`, or weaker effect was introduced inside that module or its
public dependencies.

### 28.2 Why This Holds

Modular checking.  Each module is type-checked against its own
source and the public declarations of its imports.  No global
inference pass.  No downstream re-checking when upstream internals
change.

Explicit API stability.  Every `pub` declaration is part of a
contract.  Changes to public signatures are visible as contract
diffs (§14.10) and the compiler computes the required version bump.

Complete compiler feedback.  When something does not compile, the
error comes with location, context, and suggested fix as a diff.

Proof composition.  If A calls B and B has a verified postcondition,
A uses that postcondition without re-proving B's internals.

No silent state.  Every effect is declared.  Every allocation is
tracked.  Every mutation is visible in the type.  No global mutable
state for two modules to accidentally share.

### 28.3 Where This Breaks Down

Specification gaps.  If the `post` clause is wrong, FX proves
the wrong thing.  The compiler cannot tell the specification is
wrong, only that the implementation matches it.

Proofs that need insight.  Some properties require a clever lemma
that neither Z3 nor an agent will find on its own.

Performance.  The type system catches correctness bugs.  It does
not catch "this loop is accidentally quadratic" unless complexity
bounds are declared.

Changing requirements.  When the user wants something different,
the specification changes, and that is a real cost no type system
reduces.

### 28.4 Measuring It

Tokens spent per verified function.  Count the tokens an agent used
in a session, count the `pub fn` declarations it produced with
trust `Verified`, take the ratio.  Over time the ratio should
decrease as the agent learns the codebase's conventions.

Regression rate: how many times does an edit cause a previously
verified function to need re-verification.  For private changes
this should be near zero.  For public changes it should be limited
to direct downstream consumers.


## 29. Domain Archetypes

Each reference implementation (§27) has a characteristic layout.
The archetypes below show the starting structure for each domain.

### 29.1 Hardware

Three modules: ISA specification (pure function), RTL (hardware
modules), refinement proof (connects them).

```
module MyCpu.Isa

type arch_state = {
  x   : array(bits(64), 32);
  pc  : bits(64);
  mem : bits(64) -> bits(8);
};

invariant arch_state.x[0] == 0;

layout R : bits(32) = {
  funct7: 7; rs2: 5; rs1: 5; funct3: 3; rd: 5; opcode: 7;
};

fn step(s: arch_state) : arch_state
= let insn = fetch(s.mem, s.pc);
  execute(s, decode(insn));
```

```
module MyCpu.Rtl

pipeline core with Sync(clk, reset)
  stage fetch
    let insn = imem.read(pc);
    emit insn, pc;
  end stage;
  stage decode
    let d = decode(insn);
    stall when prev.is_load and prev.rd in [d.rs1, d.rs2];
    emit d, rf.read(d.rs1), rf.read(d.rs2);
  end stage;
  stage execute
    let result = alu(a, b, d.alu_op);
    flush fetch, decode when eval_branch(d, result).taken;
    emit result, d;
  end stage;
  stage writeback
    rf.write(d.rd, result, en: d.writes_rd and d.rd != 0);
  end stage;
end pipeline;
```

```
refinement core_refines_isa
  spec = MyCpu.Isa.step;
  impl = MyCpu.Rtl.core;
  via fn(p) => arch_state {
    x: p.rf.regs, pc: committed_pc(p), mem: p.dmem,
  };
  property correspondence :
    forall(p: pipeline_state),
      commits(tick(p)) ==>
        abstract(tick(p)) == step(abstract(last_commit(p)));
end refinement;
```

### 29.2 Kernel Driver

Four files: register file, lifecycle machine, interrupt handler,
kernel entry points.

```
module MyDev.Regs

register_file MyDev at bar0
  reg ctrl : bits(32) at 0x00
    field enable : bit(0) RW;
    field mode : bits(2:1) RW where mode != 0b00;
    field reset : bit(3) W1S;
  end reg;
  reg irq_status : bits(32) at 0x0C
    field rx_done : bit(0) W1C;
    field tx_done : bit(1) W1C;
  end reg;
end register_file;
```

```
module MyDev.Lifecycle

machine Driver
  state Probed of { pci: pci_device };
  state Mapped of { pci: pci_device; regs: MyDev };
  state Started of { pci: pci_device; regs: MyDev; rings: ring_buffers };
  state Removed;

  transition map : Probed -> Mapped with Passive, MMIO
    inverse unmap;
  transition start : Mapped -> Started with Passive, DMA
    inverse stop;
  transition remove : * -> Removed with Passive, MMIO;

  initial Probed;
  terminal Removed;
  always (state is Removed) ==> pci_released and dma_freed;
end machine;
```

```
module MyDev.Irq

fn handle(ref mut regs: MyDev) : irq_return with HardIRQ, MMIO
begin fn
  let s = regs.irq_status.read();
  regs.irq_status.set(s);
  if s.rx_done; wake_rx_thread() end if;
  if s.tx_done; wake_tx_thread() end if;
  IRQ_HANDLED
end fn;
```

```
module MyDev.Module

@[abi(C, linux_kernel)]
@[link_section(".init.text")]
pub fn init_module() : i32 with Passive, IO
= let r = pci_register_driver(ref my_driver_ops);
  if r < 0; r else 0 end if;
```

### 29.3 Network Protocol

Wire format, state machine, session types, optional RFC refinement.

```
module MyNet.Tcp.Wire

layout TcpHeader : bits(160) repr(C, packed, big_endian) = {
  src_port: 16; dst_port: 16; seq: 32; ack: 32;
  data_off: 4; reserved: 3; flags: 9; window: 16;
  checksum: 16; urg_ptr: 16;
  virtual syn : bit = flags[1];
  virtual ack_flag : bit = flags[4];
  virtual fin : bit = flags[0];
};
```

```
module MyNet.Tcp.State

machine Connection
  state Closed;
  state SynSent of { iss: u32 };
  state Established of {
    snd_una: u32; snd_nxt: u32; snd_wnd: u16;
    rcv_nxt: u32; rcv_wnd: u16;
  };

  transition active_open : Closed -> SynSent with IO;
  transition recv_syn_ack : SynSent -> Established with IO
    requires segment.syn and segment.ack_flag;

  initial Closed;
  invariant snd_una <= snd_nxt;
end machine;
```

```
session TcpClient<r: region>
  connect(host: ref(r) string, port: u16);
  branch
    connected => loop
      send(data: ref bytes);
      receive(data: bytes);
    end loop;
    refused => receive(reason: string); end;
  end branch;
end session;
```

### 29.4 Database

Storage layer (pages, WAL), transaction machine, query layer,
wire protocol session.

```
module MyDb.Schema

type UserRecord = {
  id: nat { x > 0 };
  name: string { length(x) > 0 and length(x) <= 255 };
  email: string { valid_email(x) };
};

contract UserTable for UserRecord
  access id : write_once auto_increment;
  access email : unique;
  format sql {
    table "users";
    id : integer primary_key;
    name : varchar(255) not_null;
    email : varchar(255) not_null unique;
  };
end contract;
```

```
module MyDb.Txn

machine Transaction
  state Active of { reads: set(page_id); writes: map(page_id, bytes) };
  state Committed;
  state Aborted;

  transition commit : Active -> Committed with IO
    atomic;
  transition abort : Active -> Aborted with IO;

  initial Active;
  terminal (Committed | Aborted);
  always (state is Committed) ==> all_writes_durable;
  always (state is Aborted) ==> no_writes_visible;
end machine;
```

### 29.5 Image Processing

Image type with compile-time dimensions, codec as format parser,
filters as tensor operations.

```
module MyImage.Core

type pixel_format
  RGB;
  RGBA;
  Grayscale;
end type;

comptime fn bytes_per_pixel(f: pixel_format) : nat = match f;
  RGB => 3; RGBA => 4; Grayscale => 1;
end match;

type image<f: pixel_format, w: nat, h: nat> = {
  pixels: array(u8, w * h * bytes_per_pixel(f));
  stride: nat { x >= w * bytes_per_pixel(f) };
};
```

```
module MyImage.Png

layout PngChunk = {
  length : 32;
  type   : 32;
  data   : length * 8;
  crc    : 32;
};

fn decode<r: region>(ref data: bytes) : result(image(RGBA, _, _), PngError)
  with Alloc(Region(r))
begin fn
  let ihdr = parse_ihdr(data);
  // ihdr.width and ihdr.height are refined nat values
  // allocations bounded by refinements — no overflow possible
  let decoded = decode_idat_chunks(data, ihdr);
  Ok(image { pixels: decoded, w: ihdr.width, h: ihdr.height,
             stride: ihdr.width * 4 })
end fn;
```

### 29.6 Tensor Computation

Shape-typed tensors, neural network layers, autodiff via staging.

```
module MyMl.Tensor

fn matmul<a: nat, b: nat, c: nat>(
  x: tensor(f32, [a, b]),
  y: tensor(f32, [b, c]),
) : tensor(f32, [a, c])
  with Alloc;

fn broadcast_add<s1: shape, s2: shape>(
  x: tensor(f32, s1),
  y: tensor(f32, s2),
) : tensor(f32, broadcast(s1, s2))
  where broadcast(s1, s2) != None;
  with Alloc;
```

```
module MyMl.Nn

type Linear<in_f: nat, out_f: nat> = {
  weight: tensor(f32, [out_f, in_f]);
  bias: tensor(f32, [out_f]);
};

impl Linear<in_f: nat, out_f: nat>
  fn forward<batch: nat>(ref self, x: tensor(f32, [batch, in_f]))
    : tensor(f32, [batch, out_f])
    with Alloc
  = matmul(x, transpose(self.weight)) + broadcast_add(self.bias);
end impl;
```

```
module MyMl.Autodiff

comptime fn grad<a: shape, b: shape>(
  f: code(tensor(f32, a) -> tensor(f32, b)),
) : code(tensor(f32, a) -> tensor(f32, a))
= differentiate_source(f);
```

GPU execution via source type:

```
fn inference(ref model: Llama, tokens: tensor(i32, [seq_len]))
  : tensor(f32, [seq_len, vocab_size])
  with Alloc(Gpu)
= tokens.gpu()
  |> model.embed()
  |> model.layers.fold(fn(h, layer) => layer.forward(h))
  |> model.lm_head();
```


## 30. The Kernel Calculus and Metatheory

FX commits to a **finite axiomatic kernel** in the Metamath tradition.
Every surface feature in §3-§26 reduces mechanically to a small set
of kernel terms; every kernel term is checked against a finite list
of axioms (Appendix H).  The kernel is implemented in Lean 4 as the
reference stage-0 bootstrap host.  The trusted base is enumerable
per-definition via `fxc --show-axioms`.

This chapter specifies the kernel and the derivation discipline.  It
is not the user-facing language — users write surface FX.  It is the
mathematical substrate the surface language stands on.

### 30.1 The Kernel Discipline

Metamath's achievement (`set.mm`, Norman Megill) is the explicit,
enumerable trusted base: ~40 axiom schemas from which all of ZFC
set theory and most mathematics is derived, checkable by a 300-line
verifier.  FX adopts the discipline without the specific encoding:

 1. **Finite axiom list.** ~32 axioms, stated in Lean 4, listed in
    Appendix H.  Every soundness argument reduces to "the 32 axioms
    are consistent."
 2. **Derivation-only extensions.** Every §3-§26 feature has a
    "Kernel Translation" subsection showing exactly how the surface
    syntax reduces to kernel terms.  New language features are
    definitional extensions, not new axioms.
 3. **Audit trail per definition.** `fxc --show-axioms symbol`
    prints the set of kernel axioms a symbol transitively depends
    on, plus any `sorry` or user-declared `axiom` invocations, plus
    any SMT-oracle discharges with their UNSAT cores.
 4. **Lean 4 as host.** The kernel is implemented as Lean 4
    definitions.  The FX stage-1 compiler is a Lean 4 program; the
    stage-2 compiler is FX compiled through stage 1; stage 3 is
    self-compiled as fixpoint check (§30.9).

Effect: FX can stand up and say "these 32 axioms are what we
assume; everything else is derived; here's the Lean 4 mechanization
of the soundness proof."  C++, Rust, Swift, and Go cannot make this
claim.  Lean 4, Coq, F*, Agda, and Idris can — FX joins that
family.

### 30.2 Kernel Terms

The kernel syntax has ten forms.  No records, ADTs, `match`,
control flow, machines, contracts, sessions, or effects — all
derived.

```
e ::= x                           -- variable
    | e₁ e₂                        -- application
    | λ (x :_g T) => e            -- lambda (graded)
    | Π (x :_g T) → T'            -- dependent function type
    | Σ (x :_g T) × T'            -- dependent pair type
    | Type<u>                      -- universe (u a level expression)
    | Ind { ... }                  -- inductive family
    | Coind { ... }                -- coinductive family (sized)
    | Id T e₁ e₂                  -- identity / equality type
    | Quot T R                    -- quotient type
```

`g` is a grade vector — twenty components per §6.3.  Every lambda
binder, Pi binder, and Sigma binder carries a grade.  The grade is
0 for erased (ghost), 1 for linear, w for unrestricted, and
richer values per dimension.

### 30.3 Kernel Judgments

The kernel states five judgment forms:

```
Γ ⊢ T wf                   T is a well-formed type
Γ ⊢ e : T                  e has type T
Γ |-^p e : T              e has type T with grade vector p
Γ ⊢ e ≡ e'                 e and e' are definitionally equal
Γ ⊢ T <: T'               T is a subtype of T'
```

The typechecker is the Lean 4 procedure deciding these judgments.
It invokes the axioms of Appendix H and the SMT oracle.  The SMT
oracle is the one non-kernel trust component; its queries are
cached in `audit.smtq` files and auditable.

### 30.4 Universe Levels

FX has a predicative cumulative universe hierarchy.  Levels are
expressions in a decidable theory:

```
u ::= level.zero
    | level.succ(u)
    | level.max(u, u)
    | k                       -- level variable, bound by <k: level>
```

The kernel axioms U-wf, U-hier, U-cumul, U-level, and U-poly
(Appendix H) state:

 * `Type<u>` is well-formed when `u : level`.
 * `Type<u> : Type<level.succ(u)>`.
 * `Type<u> <: Type<v>` when `u ≤ v` in the level preorder.
 * `level.zero`, `level.succ`, `level.max` exist with the usual
   ordering axioms.
 * `Π (k : level). T(k)` is well-formed when `T(k)` is well-formed
   for all `k` (universe polymorphism).

**Surface syntax.**  Bare `type` in §3 is sugar for `type<0>`.  A
level variable is declared with `<k: level>` at the function or
type signature; used as `<a: type<k>>`.  Cumulative coercion is
silent: a `type<0>` value passes where `type<1>` is expected.

**Example.**

```
fn identity<a: type>(x: a) : a = x;
// Kernel: λ (a :_erased Type<0>). λ (x :_1 a). x

fn compose<k: level, a: type<k>, b: type<k>, c: type<k>>(
  f: b -> c, g: a -> b,
) : a -> c
= fn(x: a) => f(g(x));
// Kernel: λ (k :_erased level).
//         λ (a b c :_erased Type<k>).
//         λ (f :_1 (b → c)). λ (g :_1 (a → b)).
//         λ (x :_1 a). f (g x)
```

**No impredicative Prop.**  FX has one hierarchy; proof erasure is
handled by the existing Ghost grade (usage = 0, dim 3).  Mathlib-
class propositional development can be revisited as a v2
extension; it is not load-bearing for v1 systems programming.

### 30.5 Grade Algebra

§6 states the graded type system as FX surface theory.  §30.5
states the same as kernel axioms.  The grade algebra is:

 * For each of the twenty-two dimensions, a tier classification
   (S, L, T, F, V) and a per-tier structure:
   * Tier S: commutative semiring `(R, +, *, 0, 1, ≤)`
   * Tier L: lattice with validity predicate `(R, ∨, ∧, valid)`
   * Tier T: typestate transition relation
   * Tier F: foundational discharge (types, refinements)
   * Tier V: lattice of version labels with adapter edges
     (consistency check at each site, no seq — see §15)
 * The product grade vector composes via the App/Let/If/Lam rules
   of §6.2 with context division per Wood-Atkey 2022.

Kernel axioms Grade-semiring-laws, Grade-subsumption, Grade-
division, Grade-zero, and Grade-lattice (Appendix H) state the
algebraic laws.  Each surface dimension (Usage, Effect, Security,
Lifetime, Provenance, Trust, Representation, Observability, Clock,
Complexity, Precision, Space, Overflow, FP-order, Mutation,
Reentrancy, Size, Version) is a specific instantiation — not a new
axiom.

### 30.6 The Axiom List

The full kernel axiom list is Appendix H.  Summary count by
category:

```
Category              Count   Notes
──────────────────   ─────   ──────────────────────────────────────
Universes              3     U-form, U-cumul, U-poly
                              (level arithmetic absorbed into U-form)
Pi (dependent fn)      3     Pi-form, Pi-intro (Wood-Atkey corrected),
                              Pi-elim
Sigma (dep. pair)      2     Sigma-form, Sigma-intro
                              (elim folded as projection)
Inductive              2     Ind-form (with strict-positivity check),
                              Ind-elim (intro / iota folded into spec)
Coinductive            2     Coind-form (with Later-guarded productivity),
                              Coind-elim
Identity               2     Id-form, Id-J (refl folded as Id-J base)
HIT                    1     general HIT primitive subsumes Quot
                              (saves 3 Quot axioms; quotient types
                              instantiate as HIT)
Modal univalence       1     Wire-mode equivalence transport
                              (contract migration as transport)
Bridge / Later         2     B-form (parametricity), Later-form
                              (guarded recursion; replaces syntactic
                              guardedness in Coind)
Grade algebra          2     Grade-laws (per-tier semiring/lattice/
                              typestate/versioned), Grade-subsumption
                              (Grade-zero replaced by 2LTT separation)
Subsumption/convert    2     T-conv (β/ι/ν/η reduction equality),
                              T-sub (universe cumulativity + grade
                              subsumption + effect-row inclusion)
Emit-table             1     U-emit relating atomic source operations
                              to ISA-level instruction sequences
                              (§20.5)
──────────────────   ─────
Total                 23
```

Twenty-three axioms.  Publishable on a single page.  The
reduction from earlier ad-hoc kernels (Coq's ~70, Lean 4's ~30,
F*'s ~30) tracks the systematic absorption of derivable
constructs into the modality framework: the bridge modality
(§6.9 derived; B-form axiom) replaces user-defined
parametricity instances; HITs replace per-quotient axioms;
2LTT mode separation replaces the per-binding ghost grade.

### 30.7 The Kernel Translation Pattern

Every surface feature in §3-§26 has a **Kernel Translation**
subsection showing the exact kernel term it elaborates to, the
axioms invoked, and any composition proof obligations.  This is
the discipline that keeps the axiom list at 32.

Three illustrative translations:

**§3.3 Algebraic data type.**

```
// Surface:
type option<a: type>
  None;
  Some(a);
end type;

// Kernel:
Ind {
  name        = "option"
  params      = [(a :_erased Type<0>)]
  constructors = [
    { name = "None"; args = [];                 returns = option(a) }
    { name = "Some"; args = [(x :_1 a)];        returns = option(a) }
  ]
  eliminator  = option_rec
}

// Axioms invoked: U-wf, Pi-form, Ind-form, Ind-intro (×2),
// Ind-elim.
```

**§7 Linear consumption.**

```
// Surface:
fn close(file: file_handle) : unit with IO
= close_fd(file);

// Kernel:
λ (file :_{usage=1, effect={IO}} file_handle).
  close_fd file
  : Π (file :_{usage=1, effect={IO}} file_handle) → unit at {IO}

// Using `file` twice in the body would require grade `1+1=ω`,
// but `file` is bound at grade `1`.  Grade-subsumption fails;
// the kernel rejects.  Compile error M001 is the user-facing
// name for this specific axiom failure at this program point.

// Axioms invoked: Pi-intro, Pi-elim, Grade-semiring-laws,
// Grade-subsumption.
```

**§11.10 Atomic operation with emit-table axiom.**

```
// Surface:
let ctr : atomic<u64> = atomic_init(0u64);
ctr.fetch_add(@SeqCst, 1);

// Kernel:
Ind { name = "atomic"; params = [(T :_erased Type<0>)];
      constructors = [ { atomic_init : T → atomic T } ] };

fetch_add : Π (T :_erased Type<0>)
            (cell :_{usage=ω, effect={Atomic}} atomic T)
            (ord :_erased Ordering)
            (delta :_1 T)
          → T :_{effect={Atomic}}

// The meaning of fetch_add at each target is an axiom: the
// kernel's emit-table axiom (U-emit) says "fetch_add with @ord
// on arch A emits the instruction sequence specified in §20.5
// for that (operation, ord, width, arch) cell."  The refinement
// against the ISA's formal memory model (Appendix G) is a
// theorem proved in Lean 4.

// Axioms invoked: Ind-form, Pi-elim, U-emit.
```

The pattern: **every feature points at a specific small subset of
the 32 axioms**.  Users auditing their code walk the dependency
graph via `fxc --show-axioms`.

### 30.8 Lean 4 Reference Implementation

The kernel is implemented in Lean 4.  The FX stage-1 compiler is a
Lean 4 program that elaborates surface FX into kernel terms, checks
them against the kernel rules, and emits code per §20.

Directory layout (reference, subject to evolution):

```
FX/
  Kernel/
    Level.lean          -- Universe levels
    Term.lean           -- Kernel terms (the ten forms of §30.2)
    Grade.lean          -- Grade vector, 22 dimensions
    Context.lean        -- Typing context
    Typing.lean         -- The ~32 axioms as inductive relations
    Reduction.lean      -- β, ι, ν reduction
    Conversion.lean     -- Definitional equality
    Subtyping.lean      -- Universe cumulativity, grade subsumption
  Metatheory/
    Preservation.lean   -- Well-typed terms stay well-typed
    Progress.lean       -- Well-typed terms are values or reduce
    Consistency.lean    -- No closed term of type ∀(P : Type<0>). P
    Normalization.lean  -- All terms normalize
  Elaborator/
    Parser.lean         -- Surface FX → AST
    Desugar.lean        -- AST → kernel terms
    TypeCheck.lean      -- Drives Kernel.Typing
    SmtBridge.lean      -- Z3 oracle for discharge
  Derived/
    Adt.lean            -- §3.3 derivation
    Record.lean         -- §3.4 derivation
    Codata.lean         -- §3.5 derivation
    Effect.lean         -- §9 graded monads
    Session.lean        -- §11 linear codata
    Machine.lean        -- §13 state machines
    Contract.lean       -- §14 contracts
    Atomic.lean         -- §11.10 + §20.5 emit tables
    -- ... one file per spec chapter
  CodeGen/
    FXCore.lean         -- Layer 1 IR
    FXLow.lean          -- Layer 2 IR
    FXAsm/
      X86_64.lean       -- §20.5 emit table
      Arm64.lean
      Rv64.lean
      Mips64.lean
    Encode.lean         -- Bytes
    Link.lean           -- ELF / Mach-O / PE
  Compiler.lean         -- Main driver
```

Lean 4 is chosen as the host because:

 * Lean 4 is itself a proof assistant.  FX's soundness proofs live
   in the same language as the compiler.
 * Lean 4's kernel is a template for FX's kernel (both MLTT-family
   with graded extensions).  Proven kernel design patterns
   transfer directly.
 * Lean 4 compiles to C with a small runtime; compiler performance
   matches or beats OCaml for this workload.
 * Mathlib provides the mathematical substrate for dimension
   theorems, refinement predicates, and refinement proofs.
 * Lean 4's metaprogramming (tactics, elaboration macros) can
   auto-generate per-arch emit tables, check kernel invariants at
   elaboration time, and derive standard instances.

The legacy OCaml files in `ocamlx/ml/*` (FStarXC_Parser_FxParse.mly,
LexFX.ml, FxPrint.ml, ParseIt.ml) are from the earlier F*/OCaml
bootstrap plan and are retained as reference only.

### 30.9 The Bootstrap Chain

```
Stage 0: Lean 4 (host)
         │
         ▼
Stage 1: FX compiler in Lean 4
         ├── kernel typechecker
         ├── elaborator for surface FX
         ├── codegen per §20.5 emit tables
         └── linker producing ELF / Mach-O / PE
         │
         │ [compiles]
         ▼
Stage 2: FX compiler in FX
         │
         │ [stage 1 compiles stage 2 source]
         ▼
Stage 3: FX compiler in FX
         │
         │ [stage 2 compiles stage 2 source]
         ▼
Fixpoint: byte-identical stage-2 output and stage-3 output
         │
         └── if not byte-identical, bootstrap divergence bug
```

The fixpoint check is the standard trusting-trust (Thompson 1984)
mitigation: the stage-1 compiler's self-reported behavior must be
reproducible when the stage-2 binary recompiles its own source.
If not, either the stage-1 compiler is buggy or there is a
Thompson-style backdoor; either way, the discrepancy is caught.

Once stage 2 exists and the fixpoint holds, Lean 4 can be removed
from the trusted base for FX users who trust the stage-2 FX
compiler and the fixpoint theorem.  Until stage 2 exists, Lean 4
and the Lean 4 kernel soundness proof (MetaCoq-style, in progress
for Lean 4) are the base of trust.

### 30.10 IxMonad as the Canonical Tier T Instance

Tier T (Protocol typestate) was historically presented as a
bespoke transition relation specific to session types.  The
unifying foundation is the **indexed monad** (Atkey 2009,
*Parameterised Notions of Computation*): a monad parameterized
by initial and final state.  Sessions, machines, transactions,
mutex blocks, STM blocks, and any other "operations against an
explicit state index" pattern are instances of a single class.

```
class IxMonad<f: (idx, idx, type) -> type>
  fn ireturn<i: idx, a: type>(x: a) : f(i, i, a);
  fn ibind<i: idx, j: idx, k: idx, a: type, b: type>(
        x: f(i, j, a), g: a -> f(j, k, b)) : f(i, k, b);
  law left_id  : forall(i: idx, j: idx, a: type, b: type,
                        x: a, g: a -> f(j, j, b)),
                   ibind(ireturn(x), g) == g(x);
  law right_id : forall(i: idx, j: idx, a: type, m: f(i, j, a)),
                   ibind(m, ireturn) == m;
  law assoc    : forall(i: idx, j: idx, k: idx, l: idx,
                        a: type, b: type, c: type,
                        m: f(i, j, a),
                        g: a -> f(j, k, b),
                        h: b -> f(k, l, c)),
                   ibind(ibind(m, g), h)
                   == ibind(m, fn(x) => ibind(g(x), h));
end class;
```

Stdlib instances (in `Std.IxMonad`):

```
instance IxMonad for channel(p_in, p_out, t);
  // Sessions: state set = session-type expressions
instance IxMonad for machine(s_in, s_out, t);
  // State machines: state set = machine state space
instance IxMonad for tx(s_in, s_out, t);
  // Transactions: state set = transaction status
instance IxMonad for mutex(l_in, l_out, t);
  // Mutex blocks: state set = lock acquisition state
```

Each instance ships with its laws SMT-checked at instance
declaration site.  Per-instance composition (sequential
operation, choice, parallel composition) reduces to ibind plus
domain-specific combinators.  Sessions are *not* a separate
calculus; they are an IxMonad instance whose state set is the
set of session-type expressions and whose composition rule is
the per-dimension grade-flow rule of §11.3.

The LICS 2025 effectful-Mealy bisimulation result (Bonchi-Di
Lavore-Román) lifts to the IxMonad law level: bisimilarity at
the IxMonad laws subsumes per-instance bisimilarity, so proofs
about sessions, machines, and transactions reuse the same
bisimulation framework.

### 30.11 Capability Modality Kernel Rule

The Capability dimension (§6.3 dim-cap, Tier L) is the lattice
`(P(NamedCaps), ⊆, ∪, ∅)` with shareability validity predicate.
The kernel introduces the standard graded-modality intro/elim
forms:

```
cap(c, A) : Type      where c : ReachCap

Introduction:
  Γ ⊢_p e : A
  acquired(c) <= p.cap
  ─────────────────────────────────────────
  Γ ⊢_p cap_intro(c, e) : cap(c, A)

Elimination:
  Γ ⊢_p e : cap(c, A)
  Γ, x :_q A ⊢_r body : B
  q.cap = c
  ─────────────────────────────────────────
  Γ ⊢_(p + q * r) cap_elim(c, e, x, body) : B
```

The reach modality of §16.4.1 is `cap(reach(c), t)` —
instantiation at the upper-bound capability set `c` on a
container's elements; the surface form `cap(c, t)` covers both.
Composition with the Usage dimension (dim 3): a linear value
carrying a unique capability is the canonical ownership pattern;
shared capabilities compose pointwise via the lattice join with
shareability check.

### 30.12 2LTT Mode-Level Ghost Separation

The Ghost mode (§6.0) sits in the static layer of two-level
type theory (Annenkov-Capriotti-Kraus-Sattler MSCS 2023; Kovács
ICFP 2022 staged-compilation).  This section documents the
formal separation between ghost (compile-time only) and runtime
content.

```
Static layer (Ghost mode):
  - classical reasoning admitted (excluded middle, choice)
  - proof obligations live here
  - erased at codegen (§1.5)

Dynamic layer (Software mode):
  - constructive only; no excluded middle, no choice
  - compiled to executable code
  - all values are constructive witnesses
```

The `ghost ⊣ erase` adjunction (§6.9) carries the layer
separation:

  * `ghost : Ghost → Software` lifts a ghost value to its
    zero-runtime-cost Software view (the projection of a static
    layer value into the dynamic layer at the binding site,
    which the runtime cannot observe but the type checker
    can).
  * `erase : Software → Ghost` forgets a Software value's
    computational content (the canonical projection from
    constructive to specification).
  * Triangle identities ensure the canonical roundtrip:
    `erase ∘ ghost ≡ id_Ghost` modulo computational content.

A program that uses excluded middle or choice in a ghost
binding cannot extract the binding to a runtime value because
the extraction requires a constructive witness the static
layer does not supply.  This is the formal discipline behind
§1.6: `sorry`, `axiom`, and `with Div` all live at the Ghost
mode and propagate trust through the call graph (§10.6).
Release builds enforce that every reachable Software-mode
function reaches `Verified` trust, with `Assumed` permitted
only via documented `@[trust_assumed("rationale")]`
declarations whose justification surfaces in
`fxi --show-axioms`.

The 2LTT separation supersedes the previous per-binding "ghost
grade = 0" mechanism (which was a kernel axiom Grade-zero and
has been absorbed into the mode separation).  The kernel does
not need a separate erasure rule for ghost terms — the mode
boundary is the rule.

### 30.13 The Corrected Lam Rule

FX uses the Wood/Atkey 2022 formulation of function introduction
with context division (§6.2).  The broken Atkey 2018 rule allows
a linear variable to be used multiple times inside a replicable
closure.  The corrected rule divides the context by the lambda's
grade, erasing linear bindings when constructing an unrestricted
function.

The canonical witness that the broken rule accepts and the
corrected rule rejects:

```
fn higher_order(f: i64 -> i64) : i64 -> i64 =
  fn(x: i64) => f(f(x));
// rejected: f has grade 1 and 1/w = 0 — f not available in closure
```

This is the most-cited soundness regression in graded type
theory; a Coq port of the Wood-Atkey 2022 mechanization lives in
`FX/Metatheory/CorrectedLam.lean` and discharges the rule's
preservation theorem inside the `Pi-intro` axiom of Appendix
H.2.

### 30.14 Known Unsoundness Corpus

FX maintains a catalog of known type theory bugs from the
published literature.  Every entry becomes a permanent
`test_theory` case (§23.6).  The corpus grows; it never shrinks.

**Grade/linearity bugs:**

Atkey 2018 Lam rule — linear variable used twice in replicable
closure:

```
fn higher_order(f: i64 -> i64) : i64 -> i64 =
  fn(x: i64) => f(f(x));
// MUST REJECT: f is linear, used twice in closure body
```

Session endpoint aliased by replicable closure:

```
let ch = new_channel(send(i64); end);
let f = fn() => send(ch, value: 42);
f(); f();
// MUST REJECT: ch is linear, closure captures it but is called twice
```

ML value restriction — polymorphic mutable cell:

```
let id = cell(fn<a: type>(x: a) : a => x);
id.get()(42);
id.get()("hello");
// MUST REJECT: mutable cell prevents generalization
```

**Dependent type bugs:**

Type:Type (Girard's paradox):

```
type U = { t: Type; encode: t -> U; decode: U -> t };
// MUST REJECT: allows encoding a fixed point -> False
```

**Information flow bugs:**

Implicit flow via branch on secret:

```
fn leak(secret flag: bool) : i32 with IO =
  if flag; 1 else 0 end if;
// MUST REJECT: branch on secret determines unclassified output
```

CT violation via secret-dependent memory access:

```
fn bad(secret idx: u8, table: array(u64, 256)) : u64 with CT =
  table[idx];
// MUST REJECT: cache-timing attack reveals idx
```

**Concurrency bugs:**

Fractional permission overallocation:

```
fn bad(own x: ptr(i64)) : unit =
  let (r1, r2, r3) = split3_ref(x);
  // MUST REJECT if Frac(1/3) + Frac(1/3) + Frac(1/3) + epsilon > 1
```

Each entry cites its source paper.  New type theory bug
publications are incorporated as they appear.  A single corpus
regression blocks all releases.

### 30.15 The Five-Layer Defense

The kernel's soundness story is layered.  No single defense
catches everything; the composition of all five gives high
confidence.

**Layer 1: Known-witness smoke tests.**  Every bug in the §30.14
corpus is a `test_theory` case that must be rejected.  Runs on
every build.  Catches: regressions of cataloged bugs.

**Layer 2: Property-based metatheory fuzzing.**  Generate random
well-typed terms, check preservation and progress.  Runs nightly.
Catches: novel bugs matching the tested property.

**Layer 3: Cross-reference with published mechanized proofs.**
Every FX typing rule cites a source with a machine-checked
soundness proof (Coq, Agda, Lean, or F*).  Divergences require
their own proof.  Catches: rules without formal backing.

**Layer 4: Self-verified metatheory.**  Preservation, progress,
canonicity, normalization stated as theorems in FX and proved
by induction.  The proofs are part of the build.  Catches: all
preservation/progress/canonicity violations in the formalized
rules.

**Layer 5: Formal review.**  Every new rule requires provenance,
positive test, negative test, metatheory re-proof, fuzz run, and
corpus check.

### 30.16 Core Meta-Theorems Over the Kernel

The kernel calculus admits five core theorems, stated below and
proved (or to be proved) in Lean 4 in the `FX/Metatheory/` tree.
These are the soundness contract of the whole language.

**Theorem (MTT Canonicity).**  For every closed term `e` of
type `T` at mode `m`, the elaborator computes `e` to a mode-`m`
canonical form (a value, neutral, or constructor application
appropriate to `T`'s kernel form).  Canonicity is the load-
bearing theorem for FX's MTT instance — it generalizes the
strong-normalization-and-consistency story to the multimodal
setting.  Established by Gratzer LICS 2022 for general MTT
instances; FX inherits it for the specific mode theory of
§6.0.

**Theorem (Preservation).**  If `Γ ⊢ e : T` and `e → e'` (one
step of beta / iota / nu / eta reduction per §30.2), then
`Γ ⊢ e' : T`.

Well-typed terms stay well-typed under reduction.  Proved by
induction on the typing derivation.

**Theorem (Progress).**  If `∅ ⊢ e : T`, then either `e` is a
canonical form or there exists `e'` with `e → e'`.

Closed well-typed terms don't get stuck.  Progress + Preservation
together give type soundness.

**Theorem (Consistency).**  There is no closed term `e` such
that `∅ ⊢ e : Π (P : Type<0>). P`.

The kernel is consistent as a logic: no proof of False exists.
This is the load-bearing theorem — if it fails, FX proves
everything, which makes the compiler useless as a proof checker.
Proved via canonicity + classical-content separation: the static
layer (Ghost mode) admits classical reasoning but is erased; the
dynamic layer (Software / Hardware / Wire modes) is constructive
and inherits canonicity.

**Theorem (Strong Normalization).**  Every well-typed kernel
term in the pure-MLTT fragment has a finite reduction sequence
to a normal form.

Normalization implies consistency for the pure fragment.  The
emit-table axiom U-emit (Appendix H) is non-reducing at the
kernel level (it relates kernel atomics to ISA-level
instruction sequences; the kernel doesn't normalize them), so
strong normalization holds over the pure MLTT fragment, and
consistency lifts via the separation between computational
content and the emit axiom.

**Mechanization status.**  All five theorems are stated in the
Lean 4 reference implementation; mechanized proofs are the
long-term research commitment of §30.  Cited precedents:
Gratzer LICS 2022 for MTT canonicity; MetaCoq POPL 2024 for
Coq's kernel; Brandt-Guldstrand-Larsen-Pedersen for Idris 2;
recent Lean 4 kernel verification work in progress.  Until the
Lean 4 proof lands, FX's soundness is "argued-from-cited-
precedent" — the same status Coq occupied until MetaCoq.

The §6.0 mode theory's coherence (§6.0.5) is the additional
obligation MTT canonicity demands of FX specifically: the
mode-theoretic 2-cells must satisfy associativity and identity
laws (the 2-category coherence laws), which the
`FX/KernelMTT/Coherence.lean` module discharges by `decide` over
the finite mode-theory enumeration.


---


## Appendix A: Complete Keyword List

Global keywords (cannot be used as identifiers without backtick
escaping):

```
affine        and          as           assert       await
axiom         begin        bench        bisimulation break
by            calc         catch        class        code
comptime      const        continue     codata       contract
decreases     decorator    declassify   defer        dimension
drop          dual         effect       else         end
errdefer      exception    exists       exports      extern
false         fn           for          forall       ghost
handle        hint         if           impl         in
include       instance     is           label        layout
lemma         let          linear       machine      match
module        mut          not          open         or
own           post         pre          proof        pub
quotient      receive      rec          ref          refinement
return        sanitize     secret       select       self
send          session      sorry        spawn        taint_class
tainted       test         true         try          type
unfold        val          verify       while        with
where         yield
```

Total: 92 global keywords.  All are common English or technical
terms tokenizing as single BPE tokens in modern language models.

`cell` is a stdlib type/function (§4.6), not a keyword — the
same status as `option`, `list`, `result`, `map` — so users can
shadow it locally if they really need to.

Mode names (`Ghost`, `Software`, `Hardware`, `Wire` — §6.0) are
PascalCase identifiers in the mode-theory namespace, not
keywords; they appear as kind annotations in modality
applications.  Modality surface names (`later`, `bridge`, `cap`,
`fix`, `next`, `transport` — §6.10) are stdlib-supplied
lowercase type / function names, also not keywords.  The reach
annotation `reach(c)` (used as `cap(reach(c), t)`) in container
class declarations is an ordinary function call in type
position; `reach` is not a keyword.

Contextual keywords (meaningful only in specific constructs):

```
Machine blocks:     state  transition  initial  terminal
                    emits  on_event  on_signal  priority
                    concurrency  atomic  idempotent  commutative
                    inverse  on_fail  after  cancels  preempts
                    refinement  bisimulation  actor
                    (temporal properties use assert + std/ltl;
                     structural predicates live in std/machine_props;
                     see §13.5)

Contract blocks:    version  migration  compatibility  access
                    format  (serialization binding only; §14.4)

Hardware blocks:    hardware  wire  reg  rising  falling
                    stage  emit  stall  flush  forward
                    redirect  pipeline  onehot  register_file

Register blocks:    field  virtual
                    RW  RO  WO  W1C  W1S  RC  RS  RSVD

Effect blocks:      multishot

Test blocks:        assert_err  assert_within  assert_raises
                    case  expect_compile_error  expect_accepted
                    matches  test_machine  test_contract

Class blocks:       law
```

Typed closers (one closer per semantically distinct block form):

```
end fn              end match           end type            end if
end for             end while           end effect          end handle
end session         end codata          end select          end pipeline
end stage           end asm             end register_file   end machine
end contract        end impl            end test            end bench
end class           end instance        end module          end extern
end verify          end calc            end try             end proof
```

Forms whose bodies are brace-delimited literals use `};` (records
§3.4, contract `format` §14.4, hardware `layout` §18.1, bit pattern
`bits { ... }` §3.2).  These are not typed closers — they close a
brace-delimited expression value, not a declaration block.

Merged variants: `end test` covers `test`, `test_theory`, and
`test_metatheory` (the variant is selected by attribute, §23.6).
`end module` covers `module`, `module type`, and `module functor`
(§5.5).  Decorators are `@[decorator] fn` (§17.3) and close with
`end fn`.  Algebraic structures are `@[structure] class` (§16.6)
and close with `end class`.  Hardware modules are `@[hardware]
module` (§18.8) and close with `end module`.  Registers inside
a `register_file` block close with `end register_file` (no
separate `end register`).
```


## Appendix B: Effect Algebra

The effect lattice:

```
(Effects, \/, Tot) is a bounded join-semilattice.

Tot \/ e = e                 identity
e \/ e = e                   idempotent
e1 \/ e2 = e2 \/ e1         commutative
(e1 \/ e2) \/ e3 = e1 \/ (e2 \/ e3)  associative
Read <= Write                 subeffect
```

Typing rules for effects:

```
G |- e : T [Tot]                    G |- e : T [e1]    e1 <= e2
--------------------  (E-Pure)      ---------------------------  (E-Sub)
G |- e : T [e]                      G |- e : T [e2]

G |- e1 : T1 [e1]    G |- e2 : T2 [e2]
-----------------------------------------  (E-Seq)
G |- e1; e2 : T2 [e1 \/ e2]

G |- f : T1 ->{ef} T2 [e1]    G |- x : T1 [e2]
-------------------------------------------------  (E-App)
G |- f(x) : T2 [e1 \/ e2 \/ ef]

G |- body : T [<E | eff>]    handler covers E
----------------------------------------------  (E-Handle)
G |- handle body ... end handle : S [eff]
```


## Appendix C: Mode Semiring

The usage semiring:

```
Addition (parallel use):       Multiplication (sequential use):
+ |  0    1    w               * |  0    1    w
--+-----------                 --+-----------
0 |  0    1    w               0 |  0    0    0
1 |  1    w    w               1 |  0    1    w
w |  w    w    w               w |  0    w    w
```

The extended mode lattice:

```
        w (unrestricted)
       / \
 affine   relevant
       \ /
        1 (linear)
        |
        0 (absent)
```

Mapping to surface syntax:

```
FX mode       Grade    Linear logic    Rust equivalent
──────────    ─────    ────────────    ───────────────
(default)     1        T @ 1           T (owned, move)
affine        <= 1     T @ affine      —
@[copy]       w        T @ w           T: Copy
ref           w        box T @ w       &T
ref mut       1        diamond T @ 1   &mut T
ghost         0        erased          —
```


## Appendix D: Differences from F*

FX is a ground-up redesign.  The following is a summary of the
major differences for F* users.

```
F*                                  FX
──────────────────────────────────  ──────────────────────────────────
Juxtaposition application (f x y)  Parenthesized (f(x, y))
let x = e in body                  let x = e; body
!x = dereference                   x.get(); not = boolean negation
Separate typ/expr grammar          Unified — types are expressions
ML/Tot/Stack/Ghost effects         Multimodal graded: 22 dimensions, one kernel,
                                    four tiers
DM4F user-facing syntax            effect...end effect, handle...end handle
Tactics in metaprograms            comptime fn, staged programming
Pulse for separation logic         Built into usage grade (§6.4)
sedlex + Menhir lexer/parser       Built-in verified lexer/parser framework
--lax to skip proofs                sorry (tracked in trust dimension)
Z3 as external binary               SMT oracle with auditable UNSAT cores
OCaml extraction                    Native x86/ARM/RV64/MIPS64 codegen per
                                    §20.5 emit tables
OCaml stage-0 bootstrap             Lean 4 stage-0 bootstrap (§30.8-31.9)
~40 axiom equivalents (implicit)    33 explicit kernel axioms (§30,
                                    Appendix H); 'fxc --show-axioms' for
                                    per-definition dependency audit
No explicit kernel calculus         Finite MLTT-family kernel + graded
                                    modalities + emit-table axiom (§30)
Universe variables u#i (F*-style)   Predicative cumulative hierarchy
                                    type<k>, <k: level> binder, no
                                    impredicative Prop (§30.4)
Memory model implicit / LLVM        Per-arch emit tables as ground truth
                                    (§20.5); DRF-reject theorem (§11.10)
```


## Appendix E: Rigor-First Decisions

FX commits to **rigor first**: every annotation the type system uses
is written explicitly by the programmer at the binding or call site.
There is no inference of semantic values.  Mechanical desugaring
survives because it is syntactic rewriting, not semantic inference.

### E.1 Inference eliminated

FX has no inference sites.  The compiler rejects programs that
omit a required annotation with a dedicated error code:

```
Site                              Surface requirement              Error code
────────────────────────────────  ──────────────────────────────   ──────────
Kind of type parameter            <a: type>, <f: Type -> Type>     T044
Type of let-binding (if RHS      let x : T = ...                  T045
  is checking-mode)
Type of lambda parameter          fn(x: T) => ...                  T046
Variance of type parameter        <+a>, <-a>, <=a>                 T048
Lifetime at reference binding     let x : ref(r) T = ...           L001
Grade parameter at binding        grade : size, grade : effect     M003
Effect argument at call site      f<...effect args...>(args)       E043
Cross-width arithmetic            widen<T>(x) at every mixing       T043
Control-flow effect propagation   try expr for Fail/Exn            E042
```

Memory model (§11.10, §20.5) — soundness guards at atomic type
and intrinsic sites:

```
Site                                        Rule                     Error code
──────────────────────────────────────────  ───────────────────────  ──────────
atomic<T> with T not @[copy] or             invalid atomic element   T053
  sizeof(T) ∉ {1,2,4,8}                     type
atomic_wide<T> on target without            missing target feature   T054
  double-word CAS support                   (suggest seqlock<T>)
atomic<T>::load(@Release) /                 invalid ordering for     T053
  store(@Acquire) / etc.                    operation
arch intrinsic used when build target       arch mismatch             P003
  differs from intrinsic's arch
```

Dimension composition rules (§6.8) — soundness guards emitted at
the composition site:

```
Site                                        Composition rule         Error code
──────────────────────────────────────────  ───────────────────────  ──────────
Fail payload has classified data;           classified × Fail        I002
  row not declared 'Fail(secret E)'         (§6.8, gap #102)
Borrow live at 'await(...)' site            borrow × Async           L002
                                            (§6.8, gap #104)
Function declares 'with CT, Async'          CT × Async               E044
                                            (§6.8, gap #105)
'fail(...)' under classified condition      CT × Fail on secret      I003
  in a 'with CT' function                   (§6.8, gap #106)
Monotonic/append_only cell in               monotonic × concurrent   M012
  non-single_thread concurrency without     (§6.8, gap #108)
  atomic(T) or lock_free
Ghost-graded value in runtime if/match/     ghost × runtime          P002
  while/index                               (§6.8, gap #109)
Classified data over async session          classified × async ×    I004
  without CT or declassify                  session (§6.8, gap #112)
Exact decimal type with overflow(wrap)      decimal × overflow(wrap) N002
                                            (§6.8, gap #113)
Unscoped 'spawn(...)' captures borrow       borrow × spawn (unscoped) L003
  (scoped 'spawn_in(group, ...)' is ok)     (§6.8, gap #114)
Linear value may leak on Fail/Exn path      linear × Fail            M011
  (see §7.11 G-Linear-Cleanup-On-Fail)      (§7.11, gap #101)
```

### E.2 Desugaring preserved

The following are mechanical, deterministic syntactic rewrites.
They are not inference because no choice is involved; the compiler
applies a fixed transformation with a fixed target:

```
Surface                                 Desugars to
─────────────────────────────────────   ──────────────────────────────────────────
x |> f(args)                            f(...args with piped value at unnamed slot)
.field (in fn arg position)             fn(it: _) => it.field (synthesized lambda)
.field1 and .field2                     fn(it: _) => it.field1 and it.field2
else if cond; ...                       elif cond; ... (token transformer)
x, y, z,  before )                       x, y, z  (trailing comma strip)
f"value {x}"                            "value " ^ to_string(x)
rec f(x) = ...                          wrapped in fix combinator per §5.2
```

The test is whether the transformation has degrees of freedom.  If
the compiler could produce multiple valid outputs from the same
input, it is inference and eliminated.  If the output is uniquely
determined by the input, it is desugaring and preserved.

### E.3 Rationale

**For the agentic LLM primary user (§1.2):** explicit annotations
are free.  An LLM producing FX code types all annotations equally
fast and makes no decision without knowing what it wrote.  Inference
ambiguity is a source of silent bugs where the compiler picks a
meaning the LLM did not intend.  Eliminating inference eliminates
this bug class.

**For the human secondary user:** explicit annotations make every
file self-documenting.  A reader sees every decision the compiler
uses, without running the compiler or consulting an IDE hover.  The
one-time cost of typing annotations is paid back by the absence of
"why did the compiler pick that type" investigations.

**For the verifier:** explicit annotations simplify verification.
Preservation and progress are stated against a fully-annotated
surface language; soundness proofs do not need to argue about the
correctness of an inference algorithm.  Proof stability (§10.12)
improves because the compiler cannot silently change an inferred
annotation between runs.

**For the ecosystem:** every `.fx` file parses and type-checks with
the same meaning in every tool that implements the spec.  No
inference heuristic can diverge across implementations.  Third-party
tooling is reliable.

### E.4 Control-flow vs enabling effects

The rigor-first rule naturally splits effects into two classes,
resolving how `try` is applied:

```
Class             Effects                         Call-site marker required?
────────────────  ──────────────────────────────  ──────────────────────────
Control-flow      Fail, Exn                       yes: try prefix or try block
Control-flow      Async (via await)               yes: await(e)
Control-flow      Yield (in generators)           yes: yield is the marker
Enabling          IO, Alloc, Read, Write           no: declared in row only
Enabling          Div, Ghost                      no: declared in row only
Enabling          Network, MMIO, DB, etc.         no: declared in row only
```

An operation is a control-flow effect when performing it transfers
execution to a different point than the next statement (the handler,
the catch, the await resume site, the for-loop body that consumes a
yield).  An enabling effect does not change where execution
continues; it declares a capability the function is permitted to
use.  Control-flow effects require visible markers; enabling effects
do not.

### E.5 Sections governed by this rule

The rigor-first rule applies across the spec.  The following
sections carry the explicit-syntax obligation for their dimension:

 * §1.1 — Dimensions table; every annotation explicit.
 * §3.5 — Codata with explicit `sized s;` and `with Productive`.
 * §3.8 — `widen<T>` and `narrow<T>` at every cross-width site.
 * §3.13 — Kind annotations on every type parameter.
 * §4.6 — Every let-binding carries its type either via binding
   ascription or via a synthesis-mode RHS (bidirectional discipline).
 * §4.9 — `try` prefix at every callsite of a `Fail` or `Exn`
   function; control-flow vs enabling split.
 * §5.3 — Lambda parameter types mandatory.
 * §6.3 — Tier system (S, L, T, F, V); twenty-two dimensions, one kernel.
 * §6.7 — Grade parameters at every binding.
 * §6.8 — Dimension composition rules: I002, I003, I004, L002,
   L003, E044, M012, N002, P002 for cross-dimension soundness
   collisions.
 * §7.11 — `defer` and `errdefer` for cleanup; linear-cleanup rule
   at every Fail/Exn abort site.
 * §8.1 — Lifetimes at every reference-bearing site.
 * §9.2 — Effect arguments at every call to an effect-polymorphic
   function.
 * §16.7 — Variance annotations (`+`, `-`, `=`) on every type
   parameter.

See each section for the surface syntax and the error code emitted
when the rule is violated.


## Appendix F: Operator Precedence and Associativity

Sixteen precedence levels, lowest to highest.  Every infix operator
belongs to exactly one level.  The formal grammar is in
`fx_grammar.md` §3; this appendix is the human-reading reference.

```
 Level  Operators / Keywords      Assoc        Role
 -----  -----------------------   ----------   -----------------------------
   1    ->                        right        function type arrow
   2    |>                        left         pipe
   3    <==>                      right        propositional iff
   4    ==>                       right        propositional implies
   5    or                        left         logical disjunction
   6    and                       left         logical conjunction
   7    not                       prefix       boolean negation
   8    == != < > <= >=           non-chain    comparison (T050 on chain)
   9    is                        left         constructor test
  10    |                         left         bitwise OR
  11    ^                         left         bitwise XOR
  12    &                         left         bitwise AND
  13    << >>                     left         shift
  14    .. ..=                    nonassoc     range
  15    + -                       left         additive
  16    * / %                     left         multiplicative
```

Above every infix except `not`: prefix `-` (negate), `~` (bitwise
NOT).  Above prefix: postfix `.field`, `.method(args)`, `[index]`,
`(args)`.

**Two parse rules that surprise readers of C-family languages:**

 * `not` is below comparisons (level 7 vs level 8), matching
   Python.  `not x is None` parses as `not (x is None)`;
   `not x > 5` parses as `not (x > 5)`.  Below `and` is
   deliberate: `not x and y` is `(not x) and y`, as expected.

 * Chained comparison is **non-chaining**: `0 < x < 10` is compile
   error T050 with suggestion `0 < x and x < 10`.  This prevents
   the C/Java silent-`bool < int` trap and matches FX's one-way-
   to-do-it discipline for LLM-generated code.

**Function-argument position overrides precedence.**  Inside
`f(...)`, commas separate arguments at the top level regardless of
what operators appear in an argument expression.  Parentheses
around a full expression always force maximum binding.


## Appendix G: ISA Memory Models

FX's memory model (§11.10) is defined by the per-architecture
emit tables of §20.5.  Those tables, in turn, refine against
published formal memory models for each supported ISA.  This
appendix names the canonical references; it does not re-derive
them.

### G.1 x86-TSO

**Source.**  Sewell, Owens, Sarkar, "A Better x86 Memory Model:
x86-TSO" (POPL 2009); Sarkar, Sewell, Nardelli, Owens, Ridge,
Braibant, Myreen, Alglave, "The Semantics of x86-CC Multiprocessor
Machine Code" (POPL 2009); machine-checked in HOL4.

**Model summary.**  A per-core store buffer between the register
file and the coherent cache.  Loads read from the store buffer
first (forwarding), then from the cache.  Stores drain from the
store buffer to the cache in program order.  Three of four
reorderings are forbidden in hardware:

```
Load -> Load     forbidden
Load -> Store    forbidden
Store -> Store   forbidden
Store -> Load    ALLOWED   (the store-buffer reordering)
```

The MFENCE instruction drains the store buffer.  LOCK-prefixed
RMW instructions (LOCK XADD, LOCK CMPXCHG, XCHG on memory) drain
the store buffer and serialize against other LOCK-prefixed
operations — so they are simultaneously Acquire, Release, AcqRel,
and SeqCst.

**FX implications.**  The emit table for x86-64 in §20.5 uses
plain MOV for acquire/release/relaxed loads and stores, XCHG
for SeqCst stores, and LOCK-prefixed RMW for all atomic RMWs
regardless of ordering.  This follows directly from the TSO
rules above.

### G.2 ARM Flat Model

**Source.**  Pulte, Flur, Deacon, French, Sarkar, Sewell,
"Simplifying ARM Concurrency: Multicopy-Atomic Axiomatic and
Operational Models for ARMv8" (POPL 2018).  Replaces earlier
Flowing and POP models.  Machine-checked via the `rmem` tool.

**Model summary.**  Weak memory: all four reorderings allowed in
hardware absent explicit fences or acquire/release instructions.
ARMv8 is multi-copy atomic: a store becomes visible to all cores
simultaneously (unlike Power, which has a weaker model where
distinct cores can see stores in different orders).

Acquire-release instructions:

```
LDAR   Load-Acquire Register  — load with acquire semantics (RCsc)
STLR   Store-Release Register — store with release semantics (RCsc)
LDAPR  Load-Acquire PC-ordering (ARMv8.3+) — weaker load-acquire (RCpc)
```

ARMv8.1 LSE instructions (Large System Extensions) provide
single-instruction atomic RMWs with optional A (acquire), L
(release), or AL (both) suffixes: LDADD, SWP, CAS, CASP, etc.

Data Memory Barrier instruction: DMB ISH (inner shareable, full),
DMB ISHLD (load-load + load-store), DMB ISHST (store-store).

**FX implications.**  The emit table for arm64 in §20.5 uses
LDR/STR for Relaxed, LDAR/STLR for Acquire/Release/SeqCst (RCsc
is sufficient for SC on loads and stores), and LSE atomics with
A/L/AL suffixes for RMWs.  Pre-LSE ARMv8.0 (under profile
`embedded_arm64`) uses LDXR/STXR loops with explicit DMB fences
where needed.

### G.3 RVWMO

**Source.**  RISC-V ISA Manual, volume 1 ("unprivileged"),
chapter on RVWMO and Table A.6 ("Mappings from C/C++ primitives
to RISC-V primitives").  Axiomatic model adapted from Adve-
Flanagan Release Consistency with multi-copy atomicity.

**Model summary.**  Explicit predecessor/successor sets on
FENCE instructions encode directional barriers:

```
FENCE R,R        load-load
FENCE R,W        load-store
FENCE R,RW       load -> load+store
FENCE W,R        store-load
FENCE W,W        store-store
FENCE W,RW       store -> load+store
FENCE RW,R       load+store -> load
FENCE RW,W       load+store -> store
FENCE RW,RW      full fence
```

AMO instructions (AMOADD, AMOSWAP, AMOCAS, etc.) carry .AQ/.RL/
.AQRL suffixes for acquire/release/both ordering.  LR/SC
(load-reserved, store-conditional) provide LL/SC-style atomics
when Zaamo is not available.

Extensions relevant to atomics:

```
A         base atomic extension (LR, SC, AMOs for 32/64-bit)
Zaamo     reorganization of atomic memory operations (2023)
Zalrsc    LR/SC pair
Zabha     atomic byte/halfword memory operations (2024)
Zacas     atomic compare-and-swap (2024)
```

**FX implications.**  The emit table for rv64 in §20.5 uses plain
LD/SD for Relaxed, FENCE-bracketed sequences for Acquire/Release
loads and stores on baseline RV64GC, AMO with AQ/RL/AQRL suffixes
for RMWs on Zaamo targets, and LR/SC loops for CAS on targets
without Zacas.  Table A.6 of the RISC-V ISA manual is the
authoritative mapping we refine against.

### G.4 MIPS64 Release Consistency

**Source.**  MIPS64 ISA Reference Manual volume 2, chapter on
SYNC and synchronization primitives.  Release Consistency model
with typed SYNC hints.

**Model summary.**  Weak memory model with explicit SYNC
instruction; the SYNC hint encodes barrier type:

```
SYNC 0    full barrier (legacy name: SYNC)
SYNC 4    store-store barrier (wmb)
SYNC 13   synchronize writes
SYNC 16   acquire barrier
SYNC 17   release barrier
```

LL/SC via `LL` / `SC` (word) and `LLD` / `SCD` (doubleword).
No single-instruction atomic RMW — every RMW is an LL/SC loop.

**FX implications.**  MIPS64 support is available only under
profile `legacy_mips` — not a baseline target.  Emit sequences
use SYNC hints plus LL/SC loops for all RMWs.  Performance is
worse than RISC-V for atomic RMWs (5+ instructions per RMW
versus 1 for Zaamo).

### G.5 Refinement theorem

```
Theorem (memory model soundness):
  For every FX program P,
  for every supported arch A,
  let P_asm = emit(P, A) per the §20.5 tables.
  Then observable_behaviors(P_asm under M_A) ⊆ source_semantics(P),
  where M_A is the formal model of A (G.1–G.4) and source_semantics
  is DRF-SC per §11.10.
```

The proof is a case analysis over the emit tables: for each
cell, show that the instruction sequence's behavior under the
formal ISA model is contained in the SC semantics of the source
operation.  Finite check: ~30 cells per arch × 4 arches = ~120
lemmas.  Each lemma refines one instruction sequence against one
source operation under one formal memory model.

### G.6 Thin-air freedom

C++11 relaxed atomics suffer the "out-of-thin-air" (OOTA) problem:
circular data dependencies between relaxed atomic accesses can
legally produce values that were never written by any thread.
This is an artifact of the source-level specification being
weaker than hardware behavior, specifically to allow compiler
reorderings around relaxed atomics.

FX inherits hardware's no-thin-air property for free.  The emit
tables of §20.5 translate every relaxed atomic source operation
to a single instruction (MOV on x86, LDR/STR on ARM, LD/SD on
RV), and the FX compiler does not speculate across atomics in
its IR.  On single-location atomic accesses, x86-TSO, ARM Flat,
and RVWMO all forbid OOTA values.  Therefore an FX program
using only the atomics defined in §11.10 cannot exhibit OOTA
behavior on any supported target.

This is the payoff of controlling source-to-bytes end to end:
the thin-air problem in C++ exists because the compiler has
freedom hardware doesn't grant; FX has no such freedom, so the
problem doesn't arise.


## Appendix H: Complete Kernel Axiom List

The full enumeration of the 23 kernel axioms referenced in §30.
Every FX definition depends on a subset of this list (see
`fxi --show-axioms`).  Every axiom is stated as a Lean 4
inductive rule in the reference implementation.

The detailed sections H.1-H.7c below decompose each category
schematically.  Several entries are *implementation
decompositions* — for example, H.1 lists U-wf, U-hier, U-cumul,
U-level, U-poly as five rules that the kernel checker dispatches
separately, but level arithmetic (U-level, U-hier) collapses
into U-form for the count of §H.11; the inductive rules are the
same.  H.7 (HIT) replaces the previous Quotient axioms entirely.
The §H.11 totals row is canonical.

Grouped by category.  Each axiom has a short name, a schematic
form, and a one-line rationale.

### H.1 Universes (5 rules / 3 in canonical count)

```
U-wf       Γ ⊢ Type<u> wf                          when u : level
           The universe at level u is a well-formed type.

U-hier     Γ ⊢ Type<u> : Type<level.succ(u)>
           Every universe lives in the next universe up.

U-cumul    Γ ⊢ Type<u> <: Type<v>                 when u ≤ v
           Cumulative subtyping in the universe hierarchy.

U-level    level.zero : level
           level.succ : level → level
           level.max  : level → level → level
           Level arithmetic primitives.

U-poly     Γ ⊢ Π (k : level). T(k) wf
             when Γ, k : level ⊢ T(k) wf
           Universe polymorphism binds a level variable.
```

### H.2 Pi (dependent function) (3)

```
Pi-form    Γ ⊢ A : Type<u>     Γ, x :_g A ⊢ B : Type<v>
           ─────────────────────────────────────────────────
           Γ ⊢ Π (x :_g A) → B : Type<level.max(u, v)>

Pi-intro   Γ/g, x :_g A |-^1 e : B
           ────────────────────────────────
           Γ |-^p λ (x :_g A). e : Π (x :_g A) → B
           (Wood-Atkey 2022 corrected Lam rule with context
           division; prevents linear captured in replicable
           closure.)

Pi-elim    Γ |-^p1 f : Π (x :_g A) → B    Γ |-^p2 a : A
           ─────────────────────────────────────────────
           Γ |-^(p1 + g * p2) f a : B[a/x]
           (Graded application rule §6.2 App.)
```

### H.3 Sigma (dependent pair) (3)

```
Σ-form     Γ ⊢ A : Type<u>     Γ, x :_g A ⊢ B : Type<v>
           ──────────────────────────────────────────────────
           Γ ⊢ Σ (x :_g A) × B : Type<level.max(u, v)>

Σ-intro    Γ |-^p1 a : A    Γ |-^p2 b : B[a/x]
           ──────────────────────────────────────────
           Γ |-^(g * p1 + p2) (a, b) : Σ (x :_g A) × B

Σ-elim     Γ |-^p p : Σ (x :_g A) × B    Γ, x :_g A, y :_1 B ⊢ e : C
           ────────────────────────────────────────────────────────
           Γ ⊢ split p as (x, y) in e : C
```

### H.4 Inductive (4)

```
Ind-form   Γ ⊢ InductiveSpec wf     -- per strict positivity check
           ────────────────────────
           Γ ⊢ Ind { spec } : Type<u>
           (u determined by the constructors' argument universes.)

Ind-intro  Per constructor C with args args(C):
           Γ |-^p args(C) : types(C)
           ──────────────────────────
           Γ |-^p C(args(C)) : Ind { spec }

Ind-elim   The eliminator (recursor) at the motive P:
           Γ |-^_ P : Ind{spec} → Type<v>
           Γ |-^p_i methods_i : ...
           Γ |-^_ scrutinee : Ind{spec}
           ─────────────────────────────
           Γ ⊢ Ind-rec P methods scrutinee : P scrutinee

Ind-ι      Ind-rec P methods (C(args))  ≡  method_C applied to args
           (iota reduction; β-like rule for constructors)
```

### H.5 Coinductive (4)

```
Coind-form   Γ ⊢ CoinductiveSpec wf    -- per guardedness check
             Γ ⊢ Coind { spec } : Type<u>

Coind-intro  The unfold:
             Γ |-^_ s : size    Γ, self :_ω Coind{spec}(s) ⊢ body
             ─────────────────────────────────────────────────
             Γ ⊢ unfold<s> body : Coind{spec}(s)

Coind-elim   Per destructor d:
             Γ |-^p c : Coind { spec }(s)   s ≥ 1
             ────────────────────────────────────
             Γ |-^p d(c) : ...  at  Coind{spec}(s - 1)

Coind-ν      The guardedness condition (Abel-Pientka POPL 2013):
             In unfold<s> body, self appears strictly inside a
             destructor body.  Non-guarded = compile error G001.
             (Coppo-Dezani guardedness extended to copatterns.)
```

### H.6 Identity (3)

```
Id-form    Γ ⊢ T : Type<u>    Γ ⊢ a : T    Γ ⊢ b : T
           ──────────────────────────────────────────
           Γ ⊢ Id T a b : Type<u>

Id-refl    Γ ⊢ a : T
           ─────────────────────
           Γ ⊢ refl_a : Id T a a

Id-J       The J eliminator (path induction):
           Γ, x y : T, p : Id T x y ⊢ P : Type<v>
           Γ, x : T ⊢ r : P[x/y, refl_x/p]
           Γ ⊢ q : Id T a b
           ───────────────────────────────────────
           Γ ⊢ J P r q : P[a/x, b/y, q/p]
```

### H.7 HIT (Higher Inductive Types) (1)

```
HIT-form    Γ ⊢ HitSpec wf
              -- HitSpec lists data constructors C_i AND
              -- path constructors P_j whose endpoints are
              -- previously-introduced data
            ─────────────────────────────────────────
            Γ ⊢ HIT { spec } : Type<u>
            (eliminator HIT-rec is folded into the spec
             — induction respects both data and path
             constructors; Cavallo-Harper POPL 2019 cubical
             computational HIT framework)
```

Quotient types (§3.7) are HIT instances: `Quot T R` is the HIT
with data constructor `class : T → Quot T R` and a path
constructor `eq : ∀ x y. R x y → class(x) =_path class(y)`.
Quot.mk and Quot.lift are derived; the three previous Quot
axioms collapse to this one.

### H.7a Modal Univalence at Wire (1)

```
ModalUniv-Wire   Γ ⊢ A B : Type @ Wire    Γ ⊢ e : A ≃ B
                 ────────────────────────────────────────
                 Γ ⊢ ua_wire e : Id (Type @ Wire) A B
```

Equivalent Wire-mode types are propositionally equal.  Contract
migration (§14.2) is transport along this equivalence; the
two roundtrip laws of the §6.9 serialize ⊣ parse adjunction
witness the equivalence per contract.  Univalence is restricted
to the Wire mode; Software, Hardware, and Ghost modes do not
admit it (avoiding cubical-evaluation cost in the kernel hot
path).

### H.7b Bridge and Later Modalities (2)

```
B-form       Γ ⊢ A : Type @ Software
             ─────────────────────────
             Γ ⊢ B A : Type @ Software
             (Bridge modality witnesses internal parametricity;
              Bernardy-Moulin LICS 2012, Cavallo-Harper POPL
              2020 cubical formulation, Altenkirch et al. 2024
              non-cubical formulation)

later_form   Γ ⊢ a : Type @ Software
             ─────────────────────────────
             Γ ⊢ later(a) : Type @ Software
             (later modality for guarded recursion;
              Nakano LICS 2000, Birkedal-Møgelberg-Schwinghammer-
              Støvring LMCS 2012; replaces syntactic guardedness
              in coind_form with typed elimination via
              fix : (later(a) -> a) -> a)
```

### H.8 Grade Algebra (2)

```
Grade-semiring-laws
           For every Tier S dimension D, the grade set R_D
           forms a commutative semiring (R_D, +, *, 0, 1) with
           distribution and 0-annihilation:
             + commutative monoid; * monoid;
             * distributes over +; 0 * x = x * 0 = 0.

Grade-subsumption
           Γ |-^r e : T    r ≤ s in D's preorder
           ──────────────────────────────────────
           Γ |-^s e : T
           (A value at tight grade usable at loose grade.)

Grade-division
           For grade r and grade vector p, the quotient p/r is
           well-defined as max { d : d * r ≤ p }.
           (Wood-Atkey 2022; required by Pi-intro context division.)

Grade-zero
           Γ |-^0 e : T
           e is ghost — erased at compile time, no runtime cost.
           (Ghost erasure theorem, ICFP 2023 Abel et al.)

Grade-lattice
           For every Tier L dimension D, the grade set R_D forms
           a lattice (R_D, ∨, ∧) with a validity predicate
           valid_D: R_D → bool.  At join/meet sites, if
           valid_D(join(a, b)) = false, the expression is a
           compile error (e.g., clock-domain mismatch CD001,
           representation incompatibility T047).
```

### H.9 Subsumption and Conversion (2)

```
T-conv     Γ ⊢ e : T    Γ ⊢ T ≡ T'
           ──────────────────────────
           Γ ⊢ e : T'
           (Definitional equality — β, ι, ν, η reductions.)

T-sub      Γ ⊢ e : T    Γ ⊢ T <: T'
           ──────────────────────────
           Γ ⊢ e : T'
           (Subtyping at the value level — composes universe
           cumulativity U-cumul, grade subsumption Grade-
           subsumption, refinement weakening, effect row
           inclusion, all as one rule.)
```

### H.10 Emit-Table Axiom (1)

```
U-emit     For each arch A and each atomic operation (op, ord,
           width) in the §20.5 emit tables, the source
           operation's semantics is the behavior of the cited
           instruction sequence under A's formal memory model
           (x86-TSO / ARM Flat / RVWMO / MIPS64 RC; Appendix G).
           The 120-lemma refinement theorem (§20.5) is the
           proof obligation for this axiom.
```

### H.11 Totals

```
Universes                3   (U-form, U-cumul, U-poly; level
                              arithmetic absorbed into U-form)
Pi                       3   (form / Wood-Atkey-corrected intro / elim)
Sigma                    2   (form / intro; elim folded as projection)
Inductive                2   (form-with-strict-positivity / elim;
                              intro/iota folded into the spec)
Coinductive              2   (form-with-Later-guarded productivity / elim)
Identity                 2   (form / J; refl folded as J base)
HIT                      1   (subsumes Quot via path constructors)
Modal univalence         1   (Wire-mode equivalence transport)
Bridge / Later           2   (B-form, Later-form)
Grade algebra            2   (per-tier laws / subsumption;
                              Grade-zero replaced by 2LTT separation)
Subsumption / conversion 2   (T-conv definitional equality; T-sub
                              composes universe / grade / refinement /
                              effect-row inclusion)
Emit-table               1   (U-emit: source atomic op → ISA sequence)
─────────────────────   ──
                        23
```

Twenty-three axioms.  The reduction from earlier ad-hoc kernels
tracks the systematic absorption of derivable constructs:

  * Quot's three axioms (Quot-form / Quot-mk / Quot-lift) collapse
    into the single HIT primitive.  Quotient types remain in the
    surface language; the kernel sees them as HIT instances with
    a path constructor for the equivalence relation.
  * The Grade-zero axiom (ghost erasure) is absorbed into 2LTT
    Ghost ⊣ Software mode separation (§30.12) — ghost terms live
    in the static layer rather than at "grade 0".
  * Coind-ν's syntactic guardedness check is replaced by typed
    Later-elimination per Bridge / Later — Coind-form keeps the
    productivity discipline but offloads the structural check to
    a modality.
  * Inductive intro / iota fold into the spec (the recursor's
    computation rule is determined by the constructors).

The emit-table axiom U-emit is the one non-pure-MLTT axiom — it
connects the type theory to hardware.  Without U-emit, the
kernel is pure multimodal dependent type theory with graded
modalities; with U-emit, the kernel knows about atomic
operations on specific target architectures.

### H.12 Derived, Not Axiomatic

Every surface feature below is **derived** from the 23 axioms
(see the "Kernel Translation" subsection of each chapter):

```
§3.3 ADTs                      →  Ind
§3.4 records                    →  single-constructor Ind
§3.5 codata                    →  Coind
§3.6 tensors                   →  Ind with shape parameters
§3.7 quotients                 →  Quot
§3.13 higher-kinded types      →  universe-polymorphic Pi
§4.3 match                     →  Ind-elim
§4.4 if / else                 →  Ind-elim on bool
§4.5 for / while               →  Ind-elim with fuel
§4.6 let                       →  λ + application
§4.8 comprehensions            →  map / filter via Ind-elim
§4.9 Fail effect               →  Σ + specific monad encoding
§5 modules                     →  Σ records + namespacing
§6 graded types                →  IS the grade algebra axioms
§7 ownership modes             →  specific usage-grade instances
§8 regions                      →  lifetime-grade instances
§9 effects                     →  graded monads (Effect dim)
§10 refinements                 →  Σ with Prop-valued predicates
§11 sessions                   →  Coind with linearity
§12 information flow           →  Security grade + declassify pi
§13 machines                   →  Ind of states + Π transitions
§14 contracts                  →  Σ of (data, version) + migration pi
§15 code versioning            →  version-grade instance
§16 type classes, impl         →  Σ records (dictionary passing)
§17 comptime, staging          →  kernel normalization at elab time
§18 hardware, layout           →  restricted kernel fragment +
                                   emit-table axiom
§19 systems                     →  specific effect-grade instances
§20 compilation                 →  function Term → Binary + U-emit
§21 optimization                →  equivalence-preserving rewrites
§22 sketch mode                 →  same kernel, looser elaborator
§23 testing                    →  Bool-valued functions + Π quantifiers
§26 stdlib                      →  definitions over the 23 axioms
```

Each row is a proof obligation: show the reduction is typeable
using only the 23 axioms plus previously-derived constructs.
When the reduction fails to typecheck, the feature is either
not axiomatizable in the current kernel (requires a new axiom,
with justification) or needs redesign.
