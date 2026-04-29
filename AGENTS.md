# FX Language — Project Context

## MANDATORY: Read the Three Specs Before Any Implementation Work

**Hard rule, no exceptions.**  Before writing, modifying, or
reviewing any FX kernel, elaborator, or derived-layer code —
including every fresh conversation start —
read every line of the following three documents in full:

  1. `fx_design.md` — 16583 lines — canonical language spec
     (now incorporates the MTT-spine reframing content
     previously held in fx_reframing.md; see §6, §27, §30,
     and Appendix H for the kernel calculus, axiom discipline,
     and roadmap commitments)
  2. `fx_grammar.md` — 1981 lines — formal EBNF grammar
  3. `fx_lexer.md` — 598 lines — tokenizer specification

Total: ~19,200 lines.

This is not optional.  FX is a 21-dimensional graded modal type
theory with cross-dimension soundness collisions catalogued in
§6.8; implementation decisions made without full spec context
routinely violate constraints stated elsewhere in the spec.
fx_design.md additionally commits FX to a specific theoretical
direction (MTT-spine with enumerable peripheries) — every new
kernel change is checked against the decision discipline in §30
and Appendix H.

**Workflow:**

  * On clean-context / fresh-conversation start: read all three
    docs fully before touching code or tasks.
  * Session compaction is not a fresh conversation start.  After
    `/compact` or automatic context compaction, continue from the
    compacted summary and refresh only the spec sections directly
    relevant to the code being changed.
  * Do NOT rely on summaries, CLAUDE.md excerpts, or memory
    entries as substitutes for reading the specs themselves.
    Memories and CLAUDE.md are index layers over the specs, not
    replacements for them.

**What does NOT count as reading**:

  * Skimming headings.
  * Reading one document and inferring the rest.
  * Reading `fx_design.md` and skipping the two companions —
    the grammar and lexer docs are not redundant with the design
    doc; they cover distinct domains and include decisions not
    present in the design doc.

**What DOES count**:

  * Using the Read tool with `offset`/`limit` to cover every
    line of each file.  Most files fit in 2-4 Read calls;
    fx_design.md fits in ~9 chunks at 2000 lines each.
  * Reading the files in the order listed above — design first
    (establishes vocabulary and the MTT reframe), grammar
    second (surface syntax), lexer third (tokenization
    discipline).

After reading: proceed to work on FX.  Skipping this step is
a policy violation; a future agent reviewing your work will
catch it when it contradicts a spec section you should have
seen.

---

FX is a dependently-typed language with a graded modal type system.
Twenty-one graded type dimensions compose in a single function
signature; the dimensions are not orthogonal — §6.8 catalogs the
known soundness collisions. The same source describes software,
hardware (synthesizable to Verilog), and cross-boundary contracts.
Every dimension defaults to
the most restrictive setting; programmers explicitly grant
capabilities.

## Project Layout

- `fx_design.md` — 16583 lines, canonical language spec (31 numbered
  sections + 8 appendices A–H; appendix H enumerates the kernel
  axioms referenced by `fxc --show-axioms`; now incorporates the
  MTT-spine reframing content — see §6, §27, §30, Appendix H).
  REQUIRED READING per the mandatory-read-all-specs rule above.
- `fx_grammar.md` — 1981-line formal EBNF grammar, LALR(1)-compatible
  (authoritative companion to fx_design.md §4.12).  REQUIRED READING.
- `fx_lexer.md` — 598-line tokenizer spec (encoding, identifiers,
  literals, escape sequences, token transformer passes, error
  recovery).  REQUIRED READING.
- `ocamlx/ml/FStarXC_Parser_FxParse.mly` — legacy Menhir grammar
  (OUTDATED vs fx_grammar.md; kept for reference only)
- `ocamlx/ml/FStarXC_Parser_LexFX.ml` — legacy sedlex lexer
  (OUTDATED vs fx_lexer.md; kept for reference only)
- `ocamlx/ml/FStarXC_Parser_FxPrint.ml` — pretty printer
  that decodes F* AST back to FX surface syntax
- `ocamlx/ml/FStarXC_Parser_ParseIt.ml` — parser driver, v1/v2
  dispatch, token transformer pipeline (FSTRING expansion, ELSE
  IF→ELIF merge, trailing comma strip, DOT→DOT_PROJ disambig)
- `gaps.json` — 156 tracked design gaps (ids 1–156 contiguous); the
  first 114 were landed with filled `prior_art` in 46e2e566, and
  #115–156 have been added in incremental commits covering lifetime
  syntax, keyword polysemy, and foundational/semantic/practical
  design concerns
- `design_analysis.json` — 283 sections × 8 analysis fields
  (what_fx_does, closest_prior_art, where_fx_is_better/worse/missing,
  could_we_do_better, verdict, confidence); filling in progress
- `/tmp/da_template.md` — canonical agent template for analysis work

## Bootstrap Status

FX currently desugars into F*'s Parser_AST.term during parsing:
modes become `@[fx_mode("own")]` string attributes, sessions become
nested type applications via `session_send`/`session_recv`/
`session_end`, codata becomes an `@[codata]`-attributed record,
handlers become `__fx_handle(body, ret_lam, handlers_list)`
applications, select becomes `__fx_select([(channel, handler)])`,
verify blocks become `verify_scope(body_lam, ...exports)`, ghost
blocks become `ghost_block(fn() => body)`, dimension declarations
become `assume val Name : dimension`, and so on. This is temporary
scaffolding on the F* AST; FX should eventually own its AST with
seven node categories (Expression, Declaration, Machine, Contract,
Hardware, Test, Pattern).

## User Intent
Primary user of FX is an agentic LLM, not a human. Release criterion is 100% proven.
Design philosophy tracks the math-automation trend. User wants
brutal critical analysis, not cheerleading. No background agents,
no worktrees. Commit regularly with atomic semantically-unified
commits.

## Code Readability Rules (project-wide)

Code tells a story.  Reading a function should read like prose —
a noun subject, a verb action, an adjective condition.  Every
identifier reads as a sentence fragment that narrates what the
thing IS or DOES.  The primary reader of this codebase is an
agentic LLM; names carry semantic weight equal to types.

### Names by part-of-speech

Pick the word class intentionally:

  * **Nouns** for data and state: `typingContext`, `grade`,
    `resolvedBinder`, `elaboratedParams`, `pendingObligations`.
    Plural for collections.
  * **Verbs** for actions (functions, methods, effectful steps):
    `buildPiChain`, `elaborateFnDeclaration`, `resolveQualCtor`,
    `checkExhaustive`, `emitDiagnostic`.  Lead with a verb.
  * **Adjectives / past participles** for transformed values:
    `shiftedBody`, `weakenedContext`, `inlinedTerm`, `erasedGrade`,
    `canonicalForm`.
  * **Question verbs** (`is`, `has`, `should`, `must`, `can`,
    `will`, `was`, `needs`) for booleans, predicates, and
    comparison helpers — see the telling-word rule below.

### Telling-word rule for predicates and booleans

Every `Bool`, `Prop`, or yes/no flag name MUST start with or
contain a question verb so a reader can mentally complete the
sentence:

  * `isLinear`, `isWellFormed`, `isTransparent`, `isConsumed`,
    `isGhost` — "Is this <X>?"
  * `hasLinearGrade`, `hasDeclaredEffect`, `hasRefinement` —
    "Does this have <X>?"
  * `shouldInline`, `shouldEmitWarning`, `shouldSuppress` —
    "Should we <X>?"
  * `mustTerminate`, `mustDischarge`, `mustBeClosed` — "Must
    this <X>?"
  * `canUnify`, `canReduce`, `canCoerce` — "Can we <X>?"
  * `willEscape`, `willBlock` — "Will this <X>?"
  * `wasConsumed`, `wasDeclassified`, `wasVerified` — "Was
    this <X>?"
  * `needsShift`, `needsDivision`, `needsRevalidation` — "Does
    this need <X>?"

Forbidden predicate shapes:

  * `ok`, `valid`, `good`, `done`, `flag`, `check`, `b`, `p`,
    `pred` — these do not form a sentence; the reader cannot
    tell what is being asked.  Replace: `ok → wasElaboratedWithoutError`;
    `valid → isWellFormed`; `done → hasReachedTerminalState`.
  * Negation via prefix `not`: prefer a positively-named inverse
    (`isConsumed` over `isNotConsumed`; write `not isConsumed`
    at the call site when you need the inverse).  Double
    negatives (`notUnused`) are banned.

Lemma / theorem names in Lean obey the same rule:
`isConsumed_impliesGradeZero`, not `lemma1`; `wellFormed_ofChecked`,
not `wf_thm`.

### Hard rules

  * **Banned**: any non-ASCII character in an identifier
    (parameter, variable, function, theorem, constructor, field).
    No Γ, no α, no ω, no μ, no Π, no ⟦, no ≤ as an identifier
    (Lean's `≤` infix notation via `instance : LE X` is fine —
    that is a notation, not an identifier).  Docstrings MAY cite
    the published spec with Unicode.  Code MAY NOT.
  * **Banned**: single-character identifiers (`g`, `t`, `e`, `s`,
    `x`, `a`, `b`, `n`, `i`, `j`) anywhere except canonical
    numeric-`for` loop induction over ranges.
  * **Banned**: two-character identifiers (`ty`, `ex`, `fn`, `st`,
    `pt`, `tc`, `ok`, `nf`).  Abbreviations are not names.
  * **Discouraged**: identifiers ≤ 3 characters.  Prefer `scope`
    over `sc`, `param` over `p`, `binder` over `b`, `result`
    over `r`, `grade` over `g`, `index` over `i`.

### Allowed exceptions (canonical technical terminology)

Three categories of short names are exempt because they ARE the
standard vocabulary in their domain — renaming them would make
the code less recognizable, not more:

  * **Spec primitives** (§31 Kernel Translation): `shift`,
    `subst`, `whnf`, `convEq`, `beta`, `eta`, `iota`, `refl`.
  * **Parser terminology**: `lhs` / `rhs` for binary-operator
    sides inside recursive-descent or precedence-climbing loops.
    Also fine in AST-accessor helpers (`binopLhs?`, `binopRhs?`)
    because they project named fields whose semantics are
    exactly "left side" / "right side".
  * **Math-convention binders in abstract lemma statements**:
    `∀ x, P x` in the signature of a forall-quantifier lemma is
    fine when `x` is a universally-quantified element of an
    algebraic carrier with no role beyond "arbitrary".  Pattern
    variables in the proof body should still be renamed when
    they correspond to a specific role.

### Required patterns

  * Every helper function name states what it does
    (`buildPiChainOverParams`, not `piFromTerm`;
    `elaborateFnDeclaration`, not `elabFn`).  Exception: spec
    primitives above.
  * Pattern variables in match arms name their role:
    `(outerGrade, outerName, outerType) :: remainingParams` —
    not `(g, _, ty) :: rest`.
  * Every intermediate `let`-binding is named after its role:
    `retTypeInFullScope`, `bodyAfterLamChain`, `paramsWithGrades`
    — not `res`, `tmp`, `r`.
  * Fold accumulators name the element type in plural:
    `elaboratedParams`, `pendingObligations` — not `acc`.
  * Boolean helpers follow the telling-word rule:
    `isLinearGrade`, not `linearCheck`; `hasRefinementClause`,
    not `refinement?`; `shouldReject`, not `reject`.

Apply unconditionally to new code.  Apply opportunistically to
existing code when refactoring — don't open rename-only PRs.

---

## §1. Introduction

### §1.1 The Twenty-One Dimensions

Every value carries properties along all applicable dimensions.
Each dimension is a graded algebraic structure (semiring /
lattice / typestate / foundational / versioned) checked by one
grade-checking kernel parameterized by tier (§6.3). Dimensions
compose pointwise on the grade vector but are NOT orthogonal —
§6.8 catalogs the soundness collisions (classified × Fail,
borrow × Async, CT × Async, ghost × runtime, monotonic ×
concurrent, CT × Fail on secret, decimal × overflow(wrap),
borrow × unscoped spawn, classified × async × session).

Provable by the compiler (12): Type (kind of data), Refinement
(constraints), Usage (linear by default), Effect (Tot by default),
Security (classified by default), Protocol (session type),
Lifetime (explicit at every site via `<r: region>` kind),
Provenance (opaque default, granted via `source("x")`), Trust
(`sorry` default, graduates to `proof`), Representation (opaque
default, granted via `repr(C)` / `repr(packed)`), Observability
(opaque/CT default, granted via `transparent`), Clock domain
(combinational default, granted via `Sync(clk)`).

Provable bounds — must be stated or marked `unbounded` (5):
Complexity (`cost O(n)`), Precision (FP error, `exact` default),
Space (zero allocation default, granted via `Alloc(strategy)`),
Overflow (arbitrary precision default, granted via
`overflow(wrap)`), FP order (strict default, granted via
`Reassociate`).

Structural properties (3): Mutation (`immutable` default, granted
via `ref mut` / `ref append`), Reentrancy (`non-reentrant`
default, granted via `rec` / `Reentrant`), Size (observation
depth for codata — `sized s;` + `with Productive`).

Evolution (1): Version — code identity across revisions. Implicit
`version(1)` by default; `@[version(N)]` grants a non-default
label. Lives in Tier V (§6.3) — lattice of version labels with
adapter edges, checked via `refines` / `migration` (§15).

Dimensions that cannot be proved by any compiler — wall-clock
time, energy consumption, hardware clock rate — are not in the
table. They exist as library-level phantom types for annotation
and basic consistency checking.

### §1.2 Design Principles

Deny by default, grant by permission: every capability denied
unless explicitly requested. No copying without `@[copy]`. No
mutation without `ref mut`. No side effects without `with IO`.
No public exposure without `unclassified`. No allocation without
`with Alloc`. Every annotation is a grant, never a restriction.

Correct by construction: incorrect programs do not compile.
Ownership errors, protocol violations, information leaks, effect
mismatches are caught at compile time with precise diagnostics.

Effects as capabilities: `fn f() : i64` performs no IO, no
allocation, no mutation. `fn g() : i64 with IO, Alloc` may. The
difference is mathematically guaranteed. Resources as types (file
handles, connections, locks tracked by ownership). Protocols as
types (message sequence typed). Security as types (classified
data cannot flow to public outputs without `declassify` and
auditable policy). Types are expressions (no separate grammar).
Every behavior is defined (argument evaluation left-to-right,
integer overflow arbitrary-precision by default, FP strict, sort
stable). Complexity is opt-in, safety is not. The compiler is a
proof partner: `sorry` dumps proof state, `#plan` generates
skeleton, `#show` displays what is known.

### §1.3 All Dimensions Composing

A single function can exercise many dimensions simultaneously.
The canonical example `encrypt_and_send<a, r, eff>` takes a
buffer with length refinement, a `secret ref(r)` key, a channel
of session type `send(encrypted: bytes); end`, returns unit
`with IO, Crypto, Async, eff`, has `pre valid_key(key)` and
`post _ => channel_completed(ch)`. The compiler checks type
safety (buffer element type), refinement (length > 0), ownership
(plaintext consumed once, key only borrowed), lifetime (key
borrow valid for `r`), effects (only IO + Crypto + Async + eff
performed), protocol (channel follows send-then-end), and
security (secret key does not flow to unclassified channel) —
all simultaneously.

### §1.4 Structural Impossibility

Buffer overflow (index carries refinement), use-after-free
(linear ownership), double free (linear), null dereference (no
null, option forces match), uninitialized memory (linear), data
race (ownership + memory ordering), resource leak (linear),
secret in logs (classified-by-default), SQL injection (taint
tracking), deadlock (session types with priority), integer
overflow (fixed-width up to 1024 bits, overflow mode declared),
stack overflow (`decreases` proves bounded), FP non-determinism
(exact decimal default), undefined behavior (every reduction
step defined). No `unsafe` keyword. No type-system bypass.
`unreachable` requires proof of unreachability. `sorry` exists
for development but rejected in release builds.

### §1.5 Compile-Time Erasure

Erased (zero runtime cost): refinements, usage grades, security
labels, protocol states, lifetimes, provenance, trust levels,
observability markers, clock domains, complexity bounds,
precision bounds, space bounds. Survives in binary: machine
code, data tags (ADT discriminators), vtable pointers, effect
operations (IO, alloc), memory layout (repr), trust boundary
validators.

---

## §2. Lexical Structure

### §2.1 Source Encoding

UTF-8 source, `.fx` file extension. One file = one module. No
separate interface files; visibility via `pub` on declarations.

### §2.2 Identifiers

`[a-zA-Z_][a-zA-Z0-9_]*`. ASCII only in identifiers, operators,
keywords. Unicode allowed only in string literals and comments.
Single quote `'` is not an identifier character (does not appear
anywhere in FX). Compiler enforces naming: PascalCase for types,
constructors, modules, traits, effects, machine states;
snake_case for functions, variables, fields, type parameters,
effect variables; SCREAMING_SNAKE for constants only. Backticks
escape any token to an identifier: `` `let` ``, `` `fn` ``,
`` `match` ``.

### §2.3 Keywords

92 global keywords (per fx_design.md Appendix A, fx_grammar.md §2.2,
fx_lexer.md §3.2) plus contextual keywords meaningful only inside
specific blocks. Global set: affine, and, as, assert, await, axiom,
begin, bench, break, by, calc, catch, class, code, comptime, const,
continue, codata, contract, decreases, decorator, declassify, defer,
dimension, drop, dual, effect, else, end, exception, exists, exports,
extern, false, fn, for, forall, ghost, handle, hint, if, impl, in,
include, instance, is, label, lemma, let, linear, machine,
match, module, mut, not, open, or, own, post, pre, proof, pub,
receive, rec, ref, return, sanitize, secret, select, self, send,
session, sorry, spawn, tainted, test, true, try, type, val, verify,
while, with, where, yield.

Contextual keywords in machine blocks: state, transition,
initial, terminal, always, never, leads_to, eventually,
responds, reachable, deadlock_free, deterministic, emits,
on_event, on_signal, priority, concurrency, atomic, idempotent,
commutative, inverse, on_fail, after, cancels, preempts,
refinement, bisimulation, actor. In register state machines:
driven_by, when. In contract blocks: version, migration,
compatibility, access, format. In hardware blocks: hardware,
wire, reg, rising, falling, stage, emit, stall, flush, forward,
redirect, pipeline, onehot, register_file. In register blocks:
field, virtual, RW, RO, WO, W1C, W1S, RC, RS, RSVD. In effect
blocks: multishot, subsumes. In class blocks: law,
structure. In test blocks: case, expect_compile_error,
expect_accepted, matches, test_machine, test_contract,
test_theory, test_metatheory.

### §2.4 Literals

Integer: `42`, `0xFF`, `0b1010`, `0o77`. Underscores separate
digit groups: `1_000_000`. Suffix: `42u8`, `42i32`, `42u64`.
Without suffix, integer literal has type `int` (arbitrary
precision). Decimal: `3.14`, `1.0`. Dotted numeric literals are
exact decimals by default — no FP rounding. `0.1 + 0.2 == 0.3`
is always true. Suffix: `3.14d64`, `3.14d128`. Float literals
require explicit suffix: `3.14f32`, `1.0f64`. String literals:
`"hello"`, `f"value is {x}"` (format), `r"raw\nstring"`,
`b"bytes"`. Only double quote. No single-quoted character
literals — use `"c"` and let the type system resolve.
Bit literals: `0b1010` (4-bit), `8b11110000` (explicit 8-bit
via `Nb` prefix). Boolean: `true`, `false`. Ternary (balanced):
`0t10T` is the trit sequence 1, 0, -1. Fixed-width ternary
suffixes: `t6`, `t12`, `t24`, `t48`.

### §2.5 Comments

`//` line, `/* */` block (non-nesting), `///` doc comment that
attaches to the following declaration.

### §2.6 Operators and Logic Keywords

Arithmetic `+ - * / %`. Comparison `== != < > <= >=`. Logical
use keywords: `not` prefix, `and`/`or` infix (keywords, NOT
symbols — there are no `!`, `&&`, `||` tokens). Bitwise
`& | ^ ~ << >>`. Constructor test `is` infix keyword
(`x is Some` returns bool). Propositional: `==>` (implies),
`<==>` (iff) — used in `pre`/`post`/`invariant`/temporal logic.
Pipe `|>`. Arrow `->` (function type), `=>` (match arm / lambda
body). Range `..` exclusive, `..=` inclusive. Spread `...`
(rest in list patterns). Dot `.` (field access / method call).
Attribute prefix `@[`. No `:=`, `::`, `!`, `?`, `?.`, `&&`,
`||`, `<|`, `'` (per fx_grammar.md §2.4).

### §2.7 Disambiguation Rules (26 total)

(1) Semicolon after conditions: `if cond;`, `while cond;`,
`for x in xs;`, `match e;`. (2) Angle brackets introduce at
definition, parentheses apply at usage: `fn map<a, b>(...)`
introduces type parameters, `list(i64)` applies a type
constructor. (3) `->` function type arrow, `fn(x) => body`
lambda. (4) Function bodies use `= expr;` one-liner or
`begin fn ... end fn;` block. (5) Pipe fills the unnamed
parameter: `x |> f(a: v1)`. (6) Every statement and declaration
ends with `;` — no exceptions. Block functions use `return
expr;`. (7) Named definitions require typed closers (`end fn`,
`end match`, `end type`). Lambdas use bare `end`. (8) Modes
are prefix: `own x`, `ref x`, `ref mut x`, `affine x`. No mode
= linear (default). (9) Effect names PascalCase, effect
variables snake_case. (10) `not`/`and`/`or` are keywords,
dereference is `.get()`, no `!`/`&&`/`||` tokens. (11) Types
are expressions, no separate grammar. (12) `comptime` for
compile-time evaluation; no `#if`/`#elif`. (13) Backticks
escape any token. (14) Mutation via `.set(value)` on `ref`
types; in `hardware` blocks, register updates via `.set(value)`
on `reg` types. No `:=`. (15) `format` has two forms:
standalone defines bit layout; inside `contract` defines
serialization binding. (16) `{ }` is record or block in
software; bit concatenation uses `bits { a, b }` prefix;
inside `hardware`, bare `{ a, b }` is concatenation. (17)
`with` has three positions: after return type (effect
annotation), record position (record update), format binding
(format override). (18) Local `fn` inside a block is `Tot` by
default and does not inherit enclosing effects. (19)
Contradictory dimensions are compile errors. (20) Contract
versions inherit underlying type's refinements. (21) Session
branching on secret data is forbidden in CT context. (22)
Clock connections are explicit. (23) ASCII only in code. (24)
Naming conventions compiler-enforced. (25) `.field` without
left operand in function argument position is shorthand for
`fn(it) => it.field`. (26) `ref` has two meanings by position:
`ref x: T` before binding = borrow mode; `ref(value)` as
expression = create mutable heap cell.

---

## §3. Types

Types and expressions share one grammar. The type checker, not
the parser, determines whether an expression denotes a type or a
value.

### §3.1 Primitive Types

Signed fixed-width: `i8 i16 i32 i64 i128 i256 i512 i1024`.
Unsigned: `u8 u16 u32 u64 u128 u256 u512 u1024`. Platform
pointer: `isize usize`. Arbitrary precision: `int` (signed),
`nat` (= `int { x >= 0 }`). `bool`, `char`, `string` (UTF-8,
grapheme-clustered). Exact rationals: `frac64 frac128 frac256`
(numerator/denominator of `iN/iN`), `frac` (arbitrary). Exact
decimal: `decimal` (arbitrary), `dec32 dec64 dec96 dec128 dec256
dec512 dec1024`. IEEE 754: `f32 f64`. `unit` (one value, written
`()`). `never` (empty type, subtype of everything).

Fixed-width integers are preferred. Widths up to 128 bits map to
hardware (x86 SSE, ARM NEON). 256-1024 compile to multi-word
arithmetic with statically known register allocation — no heap,
no branching, fully unrolled. Cover crypto keys (256/512), hash
states (256/512), RSA moduli (1024). Each fixed-width type is a
refinement alias with representation annotation: `u8` =
`nat { x < 256 }` with `repr(bits(8))`; `i32` = `int { -2^31 <= x
and x < 2^31 }` with `repr(bits(32))`. `with overflow(wrap)`
permits wrapping arithmetic on fixed-width.

Fixed-width exact decimals follow IEEE 754-2008 decimal
arithmetic. `dec96` is SSE-size sweet spot on x86 (~4x faster
than `dec128`). Wider decimals (256-1024) use multi-word.
`dec32`=7 digits/32 bits, `dec64`=16/64, `dec96`=24/96,
`dec128`=34/128, `dec256`=71/256, `dec512`=143/512,
`dec1024`=287/1024.

Exact fractions: `frac64` = `i32/i32` pair normalized to lowest
terms after each operation; `frac128` = `i64/i64`; `frac256` =
`i128/i128`. All fraction arithmetic is closed — `frac + frac =
frac`, `frac / frac = frac`, no precision loss, stack-allocated.
Intermediate blowup (`a/b + c/d = (a*d + c*b)/(b*d)` grows
numerator/denominator) is tracked: chain of frac64 ops may
auto-widen internally to frac128 or frac256, narrowing at end if
result fits. When not provably fitting any fixed-width,
`with Alloc` required for arbitrary `frac`.

`int` and `nat` are arbitrary-precision, never overflow,
heap-allocated bignum at runtime, require `with Alloc`. Compiler
emits warning N001 when unbounded. With a refinement bounding
the range, compiler picks narrowest fixed-width and suppresses
warning — no `Alloc` needed.

When to use `int`/`nat`: ghost/proof contexts (grade 0, erased),
specifications (`pre`/`post`/`decreases`), math libraries where
arbitrary precision is the point, prototyping in sketch mode.
When to use fixed-width: all runtime computation with known
bounds, performance-critical code, public API boundaries
(callers see concrete width), cryptographic code (constant-width,
no timing variation).

Literal resolution: unsuffixed `42` has type `int` by default.
When context expects fixed-width, literal resolves at compile
time — no runtime cost, no warning. Compiler checks literal
fits: `let x : u8 = 42` ok; `let w : u8 = 300` error.

### §3.2 Bit Vectors

`bits(n)` n-bit unsigned, compile-time width. `signed_bits(n)`
two's complement. `trits(n)` n-trit balanced ternary with digits
T(-1), 0, 1. Ternary literals: `0t10T` is trits 1, 0, -1. Fixed
ternary: `t6`, `t12`, `t24`, `t48`. Bit slicing: `insn[6:0]`.
Concatenation: `bits { hi, lo }`. Without width prefix, literal
width is minimum needed: `0b1010` is `bits(4)`; `8b11110000` is
8-bit via `Nb` prefix.

### §3.3 Algebraic Data Types

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

Each constructor PascalCase. Payloads use `()` (same as
constructor application). No `of` keyword, no `|` bars. Each
constructor its own line terminated by `;`.

### §3.4 Records

```
type config {
  host: string;
  port: nat;
  tls: bool;
};
```

Construction: `config { host: "localhost", port: 8080,
tls: true }`. Access: `cfg.host`. Update: `{ cfg with port:
9090 }`. Fields use `:` in both type and value positions. `=`
is never used for record fields.

### §3.5 Codata

```
codata stream<a: type>
  fn head(self) : a;
  fn tail(self) : stream(a);
end codata;
```

Values created with `unfold`:

```
fn nats_from(n: i64) : stream(i64) = unfold
  head => n;
  tail => nats_from(n + 1);
end unfold;
```

Note: productivity checking is not explicitly addressed in
§3.5; this is a gap.

### §3.6 Tensors

`tensor(f32, [batch, seq, dim])`. Shape parameters are naturals,
computed at compile time. Shape-incompatible operations fail at
compile time. Broadcasting follows standard rules and is checked
at compile time.

### §3.7 Quotient Types

```
quotient type rat = (int, int { x != 0 })
  by fn((a, b), (c, d)) => a * d == b * c;
```

Compiler verifies the relation is reflexive, symmetric,
transitive. All functions on the quotient must respect
equivalence. Built-in `frac` types are the preferred instance;
quotient is the general mechanism.

### §3.8 Numeric Tower

Fixed-width widening (implicit, lossless):
- `u8 → u16 → u32 → u64 → u128 → u256 → u512 → u1024 → nat → int`
- `i8 → i16 → ... → i1024 → int`
- `uN → iM` when `M > N`
- Decimals: `dec32 → dec64 → dec96 → dec128 → dec256 → dec512
  → dec1024 → decimal`
- Fractions: `frac64 → frac128 → frac256 → frac`
- Bit vectors: `bits(n) → bits(m)` when `n <= m` (zero-extension)
- Cross-family lossless: `iN → frac(2*N)`, `fracN → decimal`

Widening to arbitrary-precision is implicit but introduces heap
allocation — warning if used without `with Alloc`. No implicit
coercion from decimal to float (lossy requires explicit).
Narrowing requires explicit `narrow()` and `with Fail(range_error)`
declaration. Cross-width arithmetic: result is wider of the two;
signed wins when mixing signed/unsigned.

### §3.9 The Never Type

`never` is the bottom type — kernel empty inductive (Ind with no
constructors, Appendix H.4), auto-imported from Std.Prelude,
`absurd<a>(x: never): a`. FX has no top type. Three native
patterns cover what one would reach for: (1) closed enums for
tagged data (JSON, config — enumerate variants, compiler checks
exhaustiveness); (2) contract decode at boundaries (§14 produces
typed values with validators); (3) explicit existentials (§16.5)
for opaque types with behavior. Each preserves §1.5 compile-time
erasure — no runtime type descriptor.

### §3.10 String Semantics

UTF-8 encoded, grapheme-clustered by default. Three measurement
units: Grapheme (default, `"cafe\u0301"` → 4), Codepoint (→ 5),
Byte (UTF-8 byte count). Conversion is explicit via
`as_codepoints`, `as_bytes`. Comparison on `string(Grapheme)` is
NFC-normalized: `"e\u0301" == "\u00E9"` true.

### §3.11 Floating-Point Control

`f32`/`f64` are opt-in. Default fractional type is `decimal`.
Use floats only when IEEE 754 hardware acceleration is needed
(graphics, physics, inference). Per-function controls: `NaN
(propagate)` (NaN in → NaN out), `Denormals (flush_to_zero)`,
`Rounding (toward_zero)`, `FMA`. Default is strict IEEE 754: no
NaN propagation (refinements prevent NaN creation), denormals
preserved, round-to-nearest-even, separate mul/add.

### §3.12 Sort Stability and Collection Order

Default sort is stable. Opt-in `with Unstable` for faster. Hash
maps default to unordered iteration; compiler rejects code that
depends on iteration order for an unordered map. Typed variants:
`hash_map`, `ordered_map`, `sorted_map`.

### §3.13 Higher-Kinded Types

Type constructors have kinds. `list` has kind `Type -> Type`.
Kind annotations on type parameters:

```
class Functor<f: Type -> Type>
  fn fmap<a: type, b: type>(g: a -> b, x: f(a)) : f(b);
end class;

class Monad<m: Type -> Type>
  fn pure<a: type>(x: a) : m(a);
  fn bind<a: type, b: type>(x: m(a), f: a -> m(b)) : m(b);
end class;
```

Kinds inferred from usage when unambiguous.

---

## §4. Expressions

### §4.1 Function Application

All function calls use parentheses. Juxtaposition does not exist.
One-parameter positional: `let y = f(x)`. Multi-parameter
mandatory named args: `let z = connect(host: "localhost",
port: 8080)`. No positional multi-arg syntax — call sites are
self-documenting. Evaluation left-to-right always. Implicit type
args with `#`: `None(#i64)`, `identity(#string, value: "hello")`.

### §4.2 Pipes and Dot-Shorthand

```
let result = items
  |> filter(.active and .age >= 18)
  |> map(.name)
  |> sort_by(.name)
  |> take(100);
```

`.field` without left operand in function argument position is
shorthand for `fn(it) => it.field`. Multiple dots in the same
expression refer to the SAME implicit element: `.active and
.age >= 18` desugars to `fn(it) => it.active and it.age >= 18`.
Valid in any function argument position, not only after `|>`.
When shorthand doesn't fit (complex logic, multiple params, no
field access), use explicit lambda.

### §4.3 Pattern Matching

```
match x;
  0 => "zero";
  1 => "one";
  n => f"number {n}";
end match
```

Semicolon after scrutinee (rule 1). Patterns: literals,
constructors, wildcards (`_`), variable bindings, tuple,
record, spread (`[h, ...t]`), as-bindings. Guards with `if`.
Exhaustiveness checked from constructors and refinements.
Matching on linear value consumes it; arms receive ownership of
corresponding parts. Per fx_grammar.md §8, the grammar also
supports or-patterns (`p1 | p2`), negative-literal patterns
(`-42`), GADT-style constructor patterns with named fields
(`Some(x: v)`), record-pattern rest (`{field, ...}`), and
ignore-all constructor patterns (`C(...)`). fx_design.md §4.3
does not enumerate these extras (gap).

### §4.4 Conditionals

```
if length(xs) > 0;
  head(xs)
else
  default_value
end if
```

Multi-branch via `else if cond; ...`. When `if` is tail
expression of a block, no trailing `;`. As statement, ends with
`;`.

### §4.5 Loops

`for i in 0..10; ... end for;` and `while cond; ... end while;`.
`break`/`continue` exit/skip nearest enclosing loop. Ranges:
`0..10` exclusive, `0..=10` inclusive, `0..100 by 5` stepped.

### §4.6 Let Bindings

Immutable by default: `let x = 42`. Destructuring: `let (a, b)
= split(items)`. Record: `let config { host, port, .. } =
load_config()`. Mutable via `ref`: `let counter = ref(0);
counter.set(counter.get() + 1)`. `.get()` reads, `.set(v)`
writes — method calls, no special operators. Type annotations:
`let x : nat = 42`.

### §4.7 Blocks and Return

`begin fn ... end fn` groups statements. Every statement ends
with `;`. `return` marks produced value. NO implicit tail
expression — `return` always required in block-form functions.
One-liner uses `= expr;` and no `return`. NO EARLY RETURN:
every block-form function has exactly one `return` as last
statement before `end fn`. Guard logic uses `if`/`else`
expressions or error effects (§9), not early exit. Single
entry / single exit per function simplifies verification —
postcondition checked at exactly one location. Local `fn`
inside a block is `Tot` by default and does not inherit
enclosing function's effects (rule 18).

### §4.8 Comprehensions

List comprehensions desugar to `filter` and `map`:

```
let squares = [x * x for x in 0..10];
let names = [u.name for u in users if u.active];
let pairs = [(x, y) for x in 0..5 for y in 0..5 if x != y];
```

(5-line section — likely gap relative to Python/Haskell/Scala
comprehension designs.)

### §4.9 Error Handling

Errors are an effect, not a special operator. `with Fail(E)`
declares. `fail(e)` aborts to nearest handler. Propagation
automatic — no call-site syntax needed. `try`/`catch` at
boundary:

```
try
  let data = fetch_and_parse(42);
  display(data);
catch
  HttpError(code) => log(f"HTTP {code}");
  EmptyInput => log("empty response");
end try;
```

Error types are closed unions. Every failure mode named. No
catch-all `error` type. Combined error type when composing
across modules. `Fail` effect tracks error types precisely.
Compiler verifies every `fail(e)` produces declared error type.

### §4.10 Dot Syntax for Methods

`x.method(args)` sugar for `Type.method(x, args)` where mode of
`x` is determined by the method's `self` parameter:
`conn.is_open()` = `Connection.is_open(ref conn)`;
`conn.set_timeout(5000)` = `Connection.set_timeout(ref mut conn,
5000)`; `conn.close()` = `Connection.close(own conn)`.
Resolution rules in §16.3.

### §4.11 Control Flow as Effects

All control flow derives from delimited continuations (not
user-visible): `return` aborts to function boundary, `break` to
loop, `throw` to try/catch, `yield` suspends to handler,
`await` suspends to async scheduler. Effect system tracks
which delimiters are in scope.

### §4.12 Grammar Summary

fx_design.md §4.12 gives an informal ~70-line sketch; the
authoritative formal grammar is the separate `fx_grammar.md`
(1090-line LALR(1)-compatible EBNF). The informal sketch covers
expressions (pipe, lambda, match, if, for, while, begin, app,
dot, binop, prefix, let, get/set, atom), atoms (IDENT, UIDENT,
literals, list, comprehension, implicit arg, dot shorthand),
declarations (fn with all clauses, type, val, effect, machine,
contract, impl, class, instance, module, open, include), effect
rows, specification clauses, and body forms. For formal parser
work, use fx_grammar.md.

---

## §5. Declarations and Modules

### §5.1 Function Declarations

Name, optional type parameters, parameters, return type,
optional effect annotation, optional specification clauses,
body. One-liner: `fn add(a: i64, b: i64) : i64 = a + b;`.
Block: `fn process(items: list(item)) : list(result) with IO
begin fn ... return ...; end fn;`. Type parameters with angle
brackets at definition site (rule 2). Effects with `with` after
return type. No effect annotation means `Tot`. Strict clause
ordering: `fn name<tps>(params) : return_type with effects
where type_class_constraints; pre preconditions; post r =>
postconditions; decreases measure; = body;`. Misordering is a
compile error. Multiple `post` clauses verified independently.
Identifier after `post` binds return value (programmer's
choice, no magic `result`).

### §5.2 Recursive Functions

`rec` modifier permits self-reference. Every `rec` must have
`decreases` or declare `with Div`. Mutual recursion with `and`.
`pub` on first applies to all `and` clauses. Final `;` follows
last `end fn`.

### §5.3 Lambdas

`fn(params) => body`. Destructuring in lambda params: `fn((name,
_age)) => name`. Parameter types inferred from context when
unambiguous.

### §5.4 Type Declarations

Alias: `type meters = f64; type user_id = nat { x > 0 };`.
Variant (each ctor on own line with `;`, end type terminator):
`type option<a: type> None; Some(a); end type;`. Record (brace
form with `;` separators): `type connection { fd: i32; host:
string; open: bool };`. Variant with named payloads: `type expr
Lit(value: int); Var(name: string); Add(left: expr, right:
expr); end type;`. `@[copy]` marks freely duplicable — compiler
verifies all fields also `@[copy]`. Types without `@[copy]`
are linear by default.

### §5.5 Module System

Each `.fx` file defines one module. `pub` makes declaration
visible to importers. Without `pub`, module-private. NO global
variables. NO top-level `let`. Module-scoped constants use
`const`: `const MAX_RETRIES : u8 = 5;`. Constants always
compile-time evaluated, always module-private — `pub const` is
compile error. Other modules access via `pub fn`. Functions are
sealed — behavior depends only on params and declared effects.
No ambient global state. `open` brings public decls into scope;
`include` re-exports. Scoped open limits import to block:
`begin open Std.Math.Lemmas; ...; end;`. `val` forward
declaration. `extern "C" ... end extern;` block for FFI. Module
functors parameterize module by module (OCaml-style): `module
type Ordered ... end module type; module functor MakeSet(Elem:
Ordered) ... end module functor; module IntSet =
MakeSet(struct ... end struct);`.

---

## §6. The Graded Type System

FX's type system is a graded modal type theory after Atkey 2018
and McBride 2016, with the Lam rule corrected per Wood/Atkey
2022. All twenty-one dimensions are instances of one parameterized
checking algorithm; each dimension provides a semiring.

### §6.1 Resource Semirings

Tuple `(R, +, *, 0, 1, <=)` where `(R, +, 0)` is a commutative
monoid (parallel use), `(R, *, 1)` is a monoid (sequential use),
`*` distributes over `+`, `0 * r = r * 0 = 0` (annihilation),
`<=` preorder compatible with `+` and `*`. Each of the nineteen
dimensions instantiates this structure. Product of all forms the
grade vector every binding carries.

Usage semiring (dim 3): `{0, 1, w}`. `0` absent/erased, `1`
linear, `w` unrestricted. `+` tables: `0+0=0`, `0+1=1`, `0+w=w`,
`1+1=w`, `1+w=w`, `w+w=w`. `*` tables: `0*x=0`, `1*x=x`, `w*0=0`,
`w*1=w`, `w*w=w`. Using a linear variable in both branches of
an `if` yields `1 + 1 = w` → type error for linear binding.

Security semiring (dim 5): `unclassified < classified`. `+`
(combining): `u+u=u`, `u+c=c`, `c+c=c`. Mixing public and secret
yields secret. No implicit downgrade.

### §6.2 Typing Rules

Core judgment: `G |- e : A` with grade vector `p` tracking
resource usage across all dimensions.

Var: `G, x :_r A |- x : A`, grade 0 everywhere, r at x.

App: `G |-_p1 f : (x :_r A) -> B     G |-_p2 a : A` →
`G |-_(p1 + r * p2) f(a) : B[a/x]`. Cost of applying is cost of
function plus argument's cost scaled by parameter grade.

Let: `G |-_p1 e : A     G, x :_r A |-_p2 body : B` →
`G |-_(r * p1 + p2) let x = e; body : B`.

If: `G |-_p0 cond : bool     G |-_p1 then : B     G |-_p2 else :
B` → `G |-_(p0 + p1 \/ p2) if cond; then else end if : B`. Join
is worst case — linear used in both branches becomes
unrestricted → error.

Lam (corrected, Wood/Atkey 2022): `G/p, x :_r A |-_1 b : B` →
`G |-_p fn(x) => b : (x :_r A) -> B`. `G/p` denotes context
division: each binding's grade divided by `p`, where
`pi/p = max { d : d * p <= pi }`. For usage semiring:
`1/w = 0` (linear bindings erased when constructing replicable
lambda), `w/w = w`, `0/w = 0`, `pi/1 = pi`. Rule prevents linear
variable from being captured in unrestricted closure. Broken
Atkey 2018 rule would allow `fn(own f: i64 -> i64) => fn(x) =>
f(f(x))` — using linear `f` twice in replicable closure.

Subsumption: grade weakening `r <= s` allows value at grade `r`
where grade `s` expected.

### §6.3 The Twenty-One Dimension Instances

Dim 1 Type: not a grade — types checked by bidirectional
algorithm, determine which semiring elements are valid for other
dimensions.

Dim 2 Refinement: not a grade. Predicates collected during
elaboration, discharged by SMT. Interact with grades through
dependent grades (§6.7).

Dim 3 Usage: `{0, 1, w}` described above. `own` = 1, `ref` = w,
`affine` = `<= 1`, `@[copy]` = w on type, `ghost` = 0.

Dim 4 Effect: set of labels ordered by subset. `Tot` empty set
is zero. Addition = union. Multiplication = union. `Read <=
Write`. Effects monotonic — once an expression has an effect, no
subexpression can remove it.

Dim 5 Security: two-element `unclassified < classified`.
Addition is join. Multiplication is also join for non-zero
grades; `classified * 0 = 0` (ghost computation on secret erased,
leaks nothing). Compiler tracks security grade of every value.
Unclassified return cannot depend on classified inputs unless
body contains `declassify` with explicit policy —
noninterference.

Dim 6 Protocol: session type state. Not a simple semiring —
session steps form more complex structure (§11). Grade records
which protocol step channel is at. Sending/receiving advances
step. Using channel after protocol complete is grade 0
(consumed).

Dim 7 Lifetime: region variables. Grade records which region
reference belongs to. Preorder: `'a <= 'b` when `'a` outlives
`'b`. Longer lifetime usable where shorter expected. Explicit on
`pub fn`, inferred in local scope.

Dim 8 Provenance: lattice of origin labels `Source(name)`,
`Derived(parent, transform)`, `Aggregated(list)`, `Unknown`.
Addition merges chains. `Source("x") <= Unknown`. Functions
requiring known provenance reject untracked data.

Dim 9 Trust: `Verified > Tested > Sorry > Assumed > External`.
Propagates as minimum through call graph. Addition is min.
Release builds require `>= Verified` (except `Assumed` tracked
separately for axioms).

Dim 10 Representation: not a semiring in usual sense —
`repr(C)`, `repr(packed)`, `repr(big_endian)` are attributes
constraining layout. Preorder: `repr(Native) <= repr(C)` (a
C-compatible layout usable anywhere, not vice versa).

Dim 11 Observability: `opaque < transparent`. In `with CT`
context, all values must be opaque. Addition is join.
`transparent` is a grant — "this value's access pattern may
leak its content."

Dim 12 Clock domain: `{combinational, sync(clk_id)}`.
Combinational is zero — combinational signal can feed any
domain. `sync(a) + sync(a) = sync(a)`. `sync(a) + sync(b) =
CROSS_DOMAIN_ERROR` when `a != b`.

Dim 13 Complexity: naturals with addition. `0` = free.
`cost(f) + cost(g)` = combined. `cost O(n)` function must have
all call paths bounded by O(n). Compiler sums declared costs.
When undeclared, `unbounded` required.

Dim 14 Precision: rational tracking FP error in ULPs. Each FP
op adds: `precision(a + b) = precision(a) + precision(b) + 1
ULP`. `exact` is grade 0.

Dim 15 Space: naturals tracking allocation. `0` no allocation
(stack only). Each `Alloc` adds size. `Alloc(Stack, bound:
4096)` must have all alloc paths within 4096 bytes.

Dim 16 Overflow: `{exact, wrap, trap, saturate}`. `exact` is
bottom. Other three incomparable — mixing is type error unless
coerced. `exact` requires proof that result fits target width;
`int`/`nat` bypass overflow checking but require `with Alloc`.

Dim 17 FP order: `{strict, reassociate}`. `strict <=
reassociate`. Strict means left-to-right, bit-identical across
platforms. Reassociate permits compiler reorder for SIMD.

Dim 18 Mutation: lattice `immutable < append_only < monotonic <
read_write`. Default immutable. `append_only` adds to tail.
`monotonic` permits changes forward in declared partial order.
`read_write` any mutation.

Dim 19 Reentrancy: `{non_reentrant, reentrant}`. Non-reentrant
default. `reentrant` (via `rec` or `with Reentrant`) permits
self-ref but mandates termination proof or `with Div`.

### §6.3.1 Practical Grade Checking

Grade checker maintains grade vector per variable. At each
expression, updates vectors per typing rules. At end of function
body, verifies every linear variable (grade 1) reduced to grade
0 (consumed). Double close → M001. Missing close → M002.

### §6.4 Separation Logic as Usage Grade

FX does NOT have separate separation logic. Separation logic IS
the usage grade — separating conjunction `*` is `+` of grade
algebra. Permission PCM: `Frac of p: rational { 0 < p and p <=
1 }`, `Zero`, `Omega`. `Frac(p) + Frac(q) = Frac(p + q)` when
`p + q <= 1`, else CONFLICT. Surface: `own x` = `Frac(1)`,
`ref x` = `Frac(p<1)`, `ref mut x` = `Frac(1)` exclusive,
`ghost x` = `Zero`. Frame rule automatic.

### §6.5 Ghost State and Custom PCMs

Ghost values exist in proofs but not runtime (Zero). Custom PCM
via `grade_dimension` block with type, unit, op, and
commutative/associative/identity laws verified by SMT.

### §6.6 User-Defined Grade Dimensions

Users define domain-specific semirings via `grade_dimension`
block. Compiler verifies semiring laws via SMT.

### §6.7 Dependent Grades

Grades can be terms: `fn take_n<a>(n: nat, xs: list(a))
pre n <= length(xs);`. Grade depends on runtime value.
Constraints involving runtime values discharged by SMT.

---

## §7. Ownership

### §7.1 The Mode System

Every binding has a mode. Default linear — consumed exactly once.
Modes: Linear (default, once, no drop, no copy), Affine
(`affine`, <=once, drop yes, no copy), Unrestricted (`@[copy]`,
any, drop yes, copy yes), Shared ref (`ref`, any, drop yes, read
only), Exclusive ref (`ref mut`, any, drop yes, no copy).
`@[copy]` on type → unrestricted on all bindings. Discard via
`drop(x)` or `let _ = x;`.

### §7.2 Owned Values

Parameter without mode takes ownership. Must be consumed exactly
once. Using after consumption / not consuming at all = compile
error.

### §7.3 Borrowed Values

`ref` shared borrow, duplicable. `ref mut` exclusive, one
holder. Cannot have both simultaneously.

### §7.4 Affine Values

At most once, dropping permitted. Destructor runs on drop.

### §7.5 Pattern Matching and Ownership

Match consumes scrutinee; bound vars receive ownership of parts.
Match on borrow does NOT consume. Match on `@[copy]` copies.

### §7.6 Implicit Borrowing at Call Sites

Callee's parameter mode determines borrow vs move. Caller never
annotates `ref`/`own`.

### §7.7 Context Splitting

`0 + 0 = 0`, `1 + 0 = 1`, `1 + 1 = w` (error for linear).

### §7.8 The @[copy] Propagation Rule

Type is `@[copy]` iff all components are `@[copy]`. Checked at
definition site.

### §7.9 Integration with Effects

Signature tells caller everything: modes, effects, termination.

### §7.10 Closure Capture and Ownership

Closure capturing linear value is linear (callable once).
Capturing only `@[copy]` = `@[copy]`. Lam rule enforces via
context division. Compiler infers borrow-vs-move per captured
var based on use. Closure lifetime cannot outlive borrows it
holds. On `pub fn`, lifetime parameters explicit.

### §7.11 Defer and Ownership

`defer` registers cleanup for scope exit. Value live and
borrowable until scope ends; ownership transfers to defer frame.
Between `defer` and exit: borrowable but not movable. LIFO order.
Gap: defer + linear + fail interaction underspecified (#101).

---

## §8. Memory

### §8.1 Regions and Lifetimes

Region `r` represents scope during which memory is valid.
References carry region: `fn first<a, r>(xs: ref(r) list(a)) :
ref(r) a pre length(xs) > 0 = hd(xs);`. `static` outlives all
other lifetimes. Lifetime subtyping: if `r1` outlives `r2`, then
`ref(r1, T) <: ref(r2, T)`. Region-scoped allocation frees all
allocations at once via `with_arena`. On `pub fn`, lifetime
parameters explicit. In local scope, inferred.

### §8.2 Allocation Strategies

NO garbage collector. Every heap allocation has determined
lifetime visible in the type. Compiler picks cheapest strategy
satisfying it.

| Strategy     | When selected                        | Cost          |
| ------------ | ------------------------------------ | ------------- |
| Stack        | Value does not escape function       | zero          |
| Region bump  | Group of values die together         | O(1) alloc/free |
| Slab         | Known compile-time size, escapes     | O(1) alloc/free |
| Size pool    | Runtime-determined size              | O(1) amortized |
| Refcounting  | Explicitly shared, multiple owners   | atomic inc/dec |

Programmer overrides: `fn temp<'r>() : result with
Alloc(Region('r));`, `fn small() : array(u8, 256) with
Alloc(Stack);`, `fn shared() : rc(config) with Alloc(Rc);`.
Platforms: x86/ARM — Stack/Region/Slab/Pool/Rc; GPU —
Stack/Region; FPGA — Stack only. Unavailable strategies are
compile errors on constrained platforms.

### §8.3 The Proved Allocator

Allocator is written in FX. Bootstraps from raw memory pages
(mmap or fixed region on embedded). Proves four properties: no
aliasing (every returned pointer addresses memory no other live
pointer addresses; produces `own` pointers), alignment per
type's requirement, freed memory reusable without overlap (slab
slots in free list XOR allocated), thread safety (thread-local
cache of slab pages and pool size classes; global pool under
lock when cache empty/full; every pointer issued by one
thread's cache disjoint from every pointer issued by any
other). Replaceable via interface contract.

### §8.4 Representation Inference

Compiler picks physical representation from what type system
knows. `repr(C)` / `repr(packed)` only at FFI boundaries or to
override default.

Tagged pointer packing: on 64-bit, low 3 bits of aligned
pointers are zero; top 16 bits of user-space addresses zero.
`option(own T)` is one word — `None` is null pointer.

Niche optimization: `nat { x > 0 }` never zero, `bits(3)` never
8 — compiler uses those values as discriminators.
`option(nat { x > 0 })` uses zero for `None`.

Bit packing: record with `bits(3)`, `bits(5)`, `bool`, `bits(7)`
occupies 16 bits, not 4 bytes.

Compressed pointers: pointers into region stored as 32-bit
offsets from region base — 4 GB per region. Cost: one add per
deref. Benefit: halved cache pressure.

Zero-sized types: phantom types, unit fields, markers take zero
bytes.

Struct-of-arrays: when compiler detects field-at-a-time access
patterns (from pipelines and dot-shorthand), may store
collection of records as parallel arrays of fields.
`users |> map(.name)` on SoA layout streams through just the
name array. Override with `repr(AoS)` or `repr(SoA)`.

Hot/cold splitting: struct with freq and rare fields may split
into inline hot + pointer-chased cold.

### §8.5 Memory Layout Control

Explicit layout for FFI and wire formats:

```
type ip_header repr(C, packed, big_endian) {
  version: u4;
  ihl: u4;
  tos: u8;
  total_len: u16;
};
```

Modes: `repr(Native)` (default), `repr(C)`, `repr(packed)`
(no padding), `repr(aligned(n))`, `repr(big_endian)`,
`repr(transparent)` (same layout as wrapped type).

---

## §9. Effects

### §9.1 Effect Annotations

No effect annotation = `Tot` (pure, terminating). Effects with
`with` after return type: `fn read(path: string) : string with
IO`, `fn send(msg: packet) : unit with IO, Async`, `fn loop() :
never with Div`. Effects must be declared on all `pub fn`
signatures. Compiler verifies body's effects are subset of
declared effects. If body performs IO and signature omits
`with IO`, compile error — effects never inferred upward.
`rec` without `decreases` must declare `with Div`. Argument
evaluation left-to-right.

### §9.2 Effect Variables

Allow polymorphism: `fn map<a, b, eff: effect>(f: a -> b with
eff, xs: list(a)) : list(b) with eff`. When called, `eff`
inferred. Row extension `with eff, IO` means whatever `eff` is,
plus `IO`.

### §9.3 The Effect Lattice

Bounded join-semilattice: `Tot \/ e = e`, `e \/ e = e` (idem),
`e1 \/ e2 = e2 \/ e1` (comm), `Read <= Write`. Subtyping `e1 <=
e2` when `e1 \/ e2 = e2`. `Tot` usable where `IO` expected,
not vice versa.

### §9.4 Built-In Effects

`Tot` pure terminating (default); `Div` may diverge; `Ghost`
erased at runtime, checked at compile time; `Exn` may raise;
`IO` general input/output; `Alloc` may allocate heap; `Read`
may read from references/state; `Write` may write (implies
Read); `Async` may perform async operations.

Parallelization rules: `Tot`/`Ghost` always safe; `Read` safe
(readers don't conflict); `Write` requires exclusive access
(ownership ensures); `Alloc` safe (thread-local); `IO` must
serialize or use channels.

### §9.5 User-Defined Effects

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
```

### §9.6 Effect Handlers

Handler provides implementation, removing effect from type:

```
fn run_state<a, s, eff>(init: s, body: unit -> a with
    State(s), eff) : (a, s) with eff
begin fn
  let state = ref(init);
  handle body()
    return x => (x, state.get());
    get(k) => k(state.get());
    put(new_s, k) => begin state.set(new_s); k(()) end;
  end handle
end fn;
```

Typing rule: if body has effect `<E | eff>` and handler provides
clause for every operation of `E`, result has effect `eff`. The
continuation `k` in each operation clause carries remaining
effect `eff` — resumes body with `E` already handled. Return
clause transforms body's result type `A` into handler's result
type `B`. All operation and return clauses must produce same
type `B` with same effect `eff`.

### §9.7 One-Shot and Multi-Shot Continuations

Default one-shot (linear): called at most once, implemented as
direct jumps without heap allocation. Multi-shot via
`multishot` operation mark. Multi-shot requires all captured
values `@[copy]`.

### §9.8 Generators

Sugar over `Yield` effect:

```
effect Yield<y: type>
  fn yield(value: y) : unit;
end effect;

fn fibonacci() : unit with Yield(i64)
begin fn
  let a = ref(0);
  let b = ref(1);
  while true;
    yield(a.get());
    let temp = a.get();
    a.set(b.get());
    b.set(temp + b.get());
  end while
end fn;
```

### §9.9 Async and Await

Operations of `Async` effect: `await(http_get(...))`,
`spawn_in(group, fn() => ...)`. Task groups guarantee all
spawned complete before group exits:

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

### §9.10 Platform-Conditional Effects

x86/ARM: Tot, Div, Ghost, Exn, IO, Alloc, Read, Write, Async.
GPU: Tot, Div, Alloc, Read, Write, Async. FPGA: Tot,
Alloc(Stack), Read, Write. Code on constrained platforms using
unavailable effects is compile error.

---

## §10. Verification

### §10.1 Refinement Types

Base type + predicate: `type pos_int = int { x > 0 };`, `type
bounded = nat { x < 256 };`, `type sorted_list<a> = list(a) {
is_sorted(x) } where Ord(a);`. Variable `x` in refinement
refers to value being refined. Predicates checked at compile
time by SMT when possible, at trust boundaries by generated
runtime validators when not.

### §10.2 Pre- and Postconditions

`pre` on inputs, `post r =>` where identifier after `post`
explicitly binds return value (programmer's choice, no magic
`result`), `decreases` for termination measure. Multiple `post`
verified independently; compiler reports which failed.

### §10.3 Verify Blocks

`verify ... exports` isolates proof work. `exports` section
declares which facts visible to subsequent code:

```
verify
  hint merge_preserves_sort(xs, ys);
  assert is_sorted(result);
exports
  is_sorted(result);
end verify;
```

### §10.4 Assert and Guided Proofs

`assert P;` asks compiler to prove P from context. `assert P
using lemma(args);` names lemma. Multiple via comma-separated
list.

### §10.5 Calculational Proofs

`calc` blocks chain equational reasoning: `calc a * (b + c) ==
a * b + a * c by { ring; }; == a * b + c * a by { rewrite
comm_mul(a, c); }; end calc;`.

### §10.6 Sorry and Axiom

`sorry` placeholder for unfinished proof. Compiles in dev mode,
rejected in release builds. Outputs structured diagnostic (goal,
context, candidates, suggestion). `axiom` declares mathematical
assumption — compiles in all modes but tracked in trust
dimension. Trust propagates as minimum through call graph. Any
call to `sorry`-tainted function has trust `Sorry`. Release
requires `Verified`.

### §10.7 Proof Diagnostics

`#show` displays proof state at program point (Known facts,
Goal). `#plan` generates proof skeleton from goal structure —
compiler analyzes function structure, decomposes goal, searches
lemma database, outputs skeleton with `sorry` at leaves.
Built-in tactics for `by` clauses: `ring`, `field`, `linarith`,
`omega` (Presburger), `decide`, `simp`, `norm_num`.

### §10.8 Trust Boundaries

Origin-based classification: Literal/construction full; verified
function return full; pattern match branch full (guard holds);
IO/FFI/deserialization nothing. For decidable refinements at
trust boundaries, compiler auto-generates runtime validators.
Runtime checks exist at exactly two places: trust boundaries and
external interactions. Everywhere else, compiler proved it.

### §10.9 Refinement Inference

Compiler auto-proves refinements from arithmetic, pattern
matching, just-called postconditions. Manual lemma name needed
for non-trivial cases (`rev_sorted`, existential witness).

### §10.10 Compiler Error Structure

Fixed structure: `error[CODE]: one-line summary at
FILE:LINE:COL`, source line with underline, Goal/Have/Gap,
Suggestion (concrete FX code), `[--explain CODE]`.

Taxonomy: T0xx type; R0xx refinement (pre/post/decreases/
assert); E0xx effect; M0xx mode/ownership; S0xx session; I0xx
information flow; P0xx proof (timeout, unknown, fuel); N0xx
precision; W0xx warnings. Every suggestion is valid FX code,
not vague hint.

### §10.11 Specification Validation

Compiler validates specs before attempting proofs: flags
vacuously-true specs, unrealizable (contradictory) specs, specs
weaker than implementation.

### §10.12 Proof Stability and Budgets

Tracks verification time per obligation. Obligations > 80% of
timeout flagged W001 unstable. Budget mode gives best-effort
within time limit: `fxc verify --budget 30s`.

### §10.13 Incremental Verification

Each `;` is implicit checkpoint. `verify...exports` is explicit
checkpoint. On edit, only checkpoints affected are re-verified.

### §10.14 Additional Proof Tools

Counterexample generation (SMT model), lemma database search
(`fxc search "is_sorted(append(_, _))"`), proof obligation tree,
proof diff on breakage, automatic lemma extraction suggestions,
proof minimization, specification coverage analysis.

---

## §11. Protocols and Concurrency

### §11.1 Session Types

Communication protocol as a type. Each step is send, receive,
branch, or recursive call:

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

type stream_protocol<a> = session rec Loop;
  branch
    next => receive(item: a); Loop;
    done => end;
  end branch;
end session;
```

### §11.2 Duality

`dual(send(T).S) = receive(T).dual(S)`, `dual(receive(T).S) =
send(T).dual(S)`, `dual(S1 + S2) = dual(S1) & dual(S2)` (select
↔ branch), `dual(S1 & S2) = dual(S1) + dual(S2)`, `dual(rec X.
S) = rec X. dual(S)`, `dual(end) = end`. Creating channel
produces pair with dual types.

### §11.3 Using Channels

Channels are linear. Sending consumes send permission and
advances to next protocol state. Using channel after protocol
complete is compile error.

### §11.4 Branching and Selection

Branching side offers alternatives; selecting picks. `match
receive_branch(ch); success => ...; failure => ...; end match`
on client. `select(ch, success); send(ch, token: ...)` on
server.

### §11.5 Multiparty Sessions

Protocols with > 2 participants use global session types; each
participant sees projected view: `Bidder -> Auctioneer : bid;
Auctioneer -> Bidder : result; Auctioneer -> Observer : log;`.

### §11.6 Ownership Through Channels

Sending owned value transfers ownership to receiver.

### §11.7 Task Groups

Guarantee all spawned tasks complete before group exits — no
orphans, no dangling futures: `task_group fn(group) => ...
spawn_in(group, fn() => ...); ... end task_group`.

### §11.8 Parallel Map

Pure functions parallelizable automatically — effect system
proves safety. `items.par() |> map(transform) |> filter(.valid)
|> sum()` — compiler verifies `transform` and `.valid` are Tot.
Source type determines parallelism.

### §11.9 Select

Wait on multiple channels: `select msg from ch1 =>
handle_request(msg); msg from ch2 => handle_request(msg); _
from done => break; timeout 5000 => log("idle"); end select;`.

### §11.10 Memory Ordering

Compiler inserts minimal synchronization (§21.2). Explicit
annotations available: `with MemoryOrder(data: Release, flag:
Release)`. Default for atomics is `SeqCst`.

### §11.11 Deadlock Freedom

Session types with priority annotations guarantee deadlock
freedom. Compiler rejects programs that wait on lower-priority
while holding higher: `@[priority(1)] send(...)`,
`@[priority(2)] receive(...)`.

### §11.12 Pipeline Execution Modes

Same pipeline syntax, different modes: `list(T)` eager;
`Query(T)` lazy (builds plan, `execute()` runs it);
`Stream(T)` streaming with backpressure; `list(T).par()`
parallel requires Tot; `tensor(T).gpu()` GPU kernel;
distributed via `flat_map`+`group_by_key`+`reduce_by_key`.
Eager pipeline fusion: adjacent `map`, `filter`, `map` fuse
into single pass with no intermediate allocations (linear types
prove intermediates consumed once, safe). Lazy optimizer does
predicate/projection pushdown and join reordering. Streaming
overflow strategies: `block`, `drop_newest`, `drop_oldest`,
`spill(path)`, `error`.

---

## §12. Information Flow

### §12.1 Security Labels

Data classified by default — cannot flow to unclassified outputs
without explicit action. Three security keywords: `secret`
(explicit high label), `unclassified` (explicitly safe), no
annotation (classified by default, cannot flow to IO/logs/
unclassified outputs).

### §12.2 Information Flow Rules

Type system enforces noninterference: changing secret inputs
does not change unclassified outputs. Implicit flows through
control structure tracked — branch on secret that controls
unclassified result is compile error.

### §12.3 Taint Tracking

Labels track data from untrusted sources. Each taint class
independent: `taint_class SQLi; taint_class XSS; taint_class
PathTraversal;`. `tainted(SQLi, XSS) input: string` requires
`sanitize(SQLi, input, escaper: escape_sql)` etc. before reaching
typed sinks.

### §12.4 Declassification

Controlled by named policy: `@[declassification_policy] type
CardDisplay allows: secret -> unclassified; principal:
"payment_service"; what: "last 4 digits of card number"; audit:
true; end type;`. Then `declassify(last_four, policy:
CardDisplay)`.

### §12.5 Constant-Time Execution

`with CT` effect guarantees execution trace independent of
secret inputs. Forbidden: `if`/`match` on secret-graded values;
array indexing where index is secret-graded; variable-time
operations on secret values. CT + verification compose.

### §12.6 Logging Safety

Classified-by-default auto-prevents secret-to-log flow —
compile error. `log(f"Processing {user}")` error; `log(f"...
user_id={user.id}")` ok when id is unclassified.

### §12.7 Secure Memory Zeroing

Linear value containing classified data consumed → compiler
inserts secure_zero before deallocation. No annotation needed.
Classified + linear = zeroed on drop.

---

## §13. State Machines

The `machine` construct is where all of FX's capabilities
converge. Current state tracked in the type — invalid
transitions are compile errors.

### §13.1 Declaration

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

Calling a transition invalid from current state is compile
error.

### §13.2 Transition Modifiers

`requires P` guard, `ensures Q` post, `with E` effect,
`inverse t'` verified reverse, `timeout d -> S`, `retry n
strategy`, `atomic` all-or-nothing, `idempotent(key: k)`,
`commutative`, `monotonic`, `emits Event(data)`, `on_fail mode`
(Recoverable/Critical/Atomic).

### §13.3 Inverse Transitions

`inverse` pairs transition with reverse. Compiler proves
composition restores original state. Enables compensation chains
for distributed transactions.

### §13.4 Composition

Six operations: `*` product (parallel independent), `*sync` sync
product (parallel with sync points), `>>` sequence (terminal
data of first feeds initial of second), `match` choice, `*{
while cond }` loop, nest (hierarchical machines).

### §13.5 Properties

Structural (decidable for finite state): `reachable S from T`,
`unreachable S`, `deadlock_free`, `deterministic`,
`terminating`, `bounded(n)`. Safety: `always P`, `never P`.
Liveness: `eventually P`, `leads_to P Q`, `responds P Q within
d`. Fairness: `fair_leads_to P Q`, `progress t`. Finite-state
decided by model checking; parameterized proved by induction
with SMT.

### §13.6 Refinement

When spec and implementation machines exist, compiler proves
implementation correct via state-mapping function: `refinement
RequestImpl refines RequestSpec via fn(impl_state) => match
impl_state; ...; end match; end refinement;`.

### §13.7 Grade Propagation Through Paths

§6 graded type system applies to machine paths. Transition is
function from state to state; App rule `p1 + r * p2` governs
cost. Path accumulates grades by summing across transitions. At
terminal states, compiler verifies all linear resources have
grade 0. Refinements accumulate through paths — each satisfied
guard becomes known fact. Effect composition follows join
semilattice.

### §13.8 Machines and the Twenty-One Dimensions

Each dimension applies to machine state and transitions.
Pattern is uniform: dimension's semiring governs how values
compose through paths. Usage tracks resource ownership across
states. Effects accumulate as join. Security propagates through
state data with no leaks across states. Complexity sums.
Mutation direction constrains. Reentrancy defaults non-reentrant.
Clock domains attach to states in hardware; cross-domain
transitions require synchronizers.

### §13.9 Parameterized Machines

```
machine Queue<a: type, depth: nat>
  state Empty;
  state Partial of { items: array(a, depth); count: nat
    { count < depth } };
  state Full of { items: array(a, depth) };
  transition enqueue : (Empty | Partial) -> (Partial | Full)
    requires state is not Full;
  transition dequeue : (Partial | Full) -> (Empty | Partial)
    requires state is not Empty;
  initial Empty;
end machine;
```

Value parameters must be `comptime`-evaluable.

### §13.10 Concurrency Models

Machine declares how to handle concurrent access: `concurrency
single_thread` (default — error on concurrent access);
`exclusive` (mutex); `lock_free` (CAS, requires all transitions
atomic); `tick_atomic` (per-tick batch, requires commutative).

### §13.11 External Events and Inter-Machine Communication

`on_event remote_close : Connected -> Disconnected;` externally
triggered. Every `on_event` must declare behavior for every
state (handle, ignore, error). Transitions emit events:
`transition fire : Ready -> Firing emits Fired(position,
direction);`. Signals from child to parent: `on_signal
child.Completed(result) => handle_result(result);`. Interlocks:
`transition launch : Countdown -> Launched requires safety.state
is Armed;`.

### §13.12 Machine Transformers

`intercept(M, before, after)` wrap with hooks; `guard(M, pred)`
add preconditions; `effect(M, handler)` add effect;
`monitor(M, obs)` observe; `restrict(M, pred)` remove
transitions; `extend(M, states, transitions)` add new.
Composition: `ProductionOrder = OrderFlow |> guard(perm) |>
intercept(logger) |> monitor(metrics);`.

### §13.13 Machine Collections

Dynamic sets: `machine_set(M)` with `spawn`/`destroy`/`get`/
`query`/`for_each`. Machines are linear — `spawn` creates,
`destroy` consumes. Must be in terminal state to destroy.
Dropping collection destroys all.

### §13.14 Actors

Each actor is a machine processing typed messages. Compiler
verifies exhaustive message handling per state via `receive Msg
when State => handler;`. Compile error if any (message, state)
pair unhandled.

### §13.15 Timed Transitions and Priority

`transition timeout : Waiting -> Error after 30 seconds;`.
`after` durations measured in logical ticks for reproducibility.
Priority: `machine CriticalHandler priority 0;` (highest),
`machine BackgroundTask priority 10;` (lower). Preemption
relationships form a DAG (no circular preemption).

### §13.16 Transition Failure Model

What happens when guard passes but action fails: `on_fail
Recoverable => stay;`, `on_fail Critical => goto Error;`,
`on_fail Atomic => rollback;`. Mandatory for transitions with
effects. Pure transitions cannot fail.

### §13.17 Cross-Machine Invariants

Properties spanning multiple machines, verified after every
transition in any participant: `invariant player_count_stable(
ref world: machine_set(PlayerState)) : count(world, .Alive) +
count(world, .Dead) == INITIAL;`.

### §13.18 Temporal Logic for Hardware

`G(phi)` globally, `F(phi)` finally, `X(phi)` next, `phi U psi`
until. Desugar to quantified properties over cycle-indexed
codata streams, checkable by bounded unrolling or induction.

### §13.19 Bisimulation

`bisimulation codegen_correct relates R: asm_state ->
source_state -> prop; initial: R(asm_init, source_init); step:
forall sa ss. R(sa, ss) ==> R(asm_step(sa), source_eval(ss));
end bisimulation;`. Proof technique for hardware verification
(RTL simulates ISA), compiler verification, protocol
verification.

### §13.20 Snapshots and Atomic Chains

`let snapshot = m.snapshot(); ...; let m = snapshot.restore();`.
Multi-machine atomic: `atomic inventory.remove(slot: 3);
weapon.reload(ammo: item); end atomic;` — either all succeed or
all rolled back via inverses.

### §13.21 Observable State

`m.state` borrows for reading without consuming.
`m.available_transitions()` for REST APIs (HATEOAS) or UIs (button
enablement). `m.can_transition(submit)`.

### §13.22 Machines and UI

UI is pure function from machine state to view. Compiler
verifies every state has rendering (exhaustive match) and
available transitions correspond to enabled UI actions. Example
`ShoppingApp` machine with Browse/ProductDetail/Cart/Checkout/
Processing/Confirmation/Error states. UX guarantees proved:
"user can always go back", "cannot checkout with empty cart",
"cannot charge without address and payment", "every error is
recoverable".

### §13.23 Event Sourcing

`@[event_sourced]` generates event types and replay logic. For
`BankAccount` machine with deposit/withdraw/freeze/close, the
compiler generates `Deposit(amount) | Withdraw(amount) |
Freeze(reason) | ...`, `apply_event`, `rebuild` that folds event
log, and proof that `rebuild(events) == live_state`.

---

## §14. Contracts

Contract governs how a type behaves crossing a boundary. Types
define structure, formats define encoding, machines define
behavior, contracts define rules for data crossing boundaries.
Boundary is anywhere two systems meet: client/server, app/db,
CPU/device, module/module, version N / N+1.

### §14.1 Contract Declaration

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

  format json { id: "id" as number; ... };
  format protobuf { id: 1 as uint64; ... };

  errors { InvalidEmail(string); NameTooLong(max: nat, actual:
    nat); Unauthorized; VersionMismatch(expected: nat, got:
    nat); };
  invariant name.length > 0;
  invariant role == Admin ==> email.ends_with("@company.com");
end contract;
```

One type can have multiple contracts for different boundaries
(UserApi for HTTP, UserStorage for DB, UserEvent for event bus).

### §14.2 Versioning and Migration

Each version defines data shape at that point. Migrations define
transforms. Compiler proves each migration total. Operations:
`add F default D` (backward compat), `remove F` (forward only),
`rename F -> G` (migration required), `alter F : T1 -> T2`
(migration required), `add computed F = expr` (backward compat),
`reorder fields` (backward compat).

### §14.3 Access Mode Algebra

Generalizes across domains: `ReadWrite`, `ReadOnly`,
`WriteOnly`, `WriteOnce`, `AppendOnly`, `Monotonic of order`,
`Guarded of predicate`, `Unique`, `RuntimeConst`, `HotReload`,
`Ephemeral`, `AutoIncrement`, `Deprecated of version`, plus
hardware register modes `W1C` `W1S` `RC` `RSVD` (§18.3).

### §14.4 Format Bindings

Formats define encoding rules; contracts bind formats to types.
Named format declarations can be reused with overrides: `format
json = json_defaults with { created : "created_at"; role :
lowercase; };`.

### §14.5 Generated Operations

From one contract declaration: `C.decode(fmt, raw)`,
`C.encode(fmt, val)`, `C.validate(val)`, `C.migrate(val, from,
to)`, `C.compatible(v1, v2)`, `C.project(fmt)` (external schema).

### §14.6 Contracts and Effects

Effects crossing boundaries (IO, DB, Network, MMIO) trigger
contract enforcement. Uncontracted data at a boundary is
compile error.

### §14.7 Contracts and Machines

Machine state governed by contracts evolves via migration —
transitioning between states of different contract versions
auto-applies migration. Event sourcing with contracts: replaying
old events applies migrations automatically.

### §14.8 Contracts and Sessions

Session messages carry contracted data: `session
PurchaseProtocol send(request: PurchaseRequest via PurchaseApi);
branch approved => receive(confirmation: Confirmation via
PurchaseApi); end; declined => receive(reason: Decline via
PurchaseApi); end; end branch; end session;`. Every message
serialized per contract's format, validated on receive,
version-negotiated at session establishment.

### §14.9 Contract Inheritance

`contract UserStorage for UserRecord extends BaseEntity; ...
format sql extends sql_base { ... }; end contract;`.

### §14.10 Automatic Version Computation

Compiler computes semver from contract diff: removed symbol →
MAJOR; added → MINOR; requires strengthened → MAJOR;
requires weakened → MINOR; ensures strengthened → MINOR;
ensures weakened → MAJOR; effect added → MAJOR; effect removed
→ MINOR; required field added → MAJOR; optional field added →
MINOR. Direction follows subtyping: contravariant on inputs,
covariant on outputs.

---

## §16. The Object Model

FX has NO classes and NO inheritance. It has `impl` blocks, type
classes, existentials, and a resolution lattice.

### §16.1 impl Blocks

Each method takes `self` with explicit mode: `ref self` borrows
shared, `ref mut self` exclusive, `self` (no mode) consumes,
static methods have no `self`.

### §16.2 Dot Syntax

`x.method(args)` sugar for `Type.method(x, args)`. Self mode
determines what happens to caller's value.

### §16.3 The Resolution Lattice

Specificity: Level 0 `impl T` (T's own methods, always wins);
Level 1 `instance Trait for T` (explicit trait impl); Level 2
`class default fn` (trait's default). Resolution has no runtime-
dispatch level; runtime polymorphism uses explicit existential
records (§16.5) whose fields are called directly. If two traits
define same name and T implements both, `x.method()` is compile
error — programmer qualifies `Trait1.method(x)`.

### §16.4 Type Classes

```
class Printable<T: type>
  fn to_string(ref self: T) : string;
  fn print(ref self: T) : unit with IO
  = print_line(self.to_string());   // default method
end class;

instance Printable for Connection
  fn to_string(ref self) : string
  = f"Connection({self.host}, fd={self.fd})";
end instance;
```

`where` clauses constrain type parameters. Coherence: one
instance per (Trait, Type) pair globally. Orphan rule: instances
declared where trait or type lives.

### §16.5 Existentials

FX has exactly one surface syntax for runtime polymorphism:
explicit existential records built on the kernel Sigma type
(Appendix H.3). Form: `type Closeable = exists (T: type), { val:
own T; close: fn(own T) -> unit with IO };`. The record's fields
ARE the vtable — visible at the type level, zero compiler-
generated metadata. Construction builds the record directly
(`Closeable { val: c, close: Connection.close }`); consumption
calls fields directly (`item.close(item.val)`). Multi-method
composition is field aggregation (no trait-sum operator). Kernel
translation: nested Sigma per Appendix H.3. No top type; see
§3.9.

### §16.6 Algebraic Structure Intrinsics

Compiler has built-in knowledge of algebraic structures. `law`
annotations verify via SMT and enable optimizations:
`structure CommMonoid(T) val zero: T; val add: (T, T) -> T;
law left_identity; law right_identity; law associativity; law
commutativity; end structure;`. Enables parallel reduction (comm
monoid fold), factoring (ring), short-circuit
(lattice-with-top), deduplication (idempotent). Hierarchy:
Semigroup → Monoid → CommMonoid → Group → AbelianGroup;
Semiring → Ring → CommRing → Field; PartialOrder → TotalOrder →
Lattice → BoundedLattice.

### §16.7 Variance

Optional annotations on type parameters, inferred when omitted:
`type list<+a>` covariant; `type consumer<-a>` contravariant;
`type cell<a>` inferred (read=+, write=-, both=invariant).

### §16.8 What FX Does Not Have

No class/extends (use composition), no virtual methods (use
exists record §16.5), no trait-object dispatch (use exists
record §16.5), no universal top type (use closed enum or contract
§3.9), no protected fields (use module pub/private), no abstract
class (use type class), no multiple inheritance (use multiple
type classes), no implicit constructors (use `fn new() : T`), no
implicit destructors (use `own self` + linear drop), no operator
overloading (use named methods), no implicit this mutation (use
explicit `ref mut self`), no null (use `option(T)`), no runtime
type tests (pattern match on enum), no friend classes (use module
visibility), no implicit conversions (use explicit
`narrow`/`widen`), no template metaprogramming (use `comptime` +
staging), no syntax macros, no custom operators.

### §16.9 The Builder Pattern

Methods taking `self` and returning same type enable chaining:
`HttpRequest.get(url).header("Authorization", f"Bearer {token}")
.body(payload).send();`.

---

## §17. Compile-Time Evaluation

### §17.1 comptime

`comptime` marks evaluation during compilation. Same syntax as
runtime code: `comptime fn array_size<a>() : nat = sizeof(a) *
1024;`, `comptime begin let table = generate_lookup_table(256);
end;`. Platform branching: `comptime if platform.simd_width >=
512; avx512_matmul(a, b) else if platform.simd_width >= 256;
avx2_matmul(a, b) else naive_matmul(a, b) end if`. If comptime
expression cannot be evaluated at compile time → compile error.

### §17.2 Staged Programming

`code(T)` is the type of a program fragment that when executed
produces value of type `T`. Quote `` `(expr) `` lifts. Splice
`~expr` inserts: `fn gen_power(n: nat) : code(i64 -> i64) ... if
n == 0; `( fn(x) => 1 )` else let rest = gen_power(n - 1); `(
fn(x) => x * (~rest)(x) )` end if`. Subsumes macro-like
codegen: `comptime fn compile_regex(pattern: string) :
code(string -> bool)`.

### §17.3 Decorators

Type-safe function transformers: `decorator cached<a, b>(f: a ->
b) : a -> b begin decorator let cache = ref(empty_map()); fn(x)
=> match Map.find(cache.get(), x); Some(v) => v; None => begin
let result = f(x); cache.set(Map.add(cache.get(), x, result));
result end; end match end decorator;`. Usage: `@[cached] fn
fibonacci(n: nat) : nat decreases n; = if n <= 1; n else
fibonacci(n-1) + fibonacci(n-2) end if;`. Compose:
`@[cached, retry(3)]` right-to-left.

### §17.4 Custom Attributes

Pure metadata, never change parsing or typechecking. Read by
comptime code generators. `@[route("GET", "/api/users")] pub fn
get_users() : list(user) with IO, DB;`. Code compiles with or
without custom attributes.

### §17.5 Physical Units

Named dimension algebra at type level: `dimension Length;
dimension Time; dimension Mass; type meters = qty(Length); type
seconds = qty(Time); type velocity = qty(Length / Time); type
acceleration = qty(Length / Time^2); type force = qty(Mass *
Length / Time^2);`. Runtime representation is bare `f64` — zero
overhead. Mismatched dimensions → compile error.

### §17.6 Codata Operations

Consuming codata: `fn take<a>(n: nat, s: stream(a)) : list(a)
decreases n; = if n == 0; [] else [head(s), ...take(n - 1,
tail(s))] end if;`. Constructing: `fn zip_with<a,b,c>(f: (a, b)
-> c, s1: stream(a), s2: stream(b)) : stream(c) = unfold head =>
f(head(s1), head(s2)); tail => zip_with(f, tail(s1), tail(s2));
end unfold;`.

---

## §18. Bit-Level Types and Hardware

### §18.1 Bit Formats

`format` declares named layout within `bits(n)`. Fields listed
MSB-first with widths. Compiler computes positions and generates
extraction/insertion. Virtual fields reassemble scattered bits
automatically. Dot access on formatted bits compiles to wire
selection — zero gates, zero runtime cost.

```
format R : bits(32) = {
  funct7 : 7; rs2 : 5; rs1 : 5; funct3 : 3; rd : 5; opcode : 7;
};
format B : bits(32) = {
  imm_12 : 1; imm_10_5 : 6; rs2 : 5; rs1 : 5; funct3 : 3;
  imm_4_1 : 4; imm_11 : 1; opcode : 7;
  virtual imm : bits(13) =
    bits { imm_12, imm_11, imm_10_5, imm_4_1, 1b0 };
};
```

### §18.2 Bit Pattern Matching

Match on format fields in pattern position. `.field` inside
format match accesses matched format's field. Compiler verifies
matched constant fields uniquely identify the format (no
overlapping patterns).

### §18.3 Register Access Modes

`RW` read-write, `RO` read-only (writes rejected), `WO`
write-only (reads rejected), `W1C` write-1-to-clear, `W1S`
write-1-to-set (HW self-clears), `RC` read-to-clear (linear
read), `RS` read-to-set, `RSVD` reserved (must write 0, reads
return 0). RC bits: linear operations (reading consumes). W1C
bits: compiler generates write-target-bit pattern (not
read-modify-write). RSVD non-zero write → compile error.

### §18.4 Cross-Register Dependencies

64-bit split across 32-bit regs, fields with cross-reg
dependencies, required write ordering: `virtual dma_addr :
bits(64) = bits { dma_addr_hi, dma_addr_lo } write_order hi
then lo;`. Where constraints: `where dma_len <= 0xFFFF; where
dma_addr.aligned(dma_len);`. Field requires on write:
`requires dma_addr != 0; requires dma_len > 0;`.

### §18.5 Register State Machines

Register values define device state: `register_file UsbPort at
base reg portsc : bits(32) at 0x00 field connect : bit(0) RO;
field enable : bit(1) RW; ... end reg; machine PortState
driven_by portsc state Unpowered when not power; state
Disconnected when power and not connect; ...; end machine; end
register_file;`. Compiler proves via QF_BV SMT: state predicates
mutually exclusive and exhaustive, every transition produces
valid bit pattern, no register write creates undefined state.

### §18.6 SMT Decidability

Bit-vector arithmetic decidable in SMT. Every bit-field
refinement, cross-field dependency, register state predicate,
format pattern exhaustiveness, virtual field reassembly
automatically provable. No fuel, no tactics, no manual lemmas.

### §18.7 Clock Domains

`Sync(clk)` tracks which clock drives signal. Mixing without
synchronizer → compile error. Semiring: `combinational *
sync(c) = sync(c)`, `sync(a) * sync(b) = CROSS_DOMAIN_ERROR`
when `a != b`. Explicit synchronizer: `let synced = sync_2ff(x,
from: clk_a, to: clk_b);`.

### §18.8 The Synthesizable Subset

`hardware` module restricts body to constructs mapping to gates.
Synthesizable: Tot (combinational), Sync(clk) (sequential),
bits(n), bounded loops (`for 0..n`), format types, machine with
Sync. Non-synthesizable: Div, IO, Alloc, Exn, String/list,
arbitrary-precision int.

### §18.9 Combinational Modules

`hardware fn` = pure function on bits, synthesizes to combinational
logic: `hardware fn alu<w>(a: bits(w), b: bits(w), op: bits(4))
: (result: bits(w), flags: bits(4)) = let result = match op; ...
end match; let flags = bits { result == 0, carry_out(...), ... };
(result, flags);`.

### §18.10 Sequential Logic

`on rising(clk)` block creates clocked register updates: `reg
data : bits(w) = 0; on rising(clk) if reset; data.set(0) else
data.set(...) end if; end on;`. `let` outside creates wires
(combinational). `.set()` inside creates register updates
(sequential).

### §18.11 Pipeline Sugar

`pipeline rv64 with Sync(clk, reset) stage fetch ... end stage;
stage decode ... stall when prev.is_load and prev.rd in [d.rs1,
d.rs2]; emit ...; end stage; stage execute ... flush fetch,
decode when branch.taken; ... end stage; stage memory ... end
stage; stage writeback ... end stage; end pipeline;`. Compiler
generates pipeline registers, forwarding muxes, stall logic,
flush logic, valid-bit tracking. Verifies: data hazards handled,
forwarding correct, stalls don't lose instructions, pipeline
refines ISA.

### §18.12 ISA Specification and Refinement

ISA is `Tot` function — golden reference: `fn step(s:
arch_state) : arch_state = let insn = fetch(s.mem, s.pc);
execute(s, decode(insn));`. Pipeline verified against ISA via
refinement: `refinement pipeline_correct spec =
arch_state.step; impl = rv64_pipeline; via fn(pipe) =>
arch_state { x: pipe.rf.regs, pc: committed_pc(pipe), mem:
pipe.dmem }; property correspondence : forall p. commits(tick
(p)) ==> abstract(tick(p)) == step(abstract(last_commit(p))); end
refinement;`. Extraction: `fxc --target verilog module.fx`.

### §18.13 Hardware-Software Co-Verification

Same `register_file` used by RTL, ISA spec, driver. Changing
layout produces compile errors in all three simultaneously.

### §18.14 Compilation Model

`let x = a + b;` → adder + wires; `if sel; a else b end if` →
2:1 mux; match on bits → mux tree/decoder; `reg x : bits(n) =
0;` → n flip-flops with reset; `on rising(clk) x.set(e);` →
register update; format type → wire selection (zero gates);
machine with Sync → FSM (onehot or binary); pipeline → pipeline
regs + hazard logic; `for i in 0..n` → n copies (unrolled);
comptime if → conditional generate; `bits { a, b }` → wire
concatenation (zero gates); `x[7:0]` → wire selection (zero
gates).

---

## §19. Systems Programming

### §19.1 Execution Context as Effects

Effect hierarchy: `HardIRQ < SoftIRQ < Dispatch < Passive`.
`HardIRQ` most restricted: no sleep, no mutexes, spinlocks with
IRQ disabled only, atomic allocation only. `Passive` least
restricted: sleep, mutexes, page fault. Calling less-restricted
from more-restricted → compile error.

### §19.2 DMA as Linear Ownership

CPU vs device ownership tracked. `dma_map_single` consumes buf
(CPU cannot access during DMA). `dma_unmap_single` + `reclaim`
returns ownership to CPU.

### §19.3 Driver Lifecycle Machines

Every resource acquired has `inverse` for cleanup. Compiler
generates cleanup paths for every possible failure point.
`remove` from any state: compensation chain derived from inverse
declarations. Proves: `always (state is Removed) ==>
pci_released and dma_freed and irqs_disabled;`.

### §19.4 Lock Ordering

`lock_order SpinIRQ < DeviceLock < SubsystemLock < GlobalLock;`.
Compiler rejects acquiring in wrong order.

### §19.5 Stack Budgets

`with Alloc(Stack, bound: 2048)` — compiler verifies all frames
in call tree <= 2048 bytes.

### §19.6 Inline Assembly

```
asm x86_64
  "rdmsr"
  in ecx = msr;
  out eax -> lo : bits(32);
  out edx -> hi : bits(32);
  clobbers none;
end asm;
```

### §19.7 Address Space Types

Distinct types prevent mixing: `type phys_addr = bits(64); type
virt_addr = bits(64); type bus_addr = bits(64);`. `fn
ioremap(phys: phys_addr, size: nat) : virt_addr with MMU;`.

### §19.8 NVMe Queue Pair

Detailed example: `module QueuePair<depth: nat> where depth > 0
and is_power_of_2(depth);`. `submit` moves pending_io into
tracker (linear). `complete` uses `.take()` to get owned
pending_io, replaces slot with None. Compile error if already
None (double completion). Linear tracking guarantees: every
submitted command eventually completed, no double completion,
DMA buffers not freed while device owns them.

### §19.9 WiFi Connection State Machine

Crypto keys exist in firmware only when Connected. `disconnect`
transition consumes key set — linear + classified = secure
erasure on drop. Invariants: `always (state is Connected) ==>
keys_installed(dev.fw);`, `always (state is Disconnected) ==>
not keys_installed(dev.fw);`.

### §19.10 C Interop

FX kernel modules produce standard object files: `@[abi(C,
linux_kernel)] @[link_section(".init.text")] pub fn
init_module() : i32 with Passive, IO`. `extern "C" fn
printk(fmt: ptr(u8)) : i32;`. Same calling convention as C,
same object files, links with GCC output.

### §19.11 Allocation in Context

Effect determines valid allocation flags: `with Passive,
Alloc(Kernel)` → may sleep → GFP_KERNEL. `with HardIRQ,
Alloc(Atomic)` → cannot sleep → GFP_ATOMIC. `Alloc(Kernel)`
requires Passive — using in HardIRQ is compile error.

---

## §20. Compilation Pipeline

Source is the only human-readable artifact. Four binary IRs
carry specific information layer to layer.

### §20.1 The Four Layers

| Layer   | Ext   | Represents                        |
| ------- | ----- | --------------------------------- |
| FX      | .fx   | Full language, 21 dimensions      |
| FXCore  | .fxc  | Typed, monomorphic, SSA           |
| FXLow   | .fxl  | Flat, virtual registers           |
| FXAsm   | .fxa  | Target instructions, physical regs |
| Object  | .o    | Raw instruction bytes             |

All intermediates binary with magic number, checksum, compact
encoding. Inspect: `fxc dump --core module.fxc`.

### §20.2 FX to FXCore: Verification and Erasure

90% of compiler intelligence. Parse and desugar. Elaborate and
verify — all 21 dimensions. Monomorphize. Compile constructs
(machines → state enums + dispatch, contracts → validator/
serializer/deserializer, impl → namespaced top-level fns).
Erase — refinements, security labels, protocol states,
provenance, trust levels, observability markers, complexity
bounds, precision bounds, space bounds, clock domains, usage
grades, mutation markers, reentrancy annotations. Drop calls
inserted where linear values leave scope. `secure_zero` before
drop for classified. Volatile markers for MMIO. Trust boundary
validators inserted from contracts. High-level optimize:
inlining, pipeline fusion, deforestation, constant propagation,
DCE, CSE, defunctionalization, contract validator elision.

### §20.3 FXCore to FXLow: Type-Directed Lowering

Types consumed at this layer. ADTs → tagged memory. Pattern
matches → decision trees → branches. Closures → structs (captured
values) + function pointers. Allocation strategies resolve to
concrete calls. Linear drops → Drop + SecureZero + Free
sequences. FXCore ops (~50): IAdd/ISub/IMul/IDiv/IMod, FAdd/
FSub/FMul/FDiv/FSqrt, BAdd/BSub/BMul (bits), ICmp/FCmp/BCmp,
And/Or/Not/Xor, BAnd/BOr/BXor/BNot/BShl/BShr/BAshr, BConcat/
BSlice/BZeroExt/BSignExt, conversions, control, binding, alloc,
memory, linear, data, closure, effect, atomic, ghost, contract.
FXLow ops (~100): same ops but sized (i8..i64, f32/f64, VecAdd
etc. with width × lanes), plus SSA Phi.

### §20.4 FXLow to FXAsm: Instruction Selection and Register Allocation

Each FXLow op maps to target instructions via ISA semantics.
SIMD width resolved based on target feature flags. Register
allocation: liveness, interference graph, graph coloring (or
linear scan for fast compilation). Spills to stack. Linearity
improves liveness precision — consumed value's register freed
at consumption point.

### §20.5 FXAsm to Object: Encoding

One-pass encoding to bytes. Verified: `decode(encode(insn)) ==
insn` for every instruction. Output: ELF / Mach-O / PE.

### §20.6 ISA Formalization

Each target ISA is FX module defining machine state and
instruction semantics. Same module serves codegen verification,
hardware verification, optimizer instruction rewriting. Microarch
cost models separate: latency and throughput per instruction for
specific processors, guide scheduling without affecting
correctness.

### §20.7 End-to-End Correctness

```
theorem compiler_correct :
  forall program input.
    well_typed(program) ==>
    observable(run_binary(compile(program), input))
      == observable(evaluate(program, input));
```

Proof chains simulation relations through each layer:
erase_correct → lower_correct → select_correct → alloc_correct →
encode_correct.

---

## §21. Optimization

### §21.1 Pipeline Fusion

Adjacent `map`, `filter`, `map` on eager sources fuse into single
pass — no intermediate allocations. Linear types prove
intermediates consumed once, making fusion safe.

### §21.2 Automatic Synchronization Inference

Concurrent code: happens-before graph built from access modes
and data dependencies. Compiler inserts minimum synchronization
needed: Nothing (if program structure satisfies ordering),
Fence (weakest that suffices — release/acquire/seq_cst), Atomic
op (for single-word RMW), Lock (for multi-step mutual
exclusion). Inspect with `fxc dump --sync module.fxc`. Override
with `atomic(T)` or `MemoryOrder`.

### §21.3 Aggressive Optimization

`--release=aggressive` / `@[optimize(aggressive)]`: spends more
time for faster output. Treats refinements as optimization
input. Superoptimization (small kernels — try all instruction
sequences bounded length, keep shortest computing same result;
equivalence via SMT over ISA semantics). Whole-program
specialization (generate specialized versions per call site's
refinements). Verified loop transformations (tiling for cache,
fusion of adjacent loops, vectorization, parallelization).
Data structure selection from refinements (e.g., `map(K, V)
where K: nat { <256 }` → direct array; `set(nat { <64 })` →
bits(64) bitmask; `string { length <= 23 }` → inline SSO).
Partial evaluation. Rewrite templates (proved equivalences).
Refinement suggestions (reports which refinements would enable
blocked optimizations). Compile time budget.

### §21.4 Binary Size

No mandatory runtime. Binary contains service modules only for
declared effects. No effects → 0 bytes. IO → ~200 bytes. Full
Async scheduler → ~4 KB. Fixed ELF overhead ~170 bytes. Direct
syscall emission (no libc, PLT, GOT, dynamic linker). Hello
world ~250 bytes. Bare-metal LED blink ~40 bytes. HTTP echo
server ~15 KB. JSON API server ~40 KB. Full web service + DB
~200 KB. Effect-driven linking excludes unused effect service
modules regardless of symbol reference graph.

### §21.5 Tail Call Guarantee

`rec` defaults to requiring tail calls. Non-tail must opt in
via `with StackRecursion`.

### §21.6 Memoization and Idempotency

Cache semantics as property: `with NeverMemoize` (crypto),
`with Memoize` (referential transparency). Distributed:
`with Idempotent(key: order.client_id)`, `with Commutative`,
`with Reversible(undo: rollback_migration)`.

### §21.7 Partial Failure Semantics

`with IO, Atomic` (all-or-error), `with IO, Partial` (returns
count written).

---

## §22. Sketch Mode

FX's activation energy is high — compiler demands types, modes,
effects before running. Sketch mode eliminates up-front cost:
same syntax, same parser, but compiler infers what it can,
converts compile-time checks to runtime, runs on bytecode VM
with sub-100ms startup. When mature, `fxc annotate` upgrades.

### §22.1 The Sketch Profile

Project profile (§28), not a dialect. Every sketch-mode program
is valid FX. `[profile] mode = "sketch"`. Basic type checking;
all proof obligations deferred to runtime assertions; ownership/
effects/security relaxed to warnings. TypeScript-like
strictness.

Fatal: parse errors, mismatched typed closers, missing `return`,
missing `;`, invalid identifier chars, unterminated strings/
comments, `pub const`, top-level `let`, clause ordering errors,
circular modules, missing modules, duplicate definitions,
recursive type without indirection, kind mismatch, wrong arg
count/names.

Warning (extensive list across all 21 dimensions): missing type
annotations (infer), implicit numeric conversion, unproved pre/
post/assert (becomes runtime check), linear double-use / not
consumed, missing effect annotation, classified data to IO,
non-exhaustive match, unused variable, shadowed variable, etc.

Silent (completely ignored): full SMT proof discharge,
termination proof checking, trust propagation/enforcement, proof
stability tracking, spec validation, fuel/ifuel SMT tuning.

Compiler summary at end of compilation lists warning counts per
category.

### §22.2 The Bytecode VM

Sketch compiles to bytecode: parse, infer, emit, run. Stack-
based, simple. Startup < 100ms for files < 10K lines. `.fxb`
cached — content-hash unchanged means < 10ms reload. VM loads
native-compiled modules as shared objects. Three modes: `--sketch`
default (bytecode for user code, native for stdlib), `--trace-
module` (force module to bytecode for trace visibility),
`--full-vm` (every module interpreted, slower but no blind
spots).

### §22.3 Record and Replay

VM records every step. `.fxr` file. Stores: effect log (every IO
op and result — pure native calls re-executed, effectful replayed
from log), snapshot index (periodic full VM state with offset/
line), instruction trace. Resume at arbitrary point: load nearest
earlier snapshot, replay forward.

### §22.4 Mid-Program Interactivity

`inspect;` pauses execution, drops into REPL. Agent equivalent:
`checkpoint(f"epoch_{epoch}.fxr");`. Agent loads with `fxc
replay epoch_40.fxr --eval "expression"`.

### §22.5 Traces

Reconstructor reads `.fxr` and produces readable listing with
types and all 21 dimensions shown. Verbosity: `--values`,
default (types+values), `--full` (all 19 dims), `--show
mode,security`.

### §22.6 Concurrent Traces

`.fxt` binary: timestamped events tagged with thread/task ID and
Lamport clock. 64-byte event record with timestamp, thread_id,
event_type (instruction/spawn/join/send/recv/lock/fence/atomic/
inspect/checkpoint/crash), source_line, pc, data. Rendering
views: per-thread timeline, multi-column interleaving, sync
points, shared state accesses, coroutine suspend/resume, data
races, lock cycles, aggregate stats.

### §22.7 Hot Reload

REPL / inspect breakpoint: edit source, `:reload` recompiles
changed functions, patches VM function table. Data stays in
memory. If reloaded function's type conflicts with live values,
VM warns and offers to discard affected bindings.

### §22.8 The Gradient

sketch (infer all, runtime checks, mutable default, bytecode,
100ms startup) → normal (annotated signatures, compile-time
checks, immutable default, native, seconds compile) →
aggressive (annotated refinements, compile-time proofs, tight
specs, native+superopt, minutes compile). Transition via `fxc
annotate --apply`.

---

## §23. Testing

Six built-in test constructs. Language keywords, not library
macros.

### §23.1 Unit Tests

`test name ... end test;`. Effects declared: `test name with IO,
DB`. Assertions: `assert expr;`, `assert_err expr is Variant;`,
`assert_raises ExnType { body };`, `assert_within(tolerance) a
b;`.

### §23.2 Property-Based Tests

`property sort_preserves_length(xs: list(nat)) = length(sort(xs))
== length(xs);`. Compiler generates random inputs, runs property,
shrinks failing cases. Configurable `@[samples(10000)]`,
`@[max_size(1000)]`. Custom generators via `instance Arbitrary
for T`.

### §23.3 Machine Tests

`test_machine ConnectionState end test_machine;`. Compiler
explores all reachable states, tests all transitions, verifies
invariants, checks deadlock freedom. `@[depth_range(1, 16)]`
for parameterized. `@[bound(100)]` + `@[induction]` for infinite-
state.

### §23.4 Contract Tests

`test_contract UserApi format json end test_contract;`. Tests
round-trip, version migration, invalid input (typed errors not
crashes), access rules. Multi-format, version matrix.

### §23.5 Benchmarks

`bench name ... end bench;`. With `@[compare]` multiple cases
tested side-by-side. Output: median/p95/p99, allocations,
throughput. `fxc test --bench --save-baseline` then `--compare-
baseline`.

### §23.6 Type Theory Tests

Smoke tests for type system. Every known type theory bug from
literature becomes permanent test. `test_theory`/`test_metatheory`.
Property-based metatheory fuzzing generates random well-typed
terms, checks preservation/progress, shrinks counterexamples.
Single corpus regression blocks all releases.

### §23.7 Running Tests

`fxc test [--unit|--property|--machine|--bench|--theory|
pattern|--jobs N|--format json]`. Tests stripped from release
builds.

---

## §24. Compiler Agent Protocol

FX compiler runs as persistent HTTP daemon. Agents interact via
REST — no text parsing, no cold startup per invocation.

### §24.1 REST Daemon

`fxc serve --port 9100`. Loads project once, keeps elaborated
state in memory, watches files, serves queries with warm
incremental checking. Cold startup 2-5 seconds; warm recheck
after one-line edit 50-200ms. Root `GET /` self-describes all
endpoints.

### §24.2 Discovery

`GET /symbol/Auth.login` returns signature, effects, pre/post,
trust, called_by, calls. `GET /search?name=sort` returns
candidates. `GET /search?goal=is_sorted(append(_, _))` lemma
search.

### §24.3 The Check/Fix Cycle

`POST /check { "scope": "src/Auth.fx" }` returns phase statuses
(parse, names, types, modes, effects, verify). Errors reported
by phase; later phases blocked until earlier clean. Agent
processes one phase at a time. `POST /check/c_001/auto-fix`,
`GET /check/c_002/errors?root=true`, `POST /what-if`, `POST
/edit`.

### §24.4 Suggestions

`GET /check/{id}/suggestions` — effect_narrowing, pipeline_sugar,
stronger_spec, parallel_opportunity. Categories: ownership/mode,
specification, sugar/style, effects, types/contracts,
performance, security.

### §24.5 Refactoring

`POST /rename`, `POST /extract-fn`, `POST /inline`. Returns
preview edits; agent reviews and applies.

### §24.6 Analysis

`GET /health`, `GET /impact?symbol=`, `GET /dead-code`, `GET
/dependency-graph`, `GET /coverage?kind=spec`.

### §24.7 Proof Assistance

`GET /proof-state?file=...&fn=...&line=` returns known facts,
goal, suggestion. `POST /proof-plan` returns obligations,
strategies, skeleton.

### §24.8 Iterative Session Example

Typical agent flow: orient (GET /), check (POST /check),
auto-fix, get errors with fix diffs, what-if preview, apply,
suggestions, apply, verify impact, check health — 12 calls from
"I know nothing" to "feature complete, verified,
contract-compatible".

### §24.9 CLI Fallback

`fxc check --agent Auth.fx` outputs structured phase/error/fix
lines.

### §24.10 Daemon Lifecycle

Watches files via OS notifications. Incremental background
rechecks. Read-only queries concurrent. Mutations serialized per
file. Multiple agents share warm state. Check IDs are snapshots;
file changes invalidate. `fxc serve` can expose both REST and
LSP on different ports.

---

## §25. Distribution

### §25.1 Package Identity

`namespace/name`. Namespaces verified (email domain, GitHub org,
DNS record). `std/` reserved. Manifest `package.fx.toml`. No
build scripts. No pre/post install hooks. Code generation is
`comptime` in sandbox — no IO, no network.

### §25.2 Version Resolution

`fx.lock` committed — exact versions, content hashes, trust
levels, effect summaries. Minimal Version Selection: collect min
constraints, pick max of all mins. Deterministic, O(n), no SAT.
Plus contract compatibility check.

### §25.3 Security

Three concerns separated: discovery (registry index, replicated),
storage (content-addressed SHA-256), trust (Ed25519 author
signatures + append-only transparency log). Published packages
immutable. Yanked versions remain downloadable by hash. Version
timeline append-only.

### §25.4 Automatic Version Computation

Compiler computes semver from contract diff (§14.10). Author
confirms. Overstating allowed, understating blocked. Auto-
generated changelog and migration guide for MAJOR bumps.

### §25.5 Supply Chain Defenses

No build scripts (xz attack vector doesn't exist). Effect
transparency (secret new IO/Network change contract, semver
catches). Classified-by-default (exfiltrating env vars requires
visible `declassify`). No raw pointer access (no runtime patching
of function pointers). `fxc diff-audit old.lock new.lock` warns
on new effects.

### §25.6 Project Profiles

Profiles RESTRICT language, never extend. `[profile] name =
"embedded_driver" allowed_effects = [...] alloc =
"stack_and_region" max_stack_per_function = 4096
overflow_default = "trap" sorry = "error"`. Module cannot opt
out. Module-level pragmas can only tighten.

### §25.7 The No-Dialect Rule

FX does NOT support syntax extensions, custom operators, custom
keywords, `#lang` directives, compiler plugins that change
parsing/typechecking, implicit conversions, template
metaprogramming. Code generation uses `comptime` in sandbox.
Type-level abstraction uses type classes and decorators.
Domain-specific needs use contracts, machines, existing 19-dim
type system. Hard rule: every `.fx` file parseable by any FX
tool without knowing project config. No dialect barrier.

---

## §26. Standard Library

### §26.1 Why a Large Standard Library

Avoids ecosystem fragmentation. FX can ship large stdlib because:
(1) contract-verified evolution (§14.10 gives semver diff per
change); (2) effect-driven tree shaking (program that doesn't
declare `Network` cannot import `std/http`, nothing from it
appears in binary); (3) profile-based restriction replaces
no_std (embedded profile transitively excludes heap-requiring
modules).

### §26.2 Module Catalog

Data formats (JSON, YAML, TOML, CSV, XML, MessagePack, Protobuf,
CBOR — contract-based API). Text (regex with verified bounds,
Unicode, Markdown, templating, diff/patch). Time (dates,
durations, timezones with IANA, formatting). Cryptography (SHA-2/
3, BLAKE3, ChaCha20-Poly1305, AES-GCM, Ed25519, X25519, RSA, TLS
1.3, X.509 — all verified, all constant-time). Networking
(HTTP/1.1/2, WebSocket, gRPC, DNS, QUIC, raw sockets). Database
clients (PostgreSQL, SQLite, Redis — compile-time schema
checking). Storage/compression (tar, zip, gzip, zstd, lz4,
brotli). Image codecs (PNG, JPEG, WebP, AVIF — verified decoders,
buffer overflows structurally impossible). Numerics (shape-typed
tensors, BLAS, FFT, statistics, RNG). Parsing (verified
combinator framework). System (fs, processes, threads, env, CLI
args, signals). Observability (structured logging, tracing,
metrics). Mathematics (Mathlib ported).

### §26.3 Behavior, Not Implementation

Most important rule. `map(K, V)` promises insert/lookup/delete/
iterate. Does NOT promise iterator stability, node-based
storage, specific layout. Compiler picks implementation:
`map(nat { <256 }, Config)` → direct array; `map(string, Record)
with 12 entries` → flat sorted array; `map(string, Record) with
1M entries` → Swiss Table. User writes `map` all three cases.
Allocator is NOT in the type — `list(int)` is `list(int)`
regardless of allocator. Two functions taking `list(int)`
interoperate without template parameterization. If user needs
iterator stability, `stable_map(K, V)` makes trade-off explicit.

---

## §27. Metatheory

### §27.1 The Corrected Lam Rule

FX uses Wood/Atkey 2022 with context division (§6.2). Broken
Atkey 2018 allows linear variable used multiple times inside
replicable closure. Corrected rule rejects `fn higher_order(f:
i64 -> i64) : i64 -> i64 = fn(x: i64) => f(f(x));` — `f` has
grade 1 and `1/w = 0`, not available in closure.

### §27.2 Known Unsoundness Corpus

Catalog of known type theory bugs. Every entry becomes permanent
`test_theory` case (§23.6). Grows, never shrinks. Grade/
linearity (Atkey 2018 Lam, session endpoint aliased, ML value
restriction). Dependent type (Type:Type / Girard's paradox).
Information flow (implicit flow via branch on secret, CT
violation via secret-dependent memory access). Concurrency
(fractional permission overallocation). Each cites source paper.
Corpus regression blocks all releases.

### §27.3 The Five-Layer Defense

Layer 1: known-witness smoke tests (every cataloged bug is
rejected test). Layer 2: property-based metatheory fuzzing
(preservation/progress on random well-typed terms, nightly).
Layer 3: cross-reference published mechanized proofs (every rule
cites machine-checked source in Coq/Agda/Lean/F*). Layer 4:
self-verified metatheory (preservation/progress stated as
theorems in FX, proved by induction, part of build). Layer 5:
formal review (every new rule needs provenance, positive test,
negative test, metatheory re-proof, fuzz run, corpus check).

---

## §28. Reference Implementations

Six implementations ship alongside compiler.

### §28.1 fx-chip

Verified RISC-V core (RV64GC). ISA is total function over
architectural state. Five-stage pipeline implements it.
Refinement proof (§18.12) connects. Target: boot Linux on FPGA
with every instruction commit formally proven.

### §28.2 fx-driver

Linux kernel drivers. Execution context hierarchy (§19.1)
prevents sleeping-in-interrupt. Linear DMA (§19.2) prevents
use-while-device-owns-buffer. Machine lifecycles (§19.3) auto-
generate cleanup. Initial: e1000 NIC, NVMe, XHCI USB.

### §28.3 fx-net

Verified TCP/IP stack, RFC 793/9293 compliant. Session types
for protocol states. Linear packet buffers for zero-copy.
Contracts for wire formats. Targets: UDP, TCP w/o congestion
control, then Cubic, TLS 1.3, HTTP.

### §28.4 fx-db

SQL database, SQLite → PostgreSQL scale. Machines for
transaction state with inverse chains for abort. Write-ahead log
as linear monotonic structure. Query plan correctness as
refinement proof. Enables intra-query parallelism: stages
accessing disjoint pages run concurrently, compiler proves no
conflict.

### §28.5 fx-image

Image loading/saving/filtering. Format declarations (§18.1) for
codec parsing — length fields with refinements bound every
buffer access. Buffer overflows, integer overflow in size
calcs, use-after-free structurally impossible. Targets: PNG,
JPEG, WebP, AVIF.

### §28.6 fx-numeric

Shape-typed tensors, BLAS bindings, autodiff via staging
(§17.2), GPU via `.gpu()` source type. Shape mismatches at
compile time. Target: inference for small LMs (Llama 7B) with
compile-time shape checking throughout.

---

## §29. Scaling Properties

### §29.1 Bounded Blast Radius

Well-typed edit that compiles cannot silently break anything
outside its public surface. Module M has same type errors after
upstream edit unless U changed public decls. Function f has
same proof obligations unless signature or call-graph signatures
changed. Previously-proved properties stay proved. Trust level
doesn't decrease unless `sorry`/`axiom`/weaker effect introduced.

### §29.2 Why This Holds

Modular checking. Explicit API stability via contracts.
Complete compiler feedback (location + context + fix diff).
Proof composition (A uses B's postcondition without re-proving
internals). No silent state (every effect declared, every
allocation tracked, every mutation visible).

### §29.3 Where This Breaks Down

Specification gaps (wrong `post`). Proofs needing insight (clever
lemma Z3 won't find). Performance not caught unless complexity
declared. Changing requirements (real cost no type system
reduces).

### §29.4 Measuring It

Tokens per verified function (agent session, count tokens
used, count `pub fn` with trust `Verified`, take ratio —
should decrease over time). Regression rate (how often an edit
causes previously-verified function to need re-verification —
near zero for private changes, limited for public).

---

## §30. Domain Archetypes

Each reference implementation has characteristic layout.

### §30.1 Hardware

Three modules: ISA spec (pure function), RTL (hardware modules),
refinement proof. Example RV64 cpu with `module MyCpu.Isa`
(arch_state, format R, fn step), `module MyCpu.Rtl` (pipeline
core stage fetch/decode/execute/writeback with forwarding and
stall), `refinement core_refines_isa` connecting.

### §30.2 Driver (see §19)

### §30.3 Network (see §28.3)

### §30.4 Database (see §28.4)

### §30.5 Tensor Computation (see §28.6)

---

## Appendices

### Appendix A: Complete Keyword List

92 global keywords listed in §2.3 (fx_design.md Appendix A
explicitly states "Total: 92 global keywords"). All are common
English words that tokenize as single BPE tokens in modern LMs.
Plus contextual keywords meaningful only inside specific blocks
(machine, register_file, contract, hardware, register, effect,
class, test). Typed closers: `end fn`, `end match`, `end type`,
`end if`, `end for`, `end while`, `end effect`, `end handle`,
`end session`, `end codata`, `end select`, `end decorator`,
`end structure`, `end hardware`, `end pipeline`, `end stage`,
`end asm`, `end register`, `end register_file`, `end format`,
`end contract`, `end impl`, `end test`, `end bench`,
`end test_theory`, `end test_metatheory`, `end module type`,
`end module functor`, `end extern`, bare `end` (lambda/begin).

### Appendix B: Effect Algebra

Per fx_design.md Appendix B: effects form a bounded
join-semilattice `(Effects, \/, Tot)`. Laws: `Tot \/ e = e`
(identity), `e \/ e = e` (idempotent), `e1 \/ e2 = e2 \/ e1`
(commutative), `(e1 \/ e2) \/ e3 = e1 \/ (e2 \/ e3)`
(associative). Only declared subeffect: `Read <= Write`. The
remaining built-ins (`Tot`, `Div`, `Ghost`, `Exn`, `IO`, `Alloc`,
`Read`, `Write`, `Async`) are lattice elements without a total
order — do NOT assume a chain. Subtyping: `e1 <= e2` iff
`e1 \/ e2 = e2`. Typing rules (E-Pure, E-Sub, E-Seq, E-App,
E-Handle) in fx_design.md Appendix B.

### Appendix C: Mode Semiring

Usage dimension `{0, 1, w}` with addition and multiplication
tables (§6.1). Maps to surface: `ghost`=0, `own`/(default)=1,
`@[copy]`=w, `ref`=w (shared), `ref mut`=1 (exclusive), `affine`=
grade <= 1.

### Appendix D: Differences from F*

FX is derived from F* but diverges on: (1) no juxtaposition
application — mandatory parens and named args; (2) semicolon
terminators on all statements and declarations; (3) typed
closers `end fn` / `end match` / `end type`; (4) no `!` / `&&` /
`||` — use `not` / `and` / `or` keywords; (5) dot-shorthand
`.field` with shared implicit parameter; (6) ownership modes
prefix on parameters, implicit at call sites; (7) integrated
state machines, contracts, hardware, sessions at the language
level rather than encoded in attributes and libraries; (8) 19
type dimensions vs F*'s ~5 (types, refinement, effects, ghost,
termination); (9) no `unsafe` keyword — no type-system bypass;
(10) sketch mode with bytecode VM for rapid prototyping; (11)
agent-first design — REST daemon, structured diagnostics, fix
diffs.

---

## Gaps Reference

See `/root/iprit/FX/gaps.json` for 156 tracked design gaps with
filled `prior_art` comparisons. Each gap has id, name,
description, prior_art (state-of-the-art comparison), resolution
(empty if unresolved), docs_adjusted flag. First 114 committed
as 46e2e566; #115–156 added in incremental commits (lifetime
syntax, Nb bit-literal prefix, keyword polysemy risks,
foundational/semantic/practical gaps).

## Design Analysis Reference

See `/root/iprit/FX/design_analysis.json` for per-section
critical analysis (283 entries × 8 fields: what_fx_does,
closest_prior_art, where_fx_is_better, where_fx_is_worse,
what_fx_is_missing, could_we_do_better, verdict, confidence).
Fill in progress via the agent template at `/tmp/da_template.md`.
Verdict scale: frontier / strong / adequate / weak / missing /
novel. Confidence: high / medium / low.

## Working Rules

No background agents, no worktrees. Commit regularly with
atomic semantically-unified commits. Use `rg`/`fd`/`ast-grep`/
`fzf`/`jq`/`yq`. No `sed`/`awk` — manual edits. Never `git
checkout` or `git reset` without asking. Never `--no-verify`.
Always read full files when requested (no summarization without
consent).
