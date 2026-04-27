# Error Code Registry

Canonical reference for every diagnostic code emitted by the FX
interpreter.  Each code has exactly one meaning across the
codebase; tooling, tests, and documentation should use the same
string.

Upstream spec: `fx_design.md` §10.10 taxonomy.

## Prefix conventions

| Prefix | Subsystem | Source |
|---|---|---|
| `L` | Lexer | `FX/Syntax/Lexer.lean` |
| `P` | Parser | `FX/Syntax/Parser.lean` |
| `T` | Type checker (kernel) | `FX/Kernel/Typing.lean` |
| `E` | Elaborator | `FX/Elab/Elaborate.lean` |
| `M` | Mode / ownership (graded) | `FX/Kernel/Typing.lean` (planned, A9) |
| `R` | Refinement (SMT) | planned (E4) |
| `S` | Session types | planned |
| `I` | Information flow | planned |
| `N` | Numeric precision | planned |
| `CT` | Constant-time violations | planned |
| `W` | Warnings | various |

## Currently emitted — Phase 2.2

### Lexer (`L`)

| Code | Meaning |
|---|---|
| `L001` | Invalid UTF-8 byte sequence |
| `L002` | Unterminated string literal |
| `L003` | Unterminated block comment |
| `L004` | Unterminated backtick identifier |
| `L006` | Invalid escape sequence |
| `L007` | Invalid underscore in number literal |
| `L008` | Malformed number (digits missing after prefix/suffix) |
| `L010` | Invalid character in source |
| `L011` | Invalid ternary digit |
| `L012` | Invalid integer suffix |
| `L099` | Internal lexer error (should not happen) |

### Parser (`P`)

| Code | Meaning |
|---|---|
| `P001` | `expect`/`expectKw` — required token not found |
| `P002` | `expectIdent`/`expectUIdent` — identifier expected |
| `P003` | Qualified identifier malformed (`Module.` not followed by ident) |
| `P005` | `const` declaration name missing or non-identifier |
| `P010` | `parseAtom` — non-expression-starting token |
| `P020` | `parseLamParam` — unsupported lambda-parameter form |
| `P030` | `parsePattern` — non-pattern-starting token |
| `P035` | Type-parameter list separator — expected `,` or `>` |
| `P036` | Type-parameter kind — expected `type` or identifier |
| `P040` | `parseFnBody` — neither `=` nor `begin fn` |
| `P100` | `parseDecl` — token that starts no declaration |

### Kernel type checker (`T`)

| Code | Meaning |
|---|---|
| `T001` | Expected a type, got something else (not-a-type) |
| `T002` | Type mismatch (check failed — inferred ≠ expected up to conversion) |
| `T003` | Expected function type, got something else (App on non-function) |
| `T004` | De Bruijn index out of range (free variable in malformed term) |
| `T050` | Chained comparison (`a < b < c`) — `fx_grammar.md` §3 |
| `T100` | Coinductive not yet supported (Phase 2.2 stub) |
| `T110` | Unknown inductive type (no IndSpec registered for name) |
| `T111` | Inductive arg count mismatch |
| `T112` | Constructor index out of range for the inductive |
| `T113` | Constructor arg count mismatch |
| `T114` | Recursor's method count doesn't match spec.ctorCount |
| `T115` | Eliminator target has wrong inductive type |
| `T120` | Unknown global declaration (Term.const name not in GlobalEnv) |

### Elaborator (`E`)

| Code | Meaning |
|---|---|
| `E001` | Unknown identifier (neither local, global, nor prelude) |
| `E010` | Unsupported expression form for current phase |
| `E020` | Unsupported declaration form for current phase |
| (reserved) `E030` | Block-form function body not yet handled (legacy — now handled) |
| (reserved) `E100` | Internal: impossible branch reached |

### Warnings (`W`)

| Code | Meaning |
|---|---|
| `W001` | Unstable proof (fuel within 80% of budget — `fx_design.md` §10.12) |

## Reserved — Phase 3+ (not yet emitted)

### Mode / ownership (`M`)

| Code | Planned meaning |
|---|---|
| `M001` | Linear value consumed twice (double-use) |
| `M002` | Linear value not consumed at scope exit |
| `M003` | Missing required grade annotation |
| `M011` | Linear value may leak on Fail/Exn path (linear-cleanup rule) |
| `M012` | Monotonic update in concurrent context without atomic / lock_free |
| `M013` | `ref mut self` method must not return `ref mut Self` |

### Refinement / verification (`R`)

| Code | Planned meaning |
|---|---|
| `R001` | Precondition not satisfied |
| `R002` | `pre` / `post` reference later parameter (scope error) |
| `R003` | `old(expr)` outside two-state context |
| `R004` | Verify `exports` item is not a proposition |
| `R005` | Literal violates type refinement |
| `R006` | Reachable `unreachable` |
| `R_fuel` | Reduction exceeded fuel during conversion |

### Effects (`E` — shared prefix, distinct code space)

| Code | Planned meaning |
|---|---|
| `E042` | Missing control-flow marker (`try` on Fail/Exn call) |
| `E043` | Missing effect argument at call site (effect-polymorphic fn) |
| `E044` | CT × Async incompatible (`fx_design.md` §6.8) |
| `E045` | Redundant Fail effects — combine into single Fail with union error type |
| `E046` | Effect does not satisfy expected — no subsumption edge declared |

### Information flow (`I`)

| Code | Planned meaning |
|---|---|
| `I002` | Classified × Fail — Fail payload carries classified data |
| `I003` | CT × Fail on secret — `fail` on secret-dependent condition |
| `I004` | Classified × async × session leak risk |

### Lifetime (`L` — distinct from lexer `L`; name-spaced by context)

| Code | Planned meaning |
|---|---|
| `L001` (context-dependent) | Missing lifetime annotation |
| `L002` | Borrow does not live long enough across suspension (borrow × Async) |
| `L003` | Unscoped `spawn` cannot capture borrow |

### Numeric / precision (`N`)

| Code | Planned meaning |
|---|---|
| `N001` | Unbounded `int` / `nat` — arbitrary-precision runtime cost |
| `N002` | Decimal × `overflow(wrap)` — use trap/saturate/widen |

### Constant-time (`CT`)

| Code | Planned meaning |
|---|---|
| `CT001` | Branch on secret-graded value |

### Session types (`S`)

Per `fx_design.md` §11.27 — the canonical S-code taxonomy.
Codes currently emitted by the elaborator are marked **L**
(live); the rest are reserved for future session-type work
(§11 frontier items, session runtime, subtyping, etc.).

| Code | Status | Meaning |
|---|---|---|
| `S001` | **L** | Session type ill-formed: unguarded `continueS` (outside any enclosing `loopS`) |
| `S002` | **L** | Duplicate label in `select` / `offer` / `branch` |
| `S003` | reserved | Channel declared without capacity (required for balanced+ async, §11.15) |
| `S004` | reserved | Dual mismatch — channel endpoints are not dual types |
| `S005` | reserved | Channel used after protocol complete (End state) |
| `S006` | reserved | Channel used in wrong protocol state |
| `S007` | reserved | Projection branches do not merge — plain merging failed; use `@[merge(full)]` or restructure (§11.16) |
| `S008` | reserved | Global type ill-formed (unguarded recursion variable) |
| `S009` | reserved | `Offer` from unreliable peer missing `Crash<Peer>` branch (§11.21) |
| `S010` | reserved | `Stop` from unreliable peer ill-formed — `Stop ⩽ T` always, so it carries no information |
| `S011` | reserved | Queue capacity exceeded — session would violate balanced+ (§11.15) |
| `S012` | reserved | Session type with no valid projection for some role (§11.16) |
| `S013` | reserved | Association check failed — Δ is not a subtype of G's projection (§11.17) |
| `S014` | reserved | Session composition incompatible — disjointness violated (§11.22) |
| `S015` | reserved | Session type T is not a subtype of T' (sync Gay-Hole subtyping §11.19) |
| `S016` | reserved | Session subtyping sides have different participant sets |
| `S017` | reserved | Precise-async subtype undecidable within depth D — widen `@[subtype_depth(N)]` or restructure (§11.20) |
| `S018` | reserved | Delegation violates linearity — sender loses endpoint, receiver gains; check Usage grade (§11.23) |
| `S019` | reserved | Higher-order carrier unreliable — cannot verify inner session (§11.23) |
| `S020` | reserved | Timed session budget exceeded along some path (§11.26.4) |
| `S021` | reserved | Content-addressed send: payload not `@[copy]` + content-hashable (§11.26.5) |

**S001 vs S002 split (S24).**  The elaborator uses
`FX.Derived.Session.wellFormedReason` (Binary.lean) to
distinguish the two well-formedness failure modes.  A
boolean-only `wellFormed` check would collapse both into one
code; the reason-returning variant is what lets us emit the
specific code the §11.27 taxonomy prescribes.  Consumers
reading the diagnostic message see the failing spec name plus
which invariant broke.

## Test coverage audit

Snapshot of rejection-test coverage per code.  "Covered" means
a test asserts the specific code string via `elabErrCode` /
`matches` / similar; "recovery only" means the recovery-test
fires but doesn't pin the code.  Updated alongside test edits.

### Covered

| Code | Test file |
|---|---|
| `L001`–`L012`, `L099` | `Tests/Syntax/LexerTests.lean` |
| `T050` | `Tests/Syntax/ParserTests.lean` |
| `E001` | `Tests/Elab/{Elaborate,Prelude}Tests.lean` |
| `E010` | `Tests/Elab/{Elaborate,Prelude,IfExpr,MatchExpr}Tests.lean` |
| `E020` | `Tests/Elab/ElaborateTests.lean` |
| `M001` | `Tests/Metatheory/UnsoundnessCorpusTests.lean` |

### Recovery only (code not pinned)

| Code | Note |
|---|---|
| `P100` | Tested via `recovery: *` in ParserTests; error count bounded (Q35) but code not asserted. |
| `P040` | Same — `recovery: malformed fn body` checks recovery, not code. |

### Not tested

| Code | Emission site | Gap |
|---|---|---|
| `P001` | `expect`/`expectKw` | generic delimiter-expected errors |
| `P002` | `expectIdent`/`expectUIdent` | identifier-expected |
| `P003` | `parseQualIdent` | `Module.` not followed by ident |
| `P005` | `parseConstDecl` | const name missing/non-ident |
| `P010` | `parseAtom` | non-expression-starting token |
| `P020` | `parseLamParam` | unsupported lambda-param |
| `P030` | `parsePattern` | non-pattern-starting token |
| `P035` | `parseOptionalTypeParams` | expected `,` or `>` in type-param list |
| `P036` | `parseTypeParamKind` | expected `type` or ident |
| `T001` | `inferType` | expected a type, got something else |
| `T002` | `check` | type mismatch |
| `T003` | `infer` on App | expected function type |
| `T004` | `infer` on var | de Bruijn index OOR |
| `T100` | `infer` on coind | coinductive not supported |
| `T110` | `infer` on ind/ctor/indRec | unknown inductive |
| `T111` | `infer` on ind/ctor | param-arg count mismatch |
| `T112` | `infer` on ctor | ctor index OOR |
| `T113` | `infer` on ctor | ctor-arg count mismatch |
| `T114` | `infer` on indRec | method count mismatch |
| `T115` | `infer` on indRec | target type mismatch |
| `T120` | `infer` on const | unknown global decl |
| `E100` | `elabExpr` literal catchall | internal bug (unreachable) |
| `W001` | elab warning path | unstable proof (not yet emitted) |

### Summary

  * 23 codes currently emitted by source.
  * 9 have dedicated rejection tests (L001–L012, L099, T050,
    E001, E010, E020, M001).
  * 2 have recovery-only coverage (P100, P040).
  * 14 kernel/parser codes lack dedicated rejection tests.
    The kernel codes are hardest to test surface-level because
    the elaborator's E010/E020 catches most ill-formed input
    before the kernel sees it; they become reachable once more
    surface forms are accepted.
  * `E100` is defensive — marked as internal-bug to signal that
    hitting it means an elaborator invariant broke, not a user
    input problem.  Not testable directly.

## Maintenance

When adding a new error code:

1. Update the relevant table above.
2. Use a docstring on the `throw` site naming the condition.
3. Add a rejection test verifying `elabErrCode` / equivalent
   returns the expected code string.
4. If the code replaces or supersedes an older one, mark the
   older one `(deprecated)` with the version it was dropped in.
5. Update the test-coverage audit in this file so the gap list
   stays accurate.

The registry is manually maintained — there is no automatic
scanner.  A `scripts/verify-error-codes.sh` that greps the
source and diffs against this file would be a good Q-ish
follow-up.
