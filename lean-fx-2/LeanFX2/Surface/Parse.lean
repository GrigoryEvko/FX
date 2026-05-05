/-! # Surface/Parse — token stream → AST

```lean
def Parse.run (tokens : Array Token) : Except ParseError SurfaceModule
```

Recursive-descent parser per `fx_grammar.md` (LALR(1)-compatible
grammar but recursive-descent is the implementation).

## Algorithm

Standard recursive-descent with operator precedence climbing for
binary expressions.  Each grammar production has a corresponding
`parseX` function.

## Error recovery

On parse error:
* Skip to next `;` or matching closer
* Emit diagnostic with position + expected-token list
* Continue parsing — collect all errors in one pass
* Only abandon when nesting structure breaks irrecoverably

## EOF safety

Per memory `project_parser_eof_trap.md`: every recursive-descent loop
must check EOF before recursing into a sub-parser that does
error-recovery-without-advance.  Otherwise infinite loop / OOM.
**Use `TokenStream.peekRequireNotEof` at every loop iteration**.

## Operator precedence

| Precedence | Operators |
|---|---|
| 1 (lowest) | `or` |
| 2 | `and` |
| 3 | `not` (prefix) |
| 4 | `==`, `!=` |
| 5 | `<`, `>`, `<=`, `>=`, `is` |
| 6 | `..`, `..=` (range) |
| 7 | `\|`, `^` (bit-or, bit-xor) |
| 8 | `&` (bit-and) |
| 9 | `<<`, `>>` (shifts) |
| 10 | `+`, `-` |
| 11 | `*`, `/`, `%` |
| 12 | `**` (power, right-assoc) |
| 13 (highest) | function call, dot access, type app |

## Dependencies

* `Surface/AST.lean`

## Downstream

* `Surface/Roundtrip.lean` — parse/print roundtrip
* `Surface/Elab.lean` — elaborates parse output
* `Pipeline.lean`

## Implementation plan (Layer 10)

1. Define `ParseError` enum + position
2. `TokenStream` helper struct with peek/advance/require
3. `parseExpr` precedence climbing
4. `parseDecl`, `parsePattern`, etc.
5. `Parse.run` driver
6. EOF safety: every loop guards against EOF (memory `project_parser_eof_trap`)

Target: ~1200 lines.
-/

namespace LeanFX2.Surface

-- TODO Layer 10: TokenStream + Parse.run

end LeanFX2.Surface
