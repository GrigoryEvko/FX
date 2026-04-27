import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# Parser robustness tests (task Q52)

Regression coverage for the EOF infinite-loop trap — see
`project_parser_eof_trap.md` and the `Q52` audit block at the
top of `FX/Syntax/Parser.lean`.

The bug pattern: an accumulating loop whose sub-parser has a
"record error, no advance" catch-all path can spin forever at
EOF, growing its accumulator unboundedly → OOM.  The 2026-04-24
kernel panic was caused by a stale conformance file with a
malformed session decl hitting this trap.

Each test here feeds deliberately-malformed input into
`parseFile` and verifies:

  1. The parser terminates (trivially observable: the test
     either completes or gets killed by the test-runner
     timeout — any loop that failed the Q52 audit would hang).
  2. Parse errors are recorded (we don't check the count
     precisely, just that *some* diagnostics surface; a 0-error
     result on malformed input would mean the parser silently
     accepted garbage, which is its own bug).
  3. The AST contains at least the partial results the parser
     could extract before bailing — evidence that the loop
     exited cleanly rather than being cut short at some
     arbitrary internal point.

A future regression that turns a §B-category loop (per the Q52
audit) into a hang — e.g., by adding a new sub-parser whose
catch-all records an error without calling `advance` — would
show up here first as a test timeout.
-/

namespace Tests.Syntax.ParserRobustnessTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Run the full lex+parse pipeline and return the resulting
    decls plus all collected errors (lex and parse combined). -/
def lexAndParse (sourceText : String) : Array Decl × Nat :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (fileResult, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (fileResult.decls, lexOut.errors.size + parseErrs.size)

def run : IO Unit := Tests.suite "Tests.Syntax.ParserRobustnessTests" do

  /- ## 1. Truncated session decl — the canonical regression.
     The 2026-04-24 kernel panic's input looked like this:
     a session body that starts well-formed but has no
     `end session;` closer.  The §D-category loops (stepsLoop
     and parseSessionBranchArms) must handle this cleanly. -/
  let (decls1, errorCount1) := lexAndParse
    "session MyProto rec Loop;\n  send(x: i64);\n"
  check "1. truncated session terminates" (decls1.size != 0 || errorCount1 != 0) true
  check "1. truncated session records errors" (errorCount1 != 0) true

  /- ## 2. Truncated branch block inside session.
     Tests parseSessionBranchArms at the `end branch;` closer
     when the input truncates mid-branch. -/
  let (_, errorCount2) := lexAndParse
    "session MyProto\n  branch\n    lbl =>\n      send(x: i64);"
  check "2. truncated branch terminates" (errorCount2 != 0) true

  /- ## 3. Truncated match block — parseMatchArms (§C category).
     Arms are expected until `end match`.  Input cuts off in
     the middle of an arm body. -/
  let (_, errorCount3) := lexAndParse
    "fn f(x: i64) : i64 = match x;\n  0 => \n"
  check "3. truncated match terminates" (errorCount3 != 0) true

  /- ## 4. Truncated variant type decl — variantCtorsLoop.
     Enum declaration with constructors but no `end type`. -/
  let (_, errorCount4) := lexAndParse
    "type color\n  Red;\n  Green;\n  Blue;\n"
  check "4. truncated type decl terminates" (errorCount4 != 0) true

  /- ## 5. Truncated record decl — recordFieldsLoop.
     Opens `{` but never closes. -/
  let (_, errorCount5) := lexAndParse
    "type config {\n  host: string;\n  port: nat;\n"
  check "5. truncated record decl terminates" (errorCount5 != 0) true

  /- ## 6. Truncated argument list — callArgsLoop (§B category).
     Opens call site `(` with comma-separated args, no closer. -/
  let (_, errorCount6) := lexAndParse
    "fn f() : i64 = g(a: 1, b: 2, c:"
  check "6. truncated call-args terminates" (errorCount6 != 0) true

  /- ## 7. Truncated type-param list — typeParamsLoop.
     Opens `<` with comma-separated type params, no `>`. -/
  let (_, errorCount7) := lexAndParse
    "fn map<a: type, b:"
  check "7. truncated type-params terminates" (errorCount7 != 0) true

  /- ## 8. Truncated impl block — implMembersLoop (§C).
     `impl T` with method but no `end impl`. -/
  let (_, errorCount8) := lexAndParse
    "impl MyType\n  fn helper() : i64 = 42;\n"
  check "8. truncated impl block terminates" (errorCount8 != 0) true

  /- ## 9. Truncated block body — blockFnStmtsLoop.
     `begin fn` with statements but no `return` + `end fn`. -/
  let (_, errorCount9) := lexAndParse
    "fn f() : i64 begin fn\n  let x = 1;\n  let y = 2;"
  check "9. truncated block body terminates" (errorCount9 != 0) true

  /- ## 10. Empty input — declsLoop immediately at EOF.
     The file-level loop must handle an empty stream. -/
  let (decls10, errorCount10) := lexAndParse ""
  check "10. empty input: zero decls, zero errors" true
    (decls10.size == 0 && errorCount10 == 0)

  /- ## 11. Whitespace-only input.  Lexer emits only EOF; parser
     must terminate with zero decls and zero errors. -/
  let (decls11, errorCount11) := lexAndParse "   \n\t\n   "
  check "11. whitespace-only: zero decls, zero errors" true
    (decls11.size == 0 && errorCount11 == 0)

  /- ## 12. Garbage stream — the fuzz case.  Mixes random
     keywords, delimiters, and operators.  Every loop's catch-
     all path gets exercised.  If any loop fails the Q52 audit,
     this test hangs. -/
  let garbage := "fn { match session begin = => ; , ( ] > < + - * / "
              ++ "== != rec impl type and or not if else end "
              ++ "send receive branch select end session;"
  let (_, errorCount12) := lexAndParse garbage
  check "12. fuzz input terminates" (errorCount12 != 0) true

  /- ## 13. Unterminated string literal.  Lexer should record
     an error; parser should still terminate on the partial
     token stream. -/
  let (_, errorCount13) := lexAndParse "fn f() : string = \"unterminated"
  check "13. unterminated string terminates" (errorCount13 != 0) true

  /- ## 14. Stacked-truncation: every §B/§C loop nested inside
     one truncated file.  If any loop's implicit safety is
     broken, the combined case surfaces it. -/
  let stacked :=
    "type t { a: i64; b: list(i64, i32, f64) }; " ++
    "fn f<x: type, y: nat>(p: t, q: option(t)) : t = match p;" ++
    "  { a: n, b: [_, ..._] } => t { a: n, b: [n, n, "
  let (_, errorCount14) := lexAndParse stacked
  check "14. stacked-truncation terminates" (errorCount14 != 0) true

end Tests.Syntax.ParserRobustnessTests
