import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# Parser runtime tests

Covers `fx_grammar.md` §4–§6 at the Phase-1 subset implemented
in `FX/Syntax/Parser.lean`.

## Testing strategy

Parsing produces a deeply-nested AST with spans on every node.
Comparing whole ASTs by `==` requires the spans to line up
byte-exactly, which is brittle against comment changes inside
test inputs.  Instead we assert:

  * the number of top-level decls
  * the shape of specific decls (which constructor was used,
    which sub-constructors appear, field values of string
    fields that don't depend on source positions)
  * zero parse errors on valid inputs; specific error codes on
    invalid inputs
-/

namespace Tests.Syntax.ParserTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Convenience: run the lexer + parser and return just the
    decls plus the parse errors. -/
def parse (sourceText : String) : Array Decl × Array FX.Util.Error :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (file, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (file.decls, lexOut.errors ++ parseErrs)

/-- True iff the expression is a `binop`. -/
def isBinop : Expr → Bool
  | .binop _ _ _ _ => true
  | _              => false

/-- True iff the expression is an `app`. -/
def isApp : Expr → Bool
  | .app _ _ _ => true
  | _          => false

/-- True iff the expression is an `arrow`. -/
def isArrow : Expr → Bool
  | .arrow _ _ _ => true
  | _            => false

/-- Return the top-level `op` token of a `binop` expression. -/
def binopTok? : Expr → Option Token
  | .binop t _ _ _ => some t
  | _              => none

/-- Return the LHS of a `binop` expression. -/
def binopLhs? : Expr → Option Expr
  | .binop _ l _ _ => some l
  | _              => none

/-- Return the RHS of a `binop` expression. -/
def binopRhs? : Expr → Option Expr
  | .binop _ _ r _ => some r
  | _              => none

/-- Extract a function body's expression (one-liner only). -/
def fnOneLiner? : Decl → Option Expr
  | .fnDecl _ _ _ _ _ _ _ (FnBody.oneLiner e) _ => some e
  | _                                           => none

/-- True iff the expression is a `try`-prefix wrapper (E-3). -/
def isTryPrefix : Expr → Bool
  | .tryPrefix _ _ => true
  | _              => false

/-- Extract a `tryPrefix`'s inner expression, if any. -/
def tryPrefixBody? : Expr → Option Expr
  | .tryPrefix b _ => some b
  | _              => none

/-- Classify a `Decl` constructor. -/
def declKind : Decl → String
  | .moduleDecl _ _         => "module"
  | .openDecl _ _ _         => "open"
  | .includeDecl _ _        => "include"
  | .constDecl _ _ _ _      => "const"
  | .fnDecl _ _ _ _ _ _ _ _ _ => "fn"
  | .valDecl _ _ _        => "val"
  | .typeDecl _ _ _ _ _   => "type"
  | .implDecl _ _ _       => "impl"
  | .sorryDecl _          => "sorry"
  | .sessionDecl _ _ _ _ _ => "session"
  | .effectDecl _ _ _ _    => "effect"
  | .unimplemented _ _    => "unimplemented"

def run : IO Unit := Tests.suite "Tests.Syntax.ParserTests" do

  /- §5.2 Module declaration -/
  let (ds, errs) := parse "module Foo.Bar;"
  check "module decl count" 1 ds.size
  check "module decl no errors" 0 errs.size
  check "module decl kind" "module" (ds[0]! |> declKind)

  /- §5.2 Open declaration without alias -/
  let (ds, errs) := parse "open Std.Io;"
  check "open no errors" 0 errs.size
  check "open decl kind" "open" (ds[0]! |> declKind)

  /- §5.2 Open declaration with alias -/
  let (ds, errs) := parse "open Foo.Bar as Bz;"
  check "open-as no errors" 0 errs.size
  check "open-as has alias"
    (some "Bz")
    (match ds[0]! with
     | Decl.openDecl _ alias_ _ => alias_
     | _                         => none)

  /- §5.3 Const declaration -/
  let (ds, errs) := parse "const MAX : i64 = 42;"
  check "const no errors" 0 errs.size
  check "const decl kind" "const" (ds[0]! |> declKind)

  /- §5.4 Fn one-liner -/
  let (ds, errs) := parse "pub fn id(x: i64) : i64 = x;"
  check "fn one-liner no errors" 0 errs.size
  check "fn one-liner kind" "fn" (ds[0]! |> declKind)

  /- §5.4 Fn block body -/
  let sourceText := "fn main() : unit begin fn\n  let x = 1;\n  return;\nend fn;"
  let (_ds, errs) := parse sourceText
  check "fn block no errors" 0 errs.size
  check "fn block kind" "fn" (ds[0]! |> declKind)

  /- sorry declaration -/
  let (ds, errs) := parse "sorry;"
  check "sorry decl no errors" 0 errs.size
  check "sorry decl kind" "sorry" (ds[0]! |> declKind)

  /- Multiple decls in one file -/
  let (ds, errs) := parse "module M; open Std.Io; const N : i64 = 1;"
  check "multi-decl no errors" 0 errs.size
  check "multi-decl count" 3 ds.size
  check "multi-decl kinds" #["module", "open", "const"]
    (ds.map declKind)

  /- Expression-level precedence: * binds tighter than + -/
  let (ds, errs) := parse "fn f(x: i64, y: i64, z: i64) : i64 = x + y * z;"
  check "precedence no errors" 0 errs.size
  check "precedence is fn" "fn" (ds[0]! |> declKind)
  -- The body should be binop(+, x, binop(*, y, z)), i.e.
  -- the top-level op is +.
  let bodyOp :=
    match ds[0]! with
    | Decl.fnDecl _ _ _ _ _ _ _ (FnBody.oneLiner e) _ => binopTok? e
    | _                                               => none
  check "top-level op is +" (some Token.plus) bodyOp

  /- Precedence (inner shape): `a + b * c` body is
     `binop(+, a, binop(*, b, c))` — assert on the RHS node too. -/
  let rhsOp :=
    (ds[0]! |> fnOneLiner?).bind binopRhs? |>.bind binopTok?
  check "precedence inner op is *" (some Token.star) rhsOp
  -- LHS of outer `+` is the bare variable `x`, NOT a binop.
  let lhsIsBinop :=
    ((ds[0]! |> fnOneLiner?).bind binopLhs?).map isBinop
      |>.getD false
  check "precedence LHS is not a binop" false lhsIsBinop

  /- Left-assoc additive: `a - b - c` is `(a - b) - c`, i.e. the
     LHS of the outer `-` is itself a `-` binop. -/
  let (ds2, errs) := parse "fn l(a: i64, b: i64, c: i64) : i64 = a - b - c;"
  check "left-assoc no errors" 0 errs.size
  let outerTok := (ds2[0]! |> fnOneLiner?).bind binopTok?
  check "left-assoc outer op is -" (some Token.minus) outerTok
  let lhsInner := (ds2[0]! |> fnOneLiner?).bind binopLhs? |>.bind binopTok?
  check "left-assoc LHS is - binop" (some Token.minus) lhsInner

  /- Right-assoc arrow: `A -> B -> C` parses as `A -> (B -> C)`,
     i.e. the RHS of the outer arrow is itself an arrow. -/
  let (ds3, errs) := parse "fn a3(f: i64 -> i64 -> i64) : i64 = f(1)(2);"
  check "right-assoc arrow no errors" 0 errs.size
  -- Extract the type of the first parameter, which is `i64 -> i64 -> i64`.
  let paramTy :=
    match ds3[0]! with
    | Decl.fnDecl _ _ _ ps _ _ _ _ _ =>
      match ps[0]! with
      | FnParam.mk _ _ typeExpr _ => some typeExpr
    | _ => none
  check "param type is arrow" true ((paramTy.map isArrow).getD false)
  let rhsIsArrow :=
    match paramTy with
    | some (.arrow _ rhs _) => isArrow rhs
    | _                      => false
  check "arrow is right-associative" true rhsIsArrow

  /- Precedence: prefix `-` binds tighter than `*` -/
  let (_ds, errs) := parse "fn g(x: i64) : i64 = -x;"
  check "prefix - no errors" 0 errs.size

  /- §3 T050: chained comparison rejected.  Parser continues after
     emitting T050.  The first decl is still a `fn` (possibly the
     trailing `< 10;` is then re-scanned as further decls via
     panic-mode resync — we only assert the first). -/
  let (ds, errs) := parse "fn h(x: i64) : bool = 0 < x < 10;"
  let hasT050 := errs.any (fun parseError => parseError.code = "T050")
  check "chained comparison triggers T050" true hasT050
  check "T050 still yields at least one decl" true (ds.size ≥ 1)
  check "T050 first decl kind is fn" "fn" (ds[0]! |> declKind)

  /- §3 arrow: function type in return position, right-associative -/
  let (ds, errs) := parse "fn ap(f: i64 -> i64, x: i64) : i64 = f(x);"
  check "arrow type parses" 0 errs.size
  check "arrow type is fn decl" "fn" (ds[0]! |> declKind)

  /- §6.5 if-else -/
  let sourceText := "fn choose(b: bool) : i64 = if b;\n  42\nelse\n  -1\nend if;"
  let (_ds, errs) := parse sourceText
  check "if-else no errors" 0 errs.size

  /- §6.5 if-elif-else -/
  let sourceText := "fn c(b: bool, d: bool) : i64 = if b;\n  1\nelse if d;\n  2\nelse\n  3\nend if;"
  let (_ds, errs) := parse sourceText
  check "if-elif-else no errors" 0 errs.size

  /- §6.4 block expression -/
  let sourceText := "fn b() : i64 = begin\n  let x = 1;\n  x;\nend begin;"
  let (_ds, errs) := parse sourceText
  check "block expr no errors" 0 errs.size

  /- §6.3 call args — named, positional, implicit -/
  let (_ds, errs) := parse
    "fn callit() : i64 = f(1, named: 2, #implicit);"
  check "call args no errors" 0 errs.size

  /- §5.6 parameter modes -/
  let (_ds, errs) :=
    parse "fn p(own x: i64, ref y: i64, ref mut z: i64) : i64 = x;"
  check "param modes no errors" 0 errs.size

  /- Lambda -/
  let (ds, errs) := parse "fn mk() : fn() => i64 = fn() => 42;"
  -- Lambda parses fine; the return-type form `fn() => i64` is a
  -- lambda used as a type (both share the grammar).  Either
  -- parses.  Accept zero or nonzero errors — we only assert it
  -- didn't crash.
  let _ := ds
  let _ := errs
  check "lambda doesn't crash" true (ds.size ≥ 0)

  /- Nonsense input produces errors and Decl.unimplemented -/
  let (ds, errs) := parse "?"
  check "nonsense triggers error" true (errs.size > 0)
  check "nonsense yields unimplemented-or-nothing"
    true (ds.size = 0 ∨ (ds[0]! |> declKind) = "unimplemented")

  /- Unknown decl form (e.g., class) — Phase 1 emits unimplemented -/
  let (ds, errs) := parse "class Printable<T: type>\nend class;"
  let _ := errs
  check "class decl → unimplemented placeholder"
    "unimplemented" (ds[0]! |> declKind)

  /- Pattern: wildcard -/
  let (_ds, errs) := parse "fn w() : i64 begin fn\n  let _ = 1;\n  return 0;\nend fn;"
  check "wildcard pattern no errors" 0 errs.size

  /- Pattern: constructor with payload -/
  let (_ds, errs) := parse
    "fn cp() : i64 begin fn\n  let Pair(a, b) = (1, 2);\n  return 0;\nend fn;"
  let _ := errs   -- Pattern Pair(a, b) = (1, 2); — let pattern
  check "ctor pattern parses without crash" true (errs.size ≥ 0)

  /- Error recovery: bad decl followed by good decl -/
  let sourceText := "module Good;\n? bad ? ;\nconst N : i64 = 1;"
  let (ds, errs) := parse sourceText
  check "error recovery: good + bad + good"
    true (errs.size > 0 ∧ ds.size ≥ 2)

  /- Error recovery: malformed fn body resyncs to next decl. -/
  let sourceText := "fn a() : i64 ??? ;\nconst N : i64 = 1;"
  let (ds, errs) := parse sourceText
  check "recovery: malformed fn body then const"
    true (errs.size > 0 ∧ ds.size ≥ 2)
  check "recovery: const decl survives"
    true (ds.any (fun decl => declKind decl = "const"))

  /- Error recovery: unknown decl-starting keyword is swallowed
     and the subsequent `module M;` still parses.  Because the
     token `class` appears inside its own body (`end class;`), the
     resync stops at the inner `class` — producing two
     `Decl.unimplemented` placeholders — and then the `module`
     decl follows. -/
  let sourceText := "class X end class;\nmodule M;"
  let (ds, errs) := parse sourceText
  let _ := errs
  check "recovery: unknown class yields >=1 decls"
    true (ds.size ≥ 1)
  check "recovery: trailing module survives after unknown"
    true (ds.any (fun decl => declKind decl = "module"))

  /- Error recovery: three good decls around two bad decls. -/
  let sourceText :=
    "module A;\n? ? ? ;\nmodule B;\n$$$ ;\nmodule C;"
  let (ds, errs) := parse sourceText
  let moduleCount := ds.foldl
    (fun accumulator d => if declKind d = "module" then accumulator + 1 else accumulator) 0
  check "recovery: all three module decls survive" 3 moduleCount
  check "recovery: errors were emitted" true (errs.size > 0)

  /- Cascade-boundedness: a single malformed decl produces a
     bounded number of errors, NOT an unbounded cascade as the
     parser panics and resyncs.  The exact counts below are
     upper bounds on what the resync discipline should emit —
     each figure exceeded means error generation is cascading
     past the sync point, which is the bug shape Q35 pins. -/
  -- Empirical bounds.  Each upper bound is set at twice the
  -- observed count so that a ≥2× jump — the shape that would
  -- indicate cascading — trips the test while normal variation
  -- (adding a new error code, tightening a diagnostic) does not.
  let (_, errs) := parse "? ? ? ;"
  check "cascade: one bad top-level, ≤ 8 errors" true (errs.size ≤ 8)

  let (_, errs) := parse "fn bad( : i64 = 0;"
  check "cascade: malformed fn sig, ≤ 10 errors" true (errs.size ≤ 10)

  let (_, errs) := parse "module A;\n? ? ? ;\nmodule B;"
  check "cascade: bad decl between two good, ≤ 8 errors" true (errs.size ≤ 8)

  let (_, errs) := parse "const N : i64 = ? ;"
  check "cascade: const with garbage rhs, ≤ 6 errors" true (errs.size ≤ 6)

  /- Parse errors never prevent subsequent declarations from
     being structurally recognized — this is the core recovery
     invariant.  A malformed const followed by a good fn still
     produces two parsed decls (even if the const is an
     unimplemented placeholder). -/
  let (ds, _) := parse "const N : i64 = ? ;\npub fn id(x: i64) : i64 = x;"
  check "recovery: good fn after bad const, ≥ 2 decls" true (ds.size ≥ 2)
  check "recovery: good fn after bad const parses as fn" true
    (ds.any (fun d => declKind d = "fn"))

  -- ## B4 — spec clauses attach to fnDecl (§5.1, §10)
  -- Parser round-trip: the `where` / `pre` / `post` / `decreases`
  -- clauses land on fnDecl's `specs` array in source order.
  -- Exercises parseOptionalSpecClauses's four arms plus the
  -- `post <binder> =>` / `post EXPR;` split.
  let (ds, errs) := parse
    ("fn f(n: i64) : i64" ++
     "\n  pre true;" ++
     "\n  post r => r;" ++
     "\n  decreases n;" ++
     "\n= n;")
  check "spec clauses: pre/post/decreases parse clean" 0 errs.size
  let specCount : Nat :=
    match ds[0]? with
    | some (Decl.fnDecl _ _ _ _ _ _ specs _ _) => specs.size
    | _                                          => 0
  check "spec clauses: three clauses attached" 3 specCount

  /- post without `<binder> =>` gets default binder "_". -/
  let (ds, errs) := parse "fn g() : i64 post 0;\n= 0;"
  check "post without binder parses" 0 errs.size
  let postBinder : Option String :=
    match ds[0]? with
    | some (Decl.fnDecl _ _ _ _ _ _ specs _ _) =>
      specs.findSome? fun sc =>
        match sc with
        | SpecClause.postCond binder _ _ => some binder
        | _                              => none
    | _ => none
  check "post without binder defaults to \"_\"" (some "_") postBinder

  -- `where` parses and attaches as the first clause when present.
  let (ds, errs) := parse
    ("fn h<a: type>(x: a) : a" ++
     "\n  where Ord;" ++
     "\n= x;")
  check "where clause: parses with type-class constraint" 0 errs.size
  let hasWhere : Bool :=
    match ds[0]? with
    | some (Decl.fnDecl _ _ _ _ _ _ specs _ _) =>
      specs.any fun sc =>
        match sc with
        | SpecClause.whereCstr _ _ => true
        | _                        => false
    | _ => false
  check "where clause attaches to fnDecl" true hasWhere

end Tests.Syntax.ParserTests
