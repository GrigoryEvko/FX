import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.ElabSupport

/-!
# Named argument routing tests (B12)

`fx_design.md` §4.1 requires calls with ≥2 positional args to
use named arguments.  Phase 2.2 supports all-named (or all-named
plus implicits) calls to direct references to registered fn
decls; mixed positional + named and indirect calls with named
args are rejected with specific error codes.

## Shape coverage

  * All-positional — unchanged routing, baseline.
  * All-named, matching order — routes by position.
  * All-named, reordered — routes correctly.
  * Mixed positional + named — E011.
  * Indirect callee (local binding, lambda, pipe) — E012.
  * Duplicate named — E013.
  * Unknown param name — E014.
  * Missing param — E015.
-/

namespace Tests.Elab.NamedArgsTests

open FX.Kernel
open FX.Elab
open FX.Eval
open FX.Syntax
open Tests.ElabSupport

/-! ## Parse + elab a full program with named-arg call -/

/-- Parse a source snippet and type-check it end-to-end.
    Returns the per-decl results. -/
def checkSource (source : String) : Array DeclResult :=
  let lexOutput := FX.Syntax.tokenize source
  let (parsedFile, _) := FX.Syntax.Parser.parseFile lexOutput.tokens
  FX.Elab.checkFile parsedFile

/-- Helper: predicate — all decls elaborated and type-checked. -/
def allOk (results : Array DeclResult) : Bool :=
  results.all fun result =>
    match result with
    | .okDecl _ => true
    | _         => false

/-- Helper: predicate — at least one decl failed with the given code. -/
def anyFailedWith (code : String) (results : Array DeclResult) : Bool :=
  results.any fun result =>
    match result with
    | .elabFail elabError => elabError.code == code
    | _                    => false

/-! ## Baseline sources

Use `Nat` as the concrete type — it's in the prelude and its
values are well-typed as `Nat`.  `type` as a parameter type
would make main's return `type` of universe 1, which then
mismatches the declared universe-0 return — a separate
unrelated concern.
-/

def identSource (callStr : String) : String :=
  "fn ident(x: Nat) : Nat = x;\nfn main() : Nat = " ++ callStr ++ ";"

def chooseSource (callStr : String) : String :=
  "fn choose(a: Nat, b: Nat) : Nat = a;\nfn main() : Nat = " ++ callStr ++ ";"

/-! ## 1. All-positional baseline — unchanged behavior -/

example :
  allOk (checkSource (identSource "ident(Nat.Zero)")) = true := by native_decide

/-! ## 2. All-named matching order — routes normally -/

example :
  allOk (checkSource (identSource "ident(x: Nat.Zero)")) = true := by native_decide

/-! ## 3. All-named, reordered — routes correctly -/

example :
  allOk (checkSource (chooseSource "choose(b: Nat.Zero, a: Nat.Zero)"))
  = true := by native_decide

/-! ## 4. Mixed positional + named — E011 -/

example :
  anyFailedWith "E011"
    (checkSource (chooseSource "choose(Nat.Zero, b: Nat.Zero)"))
  = true := by native_decide

/-! ## 5. Unknown parameter name — E014 -/

example :
  anyFailedWith "E014"
    (checkSource (identSource "ident(y: Nat.Zero)"))
  = true := by native_decide

/-! ## 6. Missing parameter — E015 -/

example :
  anyFailedWith "E015"
    (checkSource (chooseSource "choose(a: Nat.Zero)"))
  = true := by native_decide

/-! ## 7. Duplicate named argument — E013 -/

example :
  anyFailedWith "E013"
    (checkSource (identSource "ident(x: Nat.Zero, x: Nat.Zero)"))
  = true := by native_decide

/-! ## 8. E012 — unregistered callee name

Writing `unknownFn(x: v)` where `unknownFn` isn't declared
anywhere.  B12's reorder fires before fnExpr elab, so the
user gets the named-arg diagnostic first (rather than
falling through to an unknown-identifier error). -/

example :
  anyFailedWith "E012" (checkSource
    "fn main() : Nat = unknownFn(x: Nat.Zero);") = true := by native_decide

/-! ## 9. Reorder CORRECTNESS — evaluated result differs from
       positional order

Using distinct values and a body that returns the second
positional parameter: `fn second(a: Nat, b: Nat) : Nat = b`.
Called `second(b: 1, a: 0)`, B12 should reorder to
`second(0, 1)` — positional a=0, b=1 — so body returns
`b = 1`.  If the reorder logic were broken (source order
retained as `[b: 1, a: 0]`), positional application would
set `a := 1, b := 0`, making body return `b = 0`.

The test extracts the evaluated result for `main` and pins
it to `1`, distinguishing correct reorder from no-op. -/

/-- Attempt to evaluate the `main` decl and extract its
    numeric Nat value.  Returns `none` when elab fails, the
    body doesn't eval to a Nat chain, or `main` isn't found. -/
def evalMainNat (source : String) : Option Nat :=
  let results := checkSource source
  let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
  match results.findSome? fun result =>
    match result with
    | .okDecl elaboratedDecl =>
      if elaboratedDecl.name == "main" then some elaboratedDecl.body else none
    | _ => none with
  | some mainBody => unaryNatCount? (evalZeroArgBody evalEnv mainBody)
  | none          => none

example :
  evalMainNat (
    "fn second(a: Nat, b: Nat) : Nat = b;\n"
      ++ "fn main() : Nat = second(b: Nat.Succ(Nat.Zero), a: Nat.Zero);")
  = some 1 := by native_decide

-- And the positional baseline for comparison: same values, no reorder.
example :
  evalMainNat (
    "fn second(a: Nat, b: Nat) : Nat = b;\n"
      ++ "fn main() : Nat = second(Nat.Zero, Nat.Succ(Nat.Zero));")
  = some 1 := by native_decide

-- Three-param reorder: verify multi-swap lands each value at the
-- right slot.  `fn triple(a: Nat, b: Nat, c: Nat) : Nat = c` with
-- `triple(c: 2, a: 0, b: 1)` should return `c = 2`.
example :
  evalMainNat (
    "fn triple(a: Nat, b: Nat, c: Nat) : Nat = c;\n"
      ++ "fn main() : Nat = triple(c: Nat.Succ(Nat.Succ(Nat.Zero)),"
      ++ " a: Nat.Zero, b: Nat.Succ(Nat.Zero));")
  = some 2 := by native_decide

end Tests.Elab.NamedArgsTests
