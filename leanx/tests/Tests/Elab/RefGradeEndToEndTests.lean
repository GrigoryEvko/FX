import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.Framework

/-!
# Q53 end-to-end rejection / acceptance pin

`tests/Tests/Elab/ModeToGradeTests.lean` pins `modeToGrade` in
isolation — its 23 `native_decide` checks verify the pure
function lowers each `ParamMode` to the expected `Grade`.  This
file closes the remaining gap by running the full pipeline
(tokenize → parseFile → checkFile) on two side-by-side source
fragments that differ only in a single `ref` keyword.  The
REJECT side must surface `M001` from the linearity exit check;
the ACCEPT side must reach `okDecl`.

Without this file, a future refactor could:

  * break the wiring from `modeToGrade` to the kernel's `Pi`
    grade (e.g., `piFromTerm` forgetting to thread the returned
    `Grade`), OR
  * re-collapse `Grade.shared` into `Grade.default` somewhere
    downstream of `modeToGrade`,

...and the isolated `ModeToGradeTests` checks would still pass
while real user programs broke.  The source here is the
minimum-viable "classical Peano times" pattern where parameter
`b` is referenced twice inside the `Succ(p)` arm — once as the
left operand of the `plus` call, once as the right operand of
the recursive call.  Hand-verified against the Q53 commit
43a9e1d2; blind rebuild must reproduce.
-/

namespace Tests.Elab.RefGradeEndToEndTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open Tests

/-- Parse source text and run `checkFile` end-to-end.  Returns
    the tri-state `DeclResult` array.  Any parse error surfaces
    as a non-empty second component — callers assert empty. -/
def runPipeline (sourceText : String)
    : Array FX.Util.Error × Array DeclResult :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (parsedFile, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  let combinedErrors := lexOut.errors ++ parseErrs
  let declResults := checkFile parsedFile
  (combinedErrors, declResults)

/-- True iff the result list has no parse errors and the given
    1-indexed decl result is `okDecl`. -/
def nthIsOk (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.okDecl _) => true
  | _ => false

/-- True iff the 1-indexed decl surfaced error code
    `expectedCode`, either as an `elabFail` (elaboration-layer
    rejection) OR a `typeFail` (kernel-typing rejection).  M001
    is thrown by `Kernel/Typing.lean` at the linearity exit
    check and therefore surfaces as `typeFail`; `elabFail`
    covers elab-layer codes (E0xx, P0xx, S0xx).  The helper
    unifies both to keep the test prose focused on the
    observable-error-code level. -/
def nthFailsWithCode (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) (expectedCode : String) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.elabFail elabErr)   => elabErr.code == expectedCode
  | some (.typeFail _ typeErr) => typeErr.code == expectedCode
  | _                          => false

/-- Base source: a user-declared non-copy type `token` + a helper
    that consumes one token.  `token` isn't marked `@[copy]`, so
    the kernel treats it as linear regardless of Q55's prelude
    copy-spec upgrades.  This keeps the REJECT side genuinely
    multi-use-rejecting — Q55 made `Nat` copy by default, so a
    Nat-based witness stopped being a negative-case pin. -/
def baseSource : String :=
"type token
  Mark;
end type;

fn seen(t: token) : Nat = match t;
  Mark => Nat.Succ(Nat.Zero);
end match;"

/-- REJECT program — `dup_seen` with `t: token` (default linear,
    usage = 1).  The body calls `seen(t)` twice inside a block,
    joining `1 + 1 = ω` — M001 fires at the function-exit check.
    `Nat` wouldn't trip this post-Q55 because Nat is @[copy];
    `token` stays linear-by-default. -/
def rejectSource : String :=
baseSource ++
"
fn dup_seen(t: token) : Nat
begin fn
  let first  = seen(t);
  let second = seen(t);
  return Nat.Succ(Nat.Zero);
end fn;"

/-- ACCEPT program — identical body, but `t` is declared `ref t:
    token` → `modeToGrade ParamMode.ref_` is `Grade.shared` →
    `Pi`'s binder grade has `Usage.omega` → multi-use admitted.
    The `ref`-mode override works independently of the type's
    `@[copy]` flag; copy-able types and shared-borrow modes are
    two separate Q53/Q54 pathways that converge on
    `Grade.shared`. -/
def acceptSource : String :=
baseSource ++
"
fn dup_seen(ref t: token) : Nat
begin fn
  let first  = seen(t);
  let second = seen(t);
  return Nat.Succ(Nat.Zero);
end fn;"

def run : IO Unit := Tests.suite "Tests.Elab.RefGradeEndToEndTests" do

  /- ## REJECT: t: token (non-copy user type, linear) multi-use
     fires M001.  Decl 1 is the type, decl 2 is `seen`, decl 3
     is the multi-use `dup_seen`. -/
  let rejectResults := runPipeline rejectSource
  check "reject: token type (1) ok" true
    (nthIsOk rejectResults 1)
  check "reject: seen (2) ok" true
    (nthIsOk rejectResults 2)
  check "reject: dup_seen (3) fails with M001" true
    (nthFailsWithCode rejectResults 3 "M001")

  /- ## ACCEPT: ref t: token → Grade.shared → multi-use admitted. -/
  let acceptResults := runPipeline acceptSource
  check "accept: token type (1) ok" true
    (nthIsOk acceptResults 1)
  check "accept: seen (2) ok" true
    (nthIsOk acceptResults 2)
  check "accept: dup_seen (3) ok" true
    (nthIsOk acceptResults 3)

  /- ## Single-source delta: swap one `ref` keyword, flip the
     M001 verdict.  This is the canary for the full surface
     →kernel wiring.  If a future refactor breaks the chain in
     a way that makes BOTH programs accept (or BOTH reject),
     this pair of checks fires immediately. -/
  check "delta: reject.dup_seen fails, accept.dup_seen succeeds" true
    ((nthFailsWithCode rejectResults 3 "M001")
     && (nthIsOk acceptResults 3))

end Tests.Elab.RefGradeEndToEndTests
