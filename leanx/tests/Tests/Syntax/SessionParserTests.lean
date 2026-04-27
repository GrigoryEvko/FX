import FX.Syntax.Lexer
import FX.Syntax.Parser
import Tests.Framework

/-!
# Session decl parser tests (task S10)

Per `fx_grammar.md §11`.  Exercises the four top-level shapes:

  * Linear send/receive chains terminated by `end;`.
  * Recursive sessions with `rec LABEL;` prefix +
    `LABEL;` references.
  * `branch ARM+ end branch;` offer blocks.
  * `select ARM+ end select;` choose blocks.

Each test parses a small program, asserts zero parse errors,
then projects the resulting `Decl.sessionDecl` to verify
specific fields (name, step count, rec binder, branch arm
count).  Split into its own file from `ParserTests.lean` to
keep each test file's `run` block below the Lean 4 elab-depth
limit.
-/

namespace Tests.Syntax.SessionParserTests

open Tests FX.Syntax FX.Syntax.Ast

/-- Convenience: run the lexer + parser and return just the
    decls plus the parse errors.  Mirrors ParserTests.parse. -/
def parse (sourceText : String) : Array Decl × Array FX.Util.Error :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (fileResult, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  (fileResult.decls, lexOut.errors ++ parseErrs)

/-- Project a parsed `Decl.sessionDecl`'s name from the first
    decl, or "<not-session>" otherwise. -/
def sessionName? (decls : Array Decl) : String :=
  match decls[0]? with
  | some (Decl.sessionDecl declName _ _ _ _) => declName
  | _                                         => "<not-session>"

/-- Project the session decl's step count. -/
def sessionStepCount? (decls : Array Decl) : Nat :=
  match decls[0]? with
  | some (Decl.sessionDecl _ _ _ stepList _) => stepList.size
  | _                                         => 0

/-- Project the rec binder. -/
def sessionRecBinder? (decls : Array Decl) : Option String :=
  match decls[0]? with
  | some (Decl.sessionDecl _ _ recB _ _) => recB
  | _                                     => none

/-- Given a session decl, pick the Nth step. -/
def sessionStepAt? (decls : Array Decl) (n : Nat) : Option SessionStep :=
  match decls[0]? with
  | some (Decl.sessionDecl _ _ _ stepList _) => stepList[n]?
  | _                                         => none

/-- True iff the Nth step of the first decl is a branchStep
    with the given arm count. -/
def isBranchWithArms (decls : Array Decl) (n : Nat) (expectedArms : Nat) : Bool :=
  match sessionStepAt? decls n with
  | some (SessionStep.branchStep arms _) => arms.size == expectedArms
  | _                                     => false

/-- True iff the Nth step is a selectStep. -/
def isSelectStep (decls : Array Decl) (n : Nat) : Bool :=
  match sessionStepAt? decls n with
  | some (SessionStep.selectStep _ _) => true
  | _                                  => false

def run : IO Unit := Tests.suite "Tests.Syntax.SessionParserTests" do
  /- Simple one-shot: send then receive then end. -/
  let src1 :=
    "session request_response\n" ++
    "  send(request : Nat);\n" ++
    "  receive(response : Nat);\n" ++
    "  end;\n" ++
    "end session;"
  let (ds1, errs1) := parse src1
  check "oneshot: no parse errors" 0 errs1.size
  check "oneshot: one decl" 1 ds1.size
  check "oneshot: session name" "request_response" (sessionName? ds1)
  check "oneshot: three steps" 3 (sessionStepCount? ds1)

  /- Rec loop: rec Loop; send; Loop; -/
  let src2 :=
    "session loop_chan\n" ++
    "  rec Loop;\n" ++
    "  send(x : Nat);\n" ++
    "  Loop;\n" ++
    "end session;"
  let (ds2, errs2) := parse src2
  check "rec: no parse errors" 0 errs2.size
  check "rec: binder captured" (some "Loop") (sessionRecBinder? ds2)
  check "rec: two steps" 2 (sessionStepCount? ds2)

  /- Branch block with two arms. -/
  let src3 :=
    "session auth\n" ++
    "  send(creds : Nat);\n" ++
    "  branch\n" ++
    "    success => receive(token : Nat); end;\n" ++
    "    failure => receive(reason : Nat); end;\n" ++
    "  end branch;\n" ++
    "end session;"
  let (ds3, errs3) := parse src3
  check "branch: no parse errors" 0 errs3.size
  check "branch: two steps" 2 (sessionStepCount? ds3)
  check "branch: step 1 is branch with 2 arms" true (isBranchWithArms ds3 1 2)

  /- Select block (dual of branch). -/
  let src4 :=
    "session client\n" ++
    "  select\n" ++
    "    go => send(x : Nat); end;\n" ++
    "    stop => end;\n" ++
    "  end select;\n" ++
    "end session;"
  let (ds4, errs4) := parse src4
  check "select: no parse errors" 0 errs4.size
  check "select: step 0 is selectStep" true (isSelectStep ds4 0)

end Tests.Syntax.SessionParserTests
