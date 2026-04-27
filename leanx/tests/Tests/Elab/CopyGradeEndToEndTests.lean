import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.Framework

/-!
# Q54 end-to-end rejection / acceptance pin

Companion to `RefGradeEndToEndTests` — where Q53 tested the
`ref` surface mode flipping the grade, Q54 tests the `@[copy]`
type-level attribute doing the same through a different path:
the grade override goes via `IndSpec.isCopy` rather than
`ParamMode.ref_`.

Without this file, a future refactor could silently drop the
attribute → `IndSpec.isCopy` wiring (e.g. by reverting the
`Decl.typeDecl`-plumbs-attrs field) and `gradeForParam` would
still work perfectly on its own — but no user program would
ever benefit, because every IndSpec's `isCopy` would stay
false.  The delta here is a one-line `@[copy]` prefix; its
disappearance must flip acceptance verdict.
-/

namespace Tests.Elab.CopyGradeEndToEndTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open Tests

/-- Run tokenize → parseFile → checkFile.  Same helper shape as
    `RefGradeEndToEndTests.runPipeline`; duplicated intentionally
    to keep the two test files self-contained (any future
    refactor that consolidates into a shared harness can drop
    both copies). -/
def runPipeline (sourceText : String)
    : Array FX.Util.Error × Array DeclResult :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (parsedFile, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  let combinedErrors := lexOut.errors ++ parseErrs
  let declResults := checkFile parsedFile
  (combinedErrors, declResults)

/-- True iff the 1-indexed decl result is `okDecl` (with empty
    parse errors). -/
def nthIsOk (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.okDecl _) => true
  | _ => false

/-- True iff the 1-indexed decl surfaced error code
    `expectedCode`, via either `elabFail` OR `typeFail`.  M001
    fires from Kernel/Typing.lean → typeFail. -/
def nthFailsWithCode (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) (expectedCode : String) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.elabFail elabErr)   => elabErr.code == expectedCode
  | some (.typeFail _ typeErr) => typeErr.code == expectedCode
  | _                          => false

/-- Program body shared by both source variants — four decls:
    the type, two peek helpers (each takes the type once, so they
    always accept regardless of `@[copy]`), and the multi-use
    caller.  Only the multi-use caller is sensitive to the
    attribute. -/
def programBody : String :=
"type point
  Point(Nat);
end type;

fn deref(p: point) : Nat = match p;
  Point(inner) => inner;
end match;

fn deref_again(p: point) : Nat = match p;
  Point(inner) => inner;
end match;

fn use_twice(p: point) : Nat
begin fn
  let first  = deref(p);
  let second = deref_again(p);
  return Nat.Succ(Nat.Zero);
end fn;"

/-- ACCEPT: attribute present → IndSpec.isCopy → Grade.shared → ok. -/
def acceptSource : String := "@[copy]\n" ++ programBody

/-- REJECT: attribute absent → default linear grade → M001. -/
def rejectSource : String := programBody

def run : IO Unit := Tests.suite "Tests.Elab.CopyGradeEndToEndTests" do

  /- ## REJECT — plain type decl: multi-use fires M001. -/
  let rejectResults := runPipeline rejectSource
  check "reject: type decl (1) ok" true
    (nthIsOk rejectResults 1)
  check "reject: deref (2) ok" true
    (nthIsOk rejectResults 2)
  check "reject: deref_again (3) ok" true
    (nthIsOk rejectResults 3)
  check "reject: use_twice (4) fails with M001" true
    (nthFailsWithCode rejectResults 4 "M001")

  /- ## ACCEPT — @[copy] decl: multi-use admitted. -/
  let acceptResults := runPipeline acceptSource
  check "accept: type decl (1) ok" true
    (nthIsOk acceptResults 1)
  check "accept: deref (2) ok" true
    (nthIsOk acceptResults 2)
  check "accept: deref_again (3) ok" true
    (nthIsOk acceptResults 3)
  check "accept: use_twice (4) ok" true
    (nthIsOk acceptResults 4)

  /- ## Delta — one-line `@[copy]` prefix flips the verdict. -/
  check "delta: reject.use_twice fails, accept.use_twice succeeds" true
    ((nthFailsWithCode rejectResults 4 "M001")
     && (nthIsOk acceptResults 4))

end Tests.Elab.CopyGradeEndToEndTests
