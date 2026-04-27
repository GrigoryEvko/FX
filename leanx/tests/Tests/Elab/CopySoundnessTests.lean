import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Syntax.Parser
import FX.Syntax.Lexer
import Tests.Framework

/-!
# Q55 — `@[copy]` transitive soundness check (T121)

§7.8 mandates: a type marked `@[copy]` must have every ctor
argument itself copy-compatible.  Without this check a user
could write

    @[copy] type unsafe_wrapper
      Wrap(FileDescriptor);
    end type;

and freely duplicate the wrapper, silently duplicating the
linear `FileDescriptor` — a classic use-after-close pitfall.

Tests here exercise the `elabTypeDeclSpec` check added in
Q55:

  * Accept: `@[copy]` over a prelude copy type (`Nat`).
  * Accept: `@[copy]` self-reference — a recursive data type
    marked copyable.
  * Reject T121: `@[copy]` over a user type that isn't marked
    copyable.
  * Reject T121: `@[copy]` over a type-parameter reference
    (`@[copy] type Box<a> { x: a };`) — type params carry no
    copyability guarantee without constraint syntax (§16.4
    follow-up).

The kernel-side canary (`IndSpec.isCopy` defaulting to false,
and `Grade.shared` being the only non-default grade produced
by `gradeForParam`) protects against silent regression of the
check.  These tests additionally pin that the CHECK runs —
not just that the flag is stored.
-/

namespace Tests.Elab.CopySoundnessTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open Tests

/-- Same pipeline harness as the Q53/Q54 end-to-end tests. -/
def runPipeline (sourceText : String)
    : Array FX.Util.Error × Array DeclResult :=
  let lexOut := FX.Syntax.tokenize sourceText
  let (parsedFile, parseErrs) := FX.Syntax.Parser.parseFile lexOut.tokens
  let combinedErrors := lexOut.errors ++ parseErrs
  let declResults := checkFile parsedFile
  (combinedErrors, declResults)

def nthIsOk (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.okDecl _) => true
  | _ => false

def nthFailsWithCode (results : Array FX.Util.Error × Array DeclResult)
    (nthDecl : Nat) (expectedCode : String) : Bool :=
  results.1.isEmpty &&
  match results.2[nthDecl - 1]? with
  | some (.elabFail elabErr)   => elabErr.code == expectedCode
  | some (.typeFail _ typeErr) => typeErr.code == expectedCode
  | _                          => false

def run : IO Unit := Tests.suite "Tests.Elab.CopySoundnessTests" do

  /- ## 1. Accept — @[copy] over prelude Nat (marked isCopy). -/
  let natCopySource :=
    "@[copy]
    type cell
      Cell(Nat);
    end type;"
  check "1. @[copy] over Nat: accept" true
    (nthIsOk (runPipeline natCopySource) 1)

  /- ## 2. Accept — @[copy] self-referential recursive data.
     The rec call is Term.ind "rope" [] in ctor arg position,
     which the Q55 check whitelists.  Rope stays purely POD. -/
  let selfRefSource :=
    "@[copy]
    type rope
      Empty;
      Snoc(rope);
    end type;"
  check "2. @[copy] self-ref: accept" true
    (nthIsOk (runPipeline selfRefSource) 1)

  /- ## 3. Reject T121 — @[copy] over non-copy user type. -/
  let nonCopySource :=
    "type resource
      Handle;
    end type;

    @[copy]
    type bad_wrap
      Wrap(resource);
    end type;"
  let nonCopyResults := runPipeline nonCopySource
  check "3a. non-copy base type (1) ok" true (nthIsOk nonCopyResults 1)
  check "3b. @[copy] over non-copy type: T121" true
    (nthFailsWithCode nonCopyResults 2 "T121")

  /- ## 4. Reject T121 — @[copy] over a type parameter (generic
     copyable without constraint syntax).  Deferred to §16.4
     where-clauses once they land. -/
  let genericSource :=
    "@[copy]
    type box<a: type>
      BoxOf(a);
    end type;"
  check "4. @[copy] over generic `a`: T121" true
    (nthFailsWithCode (runPipeline genericSource) 1 "T121")

  /- ## 5. Accept — @[copy] multi-arg ctor, both args are copy.
     The check is per-arg, not just head; two Nat args pass. -/
  let multiArgSource :=
    "@[copy]
    type pair_of_nats
      MkPair(Nat, Nat);
    end type;"
  check "5. @[copy] multi-arg all copy: accept" true
    (nthIsOk (runPipeline multiArgSource) 1)

  /- ## 6. Reject T121 — @[copy] with one good arg and one bad
     arg.  Must reject even though some args ARE copy; all
     must pass.  `resource` defined above as non-copy. -/
  let mixedArgSource :=
    "type resource
      Handle;
    end type;

    @[copy]
    type mixed
      Both(Nat, resource);
    end type;"
  check "6. @[copy] mixed args (one non-copy): T121" true
    (nthFailsWithCode (runPipeline mixedArgSource) 2 "T121")

  /- ## 7. Accept — plain (non-@[copy]) type over non-copy arg
     is untouched by the T121 check.  Sanity: the check only
     fires when the enclosing type is `@[copy]`. -/
  let plainNonCopySource :=
    "type resource
      Handle;
    end type;

    type container
      Hold(resource);
    end type;"
  let plainResults := runPipeline plainNonCopySource
  check "7a. plain non-copy base (1) ok" true (nthIsOk plainResults 1)
  check "7b. plain non-copy container (2) ok (no T121)" true
    (nthIsOk plainResults 2)

end Tests.Elab.CopySoundnessTests
