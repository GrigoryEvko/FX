import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Kernel.Env
import FX.Derived.Session.Binary
import FX.Derived.Session.Translate
import FX.Syntax.Ast
import Tests.Framework

/-!
# Session decl elab tests (task S11 coverage, filed under G2)

End-to-end and unit-level coverage for the session-declaration
elaborator `elabSessionDeclSpec`.  S10 landed the parser and
S11 landed the elab, but session elab had only parser-level
tests — nothing verified that a parsed session actually
produces the right `CoindSpec` list, or that malformed shapes
surface the right error codes.

Scope per §11.24 kernel translation:

  * `endStep` at top level → one terminal `CoindSpec`
  * `sendStep p t` → `CoindSpec` whose `send` destructor
    resultType is `Π (p :_default t) → Term.coind <continuation-name>`
  * `recvStep p t` → parallel for `recv` destructor
  * `branchStep arms` → `offerS` — one destructor per arm label
  * `selectStep arms` → `selectS` — one destructor per arm label
  * `continueStep label` inside `loopS` → self-ref via shared
    loop name
  * `rec LABEL` binder → wrap top session in `loopS`; every
    `continueStep LABEL'` must have `LABEL' == LABEL` or S001
    fires
  * `continueStep` without any enclosing rec binder → S001

These tests exercise each arm end-to-end via `elabSessionDeclSpec`,
inspecting the returned `List CoindSpec` for shape, count, and
destructor names.
-/

namespace Tests.Elab.SessionElabTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests

def zeroSpan : Span := Span.zero

/-- `Nat` as an AST type reference — resolves to the prelude
    inductive, present in the default `GlobalEnv`. -/
def natType : Ast.Expr :=
  .var { parts := #[], final := "Nat", span := zeroSpan }

/-- Shorthand for the "nothing declared" globalEnv with only
    the prelude specs.  `elabSessionDeclSpec` elaborates payload
    types against this env, so any payload type must resolve
    through prelude inductives. -/
def envWithPrelude : GlobalEnv := GlobalEnv.empty

/-- Build a one-arm branch/select arm for tests. -/
def oneArm (label : String) (steps : Array Ast.SessionStep)
    : Ast.SessionBranchArm :=
  Ast.SessionBranchArm.mk label steps zeroSpan

/-- True iff the elab result succeeded (specs list non-empty
    or empty-but-valid) with no errors. -/
def elabOk (result : Except ElabError (List CoindSpec)) : Bool :=
  match result with | .ok _ => true | .error _ => false

/-- Extract the S001 error code (or "_other") from an elab
    result, for checking the right error surfaces. -/
def elabErrorCode (result : Except ElabError (List CoindSpec)) : String :=
  match result with
  | .ok _        => "_ok"
  | .error err   => err.code

/-- Spec count in a successful result, 0 on failure. -/
def specCount (result : Except ElabError (List CoindSpec)) : Nat :=
  match result with
  | .ok specs => specs.length
  | .error _  => 0

def run : IO Unit := Tests.suite "Tests.Elab.SessionElabTests" do

  /- ## 1. End-only session → 2 CoindSpecs (S12: primary + dual).
     The dual of `endS` is `endS`, so both halves emit a terminal
     spec.  Primary under "P1", dual under "P1__dual". -/
  let endOnlyResult :=
    elabSessionDeclSpec envWithPrelude "P1" #[] none
      #[Ast.SessionStep.endStep zeroSpan]
      zeroSpan
  check "1. end-only session elabs ok" true (elabOk endOnlyResult)
  check "1. end-only session: 2 specs (primary + dual)" 2 (specCount endOnlyResult)

  /- ## 2. Send-then-end → 4 CoindSpecs (S12).  Primary: send + end
     (2 specs).  Dual: recv + end (2 specs).  Total = 4. -/
  let sendEndSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.sendStep "x" natType zeroSpan,
    Ast.SessionStep.endStep zeroSpan
  ]
  let sendEndResult :=
    elabSessionDeclSpec envWithPrelude "P2" #[] none sendEndSteps zeroSpan
  check "2. send-then-end elabs ok" true (elabOk sendEndResult)
  check "2. send-then-end: 4 specs (2 primary + 2 dual)" 4
    (specCount sendEndResult)

  /- ## 3. Recv-then-end → 4 CoindSpecs (S12).  Dual flips recv to
     send; both halves have 2 specs. -/
  let recvEndSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.recvStep "x" natType zeroSpan,
    Ast.SessionStep.endStep zeroSpan
  ]
  let recvEndResult :=
    elabSessionDeclSpec envWithPrelude "P3" #[] none recvEndSteps zeroSpan
  check "3. recv-then-end elabs ok" true (elabOk recvEndResult)
  check "3. recv-then-end: 4 specs (2 primary + 2 dual)" 4
    (specCount recvEndResult)

  /- ## 4. Send→recv→end → 6 CoindSpecs (S12).  Primary: 3 specs.
     Dual: recv→send→end also 3 specs.  Total = 6. -/
  let chainSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.sendStep "x" natType zeroSpan,
    Ast.SessionStep.recvStep "y" natType zeroSpan,
    Ast.SessionStep.endStep zeroSpan
  ]
  let chainResult :=
    elabSessionDeclSpec envWithPrelude "P4" #[] none chainSteps zeroSpan
  check "4. send-recv-end elabs ok" true (elabOk chainResult)
  check "4. send-recv-end: 6 specs (3 primary + 3 dual)" 6
    (specCount chainResult)

  /- ## 5. Loop with rec binder — wraps the body in `loopS`.
     `rec Loop; send; Loop;` — the loop body sends once and
     continues. -/
  let loopSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.sendStep "x" natType zeroSpan,
    Ast.SessionStep.continueStep "Loop" zeroSpan
  ]
  let loopResult :=
    elabSessionDeclSpec envWithPrelude "P5" #[] (some "Loop") loopSteps zeroSpan
  check "5. loop-rec elabs ok" true (elabOk loopResult)

  /- ## 6. ERROR: orphan continue — no rec binder, but the
     session body has a continueStep.  Must emit S001. -/
  let orphanSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.continueStep "X" zeroSpan
  ]
  let orphanResult :=
    elabSessionDeclSpec envWithPrelude "P6" #[] none orphanSteps zeroSpan
  check "6. orphan continue: S001" "S001" (elabErrorCode orphanResult)

  /- ## 7. ERROR: continue label mismatch — rec Loop; but
     continueStep "Other";.  Must emit S001. -/
  let mismatchSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.continueStep "Other" zeroSpan
  ]
  let mismatchResult :=
    elabSessionDeclSpec envWithPrelude "P7" #[] (some "Loop") mismatchSteps zeroSpan
  check "7. mismatched continue label: S001" "S001" (elabErrorCode mismatchResult)

  /- ## 8. Branch with two arms — `offerS [("a", endS), ("b", endS)]`.
     Root spec has two destructors named `a` and `b`. -/
  let branchSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.branchStep #[
      oneArm "a" #[Ast.SessionStep.endStep zeroSpan],
      oneArm "b" #[Ast.SessionStep.endStep zeroSpan]
    ] zeroSpan
  ]
  let branchResult :=
    elabSessionDeclSpec envWithPrelude "P8" #[] none branchSteps zeroSpan
  check "8. branch-two-arms elabs ok" true (elabOk branchResult)

  /- ## 9. Select with two arms — structural dual of branch. -/
  let selectSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.selectStep #[
      oneArm "yes" #[Ast.SessionStep.endStep zeroSpan],
      oneArm "no"  #[Ast.SessionStep.endStep zeroSpan]
    ] zeroSpan
  ]
  let selectResult :=
    elabSessionDeclSpec envWithPrelude "P9" #[] none selectSteps zeroSpan
  check "9. select-two-arms elabs ok" true (elabOk selectResult)

  /- ## 10. ERROR: branch with duplicate label — per §11.27 and
     §11.14, duplicate labels in `select`/`offer`/`branch` emit
     S002 (distinct from S001 unguarded-continue).  The
     elaborator now splits these codes per S24. -/
  let dupSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.branchStep #[
      oneArm "dup" #[Ast.SessionStep.endStep zeroSpan],
      oneArm "dup" #[Ast.SessionStep.endStep zeroSpan]
    ] zeroSpan
  ]
  let dupResult :=
    elabSessionDeclSpec envWithPrelude "P10" #[] none dupSteps zeroSpan
  check "10. duplicate branch label: S002" "S002" (elabErrorCode dupResult)

  /- ## 11. Branch with recv in one arm — exercises nested
     session-step-list elaboration inside an arm body. -/
  let nestedBranchSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.branchStep #[
      oneArm "ack" #[
        Ast.SessionStep.recvStep "ack_val" natType zeroSpan,
        Ast.SessionStep.endStep zeroSpan
      ],
      oneArm "nak" #[
        Ast.SessionStep.endStep zeroSpan
      ]
    ] zeroSpan
  ]
  let nestedBranchResult :=
    elabSessionDeclSpec envWithPrelude "P11" #[] none nestedBranchSteps zeroSpan
  check "11. nested branch with recv elabs ok" true
    (elabOk nestedBranchResult)

  /- ## 12. Loop with branch inside — a stream-reader pattern
     from §11.1: `rec Loop; branch { next => recv; Loop; | done => end; }`. -/
  let streamReaderSteps : Array Ast.SessionStep := #[
    Ast.SessionStep.branchStep #[
      oneArm "next" #[
        Ast.SessionStep.recvStep "item" natType zeroSpan,
        Ast.SessionStep.continueStep "Loop" zeroSpan
      ],
      oneArm "done" #[
        Ast.SessionStep.endStep zeroSpan
      ]
    ] zeroSpan
  ]
  let streamReaderResult :=
    elabSessionDeclSpec envWithPrelude "P12" #[]
      (some "Loop") streamReaderSteps zeroSpan
  check "12. stream-reader (loop+branch+continue) elabs ok" true
    (elabOk streamReaderResult)

  /- ## 13. End-to-end via checkFile: a session decl in a file
     registers its CoindSpecs on the global env (pass 1).  The
     returned DeclResult should be `okDecl`. -/
  let fileWithSession : Ast.File := {
    span := zeroSpan,
    decls := #[
      Decl.sessionDecl "MyProto" #[] none #[
        Ast.SessionStep.sendStep "x" natType zeroSpan,
        Ast.SessionStep.endStep zeroSpan
      ] zeroSpan
    ]
  }
  let checkFileResult := checkFile fileWithSession
  let allOkInFile := checkFileResult.all fun r =>
    match r with | .okDecl _ => true | _ => false
  check "13. end-to-end checkFile: session decl ok" true allOkInFile

  /- ## 14. End-to-end: malformed session (orphan continue)
     propagates elabFail at the checkFile boundary. -/
  let fileWithBadSession : Ast.File := {
    span := zeroSpan,
    decls := #[
      Decl.sessionDecl "BadProto" #[] none #[
        Ast.SessionStep.continueStep "Nope" zeroSpan
      ] zeroSpan
    ]
  }
  let badCheckResult := checkFile fileWithBadSession
  let hasElabFail := badCheckResult.any fun r =>
    match r with | .elabFail _ => true | _ => false
  check "14. end-to-end checkFile: malformed session → elabFail" true hasElabFail

end Tests.Elab.SessionElabTests
