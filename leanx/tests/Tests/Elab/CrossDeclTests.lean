import FX.Elab.Elaborate
import FX.Elab.CheckFile
import FX.Syntax.Ast
import Tests.Framework

/-!
# Cross-decl resolution tests — two-pass checkFile

`checkFile` runs a two-pass elaboration: pass 1 pre-registers
every decl's declared type in the `GlobalEnv`; pass 2 elaborates
each body with the full environment visible.  References to a
decl's own name (self-recursion) and references to decls that
appear later in the file (forward references) both resolve to
`Term.const`, which the kernel treats as opaque for typing and
looks up for evaluation.

These tests exercise the end-to-end pipeline (parse-like AST
construction in-lean → elab → kernel check) to verify that
cross-decl references work in every direction.
-/

namespace Tests.Elab.CrossDeclTests

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests

def zeroSpan : Span := Span.zero
def qualOf (name : String) : QualIdent :=
  { parts := #[], final := name, span := zeroSpan }
def var (name : String) : Ast.Expr := .var (qualOf name)
def typeKw : Ast.Expr := .literal (.kw .typeKw) zeroSpan

/-- `fn id(a : type, x : a) : a = x;` — the standard identity. -/
def identityDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "id")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan
    ])
    (retType := var "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "x"))
    (span := zeroSpan)

/-- `fn id2(a : type, x : a) : a = id(a, x);` — calls the
    previously-elaborated `id` by name.  Without `GlobalEnv`
    threading this would emit E001 "unknown identifier 'id'". -/
def identity2Decl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "id2")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan
    ])
    (retType := var "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (var "id") #[.pos (var "a"), .pos (var "x")] zeroSpan))
    (span := zeroSpan)

/-- A file holding both decls in order. -/
def twoDeclFile : File :=
  { span := zeroSpan, decls := #[identityDecl, identity2Decl] }

/-- True iff every `DeclResult` in the array is `okDecl _`. -/
def allOk (results : Array DeclResult) : Bool :=
  results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false

/-- Count how many results matched each shape — useful for
    diagnostic asserts that show exactly which decl failed. -/
def countOk (results : Array DeclResult) : Nat :=
  results.foldl (init := 0) fun accumulator declResult =>
    match declResult with
    | .okDecl _ => accumulator + 1
    | _         => accumulator

def countElabFail (results : Array DeclResult) : Nat :=
  results.foldl (init := 0) fun accumulator declResult =>
    match declResult with
    | .elabFail _ => accumulator + 1
    | _           => accumulator

def countTypeFail (results : Array DeclResult) : Nat :=
  results.foldl (init := 0) fun accumulator declResult =>
    match declResult with
    | .typeFail _ _ => accumulator + 1
    | _             => accumulator

/-! ## Positive cases — cross-decl resolution works -/

-- Both decls elaborate and type-check.
example : allOk (checkFile twoDeclFile) = true := by native_decide

example : countOk (checkFile twoDeclFile) = 2 := by native_decide

example : countElabFail (checkFile twoDeclFile) = 0 := by native_decide

example : countTypeFail (checkFile twoDeclFile) = 0 := by native_decide

/-! ## Forward references work (two-pass check) -/

-- Same two decls in REVERSE source order: id2 references id but
-- appears BEFORE id in the file.  With two-pass elab, pass 1
-- registers both signatures in the globalEnv, so pass 2 elabs
-- id2's body against the full env — `Term.const "id"` resolves
-- at type-check time from the pre-registered type.
def reversedFile : File :=
  { span := zeroSpan, decls := #[identity2Decl, identityDecl] }

example : allOk (checkFile reversedFile) = true := by native_decide

example : countOk (checkFile reversedFile) = 2 := by native_decide

example : countElabFail (checkFile reversedFile) = 0 := by native_decide

/-! ## Zero-decl edge case -/

def emptyFile : File := { span := zeroSpan, decls := #[] }

example : (checkFile emptyFile).size = 0 := by native_decide

/-! ## Three-decl chain — id3 references id2 which references id -/

def identity3Decl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "id3")
    (params := #[
      .mk .default_ "a" typeKw zeroSpan,
      .mk .default_ "x" (var "a") zeroSpan
    ])
    (retType := var "a")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (var "id2") #[.pos (var "a"), .pos (var "x")] zeroSpan))
    (span := zeroSpan)

def threeDeclFile : File :=
  { span := zeroSpan, decls := #[identityDecl, identity2Decl, identity3Decl] }

example : allOk (checkFile threeDeclFile) = true := by native_decide

example : countOk (checkFile threeDeclFile) = 3 := by native_decide

/-! ## Two-pass edge case — decl isolation under failure

`checkFile`'s promise: one decl's elab or type-check failure
must not poison decls that are structurally independent.  Pass
1 records the per-decl sig-elab outcome separately, and pass 2
processes each decl under the already-populated environment.
A body-level reference to an unknown name (E001) in decl N
shouldn't prevent decl N+1 from elaborating normally.
-/

/-- `fn broken(x : Nat) : Nat = nonexistent_fn(x);` — body
    references a name that's not defined anywhere.  Fails pass 2
    with E001. -/
def brokenBodyDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "broken")
    (params := #[.mk .default_ "x" (var "Nat") zeroSpan])
    (retType := var "Nat")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (var "nonexistent_fn") #[.pos (var "x")] zeroSpan))
    (span := zeroSpan)

/-- `fn good(x : Nat) : Nat = x;` — trivially well-formed. -/
def goodAfterDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "good")
    (params := #[.mk .default_ "x" (var "Nat") zeroSpan])
    (retType := var "Nat")
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (var "x"))
    (span := zeroSpan)

/-- File ordering: good → broken → good.  Expected outcome:
    one result fails (broken), the two `good` decls both ok —
    isolation holds. -/
def isolationFile : File :=
  { span := zeroSpan, decls := #[goodAfterDecl, brokenBodyDecl, goodAfterDecl] }

example : (checkFile isolationFile).size = 3 := by native_decide

example : countOk (checkFile isolationFile) = 2 := by native_decide

example : countOk (checkFile isolationFile) + countElabFail (checkFile isolationFile)
            + countTypeFail (checkFile isolationFile) = 3 := by native_decide

/-- A broken decl at the head of the file still doesn't prevent
    subsequent decls from being processed.  Each decl's result
    is independent. -/
def brokenFirstFile : File :=
  { span := zeroSpan, decls := #[brokenBodyDecl, goodAfterDecl] }

example : countOk (checkFile brokenFirstFile) = 1 := by native_decide

/-- Two broken decls in a row don't amplify — one failure per
    broken decl, no spurious extra failures. -/
def twoBrokenFile : File :=
  { span := zeroSpan,
    decls := #[brokenBodyDecl, brokenBodyDecl, goodAfterDecl] }

example : countOk (checkFile twoBrokenFile) = 1 := by native_decide

example : countOk (checkFile twoBrokenFile) + countElabFail (checkFile twoBrokenFile)
            + countTypeFail (checkFile twoBrokenFile) = 3 := by native_decide

/-! ## Runtime harness -/

def run : IO Unit := Tests.suite "Tests.Elab.CrossDeclTests" do
  let twoDeclResults := checkFile twoDeclFile
  check "two-decl all ok"  true (allOk twoDeclResults)
  check "two-decl count ok"  2 (countOk twoDeclResults)
  check "two-decl no elab fail" 0 (countElabFail twoDeclResults)
  check "two-decl no type fail" 0 (countTypeFail twoDeclResults)
  let reversedResults := checkFile reversedFile
  check "forward-ref all ok"  true (allOk reversedResults)
  check "forward-ref count ok"  2 (countOk reversedResults)
  check "forward-ref no elab fail" 0 (countElabFail reversedResults)

  let emptyResults := checkFile emptyFile
  check "empty file: zero results" 0 emptyResults.size

  let threeDeclResults := checkFile threeDeclFile
  check "three-decl chain all ok"  true (allOk threeDeclResults)
  check "three-decl chain count ok" 3 (countOk threeDeclResults)

  let isolationResults := checkFile isolationFile
  check "isolation: 3 results (one per decl)" 3 isolationResults.size
  check "isolation: 2 decls ok" 2 (countOk isolationResults)

  let brokenFirstResults := checkFile brokenFirstFile
  check "broken-first: good decl survives" 1 (countOk brokenFirstResults)

  let twoBrokenResults := checkFile twoBrokenFile
  check "two-broken: one good still elaborates" 1 (countOk twoBrokenResults)

end Tests.Elab.CrossDeclTests

/-! ## `@[transparent]` attribute flows to ElabDecl + GlobalEnv (Q46)

A fn with `@[transparent]` should produce an `ElabDecl` whose
`transparent` field is `true`; `checkFile` must forward that to
`GlobalEnv.addDecl` so the kernel sees the body as reducible.
These tests pin the pipeline end-to-end without constructing
kernel-level envs by hand.
-/

namespace Tests.Elab.CrossDeclTests.Transparent

open FX.Elab
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests
open Tests.Elab.CrossDeclTests (zeroSpan qualOf)

/-- The `@[transparent]` attribute expression — a bare identifier
    under the `@[...]` prefix.  The parser emits this shape for
    `@[transparent]` on a fn decl. -/
private def transparentAttr : Ast.Expr :=
  .var { parts := #[], final := "transparent", span := zeroSpan }

/-- `@[transparent] fn myZero() : Nat = Nat.Zero;` -/
private def transparentZeroDecl : Decl :=
  .fnDecl
    (attrs := #[transparentAttr])
    (visibility := .private_)
    (name := "myZero")
    (params := #[])
    (retType := .var (qualOf "Nat"))
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.var { parts := #["Nat"], final := "Zero", span := zeroSpan }))
    (span := zeroSpan)

/-- Same body, no attribute — opaque by default. -/
private def opaqueZeroDecl : Decl :=
  .fnDecl
    (attrs := #[])
    (visibility := .private_)
    (name := "otherZero")
    (params := #[])
    (retType := .var (qualOf "Nat"))
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner (.var { parts := #["Nat"], final := "Zero", span := zeroSpan }))
    (span := zeroSpan)

private def transparencyFile : File :=
  { span := zeroSpan, decls := #[transparentZeroDecl, opaqueZeroDecl] }

/-- `elabDecl` sets `transparent := true` on an `@[transparent]`
    fn. -/
example :
    (match elabDecl transparentZeroDecl with
     | .ok elaborated => elaborated.transparent
     | _              => false) = true := by native_decide

/-- `elabDecl` leaves `transparent := false` on an unattributed fn. -/
example :
    (match elabDecl opaqueZeroDecl with
     | .ok elaborated => elaborated.transparent
     | _              => true) = false := by native_decide

/-- End-to-end: `checkFile` builds a `GlobalEnv` whose entries
    carry the transparency flag forward from the source
    attribute.  We reconstruct the env the same way `fxi run`
    does and inspect `unfold?` on both names. -/
private def transparencyEnvAfterCheck : GlobalEnv :=
  let results := checkFile transparencyFile
  results.foldl (init := GlobalEnv.empty) fun acc declResult =>
    match declResult with
    | .okDecl elaborated =>
      acc.addDecl elaborated.name elaborated.type elaborated.body
        (transparent := elaborated.transparent)
    | _ => acc

-- Transparent decl is reachable via `unfold?`.
example : (transparencyEnvAfterCheck.unfold? "myZero").isSome = true := by
  native_decide

-- Opaque decl is NOT reachable via `unfold?` (even though its
-- body is registered).
example : (transparencyEnvAfterCheck.unfold? "otherZero") = none := by
  native_decide

end Tests.Elab.CrossDeclTests.Transparent
