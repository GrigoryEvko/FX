import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Kernel.Inductive
import Tests.ElabSupport
import Tests.Framework

/-!
# Recursion + const-reference tests

`Term.const` plus the two-pass `checkFile` unlock self-recursion
and forward references.  This suite exercises end-to-end:

  * Self-recursive match — `double(Succ(m)) = Succ(Succ(double(m)))`
    runs through the iota rule, with `Term.const "double"`
    resolving via `GlobalEnv.lookupBody?` on every recursive call.
  * Forward reference — decl B appears before decl A in source but
    calls A; pass 1 pre-registers A so pass 2 elab of B resolves
    the ref to `Term.const`.
  * Mutual recursion — `isEven` and `isOdd` each call the other;
    only the two-pass trick makes this typecheck.
  * Const's type-check path — `Term.const` has its type looked up
    from `globalEnv` via the third arg of `infer`/`check`.

## Distinguishing-input strategy

Every recursion test tries MULTIPLE inputs chosen so wrong
implementations can't pass by coincidence.  Examples:

  * `double(n)` — tested at 0, 1, 2, 5, 10.  A "returns 4 on all
    inputs" bug fails at 0 and 1; a "returns n" bug fails at 2+;
    a "returns 2" bug fails at 0, 5, 10.
  * `zeroes(n)` — always returns 0, tested at 0, 3, 7.  Catches
    "recursion wired to wrong argument" bugs because the call
    itself must fire on Succ inputs and terminate on Zero.
  * `add(n, m)` — tested asymmetrically (2+3, 3+2, 1+7, 7+1) to
    catch "recurs on wrong arg" and "returns zero arg" bugs.
-/

namespace Tests.Elab.RecursionTests

open FX.Elab
open FX.Eval
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-! ## Helpers — build unary-Nat AST literals and run files -/

/-- Build `Succ^count Zero` as a surface AST literal. -/
private def natLitExpr : Nat → Ast.Expr
  | 0     => varQual ["Nat"] "Zero"
  | n + 1 => .app (varQual ["Nat"] "Succ") #[.pos (natLitExpr n)] zeroSpan

/-- Check a file with `checkFile`; return `none` if any decl
    failed; otherwise return the evaluated body of the decl at
    `callerIndex` as a unary-Nat count. -/
private def runNatFile (file : File) (callerIndex : Nat) : Option Nat :=
  let results := checkFile file
  let allOk := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allOk then none
  else
    match results[callerIndex]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      unaryNatCount? (evalZeroArgBody evalEnv elaboratedDecl.body)
    | _ => none

/-- Same as `runNatFile` but for Bool results. -/
private def runBoolFile (file : File) (callerIndex : Nat) : Option Bool :=
  let results := checkFile file
  let allOk := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allOk then none
  else
    match results[callerIndex]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      boolFromValue? (evalZeroArgBody evalEnv elaboratedDecl.body)
    | _ => none

/-- Counts how many decl results in an array are `.okDecl`. -/
private def countOk (results : Array DeclResult) : Nat :=
  results.foldl (init := 0) fun acc declResult =>
    match declResult with
    | .okDecl _ => acc + 1
    | _         => acc

/-! ## `double(n)` — doubles a unary Nat via self-recursion -/

/-- `fn double(n: Nat) : Nat = match n;
       Zero => Nat.Zero;
       Succ(m) => Nat.Succ(Nat.Succ(double(m)));
     end match;` -/
private def doubleDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "double")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.match_ (varName "n") #[
        .mk (.ctor (qualOf "Zero") #[] zeroSpan) none
            (varQual ["Nat"] "Zero") zeroSpan,
        .mk (.ctor (qualOf "Succ") #[.var "m" zeroSpan] zeroSpan) none
            (.app (varQual ["Nat"] "Succ")
              #[.pos
                (.app (varQual ["Nat"] "Succ")
                  #[.pos
                    (.app (varName "double")
                      #[.pos (varName "m")] zeroSpan)]
                  zeroSpan)]
              zeroSpan)
            zeroSpan
      ] zeroSpan))
    (span := zeroSpan)

/-- `fn callDouble() : Nat = double(Nat.Succ(Nat.Succ(Nat.Zero)));` -/
private def callDoubleDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "result")
    (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (varName "double") #[.pos (natLitExpr 2)] zeroSpan))
    (span := zeroSpan)

/-- Elaborate the `double` + caller file, then evaluate the caller
    and return the resulting unary-Nat count.  `none` if anything
    fails. -/
private def runDoubleCall (inputCount : Nat) : Option Nat :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := natTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "double") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  runNatFile { decls := #[doubleDecl, caller], span := zeroSpan } 1

-- Coverage across inputs 0..10 rules out constant-return and
-- identity-function impostors.  A broken `double` that returns `n`
-- (identity) fails at 1/2/5/10.  A broken `double` that returns a
-- constant 0 fails at 1/2/5/10.  A broken `double` that returns
-- `2` regardless of input fails at 0/5/10.
example : runDoubleCall 0 = some 0 := by native_decide
example : runDoubleCall 1 = some 2 := by native_decide
example : runDoubleCall 2 = some 4 := by native_decide
example : runDoubleCall 3 = some 6 := by native_decide
example : runDoubleCall 5 = some 10 := by native_decide
example : runDoubleCall 10 = some 20 := by native_decide

/-! ## `zeroes(n)` — constant-zero self-recursion

Catches "recursion wired to wrong argument" bugs that a
monotone-output test like `double` would miss.  The recursive
call must fire on every `Succ` step, so a bug that short-circuits
at the first Succ still hits a runtime shape (Zero) test can
catch. -/

/-- `fn zeroes(n: Nat) : Nat = match n;
       Zero => Nat.Zero;
       Succ(k) => zeroes(k);
     end match;` -/
private def zeroesDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "zeroes")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.match_ (varName "n") #[
        .mk (.ctor (qualOf "Zero") #[] zeroSpan) none
            (varQual ["Nat"] "Zero") zeroSpan,
        .mk (.ctor (qualOf "Succ") #[.var "k" zeroSpan] zeroSpan) none
            (.app (varName "zeroes") #[.pos (varName "k")] zeroSpan)
            zeroSpan
      ] zeroSpan))
    (span := zeroSpan)

private def runZeroesCall (inputCount : Nat) : Option Nat :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := natTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "zeroes") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  runNatFile { decls := #[zeroesDecl, caller], span := zeroSpan } 1

-- Multi-input: a broken `zeroes` returning the input would fail at
-- 3 and 7 (identity test); verifies the recursive step fires.
example : runZeroesCall 0 = some 0 := by native_decide
example : runZeroesCall 3 = some 0 := by native_decide
example : runZeroesCall 7 = some 0 := by native_decide

/-! ## `runTwiceDouble` — two calls to the same recursive fn

`fn fourTimes(n: Nat) : Nat = double(double(n));`  Two `const`
references to `double` in one body + nested app.  Catches bugs
where the const cache is stale between calls or where
nested-call environment threading drops the outer context. -/

/-- `fn fourTimes(n: Nat) : Nat = double(double(n));` -/
private def fourTimesDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "fourTimes")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (varName "double")
        #[.pos (.app (varName "double") #[.pos (varName "n")] zeroSpan)]
        zeroSpan))
    (span := zeroSpan)

private def runFourTimesCall (inputCount : Nat) : Option Nat :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := natTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "fourTimes") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  runNatFile { decls := #[doubleDecl, fourTimesDecl, caller], span := zeroSpan } 2

example : runFourTimesCall 0 = some 0 := by native_decide
example : runFourTimesCall 1 = some 4 := by native_decide
example : runFourTimesCall 3 = some 12 := by native_decide

/-! ## Forward references — callee declared AFTER caller

The `forwardOrderFile` puts the caller BEFORE the callee in source.
Pass 1 pre-registers both signatures; pass 2 elabs caller's body
with a `Term.const "double"` that resolves at eval time.

We test BOTH elab success (two-pass trick works at all) AND eval
(the resolved `const` actually reduces to the right value) across
multiple inputs.  The original suite only tested the fixed
`double(2) = 4` case; a broken forward-ref resolution that
happened to return 4 on input 2 would have slipped through. -/

/-- File with caller BEFORE callee — forces forward-ref path. -/
private def forwardDoubleFile (inputCount : Nat) : File :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := natTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "double") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  -- caller at index 0; doubleDecl at index 1
  { decls := #[caller, doubleDecl], span := zeroSpan }

/-- Run forward-ordered file; caller lives at index 0. -/
private def runForwardDoubleCall (inputCount : Nat) : Option Nat :=
  runNatFile (forwardDoubleFile inputCount) 0

-- The forward-reference path must compute the SAME values as the
-- declared-first path.  Multiple inputs guarantee the ref isn't
-- hardcoded to a specific value.
example : runForwardDoubleCall 0 = some 0 := by native_decide
example : runForwardDoubleCall 1 = some 2 := by native_decide
example : runForwardDoubleCall 2 = some 4 := by native_decide
example : runForwardDoubleCall 4 = some 8 := by native_decide
example : runForwardDoubleCall 7 = some 14 := by native_decide

/-- Forward reference keeps on working when the caller is
    declared last — both orderings should produce identical
    results on the same input. -/
example :
    runForwardDoubleCall 5 = runDoubleCall 5 := by native_decide

/-! ## Forward-ref rejection — unknown target

If caller B references a name `nonexistent_fn` that doesn't
appear in the file, pass 1 never registers it.  Pass 2 elabs
B's body, finds the var unbound, and throws E001.  `checkFile`
surfaces this as `.elabFail`. -/

private def callsUnknownDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "callsUnknown") (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (varName "nonexistent_fn")
        #[.pos (natLitExpr 1)] zeroSpan))
    (span := zeroSpan)

private def unknownTargetFile : File :=
  { decls := #[callsUnknownDecl, doubleDecl], span := zeroSpan }

-- The `callsUnknown` decl fails pass 2 (elab can't resolve the name);
-- `double` beside it still elaborates — checkFile isolates failures.
example : countOk (checkFile unknownTargetFile) = 1 := by native_decide

/-! ## `add(n, m)` — two-arg self-recursion, asymmetric inputs -/

/-- `fn add(n: Nat, m: Nat) : Nat = match n;
       Zero => m;
       Succ(k) => Nat.Succ(add(k, m));
     end match;` -/
private def addDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "add")
    (params := #[
      .mk .default_ "n" natTy zeroSpan,
      .mk .default_ "m" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.match_ (varName "n") #[
        .mk (.ctor (qualOf "Zero") #[] zeroSpan) none (varName "m") zeroSpan,
        .mk (.ctor (qualOf "Succ") #[.var "k" zeroSpan] zeroSpan) none
            (.app (varQual ["Nat"] "Succ")
              #[.pos
                (.app (varName "add")
                  #[.pos (varName "k"), .pos (varName "m")] zeroSpan)]
              zeroSpan)
            zeroSpan
      ] zeroSpan))
    (span := zeroSpan)

private def runAddCall (leftCount rightCount : Nat) : Option Nat :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := natTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "add")
          #[.pos (natLitExpr leftCount), .pos (natLitExpr rightCount)] zeroSpan))
      (span := zeroSpan)
  runNatFile { decls := #[addDecl, caller], span := zeroSpan } 1

-- Asymmetric pairs catch "returns left arg", "returns right arg",
-- "recurs on wrong arg" (e.g. `Succ(k) => add(n, m)`).  Using 0
-- on one side + nonzero on the other exposes the Zero base case.
example : runAddCall 0 0 = some 0 := by native_decide
example : runAddCall 0 3 = some 3 := by native_decide
example : runAddCall 3 0 = some 3 := by native_decide
example : runAddCall 2 3 = some 5 := by native_decide
example : runAddCall 3 2 = some 5 := by native_decide
example : runAddCall 1 7 = some 8 := by native_decide
example : runAddCall 7 1 = some 8 := by native_decide

/-! ## Mutual recursion — `isEven` / `isOdd`

Each refers to the other via `Term.const`.  Only the two-pass
`checkFile` makes this typecheck: pass 1 registers BOTH
signatures before either body is elaborated.  This exercises
the same `const` resolution path as self-ref, but with two
distinct names in flight simultaneously.

Bodies:
  `fn isEven(n: Nat) : Bool =
     match n; Zero => Bool.True; Succ(k) => isOdd(k); end match;`
  `fn isOdd(n: Nat) : Bool =
     match n; Zero => Bool.False; Succ(k) => isEven(k); end match;` -/

private def isEvenDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "isEven")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.match_ (varName "n") #[
        .mk (.ctor (qualOf "Zero") #[] zeroSpan) none
            (varQual ["Bool"] "True") zeroSpan,
        .mk (.ctor (qualOf "Succ") #[.var "k" zeroSpan] zeroSpan) none
            (.app (varName "isOdd") #[.pos (varName "k")] zeroSpan)
            zeroSpan
      ] zeroSpan))
    (span := zeroSpan)

private def isOddDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "isOdd")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.match_ (varName "n") #[
        .mk (.ctor (qualOf "Zero") #[] zeroSpan) none
            (varQual ["Bool"] "False") zeroSpan,
        .mk (.ctor (qualOf "Succ") #[.var "k" zeroSpan] zeroSpan) none
            (.app (varName "isEven") #[.pos (varName "k")] zeroSpan)
            zeroSpan
      ] zeroSpan))
    (span := zeroSpan)

/-- Both decls must elaborate and kernel-check together. -/
example :
    countOk (checkFile
      { decls := #[isEvenDecl, isOddDecl], span := zeroSpan }) = 2 := by
  native_decide

/-- Reverse source order — each decl still forward-refs the other.
    Pass 1's sig registration is what makes BOTH orderings work. -/
example :
    countOk (checkFile
      { decls := #[isOddDecl, isEvenDecl], span := zeroSpan }) = 2 := by
  native_decide

/-- Evaluate `isEven(input)` in the mutual-rec file. -/
private def runIsEvenCall (inputCount : Nat) : Option Bool :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := boolTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "isEven") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  runBoolFile
    { decls := #[isEvenDecl, isOddDecl, caller], span := zeroSpan } 2

/-- Evaluate `isOdd(input)` in the mutual-rec file. -/
private def runIsOddCall (inputCount : Nat) : Option Bool :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := boolTy)
      (effects := #[])
    (specs := #[])
    (body :=.oneLiner
        (.app (varName "isOdd") #[.pos (natLitExpr inputCount)] zeroSpan))
      (span := zeroSpan)
  runBoolFile
    { decls := #[isEvenDecl, isOddDecl, caller], span := zeroSpan } 2

-- Alternating truth values across many inputs: a broken mutual-ref
-- that always hit one of the two bodies would produce a constant.
-- Testing at 0, 1, 2, 3, 4, 5, 6 verifies both directions of the
-- bounce plus the shared Zero-base.
example : runIsEvenCall 0 = some true  := by native_decide
example : runIsEvenCall 1 = some false := by native_decide
example : runIsEvenCall 2 = some true  := by native_decide
example : runIsEvenCall 3 = some false := by native_decide
example : runIsEvenCall 4 = some true  := by native_decide
example : runIsEvenCall 5 = some false := by native_decide
example : runIsEvenCall 6 = some true  := by native_decide

example : runIsOddCall 0 = some false := by native_decide
example : runIsOddCall 1 = some true  := by native_decide
example : runIsOddCall 2 = some false := by native_decide
example : runIsOddCall 3 = some true  := by native_decide
example : runIsOddCall 4 = some false := by native_decide
example : runIsOddCall 5 = some true  := by native_decide

/-- `isEven(n) ≠ isOdd(n)` for every tested n — the two mutuals
    are truly each other's complement, not accidentally equal. -/
example : runIsEvenCall 3 ≠ runIsOddCall 3 := by native_decide
example : runIsEvenCall 6 ≠ runIsOddCall 6 := by native_decide

/-! ## Backward order preserved for self-recursion

The original `callDoubleDecl` file placed `double` FIRST and the
caller SECOND, which exercises the plain (non-forward) ordering.
This test verifies the caller at index 0 path still produces the
same value the forward-ordered file does — a sanity check that
our forward/backward harness isn't silently diverging. -/

private def backwardOrderFile : File :=
  { decls := #[doubleDecl, callDoubleDecl], span := zeroSpan }

private def backwardRefReducesTo4 : Bool :=
  match runNatFile backwardOrderFile 1 with
  | some 4 => true
  | _      => false

example : backwardRefReducesTo4 = true := by native_decide

/-! ## Runtime suite

Each `check` doubles as a regression anchor — the runtime path
should mirror the compile-time `example` results above; if they
disagree, one of `native_decide` vs runtime elab/eval is broken. -/

def run : IO Unit := Tests.suite "Tests.Elab.RecursionTests" do
  -- double: multi-input coverage
  Tests.check "double(0) = 0"   (some 0)  (runDoubleCall 0)
  Tests.check "double(1) = 2"   (some 2)  (runDoubleCall 1)
  Tests.check "double(2) = 4"   (some 4)  (runDoubleCall 2)
  Tests.check "double(3) = 6"   (some 6)  (runDoubleCall 3)
  Tests.check "double(5) = 10"  (some 10) (runDoubleCall 5)
  Tests.check "double(10) = 20" (some 20) (runDoubleCall 10)

  -- zeroes: constant-output catches wrong-arg recursion
  Tests.check "zeroes(0) = 0" (some 0) (runZeroesCall 0)
  Tests.check "zeroes(3) = 0" (some 0) (runZeroesCall 3)
  Tests.check "zeroes(7) = 0" (some 0) (runZeroesCall 7)

  -- fourTimes: composition via `double(double(n))`
  Tests.check "fourTimes(0) = 0"  (some 0)  (runFourTimesCall 0)
  Tests.check "fourTimes(1) = 4"  (some 4)  (runFourTimesCall 1)
  Tests.check "fourTimes(3) = 12" (some 12) (runFourTimesCall 3)

  -- forward-ref: multi-input eval (not just elab)
  Tests.check "forward-ref double(0) = 0"  (some 0)  (runForwardDoubleCall 0)
  Tests.check "forward-ref double(1) = 2"  (some 2)  (runForwardDoubleCall 1)
  Tests.check "forward-ref double(2) = 4"  (some 4)  (runForwardDoubleCall 2)
  Tests.check "forward-ref double(4) = 8"  (some 8)  (runForwardDoubleCall 4)
  Tests.check "forward-ref double(7) = 14" (some 14) (runForwardDoubleCall 7)
  Tests.check "forward/backward orderings agree on double(5)"
    (runDoubleCall 5) (runForwardDoubleCall 5)

  -- forward-ref rejection: unknown target fails elab of that one decl
  Tests.check "unknown forward-ref fails only its own decl"
    1 (countOk (checkFile unknownTargetFile))

  -- add: asymmetric pairs
  Tests.check "add(0, 0) = 0" (some 0) (runAddCall 0 0)
  Tests.check "add(0, 3) = 3" (some 3) (runAddCall 0 3)
  Tests.check "add(3, 0) = 3" (some 3) (runAddCall 3 0)
  Tests.check "add(2, 3) = 5" (some 5) (runAddCall 2 3)
  Tests.check "add(3, 2) = 5" (some 5) (runAddCall 3 2)
  Tests.check "add(1, 7) = 8" (some 8) (runAddCall 1 7)
  Tests.check "add(7, 1) = 8" (some 8) (runAddCall 7 1)

  -- mutual rec: isEven/isOdd elab succeeds in both source orders
  Tests.check "mutual rec elabs (isEven, isOdd)"
    2 (countOk (checkFile { decls := #[isEvenDecl, isOddDecl], span := zeroSpan }))
  Tests.check "mutual rec elabs (isOdd, isEven) — reverse order"
    2 (countOk (checkFile { decls := #[isOddDecl, isEvenDecl], span := zeroSpan }))

  -- mutual rec: eval alternates truth values
  Tests.check "isEven(0) = true"  (some true)  (runIsEvenCall 0)
  Tests.check "isEven(1) = false" (some false) (runIsEvenCall 1)
  Tests.check "isEven(2) = true"  (some true)  (runIsEvenCall 2)
  Tests.check "isEven(3) = false" (some false) (runIsEvenCall 3)
  Tests.check "isEven(6) = true"  (some true)  (runIsEvenCall 6)
  Tests.check "isOdd(0) = false"  (some false) (runIsOddCall 0)
  Tests.check "isOdd(1) = true"   (some true)  (runIsOddCall 1)
  Tests.check "isOdd(4) = false"  (some false) (runIsOddCall 4)
  Tests.check "isOdd(5) = true"   (some true)  (runIsOddCall 5)

  -- backward-ordered self-ref file still resolves
  Tests.checkTrue "backward-order result = 4" backwardRefReducesTo4

end Tests.Elab.RecursionTests
