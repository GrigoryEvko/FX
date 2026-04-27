import FX.Elab.Elaborate
import FX.Eval.Interp
import FX.Kernel.Inductive
import FX.Kernel.Reduction
import Tests.ElabSupport
import Tests.Framework

/-!
# Match elaboration tests (B7)

Exercises match-expression elaboration to `Term.indRec`.

Shapes covered:

  * Basic Bool match — both arm orderings (arms reorder to ctor-index
    order in the emitted `indRec` methods).
  * Nat match with `Succ(m)` — self-referential ctor arg introduces
    an extra unused lambda for the recursive-result binder.
  * Qualified vs unqualified ctor names in patterns.
  * Non-exhaustive / guarded / nested-pattern / missing-result-type
    / parameterized-spec rejections (E010).
  * End-to-end: `elabAndCheck` passes on realistic `fnDecl`s, and
    `Eval.Interp.eval` + `Term.normalize` produce the expected
    iota-reduced result.

## Falsifiability discipline

Every `decl_ok` assertion is paired with one or more eval-based
assertions that fire the decl on at least TWO distinct scrutinees
producing distinct return values.  A broken elab that silently
picked a fixed arm, dropped the payload binder, or always returned
a default would be caught by the eval tests — `decl_ok` alone is
not enough.  See the `runUnaryCall` / `runBoolCall` harnesses.
-/

namespace Tests.Elab.MatchExprTests

open FX.Elab
open FX.Eval
open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast
open Tests.ElabSupport

/-- Compare elab result to an expected Term via `BEq Term`. -/
private def elabEq (elabResult : Except ElabError Term) (expected : Term) : Bool :=
  match elabResult with
  | .ok resultTerm => resultTerm == expected
  | _              => false

private def runWith (expected : Option Term) (expr : Expr)
    : Except ElabError Term :=
  elabExpr GlobalEnv.empty Scope.empty expected expr

/-! ## Pattern / arm / literal builders

Default arguments on `pctor` / `pctorQ` keep nullary-ctor patterns
concise (`pctor "True"`) without shadowing the arg-bearing form
(`pctor "Succ" [pvar "m"]`).
-/

private def pvar (name : String) : Pattern := .var name zeroSpan
private def pwild : Pattern := .wildcard zeroSpan
private def pctor (name : String) (args : List Pattern := []) : Pattern :=
  .ctor (qualOf name) args.toArray zeroSpan
private def pctorQ (path : List String) (name : String)
    (args : List Pattern := []) : Pattern :=
  .ctor (qualPath path name) args.toArray zeroSpan

private def arm (pattern : Pattern) (body : Expr) : MatchArm :=
  .mk pattern none body zeroSpan

private def armWithGuard (pattern : Pattern) (guard : Expr) (body : Expr) : MatchArm :=
  .mk pattern (some guard) body zeroSpan

private def matchExpr (scrutinee : Expr) (arms : List MatchArm) : Expr :=
  .match_ scrutinee arms.toArray zeroSpan

/-! ## Expected-term builders -/

private def natCtor (ctorIndex : Nat) (valueArgs : List Term := []) : Term :=
  .ctor "Nat" ctorIndex [] valueArgs
private def natKernelZero : Term := natCtor 0
private def natOne : Term := natCtor 1 [natKernelZero]

private def boolCtor (ctorIndex : Nat) : Term := .ctor "Bool" ctorIndex [] []

/-- Expected motive for a match with non-dependent Nat return type. -/
private def natMotive : Term :=
  .lam Grade.default (.ind "Bool" []) (Term.shift 0 1 (.ind "Nat" []))

/-! ## AST builders for unary-Nat literals reaching through call sites -/

/-- Build `Nat.Succ^n Nat.Zero` as a surface expression.  Mirrors
    the pattern used by RecursionTests to construct scrutinees of
    varying Succ-depth. -/
private def natLitExpr : Nat → Ast.Expr
  | 0     => varQual ["Nat"] "Zero"
  | n + 1 => .app (varQual ["Nat"] "Succ") #[.pos (natLitExpr n)] zeroSpan

/-- Build `Bool.True` or `Bool.False` as a surface expression. -/
private def boolLitExpr : Bool → Ast.Expr
  | true  => varQual ["Bool"] "True"
  | false => varQual ["Bool"] "False"

/-! ## Eval harnesses for end-to-end arm-selection checks -/

/-- Classify a Value as a Bool: Some true / Some false / none for
    anything else (neutral, non-Bool ctor, stuck indRec).  Used by
    eval assertions that want to distinguish `true` from `false`
    from "elaboration silently produced garbage." -/
private def asBool? : Value → Option Bool
  | .ctor "Bool" 0 _ _ => some false
  | .ctor "Bool" 1 _ _ => some true
  | _                  => none

/-- Elaborate a two-decl file `[fnDecl, caller]` where `caller` is
    synthesized here to be `fn result() : retTy = fnName(arg);`.
    Returns the evaluated body of `caller`, or `none` if any decl
    failed to elab.  Shared by the Nat and Bool call harnesses
    below — separating the scaffolding from the retTy/arg shape
    keeps the two call helpers compact. -/
private def runFnCall (fnDecl : Decl) (fnName : String) (retTy : Ast.Expr)
    (argExpr : Ast.Expr) : Option Value :=
  let caller : Decl :=
    .fnDecl (attrs := #[]) (visibility := .private_)
      (name := "result") (params := #[])
      (retType := retTy)
      (effects := #[])
      (specs := #[])
      (body := .oneLiner
        (.app (varName fnName) #[.pos argExpr] zeroSpan))
      (span := zeroSpan)
  let file : File := { decls := #[fnDecl, caller], span := zeroSpan }
  let results := checkFile file
  let allOk := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allOk then none
  else
    match results[1]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      some (evalZeroArgBody evalEnv elaboratedDecl.body)
    | _ => none

/-- Elab `fnDecl` (which takes a single Nat arg and returns Nat),
    call it with `Succ^inputCount Zero`, and return the evaluated
    result as a unary-Nat count.  None if elab failed or the
    evaluated value wasn't a well-formed Nat. -/
private def runUnaryCall (fnDecl : Decl) (fnName : String) (inputCount : Nat)
    : Option Nat :=
  match runFnCall fnDecl fnName natTy (natLitExpr inputCount) with
  | some value => unaryNatCount? value
  | none       => none

/-- Elab `fnDecl` (which takes a single Nat arg and returns Bool),
    call it with `Succ^inputCount Zero`, and return the evaluated
    Bool result.  Distinguishes `some true` from `some false` from
    `none` (elab failed / stuck eval) so tests can pin arm selection. -/
private def runNatToBoolCall (fnDecl : Decl) (fnName : String)
    (inputCount : Nat) : Option Bool :=
  match runFnCall fnDecl fnName boolTy (natLitExpr inputCount) with
  | some value => asBool? value
  | none       => none

/-- Elab `fnDecl` (which takes a single Bool arg and returns Bool),
    call it with the given Bool, and return the evaluated Bool. -/
private def runBoolToBoolCall (fnDecl : Decl) (fnName : String)
    (inputBool : Bool) : Option Bool :=
  match runFnCall fnDecl fnName boolTy (boolLitExpr inputBool) with
  | some value => asBool? value
  | none       => none

/-- Elab `fnDecl` (which takes a single Bool arg and returns Nat),
    call it with the given Bool, and return the evaluated Nat as
    a unary count. -/
private def runBoolToNatCall (fnDecl : Decl) (fnName : String)
    (inputBool : Bool) : Option Nat :=
  match runFnCall fnDecl fnName natTy (boolLitExpr inputBool) with
  | some value => unaryNatCount? value
  | none       => none

/-! ## Direct-elab structural tests -/

/-- Bare match without an expected type → E010. -/
example :
  elabErrCode (runWith none
    (matchExpr trueLit
       [arm (pctor "True") (natLit 1), arm (pctor "False") (natLit 0)])) "E010" := by
  native_decide

/-- `match true; True => 1; False => 0; end match` with expected Nat
    elaborates to `indRec "Bool" motive [Zero, Succ Zero] True`.
    Arms in True-first source order get reordered to ctor-index
    order (False=0, True=1) in the emitted `methods` list. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (pctor "True") (natLit 1), arm (pctor "False") (natLit 0)]))
    (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)) := by
  native_decide

/-- Same match, arms already in ctor order: same emitted term. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (pctor "False") (natLit 0), arm (pctor "True") (natLit 1)]))
    (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)) := by
  native_decide

/-- Qualified ctor patterns work identically to unqualified. -/
example :
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (pctorQ ["Bool"] "True")  (natLit 1),
        arm (pctorQ ["Bool"] "False") (natLit 0)]))
    (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)) := by
  native_decide

/-- Non-exhaustive match (missing `False` arm) → E010. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit [arm (pctor "True") (natLit 1)])) "E010" := by
  native_decide

/-- Non-exhaustive match on Nat (missing `Succ` arm) → E010.  A
    previous regression silently allowed Nat matches with only
    `Zero` because exhaustiveness was checked against a partial
    registry; pinning both directions (Bool-missing-False and
    Nat-missing-Succ) catches reintroductions. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr (natLit 0)
      [arm (pctor "Zero") (natLit 0)])) "E010" := by
  native_decide

/-- Non-exhaustive match on Nat (missing `Zero` arm) → E010. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr (natLit 0)
      [arm (pctor "Succ" [pwild]) (natLit 0)])) "E010" := by
  native_decide

/-- Guarded arm → E010 (M2 deferred). -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [armWithGuard (pctor "True")  trueLit (natLit 1),
        arm          (pctor "False") (natLit 0)])) "E010" := by
  native_decide

/-- Variable arm as catch-all → E010: every ctor must have a
    dedicated arm in M2. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit [arm (pvar "x") (natLit 1)])) "E010" := by
  native_decide

/-- Literal pattern (`0 => ...`) → E010.  Literal patterns parse
    per fx_grammar.md §8 but Phase 2.2's match compilation (B7)
    only handles constructor + wildcard + variable patterns;
    decidable-literal matching lands with the numeric-primitive
    work of D2. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr (natLit 0)
       [arm (.literal (.kw .trueKw) zeroSpan) (natLit 1),
        arm (pctor "Succ" [pwild])            (natLit 0)])) "E010" := by
  native_decide

/-- Tuple pattern (`(a, b) => ...`) → E010.  Tuple patterns need
    record-translation (B8) to desugar into sequential Sigma
    destructures; no kernel path exists yet. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (.tuple #[pvar "a", pvar "b"] zeroSpan) (natLit 1),
        arm (pctor "False")                         (natLit 0)])) "E010" := by
  native_decide

/-- Ascribed pattern (`(x : T) => ...`) → E010.  Ascribed
    patterns are useful for disambiguation once refinements land
    (M5) but have no place in the current decidable-exhaustive
    match compilation. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (.ascribed (pvar "x") boolTy zeroSpan) (natLit 1),
        arm (pctor "False")                         (natLit 0)])) "E010" := by
  native_decide

/-- Unknown ctor in pattern (`Foo => ...` where Foo isn't a
    Bool ctor) → E010.  The elaborator's `resolveQualCtor?`
    returns `none` and the arm fails ctor-index resolution. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (pctor "Foo")   (natLit 1),
        arm (pctor "False") (natLit 0)])) "E010" := by
  native_decide

/-- Zero arms → E010: `resolveMatchSpec?` cannot infer the
    scrutinee's inductive family from no ctor references.
    Important because the parser accepts `match e; end match`
    syntactically (a surface `match` on an `Empty` scrutinee
    is the only case where zero arms is semantically well-
    formed, and even that still has no spec-resolving arm). -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit [])) "E010" := by
  native_decide

/-- Wildcard-only arm (no ctor ref) → E010.  `resolveMatchSpec?`
    walks arms looking for a ctor pattern to anchor the inductive
    family; a wildcard arm alone fails that resolution.  Pinning
    the error site prevents accidental wildcard-as-catchall
    acceptance if the resolver changes. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit [arm pwild (natLit 1)])) "E010" := by
  native_decide

/-- Mixing ctors from different inductive families in one match
    → E010.  The first resolvable arm pins the family; the second
    arm refers to a ctor that doesn't belong to that family, so
    ctor-index lookup fails the exhaustiveness scan. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr trueLit
       [arm (pctor "True")  (natLit 1),
        arm (pctor "Zero")  (natLit 0)])) "E010" := by
  native_decide

/-- Nat match with self-referential `Succ(m)` pattern.  The method
    for `Succ` becomes `\(m : Nat). \(_rec : Nat). m` — the
    recursive-result lambda sits between the user's bound name and
    the body, so `m` is `var 1` after the extra binder.  This test
    catches a missing-rec-binder bug (method would be
    `\m. m = var 0`) and a swapped-binder bug (method would be
    `\m. \_rec. _rec = var 0`). -/
example :
  let succMethod : Term :=
    .lam Grade.default (.ind "Nat" [])
      (.lam Grade.default (.ind "Nat" [])
        (Term.var 1))
  let natMatchMotive : Term :=
    .lam Grade.default (.ind "Nat" []) (Term.shift 0 1 (.ind "Nat" []))
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr (natLit 0)
       [arm (pctor "Zero")             (natLit 0),
        arm (pctor "Succ" [pvar "m"])  (.var (qualOf "m"))]))
    (Term.indRec "Nat" natMatchMotive [natKernelZero, succMethod] natKernelZero) := by
  native_decide

/-- Wildcard pattern arg emits the same binder shape but never
    references it. -/
example :
  let succMethod : Term :=
    .lam Grade.default (.ind "Nat" [])
      (.lam Grade.default (.ind "Nat" [])
        natKernelZero)
  let natMatchMotive : Term :=
    .lam Grade.default (.ind "Nat" []) (Term.shift 0 1 (.ind "Nat" []))
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr (natLit 0)
       [arm (pctor "Zero")          (natLit 0),
        arm (pctor "Succ" [pwild])  (natLit 0)]))
    (Term.indRec "Nat" natMatchMotive [natKernelZero, succMethod] natKernelZero) := by
  native_decide

/-! ## Unit inductive coverage

Unit has one ctor (`tt`, index 0) with zero args.  Matching on it
exercises the "single arm is exhaustive" path; missing the arm
is non-exhaustive. -/

/-- `match Unit.tt; tt => 42 end match` with expected Nat.  Even
    though a match on Unit is tautological, exercising it prevents
    a regression where single-ctor specs get a spurious second-arm
    requirement. -/
example :
  let unitMotive : Term :=
    .lam Grade.default (.ind "Unit" []) (Term.shift 0 1 (.ind "Nat" []))
  elabEq (runWith (some (.ind "Nat" []))
    (matchExpr (.var (qualPath ["Unit"] "tt"))
       [arm (pctor "tt") (natLit 0)]))
    (Term.indRec "Unit" unitMotive [natKernelZero] (.ctor "Unit" 0 [] [])) := by
  native_decide

/-- Non-exhaustive Unit match (no arms at all after spec is known
    — can't be resolved without an arm) → E010. -/
example :
  elabErrCode (runWith (some (.ind "Nat" []))
    (matchExpr (.var (qualPath ["Unit"] "tt")) [])) "E010" := by
  native_decide

/-! ## fnDecl integration (elab + kernel check + eval) -/

/-- `fn neg(b: Bool) : Bool = match b; True => false; False => true; end match;` -/
private def negDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "neg")
    (params := #[.mk .default_ "b" boolTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (matchExpr (.var (qualOf "b"))
        [arm (pctor "True") falseLit, arm (pctor "False") trueLit]))
    (span := zeroSpan)

example : decl_ok negDecl := by native_decide

/-- `neg(True) = False`.  Without this, a broken elab that always
    picked arm[0] (False method) would return `False` for both
    inputs — `decl_ok` alone can't distinguish. -/
example : runBoolToBoolCall negDecl "neg" true  = some false := by native_decide

/-- `neg(False) = True`.  Paired with the above, verifies arm
    SELECTION actually flips with the scrutinee. -/
example : runBoolToBoolCall negDecl "neg" false = some true  := by native_decide

/-- `fn pred(n: Nat) : Nat = match n; Zero => Zero; Succ(m) => m; end match;` -/
private def predDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "pred")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (matchExpr (.var (qualOf "n"))
        [arm (pctor "Zero") (.var (qualPath ["Nat"] "Zero")),
         arm (pctor "Succ" [pvar "m"]) (.var (qualOf "m"))]))
    (span := zeroSpan)

example : decl_ok predDecl := by native_decide

/-- `pred(Zero) = Zero`.  Arm 0 return path. -/
example : runUnaryCall predDecl "pred" 0 = some 0 := by native_decide

/-- `pred(Succ(Zero)) = Zero`.  Arm 1 return path with `m = Zero`.
    Catches a dropped-`k`-binder bug: if elab emitted the Succ
    method without binding `m`, the body's `var 1` would resolve
    to the caller's scope (or to `n` shifted), producing garbage. -/
example : runUnaryCall predDecl "pred" 1 = some 0 := by native_decide

/-- `pred(Succ(Succ(Zero))) = Succ(Zero)`.  Confirms `m` actually
    carries the inner payload — a swapped-binder bug (where the
    body references the rec-result slot, var 0) would return
    stuck/garbage instead of `Succ(Zero)`. -/
example : runUnaryCall predDecl "pred" 2 = some 1 := by native_decide

/-- `pred(Succ(Succ(Succ(Zero)))) = Succ(Succ(Zero))`.  Deeper
    Succ chain rules out any lookup bug that only surfaces at
    one specific depth. -/
example : runUnaryCall predDecl "pred" 3 = some 2 := by native_decide

/-- `fn isZero(n: Nat) : Bool = match n; Zero => true; Succ(_) => false; end match;` -/
private def isZeroDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "isZero")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (matchExpr (.var (qualOf "n"))
        [arm (pctor "Zero") trueLit,
         arm (pctor "Succ" [pwild]) falseLit]))
    (span := zeroSpan)

example : decl_ok isZeroDecl := by native_decide

/-- `isZero(Zero) = True`.  Arm 0 return path (baseline). -/
example : runNatToBoolCall isZeroDecl "isZero" 0 = some true  := by native_decide

/-- `isZero(Succ(Zero)) = False`.  Arm 1 with wildcard payload;
    verifies arm selection flips when scrutinee ctor changes. -/
example : runNatToBoolCall isZeroDecl "isZero" 1 = some false := by native_decide

/-- `isZero(Succ(Succ(Zero))) = False`.  The wildcard payload
    shouldn't affect outcome — returns `false` regardless of
    Succ depth. -/
example : runNatToBoolCall isZeroDecl "isZero" 2 = some false := by native_decide

/-- `fn isSucc(n: Nat) : Bool = match n; Zero => false; Succ(_) => true; end match;`
    Inverse of `isZero` — pairs with the above so that a bug
    "always returns true" on Bool-result matches can't hide in
    one of them.  Both helpers share scrutinee plumbing but
    return OPPOSITE constants per arm; a swapped-method elab
    would flip the sense of exactly one of them. -/
private def isSuccDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "isSucc")
    (params := #[.mk .default_ "n" natTy zeroSpan])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (matchExpr (.var (qualOf "n"))
        [arm (pctor "Zero") falseLit,
         arm (pctor "Succ" [pwild]) trueLit]))
    (span := zeroSpan)

example : decl_ok isSuccDecl := by native_decide
example : runNatToBoolCall isSuccDecl "isSucc" 0 = some false := by native_decide
example : runNatToBoolCall isSuccDecl "isSucc" 1 = some true  := by native_decide
example : runNatToBoolCall isSuccDecl "isSucc" 5 = some true  := by native_decide

/-- Match inside a block body, after a `let`:
    `fn f(b: Bool) : Nat = begin fn
       let x : Bool = b;
       return match x; True => 1; False => 0; end match;
     end fn;`  Verifies expected-type propagation through
    `elabStmtChain` + scope shift. -/
private def letThenMatchDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "letThenMatch")
    (params := #[.mk .default_ "b" boolTy zeroSpan])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.block
      #[.letStmt (.var "x" zeroSpan) (some boolTy)
          (.var (qualOf "b")) zeroSpan]
      (matchExpr (.var (qualOf "x"))
        [arm (pctor "True") (natLit 1), arm (pctor "False") (natLit 0)]))
    (span := zeroSpan)

example : decl_ok letThenMatchDecl := by native_decide

/-- `letThenMatch(True) = 1`.  Through the let-stmt shift, the
    match sees a Bool-typed binder and selects the True arm. -/
example : runBoolToNatCall letThenMatchDecl "letThenMatch" true  = some 1 := by
  native_decide

/-- `letThenMatch(False) = 0`.  Pairs with the above; arm selection
    visibly differs across the two Bool scrutinees, so a
    wrong-binder-resolution bug (e.g. matching on the parameter
    before the let shift rather than the let-bound `x`) can't
    silently pass. -/
example : runBoolToNatCall letThenMatchDecl "letThenMatch" false = some 0 := by
  native_decide

/-! ## End-to-end: elab + kernel check + eval (iota reduction) -/

/-- `result = isZero(Zero)` — two-decl file, second decl's body
    iota-reduces to `Bool.True`.  Kept as a structural-level
    test since it exercises the bare `checkFile` → `eval` chain
    without the `runFnCall` harness. -/
private def isZeroAppliedZeroDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "result")
    (params := #[])
    (retType := boolTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (.var (qualOf "isZero"))
        #[.pos (.var (qualPath ["Nat"] "Zero"))] zeroSpan))
    (span := zeroSpan)

private def isZeroTrueCheck : Bool :=
  let file : File := { decls := #[isZeroDecl, isZeroAppliedZeroDecl], span := zeroSpan }
  let results := checkFile file
  let allCheck := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allCheck then false
  else
    match results[1]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      match evalZeroArgBody evalEnv elaboratedDecl.body with
      | .ctor "Bool" 1 _ _ => true
      | _                    => false
    | _ => false

example : isZeroTrueCheck = true := by native_decide

/-- `result = pred(Succ(Succ(Zero)))` — second decl's body
    iota-reduces to `Succ(Zero)`. -/
private def predAppliedDecl : Decl :=
  .fnDecl (attrs := #[]) (visibility := .private_)
    (name := "result")
    (params := #[])
    (retType := natTy)
    (effects := #[])
    (specs := #[])
    (body :=.oneLiner
      (.app (.var (qualOf "pred"))
        #[.pos
          (.app (.var (qualPath ["Nat"] "Succ"))
             #[.pos
               (.app (.var (qualPath ["Nat"] "Succ"))
                  #[.pos (.var (qualPath ["Nat"] "Zero"))]
                  zeroSpan)]
             zeroSpan)]
        zeroSpan))
    (span := zeroSpan)

private def predTwoCheck : Bool :=
  let file : File := { decls := #[predDecl, predAppliedDecl], span := zeroSpan }
  let results := checkFile file
  let allCheck := results.all fun declResult =>
    match declResult with
    | .okDecl _ => true
    | _         => false
  if ¬ allCheck then false
  else
    match results[1]? with
    | some (DeclResult.okDecl elaboratedDecl) =>
      let evalEnv : EvalEnv := EvalEnv.ofGlobals (resultsToEnv results)
      -- pred(Succ(Succ(Zero))) should evaluate to Succ(Zero).
      match evalZeroArgBody evalEnv elaboratedDecl.body with
      | .ctor "Nat" 1 _ [.ctor "Nat" 0 _ _] => true
      | _                                    => false
    | _ => false

example : predTwoCheck = true := by native_decide

/-! ## Runtime suite -/

def run : IO Unit := Tests.suite "Tests.Elab.MatchExprTests" do
  Tests.check "bare match (no expected) → E010" true
    (elabErrCode (runWith none
      (matchExpr trueLit
        [arm (pctor "True") (natLit 1), arm (pctor "False") (natLit 0)])) "E010")
  Tests.check "non-exhaustive match Bool missing False → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit [arm (pctor "True") (natLit 1)])) "E010")
  Tests.check "non-exhaustive Nat match missing Succ → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr (natLit 0) [arm (pctor "Zero") (natLit 0)])) "E010")
  Tests.check "non-exhaustive Nat match missing Zero → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr (natLit 0) [arm (pctor "Succ" [pwild]) (natLit 0)])) "E010")
  Tests.check "guard on arm → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [armWithGuard (pctor "True") trueLit (natLit 1),
         arm          (pctor "False") (natLit 0)])) "E010")
  Tests.check "var catch-all arm → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit [arm (pvar "catchall") (natLit 1)])) "E010")
  Tests.check "literal pattern in match → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr (natLit 0)
        [arm (.literal (.kw .trueKw) zeroSpan) (natLit 1),
         arm (pctor "Succ" [pwild])            (natLit 0)])) "E010")
  Tests.check "tuple pattern in match → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (.tuple #[pvar "a", pvar "b"] zeroSpan) (natLit 1),
         arm (pctor "False")                         (natLit 0)])) "E010")
  Tests.check "ascribed pattern in match → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (.ascribed (pvar "x") boolTy zeroSpan) (natLit 1),
         arm (pctor "False")                         (natLit 0)])) "E010")
  Tests.check "unknown ctor in pattern → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (pctor "Foo")   (natLit 1),
         arm (pctor "False") (natLit 0)])) "E010")
  Tests.check "zero-arm match → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit [])) "E010")
  Tests.check "wildcard-only arm (no ctor anchor) → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit [arm pwild (natLit 1)])) "E010")
  Tests.check "mixed inductive families in arms → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (pctor "True") (natLit 1),
         arm (pctor "Zero") (natLit 0)])) "E010")
  Tests.check "Unit match non-exhaustive (zero arms) → E010" true
    (elabErrCode (runWith (some (.ind "Nat" []))
      (matchExpr (.var (qualPath ["Unit"] "tt")) [])) "E010")
  Tests.check "bool match, arms in spec order" true
    (elabEq (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (pctor "False") (natLit 0), arm (pctor "True") (natLit 1)]))
      (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)))
  Tests.check "bool match, user order reordered to ctor order" true
    (elabEq (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (pctor "True") (natLit 1), arm (pctor "False") (natLit 0)]))
      (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)))
  Tests.check "qualified Bool.True / Bool.False patterns work" true
    (elabEq (runWith (some (.ind "Nat" []))
      (matchExpr trueLit
        [arm (pctorQ ["Bool"] "True")  (natLit 1),
         arm (pctorQ ["Bool"] "False") (natLit 0)]))
      (Term.indRec "Bool" natMotive [natKernelZero, natOne] (boolCtor 1)))
  -- fnDecl elab + arm-selection on distinct scrutinees.  Every
  -- decl_ok assertion is paired with two or more eval checks that
  -- fire the decl on inputs whose arms return DISTINCT values —
  -- without this pairing, a broken elab that fixed arm[0] would
  -- still pass `decl_ok`.
  Tests.check "fn neg elab+check" true (decl_ok negDecl)
  Tests.check "neg(True)  = False" (some false) (runBoolToBoolCall negDecl "neg" true)
  Tests.check "neg(False) = True"  (some true)  (runBoolToBoolCall negDecl "neg" false)
  Tests.check "fn pred elab+check" true (decl_ok predDecl)
  Tests.check "pred(Zero)             = Zero"          (some 0)
    (runUnaryCall predDecl "pred" 0)
  Tests.check "pred(Succ(Zero))       = Zero"          (some 0)
    (runUnaryCall predDecl "pred" 1)
  Tests.check "pred(Succ(Succ(Zero))) = Succ(Zero)"    (some 1)
    (runUnaryCall predDecl "pred" 2)
  Tests.check "pred(Succ^3(Zero))     = Succ(Succ(Zero))" (some 2)
    (runUnaryCall predDecl "pred" 3)
  Tests.check "fn isZero elab+check" true (decl_ok isZeroDecl)
  Tests.check "isZero(Zero)       = True"  (some true)
    (runNatToBoolCall isZeroDecl "isZero" 0)
  Tests.check "isZero(Succ(Zero)) = False" (some false)
    (runNatToBoolCall isZeroDecl "isZero" 1)
  Tests.check "isZero(Succ^2(Zero)) = False" (some false)
    (runNatToBoolCall isZeroDecl "isZero" 2)
  Tests.check "fn isSucc elab+check" true (decl_ok isSuccDecl)
  Tests.check "isSucc(Zero)       = False" (some false)
    (runNatToBoolCall isSuccDecl "isSucc" 0)
  Tests.check "isSucc(Succ(Zero)) = True"  (some true)
    (runNatToBoolCall isSuccDecl "isSucc" 1)
  Tests.check "isSucc(Succ^5(Zero)) = True" (some true)
    (runNatToBoolCall isSuccDecl "isSucc" 5)
  Tests.check "fn letThenMatch elab+check" true (decl_ok letThenMatchDecl)
  Tests.check "letThenMatch(True)  = 1" (some 1)
    (runBoolToNatCall letThenMatchDecl "letThenMatch" true)
  Tests.check "letThenMatch(False) = 0" (some 0)
    (runBoolToNatCall letThenMatchDecl "letThenMatch" false)
  Tests.check "isZero(Zero) normalizes to Bool.True" true isZeroTrueCheck
  Tests.check "pred(Succ(Succ(Zero))) normalizes to Succ(Zero)" true predTwoCheck

end Tests.Elab.MatchExprTests
