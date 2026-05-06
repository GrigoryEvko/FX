import LeanFX2.Surface.AST
import LeanFX2.Surface.KernelBridge
import LeanFX2.Surface.StdNames

/-! # Surface/KernelEnv — env-aware bridge for free-name + operator resolution

Per `Surface/KernelBridge.lean`'s docstring, the env-free bridge
`RawExpr.toRawTerm?` returns `none` for:
* Gap #1: free names (no kernel encoding)
* Gap #2: binops / unops (desugar to free-name applications)
* Gap #3: dot projections (need record schema)
* Gap #4: non-zero literals (need succ-chain)

This module addresses gaps #1 and #2 with a `KernelEnv` (qualified-
name → RawTerm symbol table) and `RawExpr.toRawTermWithEnv?`.

```lean
structure ResolvedDef where rawTerm : RawTerm 0
structure KernelEnv where lookup : QualifiedName → Option ResolvedDef

def RawExpr.toRawTermWithEnv? (env : KernelEnv) :
    RawExpr scope → Option (RawTerm scope)
```

## Free-name resolution (gap #1)

`rawFree qname` → `env.lookup qname` → lift module-scope
`RawTerm 0` to caller's `RawTerm scope` via iterated
`RawTerm.weaken`.

## Operator resolution (gap #2)

`rawBinop op lhs rhs` → look up `op.toQualifiedName` (defined
in `Surface/StdNames.lean`) in the env → if resolved, build
`app (app opRaw lhsRaw) rhsRaw`.

`rawUnop op operand` → analogous: `app opRaw operandRaw`.

## Why not extend the kernel?

Extending `RawTerm` with a `const` ctor would require updating
every reduction proof (Step / Step.par / confluence / ...) with
inert cases.  ~500 LoC of mechanical proof amendment.  The
env-at-surface approach keeps the kernel pristine and Layer K
strict zero-axiom.

## Architecture

Full mutual block mirroring `Surface/KernelBridge.lean`'s
env-free bridge but threading `env` through every recursive
call.  Termination by Lean's auto-derived `sizeOf`.

The env-free bridge (in `KernelBridge.lean`) is a SPECIAL CASE
of the env-aware bridge with `KernelEnv.empty` — provable as a
theorem `RawExpr.toRawTermWithEnv?_empty` (deferred).

Zero-axiom verified.
-/

namespace LeanFX2.Surface

/-- A resolved kernel-side definition for a qualified name.
The RawTerm is at module scope (`scope = 0`); the env's
`liftToScope` operation weakens it to the caller's scope. -/
structure ResolvedDef where
  /-- The definition's kernel RawTerm at module scope (0). -/
  rawTerm : RawTerm 0

/-- The global environment.  Maps qualified names to their
kernel-form definitions.  Total function (returns `none` for
unknown names). -/
structure KernelEnv where
  lookup : QualifiedName → Option ResolvedDef

/-- The empty environment — every lookup returns `none`. -/
def KernelEnv.empty : KernelEnv := { lookup := fun _ => none }

/-- Iterated weakening: `RawTerm sourceScope` lifted to
`RawTerm (sourceScope + n)` by applying `RawTerm.weaken` n
times. -/
def RawTerm.weakenIter {sourceScope : Nat}
    (term : RawTerm sourceScope) : ∀ (n : Nat), RawTerm (sourceScope + n)
  | 0 => term
  | n + 1 => (RawTerm.weakenIter term n).weaken

/-- Lift a module-scope (`RawTerm 0`) definition to the caller's
scope by iterated weakening. -/
def ResolvedDef.liftToScope {scope : Nat} (rd : ResolvedDef) :
    Option (RawTerm scope) :=
  some (Nat.zero_add scope ▸ RawTerm.weakenIter rd.rawTerm scope)

/-- KernelEnv-aware literal desugaring.  Extends `Literal.toRawTerm?`
to handle negative integer literals via `Std.Int.neg` lookup
in the env. -/
def Literal.toRawTermWithEnv? {scope : Nat} (env : KernelEnv) :
    Literal → Option (RawTerm scope)
  | .unitLit => some RawTerm.unit
  | .boolLit true => some RawTerm.boolTrue
  | .boolLit false => some RawTerm.boolFalse
  | .intLit n _ =>
    if 0 ≤ n then
      some (RawTerm.natOfNat n.toNat)
    else
      -- Negative: encode as Std.Int.neg applied to abs (positive).
      -- Note: `Int.toNat` returns 0 for negative; use `Int.natAbs`.
      let posRaw : RawTerm scope := RawTerm.natOfNat n.natAbs
      match env.lookup UnaryOp.negate.toQualifiedName with
      | none => none
      | some negDef =>
        match negDef.liftToScope (scope := scope) with
        | none => none
        | some negRaw => some (RawTerm.app negRaw posRaw)
  | .decLit _ _ => none
  | .floatLit _ _ => none
  | .strLit _ => none
  | .bitLit _ _ _ => none
  | .tritLit _ _ _ => none

mutual

/-- KernelEnv-aware bridge: desugars `RawExpr scope` to kernel
`RawTerm scope`, resolving free names and operators via `env`.

Mirrors `RawExpr.toRawTerm?` from `KernelBridge.lean` but
threads `env` through every recursive call. -/
def RawExpr.toRawTermWithEnv? {scope : Nat} (env : KernelEnv) :
    RawExpr scope → Option (RawTerm scope)
  | .rawBound idx => some (RawTerm.var idx)
  | .rawFree qname =>
    match env.lookup qname with
    | none => none
    | some rd => rd.liftToScope
  | .rawLit lit => Literal.toRawTermWithEnv? env lit
  | .rawUnit => some RawTerm.unit
  | .rawParen inner => RawExpr.toRawTermWithEnv? env inner
  | .rawDot _ _ => none  -- gap #3: needs record schema
  | .rawApp fn args =>
      match RawExpr.toRawTermWithEnv? env fn with
      | none => none
      | some fnRaw => RawArgList.foldAppsEnv? env fnRaw args
  | .rawBinop op lhs rhs =>
      -- Three syntactic roles get distinct treatment:
      -- * `pipe` (x |> f) is structural application: f x
      --   (no env lookup needed)
      -- * `arrow` is type-level — bridge can't produce a value
      --   RawTerm; returns none
      -- * `isCtor` (x is Foo) is pattern-matching, kernel special;
      --   returns none
      -- * Everything else: env lookup of stdlib name + nested app
      -- Look up the canonical name (returns none for arrow / pipe
      -- / isCtor — those have distinct syntactic roles).
      match op.toQualifiedName with
      | none =>
        -- Distinct-role operators: handle each explicitly.
        match op with
        | .pipe =>
          -- `x |> f` desugars to `f x` (no env lookup needed).
          match RawExpr.toRawTermWithEnv? env lhs with
          | none => none
          | some lhsRaw =>
            match RawExpr.toRawTermWithEnv? env rhs with
            | none => none
            | some rhsRaw => some (RawTerm.app rhsRaw lhsRaw)
        | .arrow => none      -- type-level
        | .isCtor => none     -- pattern match
        -- All other ops have a Some name (full enum to avoid
        -- wildcard propext leak):
        | .logicalAnd | .logicalOr
        | .eqEq | .notEq | .lt | .gt | .le | .ge
        | .bitAnd | .bitOr | .bitXor | .shiftLeft | .shiftRight
        | .plus | .minus | .star | .slash | .percent
        | .rangeExcl | .rangeIncl
        | .iff | .implies => none  -- unreachable per toQualifiedName
      | some qname =>
        match env.lookup qname with
        | none => none
        | some opDef =>
          match opDef.liftToScope (scope := scope) with
          | none => none
          | some opRaw =>
            match RawExpr.toRawTermWithEnv? env lhs with
            | none => none
            | some lhsRaw =>
              match RawExpr.toRawTermWithEnv? env rhs with
              | none => none
              | some rhsRaw =>
                some (RawTerm.app (RawTerm.app opRaw lhsRaw) rhsRaw)
  | .rawUnop op operand =>
      match env.lookup op.toQualifiedName with
      | none => none
      | some opDef =>
        match opDef.liftToScope (scope := scope) with
        | none => none
        | some opRaw =>
          match RawExpr.toRawTermWithEnv? env operand with
          | none => none
          | some operandRaw =>
            some (RawTerm.app opRaw operandRaw)
  | .rawLam _ _ body =>
      match RawExpr.toRawTermWithEnv? env body with
      | none => none
      | some bodyRaw => some (RawTerm.lam bodyRaw)
  | .rawBlock stmts final =>
      match RawExpr.toRawTermWithEnv? env final with
      | none => none
      | some finalRaw => RawStmtList.foldBlockEnv? env stmts finalRaw
  | .rawIf cond thenBr elseBr =>
      match RawExpr.toRawTermWithEnv? env cond with
      | none => none
      | some condRaw =>
        match RawExpr.toRawTermWithEnv? env thenBr with
        | none => none
        | some thenRaw =>
          match OptRawExpr.toRawTermOrUnitEnv? env elseBr with
          | none => none
          | some elseRaw =>
              some (RawTerm.boolElim condRaw thenRaw elseRaw)

/-- KernelEnv-aware fold of an arg list into nested `RawTerm.app`. -/
def RawArgList.foldAppsEnv? {scope : Nat} (env : KernelEnv) (acc : RawTerm scope) :
    RawArgList scope → Option (RawTerm scope)
  | .rawNilArg => some acc
  | .rawConsArg arg rest =>
      match RawCallArg.toRawTermWithEnv? env arg with
      | none => none
      | some argRaw => RawArgList.foldAppsEnv? env (RawTerm.app acc argRaw) rest

/-- KernelEnv-aware desugar of a single call-arg. -/
def RawCallArg.toRawTermWithEnv? {scope : Nat} (env : KernelEnv) :
    RawCallArg scope → Option (RawTerm scope)
  | .rawPositional v => RawExpr.toRawTermWithEnv? env v
  | .rawNamed _ v => RawExpr.toRawTermWithEnv? env v
  | .rawImplicit v => RawExpr.toRawTermWithEnv? env v

/-- KernelEnv-aware OptRawExpr → RawTerm (with unit fallback). -/
def OptRawExpr.toRawTermOrUnitEnv? {scope : Nat} (env : KernelEnv) :
    OptRawExpr scope → Option (RawTerm scope)
  | .rawNone => some RawTerm.unit
  | .rawSome r => RawExpr.toRawTermWithEnv? env r

/-- KernelEnv-aware fold of a StmtList into the let-as-application chain. -/
def RawStmtList.foldBlockEnv? {scope outScope : Nat} (env : KernelEnv) :
    RawStmtList scope outScope → RawTerm outScope →
    Option (RawTerm scope)
  | .rawNilStmt, finalRaw => some finalRaw
  | .rawLetCons _ _ value rest, finalRaw =>
      match RawExpr.toRawTermWithEnv? env value with
      | none => none
      | some valueRaw =>
        match RawStmtList.foldBlockEnv? env rest finalRaw with
        | none => none
        | some restRaw => some (RawTerm.app (RawTerm.lam restRaw) valueRaw)
  | .rawExprCons value rest, finalRaw =>
      match RawExpr.toRawTermWithEnv? env value with
      | none => none
      | some valueRaw =>
        match RawStmtList.foldBlockEnv? env rest finalRaw with
        | none => none
        | some restRaw =>
          some (RawTerm.app (RawTerm.lam restRaw.weaken) valueRaw)

end -- mutual

/-- Wrapper: env-aware desugar from decorated `Expr`. -/
@[reducible] def Expr.toRawTermWithEnv? {scope : Nat} {raw : RawExpr scope}
    (env : KernelEnv) (_e : Expr raw) : Option (RawTerm scope) :=
  RawExpr.toRawTermWithEnv? env raw

end LeanFX2.Surface
