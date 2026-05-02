import LeanFX2.Surface.AST
import LeanFX2.Term

/-! # Surface/KernelBridge — wire Surface AST into the kernel

## Honest accounting of kernel ↔ surface

The kernel `RawTerm scope` covers the LAMBDA CALCULUS +
CANONICAL DATA fragment of FX comprehensively.  What the
kernel DOES NOT have (genuine gaps):

| Missing                       | Effect on bridge          | Path forward                |
|-------------------------------|---------------------------|-----------------------------|
| `RawTerm.const` (free names)  | `rawFree _ ↦ none`        | extend kernel + global env  |
| Primitive operators           | `rawBinop _ _ _ ↦ none`   | stdlib defs + name resolve  |
| First-class records           | `rawDot _ _ ↦ none`       | record schema + projection  |
| N-literal primitives          | `intLit n>0 ↦ none`       | succ-chain encoding         |

These aren't blockers — they're separate phases that extend or
combine the kernel with environment infrastructure.  The bridge
ships the DIRECT-CORRESPONDENCE FRAGMENT now.

## What ships

```lean
def RawExpr.toRawTerm? : RawExpr scope → Option (RawTerm scope)
def Expr.toRawTerm?    : Expr raw      → Option (RawTerm scope)
```

Total + zero-axiom on the fragment that maps directly to kernel
constructs.  Returns `none` exactly for the four gap categories
above (and for `exprCons` block statements which need raw-level
weakening — the kernel's `RawTermSubst.shift` could be wired up
here in a follow-up).

## Termination

Mutual block of five functions:
`RawExpr.toRawTerm?`, `RawArgList.toRawTermArgs?`,
`RawCallArg.toRawTerm?`, `OptRawExpr.toRawTermOrUnit?`,
`RawStmtList.foldBlock?`.  Termination is by `sizeOf` of the
primary argument; cross-function calls go through structurally
smaller sub-components.

## Reduction in proofs

Mutual definitions don't reduce by `rfl` on concrete inputs.
To prove `(rawBound idx).toRawTerm? = some (RawTerm.var idx)`,
use `unfold RawExpr.toRawTerm?` and let the WellFoundedRecursion
unfold lemma fire.  `simp [RawExpr.toRawTerm?]` also works.

A future "BridgeReduction.lean" file could state the per-ctor
reduction lemmas explicitly for ergonomic downstream use.
-/

namespace LeanFX2.Surface

/-- Desugar a literal to its kernel canonical form.  Only
direct correspondences handled (unit, bool, nat-zero); other
literals need the elaborator.

The `intLit n _` case uses `if n = 0` (Decidable on Int)
rather than the nested pattern `.intLit (.ofNat 0) _` which
would leak propext via Lean 4 v4.29.1's match compiler. -/
def Literal.toRawTerm? {scope : Nat} : Literal → Option (RawTerm scope)
  | .unitLit => some RawTerm.unit
  | .boolLit true => some RawTerm.boolTrue
  | .boolLit false => some RawTerm.boolFalse
  | .intLit n _ => if n = 0 then some RawTerm.natZero else none
  | .decLit _ _ => none
  | .floatLit _ _ => none
  | .strLit _ => none
  | .bitLit _ _ _ => none
  | .tritLit _ _ _ => none

mutual

/-- Desugar a RawExpr to kernel RawTerm.  Returns none for the
four gap categories (free names, binops, unops, dot proj) and
for non-trivial literals. -/
def RawExpr.toRawTerm? {scope : Nat} :
    RawExpr scope → Option (RawTerm scope)
  | .rawBound idx => some (RawTerm.var idx)
  | .rawFree _ => none
  | .rawLit lit => Literal.toRawTerm? lit
  | .rawUnit => some RawTerm.unit
  | .rawParen inner => RawExpr.toRawTerm? inner
  | .rawDot _ _ => none
  | .rawApp fn args =>
      match RawExpr.toRawTerm? fn with
      | none => none
      | some fnRaw => RawArgList.foldApps? fnRaw args
  | .rawBinop _ _ _ => none
  | .rawUnop _ _ => none
  | .rawLam _ _ body =>
      match RawExpr.toRawTerm? body with
      | none => none
      | some bodyRaw => some (RawTerm.lam bodyRaw)
  | .rawBlock stmts final =>
      match RawExpr.toRawTerm? final with
      | none => none
      | some finalRaw => RawStmtList.foldBlock? stmts finalRaw  -- handles exprCons via RawTerm.weaken
  | .rawIf cond thenBr elseBr =>
      match RawExpr.toRawTerm? cond with
      | none => none
      | some condRaw =>
        match RawExpr.toRawTerm? thenBr with
        | none => none
        | some thenRaw =>
          match OptRawExpr.toRawTermOrUnit? elseBr with
          | none => none
          | some elseRaw =>
              some (RawTerm.boolElim condRaw thenRaw elseRaw)

/-- Fold a RawArgList into nested `RawTerm.app` applications.
Recurses structurally on the RawArgList. -/
def RawArgList.foldApps? {scope : Nat} (acc : RawTerm scope) :
    RawArgList scope → Option (RawTerm scope)
  | .rawNilArg => some acc
  | .rawConsArg arg rest =>
      match RawCallArg.toRawTerm? arg with
      | none => none
      | some argRaw => RawArgList.foldApps? (RawTerm.app acc argRaw) rest

/-- Desugar a single call-arg.  Named/implicit collapse to the
same value at kernel level. -/
def RawCallArg.toRawTerm? {scope : Nat} :
    RawCallArg scope → Option (RawTerm scope)
  | .rawPositional v => RawExpr.toRawTerm? v
  | .rawNamed _ v => RawExpr.toRawTerm? v
  | .rawImplicit v => RawExpr.toRawTerm? v

/-- An OptRawExpr that's `rawNone` desugars to `RawTerm.unit`
(placeholder for omitted else branches). -/
def OptRawExpr.toRawTermOrUnit? {scope : Nat} :
    OptRawExpr scope → Option (RawTerm scope)
  | .rawNone => some RawTerm.unit
  | .rawSome r => RawExpr.toRawTerm? r

/-- Fold a RawStmtList + already-desugared final into the
let-as-application chain.  Recurses structurally on the
RawStmtList.

`exprCons` (a discarded statement `expr;`) desugars to
`(fun _ => rest.weaken) value` — wrap `rest` in a lambda that
ignores its argument.  Uses kernel `RawTerm.weaken`
(`Foundation/RawSubst.lean`) to lift `rest` from scope to
scope+1.

`letCons` desugars to `(fun bound => rest) value` directly —
`rest` is already at scope+1 (the let extends scope by 1). -/
def RawStmtList.foldBlock? {scope outScope : Nat} :
    RawStmtList scope outScope → RawTerm outScope →
    Option (RawTerm scope)
  | .rawNilStmt, finalRaw => some finalRaw
  | .rawLetCons _ _ value rest, finalRaw =>
      match RawExpr.toRawTerm? value with
      | none => none
      | some valueRaw =>
        match RawStmtList.foldBlock? rest finalRaw with
        | none => none
        | some restRaw => some (RawTerm.app (RawTerm.lam restRaw) valueRaw)
  | .rawExprCons value rest, finalRaw =>
      match RawExpr.toRawTerm? value with
      | none => none
      | some valueRaw =>
        match RawStmtList.foldBlock? rest finalRaw with
        | none => none
        | some restRaw =>
          -- exprCons: (fun _ => rest.weaken) value
          some (RawTerm.app (RawTerm.lam restRaw.weaken) valueRaw)

end -- mutual

/-- Wrapper: desugar a decorated `Expr` by projecting to its
indexed `RawExpr`.  Definitionally equal:
`(e : Expr raw).toRawTerm? = raw.toRawTerm?`. -/
@[reducible] def Expr.toRawTerm? {scope : Nat} {raw : RawExpr scope}
    (_e : Expr raw) : Option (RawTerm scope) :=
  RawExpr.toRawTerm? raw

end LeanFX2.Surface
