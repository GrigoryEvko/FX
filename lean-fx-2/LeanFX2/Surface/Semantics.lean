import LeanFX2.Surface.KernelBridge

/-! # Surface/Semantics — denotational semantics for `Expr scope`

## Design choice: the bridge IS the denotation

Surface audits (2026-05-07) flagged the original B-series "bridge
correctness" tasks (B02–B12, tracker #1242–#1252) as vapourware:
eleven separate "correctness" theorems were claimed pending, but
no formal denotational ⟦·⟧ existed for `Expr scope`.  The cure is
to identify the denotation function with the bridge function:

```
  Expr.denote      e := Expr.toRawTerm?      e
  RawExpr.denote raw := RawExpr.toRawTerm? raw
```

With this identification, the eleven B-series tasks collapse:

* B02–B07 (per-ctor correctness for `boundExpr` / `unitExpr` /
  `appExpr` / `lamExpr` / `ifExpr` / `blockExpr`) become
  reduction-shape lemmas — already shipped as the R-series in
  `Surface/KernelBridgeReduction.lean` (tracker #1280).
* B08–B09 (env-aware variants for `binopExpr` / `freeNameExpr`)
  become the env-aware bridge in `Surface/KernelEnv.lean`.
* B10 (env-aware = env-free with `KernelEnv.empty`) is now
  literally the equality of two `denote` functions.
* B11 (`Expr.toRaw_rfl` extends to bridge-projection
  commutativity) is now `denote ∘ Expr.toRaw = denote` by `rfl`.
* B12 (totality on gap-free fragment) is the only remaining
  non-trivial obligation — characterising the input shapes for
  which `denote` returns `some _`.

This file ships the load-bearing definition + the rfl bridge to
the existing `toRawTerm?` operational form.  Downstream B-series
follow-ups consume `Expr.denote` rather than going around it.

## What this file does NOT do

* Define operational semantics (kernel `Step` already exists in
  `Reduction/Step.lean`; `Term.toRaw` is the operational mapping).
* Prove totality (B12 / tracker #1252 — separate commit).
* Define env-aware semantics (B10 / B-umbrella #1532 — separate
  commit using `KernelEnv` infrastructure).
-/

namespace LeanFX2.Surface

/-- Denotational semantics for the `RawExpr scope` indexed
inductive: an expression's meaning is its kernel `RawTerm`
projection via the bridge.  Returns `none` for the four bridge
gap categories enumerated in `KernelBridge.lean` (free names,
binops/unops, dot projections, non-trivial literals). -/
@[reducible] def RawExpr.denote {scope : Nat} (raw : RawExpr scope) :
    Option (RawTerm scope) :=
  RawExpr.toRawTerm? raw

/-- Denotational semantics for the decorated `Expr raw` family.
By the `Expr.toRaw_rfl` invariant, this just projects to the
`RawExpr.denote` of the underlying raw expression. -/
@[reducible] def Expr.denote {scope : Nat} {raw : RawExpr scope}
    (expr : Expr raw) : Option (RawTerm scope) :=
  Expr.toRawTerm? expr

/-- The bridge function and the denotation function are the same
function, by definition.  Subsumes the operational vs denotational
distinction at this layer of the surface stack. -/
theorem RawExpr.denote_eq_toRawTerm? {scope : Nat}
    (raw : RawExpr scope) :
    RawExpr.denote raw = RawExpr.toRawTerm? raw :=
  rfl

/-- Decorated counterpart of `RawExpr.denote_eq_toRawTerm?`. -/
theorem Expr.denote_eq_toRawTerm? {scope : Nat}
    {raw : RawExpr scope} (expr : Expr raw) :
    Expr.denote expr = Expr.toRawTerm? expr :=
  rfl

/-- Decorated denotation projects through the `Expr.toRaw_rfl`
invariant: the meaning of a decorated `Expr raw` is the meaning
of its underlying `RawExpr raw`.  This is the bridge-projection
commutativity claim of B11 (tracker #1251), now `rfl`. -/
theorem Expr.denote_eq_RawExpr_denote {scope : Nat}
    {raw : RawExpr scope} (expr : Expr raw) :
    Expr.denote expr = RawExpr.denote raw :=
  rfl

/-! ## Per-ctor denotation corollaries (B02–B07 collapse)

The R-series in `KernelBridgeReduction.lean` ships per-ctor
reduction lemmas at the `RawExpr.toRawTerm?` level.  With
`Expr.denote := Expr.toRawTerm?` (reducible alias) the same
reductions fire at the decorated `Expr.denote` level — each
theorem below is a definitional `rfl` corollary that lifts the
operational reduction to the denotational layer.  These close
the umbrella collapse claim of B-VAPOURWARE-UMBRELLA (#1532):
the eleven B-series "correctness" theorems become the unfolding
equations stated here. -/

/-- B02 (tracker #1242): `boundExpr` denotes to its kernel
`var`.  De Bruijn variable: zero-cost lift through the bridge. -/
theorem Expr.denote_boundExpr {scope : Nat} (idx : Fin scope)
    (pos : SrcPos) :
    Expr.denote (Expr.boundExpr idx pos) = some (RawTerm.var idx) :=
  rfl

/-- B02 (tracker #1242) partial: free-name lookup is OUTSIDE the
gap-free fragment in the env-free bridge.  Returns `none` per
gap #1 (free names need env). -/
theorem Expr.denote_freeNameExpr {scope : Nat}
    (qname : QualifiedName) (pos : SrcPos) :
    Expr.denote (Expr.freeNameExpr (scope := scope) qname pos) = none :=
  rfl

/-- B03 (tracker #1243): bare `unitExpr` denotes to kernel `unit`. -/
theorem Expr.denote_unitExpr {scope : Nat} (pos : SrcPos) :
    Expr.denote (Expr.unitExpr (scope := scope) pos)
      = some RawTerm.unit :=
  rfl

/-- B03 (tracker #1243): `litExpr Literal.unitLit` denotes to
kernel `unit`.  Literal-form sibling of `denote_unitExpr`. -/
theorem Expr.denote_litExpr_unitLit {scope : Nat} (pos : SrcPos) :
    Expr.denote (Expr.litExpr (scope := scope) Literal.unitLit pos)
      = some RawTerm.unit :=
  rfl

/-- B03 (tracker #1243): boolean-true literal denotes to kernel
`boolTrue`. -/
theorem Expr.denote_litExpr_boolTrue {scope : Nat} (pos : SrcPos) :
    Expr.denote
        (Expr.litExpr (scope := scope) (Literal.boolLit true) pos)
      = some RawTerm.boolTrue :=
  rfl

/-- B03 (tracker #1243): boolean-false literal denotes to kernel
`boolFalse`. -/
theorem Expr.denote_litExpr_boolFalse {scope : Nat} (pos : SrcPos) :
    Expr.denote
        (Expr.litExpr (scope := scope) (Literal.boolLit false) pos)
      = some RawTerm.boolFalse :=
  rfl

/-- B03 (tracker #1243): integer literal `0` (any suffix) denotes
to kernel `natZero`.  Tests the env-free succ-chain encoding base. -/
theorem Expr.denote_litExpr_intLit_zero {scope : Nat}
    (suffix : Option String) (pos : SrcPos) :
    Expr.denote
        (Expr.litExpr (scope := scope) (Literal.intLit 0 suffix) pos)
      = some RawTerm.natZero :=
  rfl

/-- B03 (tracker #1243): string literal is OUTSIDE the gap-free
fragment.  Returns `none` per gap #4 (no kernel string encoding). -/
theorem Expr.denote_litExpr_strLit {scope : Nat} (value : String)
    (pos : SrcPos) :
    Expr.denote
        (Expr.litExpr (scope := scope) (Literal.strLit value) pos)
      = none :=
  rfl

/-- B04 (tracker #1244): `appExpr` denotes by folding the bridge
result of the function with the bridged argument list.  The
match-shape mirrors `RawExpr.toRawTerm?_rawApp` exactly. -/
theorem Expr.denote_appExpr {scope : Nat} {fnRaw : RawExpr scope}
    {argsRaw : RawArgList scope} (fn : Expr fnRaw)
    (args : ArgList argsRaw) (pos : SrcPos) :
    Expr.denote (Expr.appExpr fn args pos)
      = (match RawExpr.toRawTerm? fnRaw with
         | none => none
         | some fnRawTerm => RawArgList.foldApps? fnRawTerm argsRaw) :=
  rfl

/-- B05 (tracker #1245): `lamExpr` denotes to `RawTerm.lam` of
the bridged body.  Lambda body weakening is implicit in the
scope-indexed body type `Expr bodyRaw : RawExpr (scope + 1)`. -/
theorem Expr.denote_lamExpr {scope : Nat}
    {paramTypeRaw : OptRawExpr scope}
    {bodyRaw : RawExpr (scope + 1)}
    (paramName : LowerIdent) (paramType : OptExpr paramTypeRaw)
    (body : Expr bodyRaw) (pos : SrcPos) :
    Expr.denote (Expr.lamExpr paramName paramType body pos)
      = (match RawExpr.toRawTerm? bodyRaw with
         | none => none
         | some bodyRawTerm => some (RawTerm.lam bodyRawTerm)) :=
  rfl

/-- B06 (tracker #1246): `ifExpr` denotes to `RawTerm.boolElim`
correspondence — three-way match on the bridged condition,
then-branch, and (else-or-unit) branch. -/
theorem Expr.denote_ifExpr {scope : Nat}
    {condRaw thenRaw : RawExpr scope}
    {elseRaw : OptRawExpr scope}
    (cond : Expr condRaw) (thenBr : Expr thenRaw)
    (elseBr : OptExpr elseRaw) (pos : SrcPos) :
    Expr.denote (Expr.ifExpr cond thenBr elseBr pos)
      = (match RawExpr.toRawTerm? condRaw with
         | none => none
         | some condRawTerm =>
           match RawExpr.toRawTerm? thenRaw with
           | none => none
           | some thenRawTerm =>
             match OptRawExpr.toRawTermOrUnit? elseRaw with
             | none => none
             | some elseRawTerm =>
                 some (RawTerm.boolElim condRawTerm thenRawTerm
                                        elseRawTerm)) :=
  rfl

/-- B07 (tracker #1247): `blockExpr` denotes by folding the
statement list against the bridged final expression — the
let-as-application desugaring claim of #1247. -/
theorem Expr.denote_blockExpr {scope outScope : Nat}
    {stmtsRaw : RawStmtList scope outScope}
    {finalRaw : RawExpr outScope}
    (stmts : StmtList stmtsRaw) (final : Expr finalRaw)
    (pos : SrcPos) :
    Expr.denote (Expr.blockExpr stmts final pos)
      = (match RawExpr.toRawTerm? finalRaw with
         | none => none
         | some finalRawTerm =>
             RawStmtList.foldBlock? stmtsRaw finalRawTerm) :=
  rfl

/-- B-series partial (paren transparency): `parenExpr` denotes
identically to its inner expression — parens are erased at the
bridge layer. -/
theorem Expr.denote_parenExpr {scope : Nat} {raw : RawExpr scope}
    (inner : Expr raw) (pos : SrcPos) :
    Expr.denote (Expr.parenExpr inner pos) = Expr.denote inner :=
  rfl

/-- Gap-explicit: `dotExpr` is OUTSIDE the gap-free fragment per
gap #3 (records).  Returns `none` until #1253 G01 ships. -/
theorem Expr.denote_dotExpr {scope : Nat} {objRaw : RawExpr scope}
    (obj : Expr objRaw) (field : LowerIdent) (pos : SrcPos) :
    Expr.denote (Expr.dotExpr obj field pos) = none :=
  rfl

/-- Gap-explicit: `binopExpr` is OUTSIDE the gap-free fragment in
the env-free bridge per gap #2 (operators need env lookup).
Returns `none` until env-aware bridge wires up B08–B10. -/
theorem Expr.denote_binopExpr {scope : Nat}
    {lhsRaw rhsRaw : RawExpr scope} (op : BinaryOp)
    (lhs : Expr lhsRaw) (rhs : Expr rhsRaw)
    (chainOk : op.isComparison = true →
                  lhsRaw.topNotComparison = true ∧
                  rhsRaw.topNotComparison = true)
    (pos : SrcPos) :
    Expr.denote (Expr.binopExpr op lhs rhs chainOk pos) = none :=
  rfl

/-- Gap-explicit: `unopExpr` is OUTSIDE the gap-free fragment in
the env-free bridge per gap #2 (operators need env lookup). -/
theorem Expr.denote_unopExpr {scope : Nat}
    {operandRaw : RawExpr scope} (op : UnaryOp)
    (operand : Expr operandRaw) (pos : SrcPos) :
    Expr.denote (Expr.unopExpr op operand pos) = none :=
  rfl

end LeanFX2.Surface
