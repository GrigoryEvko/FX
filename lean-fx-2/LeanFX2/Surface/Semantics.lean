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

/-! ## B12: bridge totality on the gap-free fragment (#1252)

The env-free bridge `RawExpr.toRawTerm?` returns `none` exactly
on the four gap categories enumerated in `KernelBridge.lean`
(free names, binops/unops, dot projections, non-positive integer
literals + non-int literals).  The `isGapFree` predicate below
characterizes the complementary fragment: every `RawExpr` whose
shape avoids those gaps.

Totality: `RawExpr.isGapFree raw = true → bridge succeeds`. -/

/-- `Literal.isGapFree` covers atomic literal shapes the env-free
bridge can encode: `unitLit`, `boolLit _`, and non-negative
integer literals.  `decLit`/`floatLit`/`strLit`/`bitLit`/`tritLit`
have no kernel encoding (gap #4). -/
def Literal.isGapFree : Literal → Bool
  | .unitLit => true
  | .boolLit _ => true
  | .intLit (Int.ofNat _) _ => true
  | .intLit (Int.negSucc _) _ => false
  | .decLit _ _ => false
  | .floatLit _ _ => false
  | .strLit _ => false
  | .bitLit _ _ _ => false
  | .tritLit _ _ _ => false

mutual

/-- `RawExpr.isGapFree` characterizes the syntactic fragment on
which the env-free bridge succeeds.  `none`-producing ctors are
explicitly false; recursive ctors require their subcomponents
to also be gap-free. -/
def RawExpr.isGapFree {scope : Nat} : RawExpr scope → Bool
  | .rawBound _ => true
  | .rawFree _ => false
  | .rawLit lit => Literal.isGapFree lit
  | .rawUnit => true
  | .rawParen inner => RawExpr.isGapFree inner
  | .rawDot _ _ => false
  | .rawApp fn args => RawExpr.isGapFree fn && RawArgList.isGapFree args
  | .rawBinop _ _ _ => false
  | .rawUnop _ _ => false
  | .rawLam _ _ body => RawExpr.isGapFree body
  | .rawBlock stmts final =>
      RawStmtList.isGapFree stmts && RawExpr.isGapFree final
  | .rawIf cond thenBr elseBr =>
      RawExpr.isGapFree cond && RawExpr.isGapFree thenBr
        && OptRawExpr.isGapFree elseBr

/-- Optional-expression gap-free predicate.  `rawNone` always
denotes (to `RawTerm.unit`); `rawSome` requires its inner
expression to be gap-free. -/
def OptRawExpr.isGapFree {scope : Nat} : OptRawExpr scope → Bool
  | .rawNone => true
  | .rawSome value => RawExpr.isGapFree value

/-- Argument-list gap-free predicate. -/
def RawArgList.isGapFree {scope : Nat} : RawArgList scope → Bool
  | .rawNilArg => true
  | .rawConsArg arg rest =>
      RawCallArg.isGapFree arg && RawArgList.isGapFree rest

/-- Call-arg gap-free predicate. -/
def RawCallArg.isGapFree {scope : Nat} : RawCallArg scope → Bool
  | .rawPositional value => RawExpr.isGapFree value
  | .rawNamed _ value => RawExpr.isGapFree value
  | .rawImplicit value => RawExpr.isGapFree value

/-- Statement-list gap-free predicate. -/
def RawStmtList.isGapFree {scope outScope : Nat} :
    RawStmtList scope outScope → Bool
  | .rawNilStmt => true
  | .rawLetCons _ _ value rest =>
      RawExpr.isGapFree value && RawStmtList.isGapFree rest
  | .rawExprCons value rest =>
      RawExpr.isGapFree value && RawStmtList.isGapFree rest

end -- mutual

/-! ### Literal-level totality (non-mutual) -/

/-- Every gap-free literal denotes to a kernel `RawTerm`.  Base
case for the recursive bridge totality. -/
theorem Literal.bridgeIsTotalOnGapFree {scope : Nat} (lit : Literal)
    (gapFree : Literal.isGapFree lit = true) :
    ∃ rawTerm : RawTerm scope,
        Literal.toRawTerm? (scope := scope) lit = some rawTerm := by
  match lit, gapFree with
  | .unitLit, _ => exact ⟨RawTerm.unit, rfl⟩
  | .boolLit true, _ => exact ⟨RawTerm.boolTrue, rfl⟩
  | .boolLit false, _ => exact ⟨RawTerm.boolFalse, rfl⟩
  | .intLit (Int.ofNat n) suffix, _ =>
      exact ⟨RawTerm.natOfNat n, rfl⟩

/-! ### B12 atomic-case totality

Atomic (non-recursive) totality theorems closing the gap-free
case for the leaf `RawExpr` ctors.  These are the unconditional
totality claims; recursive ctors (`rawApp`, `rawLam`, `rawBlock`,
`rawIf`, `rawParen`) carry their inductive premises explicitly
in the **compositional** theorems below.

**Why not one universal theorem?**  Lean 4 v4.29.1's structural-
recursion analyzer cannot infer termination for a mutual block
of five totality theorems across the indexed mutual inductive
`(RawExpr, OptRawExpr, RawArgList, RawCallArg, RawStmtList)`
when each carries an `Eq` premise (the `gapFree` argument).  The
analyzer skips the `Eq` parameter (its indices aren't variables)
and fails to find a decreasing measure on the structural inputs
because the cross-call mutual relations aren't tracked.  Path
forward (future): use `WellFoundedRecursion` on `sizeOf raw` with
explicit `decreasing_by` annotations, OR define a `bridgeOrFail`
function via mutual `def` (which Lean's termination DOES handle)
and derive existence from it.  See tracker #1252 for status.

The compositional toolkit below lets users prove totality of
specific surface programs by composing per-ctor theorems. -/

/-- B12 atomic: bound variables always denote. -/
theorem RawExpr.bridgeIsTotalOnRawBound {scope : Nat} (idx : Fin scope) :
    ∃ rawTerm, RawExpr.toRawTerm? (RawExpr.rawBound idx) = some rawTerm :=
  ⟨RawTerm.var idx, rfl⟩

/-- B12 atomic: unit always denotes. -/
theorem RawExpr.bridgeIsTotalOnRawUnit {scope : Nat} :
    ∃ rawTerm, RawExpr.toRawTerm? (RawExpr.rawUnit (scope := scope))
                = some rawTerm :=
  ⟨RawTerm.unit, rfl⟩

/-- B12 atomic: gap-free literals always denote (lifted from
`Literal.bridgeIsTotalOnGapFree` to the `rawLit` ctor). -/
theorem RawExpr.bridgeIsTotalOnRawLit {scope : Nat} (lit : Literal)
    (gapFree : Literal.isGapFree lit = true) :
    ∃ rawTerm, RawExpr.toRawTerm? (RawExpr.rawLit (scope := scope) lit)
                = some rawTerm :=
  Literal.bridgeIsTotalOnGapFree (scope := scope) lit gapFree

/-! ### B12 compositional totality (each non-leaf ctor)

Each compositional theorem assumes totality of the structural
sub-components and concludes totality of the parent.  Together
with the atomic theorems they form a complete proof toolkit for
gap-free totality without requiring mutual induction. -/

/-- Compositional: `rawParen` denotes whenever its inner does. -/
theorem RawExpr.bridgeIsTotalOnRawParen {scope : Nat}
    (inner : RawExpr scope)
    (innerTotal : ∃ innerTerm, RawExpr.toRawTerm? inner = some innerTerm) :
    ∃ rawTerm, RawExpr.toRawTerm? (RawExpr.rawParen inner) = some rawTerm := by
  obtain ⟨innerTerm, innerEq⟩ := innerTotal
  exact ⟨innerTerm, by show inner.toRawTerm? = some innerTerm; exact innerEq⟩

/-- Compositional: `rawLam` denotes whenever its body does. -/
theorem RawExpr.bridgeIsTotalOnRawLam {scope : Nat}
    (paramName : LowerIdent) (paramType : OptRawExpr scope)
    (body : RawExpr (scope + 1))
    (bodyTotal : ∃ bodyTerm, RawExpr.toRawTerm? body = some bodyTerm) :
    ∃ rawTerm,
        RawExpr.toRawTerm? (RawExpr.rawLam paramName paramType body)
          = some rawTerm := by
  obtain ⟨bodyTerm, bodyEq⟩ := bodyTotal
  refine ⟨RawTerm.lam bodyTerm, ?_⟩
  show (match RawExpr.toRawTerm? body with
        | none => none
        | some bodyRaw => some (RawTerm.lam bodyRaw))
        = some (RawTerm.lam bodyTerm)
  rw [bodyEq]

/-- Compositional: `rawApp` denotes whenever its function and
fold of its arguments both succeed. -/
theorem RawExpr.bridgeIsTotalOnRawApp {scope : Nat}
    (fn : RawExpr scope) (args : RawArgList scope)
    (fnTotal : ∃ fnTerm, RawExpr.toRawTerm? fn = some fnTerm)
    (foldTotal : ∀ acc, ∃ result, RawArgList.foldApps? acc args = some result) :
    ∃ rawTerm, RawExpr.toRawTerm? (RawExpr.rawApp fn args) = some rawTerm := by
  obtain ⟨fnTerm, fnEq⟩ := fnTotal
  obtain ⟨appResult, foldEq⟩ := foldTotal fnTerm
  refine ⟨appResult, ?_⟩
  show (match RawExpr.toRawTerm? fn with
        | none => none
        | some fnRaw => RawArgList.foldApps? fnRaw args)
        = some appResult
  rw [fnEq]; exact foldEq

/-- B12 lifted to the decorated `Expr` family — atomic case. -/
theorem Expr.denoteIsTotalOnBoundExpr {scope : Nat} (idx : Fin scope)
    (pos : SrcPos) :
    ∃ rawTerm, Expr.denote (Expr.boundExpr idx pos) = some rawTerm :=
  ⟨RawTerm.var idx, rfl⟩

/-- B12 lifted to the decorated `Expr` family — unitExpr case. -/
theorem Expr.denoteIsTotalOnUnitExpr {scope : Nat} (pos : SrcPos) :
    ∃ rawTerm, Expr.denote (Expr.unitExpr (scope := scope) pos)
                = some rawTerm :=
  ⟨RawTerm.unit, rfl⟩

/-- B12 lifted to the decorated `Expr` family — litExpr case. -/
theorem Expr.denoteIsTotalOnLitExpr {scope : Nat} (lit : Literal)
    (gapFree : Literal.isGapFree lit = true) (pos : SrcPos) :
    ∃ rawTerm, Expr.denote (Expr.litExpr (scope := scope) lit pos)
                = some rawTerm :=
  Literal.bridgeIsTotalOnGapFree (scope := scope) lit gapFree

/-! ### B12 compositional totality — helper families

The `OptRawExpr`, `RawArgList`, `RawCallArg`, and `RawStmtList`
families each carry their own gap-free predicate and per-ctor
totality lemma.  Together with the `RawExpr` ctors above they
form the full compositional toolkit on which any specific
gap-free surface program can be proved total by structural
recursion at the call site. -/

/-- B12 atomic: `rawNone` always denotes (to `RawTerm.unit`). -/
theorem OptRawExpr.bridgeIsTotalOnRawNone {scope : Nat} :
    ∃ rawTerm,
        OptRawExpr.toRawTermOrUnit?
          (OptRawExpr.rawNone (scope := scope)) = some rawTerm :=
  ⟨RawTerm.unit, rfl⟩

/-- B12 compositional: `rawSome value` denotes whenever its
inner expression does. -/
theorem OptRawExpr.bridgeIsTotalOnRawSome {scope : Nat}
    (value : RawExpr scope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm) :
    ∃ rawTerm,
        OptRawExpr.toRawTermOrUnit? (OptRawExpr.rawSome value)
          = some rawTerm := by
  obtain ⟨valueTerm, valueEq⟩ := valueTotal
  exact ⟨valueTerm, valueEq⟩

/-- B12 atomic: `rawNilArg` always succeeds for any starting
accumulator (the fold returns the accumulator unchanged). -/
theorem RawArgList.bridgeIsTotalOnRawNilArg {scope : Nat}
    (acc : RawTerm scope) :
    ∃ result,
        RawArgList.foldApps? acc
          (RawArgList.rawNilArg (scope := scope)) = some result :=
  ⟨acc, rfl⟩

/-- B12 compositional: `rawConsArg arg rest` succeeds whenever
`arg` is total and the recursive fold over `rest` succeeds for
every starting accumulator. -/
theorem RawArgList.bridgeIsTotalOnRawConsArg {scope : Nat}
    (arg : RawCallArg scope) (rest : RawArgList scope)
    (acc : RawTerm scope)
    (argTotal : ∃ argTerm, RawCallArg.toRawTerm? arg = some argTerm)
    (restTotal : ∀ acc' : RawTerm scope,
        ∃ result, RawArgList.foldApps? acc' rest = some result) :
    ∃ result,
        RawArgList.foldApps? acc (RawArgList.rawConsArg arg rest)
          = some result := by
  obtain ⟨argTerm, argEq⟩ := argTotal
  obtain ⟨result, restEq⟩ := restTotal (RawTerm.app acc argTerm)
  refine ⟨result, ?_⟩
  show (match RawCallArg.toRawTerm? arg with
        | none => none
        | some argRaw => RawArgList.foldApps? (RawTerm.app acc argRaw) rest)
        = some result
  rw [argEq]; exact restEq

/-- B12 compositional: `rawPositional` reduces to inner totality. -/
theorem RawCallArg.bridgeIsTotalOnRawPositional {scope : Nat}
    (value : RawExpr scope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm) :
    ∃ argTerm,
        RawCallArg.toRawTerm? (RawCallArg.rawPositional value)
          = some argTerm :=
  valueTotal

/-- B12 compositional: `rawNamed` reduces to inner totality
(the `name` field is discarded by the env-free bridge). -/
theorem RawCallArg.bridgeIsTotalOnRawNamed {scope : Nat}
    (name : LowerIdent) (value : RawExpr scope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm) :
    ∃ argTerm,
        RawCallArg.toRawTerm? (RawCallArg.rawNamed name value)
          = some argTerm :=
  valueTotal

/-- B12 compositional: `rawImplicit` reduces to inner totality
(implicit args collapse to the same kernel value as positional). -/
theorem RawCallArg.bridgeIsTotalOnRawImplicit {scope : Nat}
    (value : RawExpr scope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm) :
    ∃ argTerm,
        RawCallArg.toRawTerm? (RawCallArg.rawImplicit value)
          = some argTerm :=
  valueTotal

/-- B12 atomic: `rawNilStmt` always succeeds (the fold returns
the supplied final term unchanged). -/
theorem RawStmtList.bridgeIsTotalOnRawNilStmt {scope : Nat}
    (finalRaw : RawTerm scope) :
    ∃ result,
        RawStmtList.foldBlock?
          (RawStmtList.rawNilStmt (scope := scope)) finalRaw = some result :=
  ⟨finalRaw, rfl⟩

/-- B12 compositional: `rawLetCons` succeeds when the let-value
denotes and the recursive fold over the rest succeeds. -/
theorem RawStmtList.bridgeIsTotalOnRawLetCons {scope outScope : Nat}
    (name : LowerIdent) (typeAnnot : OptRawExpr scope)
    (value : RawExpr scope) (rest : RawStmtList (scope + 1) outScope)
    (finalRaw : RawTerm outScope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm)
    (restTotal : ∃ restRaw,
        RawStmtList.foldBlock? rest finalRaw = some restRaw) :
    ∃ result,
        RawStmtList.foldBlock?
          (RawStmtList.rawLetCons name typeAnnot value rest) finalRaw
          = some result := by
  obtain ⟨valueTerm, valueEq⟩ := valueTotal
  obtain ⟨restRaw, restEq⟩ := restTotal
  refine ⟨RawTerm.app (RawTerm.lam restRaw) valueTerm, ?_⟩
  show (match RawExpr.toRawTerm? value with
        | none => none
        | some valueRaw =>
          match RawStmtList.foldBlock? rest finalRaw with
          | none => none
          | some restRawInner =>
              some (RawTerm.app (RawTerm.lam restRawInner) valueRaw))
        = some (RawTerm.app (RawTerm.lam restRaw) valueTerm)
  rw [valueEq, restEq]

/-- B12 compositional: `rawExprCons` succeeds when the discarded
expression denotes and the recursive fold over the rest succeeds.
The kernel-level encoding wraps the rest in a vacuous `lam`
applied to the discarded value (using `RawTerm.weaken` to lift
the rest to the wider scope). -/
theorem RawStmtList.bridgeIsTotalOnRawExprCons {scope outScope : Nat}
    (value : RawExpr scope) (rest : RawStmtList scope outScope)
    (finalRaw : RawTerm outScope)
    (valueTotal : ∃ valueTerm, RawExpr.toRawTerm? value = some valueTerm)
    (restTotal : ∃ restRaw,
        RawStmtList.foldBlock? rest finalRaw = some restRaw) :
    ∃ result,
        RawStmtList.foldBlock?
          (RawStmtList.rawExprCons value rest) finalRaw = some result := by
  obtain ⟨valueTerm, valueEq⟩ := valueTotal
  obtain ⟨restRaw, restEq⟩ := restTotal
  refine ⟨RawTerm.app (RawTerm.lam restRaw.weaken) valueTerm, ?_⟩
  show (match RawExpr.toRawTerm? value with
        | none => none
        | some valueRaw =>
          match RawStmtList.foldBlock? rest finalRaw with
          | none => none
          | some restRawInner =>
              some (RawTerm.app (RawTerm.lam restRawInner.weaken) valueRaw))
        = some (RawTerm.app (RawTerm.lam restRaw.weaken) valueTerm)
  rw [valueEq, restEq]

/-! ### B12 compositional totality — remaining `RawExpr` ctors -/

/-- B12 compositional: `rawIf cond thenBr elseBr` denotes whenever
all three branches denote (using `OptRawExpr.toRawTermOrUnit?` for
the `else` branch — `rawNone` already denotes to `RawTerm.unit`). -/
theorem RawExpr.bridgeIsTotalOnRawIf {scope : Nat}
    (cond thenBr : RawExpr scope) (elseBr : OptRawExpr scope)
    (condTotal : ∃ condRaw, RawExpr.toRawTerm? cond = some condRaw)
    (thenTotal : ∃ thenRaw, RawExpr.toRawTerm? thenBr = some thenRaw)
    (elseTotal : ∃ elseRaw,
        OptRawExpr.toRawTermOrUnit? elseBr = some elseRaw) :
    ∃ rawTerm,
        RawExpr.toRawTerm? (RawExpr.rawIf cond thenBr elseBr)
          = some rawTerm := by
  obtain ⟨condRaw, condEq⟩ := condTotal
  obtain ⟨thenRaw, thenEq⟩ := thenTotal
  obtain ⟨elseRaw, elseEq⟩ := elseTotal
  refine ⟨RawTerm.boolElim condRaw thenRaw elseRaw, ?_⟩
  show (match RawExpr.toRawTerm? cond with
        | none => none
        | some condRaw' =>
          match RawExpr.toRawTerm? thenBr with
          | none => none
          | some thenRaw' =>
            match OptRawExpr.toRawTermOrUnit? elseBr with
            | none => none
            | some elseRaw' =>
                some (RawTerm.boolElim condRaw' thenRaw' elseRaw'))
        = some (RawTerm.boolElim condRaw thenRaw elseRaw)
  rw [condEq, thenEq, elseEq]

/-- B12 compositional: `rawBlock stmts final` denotes whenever
the final expression denotes and the statement-list fold
succeeds against that final term. -/
theorem RawExpr.bridgeIsTotalOnRawBlock {scope outScope : Nat}
    (stmts : RawStmtList scope outScope) (final : RawExpr outScope)
    (finalTotal : ∃ finalRaw, RawExpr.toRawTerm? final = some finalRaw)
    (stmtsTotal : ∀ finalRaw' : RawTerm outScope,
        ∃ result, RawStmtList.foldBlock? stmts finalRaw' = some result) :
    ∃ rawTerm,
        RawExpr.toRawTerm? (RawExpr.rawBlock stmts final) = some rawTerm := by
  obtain ⟨finalRaw, finalEq⟩ := finalTotal
  obtain ⟨result, stmtsEq⟩ := stmtsTotal finalRaw
  refine ⟨result, ?_⟩
  show (match RawExpr.toRawTerm? final with
        | none => none
        | some finalRawInner => RawStmtList.foldBlock? stmts finalRawInner)
        = some result
  rw [finalEq]; exact stmtsEq

/-! ### B12 lifted — remaining `Expr` ctors

Each `Expr.denoteIsTotalOn*` theorem lifts the corresponding
`RawExpr` totality to the decorated family by definitional
unfolding of `Expr.denote = Expr.toRawTerm? = RawExpr.toRawTerm?
∘ Expr.toRaw`. -/

/-- B12 lifted: `parenExpr` denotes whenever its inner does. -/
theorem Expr.denoteIsTotalOnParenExpr {scope : Nat} {innerRaw : RawExpr scope}
    (inner : Expr innerRaw) (pos : SrcPos)
    (innerTotal : ∃ innerTerm, RawExpr.toRawTerm? innerRaw = some innerTerm) :
    ∃ rawTerm,
        Expr.denote (Expr.parenExpr inner pos) = some rawTerm :=
  RawExpr.bridgeIsTotalOnRawParen (scope := scope) innerRaw innerTotal

/-! ## S04 bridge invariant theorem (#1288)

The semantic equivalence `e ≅ r` between a decorated `Expr raw`
and a kernel `RawTerm scope` is, by the design choice declared at
the top of this file, the equation `Expr.denote e = some r`.

Since `Expr.denote := Expr.toRawTerm?` is `@[reducible]`, the
"bridge invariant" (bridge-success implies semantic equivalence
between source `Expr` and target `RawTerm`) is the iff between
the two `Option`-equality forms — `rfl` after unfolding `denote`.

This theorem is intentionally trivial: the value lies in NAMING
the invariant for downstream consumers, not in proof content.
Future S-series entries for the env-aware bridge thread the same
invariant via `Expr.toRawTermWithEnv?`. -/

/-- S04 (tracker #1288): the bridge result IS the semantic
equivalence witness.  Whenever `Expr.toRawTerm? expr = some
target`, the decorated `Expr` denotes to `target`, and vice
versa.  The equivalence relation `≅` between source surface
and target kernel is exactly this denotational equality. -/
theorem Expr.bridge_invariant {scope : Nat} {raw : RawExpr scope}
    (expr : Expr raw) (target : RawTerm scope) :
    Expr.toRawTerm? expr = some target ↔ Expr.denote expr = some target :=
  Iff.rfl

/-- S04 raw counterpart: the same invariant at the
underlying-`RawExpr` layer.  Bridges the two-tier Surface AST
to the kernel by witnessing semantic equivalence
`raw ≅ target` as `RawExpr.denote raw = some target`. -/
theorem RawExpr.bridge_invariant {scope : Nat}
    (raw : RawExpr scope) (target : RawTerm scope) :
    RawExpr.toRawTerm? raw = some target ↔ RawExpr.denote raw = some target :=
  Iff.rfl

end LeanFX2.Surface
