import LeanFX2.Surface.KernelBridge

/-! # Surface/KernelBridgeReduction — per-ctor reduction lemmas

Explicit per-ctor `_eq` lemmas for the env-free bridge mutual
block in `Surface/KernelBridge.lean`.  Downstream proofs use
`rw` / `simp only` instead of unfolding the mutual block by hand.

Implementation note: Lean 4 v4.29.1 reduces these mutual block
definitions by `rfl` when the scrutinee is a concrete constructor
— pattern-match reduction on ctor heads fires.  The
KernelBridge.lean docstring's claim that "mutual definitions
don't reduce by rfl" was overly cautious — it holds for some
tactics (`unfold` over-expands when RHS also mentions the
function) but `rfl` works for ctor-head LHSes.

## Why this matters

Bridge correctness (`B01–B12`), bridge invariants
(`S01–S04`), and the env-aware/env-free equivalence (`B10`) all
reason about `RawExpr.toRawTerm?` on specific constructors.

## Coverage (30 lemmas)

* `RawExpr.toRawTerm?` — 12 ctor lemmas (R01–R12)
* `RawArgList.foldApps?` — 2 ctor lemmas
* `RawCallArg.toRawTerm?` — 3 ctor lemmas
* `OptRawExpr.toRawTermOrUnit?` — 2 ctor lemmas
* `RawStmtList.foldBlock?` — 3 ctor lemmas
* `Literal.toRawTerm?` — 8 ctor lemmas (non-mutual)

Zero-axiom verified per declaration via AuditAll.
-/

namespace LeanFX2.Surface

variable {scope : Nat}

/-! ## Literal.toRawTerm? per-ctor lemmas

`Literal.toRawTerm?` is NOT in the mutual block — plain function. -/

theorem Literal.toRawTerm?_unitLit :
    Literal.toRawTerm? (scope := scope) Literal.unitLit
      = some RawTerm.unit := rfl

theorem Literal.toRawTerm?_boolLit_true :
    Literal.toRawTerm? (scope := scope) (Literal.boolLit true)
      = some RawTerm.boolTrue := rfl

theorem Literal.toRawTerm?_boolLit_false :
    Literal.toRawTerm? (scope := scope) (Literal.boolLit false)
      = some RawTerm.boolFalse := rfl

theorem Literal.toRawTerm?_intLit_zero (suffix : Option String) :
    Literal.toRawTerm? (scope := scope) (Literal.intLit 0 suffix)
      = some RawTerm.natZero := rfl

theorem Literal.toRawTerm?_decLit
    (mantissa : String) (suffix : Option String) :
    Literal.toRawTerm? (scope := scope) (Literal.decLit mantissa suffix)
      = none := rfl

theorem Literal.toRawTerm?_floatLit
    (mantissa : String) (suffix : String) :
    Literal.toRawTerm? (scope := scope) (Literal.floatLit mantissa suffix)
      = none := rfl

theorem Literal.toRawTerm?_strLit (value : String) :
    Literal.toRawTerm? (scope := scope) (Literal.strLit value) = none := rfl

/-- Negative integer literal returns `none` from the env-free
bridge.  Negatives need `Std.Int.neg` via the env-aware bridge.

Hypothesis form: takes `¬(0 ≤ n)` directly rather than `n < 0`.
This keeps the lemma propext-free — stdlib's `Int.lt_irrefl`
and `Int.lt_of_le_of_lt` both leak propext, so reducing
`n < 0 → ¬(0 ≤ n)` is the user's responsibility (typically by
`decide` for concrete numerals or by accepting the propext hit
at the call site). -/
theorem Literal.toRawTerm?_intLit_neg
    (n : Int) (suffix : Option String) (notNonNeg : ¬(0 ≤ n)) :
    Literal.toRawTerm? (scope := scope) (Literal.intLit n suffix) = none := by
  show (if 0 ≤ n then some (RawTerm.natOfNat n.toNat) else none) = none
  exact if_neg notNonNeg

/-! ## RawExpr.toRawTerm? per-ctor lemmas (mutual block)

For ctor-applied scrutinees, Lean's pattern-match reduction
fires and `rfl` discharges the goal. -/

theorem RawExpr.toRawTerm?_rawBound (idx : Fin scope) :
    (RawExpr.rawBound idx).toRawTerm? = some (RawTerm.var idx) := rfl

theorem RawExpr.toRawTerm?_rawFree (qname : QualifiedName) :
    (RawExpr.rawFree (scope := scope) qname).toRawTerm? = none := rfl

theorem RawExpr.toRawTerm?_rawLit (lit : Literal) :
    (RawExpr.rawLit (scope := scope) lit).toRawTerm?
      = Literal.toRawTerm? lit := rfl

theorem RawExpr.toRawTerm?_rawUnit :
    (RawExpr.rawUnit (scope := scope)).toRawTerm? = some RawTerm.unit := rfl

theorem RawExpr.toRawTerm?_rawParen (inner : RawExpr scope) :
    (RawExpr.rawParen inner).toRawTerm? = inner.toRawTerm? := rfl

theorem RawExpr.toRawTerm?_rawDot (obj : RawExpr scope) (field : LowerIdent) :
    (RawExpr.rawDot obj field).toRawTerm? = none := rfl

theorem RawExpr.toRawTerm?_rawApp (fn : RawExpr scope) (args : RawArgList scope) :
    (RawExpr.rawApp fn args).toRawTerm?
      = match fn.toRawTerm? with
        | none => none
        | some fnRaw => RawArgList.foldApps? fnRaw args := rfl

theorem RawExpr.toRawTerm?_rawBinop
    (op : BinaryOp) (lhs rhs : RawExpr scope) :
    (RawExpr.rawBinop op lhs rhs).toRawTerm? = none := rfl

theorem RawExpr.toRawTerm?_rawUnop (op : UnaryOp) (operand : RawExpr scope) :
    (RawExpr.rawUnop op operand).toRawTerm? = none := rfl

theorem RawExpr.toRawTerm?_rawLam
    (paramName : LowerIdent) (paramType : OptRawExpr scope)
    (body : RawExpr (scope + 1)) :
    (RawExpr.rawLam paramName paramType body).toRawTerm?
      = match body.toRawTerm? with
        | none => none
        | some bodyRaw => some (RawTerm.lam bodyRaw) := rfl

theorem RawExpr.toRawTerm?_rawBlock
    {outScope : Nat} (stmts : RawStmtList scope outScope) (final : RawExpr outScope) :
    (RawExpr.rawBlock stmts final).toRawTerm?
      = match final.toRawTerm? with
        | none => none
        | some finalRaw => RawStmtList.foldBlock? stmts finalRaw := rfl

theorem RawExpr.toRawTerm?_rawIf
    (cond thenBr : RawExpr scope) (elseBr : OptRawExpr scope) :
    (RawExpr.rawIf cond thenBr elseBr).toRawTerm?
      = match cond.toRawTerm? with
        | none => none
        | some condRaw =>
          match thenBr.toRawTerm? with
          | none => none
          | some thenRaw =>
            match OptRawExpr.toRawTermOrUnit? elseBr with
            | none => none
            | some elseRaw => some (RawTerm.boolElim condRaw thenRaw elseRaw) := rfl

/-! ## RawArgList.foldApps? per-ctor lemmas -/

theorem RawArgList.foldApps?_rawNilArg (acc : RawTerm scope) :
    RawArgList.foldApps? acc (RawArgList.rawNilArg) = some acc := rfl

theorem RawArgList.foldApps?_rawConsArg
    (acc : RawTerm scope) (arg : RawCallArg scope) (rest : RawArgList scope) :
    RawArgList.foldApps? acc (RawArgList.rawConsArg arg rest)
      = match RawCallArg.toRawTerm? arg with
        | none => none
        | some argRaw => RawArgList.foldApps? (RawTerm.app acc argRaw) rest := rfl

/-! ## RawCallArg.toRawTerm? per-ctor lemmas -/

theorem RawCallArg.toRawTerm?_rawPositional (value : RawExpr scope) :
    RawCallArg.toRawTerm? (RawCallArg.rawPositional value)
      = value.toRawTerm? := rfl

theorem RawCallArg.toRawTerm?_rawNamed
    (name : LowerIdent) (value : RawExpr scope) :
    RawCallArg.toRawTerm? (RawCallArg.rawNamed name value)
      = value.toRawTerm? := rfl

theorem RawCallArg.toRawTerm?_rawImplicit (value : RawExpr scope) :
    RawCallArg.toRawTerm? (RawCallArg.rawImplicit value)
      = value.toRawTerm? := rfl

/-! ## OptRawExpr.toRawTermOrUnit? per-ctor lemmas -/

theorem OptRawExpr.toRawTermOrUnit?_rawNone :
    OptRawExpr.toRawTermOrUnit? (OptRawExpr.rawNone (scope := scope))
      = some RawTerm.unit := rfl

theorem OptRawExpr.toRawTermOrUnit?_rawSome (value : RawExpr scope) :
    OptRawExpr.toRawTermOrUnit? (OptRawExpr.rawSome value)
      = value.toRawTerm? := rfl

/-! ## RawStmtList.foldBlock? per-ctor lemmas -/

theorem RawStmtList.foldBlock?_rawNilStmt
    (finalRaw : RawTerm scope) :
    RawStmtList.foldBlock? (RawStmtList.rawNilStmt) finalRaw
      = some finalRaw := rfl

theorem RawStmtList.foldBlock?_rawLetCons
    {outScope : Nat}
    (name : LowerIdent) (typeAnnot : OptRawExpr scope)
    (value : RawExpr scope)
    (rest : RawStmtList (scope + 1) outScope)
    (finalRaw : RawTerm outScope) :
    RawStmtList.foldBlock?
        (RawStmtList.rawLetCons name typeAnnot value rest) finalRaw
      = match value.toRawTerm? with
        | none => none
        | some valueRaw =>
          match RawStmtList.foldBlock? rest finalRaw with
          | none => none
          | some restRaw => some (RawTerm.app (RawTerm.lam restRaw) valueRaw) := rfl

theorem RawStmtList.foldBlock?_rawExprCons
    {outScope : Nat}
    (value : RawExpr scope)
    (rest : RawStmtList scope outScope)
    (finalRaw : RawTerm outScope) :
    RawStmtList.foldBlock?
        (RawStmtList.rawExprCons value rest) finalRaw
      = match value.toRawTerm? with
        | none => none
        | some valueRaw =>
          match RawStmtList.foldBlock? rest finalRaw with
          | none => none
          | some restRaw => some (RawTerm.app (RawTerm.lam restRaw.weaken) valueRaw) := rfl

end LeanFX2.Surface
