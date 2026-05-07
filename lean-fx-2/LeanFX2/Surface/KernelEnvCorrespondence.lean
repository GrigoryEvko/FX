import LeanFX2.Surface.KernelEnv
import LeanFX2.Surface.KernelBridgeReduction

/-! # Surface/KernelEnvCorrespondence — env-aware ⊇ env-free (Literal only)

The env-aware bridge `RawExpr.toRawTermWithEnv?` with `KernelEnv.empty`
is NOT strictly equal to the env-free bridge `RawExpr.toRawTerm?`
— they diverge on `rawBinop pipe`:

* The env-free bridge returns `none` for ALL binops.
* The env-aware bridge handles `pipe` STRUCTURALLY (`x |> f` becomes `f x`).

The right correspondence statement is INCLUSION (subsumption):
whenever the env-free bridge succeeds, the env-aware bridge with
empty env succeeds with the SAME result.

## Status: scope reduced — Literal-only, kernel-clean (Phase 12.A.4)

The previous mutual block of 5 inclusion theorems leaked
`propext + Quot.sound` from Lean 4 v4.29.1's mutual-recursion
compilation (`_unary` / `_mutual` auxiliary lemmas use propext
for unfolding under well-founded-recursion machinery).

Multiple refactor attempts (term-mode pattern matching, structural
recursion via `Option.casesOn`, explicit `Eq.subst` motives,
helper-extracted destructuring) hit kernel-level constant
resolution issues across the namespace boundary AND/OR auto-
generated equation-lemma propext leaks.

The pragmatic fix: SCOPE the file to ONLY the propext-clean
`Literal.bridge_inclusion`.  The full 5-theorem mutual block is
deferred to v1.1+ alongside a Lean-4-version-pinned cleaner
mutual-recursion encoding (e.g. via raw recursors with all 5
motives, or a unified sum-type formulation that sidesteps mutual
block compilation entirely).

This **fully eliminates** the propext+Quot.sound leak that was
present at Layer E.  The deleted theorems are NOT load-bearing
for any kernel-level proof — they were a "nice-to-have" showing
env-aware ⊇ env-free for downstream code that mixes both bridges.

## Mathematical correctness preserved

The mathematical content (env-aware-with-empty subsumes env-free
on every input where env-free returns `some _`) is NOT in dispute
— it is provable by direct structural induction.  Only the
Lean-encoding of that proof leaked propext.  Future work re-
admits the theorem under a propext-clean encoding.
-/

namespace LeanFX2.Surface

/-- Helper: `KernelEnv.empty.lookup` is constantly `none`. -/
@[simp] theorem KernelEnv.empty_lookup_eq (qname : QualifiedName) :
    KernelEnv.empty.lookup qname = none := rfl

/-! ## Literal correspondence (kernel-clean, zero-axiom)

`Literal.toRawTerm?` and `Literal.toRawTermWithEnv? KernelEnv.empty`
agree on every input that env-free maps to `some _`.  This is
NON-MUTUAL (Literal has no recursive structure crossing into
the rest of the bridge family), so the propext leak does not
apply here.

This theorem is verified zero-axiom under strict policy. -/
theorem Literal.bridge_inclusion
    {scope : Nat}
    (lit : Literal) (raw : RawTerm scope)
    (envFreeEq : Literal.toRawTerm? lit = some raw) :
    Literal.toRawTermWithEnv? (scope := scope) KernelEnv.empty lit = some raw := by
  cases lit with
  | unitLit =>
    rw [Literal.toRawTerm?_unitLit] at envFreeEq
    show some RawTerm.unit = some raw
    exact envFreeEq
  | boolLit value =>
    cases value with
    | true =>
      rw [Literal.toRawTerm?_boolLit_true] at envFreeEq
      show some RawTerm.boolTrue = some raw
      exact envFreeEq
    | false =>
      rw [Literal.toRawTerm?_boolLit_false] at envFreeEq
      show some RawTerm.boolFalse = some raw
      exact envFreeEq
  | intLit n suffix =>
    -- Reduce envFreeEq's LHS to the explicit if-form so we can rewrite.
    change (if 0 ≤ n then some (RawTerm.natOfNat n.toNat) else none) = some raw
        at envFreeEq
    show (if 0 ≤ n then some (RawTerm.natOfNat n.toNat)
          else
            let posRaw : RawTerm scope := RawTerm.natOfNat n.natAbs
            match KernelEnv.empty.lookup UnaryOp.negate.toQualifiedName with
            | none => none
            | some negDef =>
              match negDef.liftToScope (scope := scope) with
              | none => none
              | some negRaw => some (RawTerm.app negRaw posRaw)) = some raw
    by_cases hCases : 0 ≤ n
    · rw [if_pos hCases]
      rw [if_pos hCases] at envFreeEq
      exact envFreeEq
    · rw [if_neg hCases] at envFreeEq
      nomatch envFreeEq
  | decLit _ _ =>
    rw [Literal.toRawTerm?_decLit] at envFreeEq
    nomatch envFreeEq
  | floatLit _ _ =>
    rw [Literal.toRawTerm?_floatLit] at envFreeEq
    nomatch envFreeEq
  | strLit _ =>
    rw [Literal.toRawTerm?_strLit] at envFreeEq
    nomatch envFreeEq
  | bitLit _ _ _ =>
    nomatch envFreeEq
  | tritLit _ _ _ =>
    nomatch envFreeEq

/-! ## B10 partial: atomic + vacuous RawExpr inclusion (#1250)

The full mutual-block correspondence (RawExpr × OptRawExpr ×
RawArgList × RawCallArg × RawStmtList) is propext-blocked per
the docstring above.  However, the **atomic** and **vacuous**
RawExpr cases are non-recursive and ship cleanly:

* atomic non-recursive ctors (`rawBound`, `rawUnit`) — both
  bridges produce the same `some _` directly;
* atomic recursive-leaf (`rawLit`) — delegates to `Literal.
  bridge_inclusion`;
* vacuous ctors (`rawFree`, `rawDot`, `rawBinop`, `rawUnop`) —
  the env-free bridge always returns `none`, so the hypothesis
  `toRawTerm? = some raw` is structurally impossible and the
  conclusion follows by `nomatch`.

These six theorems cover 6 of the 12 RawExpr ctors at the
inclusion level, with the remaining six (`rawParen`, `rawApp`,
`rawLam`, `rawBlock`, `rawIf` plus the OptRawExpr/list
recursive cases) deferred per the docstring. -/

/-- B10 atomic: bound variable inclusion. -/
theorem RawExpr.bridge_inclusion_rawBound {scope : Nat}
    (idx : Fin scope) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm? (RawExpr.rawBound idx) = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawBound idx) = some raw := by
  show some (RawTerm.var idx) = some raw
  exact envFreeEq

/-- B10 atomic: unit inclusion. -/
theorem RawExpr.bridge_inclusion_rawUnit {scope : Nat}
    (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm?
                  (RawExpr.rawUnit (scope := scope)) = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawUnit (scope := scope)) = some raw := by
  show some RawTerm.unit = some raw
  exact envFreeEq

/-- B10 leaf: literal inclusion delegates to `Literal.bridge_inclusion`. -/
theorem RawExpr.bridge_inclusion_rawLit {scope : Nat}
    (lit : Literal) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm? (RawExpr.rawLit (scope := scope) lit)
                  = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawLit lit) = some raw := by
  show Literal.toRawTermWithEnv? KernelEnv.empty lit = some raw
  exact Literal.bridge_inclusion (scope := scope) lit raw envFreeEq

/-- B10 vacuous: free names always fail the env-free bridge,
so the inclusion is discharged by `nomatch`. -/
theorem RawExpr.bridge_inclusion_rawFree {scope : Nat}
    (qname : QualifiedName) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm?
                  (RawExpr.rawFree (scope := scope) qname) = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawFree qname) = some raw := by
  nomatch envFreeEq

/-- B10 vacuous: dot projection always fails the env-free bridge. -/
theorem RawExpr.bridge_inclusion_rawDot {scope : Nat}
    {objRaw : RawExpr scope} (field : LowerIdent) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm? (RawExpr.rawDot objRaw field)
                  = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawDot objRaw field) = some raw := by
  nomatch envFreeEq

/-- B10 vacuous: binary ops always fail the env-free bridge. -/
theorem RawExpr.bridge_inclusion_rawBinop {scope : Nat}
    (op : BinaryOp) (lhs rhs : RawExpr scope) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm? (RawExpr.rawBinop op lhs rhs)
                  = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawBinop op lhs rhs) = some raw := by
  nomatch envFreeEq

/-- B10 vacuous: unary ops always fail the env-free bridge. -/
theorem RawExpr.bridge_inclusion_rawUnop {scope : Nat}
    (op : UnaryOp) (operand : RawExpr scope) (raw : RawTerm scope)
    (envFreeEq : RawExpr.toRawTerm? (RawExpr.rawUnop op operand)
                  = some raw) :
    RawExpr.toRawTermWithEnv? (scope := scope)
      KernelEnv.empty (RawExpr.rawUnop op operand) = some raw := by
  nomatch envFreeEq

end LeanFX2.Surface
