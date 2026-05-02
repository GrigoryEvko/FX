import LeanFX2.Surface.KernelEnv
import LeanFX2.Surface.KernelBridgeReduction

/-! # Surface/KernelEnvCorrespondence — env-aware ⊇ env-free

The env-aware bridge `RawExpr.toRawTermWithEnv?` with `Env.empty`
is NOT strictly equal to the env-free bridge `RawExpr.toRawTerm?`
— they diverge on `rawBinop pipe`:

* Env-free returns `none` for ALL binops (no kernel desugaring).
* Env-aware handles `pipe` STRUCTURALLY (`x |> f` becomes
  `f x` with no env lookup), so env-aware-with-empty returns
  `some (app rhs lhs)` when env-free returns `none`.

The right correspondence statement is INCLUSION (subsumption):
whenever the env-free bridge succeeds, the env-aware bridge with
empty env succeeds with the SAME result.  The reverse direction
fails for `pipe`.

```lean
theorem RawExpr.bridge_inclusion :
    e.toRawTerm? = some r →
    RawExpr.toRawTermWithEnv? Env.empty e = some r
```

This establishes env-aware as a CONSERVATIVE EXTENSION of
env-free: anywhere downstream code uses env-free's `some`
result, it can substitute env-aware's same result.

## Axiom status (KNOWN-LEAKY — Phase 11+ cleanup)

`Literal.bridge_inclusion` is zero-axiom.  The mutual block
of `RawExpr.bridge_inclusion` + 4 siblings (and the headline
`RawExpr.toRawTermWithEnv?_empty_subsumes` corollary) depend on
`propext` and `Quot.sound`.

Probes show that individual building blocks (cases-with-equation
on `Option`, `nomatch` on impossible equalities, `rw [...] at h`
chains) are propext-clean in isolation.  The leak emerges from
the mutual-block structural recursion's auto-generated equation
lemmas — Lean's match compiler emits propext-using helpers when
combining nested `cases`+`rw` patterns across mutual recursion.

The result is mathematically correct (proof is structurally
exhaustive over all 5 families' constructors, terminates by
`sizeOf`, and discharges every case).  It is propext-tainted
purely from the proof-encoding strategy.

A propext-clean reformulation is feasible by switching to
`Option.recOn` / explicit recursors / term-mode match
expressions; deferred as a follow-up cleanup task.

Per `AXIOMS.md` Layer E policy: documented exception pending
refactor.
-/

namespace LeanFX2.Surface

/-- Helper: `Env.empty.lookup` is constantly `none`. -/
@[simp] theorem Env.empty_lookup_eq (qname : QualifiedName) :
    Env.empty.lookup qname = none := rfl

/-! ## Literal correspondence (non-mutual)

`Literal.toRawTerm?` and `Literal.toRawTermWithEnv? Env.empty`
agree on every input that env-free maps to `some _`.  Negative
ints, decLit, floatLit, strLit, bitLit, tritLit all return `none`
in env-free, so the implication is vacuous for those. -/
theorem Literal.bridge_inclusion
    {scope : Nat}
    (lit : Literal) (raw : RawTerm scope)
    (envFreeEq : Literal.toRawTerm? lit = some raw) :
    Literal.toRawTermWithEnv? (scope := scope) Env.empty lit = some raw := by
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
            match Env.empty.lookup UnaryOp.negate.toQualifiedName with
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
      -- After if_neg, envFreeEq : none = some raw
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
    -- env-free returns none for bitLit (falls through `intLit/...`).
    nomatch envFreeEq
  | tritLit _ _ _ =>
    nomatch envFreeEq

/-! ## Mutual bridge inclusion

Five mutually-recursive theorems mirroring the bridge's 5-function
mutual block.  Each binds its own `scope` (no shared variable)
because some recursive calls cross scope boundaries (e.g.
`rawLam`'s body is at `scope + 1`, `rawBlock`'s final is at the
inner `outScope`). -/

mutual

theorem RawExpr.bridge_inclusion
    {scope : Nat}
    (e : RawExpr scope) (raw : RawTerm scope)
    (envFreeEq : e.toRawTerm? = some raw) :
    RawExpr.toRawTermWithEnv? Env.empty e = some raw := by
  cases e with
  | rawBound idx =>
    rw [RawExpr.toRawTerm?_rawBound] at envFreeEq
    show some (RawTerm.var idx) = some raw
    exact envFreeEq
  | rawFree qname =>
    rw [RawExpr.toRawTerm?_rawFree] at envFreeEq
    nomatch envFreeEq
  | rawLit lit =>
    rw [RawExpr.toRawTerm?_rawLit] at envFreeEq
    show Literal.toRawTermWithEnv? Env.empty lit = some raw
    exact Literal.bridge_inclusion lit raw envFreeEq
  | rawUnit =>
    rw [RawExpr.toRawTerm?_rawUnit] at envFreeEq
    show some RawTerm.unit = some raw
    exact envFreeEq
  | rawParen inner =>
    rw [RawExpr.toRawTerm?_rawParen] at envFreeEq
    show RawExpr.toRawTermWithEnv? Env.empty inner = some raw
    exact RawExpr.bridge_inclusion inner raw envFreeEq
  | rawDot _ _ =>
    rw [RawExpr.toRawTerm?_rawDot] at envFreeEq
    nomatch envFreeEq
  | rawApp fn args =>
    rw [RawExpr.toRawTerm?_rawApp] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty fn with
          | none => none
          | some fnRaw => RawArgList.foldAppsEnv? Env.empty fnRaw args) = some raw
    cases hFn : fn.toRawTerm? with
    | none =>
      rw [hFn] at envFreeEq
      nomatch envFreeEq
    | some fnRaw =>
      rw [hFn] at envFreeEq
      have fnLifted : RawExpr.toRawTermWithEnv? Env.empty fn = some fnRaw :=
        RawExpr.bridge_inclusion fn fnRaw hFn
      rw [fnLifted]
      exact RawArgList.foldAppsEnv_inclusion args fnRaw raw envFreeEq
  | rawBinop _ _ _ =>
    rw [RawExpr.toRawTerm?_rawBinop] at envFreeEq
    nomatch envFreeEq
  | rawUnop _ _ =>
    rw [RawExpr.toRawTerm?_rawUnop] at envFreeEq
    nomatch envFreeEq
  | rawLam paramName paramType body =>
    rw [RawExpr.toRawTerm?_rawLam] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty body with
          | none => none
          | some bodyRaw => some (RawTerm.lam bodyRaw)) = some raw
    cases hBody : body.toRawTerm? with
    | none =>
      rw [hBody] at envFreeEq
      nomatch envFreeEq
    | some bodyRaw =>
      rw [hBody] at envFreeEq
      have bodyLifted : RawExpr.toRawTermWithEnv? Env.empty body = some bodyRaw :=
        RawExpr.bridge_inclusion body bodyRaw hBody
      rw [bodyLifted]
      exact envFreeEq
  | rawBlock stmts final =>
    rw [RawExpr.toRawTerm?_rawBlock] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty final with
          | none => none
          | some finalRaw => RawStmtList.foldBlockEnv? Env.empty stmts finalRaw) = some raw
    cases hFinal : final.toRawTerm? with
    | none =>
      rw [hFinal] at envFreeEq
      nomatch envFreeEq
    | some finalRaw =>
      rw [hFinal] at envFreeEq
      have finalLifted : RawExpr.toRawTermWithEnv? Env.empty final = some finalRaw :=
        RawExpr.bridge_inclusion final finalRaw hFinal
      rw [finalLifted]
      exact RawStmtList.foldBlockEnv_inclusion stmts finalRaw raw envFreeEq
  | rawIf cond thenBr elseBr =>
    rw [RawExpr.toRawTerm?_rawIf] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty cond with
          | none => none
          | some condRaw =>
            match RawExpr.toRawTermWithEnv? Env.empty thenBr with
            | none => none
            | some thenRaw =>
              match OptRawExpr.toRawTermOrUnitEnv? Env.empty elseBr with
              | none => none
              | some elseRaw =>
                some (RawTerm.boolElim condRaw thenRaw elseRaw)) = some raw
    cases hCond : cond.toRawTerm? with
    | none =>
      rw [hCond] at envFreeEq
      nomatch envFreeEq
    | some condRaw =>
      rw [hCond] at envFreeEq
      have condLifted : RawExpr.toRawTermWithEnv? Env.empty cond = some condRaw :=
        RawExpr.bridge_inclusion cond condRaw hCond
      rw [condLifted]
      cases hThen : thenBr.toRawTerm? with
      | none =>
        rw [hThen] at envFreeEq
        nomatch envFreeEq
      | some thenRaw =>
        rw [hThen] at envFreeEq
        have thenLifted : RawExpr.toRawTermWithEnv? Env.empty thenBr = some thenRaw :=
          RawExpr.bridge_inclusion thenBr thenRaw hThen
        rw [thenLifted]
        cases hElse : OptRawExpr.toRawTermOrUnit? elseBr with
        | none =>
          rw [hElse] at envFreeEq
          nomatch envFreeEq
        | some elseRaw =>
          rw [hElse] at envFreeEq
          have elseLifted : OptRawExpr.toRawTermOrUnitEnv? Env.empty elseBr = some elseRaw :=
            OptRawExpr.toRawTermOrUnit_inclusion elseBr elseRaw hElse
          rw [elseLifted]
          exact envFreeEq
termination_by sizeOf e

theorem RawArgList.foldAppsEnv_inclusion
    {scope : Nat}
    (args : RawArgList scope) (acc : RawTerm scope) (raw : RawTerm scope)
    (envFreeEq : RawArgList.foldApps? acc args = some raw) :
    RawArgList.foldAppsEnv? Env.empty acc args = some raw := by
  cases args with
  | rawNilArg =>
    rw [RawArgList.foldApps?_rawNilArg] at envFreeEq
    show some acc = some raw
    exact envFreeEq
  | rawConsArg arg rest =>
    rw [RawArgList.foldApps?_rawConsArg] at envFreeEq
    show (match RawCallArg.toRawTermWithEnv? Env.empty arg with
          | none => none
          | some argRaw => RawArgList.foldAppsEnv? Env.empty (RawTerm.app acc argRaw) rest)
        = some raw
    cases hArg : RawCallArg.toRawTerm? arg with
    | none =>
      rw [hArg] at envFreeEq
      nomatch envFreeEq
    | some argRaw =>
      rw [hArg] at envFreeEq
      have argLifted : RawCallArg.toRawTermWithEnv? Env.empty arg = some argRaw :=
        RawCallArg.bridge_inclusion arg argRaw hArg
      rw [argLifted]
      exact RawArgList.foldAppsEnv_inclusion rest (RawTerm.app acc argRaw) raw envFreeEq
termination_by sizeOf args

theorem RawCallArg.bridge_inclusion
    {scope : Nat}
    (callArg : RawCallArg scope) (raw : RawTerm scope)
    (envFreeEq : RawCallArg.toRawTerm? callArg = some raw) :
    RawCallArg.toRawTermWithEnv? Env.empty callArg = some raw := by
  cases callArg with
  | rawPositional value =>
    rw [RawCallArg.toRawTerm?_rawPositional] at envFreeEq
    show RawExpr.toRawTermWithEnv? Env.empty value = some raw
    exact RawExpr.bridge_inclusion value raw envFreeEq
  | rawNamed name value =>
    rw [RawCallArg.toRawTerm?_rawNamed] at envFreeEq
    show RawExpr.toRawTermWithEnv? Env.empty value = some raw
    exact RawExpr.bridge_inclusion value raw envFreeEq
  | rawImplicit value =>
    rw [RawCallArg.toRawTerm?_rawImplicit] at envFreeEq
    show RawExpr.toRawTermWithEnv? Env.empty value = some raw
    exact RawExpr.bridge_inclusion value raw envFreeEq
termination_by sizeOf callArg

theorem OptRawExpr.toRawTermOrUnit_inclusion
    {scope : Nat}
    (optExpr : OptRawExpr scope) (raw : RawTerm scope)
    (envFreeEq : OptRawExpr.toRawTermOrUnit? optExpr = some raw) :
    OptRawExpr.toRawTermOrUnitEnv? Env.empty optExpr = some raw := by
  cases optExpr with
  | rawNone =>
    rw [OptRawExpr.toRawTermOrUnit?_rawNone] at envFreeEq
    show some RawTerm.unit = some raw
    exact envFreeEq
  | rawSome value =>
    rw [OptRawExpr.toRawTermOrUnit?_rawSome] at envFreeEq
    show RawExpr.toRawTermWithEnv? Env.empty value = some raw
    exact RawExpr.bridge_inclusion value raw envFreeEq
termination_by sizeOf optExpr

theorem RawStmtList.foldBlockEnv_inclusion
    {scope outScope : Nat}
    (stmts : RawStmtList scope outScope) (finalRaw : RawTerm outScope)
    (raw : RawTerm scope)
    (envFreeEq : RawStmtList.foldBlock? stmts finalRaw = some raw) :
    RawStmtList.foldBlockEnv? Env.empty stmts finalRaw = some raw := by
  cases stmts with
  | rawNilStmt =>
    rw [RawStmtList.foldBlock?_rawNilStmt] at envFreeEq
    show some finalRaw = some raw
    exact envFreeEq
  | rawLetCons name typeAnnot value rest =>
    rw [RawStmtList.foldBlock?_rawLetCons] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty value with
          | none => none
          | some valueRaw =>
            match RawStmtList.foldBlockEnv? Env.empty rest finalRaw with
            | none => none
            | some restRaw => some (RawTerm.app (RawTerm.lam restRaw) valueRaw))
        = some raw
    cases hValue : value.toRawTerm? with
    | none =>
      rw [hValue] at envFreeEq
      nomatch envFreeEq
    | some valueRaw =>
      rw [hValue] at envFreeEq
      have valueLifted : RawExpr.toRawTermWithEnv? Env.empty value = some valueRaw :=
        RawExpr.bridge_inclusion value valueRaw hValue
      rw [valueLifted]
      cases hRest : RawStmtList.foldBlock? rest finalRaw with
      | none =>
        rw [hRest] at envFreeEq
        nomatch envFreeEq
      | some restRaw =>
        rw [hRest] at envFreeEq
        have restLifted : RawStmtList.foldBlockEnv? Env.empty rest finalRaw = some restRaw :=
          RawStmtList.foldBlockEnv_inclusion rest finalRaw restRaw hRest
        rw [restLifted]
        exact envFreeEq
  | rawExprCons value rest =>
    rw [RawStmtList.foldBlock?_rawExprCons] at envFreeEq
    show (match RawExpr.toRawTermWithEnv? Env.empty value with
          | none => none
          | some valueRaw =>
            match RawStmtList.foldBlockEnv? Env.empty rest finalRaw with
            | none => none
            | some restRaw => some (RawTerm.app (RawTerm.lam restRaw.weaken) valueRaw))
        = some raw
    cases hValue : value.toRawTerm? with
    | none =>
      rw [hValue] at envFreeEq
      nomatch envFreeEq
    | some valueRaw =>
      rw [hValue] at envFreeEq
      have valueLifted : RawExpr.toRawTermWithEnv? Env.empty value = some valueRaw :=
        RawExpr.bridge_inclusion value valueRaw hValue
      rw [valueLifted]
      cases hRest : RawStmtList.foldBlock? rest finalRaw with
      | none =>
        rw [hRest] at envFreeEq
        nomatch envFreeEq
      | some restRaw =>
        rw [hRest] at envFreeEq
        have restLifted : RawStmtList.foldBlockEnv? Env.empty rest finalRaw = some restRaw :=
          RawStmtList.foldBlockEnv_inclusion rest finalRaw restRaw hRest
        rw [restLifted]
        exact envFreeEq
termination_by sizeOf stmts

end -- mutual

/-! ## Termination

Mutual block decreases on `sizeOf` of the inductive scrutinee
(RawExpr / RawArgList / RawCallArg / OptRawExpr / RawStmtList).
Lean's auto-termination heuristic loses the connection through
the multiple `cases` + `rw [...] at envFreeEq` chain, so we
provide the measure explicitly per theorem. -/

/-- The headline corollary: env-aware bridge with empty env
SUBSUMES the env-free bridge.  Whenever env-free returns
`some r`, env-aware-with-empty also returns `some r`. -/
theorem RawExpr.toRawTermWithEnv?_empty_subsumes
    {scope : Nat}
    (e : RawExpr scope) (raw : RawTerm scope)
    (envFreeEq : e.toRawTerm? = some raw) :
    RawExpr.toRawTermWithEnv? Env.empty e = some raw :=
  RawExpr.bridge_inclusion e raw envFreeEq

end LeanFX2.Surface
