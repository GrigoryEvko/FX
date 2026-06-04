import FX1Poly.Typed.DenoteKeyedBoundedTelescopeFundamental
import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge

/-! # FX1Poly/Typed/BoundedTelescopeConsSucc
    — the +1-closing cons telescope companion arm (for the grown-FT motive_2)

The shipped `fundamentalTelescopeConsAtBounded` (`DenoteKeyedBoundedTelescopeFundamental.lean`) takes the head
child's `FundamentalConclusionAtBounded` at ARBITRARY target scope.  But the bounded grown fundamental theorem
(`HasTypeDescPi.rec`) uses `motive_1 = FundamentalConclusionAtBoundedSucc` — every head child's IH is the
`+1`-closing conclusion (substitutions into `targetScope + 1`).  A `+1` IH is strictly weaker than the
arbitrary-scope one, so it cannot feed the arbitrary-scope companion; this file ships the `+1` mirror.

The proof is identical to the arbitrary-scope companion — read the head member off its conclusion applied to the
closing substitution (now at `targetScope + 1`) and the bound-reducible environment, with `subst_universeCodeCell`
cancelling the substitution on the closed universe code, then thread the tail premise — only the head IH's type
(`FundamentalConclusionAtBoundedSucc`) and the substitution's `+1` target scope change.  This is the cons
recursor-arm body the eventual `HasTypeDescPi.rec` dispatch discharges for the `motive_2` telescope predicate
(uniform in the argument-quantification level `argLevel`, which the dispatch instantiates to the former's decoded
output level).

## Zero-axiom verification

The anonymous constructor of the relation's cons conjunction: the head member from `headFundamental substitution
reducibleEnv` rewritten by `subst_universeCodeCell`, and the tail premise passed through.  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked:
depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The +1-closing cons telescope companion.**  Like `fundamentalTelescopeConsAtBounded`, but the head child's
IH is the `+1`-closing `FundamentalConclusionAtBoundedSucc` (the grown-FT recursor's `motive_1`), and the closing
substitution targets `targetScope + 1`.  Assembles the cons telescope at any argument-quantification level
`argLevel` from the head member (read off the `+1` conclusion) and the tail premise. -/
theorem fundamentalTelescopeConsAtBoundedSucc {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat} (env : Nat → Nat) (bound argLevel : Nat)
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (reducibleEnv : ReducibleEnvAtBounded env bound context substitution)
    (headFundamental :
      FundamentalConclusionAtBoundedSucc env bound context head (universeCodeCell headLevel flag))
    (tailReducible :
      ∀ (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtBounded env argLevel (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtBounded env bound argLevel flag (currentDepth + 1) count
          (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth (count + 1) substitution
      (headLevel :: restLevels) (.childCons head rest) :=
  ⟨by have headMember := headFundamental substitution reducibleEnv
      rwa [subst_universeCodeCell] at headMember,
    fun argument argumentMember => tailReducible argument argumentMember⟩

end FX1Poly.Typed
