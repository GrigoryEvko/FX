import FX1Poly.Typed.DenoteKeyedBoundedTelescopeReducible
import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive
import FX1Poly.Typed.HasTypeSubstitution

/-! # FX1Poly/Typed/DenoteKeyedBoundedTelescopeFundamental
    — the bound-carrying telescope fundamental-theorem companion arms (nil + cons)

The bounded grown-engine fundamental theorem's `genFormationPi` arm receives a former's children as a
`DescTelescopePi` telescope and must produce their joint bound-reducibility as a `TelescopeReducibleAtBounded`
(`DenoteKeyedBoundedTelescopeReducible.lean`).  That production is a structural recursion on the telescope whose
two minor-premise bodies — the `nil` base and the `cons` step — are factored here, exactly as the denote route
factors `fundamentalTelescopeNilAtDenote` / `fundamentalTelescopeConsAtDenote`
(`DenoteKeyedTelescopeFundamental.lean`).

The bound-carrying versions track the same two-level split the bounded telescope relation does
(`DenoteKeyedBoundedTelescopeReducible` docstring): each child head is a bound-reducible member of its universe
code at `bound` (read off the head's `FundamentalConclusionAtBounded`), while the tail's domain argument is
quantified at `argLevel` (the former's decoded output level).  The denote companion collapses these onto one
ambient `level`; here `bound` carries the head membership and `argLevel` carries the argument quantification.  No
recursion lives here — the eventual mutual `HasTypeDescPi`/`DescTelescopePi` FT recursor supplies the structural
tail premise; these arms are the per-constructor bodies it discharges.

## The two declarations

  * `fundamentalTelescopeNilAtBounded` — the empty telescope (child count `0`) is reducible (`True` by the
    relation's `count = 0` clause).
  * `fundamentalTelescopeConsAtBounded` — a reducible head child (its `FundamentalConclusionAtBounded`, applied to
    the closing substitution + bound-reducible environment, gives the head as a bound-reducible member of its
    universe code at `bound` after `subst_universeCodeCell` cancels the substitution on the closed code) plus an
    already-produced reducible tail under each bound-reducible argument at `argLevel` assemble the reducible cons
    telescope.

## Zero-axiom verification

`nil` is `True.intro`.  `cons` is the anonymous constructor of the relation's cons conjunction: the head member
from `headFundamental substitution reducibleEnv` rewritten by `subst_universeCodeCell` (the universe code is
closed, so the closing substitution leaves the classifier fixed), and the tail premise passed through.  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Empty telescope reducibility (bound-carrying).**  At child count `0`, `TelescopeReducibleAtBounded` reduces
to `True`.  The `DescTelescopePi.nil` minor-premise body of the bounded telescope companion. -/
theorem fundamentalTelescopeNilAtBounded {baseScope targetScope currentDepth : Nat}
    (env : Nat → Nat) (bound argLevel : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope} :
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth 0 substitution []
      (.childNil : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :=
  True.intro

/-- **Cons telescope reducibility (bound-carrying).**  The head child is a bound-reducible member of its universe
code `Type@headLevel` at `bound` — read off its `FundamentalConclusionAtBounded` applied to the closing
substitution and the bound-reducible environment, with `subst_universeCodeCell` cancelling the closing
substitution on the closed universe code; the tail is supplied as the explicit structural premise for every
bound-reducible argument at `argLevel`.  The non-recursive `DescTelescopePi.cons` minor-premise body the eventual
FT recursor discharges. -/
theorem fundamentalTelescopeConsAtBounded {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat} (env : Nat → Nat) (bound argLevel : Nat)
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope}
    (reducibleEnv : ReducibleEnvAtBounded env bound context substitution)
    (headFundamental :
      FundamentalConclusionAtBounded env bound context head (universeCodeCell headLevel flag))
    (tailReducible :
      ∀ (argument : RawTerm targetScope),
        IsReducibleMemberAtBounded env argLevel (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtBounded env bound argLevel flag (currentDepth + 1) count
          (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth (count + 1) substitution
      (headLevel :: restLevels) (.childCons head rest) :=
  ⟨by have headMember := headFundamental substitution reducibleEnv
      rwa [subst_universeCodeCell] at headMember,
    fun argument argumentMember => tailReducible argument argumentMember⟩

end FX1Poly.Typed
