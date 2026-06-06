import FX1Poly.Typed.DenoteKeyedTelescopeReducible
import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.CellSubstitution

/-! # FX1Poly/Typed/DenoteKeyedTelescopeFundamental
    — the denote telescope fundamental-theorem companion arms (nil + cons; toward strong normalization)

**OFF-PATH CROSSCHECK: part of the UNBOUNDED denote fundamental-theorem assembly.  The bounded route reaches
strong normalization without it; not imported by any `*Bounded` file.  Retained as a crosscheck.**

The denote fundamental theorem's `genFormationPi` arm receives a former's children as a `DescTelescopePi`
telescope and must produce their joint denote-reducibility as a `TelescopeReducibleAtDenote`
(`DenoteKeyedTelescopeReducible.lean`).  That production is a structural recursion on the telescope whose two
minor-premise bodies — the `nil` base and the `cons` step — are factored here, exactly as the fuel route
factors `fundamentalTelescopeNilAtAll` / `fundamentalTelescopeConsAtAll` (`FundamentalAtAllTelescope.lean`).

The denote versions are SIMPLER than the fuel originals on the same two counts the telescope relation is
(`DenoteKeyedTelescopeReducible` docstring): each child head is a denote-reducible member at the SINGLE ambient
`level` (the fuel cons reads its head member at every positive level, `∀ level`), and the closing substitution
rides on `RawTermSubst (baseScope + currentDepth) targetScope` (no successor scope).  No recursion lives here —
the eventual mutual `HasTypeDescPi`/`DescTelescopePi` FT recursor supplies the structural tail premise; these
arms are the per-constructor bodies it discharges.

## The two declarations

  * `fundamentalTelescopeNilAtDenote` — the empty telescope (child count `0`) is reducible (`True` by the
    relation's `count = 0` clause).
  * `fundamentalTelescopeConsAtDenote` — a reducible head child (its `FundamentalConclusionAtDenote`, applied
    to the closing substitution + denote-reducible environment, gives the head as a denote-reducible member of
    its universe code after `subst_universeCodeCell` cancels the substitution on the closed code) plus an
    already-produced reducible tail under each denote-reducible argument assemble the reducible cons telescope.

## Zero-axiom verification

`nil` is `True.intro`.  `cons` is the anonymous constructor of the relation's cons conjunction: the head member
from `headFundamental substitution reducibleEnv` rewritten by `subst_universeCodeCell` (the universe code is
closed, so the closing substitution leaves the classifier fixed), and the tail premise passed through.  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Empty telescope reducibility (denote-keyed).**  At child count `0`, `TelescopeReducibleAtDenote` reduces
to `True`.  The `DescTelescopePi.nil` minor-premise body of the denote telescope companion. -/
theorem fundamentalTelescopeNilAtDenote {baseScope targetScope currentDepth : Nat}
    (env : Nat → Nat) (level : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope} :
    TelescopeReducibleAtDenote env level flag currentDepth 0 substitution []
      (.childNil : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :=
  True.intro

/-- **Cons telescope reducibility (denote-keyed).**  The head child is a denote-reducible member of its
universe code `Type@headLevel` at the ambient `level` — read off its `FundamentalConclusionAtDenote` applied to
the closing substitution and the denote-reducible environment, with `subst_universeCodeCell` cancelling the
closing substitution on the closed universe code; the tail is supplied as the explicit structural premise for
every denote-reducible argument.  The non-recursive `DescTelescopePi.cons` minor-premise body the eventual FT
recursor discharges. -/
theorem fundamentalTelescopeConsAtDenote {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat} (env : Nat → Nat) (level : Nat)
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope}
    (reducibleEnv : ReducibleEnvAtDenote env level context substitution)
    (headFundamental :
      FundamentalConclusionAtDenote env level context head (universeCodeCell headLevel flag))
    (tailReducible :
      ∀ (argument : RawTerm targetScope),
        IsReducibleMemberAtDenote env level (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtDenote env level flag (currentDepth + 1) count
          (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducibleAtDenote env level flag currentDepth (count + 1) substitution
      (headLevel :: restLevels) (.childCons head rest) :=
  ⟨by have headMember := headFundamental substitution reducibleEnv
      rwa [subst_universeCodeCell] at headMember,
    fun argument argumentMember => tailReducible argument argumentMember⟩

end FX1Poly.Typed
