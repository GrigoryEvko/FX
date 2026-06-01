import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.TelescopeReducible

/-! # FX1Poly/Typed/FundamentalAtAllTelescope
    — non-recursive telescope assembly bricks over the ∀-level fundamental-theorem conclusion

The eventual `DescTelescopePi` companion of the dependent fundamental theorem must build
`TelescopeReducible`.  This file factors the two non-recursive telescope constructors:

* `fundamentalTelescopeNilAtAll` — the empty telescope is reducible (`True` by definition).
* `fundamentalTelescopeConsAtAll` — a reducible head child (from `FundamentalConclusionAtAll`) plus an
  already-produced reducible tail under each reducible argument assemble the reducible cons telescope.

No recursion lives here.  These are the telescope-level analogues of the factored term/former arms in
`FundamentalAtAllLeafArms`: the future recursor only has to supply the structural tail premise. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Empty premise telescope reducibility.**  At count `0`, `TelescopeReducible` reduces to `True`. -/
theorem fundamentalTelescopeNilAtAll {baseScope targetScope currentDepth : Nat}
    {flag : UniverseFlag}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)} :
    TelescopeReducible flag currentDepth 0 substitution [] (.childNil : RawTermChildren [] baseScope) :=
  True.intro

/-- **Cons premise telescope reducibility over the ∀-level conclusion.**  The head child is read at every
positive level from its `FundamentalConclusionAtAll` result (then the universe classifier is simplified);
the tail is supplied as an explicit semantic premise for every reducible argument.  This is exactly the
non-recursive body of the `DescTelescopePi.cons` minor premise, isolated for reuse by the full recursor
assembly. -/
theorem fundamentalTelescopeConsAtAll {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (env : ReducibleEnvAtAllLevels context substitution)
    (headFundamental : FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (tailReducible :
      ∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel (RawTerm.subst substitution head) argument →
        TelescopeReducible flag (currentDepth + 1) count
          (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  ⟨fun level => by
      have headMember := headFundamental substitution env level
      rwa [subst_universeCodeCell] at headMember,
    fun {_memberLevel} argument argumentMember => tailReducible argument argumentMember⟩

end FX1Poly.Typed
