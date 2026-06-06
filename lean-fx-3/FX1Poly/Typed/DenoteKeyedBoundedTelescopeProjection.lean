import FX1Poly.Typed.DenoteKeyedBoundedTelescopeReducible
import FX1Poly.Core.RawTermSubstConsCommute

/-! # FX1Poly/Typed/DenoteKeyedBoundedTelescopeProjection
    — project the two-child bounded telescope into the discharge's domain/codomain member shape

The bounded `genFormationPi` recursor arm consumes the children's reducibility as a
`TelescopeReducibleAtBounded` (`DenoteKeyedBoundedTelescopeReducible.lean`) but feeds the non-uniform discharge
`piReducibleAsTypeFromNonUniformLevelMemberBounded` (`DenoteKeyedBoundedGenFormationPiDischarge.lean`), which
wants the domain and codomain as separate bounded universe-members.  `twoChildMembers` is that pure projection:
it reads the two conjuncts off the depth-0/count-2 telescope (the Π/Σ-former shape, `consecutiveShifts 0 2`).

The only non-projection step is reshaping the codomain member.  The telescope's tail delivers the codomain member
at `RawTerm.subst (RawTermSubst.cons argument substitution) codomain`; the discharge wants it at
`RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument`.  These are equal by the
binder-split keystone `RawTerm.subst_cons_eq_subst0_lift` — the same `subst (cons …) = subst0 (subst (lift …))`
commutation the denote `piIntro` arm uses — so a single `rwa` closes it.

## Zero-axiom verification

The domain conjunct is `telescope.1`; the codomain conjunct is `(telescope.2 argument argumentMember).1`
(the depth-0/count-2 and the tail depth-1/count-1 telescopes both reduce definitionally to the `And` the
`.twoChild` constructor built), rewritten by `RawTerm.subst_cons_eq_subst0_lift`.  No induction, no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no
axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Project the two-child Π/Σ bounded telescope into the discharge's member shape.**  From the depth-0/count-2
`TelescopeReducibleAtBounded` over `[domainLevel, codomainLevel]` and the two-child spine, read off: the domain as
a bound-reducible member of `Type@domainLevel`, and — for every bound-reducible argument of the (substituted)
domain at `argLevel` — the codomain (instantiated at that argument, under the lifted substitution) as a
bound-reducible member of `Type@codomainLevel`.  Exactly the `domainMember` / `codomainMember` premises
`piReducibleAsTypeFromNonUniformLevelMemberBounded` consumes.  The codomain reshaping is
`RawTerm.subst_cons_eq_subst0_lift`. -/
theorem TelescopeReducibleAtBounded.twoChildMembers {baseScope targetScope : Nat} {env : Nat → Nat}
    {bound argLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst baseScope targetScope}
    {domainLevel codomainLevel : LevelExpr}
    {domain : RawTerm baseScope} {codomain : RawTerm (baseScope + 1)}
    (telescope : TelescopeReducibleAtBounded env bound argLevel flag 0 2 substitution
      [domainLevel, codomainLevel]
      (.childCons domain (.childCons codomain .childNil))) :
    IsReducibleMemberAtBounded env bound (universeCodeCell domainLevel flag)
      (RawTerm.subst substitution domain) ∧
    (∀ argument : RawTerm targetScope,
      IsReducibleMemberAtBounded env argLevel (RawTerm.subst substitution domain) argument →
      IsReducibleMemberAtBounded env bound (universeCodeCell codomainLevel flag)
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :=
  ⟨telescope.1,
   fun argument argumentMember => by
     have codomainMember := (telescope.2 argument argumentMember).1
     rwa [RawTerm.subst_cons_eq_subst0_lift] at codomainMember⟩

/-- **Project the one-child data-former bounded telescope into the element member.**  The one-child
(`consecutiveShifts 0 1`, `[0]` binderShifts) analogue of `twoChildMembers`, for the data type-code formers
(`listCode` / `optionCode`): from the depth-0/count-1 `TelescopeReducibleAtBounded` over `[elementLevel]` and the
one-child spine `childCons _ childNil`, read off the element as a bound-reducible member of `Type@elementLevel`.
A pure projection (`telescope.1`) — the depth-0/count-1 telescope reduces definitionally to the `And` whose
first conjunct is the head member, with NO codomain reshaping (the data former is non-dependent, unlike Π/Σ).
Consumed by the bounded `genFormationPi` arm's data-former branch. -/
theorem TelescopeReducibleAtBounded.oneChildMember {baseScope targetScope : Nat} {env : Nat → Nat}
    {bound argLevel : Nat} {flag : UniverseFlag} {substitution : RawTermSubst baseScope targetScope}
    {elementLevel : LevelExpr} {element : RawTerm baseScope}
    (telescope : TelescopeReducibleAtBounded env bound argLevel flag 0 1 substitution
      [elementLevel]
      (.childCons element .childNil)) :
    IsReducibleMemberAtBounded env bound (universeCodeCell elementLevel flag)
      (RawTerm.subst substitution element) :=
  telescope.1

end FX1Poly.Typed
