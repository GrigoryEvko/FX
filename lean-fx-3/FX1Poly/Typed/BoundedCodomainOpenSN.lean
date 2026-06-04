import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.StrongNormalizationReflection

/-! # FX1Poly/Typed/BoundedCodomainOpenSN
    — open-codomain strong normalization from a bounded FILLED codomain member (genFormationPi `codomainSN`)

The bounded `genFormationPi` recursor arm feeds `fundamentalGenFormationPiAtBoundedSucc`, whose `codomainSN`
premise asks for strong normalization of the OPEN substituted codomain `RawTerm.subst (lift substitution)
codomain` (the binder preserved, scope `targetScope + 2`).  The bounded telescope, however, only ever delivers
the codomain FILLED at a concrete domain argument — `twoChildMembers` (`DenoteKeyedBoundedTelescopeProjection`)
gives a bound-reducible member at `RawTerm.subst0 (RawTerm.subst (lift substitution) codomain) argument`.

This bridges the two using only shipped primitives:

  * bounded CR1 at `scope + 1` (`stronglyNormalizing_of_memberAtBoundedSucc`) turns the filled member into
    strong normalization of the filled codomain `subst0 (subst (lift substitution) codomain) argument`;
  * the relation-agnostic `IsStronglyNormalizing.ofSubst0Body` (`StrongNormalizationReflection`) reflects that
    SN back to the OPEN body `subst (lift substitution) codomain` — `subst0` instantiation preserves body
    reduction, so SN of the instance forces SN of the body.

No binder-lifted reducible environment and no renaming-stability of the bounded relation is needed — the same
substitution-reflection the denote/fuel routes use, here at the bounded layer.  This is the codomain half of the
genFormationPi recursor arm; the domain member and the `piReducibleAsType` discharge are the other two premises.

## Zero-axiom verification

A single composition of `IsStronglyNormalizing.ofSubst0Body` after `stronglyNormalizing_of_memberAtBoundedSucc`.
No induction here (both callees carry their own), no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Open-codomain SN from a bounded filled codomain member.**  Given a bound-reducible member at the
`subst0`-instantiated codomain `RawTerm.subst0 (RawTerm.subst (lift substitution) codomain) argument` (the shape
`TelescopeReducibleAtBounded.twoChildMembers` produces for the codomain), the OPEN codomain `RawTerm.subst (lift
substitution) codomain` is strongly normalizing.  Bounded CR1 (`stronglyNormalizing_of_memberAtBoundedSucc`) gives
SN of the instantiation; `IsStronglyNormalizing.ofSubst0Body` reflects it to the open body.  Discharges the
`codomainSN` premise of `fundamentalGenFormationPiAtBoundedSucc`. -/
theorem codomainOpenStronglyNormalizing_ofBoundedFilledMember {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {classifier : RawTerm (targetScope + 1)}
    {codomain : RawTerm (scope + 1)} {argument : RawTerm (targetScope + 1)}
    {substitution : RawTermSubst scope (targetScope + 1)}
    (filledMember : IsReducibleMemberAtBounded env bound classifier
      (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain) :=
  IsStronglyNormalizing.ofSubst0Body (stronglyNormalizing_of_memberAtBoundedSucc filledMember)

end FX1Poly.Typed
