import FX1Poly.Core.ReducibleTypeWellFormed
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/AbstractionNonDependentUnderSubstLevelFree
    — the simply-typed lam arm of the LEVEL-FREE term fundamental theorem

The simply-typed (non-dependent) fundamental theorem assembles over the LEVEL-FREE reducibility layer
(`IsReducibleMember` / `ReducibleType` / `ReducibleEnv`), NOT the stratified one.  Reason — the two layers
have DUAL obstructions for the lambda arm, and only the level-free layer is wall-free for a non-dependent
codomain:

  * **Stratified layer** (`IsReducibleMemberAt level`): the lam arm (`fundamentalPiIntroNonDependentAtAll`)
    extends an all-levels environment (`ReducibleEnvAtAllLevels.cons`), which needs the bound argument
    reducible at ALL levels — but the arm only has it at one level.  That is the universe wall.
  * **Level-free layer** (`IsReducibleMember`): no levels, so `ReducibleEnv.cons` extends the environment
    from a SINGLE `IsReducibleMember` of the bound argument — no all-levels demand, no wall.  (Its dual
    limitation — a type-variable domain's universe membership decodes only to `SN`, not a `ReducibleType` —
    bites only for type-VARIABLE domains, which the simply-typed term FT over directly-reducible domains
    avoids.)

So the level-free layer is the home of the simply-typed term FT.  Its lambda arm is the NON-DEPENDENT
specialization of the shipped dependent `IsReducibleMember.abstractionUnderSubst`: the codomain is
`RawTerm.weaken codomainBase`, so the dependent rule's per-argument codomain
`subst0 (subst (lift substitution) (weaken codomainBase)) argument` collapses to the σ-independent
`subst substitution codomainBase`.  This file ships that specialization — the lambda arm the assembly
consumes, pre-cancelling the weakening so the codomain hypotheses are stated directly at `subst σ codomainBase`.

## The codomain collapse

`subst0 (subst (lift substitution) (weaken codomainBase)) argument = subst substitution codomainBase`:
`subst_lift_weaken_commute` pushes the weakening out through the lift
(`subst (lift σ) (weaken B) = weaken (subst σ B)`), then `RawTerm.weaken_subst_singleton` cancels the
weakening against the singleton substitution (`subst0 (weaken Y) argument = Y`, since
`subst0 := subst (singleton ·)`).  The equality is stated in `RawTerm.weaken` form (matching the goal
`abstractionUnderSubst` produces) and proved by `congrArg`/`Eq.trans` so the `RawTerm.weaken` /
`rename RawRenaming.weaken` definitional unfolding rides through.

## Zero-axiom verification

`congrArg` + `Eq.trans` over `subst_lift_weaken_commute` and `RawTerm.weaken_subst_singleton`, feeding the
shipped `IsReducibleMember.abstractionUnderSubst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **The simply-typed lambda arm of the level-free fundamental theorem (non-dependent abstraction under a
closing substitution).**  For a lambda whose classifier is the simple arrow
`piTyCodeCell domainCode (RawTerm.weaken codomainBase)`, given that the closing `substitution` makes the
domain a reducible type (`domainReducible`) with strongly-normalizing members (`domainArgumentsSN`), the
base codomain a reducible type (`codomainReducible`), and the body — under the lifted substitution —
a reducible member of the (σ-closed, weakening-cancelled) codomain for every domain-reducible argument
(`bodyReducible`), it sends `lamCell body` to a reducible member of the closed simple arrow.

The per-argument codomain `subst0 (subst (lift substitution) (weaken codomainBase)) argument` collapses to
the constant `subst substitution codomainBase` (`subst_lift_weaken_commute` + `RawTerm.weaken_subst_singleton`),
so the codomain/body hypotheses are stated directly at the base codomain — the shape the simply-typed term
FT's binder step produces (the body's induction hypothesis at the `ReducibleEnv.cons`-extended environment,
reshaped by `RawTerm.subst_cons_eq_subst0_lift`).  Reduces to the shipped dependent
`IsReducibleMember.abstractionUnderSubst`. -/
theorem IsReducibleMember.abstractionNonDependentUnderSubst {scope targetScope : Nat}
    {domainCode codomainBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleType (RawTerm.subst substitution domainCode) domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : IsReducibleType (RawTerm.subst substitution codomainBase))
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleMember (RawTerm.subst substitution codomainBase)
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    IsReducibleMember
      (RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase)))
      (RawTerm.subst substitution (lamCell body)) := by
  -- the per-argument codomain collapses to the constant base codomain; annotated in `RawTerm.weaken`
  -- form so the rewrites below match the goal `abstractionUnderSubst` produces
  have codomainCollapse : ∀ argument : RawTerm targetScope,
      RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) (RawTerm.weaken codomainBase)) argument
        = RawTerm.subst substitution codomainBase :=
    fun argument =>
      (congrArg (RawTerm.subst0 · argument)
        (subst_lift_weaken_commute substitution codomainBase)).trans
        (RawTerm.weaken_subst_singleton (RawTerm.subst substitution codomainBase) argument)
  exact IsReducibleMember.abstractionUnderSubst substitution domainReducible domainArgumentsSN
    (fun argument _argumentInDomain => by
      rw [codomainCollapse argument]; exact codomainReducible)
    (fun argument argumentInDomain => by
      rw [codomainCollapse argument]; exact bodyReducible argument argumentInDomain)

end FX1Poly.Typed
