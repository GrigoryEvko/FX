import FX1Poly.Typed.DependentPiOverNeutralDomain
import FX1Poly.Core.BetaRedexCompoundPreservation

/-! # FX1Poly/Typed/DependentPiNeutralCodomain
    — the first FULLY UNCONDITIONAL dependent Π fuel-stability arm, plus a concrete closed witness

`DependentPiOverNeutralDomain` reduced the dependent-Π fuel-stability obligation (toward #672 / SN-043), for a
neutral / data domain, to its CODOMAIN leg alone.  This file discharges the codomain leg too — for the case
where the codomain INSTANTIATIONS `RawTerm.subst0 cod arg` are themselves neutral / data (weak-head-normal,
non-Π, non-universe) for every argument.  Then the whole dependent Π is reducible at every positive level —
and admits member-extension — with NO reducibility hypothesis at all, only the syntactic neutrality of the
domain and of each codomain instantiation.

This is the first FULLY UNCONDITIONAL dependent Π arm: the codomain genuinely mentions the bound variable
(unlike a simply-typed non-dependent arrow `RawTerm.weaken codomainBase`), yet because every instantiation
stays neutral, the type-level / member-level candidates are the level-independent `IsStronglyNormalizing`
predicate (the neutral leaf `ofWeakHeadNormalNonPiNonUniverse` and the #717 neutral member arm
`ofNeutralTypeMember`), so no fuel-saturation argument is needed.

The headline corollary `concreteDependentPi_isReducibleType` exhibits a CONCRETE closed dependent type that
satisfies the hypotheses end-to-end: `Π (x : A). P x` where `A` is a free type variable and `P` a free
type-FAMILY variable.  The codomain `app (weaken P) (var 0)` mentions the bound `x`, and substitution gives
`subst0 (app (weaken P) (var 0)) arg = app P arg` (the weakening cancels the substitution; the bound variable
becomes the argument), which is neutral because its head `P` is a variable.  This is the first genuinely
dependent type proven reducible through the stratified reducibility model — beyond the non-dependent
`Type@e → Type@e` witnesses in `StratifiedReducibleSmoke`.  The residual open crux of #672 remains the
universe-DOMAIN dependent Π (type-polymorphism / impredicativity).

## Zero-axiom verification

The unconditional arms feed the conditional `dependentPiOverNeutralDomain` / its member twin with the codomain
legs discharged by the neutral leaf and the #717 neutral member arm.  The concrete witness computes the
codomain substitution by `subst0_app_reduces` (definitional app distribution) + `weaken_subst_singleton`
(weaken/subst cancellation) + `subst0_var_zero` (bound-variable substitution), then reads neutrality off
`IsNeutral.app (IsNeutral.var _)`.  No induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Fully unconditional dependent Π reducibility** for a neutral / data domain with neutral-valued codomain
instantiations.  When `dom` is weak-head-normal non-Π non-universe AND every codomain instantiation
`RawTerm.subst0 cod arg` is too, the dependent Π `Π (x : dom). cod` is reducible at every positive level with
no reducibility hypothesis — the codomain leg of `dependentPiOverNeutralDomain` discharges via the neutral
leaf `ofWeakHeadNormalNonPiNonUniverse` for every argument.  The codomain still genuinely mentions the bound
variable; only its instantiations are required neutral. -/
theorem IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainWeakHeadNormal : ∀ arg : RawTerm scope,
        ∀ reduct : RawTerm scope, ¬ WeakHeadStep (RawTerm.subst0 cod arg) reduct)
    (codomainNotPiType : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_piTyCode)
    (codomainNotUniverse : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) :=
  IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain
    domainWeakHeadNormal domainNotPiType domainNotUniverse
    (fun {arg} _member =>
      (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (codomainWeakHeadNormal arg) (codomainNotPiType arg)
        (codomainNotUniverse arg)).atAllPositiveLevels)

/-- **Fully unconditional member-extension** for the same fully-neutral dependent Π.  A positive-level member
of `Π (x : dom). cod` (neutral domain, neutral codomain instantiations) extends to all positive levels with no
reducibility hypothesis: both codomain legs of `dependentPiMemberExtensionOverNeutralDomain` discharge via the
neutral leaf (codomain all-levels) and the #717 neutral member arm (codomain member-extension), for every
argument. -/
theorem IsReducibleMemberAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainWeakHeadNormal : ∀ arg : RawTerm scope,
        ∀ reduct : RawTerm scope, ¬ WeakHeadStep (RawTerm.subst0 cod arg) reduct)
    (codomainNotPiType : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_piTyCode)
    (codomainNotUniverse : ∀ arg : RawTerm scope,
        (RawTerm.subst0 cod arg).rootGenerator ≠ Generator.gen_universeCode)
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm :=
  IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain
    domainWeakHeadNormal domainNotPiType domainNotUniverse
    (fun argument _argMember =>
      IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument))
    (fun argument _argMember _applicationTerm {_memberPredLevel} applicationMember =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument)
        (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          (codomainWeakHeadNormal argument) (codomainNotPiType argument) (codomainNotUniverse argument))
        applicationMember)
    member

/-- **Concrete closed dependent type, reducible end-to-end.**  `Π (x : A). P x` — with `A = var domVar` a
free type variable and `P = var familyVar` a free type-FAMILY variable — is reducible at every positive level,
with NO hypotheses.  The codomain `app (weaken P) (var 0)` genuinely depends on the bound `x`; its
instantiation `subst0 (app (weaken P) (var 0)) arg = app P arg` is neutral (head `P` is a variable), so the
unconditional neutral-codomain arm fires.  This is the first genuinely DEPENDENT type proven reducible through
the stratified reducibility model — the non-dependent `Type@e → Type@e` is `StratifiedReducibleSmoke`'s
`closedSimpleArrow_isReducibleType`; this exhibits the dependent codomain machinery on a concrete cell. -/
theorem concreteDependentPi_isReducibleType {scope : Nat} (domVar familyVar : Fin scope) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_var domVar .childNil)
          (.childCons
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            .childNil))) := by
  have codEq : ∀ arg : RawTerm scope,
      RawTerm.subst0
          (.mkGen .gen_app ()
            (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
              (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
          arg =
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil))) := by
    intro arg
    rw [RawTerm.subst0_app_reduces,
        show RawTerm.subst0 (RawTerm.weaken (.mkGen .gen_var familyVar .childNil)) arg
          = (.mkGen .gen_var familyVar .childNil : RawTerm scope)
          from RawTerm.weaken_subst_singleton _ _,
        RawTerm.subst0_var_zero]
  have neutralInstantiation : ∀ arg : RawTerm scope,
      IsNeutral (.mkGen .gen_app ()
        (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil))) :=
    fun arg => IsNeutral.app (IsNeutral.var familyVar)
  exact IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain
    (fun _reduct => (IsNeutral.var domVar).noWeakHeadStep _)
    (IsNeutral.var domVar).rootGenerator_ne_piTyCode
    (IsNeutral.var domVar).rootGenerator_ne_universeCode
    (fun {arg} _member => by
      rw [codEq arg]
      exact (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
        (neutralInstantiation arg).noWeakHeadStep
        (neutralInstantiation arg).rootGenerator_ne_piTyCode
        (neutralInstantiation arg).rootGenerator_ne_universeCode).atAllPositiveLevels)

end FX1Poly.Typed
