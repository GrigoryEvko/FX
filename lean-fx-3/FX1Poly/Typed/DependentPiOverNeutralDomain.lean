import FX1Poly.Typed.PiTypeSaturationReassembly
import FX1Poly.Typed.NeutralFuelStability
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension

/-! # FX1Poly/Typed/DependentPiOverNeutralDomain
    — the first genuinely DEPENDENT Π fuel-stability arm: a Π over a neutral/data domain

`FirstOrderSimplyTypedReducibility` / `HigherOrderSimplyTypedReducibility` close the SIMPLY-TYPED fragment
(types built from neutral / data formers and NON-dependent arrows `dom → codBase`).  The remaining open
surface of the #672 gate (`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`) is the genuinely
DEPENDENT Π — where the codomain `cod` actually mentions the bound variable, so `RawTerm.subst0 cod arg`
varies per argument — together with the universe-domain (type-polymorphism) impredicative core.

This file takes the first dependent case: a dependent Π `Π (x : dom). cod` whose DOMAIN is a weak-head-normal
neutral / data type (a variable, a stuck eliminator, or any data former — Σ / Nat / List / Option / Either /
Id / product / sum codes; everything except Π- and universe-rooted).  For such a domain BOTH domain legs of
the Π reassembly discharge unconditionally:

  * `domainAllPositive` — the neutral / data domain is reducible at every level (`ReducibleTypeAtAllLevels.
    ofWeakHeadNormalNonPiNonUniverse`, then `.atAllPositiveLevels`);
  * `domainMembersStable` / `domainMemberExtension` — domain membership is fuel-stable because the neutral
    candidate is the level-independent `IsStronglyNormalizing` (`IsReducibleMemberAtAllPositiveLevels.
    ofNeutralTypeMember`, the #717 neutral arm).

So the Π reassembly (`IsReducibleTypeAtAllPositiveLevels.ofPiType`, #718) and the Π member-extension
(`piTypeMemberExtensionPositive`) collapse from THREE / FOUR hypotheses to a SINGLE residual obligation: the
CODOMAIN's fuel-stability per all-positive argument — exactly the codomain sub-term IH the eventual
well-founded recursion supplies.  This strictly extends the closed surface past the simply-typed fragment
(the codomain `cod` here genuinely depends on the bound variable, unlike `nonDependentArrow`'s
`RawTerm.weaken codomainBase`), and sharply isolates the remaining dependent obstruction to the codomain
alone.  The universe-domain case (a Π whose domain is `Type@e`) stays the open impredicative core.

## Zero-axiom verification

Each lemma feeds the shipped Π reassembly / member-extension with the domain legs discharged by the neutral
leaf (`ofWeakHeadNormalNonPiNonUniverse`) and the neutral member arm (`ofNeutralTypeMember`).  No induction.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Dependent Π over a neutral / data domain is reducible at every positive level — conditional only on the
codomain.**  When the domain `dom` is weak-head-normal and neither Π- nor universe-rooted (a neutral or any
data former), its all-level reducibility and member fuel-stability are unconditional, so the Π reassembly
`IsReducibleTypeAtAllPositiveLevels.ofPiType` (#718) reduces to its codomain hypothesis alone: for every
all-positive member `arg` of the domain, the instantiated codomain `RawTerm.subst0 cod arg` is reducible at
every positive level.  This is the first DEPENDENT Π reducibility arm (the codomain genuinely varies with the
argument), strictly beyond the simply-typed non-dependent-arrow fragment. -/
theorem IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllPositive : ∀ {arg : RawTerm scope},
        IsReducibleMemberAtAllPositiveLevels dom arg →
        IsReducibleTypeAtAllPositiveLevels (RawTerm.subst0 cod arg)) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) := by
  have domainAllLevels : IsReducibleTypeAtAllLevels dom :=
    IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse
  exact IsReducibleTypeAtAllPositiveLevels.ofPiType
    domainAllLevels.atAllPositiveLevels
    (fun {_arg _predLevel} member =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        domainWeakHeadNormal domainNotPiType domainNotUniverse domainAllLevels member)
    codomainAllPositive

/-- **Member-extension for a dependent Π over a neutral / data domain — conditional only on the codomain.**
A positive-level member of `Π (x : dom). cod` (neutral / data `dom`) extends to all positive levels, given
only the codomain's all-level reducibility and member-extension per all-positive domain argument.  The Π
member-extension `piTypeMemberExtensionPositive`'s domain legs (domain all-level reducibility + positive
domain member-extension) discharge from the neutral leaf and the #717 neutral member arm, leaving the codomain
hypotheses as the sole residual — the member-side twin of `dependentPiOverNeutralDomain`. -/
theorem IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain
    {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 cod argument))
    (codomainMemberExtension : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
          ∀ applicationTerm : RawTerm scope, ∀ {memberPredLevel : Nat},
            IsReducibleMemberAt (memberPredLevel + 1) (RawTerm.subst0 cod argument) applicationTerm →
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 cod argument) applicationTerm)
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))
      functionTerm := by
  have domainAllLevels : IsReducibleTypeAtAllLevels dom :=
    IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse
  exact IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtensionPositive
    domainAllLevels
    (fun _argument {_memberPredLevel} argMember =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember
        domainWeakHeadNormal domainNotPiType domainNotUniverse domainAllLevels argMember)
    codomainAllLevels
    codomainMemberExtension
    member

end FX1Poly.Typed
