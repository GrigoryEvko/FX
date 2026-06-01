import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsLeaves
    — member-level-irrelevance for neutral / data-former classifiers (the member-side leaf)

The MEMBER-side dual of `ReducibleTypeAtAllLevelsLeaves`.  A member of a weak-head-normal non-Π non-universe
classifier (a variable / stuck eliminator [neutral] or any DATA former) is, by the Tarski model, exactly a
strongly-normalizing term (`IsReducibleMemberAt.atNeutralClassifier`: membership ⟺ `IsStronglyNormalizing`,
at EVERY level).  So membership in such a classifier is level-INDEPENDENT, and a member at any single level
extends to a member at every positive level with no further hypothesis.

This is precisely the formation-FT telescope-cons companion's `headMemberExtendsToAllPositive` premise
(`fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises`) for a binder whose (substituted) DOMAIN is
neutral / a data former: the fresh argument's one-level membership strengthens to all-positive membership
for free, so the all-level Kripke environment `ReducibleEnvAtAllLevels` can be `cons`-extended.  Thus the
cons arm closes for every non-universe (and non-Π — those go through the dependent-arrow candidate) domain,
member-side; the universe domain remains the open case (its membership decodes a level-dependent lower type).

## Zero-axiom verification

`atNeutralClassifier` forward to extract `IsStronglyNormalizing`, then backward at every positive level.  No
induction, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated
per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-level-irrelevance for a neutral / data-former classifier.**  A member of a weak-head-normal
non-Π non-universe classifier at any single level is a member at every positive level — membership in such a
classifier is `IsStronglyNormalizing` (level-independent) via `IsReducibleMemberAt.atNeutralClassifier`. -/
theorem IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier {scope : Nat}
    {classifier term : RawTerm scope} {level : Nat}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
    (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode)
    (member : IsReducibleMemberAt level classifier term) :
    IsReducibleMemberAtAllPositiveLevels classifier term := by
  have stronglyNormalizing : IsStronglyNormalizing term :=
    (IsReducibleMemberAt.atNeutralClassifier weakHeadNormal notPiType notUniverse).mp member
  intro positiveLevel
  exact (IsReducibleMemberAt.atNeutralClassifier weakHeadNormal notPiType notUniverse).mpr
    stronglyNormalizing

/-- **The cons-arm `headMemberExtendsToAllPositive` premise for a neutral / data-former domain.**  Packaged
in the exact shape `fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises` consumes: for a domain
classifier that is weak-head-normal and neither Π- nor universe-rooted, every one-level member strengthens
to all-positive membership.  Supplying this discharges the telescope-cons argument-strengthening for a
neutral-domain former. -/
theorem headMemberExtendsToAllPositive_ofNeutralClassifier {scope : Nat}
    {classifier : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
    (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
    ∀ {memberLevel : Nat} (argument : RawTerm scope),
      IsReducibleMemberAt memberLevel classifier argument →
        IsReducibleMemberAtAllPositiveLevels classifier argument :=
  fun {_memberLevel} _argument member =>
    IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier weakHeadNormal notPiType notUniverse member

end FX1Poly.Typed
