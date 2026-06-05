import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsNonDependentArrow
import FX1Poly.Typed.ReducibleTypeAtAllLevelsNonDependentArrow
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves

/-! # FX1Poly/Typed/FirstOrderSimplyTypedReducibility
    — the universe member-extension principle, ASSEMBLED for the first-order simply-typed fragment

**OFF-PATH CROSSCHECK (supersession map, 2026-06-05): this is a ROUTE-A all-level fragment — it discharges the
universe member-extension principle (`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes`, #672) for
a sub-fragment.  That principle was the route-A SN-043 gate, but the BFT BOUNDED route (OB-5 /
`ValidTyping.closedStronglyNormalizing`) closed SN-043 WITHOUT it.  Off the kernel critical path; retained as a
crosscheck, not critical-path.**

This is the assembly capstone of the member-extension arm family.  The operational principle
`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` (a member of a strongly-normalizing all-levels
type at one positive fuel is a member at every positive fuel) is OPEN in general — its `piType` arm bottoms
out at the degenerate fuel-`0` Tarski decode of universe membership (the type-polymorphism wall).  But for the
FIRST-ORDER simply-typed fragment — types built from neutral / data formers and non-dependent arrows whose
DOMAINS are neutral / data — the principle holds UNCONDITIONALLY, assembled by induction on a witness inductive.

The fuel-`0` obstruction is structurally absent here for two reasons.  (1) Every arrow DOMAIN is a neutral /
data leaf, whose member-extension (`ofNeutralClassifier`) is level-independent — so the type-side
`piTypeOfDomainMemberExtension` (which genuinely consumes domain member-extension at fuel `0` in its level-`0`
case) is fed without obstruction.  (2) Codomains are threaded only through POSITIVE-source member-extension
(`piTypeMemberExtensionPositive`, `nonDependentArrowPositive`), so a sub-arrow codomain need only supply
member-extension from positive source levels — exactly what the inductive hypothesis provides.  Codomains may
themselves be arrows (curried first-order functions `A → B → C`), but a higher-order DOMAIN (`(A → B) → C`)
would require arrow member-extension at fuel `0`, which is the open wall — hence the first-order restriction.

This is the classic Tait reducibility result (1967, for first-order Gödel's T) realized on FX's stratified
Tarski candidate substrate: the first non-trivial fragment for which the reducibility machinery closes
end-to-end, and the precise documentation of the saturation boundary (first-order works; higher-order domains
and universe domains need the non-fuel / induction-recursive reformulation).

## Zero-axiom verification

A 2-constructor witness inductive (`leaf` / first-order `arrow`) plus one induction proving the bundled
type-reducibility-and-member-extension pair: `leaf` via `ofWeakHeadNormalNonPiNonUniverse` /
`ofNeutralClassifier`; `arrow` via `IsReducibleTypeAtAllLevels.nonDependentArrow` (domain member-extension
from the neutral leaf, all levels) and `nonDependentArrowPositive` (codomain member-extension from the IH,
positive source).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-extension for a non-dependent arrow — POSITIVE-source codomain form.**  The positive-source
variant of `IsReducibleMemberAtAllPositiveLevels.nonDependentArrow`, built on `piTypeMemberExtensionPositive`:
the domain and codomain member-extension premises need only hold from POSITIVE source levels.  This is what
lets a non-dependent arrow be assembled when its codomain is itself a (sub-witness) arrow supplying only
positive-source member-extension. -/
theorem IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive {scope : Nat}
    {domainCode codomainBase : RawTerm scope}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ argument : RawTerm scope, ∀ {memberPredLevel : Nat},
        IsReducibleMemberAt (memberPredLevel + 1) domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevels : IsReducibleTypeAtAllLevels codomainBase)
    (codomainMemberExtension : ∀ applicationTerm : RawTerm scope, ∀ {memberPredLevel : Nat},
        IsReducibleMemberAt (memberPredLevel + 1) codomainBase applicationTerm →
          IsReducibleMemberAtAllPositiveLevels codomainBase applicationTerm)
    (member : IsReducibleMemberAt (predLevel + 1)
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) functionTerm := by
  refine IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtensionPositive domainAllLevels
    domainMemberExtension ?_ ?_ member
  · intro argument _argumentInDomain
    rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
      RawTerm.weaken_subst_singleton codomainBase argument]
    exact codomainAllLevels
  · intro argument _argumentInDomain applicationTerm memberPredLevel applicationMember
    rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
      RawTerm.weaken_subst_singleton codomainBase argument] at applicationMember ⊢
    exact codomainMemberExtension applicationTerm applicationMember

/-- **First-order simply-typed witness.**  A type is first-order simply-typed when it is either a neutral /
data former (a `leaf`: weak-head-normal, not Π-, not universe-rooted) or a non-dependent `arrow` whose DOMAIN
is such a leaf and whose codomain is itself first-order simply-typed.  This captures the curried first-order
function types `A₁ → A₂ → … → Aₙ → B` over neutral / data base types — every arrow domain is base, while
codomains may nest arrows.  Higher-order arrow domains (`(A → B) → C`) are excluded from THIS inductive only;
they are NOT blocked — `IsSimplyTyped` (HigherOrderSimplyTypedReducibility) closes arrows on the domain too
and proves the same Tait result for the full simply-typed fragment.  The genuine fuel-`0` wall is confined to
UNIVERSE domains (`Type@e → C`, dependent), whose member-extension is the open type-polymorphic core. -/
inductive IsFirstOrderSimplyTyped : {scope : Nat} → RawTerm scope → Prop
  | leaf {scope : Nat} {classifier : RawTerm scope}
      (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
      (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
      (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
      IsFirstOrderSimplyTyped classifier
  | arrow {scope : Nat} {domainCode codomainBase : RawTerm scope}
      (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
      (domainNotPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
      (domainNotUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
      (codomainFirstOrder : IsFirstOrderSimplyTyped codomainBase) :
      IsFirstOrderSimplyTyped (piTyCodeCell domainCode (RawTerm.weaken codomainBase))

/-- **The universe member-extension principle, proved for the first-order simply-typed fragment.**  Every
first-order simply-typed type is reducible at all levels AND admits member-extension (a member at one positive
source level is a member at every positive level).  The member half is exactly
`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` restricted to this fragment — the classic Tait
reducibility result, assembled by induction on the witness from the shipped neutral-leaf, non-dependent-arrow
(type + positive member), and `ofNeutralClassifier` arms. -/
theorem IsFirstOrderSimplyTyped.reducibleAndMemberExtension {scope : Nat} {typeCode : RawTerm scope}
    (firstOrder : IsFirstOrderSimplyTyped typeCode) :
    IsReducibleTypeAtAllLevels typeCode ∧
      (∀ (term : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) typeCode term →
          IsReducibleMemberAtAllPositiveLevels typeCode term) := by
  induction firstOrder with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact ⟨IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          weakHeadNormal notPiType notUniverse,
        fun term {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
            weakHeadNormal notPiType notUniverse member⟩
  | arrow domainWeakHeadNormal domainNotPiType domainNotUniverse _codomainFirstOrder codomainIH =>
      obtain ⟨codomainAllLevels, codomainMemberExtension⟩ := codomainIH
      have domainAllLevels : IsReducibleTypeAtAllLevels _ :=
        IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          domainWeakHeadNormal domainNotPiType domainNotUniverse
      have domainMemberExtension : ∀ argument : RawTerm scope, ∀ {memberLevel : Nat},
          IsReducibleMemberAt memberLevel _ argument →
            IsReducibleMemberAtAllPositiveLevels _ argument :=
        fun argument {_memberLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
            domainWeakHeadNormal domainNotPiType domainNotUniverse member
      refine ⟨IsReducibleTypeAtAllLevels.nonDependentArrow domainAllLevels
          domainMemberExtension codomainAllLevels,
        fun functionTerm {predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive domainAllLevels
            (fun argument {_memberPredLevel} m => domainMemberExtension argument m)
            codomainAllLevels
            (fun applicationTerm {_memberPredLevel} m => codomainMemberExtension applicationTerm m)
            member⟩

/-- **A variable type is first-order simply-typed.**  The canonical neutral leaf: a de Bruijn variable is
weak-head-normal (`WeakHeadStep.not_from_var`), is `gen_var`-rooted (neither Π- nor universe-rooted), so it is
an `IsFirstOrderSimplyTyped` leaf.  This is the base inhabitant witnessing the fragment is non-empty and
constructible for concrete types. -/
theorem IsFirstOrderSimplyTyped.ofVariable {scope : Nat} {index : Fin scope} :
    IsFirstOrderSimplyTyped (variableCell index) :=
  IsFirstOrderSimplyTyped.leaf
    (fun _reduct => WeakHeadStep.not_from_var)
    (show Generator.gen_var ≠ Generator.gen_piTyCode by decide)
    (show Generator.gen_var ≠ Generator.gen_universeCode by decide)

/-- **Every neutral type is first-order simply-typed.**  The general leaf principle: a neutral term
(variable, neutral application `f a`, projection `fst p`, or stuck eliminator `natElim n …`) is
weak-head-normal (`IsNeutral.noWeakHeadStep`) and rooted at an elimination generator — neither Π nor
universe (`IsNeutral.rootGenerator_ne_piTyCode` / `…_ne_universeCode`) — so it is an `IsFirstOrderSimplyTyped`
leaf.  This lifts the fragment's leaf class from bare variables to the full Tait neutral family in one
constructor; `ofVariable` is the `IsNeutral.var` instance. -/
theorem IsFirstOrderSimplyTyped.ofNeutral {scope : Nat} {classifier : RawTerm scope}
    (neutral : IsNeutral classifier) : IsFirstOrderSimplyTyped classifier :=
  IsFirstOrderSimplyTyped.leaf
    neutral.noWeakHeadStep
    neutral.rootGenerator_ne_piTyCode
    neutral.rootGenerator_ne_universeCode

/-- **A neutral application `f a` is first-order simply-typed** whenever its function head `f` is neutral —
the canonical NON-variable neutral leaf (a type-family application `F a`).  Instantiates `ofNeutral` at the
`IsNeutral.app` arm, demonstrating the leaf class genuinely extends past variables and Σ-codes. -/
theorem IsFirstOrderSimplyTyped.ofNeutralApplication {scope : Nat}
    {function argument : RawTerm scope} (functionIsNeutral : IsNeutral function) :
    IsFirstOrderSimplyTyped
      (.mkGen .gen_app () (.childCons function (.childCons argument .childNil))) :=
  IsFirstOrderSimplyTyped.ofNeutral (IsNeutral.app functionIsNeutral)

/-- **A Σ-type code is first-order simply-typed.**  A dependent-pair type former is a DATA leaf in the
reducibility model (`ReducibleTypeStep` has no `sigmaType` arm — Σ is `neutral`-treated), weak-head-normal
(`WeakHeadStep.not_from_sigmaTyCode`) and `gen_sigmaTyCode`-rooted (neither Π nor universe), hence a leaf. -/
theorem IsFirstOrderSimplyTyped.ofSigmaTyCode {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} :
    IsFirstOrderSimplyTyped (sigmaTyCodeCell domainCode codomainCode) :=
  IsFirstOrderSimplyTyped.leaf
    (fun _reduct => WeakHeadStep.not_from_sigmaTyCode)
    (show Generator.gen_sigmaTyCode ≠ Generator.gen_piTyCode by decide)
    (show Generator.gen_sigmaTyCode ≠ Generator.gen_universeCode by decide)

/-- **An arrow with a VARIABLE domain over a first-order codomain is first-order simply-typed.**  The recursive
constructor instantiated at the canonical neutral domain: `variableCell index → codomainBase` is first-order
whenever `codomainBase` is, building curried first-order function types `α → β → … → ω` over variable base
types. -/
theorem IsFirstOrderSimplyTyped.arrowOfVariableDomain {scope : Nat} {index : Fin scope}
    {codomainBase : RawTerm scope} (codomain : IsFirstOrderSimplyTyped codomainBase) :
    IsFirstOrderSimplyTyped (piTyCodeCell (variableCell index) (RawTerm.weaken codomainBase)) :=
  IsFirstOrderSimplyTyped.arrow
    (fun _reduct => WeakHeadStep.not_from_var)
    (show Generator.gen_var ≠ Generator.gen_piTyCode by decide)
    (show Generator.gen_var ≠ Generator.gen_universeCode by decide)
    codomain

/-- **End-to-end: a variable type is reducible at all levels and member-extending.**  The first-order Tait
assembly applied to the concrete `ofVariable` witness — a closed demonstration that the reducibility machinery
produces the universe member-extension principle on a concrete type, not merely an abstract fragment. -/
theorem IsFirstOrderSimplyTyped.variableReducibleAndMemberExtension {scope : Nat} {index : Fin scope} :
    IsReducibleTypeAtAllLevels (variableCell index) ∧
      (∀ (term : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) (variableCell index) term →
          IsReducibleMemberAtAllPositiveLevels (variableCell index) term) :=
  IsFirstOrderSimplyTyped.ofVariable.reducibleAndMemberExtension

/-- **End-to-end on a NON-variable neutral type: a neutral application is reducible at all levels and
member-extending.**  The first-order Tait assembly applied to `ofNeutralApplication` — concretely
exercising the reducibility machinery on a type-family application `f a` (function head neutral), the
ground newly covered by `ofNeutral` beyond the bare-variable `variableReducibleAndMemberExtension`. -/
theorem IsFirstOrderSimplyTyped.neutralApplicationReducibleAndMemberExtension {scope : Nat}
    {function argument : RawTerm scope} (functionIsNeutral : IsNeutral function) :
    IsReducibleTypeAtAllLevels
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil))) ∧
      (∀ (term : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1)
            (.mkGen .gen_app () (.childCons function (.childCons argument .childNil))) term →
          IsReducibleMemberAtAllPositiveLevels
            (.mkGen .gen_app () (.childCons function (.childCons argument .childNil))) term) :=
  (IsFirstOrderSimplyTyped.ofNeutralApplication functionIsNeutral).reducibleAndMemberExtension

end FX1Poly.Typed
