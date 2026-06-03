import FX1Poly.Typed.DependentPiNeutralCodomain
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension

/-! # FX1Poly/Typed/DependentlyTypedNeutralDomainFragment
    — the DEPENDENT analogue of `IsFirstOrderSimplyTyped`: an inductive fragment + fundamental theorem

`FirstOrderSimplyTypedReducibility` / `HigherOrderSimplyTypedReducibility` close the SIMPLY-TYPED fragment
(neutral / data leaves + NON-dependent arrows) under one fundamental theorem.  The previous ticks shipped the
POINT lemmas for the genuinely dependent case (`dependentPiOverNeutralDomain`, its neutral-codomain
specialization).  This file CONSOLIDATES them into a proper inductive fragment with a single fundamental
theorem — the dependent analogue of `IsFirstOrderSimplyTyped.reducibleAndMemberExtension`.

`IsNeutralDomainDependentlyTyped` is the closure of: neutral / data leaves, under dependent Π `Π (x : dom).
cod` whose DOMAIN is a neutral / data leaf and whose codomain INSTANTIATIONS `RawTerm.subst0 cod arg` are
recursively in the fragment (for every argument).  This captures arbitrarily-deep curried dependent function
types `Π (x : A). Π (y : B x). C x y` over neutral / data base types — the codomain genuinely depends on the
bound variable at every layer, so it lives strictly beyond the simply-typed (non-dependent-arrow) fragment.
Substitution-stability is not needed as a side lemma: the `dependentPi` constructor stores the codomain's
fragment-membership UNIVERSALLY over arguments, so the structural recursion bottoms out at neutral leaves.

The fundamental theorem `reducibleAndMemberExtension` proves every fragment type is reducible at all levels AND
admits member-extension (a positive-level member extends to all positive levels — the #672 gate restricted to
this fragment).  The leaf arm is the neutral leaf + the #717-style neutral member arm `ofNeutralClassifier`;
the `dependentPi` arm is the all-levels Π reassembly `dependentPiOverNeutralDomain` (type) and the Π
member-extension `dependentPiMemberExtensionOverNeutralDomain` (member), each fed the codomain inductive
hypothesis per argument.  The open crux of #672 remains the universe-DOMAIN dependent Π (type-polymorphism).

## Zero-axiom verification

A 2-constructor witness inductive (`leaf` / `dependentPi` with a universally-quantified codomain premise —
strictly positive) plus one induction over it, feeding the shipped all-levels Π reassembly + neutral leaves.
The concrete witness `typeFamilyApplication` computes the codomain substitution by `subst0_app_reduces` +
`weaken_subst_singleton` + `subst0_var_zero` and reads neutrality off `IsNeutral.app (IsNeutral.var _)`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **All-levels dependent Π reducibility over a neutral / data domain.**  The ALL-LEVELS (incl. fuel `0`)
companion to the positive-only `IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain`.  When the
domain is weak-head-normal non-Π non-universe, the all-levels Π reassembly `piTypeOfDomainMemberExtension`'s
domain legs discharge via the neutral leaf (`ofWeakHeadNormalNonPiNonUniverse`) and the arbitrary-level
neutral member arm (`ofNeutralClassifier`, which accepts a member at ANY level including `0` — unlike the
positive-only `ofNeutralTypeMember`), isolating the residual to the codomain's all-levels reducibility per
all-positive argument.  This all-levels form is what the fragment fundamental theorem's member leg needs (it
feeds the codomain's all-levels reducibility into the Π member-extension). -/
theorem IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain {scope : Nat}
    {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
    (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels dom argument →
        IsReducibleTypeAtAllLevels (RawTerm.subst0 cod argument)) :
    IsReducibleTypeAtAllLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) :=
  IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension
    (IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
      domainWeakHeadNormal domainNotPiType domainNotUniverse)
    (fun _argument {_memberLevel} member =>
      IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
        domainWeakHeadNormal domainNotPiType domainNotUniverse member)
    codomainAllLevels

/-- **The dependently-typed neutral-domain fragment.**  The closure of neutral / data leaves under dependent
Π `Π (x : dom). cod` whose domain is a neutral / data leaf and whose codomain instantiations are recursively
in the fragment.  Captures curried dependent function types `Π (x : A). Π (y : B x). C x y` over neutral /
data base types — the dependent analogue of `IsFirstOrderSimplyTyped` (whose arrows are non-dependent).  The
`dependentPi` premise is universally quantified over arguments (strictly positive: the inductive occurs under
a `∀`), so no substitution-stability side lemma is needed. -/
inductive IsNeutralDomainDependentlyTyped : {scope : Nat} → RawTerm scope → Prop
  /-- A neutral / data leaf (weak-head-normal, neither Π- nor universe-rooted). -/
  | leaf {scope : Nat} {classifier : RawTerm scope}
      (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
      (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode)
      (notUniverse : classifier.rootGenerator ≠ Generator.gen_universeCode) :
      IsNeutralDomainDependentlyTyped classifier
  /-- A dependent Π over a neutral / data domain whose every codomain instantiation is recursively in the
  fragment. -/
  | dependentPi {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
      (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep dom reduct)
      (domainNotPiType : dom.rootGenerator ≠ Generator.gen_piTyCode)
      (domainNotUniverse : dom.rootGenerator ≠ Generator.gen_universeCode)
      (codomainFragment : ∀ argument : RawTerm scope,
          IsNeutralDomainDependentlyTyped (RawTerm.subst0 cod argument)) :
      IsNeutralDomainDependentlyTyped
        (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil)))

/-- **Fundamental theorem for the dependently-typed neutral-domain fragment.**  Every fragment type is
reducible at all levels AND admits member-extension (a positive-level member extends to all positive levels —
the #672 fuel-stability gate restricted to this fragment).  By induction on the fragment witness: the `leaf`
arm uses the neutral leaf (`ofWeakHeadNormalNonPiNonUniverse`) and the arbitrary-level neutral member arm
(`ofNeutralClassifier`); the `dependentPi` arm uses the all-levels Π reassembly
(`dependentPiOverNeutralDomain`) for the type half and the Π member-extension
(`dependentPiMemberExtensionOverNeutralDomain`) for the member half, each fed the per-argument codomain
inductive hypothesis.  The dependent analogue of `IsFirstOrderSimplyTyped.reducibleAndMemberExtension`. -/
theorem IsNeutralDomainDependentlyTyped.reducibleAndMemberExtension
    {scope : Nat} {typeCode : RawTerm scope}
    (fragment : IsNeutralDomainDependentlyTyped typeCode) :
    IsReducibleTypeAtAllLevels typeCode ∧
      (∀ (functionTerm : RawTerm scope) {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) typeCode functionTerm →
          IsReducibleMemberAtAllPositiveLevels typeCode functionTerm) := by
  induction fragment with
  | leaf weakHeadNormal notPiType notUniverse =>
      exact ⟨IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
          weakHeadNormal notPiType notUniverse,
        fun functionTerm {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
            weakHeadNormal notPiType notUniverse member⟩
  | dependentPi domainWeakHeadNormal domainNotPiType domainNotUniverse _codomainFragment codomainIH =>
      refine ⟨IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain
          domainWeakHeadNormal domainNotPiType domainNotUniverse
          (fun argument _argMember => (codomainIH argument).1),
        fun functionTerm {_predLevel} member =>
          IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain
            domainWeakHeadNormal domainNotPiType domainNotUniverse
            (fun argument _argMember => (codomainIH argument).1)
            (fun argument _argMember applicationTerm {_memberPredLevel} applicationMember =>
              (codomainIH argument).2 applicationTerm applicationMember)
            member⟩

/-- **Every neutral term is in the fragment.**  The leaf class lifted to the full Tait neutral family
(variable, neutral application, projection, stuck eliminator) via `IsNeutral`. -/
theorem IsNeutralDomainDependentlyTyped.ofNeutral {scope : Nat} {classifier : RawTerm scope}
    (neutral : IsNeutral classifier) : IsNeutralDomainDependentlyTyped classifier :=
  IsNeutralDomainDependentlyTyped.leaf
    neutral.noWeakHeadStep neutral.rootGenerator_ne_piTyCode neutral.rootGenerator_ne_universeCode

/-- **A type-family application `Π (x : A). P x` is in the fragment** — a concrete genuinely-DEPENDENT member
(`A = var domVar`, `P = var familyVar`).  The codomain `app (weaken P) (var 0)` mentions the bound `x`; every
instantiation `subst0 (app (weaken P) (var 0)) arg = app P arg` is a neutral leaf (head `P` a variable), so
the `dependentPi` constructor applies.  Combined with the fundamental theorem this re-derives the previous
tick's `concreteDependentPi_isReducibleType`, now as a fragment member. -/
theorem IsNeutralDomainDependentlyTyped.typeFamilyApplication {scope : Nat} (domVar familyVar : Fin scope) :
    IsNeutralDomainDependentlyTyped
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_var domVar .childNil)
          (.childCons
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            .childNil))) :=
  IsNeutralDomainDependentlyTyped.dependentPi
    (fun _reduct => (IsNeutral.var domVar).noWeakHeadStep _)
    (IsNeutral.var domVar).rootGenerator_ne_piTyCode
    (IsNeutral.var domVar).rootGenerator_ne_universeCode
    (fun arg => by
      rw [show RawTerm.subst0
            (.mkGen .gen_app ()
              (.childCons (RawTerm.weaken (.mkGen .gen_var familyVar .childNil))
                (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil) .childNil)))
            arg
          = (.mkGen .gen_app ()
              (.childCons (.mkGen .gen_var familyVar .childNil) (.childCons arg .childNil)))
          from by
            rw [RawTerm.subst0_app_reduces,
                show RawTerm.subst0 (RawTerm.weaken (.mkGen .gen_var familyVar .childNil)) arg
                  = (.mkGen .gen_var familyVar .childNil : RawTerm scope)
                  from RawTerm.weaken_subst_singleton _ _,
                RawTerm.subst0_var_zero]]
      exact IsNeutralDomainDependentlyTyped.ofNeutral (IsNeutral.app (IsNeutral.var familyVar)))

end FX1Poly.Typed
