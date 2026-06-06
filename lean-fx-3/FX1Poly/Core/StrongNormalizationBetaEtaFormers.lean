import FX1Poly.Core.StrongNormalizationBetaEtaLeaves

/-! # Foundation/PolyCell/Core/StrongNormalizationBetaEtaFormers
    — the per-former SN corpus is robust under the eta extension (formers)

The leaf base (`StrongNormalizationBetaEtaLeaves`) lifts the variable / unit SN entry points to
`Step.betaEtaStar.IsStronglyNormalizing` (over `Step.betaEta = Step ∪ Step.eta`).  This file completes
the eta extension by lifting the full per-former corpus: every former over the (beta-eta-normal) unit leaf
children is itself beta-eta normal, hence beta-eta strongly normalizing.

Each former-over-unit is beta-eta normal for two independent reasons:

* **No `Step`.**  A `Step` of `former unit…` can only be the generic congruence `cong` (the `beta` and the
  seventeen `iota*` constructors demand an application / eliminator root, pruned here by generator
  mismatch); its `StepChildren` payload would step some child, but every child is the unit leaf, which has
  no `Step` (`noStep_unit`).  The two `StepChildren` inversion helpers `noStepChildren_oneNormalChild` /
  `noStepChildren_twoNormalChildren` discharge this for the one- and two-child spines uniformly across
  scopes (a binder child sits at `scope + 1`; the helpers are scope-shift polymorphic).

* **No `Step.eta`.**  The five eta constructors demand a specific former-shaped redex source
  (`lam (app f (var 0))`, `pair (fst p) (snd p)`, …); `former unit…` matches none — either the root
  generator differs, or (for the eta-shaped roots lam / pair / pathLam / modIntro / glueIntro) the child is
  the unit leaf rather than the required projection / application shape — so `cases` closes by mismatch.

Beta-eta normality then yields beta-eta SN through the reusable `Acc.intro` base
`isStronglyNormalizingBetaEta_of_noBetaEtaStep`.

## Zero-axiom verification

`cases` on the `Step.betaEta` disjunction, on `Step` (only `cong` survives), on `StepChildren`
(`here` / `there`), and on `Step.eta` (all closed by generator / child-shape mismatch); each is pure
constructor inversion with no equational rewriting on indices.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before
landing).  Gated per declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-! ## Generic StepChildren-normality inversion helpers -/

/-- **A one-child spine over a `Step`-normal child takes no `StepChildren` step.**  The `here`
constructor would step the (normal) head; the `there` constructor would step the empty tail. -/
theorem noStepChildren_oneNormalChild {parentScope headShift : Nat}
    {child : RawTerm (parentScope + headShift)}
    (childNormal : ∀ reduct : RawTerm (parentScope + headShift), ¬ Step child reduct)
    {children' : RawTermChildren [headShift] parentScope}
    (childrenStep : StepChildren (.childCons child .childNil) children') : False := by
  cases childrenStep with
  | here _rest childStep => exact childNormal _ childStep
  | there _head restStep => cases restStep

/-- **A two-child spine over two `Step`-normal children takes no `StepChildren` step.**  Inverting twice:
each `here` steps a (normal) child, the inner `there` steps the empty tail. -/
theorem noStepChildren_twoNormalChildren {parentScope headShift secondShift : Nat}
    {first : RawTerm (parentScope + headShift)} {second : RawTerm (parentScope + secondShift)}
    (firstNormal : ∀ reduct : RawTerm (parentScope + headShift), ¬ Step first reduct)
    (secondNormal : ∀ reduct : RawTerm (parentScope + secondShift), ¬ Step second reduct)
    {children' : RawTermChildren [headShift, secondShift] parentScope}
    (childrenStep : StepChildren (.childCons first (.childCons second .childNil)) children') : False := by
  cases childrenStep with
  | here _rest childStep => exact firstNormal _ childStep
  | there _head restStep =>
    cases restStep with
    | here _rest childStep => exact secondNormal _ childStep
    | there _head restStep => cases restStep

/-! ## Lambda binder family — body under one fresh binder (child at scope + 1) -/

/-- **Smoke: a lambda over the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_lam_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_lam () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a cubical path abstraction over the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_pathLam_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_pathLam () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a differential lambda over the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_diffLambda_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_diffLambda () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-! ## Unary data constructor family (child at scope) -/

/-- **Smoke: the natural successor of the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_natSucc_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_natSucc () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: option `some` of the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_optionSome_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_optionSome () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: either-left of the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_eitherInl_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_eitherInl () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: either-right of the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_eitherInr_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_eitherInr () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a reflexivity witness over the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_refl_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_refl () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: modal introduction over the unit leaf is beta-eta strongly normalizing.** -/
theorem smoke_modIntro_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_modIntro () (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_oneNormalChild (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-! ## Binary data constructor family (both children at scope) -/

/-- **Smoke: the pair of two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_pair_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a list cons of two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_listCons_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_listCons ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: glue introduction over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_glueIntro_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-! ## Non-dependent type-code family (both children at scope) -/

/-- **Smoke: an arrow type code over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_arrowCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_arrowCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a product type code over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_productCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_productCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a sum type code over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_sumCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_sumCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: an either type code over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_eitherCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_eitherCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: an equivalence type code over two unit leaves is beta-eta strongly normalizing.** -/
theorem smoke_equivCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_equivCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-! ## Dependent type-code and functor family (second child at scope + 1) -/

/-- **Smoke: a pi type code (unit domain, unit under-binder codomain) is beta-eta strongly normalizing.** -/
theorem smoke_piTyCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a sigma type code (unit domain, unit under-binder codomain) is beta-eta strongly
normalizing.** -/
theorem smoke_sigmaTyCode_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_sigmaTyCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-- **Smoke: a polynomial functor code (unit position type, unit under-binder family) is beta-eta
strongly normalizing.** -/
theorem smoke_polyFunctor_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_polyFunctor ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply isStronglyNormalizingBetaEta_of_noBetaEtaStep
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | cong _generator _payload childrenStep =>
      exact noStepChildren_twoNormalChildren (fun _ => noStep_unit) (fun _ => noStep_unit) childrenStep
  | inr etaEdge => cases etaEdge

/-! ## Identity beta-redex — the non-normal-form entry point (completes the entry-point corpus under betaEta) -/

/-- **The identity lambda is `Step`-normal.**  `lam (var 0)` has no `beta` / `iota` redex (its root is a
lambda, not an application or eliminator) and its single child `var 0` is `Step`-normal (`noStep_var`), so
the only surviving `cong` carries an impossible child step. -/
theorem noStep_lamVar0 {scope : Nat} {targetTerm : RawTerm scope}
    (step : Step
      (.mkGen .gen_lam ()
        (.childCons (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) .childNil)) targetTerm) :
    False := by
  cases step with
  | cong _generator _payload childrenStep =>
    exact noStepChildren_oneNormalChild
      (fun _ stepFromVar => noStep_var ⟨0, Nat.succ_pos scope⟩ stepFromVar) childrenStep

/-- **Smoke: the identity beta-redex `(lam (var 0)) unit` is beta-eta strongly normalizing.**  Unlike the
leaf and former witnesses this is NOT beta-eta normal — it carries a redex — so this is the corpus's first
head-expansion case: its sole beta-eta reduct is the contractum `unit` (beta-eta SN by
`unit_isStronglyNormalizingBetaEta`), the `cong` congruences are impossible (both children
`lam (var 0)` / `unit` are `Step`-normal), and no `Step.eta` fires (an application is not an eta redex
shape).  Completes the entry-point corpus (variable / unit / identity redex) under the eta
extension. -/
theorem smoke_identityRedex_isStronglyNormalizingBetaEta {scope : Nat} :
    Step.betaEtaStar.IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) := by
  apply Acc.intro
  intro _reduct edge
  cases edge with
  | inl stepEdge =>
    cases stepEdge with
    | beta => exact unit_isStronglyNormalizingBetaEta
    | cong _generator _payload childrenStep =>
      exact (noStepChildren_twoNormalChildren
        (fun _ stepFromLam => noStep_lamVar0 stepFromLam) (fun _ => noStep_unit) childrenStep).elim
  | inr etaEdge => cases etaEdge

end FX1Poly.Core
