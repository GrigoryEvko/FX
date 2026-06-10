import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationSmokeCorpus
import FX1Poly.Core.StrongNormalizationModalEliminators
import FX1Poly.Core.StrongNormalizationUniverseModeBridges

/-! # Foundation/PolyCell/Core/StrongNormalizationFormerCorpus
    — one closed strong-normalization witness per raw former family

`StrongNormalizationSmokeCorpus` pins the three SN entry points the typed engine reduces to:
the variable leaf, the unit leaf, and the identity beta redex.  This file widens that into a complete
per-former regression corpus: one closed witness for every raw former that ships a forward
strong-normalization closure lemma in `StrongNormalizationConstructors`.  Each witness applies that
former's `..._isStronglyNormalizing_of_...` closure to the universal strongly-normalizing leaf
(`smoke_unit_isStronglyNormalizing`, the unit cell, which is scope polymorphic so it fills both
same-scope and under-binder child slots).  Together they exercise every `Step.from_<former>`
congruence injection plus the generic one-child and two-child congruence drivers
(`isStronglyNormalizing_of_oneChildCong` / `isStronglyNormalizing_of_twoChildCong`) on a concrete
cell, so a regression in any single former's congruence lemma fails its own gated witness.

The twenty single-former witnesses are grouped by family: lambda binders (under one fresh binder),
unary data constructors, binary data constructors, non-dependent type codes, and dependent type
codes plus the polynomial functor (whose second child lives under a binder).  Two closing witnesses
nest formers (`lam (natSucc unit)` and `piTyCode unit (sigmaTyCode unit unit)`) to show the closures
compose with correct de Bruijn scope threading through the under-binder slots — the codomain of the
outer pi code lives at `scope + 1`, the inner sigma codomain at `scope + 2`, and the leaves adapt by
scope polymorphism.

## Zero-axiom verification

Every witness is a shipped-lemma application terminating in the unit-leaf witness; no tactic, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-! ## Lambda binder family — body under one fresh binder -/

/-- **Smoke: a lambda over the unit leaf is strongly normalizing.** -/
theorem smoke_lam_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_lam ()
        (.childCons
          (.mkGen .gen_unit () .childNil : RawTerm scope)
          (.childCons
            (.mkGen .gen_unit () .childNil : RawTerm (scope + 1))
            .childNil)) : RawTerm scope) :=
  lam_isStronglyNormalizing_of_body
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a cubical path abstraction over the unit leaf is strongly normalizing.** -/
theorem smoke_pathLam_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_pathLam ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  pathLam_isStronglyNormalizing_of_body smoke_unit_isStronglyNormalizing

/-- **Smoke: a differential lambda over the unit leaf is strongly normalizing.** -/
theorem smoke_diffLambda_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_diffLambda ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  diffLambda_isStronglyNormalizing_of_body smoke_unit_isStronglyNormalizing

/-! ## Unary data constructor family -/

/-- **Smoke: the natural successor of the unit leaf is strongly normalizing.** -/
theorem smoke_natSucc_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_natSucc ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  natSucc_isStronglyNormalizing_of_predecessor smoke_unit_isStronglyNormalizing

/-- **Smoke: option `some` of the unit leaf is strongly normalizing.** -/
theorem smoke_optionSome_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_optionSome ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  optionSome_isStronglyNormalizing_of_value smoke_unit_isStronglyNormalizing

/-- **Smoke: either-left of the unit leaf is strongly normalizing.** -/
theorem smoke_eitherInl_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_eitherInl ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  eitherInl_isStronglyNormalizing_of_value smoke_unit_isStronglyNormalizing

/-- **Smoke: either-right of the unit leaf is strongly normalizing.** -/
theorem smoke_eitherInr_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_eitherInr ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  eitherInr_isStronglyNormalizing_of_value smoke_unit_isStronglyNormalizing

/-- **Smoke: a reflexivity witness over the unit leaf is strongly normalizing.** -/
theorem smoke_refl_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_refl ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  refl_isStronglyNormalizing_of_witness smoke_unit_isStronglyNormalizing

/-- **Smoke: modal introduction over the unit leaf is strongly normalizing.** -/
theorem smoke_modIntro_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_modIntro ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  modIntro_isStronglyNormalizing_of_value smoke_unit_isStronglyNormalizing

/-! ## Binary data constructor family -/

/-- **Smoke: the pair of two unit leaves is strongly normalizing.** -/
theorem smoke_pair_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  pair_isStronglyNormalizing_of_components
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a list cons of two unit leaves is strongly normalizing.** -/
theorem smoke_listCons_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_listCons ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  listCons_isStronglyNormalizing_of_head_tail
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: glue introduction over two unit leaves is strongly normalizing.** -/
theorem smoke_glueIntro_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_glueIntro ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  glueIntro_isStronglyNormalizing_of_components
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-! ## Non-dependent type-code family -/

/-- **Smoke: an arrow type code over two unit leaves is strongly normalizing.** -/
theorem smoke_arrowCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_arrowCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  arrowCode_isStronglyNormalizing_of_domain_codomain
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a product type code over two unit leaves is strongly normalizing.** -/
theorem smoke_productCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_productCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  productCode_isStronglyNormalizing_of_left_right
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a sum type code over two unit leaves is strongly normalizing.** -/
theorem smoke_sumCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_sumCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  sumCode_isStronglyNormalizing_of_left_right
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: an either type code over two unit leaves is strongly normalizing.** -/
theorem smoke_eitherCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_eitherCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  eitherCode_isStronglyNormalizing_of_left_right
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: an equivalence type code over two unit leaves is strongly normalizing.** -/
theorem smoke_equivCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_equivCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  equivCode_isStronglyNormalizing_of_source_target
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-! ## Dependent type-code and functor family — second child under one fresh binder -/

/-- **Smoke: a pi type code (unit domain, unit under-binder codomain) is strongly normalizing.** -/
theorem smoke_piTyCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  piTyCode_isStronglyNormalizing_of_domain_codomain
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a sigma type code (unit domain, unit under-binder codomain) is strongly normalizing.** -/
theorem smoke_sigmaTyCode_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_sigmaTyCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  sigmaTyCode_isStronglyNormalizing_of_domain_codomain
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: a polynomial functor code (unit position type, unit under-binder family) is strongly
normalizing.** -/
theorem smoke_polyFunctor_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_polyFunctor ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  polyFunctor_isStronglyNormalizing_of_position_type_family
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-! ## Nested composition — closures compose with correct de Bruijn scope threading -/

/-- **Smoke: a lambda whose body is the successor of the unit leaf is strongly normalizing.**  The
inner `natSucc unit` is built at scope `scope + 1` (under the lambda binder) and lifted by the
successor closure; the lambda closure then lifts that to the abstraction.  Demonstrates a forward SN
closure applied to a non-leaf, under-binder child. -/
theorem smoke_nestedLamNatSucc_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_lam ()
        (.childCons
          (.mkGen .gen_unit () .childNil : RawTerm scope)
          (.childCons
            (.mkGen .gen_natSucc ()
              (.childCons (.mkGen .gen_unit () .childNil) .childNil))
            .childNil)) : RawTerm scope) :=
  lam_isStronglyNormalizing_of_body
    smoke_unit_isStronglyNormalizing
    (natSucc_isStronglyNormalizing_of_predecessor smoke_unit_isStronglyNormalizing)

/-- **Smoke: a pi type code whose codomain is a sigma type code is strongly normalizing.**  The pi
codomain lives at `scope + 1`; the sigma there carries its own under-binder codomain at `scope + 2`.
All four unit leaves adapt by scope polymorphism, so this single witness exercises three-deep
under-binder scope threading across two dependent type-code closures. -/
theorem smoke_nestedPiSigma_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons
            (.mkGen .gen_sigmaTyCode ()
              (.childCons (.mkGen .gen_unit () .childNil)
                (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
            .childNil)) : RawTerm scope) :=
  piTyCode_isStronglyNormalizing_of_domain_codomain
    smoke_unit_isStronglyNormalizing
    (sigmaTyCode_isStronglyNormalizing_of_domain_codomain
      smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing)

/-! ## Modal core + universe-mode bridge family — congruence-only operators

The modal eliminators (`gen_modElim` / `gen_subsume`) and the 2LTT universe-mode bridges
(`gen_liftInnerToOuter` / `gen_lowerOuterToInner`) carry no β+ι root rule — their only collapses
(`modIntro (modElim m) ↝ m`, `lower (lift x) ↝ x`) are raw η / mode-bridge rules outside the β+ι
substrate — so each ships a congruence-only forward SN closure in `StrongNormalizationModalEliminators`
/ `StrongNormalizationUniverseModeBridges`.  These witnesses pin one closed cell per operator, exactly
as the per-former corpus does for the data/type-code formers, so a regression in any single congruence
closure fails its own gated witness. -/

/-- **Smoke: modal elimination of the unit leaf is strongly normalizing.** -/
theorem smoke_modElim_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_modElim ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  modElim_isStronglyNormalizing_of_child smoke_unit_isStronglyNormalizing

/-- **Smoke: modal subsumption of the unit leaf is strongly normalizing.** -/
theorem smoke_subsume_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_subsume ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  subsume_isStronglyNormalizing_of_child smoke_unit_isStronglyNormalizing

/-- **Smoke: the inner→outer universe-mode lift of the unit leaf is strongly normalizing.** -/
theorem smoke_liftInnerToOuter_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_liftInnerToOuter ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil) : RawTerm scope) :=
  liftInnerToOuter_isStronglyNormalizing_of_child smoke_unit_isStronglyNormalizing

/-- **Smoke: the outer→inner universe-mode lower of two unit leaves (outer term + cofibrancy witness)
is strongly normalizing.**  Exercises the two-child congruence closure of the mode-bridge lower. -/
theorem smoke_lowerOuterToInner_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_lowerOuterToInner ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)) : RawTerm scope) :=
  lowerOuterToInner_isStronglyNormalizing_of_children
    smoke_unit_isStronglyNormalizing smoke_unit_isStronglyNormalizing

/-- **Smoke: modal elimination of an inner→outer lift is strongly normalizing.**  Nests two
congruence-only modal / mode-bridge closures (`modElim` over `liftInnerToOuter` over the unit leaf)
to show they compose, every child living at the ambient scope. -/
theorem smoke_modElimLiftInnerToOuter_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_modElim ()
        (.childCons
          (.mkGen .gen_liftInnerToOuter ()
            (.childCons (.mkGen .gen_unit () .childNil) .childNil))
          .childNil) : RawTerm scope) :=
  modElim_isStronglyNormalizing_of_child smoke_liftInnerToOuter_isStronglyNormalizing

end FX1Poly.Core
