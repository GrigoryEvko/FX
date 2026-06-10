import FX1Poly.Core.RawTermStrengthen
import FX1Poly.Core.StepStar

/-! # Foundation/PolyCell/Core/StepEta

Raw structural eta reduction for the PolyCell v2 substrate.

This file deliberately keeps eta separate from the beta+iota `Step`
relation.  Existing `Step` confluence and strong-normalization work
therefore remains beta+iota-scoped; beta+eta consumers opt in through
`Step.betaEta` and `Step.betaEtaStar`.

Binder eta is gated by construction: the left hand side contains
`RawTerm.weaken innerTerm`, so the freshness/strengthening witness is
the raw syntax itself rather than an external proof premise.  The
semantic strengthening lemmas live in `RawTermStrengthen.lean`.
-/

namespace FX1Poly.Core

namespace RawTerm

/-- Newest de Bruijn variable in a freshly extended scope. -/
@[reducible] def newestVar {scope : Nat} : RawTerm (scope + 1) :=
  .mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil

/-- Raw eta source for functions:
`lam domainAnn (app (weaken f) newestVar)`.  Church-style: the lambda
carries a domain annotation; eta contraction discards it. -/
@[reducible] def etaLamSource {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_lam ()
    (.childCons domainAnn
      (.childCons
        (.mkGen .gen_app ()
          (.childCons
            (RawTerm.weaken innerFunction)
            (.childCons RawTerm.newestVar .childNil)))
        .childNil))

/-- Raw eta source for pairs:
`pair (fst p) (snd p)`. -/
@[reducible] def etaPairSource {scope : Nat}
    (pairTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pair ()
    (.childCons
      (.mkGen .gen_fst () (.childCons pairTerm .childNil))
      (.childCons
        (.mkGen .gen_snd () (.childCons pairTerm .childNil))
        .childNil))

/-- Raw eta source for cubical paths:
`pathLam (pathApp (weaken p) newestVar)`.  The current raw substrate
uses `gen_var` for the bound interval slot; the typed cubical layer
interprets that slot as an interval variable. -/
@[reducible] def etaPathLamSource {scope : Nat}
    (innerPath : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_pathLam ()
    (.childCons
      (.mkGen .gen_pathApp ()
        (.childCons
          (RawTerm.weaken innerPath)
          (.childCons RawTerm.newestVar .childNil)))
      .childNil)

/-- Raw eta source for modal introduction/elimination:
`modIntro (modElim m)`.  Profile-level admissibility decides which
modalities may consume this eta rule downstream. -/
@[reducible] def etaModIntroSource {scope : Nat}
    (modalTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_modIntro ()
    (.childCons
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil))
      .childNil)

/-- Raw eta source for cubical Glue:
`glueIntro (glueElim g) g`.  The second child records the same glued
term so the rule is syntactically by-construction; CCHM coherence
side conditions remain profile-layer obligations. -/
@[reducible] def etaGlueIntroSource {scope : Nat}
    (gluedTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_glueIntro ()
    (.childCons
      (.mkGen .gen_glueElim () (.childCons gluedTerm .childNil))
      (.childCons gluedTerm .childNil))

end RawTerm

namespace Step

/-- Single-step raw eta reduction, sibling to beta+iota `Step`.

The current `Generator` enum contains lambda/application,
pair/projection, path abstraction/application, modal
intro/elimination, and Glue intro/elimination.  Clock and
parametricity eta slots described in `polycell.md` are intentionally
not constructors here yet because their generators are Phase Z7/Z8
entries and are not present in the current enum. -/
inductive eta : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- Function eta: `lam (app (weaken f) newestVar)` contracts to `f`. -/
  | etaLam {scope : Nat} (domainAnn innerFunction : RawTerm scope) :
      eta (RawTerm.etaLamSource domainAnn innerFunction) innerFunction
  /-- Pair eta: `pair (fst p) (snd p)` contracts to `p`. -/
  | etaPair {scope : Nat} (pairTerm : RawTerm scope) :
      eta (RawTerm.etaPairSource pairTerm) pairTerm
  /-- Cubical path eta: `pathLam (pathApp (weaken p) newestVar)`
      contracts to `p`. -/
  | etaPathLam {scope : Nat} (innerPath : RawTerm scope) :
      eta (RawTerm.etaPathLamSource innerPath) innerPath
  /-- Modal eta skeleton: `modIntro (modElim m)` contracts to `m`
      for profiles that admit the matching modality law. -/
  | etaModIntro {scope : Nat} (modalTerm : RawTerm scope) :
      eta (RawTerm.etaModIntroSource modalTerm) modalTerm
  /-- Glue eta skeleton: `glueIntro (glueElim g) g` contracts to `g`
      once the profile supplies the CCHM Glue coherence obligations. -/
  | etaGlueIntro {scope : Nat} (gluedTerm : RawTerm scope) :
      eta (RawTerm.etaGlueIntroSource gluedTerm) gluedTerm

/-- Reflexive-transitive closure of raw eta. -/
inductive etaStar {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- Zero eta steps. -/
  | refl (term : RawTerm scope) : etaStar term term
  /-- Left extension by one eta step. -/
  | trans {first second third : RawTerm scope} :
      Step.eta first second → etaStar second third → etaStar first third

/-- Combined beta+iota or eta single-step relation. -/
def betaEta {scope : Nat} (sourceTerm targetTerm : RawTerm scope) : Prop :=
  Step sourceTerm targetTerm ∨ Step.eta sourceTerm targetTerm

/-- Reflexive-transitive closure of the combined beta+iota+eta
relation. -/
inductive betaEtaStar {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- Zero beta+iota+eta steps. -/
  | refl (term : RawTerm scope) : betaEtaStar term term
  /-- Left extension by one beta+iota+eta step. -/
  | trans {first second third : RawTerm scope} :
      Step.betaEta first second → betaEtaStar second third →
        betaEtaStar first third

namespace eta

/-- Lift a single eta step through a raw-term transformer that preserves
eta.  This is the single-step counterpart of the closure-level
`Step.etaStar.mapStep`. -/
theorem mapStep {scope : Nat}
    (mapTerm : RawTerm scope → RawTerm scope)
    (mapEta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step.eta sourceTerm targetTerm →
          Step.eta (mapTerm sourceTerm) (mapTerm targetTerm))
    {sourceTerm targetTerm : RawTerm scope}
    (etaStep : Step.eta sourceTerm targetTerm) :
    Step.eta (mapTerm sourceTerm) (mapTerm targetTerm) :=
  mapEta etaStep

/-- The function-eta source really satisfies the computational
strengthening side condition for its function child. -/
theorem etaLam_weakened_function_strengthens {scope : Nat}
    (innerFunction : RawTerm scope) :
    RawTerm.strengthen (RawTerm.weaken innerFunction) =
      some innerFunction :=
  RawTerm.strengthen_weaken innerFunction

/-- Smoke: eta-lambda fires on a closed unit-shaped raw term.

Church-style: `etaLamSource` carries a domain annotation as its
first argument; the contraction discards it.  Both the annotation
and the inner function are the closed `unit` term here. -/
theorem etaLam_unit_smoke :
    Step.eta
      (RawTerm.etaLamSource
        (.mkGen .gen_unit () .childNil : RawTerm 0)
        (.mkGen .gen_unit () .childNil : RawTerm 0))
      (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  Step.eta.etaLam _ _

/-- Smoke: eta-pair fires on an explicit pair term. -/
theorem etaPair_pair_smoke :
    let pairTerm : RawTerm 0 :=
      .mkGen .gen_pair ()
        (.childCons
          (.mkGen .gen_boolTrue () .childNil)
          (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil))
    Step.eta (RawTerm.etaPairSource pairTerm) pairTerm :=
  Step.eta.etaPair _

/-- Smoke: path eta fires on a closed unit-shaped raw term. -/
theorem etaPathLam_unit_smoke :
    Step.eta
      (RawTerm.etaPathLamSource
        (.mkGen .gen_unit () .childNil : RawTerm 0))
      (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  Step.eta.etaPathLam _

/-- Smoke: modal eta fires on a closed unit-shaped raw term. -/
theorem etaModIntro_unit_smoke :
    Step.eta
      (RawTerm.etaModIntroSource
        (.mkGen .gen_unit () .childNil : RawTerm 0))
      (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  Step.eta.etaModIntro _

/-- Smoke: Glue eta fires on a closed unit-shaped raw term. -/
theorem etaGlueIntro_unit_smoke :
    Step.eta
      (RawTerm.etaGlueIntroSource
        (.mkGen .gen_unit () .childNil : RawTerm 0))
      (.mkGen .gen_unit () .childNil : RawTerm 0) :=
  Step.eta.etaGlueIntro _

end eta

namespace etaStar

/-- Embed one eta step into `etaStar`. -/
theorem single {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (etaStep : Step.eta sourceTerm targetTerm) :
    Step.etaStar sourceTerm targetTerm :=
  Step.etaStar.trans etaStep (Step.etaStar.refl _)

/-- Compose two eta-star chains. -/
theorem trans_compose {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    (firstChain : Step.etaStar firstTerm secondTerm)
    (secondChain : Step.etaStar secondTerm thirdTerm) :
    Step.etaStar firstTerm thirdTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans headStep _ tailIH =>
      exact Step.etaStar.trans headStep (tailIH secondChain)

/-- Lift an eta-star chain through a transformer that preserves
single eta steps. -/
theorem mapStep {scope : Nat}
    (mapTerm : RawTerm scope → RawTerm scope)
    (mapEta :
      ∀ {sourceTerm targetTerm : RawTerm scope},
        Step.eta sourceTerm targetTerm →
          Step.eta (mapTerm sourceTerm) (mapTerm targetTerm))
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.etaStar sourceTerm targetTerm) :
    Step.etaStar (mapTerm sourceTerm) (mapTerm targetTerm) := by
  induction chain with
  | refl term => exact Step.etaStar.refl (mapTerm term)
  | trans headStep _ tailIH =>
      exact Step.etaStar.trans (mapEta headStep) tailIH

end etaStar

namespace betaEtaStar

/-- Embed one beta+iota+eta step into `betaEtaStar`. -/
theorem single {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (singleStep : Step.betaEta sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm :=
  Step.betaEtaStar.trans singleStep (Step.betaEtaStar.refl _)

/-- Embed a beta+iota `Step` into the beta+eta closure. -/
theorem ofStep {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (singleStep : Step sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm :=
  single (Or.inl singleStep)

/-- Embed a raw eta step into the beta+eta closure. -/
theorem ofEta {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (etaStep : Step.eta sourceTerm targetTerm) :
    Step.betaEtaStar sourceTerm targetTerm :=
  single (Or.inr etaStep)

/-- Compose two beta+eta-star chains. -/
theorem trans_compose {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    (firstChain : Step.betaEtaStar firstTerm secondTerm)
    (secondChain : Step.betaEtaStar secondTerm thirdTerm) :
    Step.betaEtaStar firstTerm thirdTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans headStep _ tailIH =>
      exact Step.betaEtaStar.trans headStep (tailIH secondChain)

end betaEtaStar

end Step

end FX1Poly.Core
