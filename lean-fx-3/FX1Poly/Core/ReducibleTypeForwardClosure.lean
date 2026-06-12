import FX1Poly.Core.ReducibleType
import FX1Poly.Core.ReducibleTypeInversion
import FX1Poly.Core.WeakHeadStepCommute
import FX1Poly.Core.WeakHeadStepNormalForms
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StepTable

/-! # Foundation/PolyCell/Core/ReducibleTypeForwardClosure
    — reduction stability of the dependent reducibility relation (foundations)

The conversion-invariance of `ReducibleType` (the prize the commutation diamond `WeakHeadStepCommute`
was built for) factors through FORWARD CLOSURE: a reducible type stays reducible at the SAME candidate as
it reduces.  Along a single weak-head step that is immediate — `reductReducibleThroughWeakHeadStep`
(`ReducibleTypeInversion`) already gives `ReducibleType typeCode candidate → WeakHeadStep typeCode reduct
→ ReducibleType reduct candidate` by determinism.  Along an ARBITRARY step the three arms behave
differently — the `whnfExpand` arm pushes the step past the weak-head redex (the commutation diamond),
the `piType` arm decomposes a Π-code step into domain/codomain steps, and the `neutral` arm needs that a
weak-head-NORMAL non-Π type stays weak-head-normal non-Π under reduction.

This file ships the reduction-substrate FACTS the arbitrary-step closure consumes, each a complete,
standalone, reusable theorem:

  * `Step.rootGenerator_eq_of_weakHeadNormal` — a step out of a weak-head-NORMAL term is a congruence,
    hence preserves the root generator.  (A root β / root ι step would be a `WeakHeadStep`, contradicting
    weak-head normality; only the uniform `cong` rule remains, and it keeps the generator.)  This is the
    `neutral` arm's engine: it keeps `root ≠ piTyCode` stable, and — composed with weak-head-normality
    preservation — keeps the whole `neutral` classification stable.

  * `StepStar.subst0Body` — replay a body `StepStar` chain through `subst0` with a fixed argument (the
    chain lift of `Step.subst0Body`).  The `piType` arm needs it: a codomain reduction `codomain ↠
    codomain'` induces `subst0 codomain argument ↠ subst0 codomain' argument`, which re-interprets the
    codomain candidate at the reduced code.

## Zero-axiom verification

`rootGenerator_eq_of_weakHeadNormal` is `cases` on the TABLE image of the step (the IOTA-T1 adequacy):
a root firing of any legacy row is a weak-head redex (`legacyRootFiringToWeakHeadStep`), refuted by the
weak-head-normality hypothesis; the uniform `cong` constructor keeps the generator (`rfl` on
`rootGenerator`).  TWO arms where the bespoke proof had eighteen.
`StepStar.subst0Body` is induction on the chain composing `Step.subst0Body` links by `trans_compose`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration
by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **A step out of a weak-head-normal term preserves the root generator.**  If `subjectType` has no
weak-head step, any `Step subjectType reductType` is the uniform congruence rule (a root β or root ι step
would itself be a `WeakHeadStep`), so `reductType` keeps `subjectType`'s root generator. -/
theorem Step.rootGenerator_eq_of_weakHeadNormal {scope : Nat} {subjectType reductType : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep subjectType reduct)
    (step : Step subjectType reductType) :
    reductType.rootGenerator = subjectType.rootGenerator := by
  cases stepOverLegacyTable_iff_step.mpr step with
  | cong generator payload childStep => rfl
  | tableRedex isRow elimPayload fires =>
      exact absurd (legacyRootFiringToWeakHeadStep isRow elimPayload fires)
        (weakHeadNormal _)

/-- **Replay a body `StepStar` chain through `subst0`.**  A codomain reduction `body ↠ updatedBody`
induces `subst0 body argument ↠ subst0 updatedBody argument` (fixed argument): the chain lift of
`Step.subst0Body`, composing one substituted link per source step.  The `piType` arm of forward closure
re-interprets the codomain candidate at the reduced code through this. -/
theorem StepStar.subst0Body {scope : Nat} (argument : RawTerm scope)
    {body updatedBody : RawTerm (scope + 1)} (bodyChain : StepStar body updatedBody) :
    StepStar (RawTerm.subst0 body argument) (RawTerm.subst0 updatedBody argument) := by
  induction bodyChain with
  | refl _ => exact StepStar.refl _
  | trans headStep _restChain restStepStar =>
      exact StepStar.trans_compose (Step.subst0Body argument headStep) restStepStar

/-- Auxiliary for `StepStar.piTyCode_decompose`: the start carried as an equation so the chain induction's
hypothesis applies to each reduced Π-code along the way. -/
theorem StepStar.piTyCode_decompose_through {scope : Nat} :
    ∀ {startType target : RawTerm scope}, StepStar startType target →
      ∀ {domain : RawTerm scope} {codomain : RawTerm (scope + 1)},
        startType = .mkGen .gen_piTyCode () (.childCons domain (.childCons codomain .childNil)) →
        ∃ (updatedDomain : RawTerm scope) (updatedCodomain : RawTerm (scope + 1)),
          target = .mkGen .gen_piTyCode ()
            (.childCons updatedDomain (.childCons updatedCodomain .childNil)) ∧
          StepStar domain updatedDomain ∧ StepStar codomain updatedCodomain := by
  intro startType target chain
  induction chain with
  | refl _ =>
      intro domain codomain startEquation
      exact ⟨domain, codomain, startEquation, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _restChain restDecompose =>
      intro domain codomain startEquation
      subst startEquation
      rcases Step.from_piTyCode headStep with
        ⟨_domainAfter, midEquation, domainStep⟩ | ⟨_codomainAfter, midEquation, codomainStep⟩
      · obtain ⟨updatedDomain, updatedCodomain, targetEquation, domainChain, codomainChain⟩ :=
          restDecompose midEquation
        exact ⟨updatedDomain, updatedCodomain, targetEquation,
          StepStar.trans domainStep domainChain, codomainChain⟩
      · obtain ⟨updatedDomain, updatedCodomain, targetEquation, domainChain, codomainChain⟩ :=
          restDecompose midEquation
        exact ⟨updatedDomain, updatedCodomain, targetEquation, domainChain,
          StepStar.trans codomainStep codomainChain⟩

/-- **A Π-code's reduction is a Π-code with reduced children.**  Reduction out of a `gen_piTyCode`-rooted
type stays `gen_piTyCode`-rooted (the former has no root redex), decomposing into a domain `StepStar` and a
codomain `StepStar`.  The `piType` arm of forward closure consumes this: it re-interprets the domain and
(via `StepStar.subst0Body`) the codomain candidate at the reduced children, then rebuilds `piType`. -/
theorem StepStar.piTyCode_decompose {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} {target : RawTerm scope}
    (chain : StepStar
      (.mkGen .gen_piTyCode () (.childCons domain (.childCons codomain .childNil))) target) :
    ∃ (updatedDomain : RawTerm scope) (updatedCodomain : RawTerm (scope + 1)),
      target = .mkGen .gen_piTyCode ()
        (.childCons updatedDomain (.childCons updatedCodomain .childNil)) ∧
      StepStar domain updatedDomain ∧ StepStar codomain updatedCodomain :=
  StepStar.piTyCode_decompose_through chain rfl

/-- **Reduction dichotomy.**  Every `Step` out of a term is EITHER a root reduction (β / ι), exposing a
weak-head step on the SOURCE, OR the uniform congruence rule (the source and reduct share generator and
payload, their child spines related by a `StepChildren`).  This is the inversion the weak-head-normality
preservation proof rests on: a step that does not expose a source weak-head step must be a congruence,
which preserves the root and confines the change to one child — so weak-head-normality of the parent
descends to a weak-head-normality obligation on the stepped child. -/
theorem Step.weakHeadStep_or_cong {scope : Nat} {subjectType reductType : RawTerm scope}
    (step : Step subjectType reductType) :
    (∃ reduct : RawTerm scope, WeakHeadStep subjectType reduct) ∨
    (∃ (generator : Generator) (payload : generator.payload scope)
        (children childrenAfter : RawTermChildren generator.binderShifts scope),
      subjectType = .mkGen generator payload children ∧
      reductType = .mkGen generator payload childrenAfter ∧
      StepChildren children childrenAfter) := by
  cases step with
  | beta => exact Or.inl ⟨_, WeakHeadStep.beta⟩
  | cong generator payload childStep =>
      exact Or.inr ⟨generator, payload, _, _, rfl, rfl, childStep⟩
  | iotaBoolTrue => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolTrue⟩
  | iotaBoolFalse => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolFalse⟩
  | iotaFstPair => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaFstPair⟩
  | iotaSndPair => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaSndPair⟩
  | iotaNatElimZero => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimZero⟩
  | iotaNatRecZero => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecZero⟩
  | iotaListElimNil => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimNil⟩
  | iotaOptionMatchNone => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchNone⟩
  | iotaOptionMatchSome => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
  | iotaEitherMatchInl => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
  | iotaEitherMatchInr => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
  | iotaNatElimSucc => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
  | iotaNatRecSucc => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
  | iotaListElimCons => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
  | iotaIdJRefl => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl⟩
  | iotaIdStrictRecRefl => exact Or.inl ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl⟩

end FX1Poly.Core
