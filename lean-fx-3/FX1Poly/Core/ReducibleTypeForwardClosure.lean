import FX1Poly.Core.ReducibleType
import FX1Poly.Core.ReducibleTypeInversion
import FX1Poly.Core.WeakHeadStepCommute
import FX1Poly.Core.WeakHeadStepNormalForms
import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst

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

`rootGenerator_eq_of_weakHeadNormal` is `cases` on the step: the β and sixteen ι constructors each expose
a weak-head redex, refuted by the weak-head-normality hypothesis via `WeakHeadStep.beta` /
`WeakHeadStep.rootIota`; the uniform `cong` constructor keeps the generator (`rfl` on `rootGenerator`).
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
  cases step with
  | cong _generator _payload _childStep => rfl
  | beta => exact absurd WeakHeadStep.beta (weakHeadNormal _)
  | iotaBoolTrue => exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaBoolTrue) (weakHeadNormal _)
  | iotaBoolFalse => exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaBoolFalse) (weakHeadNormal _)
  | iotaFstPair => exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaFstPair) (weakHeadNormal _)
  | iotaSndPair => exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaSndPair) (weakHeadNormal _)
  | iotaNatElimZero =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaNatElimZero) (weakHeadNormal _)
  | iotaNatRecZero =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaNatRecZero) (weakHeadNormal _)
  | iotaListElimNil =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaListElimNil) (weakHeadNormal _)
  | iotaOptionMatchNone =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchNone) (weakHeadNormal _)
  | iotaOptionMatchSome =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome) (weakHeadNormal _)
  | iotaEitherMatchInl =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl) (weakHeadNormal _)
  | iotaEitherMatchInr =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr) (weakHeadNormal _)
  | iotaNatElimSucc =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc) (weakHeadNormal _)
  | iotaNatRecSucc =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc) (weakHeadNormal _)
  | iotaListElimCons =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons) (weakHeadNormal _)
  | iotaIdJRefl => exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl) (weakHeadNormal _)
  | iotaIdStrictRecRefl =>
      exact absurd (WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl) (weakHeadNormal _)

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

end FX1Poly.Core
