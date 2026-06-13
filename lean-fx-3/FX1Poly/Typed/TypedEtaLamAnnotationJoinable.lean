import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Core.ConvRenameReflection
import FX1Poly.Core.EtaSources
import FX1Poly.Core.EtaLamAnnotationJoinable

/-! # FX1Poly/Typed/TypedEtaLamAnnotationJoinable
    — typing supplies the weakened Nederpelt guard at a lambda eta root.

`HasTypeDescPi.etaLamSourceAnnotationJoinable`: if the eta source
`lam domainAnn (app (weaken innerFunction) newestVar)` is grown-typed and the inner function
is itself an annotated lambda, the inner and outer domain annotations are CONVERTIBLE — and
`Conv` IS `StepStar.Join`, so they are joinable, exactly the `EtaLamAnnotationJoinable` guard.

This is the typed extraction that discharges the joinability guard the native table beta-eta
Church-Rosser needs at every eta-lambda critical pair.  It is a pure composition of surviving
typed inversions (`invertLam`/`invertApp`/`invertVar`/`invertLamGeneral`), Π-injectivity
(`Conv.piTyCode_inj`), and rename reflection (`Conv.reflectWeaken`) — it references no bespoke
`Step.eta` relation.  It previously lived inside the deletable
`WfContextBetaEtaConfluenceUnconditional`; it is relocated here to a bespoke-`Step.eta`-cluster-free
home so the native confluence consumes it without keeping the bespoke cluster alive.

## Zero-axiom verification

A composition of shipped zero-axiom bricks (typed inversions, Π-injectivity, rename
reflection); no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Typed annotation joinability at a lambda eta root.**  If the eta source
`lam domainAnn (app (weaken innerFunction) newestVar)` is grown-typed and the inner function
is itself an annotated lambda, the inner and outer annotations are CONVERTIBLE — and `Conv`
is `StepStar.Join`, so they are joinable: exactly the weakened Nederpelt guard. -/
theorem HasTypeDescPi.etaLamSourceAnnotationJoinable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn innerFunction classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaLamSource domainAnn innerFunction) classifier) :
    BetaEtaPairJoin.EtaLamAnnotationJoinable domainAnn innerFunction := by
  intro innerDomainAnn innerBody innerFunctionEq
  have lamTyped : HasTypeDescPi profile context
      (lamCell domainAnn
        (appCell (RawTerm.weaken innerFunction) RawTerm.newestVar)) classifier := typed
  obtain ⟨bodyClassifier, _domainLevel, _codomainLevel, _flag, _convToPi, _domainTyped,
      _bodyClassifierTyped, bodyTyped⟩ := HasTypeDescPi.invertLam lamTyped
  obtain ⟨innerDomain, innerCodomain, weakenedFunctionTyped, argumentTyped,
      _bodyClassifierConv⟩ := HasTypeDescPi.invertApp bodyTyped
  -- the application argument is the newest variable: its domain pins to the WEAKENED outer
  -- annotation (the cons-lookup at zero is definitionally `weaken domainAnn`)
  have innerDomainToWeakenedOuter :
      Conv innerDomain (RawTerm.rename RawRenaming.weaken domainAnn) :=
    HasTypeDescPi.invertVar argumentTyped
  -- the inner function is a lambda, so its weakening is a lambda with the WEAKENED inner
  -- annotation; inverting that typing pins the same domain through the Π classifier
  subst innerFunctionEq
  obtain ⟨_weakenedCodomain, _dLevel, _cLevel, _uFlag, weakenedPiConv, _wDomainTyped,
      _wCodomainTyped, _wBodyTyped⟩ :=
    HasTypeDescPi.invertLamGeneral weakenedFunctionTyped
      (rename_lamCell RawRenaming.weaken innerDomainAnn innerBody)
  obtain ⟨domainsConv, _codomainsConv⟩ := Conv.piTyCode_inj weakenedPiConv
  -- align the two pins and strip the shared weakening
  have weakenedAnnotationsConv :
      Conv (RawTerm.rename RawRenaming.weaken innerDomainAnn)
        (RawTerm.rename RawRenaming.weaken domainAnn) :=
    Conv.trans domainsConv.sym innerDomainToWeakenedOuter
  exact Conv.reflectWeaken weakenedAnnotationsConv

end FX1Poly.Typed
