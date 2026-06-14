import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiLamInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiAppInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiVarInversion
import FX1Poly.Typed.Ledger.Misc.ConvCodeInjectivity
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiWeakening
import FX1Poly.Core.Rewriting.Conversion.ConvRenameReflection
import FX1Poly.Core.Equality.Eta.EtaSources
import FX1Poly.Core.Equality.Eta.EtaLamAnnotationJoinable
import FX1Poly.Core.Rewriting.Reduction.Step.StepLamDomainCong
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable
import FX1Poly.Typed.Metatheory.SubjectReduction.TableBetaEtaRootSubjectReduction

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

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

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

/-- A reflexive-transitive iota table chain lifts into the table
beta-eta-root union closure by the left injection.  A local twin of
`reflTransClosureStepTableToUnion` (cross-quadrant file), inlined here
so this annotation-clash join needs only the lightweight
`StepTableBetaEtaRoot` definition, not the heavy guarded-confluence
chain. -/
theorem reflTransClosureStepTableIntoUnion {scope : Nat}
    {source target : RawTerm scope}
    (chain : ReflTransClosure
      (fun left right : RawTerm scope => StepTable left right) source target) :
    ReflTransClosure StepTableBetaEtaRoot source target := by
  induction chain with
  | refl point => exact .refl point
  | head firstStep _restChain liftedRest =>
      exact .head (Or.inl firstStep) liftedRest

/-- **★ The table-native Nederpelt diagonal join.**

The annotation-clash critical pair at a lambda eta peak, phrased over
the canonical table beta-eta-root union (`StepTableBetaEtaRoot`) instead
of the bespoke `Step.eta.etaLam` join `BetaEtaPairJoin.etaLamBodyBeta`.

At a function-eta peak the LEFT branch (inner root-beta) reaches
`lam domainAnn innerBody` while the RIGHT branch (the `etaLamRow`
contraction) reaches `lam innerDomainAnn innerBody`; under Church-style
annotations the two domain annotations need NOT agree (the Nederpelt
clash, raw-non-joinable).  Given the joinability witness
`StepStar.Join innerDomainAnn domainAnn` — exactly what
`HasTypeDescPi.etaLamSourceAnnotationJoinable` supplies from typing — the
two lambda reducts join over `StepTableBetaEtaRoot` at
`lam commonAnn innerBody`: each domain annotation reaches the common
`commonAnn` by replaying the joinability chain through the lambda's
domain child (`StepStar.lamDomainCong`), lifted across the iota-table
adequacy (`StepStar.toTableClosure`) into the union's left injection.

This is the additive table-native equivalent of the raw bespoke diagonal
that the typed capstone `childJoinLam` (agent D's file) can consume for
its root-beta arm in place of the inline annotation replay, so the
bespoke `Step.eta.etaLam`-keyed diagonal in `StepEtaCriticalPairs` can be
terminally deleted.

Proven entirely over the table relation; no bespoke `Step.eta` is ever
built. -/
theorem etaLamAnnotationClashJoinsOverTable {scope : Nat}
    {domainAnn innerDomainAnn : RawTerm scope}
    {innerBody : RawTerm (scope + 1)}
    (annotationJoin :
      StepStar.Join innerDomainAnn domainAnn) :
    Joinable StepTableBetaEtaRoot
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainAnn (.childCons innerBody .childNil)))
      (RawTerm.mkGen .gen_lam ()
        (.childCons innerDomainAnn (.childCons innerBody .childNil))) := by
  obtain ⟨commonAnn, innerToCommon, outerToCommon⟩ := annotationJoin
  refine ⟨RawTerm.mkGen .gen_lam ()
      (.childCons commonAnn (.childCons innerBody .childNil)), ?_, ?_⟩
  · -- LEFT: `lam domainAnn innerBody` replays `domainAnn ↝* commonAnn`.
    exact reflTransClosureStepTableIntoUnion
      (StepStar.lamDomainCong innerBody outerToCommon).toTableClosure
  · -- RIGHT: `lam innerDomainAnn innerBody` replays `innerDomainAnn ↝* commonAnn`.
    exact reflTransClosureStepTableIntoUnion
      (StepStar.lamDomainCong innerBody innerToCommon).toTableClosure

end FX1Poly.Typed
