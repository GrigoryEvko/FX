import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Canonicity.BridgeCanonicalFormsCandidate
import FX1Poly.Core.Substrate.Neutral.NeutralStepClosure
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepCommute
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors

/-! # FX1Poly/Core/BridgeReducibleCandidate
    — the carrier-aware bridge (path-type) reducibility candidate, the endpoint-β residue source, zero-axiom

The bridge type `Bridge carrier left right` is the path type from `left` to `right` in `carrier`.  Its single
introduction is `pathLam body` (a path abstraction over an interval variable), and its eliminator is the
endpoint application `pathApp path arg`, which β-reduces `pathApp (pathLam body) arg ↝ body[arg]`.

`pathApp` is therefore a GENUINE β-elimination (the `app` twin), NOT a structural data eliminator: its
contractum `body[arg]` is a substitution extracted from the PATH itself (there is no separate base-case premise
the way `idJ` has one).  So the path's reducibility candidate must be CARRIER-AWARE — it must record that the
path, once it reaches a `pathLam body`, sends every interval point into the carrier candidate.  This is the
exact bridge analogue of the `DependentArrowCandidate` (the Π/`app` residue source), and it is what the
`pathApp` elim-FT row extracts to discharge the `contractumMemberIfReachesPathLam` residue that
`pathAppMemberAtBounded` / the Core `pathAppDependentReducibleMember` consume.

**Why this is FULLY reachable (no conversion-invariance wall).**  `DependentArrowCandidate`'s CR3 is the
localized conversion-invariance wall (`ReducibleTypeArrowCandidate`): it needs the codomain candidate stable
under ARGUMENT reduction, which the kernel does not yet supply for a DEPENDENT codomain.  The bridge carrier in
this kernel is NON-DEPENDENT (a constant `carrierCode`, per `pathAppElimRule.outputType`), so the carrier
candidate does NOT depend on the interval point — the wall vanishes, and CR1/CR2/CR3 all hold.  CR3's residue
conjunct is vacuous for a neutral path: a neutral term stays neutral along every reduction
(`IsNeutral.closedUnderStepStar`), and `pathLam` is a constructor (`pathLamValueCell_not_neutral`), so a neutral
path can never reach `pathLam body`.

The candidate is the ENRICHED-canonical-forms shape (`dataTaitCandidate isPathLamValue` ∧ the residue), matching
`gen_bridgeCode`'s term-indexed-code reservation (`BasedReflCandidate`): the first conjunct feeds the Core
member's `pathMember`, the second IS the conditioned contractum residue.

## Zero-axiom verification

CR1 is the first conjunct's CR1; CR2 prepends the step to each residue chain; CR3 splits the first conjunct via
`dataTaitCandidate.neutralExpansion` and discharges the residue conjunct by neutral-stays-neutral.  No `funext`,
no `induction` on data.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated by the `FX1Poly.Core` namespace sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **A `pathLam` cell is not neutral.**  `gen_pathLam` is an introduction (a constructor), so it heads no
`IsNeutral` form — every `IsNeutral` constructor heads a stuck variable, application, or eliminator.  The
refutation that makes the bridge candidate's CR3 residue conjunct vacuous: combined with
`IsNeutral.closedUnderStepStar`, a neutral path can never reach a `pathLam` value. -/
theorem pathLamValueCell_not_neutral {scope : Nat} {body : RawTerm (scope + 1)}
    (neutral : IsNeutral (pathLamValueCell body)) : False := by
  cases neutral

/-- **The carrier-aware bridge (path-type) reducibility candidate.**  A path is reducible at the bridge type
over an interval candidate and a (non-dependent) carrier candidate when it is a head-expansion-closed
`dataTaitCandidate isPathLamValue` member AND, once it reaches any `pathLam body`, it sends every reducible
interval point into the carrier candidate (the endpoint-β residue, generalized over the interval argument).
The bridge analogue of `DependentArrowCandidate`; the constant carrier keeps it conversion-invariance-free. -/
def bridgeReducibleCandidate {scope : Nat}
    (intervalCandidate carrierCandidate : RawTerm scope → Prop)
    (path : RawTerm scope) : Prop :=
  dataTaitCandidate isPathLamValue path ∧
    ∀ body : RawTerm (scope + 1), StepStar path (pathLamValueCell body) →
      ∀ argument : RawTerm scope, intervalCandidate argument →
        carrierCandidate (RawTerm.subst0 body argument)

/-- **CR1: a bridge-candidate member is strongly normalizing** — the first conjunct's CR1. -/
theorem bridgeReducibleCandidate.stronglyNormalizing {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} {path : RawTerm scope}
    (member : bridgeReducibleCandidate intervalCandidate carrierCandidate path) :
    IsStronglyNormalizing path :=
  member.1.stronglyNormalizing

/-- **CR2: forward closure under one `Step`.**  The first conjunct is forward-closed
(`dataTaitCandidate.closedUnderStep`); the residue conjunct transfers by PREPENDING the step to each
reaches-`pathLam` chain (`StepStar.trans`). -/
theorem bridgeReducibleCandidate.closedUnderStep {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} {path reduct : RawTerm scope}
    (member : bridgeReducibleCandidate intervalCandidate carrierCandidate path)
    (step : Step path reduct) :
    bridgeReducibleCandidate intervalCandidate carrierCandidate reduct :=
  ⟨member.1.closedUnderStep step,
   fun body reductReachesPathLam argument argumentInterval =>
     member.2 body (StepStar.trans step reductReachesPathLam) argument argumentInterval⟩

/-- **CR3: neutral expansion.**  A neutral path whose every one-step reduct is a bridge-candidate member is
itself one.  The first conjunct is the data candidate's `neutralExpansion`; the residue conjunct is VACUOUS — a
neutral path stays neutral (`IsNeutral.closedUnderStepStar`) so it can never reach the `pathLam` constructor
(`pathLamValueCell_not_neutral`). -/
theorem bridgeReducibleCandidate.neutralExpansion {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} {path : RawTerm scope}
    (pathIsNeutral : IsNeutral path)
    (reductsMembers : ∀ reduct : RawTerm scope, Step path reduct →
      bridgeReducibleCandidate intervalCandidate carrierCandidate reduct) :
    bridgeReducibleCandidate intervalCandidate carrierCandidate path :=
  ⟨dataTaitCandidate.neutralExpansion pathIsNeutral
     (fun reduct step => (reductsMembers reduct step).1),
   fun _body pathReachesPathLam _argument _argumentInterval =>
     absurd (IsNeutral.closedUnderStepStar pathIsNeutral pathReachesPathLam)
       pathLamValueCell_not_neutral⟩

/-- **The carrier-aware bridge candidate IS a Girard reducibility candidate** (CR1+CR2+CR3), for every interval
and (non-dependent) carrier candidate.  The reducibility model pins the bridge type to this candidate; the
`pathApp` elim-FT row extracts its two projections. -/
theorem bridgeReducibleCandidate_isReducibilityCandidate {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} :
    IsReducibilityCandidate (bridgeReducibleCandidate intervalCandidate carrierCandidate) :=
  ⟨bridgeReducibleCandidate.stronglyNormalizing,
   bridgeReducibleCandidate.closedUnderStep,
   bridgeReducibleCandidate.neutralExpansion⟩

/-- **The path-member projection** — the first conjunct, the head-expansion-closed `dataTaitCandidate
isPathLamValue` membership the Core `pathAppDependentReducibleMember` consumes as `pathMember`. -/
theorem bridgeReducibleCandidate.pathMember {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} {path : RawTerm scope}
    (member : bridgeReducibleCandidate intervalCandidate carrierCandidate path) :
    dataTaitCandidate isPathLamValue path :=
  member.1

/-- **The endpoint-β contractum residue projection** — the second conjunct instantiated at one interval
argument: once the path reaches `pathLam body`, the contractum `body[argument]` is a carrier-candidate member.
This is exactly the `contractumMemberIfReachesPathLam` residue `pathAppMemberAtBounded` threads. -/
theorem bridgeReducibleCandidate.contractumMemberAt {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop}
    {path argument : RawTerm scope}
    (member : bridgeReducibleCandidate intervalCandidate carrierCandidate path)
    (argumentInterval : intervalCandidate argument)
    {body : RawTerm (scope + 1)} (pathReachesPathLam : StepStar path (pathLamValueCell body)) :
    carrierCandidate (RawTerm.subst0 body argument) :=
  member.2 body pathReachesPathLam argument argumentInterval

/-- **The bridge candidate is congruent in its carrier candidate.**  If two carrier candidates agree pointwise,
the bridge candidates over them agree pointwise: the `dataTaitCandidate isPathLamValue` first conjunct is shared,
and the residue conjunct transports along the carrier iff at the contractum `subst0 body argument`.  This is the
bridge analogue of `CarrierCombinator.assemble_congr`, consumed by the reducibility model's `deterministic`
`dataBridgeCarrierAware` arm to equate two bridge derivations once their carriers are equated.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`. -/
theorem bridgeReducibleCandidate_congr {scope : Nat}
    {intervalCandidate carrierCandidate1 carrierCandidate2 : RawTerm scope → Prop}
    (carrierIff : ∀ term : RawTerm scope, carrierCandidate1 term ↔ carrierCandidate2 term)
    (path : RawTerm scope) :
    bridgeReducibleCandidate intervalCandidate carrierCandidate1 path ↔
      bridgeReducibleCandidate intervalCandidate carrierCandidate2 path :=
  ⟨fun member => ⟨member.1, fun body pathReachesPathLam argument argumentInterval =>
      (carrierIff _).mp (member.2 body pathReachesPathLam argument argumentInterval)⟩,
   fun member => ⟨member.1, fun body pathReachesPathLam argument argumentInterval =>
      (carrierIff _).mpr (member.2 body pathReachesPathLam argument argumentInterval)⟩⟩

/-- **CR-bonus: the bridge candidate is head-expansion-closed.**  A spined β-redex inherits bridge
membership from its contractum.  The first conjunct is `dataTaitCandidate_headExpansionClosed`; the residue
transports through the SAME weak-head (`betaSpine`) step the redex makes to its contractum: by weak-head
postponement (`weakHeadReductReachesWeakHeadNormalForm`) the contractum reaches the EXACT `pathLam body` the
redex reaches — `pathLamValueCell` is weak-head normal (`WeakHeadStep.not_from_pathLam`) — so the contractum's
residue lands at the literal body, no reformulation needed.  This is the bridge analogue of
`DependentArrowCandidate.abstraction`'s codomain head-expansion, consumed by the Π-introduction FT arm when a
bridge type sits in codomain position.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`. -/
theorem bridgeReducibleCandidate_headExpansionClosed {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop} :
    HeadExpansionClosed (bridgeReducibleCandidate intervalCandidate carrierCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  refine ⟨dataTaitCandidate_headExpansionClosed domainAnnSN argumentSN contractumMember.1, ?_⟩
  intro reachedBody redexReachesPathLam intervalPoint intervalPointMember
  exact contractumMember.2 reachedBody
    (weakHeadReductReachesWeakHeadNormalForm WeakHeadStep.betaSpine redexReachesPathLam
      (fun _ => WeakHeadStep.not_from_pathLam))
    intervalPoint intervalPointMember

/-- **CR-bonus: member weak-head expansion.**  A strongly-normalizing path that weak-head-steps to a bridge
member is a bridge member.  The first conjunct is `dataTaitCandidate_memberWeakHeadExpansion`; the residue
transports through the SAME weak-head step by `weakHeadReductReachesWeakHeadNormalForm` (the reduct reaches the
exact `pathLam body` the source reaches, `pathLamValueCell` being weak-head normal).  Consumed by the
reducibility model's member-weak-head-expansion arm at the bridge type.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`. -/
theorem bridgeReducibleCandidate_memberWeakHeadExpansion {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop}
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : bridgeReducibleCandidate intervalCandidate carrierCandidate reduct) :
    bridgeReducibleCandidate intervalCandidate carrierCandidate source :=
  ⟨dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember.1,
   fun reachedBody sourceReachesPathLam intervalPoint intervalPointMember =>
     reductMember.2 reachedBody
       (weakHeadReductReachesWeakHeadNormalForm weakHeadStep sourceReachesPathLam
         (fun _ => WeakHeadStep.not_from_pathLam))
       intervalPoint intervalPointMember⟩

/-- **`pathLam` is injective.**  Two `pathLam` cells over equal bodies are equal terms iff their bodies are
equal — the constructor injectivity for `gen_pathLam`'s single body child.  Used by the bridge-intro member to
project a `pathLam`-targeted reduction chain back onto its body. -/
theorem pathLamValueCell_inj {scope : Nat} {body1 body2 : RawTerm (scope + 1)}
    (equal : pathLamValueCell body1 = pathLamValueCell body2) : body1 = body2 := by
  injection equal with _scopeEq _generatorEq _payloadEq childrenEq
  exact (RawTermChildren.childCons.inj childrenEq).1

/-- **Reduction from a `pathLam` stays under the `pathLam`.**  Every reduction chain out of `pathLam body`
reaches a `pathLam reachedBody` with `body ↠ reachedBody`: `gen_pathLam` is a constructor, so the only `Step`
out of it is body congruence (`Step.from_pathLam`), and a chain composes those congruences.  Carrying the start
as an equation in the conclusion makes the chain induction's hypothesis apply to each reduced cell along the
way (the `pathLam`-congruence inversion analogue of `StepStar.piTyCode_decompose_through`). -/
theorem stepStar_pathLamValueCell_inversion {scope : Nat} :
    ∀ {startTerm target : RawTerm scope}, StepStar startTerm target →
      ∀ {body : RawTerm (scope + 1)}, startTerm = pathLamValueCell body →
      ∃ reachedBody : RawTerm (scope + 1),
        target = pathLamValueCell reachedBody ∧ StepStar body reachedBody := by
  intro startTerm target chain
  induction chain with
  | refl _term =>
      intro body startEquation
      exact ⟨body, startEquation, StepStar.refl body⟩
  | trans firstStep _restChain restInductiveHypothesis =>
      intro body startEquation
      subst startEquation
      obtain ⟨bodyAfterFirst, midpointEq, bodyFirstStep⟩ := Step.from_pathLam firstStep
      obtain ⟨reachedBody, targetEq, bodyAfterToReached⟩ :=
        restInductiveHypothesis midpointEq
      exact ⟨reachedBody, targetEq, StepStar.trans bodyFirstStep bodyAfterToReached⟩

/-- **A reduction between two `pathLam` cells projects onto a body reduction.**  Specializes
`stepStar_pathLamValueCell_inversion` to a `pathLam`-headed target and discharges the cell equation by
`pathLamValueCell_inj`. -/
theorem stepStar_under_pathLamValueCell {scope : Nat} {body reachedBody : RawTerm (scope + 1)}
    (chain : StepStar (pathLamValueCell body) (pathLamValueCell reachedBody)) :
    StepStar body reachedBody := by
  obtain ⟨reached, cellEq, bodyToReached⟩ := stepStar_pathLamValueCell_inversion chain rfl
  have bodyEq : reachedBody = reached := pathLamValueCell_inj cellEq
  exact bodyEq ▸ bodyToReached

/-- **★ The bridge-introduction member: `pathLam body` lies in the carrier-aware bridge candidate.**  Given the
body is strongly normalizing and a uniform residue supplier (for every body reduct `reachedBody` and every
interval point `argument` in the interval candidate, `reachedBody[argument]` lands in the carrier candidate),
`pathLam body` is a `bridgeReducibleCandidate` member.  The first conjunct (`dataTaitCandidate isPathLamValue`)
holds because `pathLam body` is SN (`pathLam_isStronglyNormalizing_of_body`) and every reachable normal form is a
`pathLam` of a normal body (`stepStar_pathLamValueCell_inversion`, the cell's `isStepNormalFormBool` reducing to
its body's); the residue conjunct is the supplied uniform residue projected through
`stepStar_under_pathLamValueCell`.  The intro-side dual of `bridgeReducibleCandidate.contractumMemberAt` — the
`pathLam` FT row's member witness. -/
theorem bridgeReducibleCandidate_pathLamIntro {scope : Nat}
    {intervalCandidate carrierCandidate : RawTerm scope → Prop}
    {body : RawTerm (scope + 1)}
    (bodyStronglyNormalizing : IsStronglyNormalizing body)
    (residueSupplier : ∀ reachedBody : RawTerm (scope + 1), StepStar body reachedBody →
      ∀ argument : RawTerm scope, intervalCandidate argument →
        carrierCandidate (RawTerm.subst0 reachedBody argument)) :
    bridgeReducibleCandidate intervalCandidate carrierCandidate (pathLamValueCell body) := by
  refine ⟨⟨pathLam_isStronglyNormalizing_of_body bodyStronglyNormalizing, ?_⟩, ?_⟩
  · intro normalForm reaches normalFormIsNormal
    obtain ⟨reachedBody, normalFormEq, _bodyToReached⟩ := stepStar_pathLamValueCell_inversion reaches rfl
    refine Or.inl ⟨reachedBody, normalFormEq, ?_⟩
    rw [normalFormEq] at normalFormIsNormal
    have bodyNormalBool : (RawTerm.isStepNormalFormBool reachedBody && true) = true := normalFormIsNormal
    rwa [Bool.and_true] at bodyNormalBool
  · intro reachedBody pathReaches argument argumentInterval
    exact residueSupplier reachedBody (stepStar_under_pathLamValueCell pathReaches) argument
      argumentInterval

end FX1Poly.Core
