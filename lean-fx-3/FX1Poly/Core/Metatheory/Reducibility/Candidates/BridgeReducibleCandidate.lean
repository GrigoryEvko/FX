import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Canonicity.BridgeCanonicalFormsCandidate
import FX1Poly.Core.Substrate.Neutral.NeutralStepClosure

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

end FX1Poly.Core
