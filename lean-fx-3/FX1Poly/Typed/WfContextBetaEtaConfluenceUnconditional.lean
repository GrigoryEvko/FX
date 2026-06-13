import FX1Poly.Typed.GrownEtaSubjectReduction
import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.WfContextBetaEtaConfluence
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc
import FX1Poly.Core.StepBetaEtaJoinableConfluence
import FX1Poly.Core.ConvRenameReflection
import FX1Poly.Typed.TypedEtaLamAnnotationJoinable

/-! # FX1Poly/Typed/WfContextBetaEtaConfluenceUnconditional
    — ★ UNCONDITIONAL typed βη Church-Rosser: the Nederpelt guard is FREE for well-typed subjects

`WfContextBetaEtaConfluence` ships the Geuvers βη-CR + unique-βη-NF theorems CONDITIONAL on
`HereditaryLamDiagonal` — the syntactic annotation-EQUALITY guard at every reachable lambda
eta root.  Its own docstring names the two missing ingredients for the unconditional claim:
(a) a Conv/joinability-guarded variant of the local join, and (b) βη subject reduction on the
grown engine.  Both are now shipped — (a) is `StepBetaEtaJoinableConfluence` (the
`EtaLamAnnotationJoinable` guard + Newman twin), (b) is
`HasTypeDescPi.subjectReductionBetaEtaStar` — and this file fires them:

  1. `etaLamSourceAnnotationJoinable` — a TYPED lambda eta source whose inner function is
     itself a lambda has JOINABLE annotations: `invertLam` exposes the body's application
     typing, `invertApp` + `invertVar` pin the application domain to the WEAKENED outer
     annotation, a second `invertLam` on the weakened inner lambda pins the same domain to
     the WEAKENED inner annotation through the Π classifier, `Conv.piTyCode_inj` aligns the
     two pins, and `Conv.reflectWeaken` strips the shared weakening.  `Conv` IS
     `StepStar.Join`, so the conversion is LITERALLY the joinability witness.
  2. `hereditaryLamJoinableOfTyped` — βη-SR-star keeps every βη-reachable reduct typed at
     the same classifier, so the guard discharges HEREDITARILY.
  3. ★ `subjectBetaEtaConfluenceTypedUnconditional` /
     ★ `uniqueBetaEtaNormalFormTypedUnconditional` — the Geuvers theorems with the
     `hereditaryDiagonal` premise GONE: well-typedness in a well-formed context is the only
     hypothesis.  This is Geuvers' LICS '92 "CR for βη on well-typed terms" in its full
     unconditional form for the FX grown engine.

The conditional pair in `WfContextBetaEtaConfluence` remains valid (and is now subsumed on
typed subjects); the raw-layer non-joinability (`NederpeltNonJoinability`) is untouched —
typing is exactly what buys the guard.

## Zero-axiom verification

Compositions of shipped zero-axiom bricks (inversions, Π-injectivity, rename reflection,
βη-SR, βη-SN, the joinable Newman bridge).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/- `HasTypeDescPi.etaLamSourceAnnotationJoinable` (the typed annotation-joinability extraction
at a lambda eta root) is relocated to the bespoke-`Step.eta`-cluster-free home
`FX1Poly/Typed/TypedEtaLamAnnotationJoinable.lean` so the native table beta-eta confluence
consumes it without keeping the bespoke cluster alive; it is imported above. -/

/-- Every grown-typed term satisfies the joinability guard at its own root: if it IS a
lambda eta source with a lambda-shaped inner function, the annotations join. -/
theorem HasTypeDescPi.lamJoinableGuardOfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.LamJoinableGuard subject := by
  intro domainAnn innerFunction subjectEq
  exact HasTypeDescPi.etaLamSourceAnnotationJoinable (subjectEq ▸ typed)

/-- **Hereditary guard discharge via βη subject reduction**: every βη-reachable reduct of a
grown-typed subject in a well-formed context stays typed at the same classifier
(`subjectReductionBetaEtaStar`), hence satisfies the joinability guard. -/
theorem HasTypeDescPi.hereditaryLamJoinableOfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.HereditaryLamJoinable subject := by
  intro reachedTerm reachChain
  exact HasTypeDescPi.lamJoinableGuardOfTyped
    (HasTypeDescPi.subjectReductionBetaEtaStar wellFormed typed reachChain)

/-- ★ **UNCONDITIONAL typed βη Church-Rosser** — the Geuvers theorem with no syntactic
guard: any two βη-reducts of a well-typed subject in a well-formed context join.  The
βη-SN witness supplies accessibility; βη-SR + the typed annotation extraction discharge
the hereditary joinability guard the Newman bridge consumes. -/
theorem HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject leftReduct)
    (subjectToRight : Step.betaEtaStar subject rightReduct) :
    Step.betaEtaStar.Join leftReduct rightReduct :=
  Step.betaEtaStar.confluence_of_localJoin_and_accessibleJoinable
    (HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc contextWellFormed typed)
    (HasTypeDescPi.hereditaryLamJoinableOfTyped
      (WfContextDescPi.ofWfContextDesc contextWellFormed) typed)
    subjectToLeft subjectToRight

/-- ★ **UNCONDITIONAL unique βη-normal-forms** — a well-typed subject in a well-formed
context has at most one βη-normal-form, with no guard premise. -/
theorem HasTypeDescPi.uniqueBetaEtaNormalFormTypedUnconditional {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {normalFormLeft normalFormRight : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject normalFormLeft)
    (leftNoStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormLeft reduct)
    (subjectToRight : Step.betaEtaStar subject normalFormRight)
    (rightNoStep : ∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormRight reduct) :
    normalFormLeft = normalFormRight := by
  obtain ⟨apex, leftToApex, rightToApex⟩ :=
    HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional contextWellFormed typed
      subjectToLeft subjectToRight
  have leftEqApex : normalFormLeft = apex :=
    Step.betaEtaStar.eq_of_noBetaEtaStep leftNoStep leftToApex
  have rightEqApex : normalFormRight = apex :=
    Step.betaEtaStar.eq_of_noBetaEtaStep rightNoStep rightToApex
  exact leftEqApex.trans rightEqApex.symm

end FX1Poly.Typed
