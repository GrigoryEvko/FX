import FX1Poly.Core.StepEta
import FX1Poly.Core.GeneratorRedexHeadSoundness
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Core/EtaRootClassifier — the η-root operational classifier + βη-inertness soundness (HON-15)

`GeneratorRedexHead.hasRedexHead` (HON-2) classifies the β/ι redex heads, and `GeneratorRedexHeadSoundness`
(HON-6) proves its soundness: a generator the β/ι classifier rejects sources no root β/ι redex.  But HON-6's own
docstring flags the gap — the kernel ALSO has η (the `Step.eta` sibling inductive), and the β/ι classifier is
silent about it: `hasRedexHead gen_lam = false`, yet `lam (app (weaken f) var0)` η-contracts to `f`.  So the
operational classifier was NOT honest about the full βη calculus.  This file closes that gap — "the one missing
brick for total operational inertness."

The five η-source SHAPES (`RawTerm.etaXxxSource`, `StepEta.lean`) are headed by exactly five generators:
`gen_lam` / `gen_pair` / `gen_pathLam` / `gen_modIntro` / `gen_glueIntro`.  Crucially `Step.eta` is ROOT-ONLY (its
five constructors are the five η-rules, with no congruence arm), so "the head is not an η-source head ⟹ no root
η step" is an exact, unconditional statement — unlike the β/ι side, where `Step` has congruence arms and HON-6
can only claim the root-SOURCE detector is false.

  * **`Generator.hasEtaSourceHead`** — the five η-source heads, a `decide`-disjunction (HON-2's style).
  * **`Generator.hasRedexHeadBetaEta`** — `hasRedexHead || hasEtaSourceHead`: the honest βη operational classifier.
  * **`RawTerm.hasRootEtaSource`** — the term-level (conservative, head-driven) η-root detector + five
    completeness witnesses `hasRootEtaSource (etaXxxSource s) = true` (every η-source is detected).
  * **`hasRootEtaSource_false_imp_no_root_eta`** (★) — the η-inertness soundness: a term the detector rejects
    fires NO root η step.  `Step.eta` is root-only, so this is `cases step <;> Bool.noConfusion` — each arm fixes
    the subject to an `etaXxxSource`, whose head computes the detector to `true`, contradicting the `false`.
  * **`hasRedexHeadBetaEta_false_imp_betaEta_inert`** (★) — the combined βη operational-inertness soundness: a
    βη-classifier-rejected head sources no root β/ι redex (HON-6) AND fires no root η step (the above).  This is
    HON-6 extended to the full `Step.betaEta = Step ∨ Step.eta` union.
  * **`lam_etaLive_betaInert`** — the honest gain made explicit: `gen_lam` has `hasRedexHead = false` (β/ι-inert)
    yet `hasRedexHeadBetaEta = true` (η-live), the η-source head the β/ι classifier silently missed.

## Zero-axiom

`hasRootEtaSource_false_imp_no_root_eta` is `cases` on the root-only `Step.eta` + `Bool.noConfusion` (each
η-source head computes `hasEtaSourceHead = true` by `rfl`); the combined theorem splits
`(hasRedexHead || hasEtaSourceHead) = false` by `cases` on `hasRedexHead` (propext-free, never
`Bool.or_eq_false_iff`) and feeds HON-6 + the η lemma; witnesses are `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **The five η-source heads.**  `lam` / `pair` / `pathLam` / `modIntro` / `glueIntro` head the five raw
η-source shapes (`RawTerm.etaXxxSource`).  A `decide`-disjunction, mirroring `Generator.hasRedexHead`. -/
def Generator.hasEtaSourceHead (g : Generator) : Bool :=
  decide (g = .gen_lam) || decide (g = .gen_pair) || decide (g = .gen_pathLam)
  || decide (g = .gen_modIntro) || decide (g = .gen_glueIntro)

/-- **The βη operational classifier.**  A generator is operationally live under β+ι+η iff it heads a β/ι redex
(`hasRedexHead`, HON-2) OR an η source (`hasEtaSourceHead`).  The honest extension of HON-2 to the full calculus. -/
def Generator.hasRedexHeadBetaEta (g : Generator) : Bool :=
  g.hasRedexHead || g.hasEtaSourceHead

/-- **Term-level η-root detector** (conservative, head-driven): the head is an η-source head.  Complete (every
`etaXxxSource` is detected, below) and sound for inertness (`hasRootEtaSource_false_imp_no_root_eta`). -/
def RawTerm.hasRootEtaSource {scope : Nat} (term : RawTerm scope) : Bool :=
  term.rootGenerator.hasEtaSourceHead

/-! ## LIVE / RESERVED classifier witnesses -/

/-- Function η-source head. -/
theorem hasEtaSourceHead_lam : Generator.gen_lam.hasEtaSourceHead = true := rfl
/-- Pair η-source head. -/
theorem hasEtaSourceHead_pair : Generator.gen_pair.hasEtaSourceHead = true := rfl
/-- Cubical-path η-source head. -/
theorem hasEtaSourceHead_pathLam : Generator.gen_pathLam.hasEtaSourceHead = true := rfl
/-- Modal η-source head. -/
theorem hasEtaSourceHead_modIntro : Generator.gen_modIntro.hasEtaSourceHead = true := rfl
/-- Glue η-source head. -/
theorem hasEtaSourceHead_glueIntro : Generator.gen_glueIntro.hasEtaSourceHead = true := rfl
/-- A genuinely reserved head is no η source. -/
theorem hasEtaSourceHead_hilbertSpace : Generator.gen_hilbertSpace.hasEtaSourceHead = false := rfl
/-- The β-application head is no η source (it is a β-redex head, the other axis). -/
theorem hasEtaSourceHead_app : Generator.gen_app.hasEtaSourceHead = false := rfl

/-- **★ The honest gain: `lam` is η-LIVE though β-INERT.**  `hasRedexHead gen_lam = false` (the β/ι classifier
correctly rejects it — `app(lam, _)` reduces, headed by `gen_app`, not `lam`), yet `hasRedexHeadBetaEta gen_lam =
true` because `lam (app (weaken f) var0)` is an η redex.  The η axis catches exactly what the β/ι classifier
silently missed — the operational classifier is now truthful about the full βη calculus. -/
theorem lam_etaLive_betaInert :
    Generator.gen_lam.hasRedexHead = false ∧ Generator.gen_lam.hasRedexHeadBetaEta = true := ⟨rfl, rfl⟩

/-! ## completeness — every η-source is detected -/

theorem hasRootEtaSource_etaLamSource {scope : Nat} (domainAnn innerFunction : RawTerm scope) :
    (RawTerm.etaLamSource domainAnn innerFunction).hasRootEtaSource = true := rfl
theorem hasRootEtaSource_etaPairSource {scope : Nat} (pairTerm : RawTerm scope) :
    (RawTerm.etaPairSource pairTerm).hasRootEtaSource = true := rfl
theorem hasRootEtaSource_etaPathLamSource {scope : Nat} (innerPath : RawTerm scope) :
    (RawTerm.etaPathLamSource innerPath).hasRootEtaSource = true := rfl
theorem hasRootEtaSource_etaModIntroSource {scope : Nat} (modalTerm : RawTerm scope) :
    (RawTerm.etaModIntroSource modalTerm).hasRootEtaSource = true := rfl
theorem hasRootEtaSource_etaGlueIntroSource {scope : Nat} (gluedTerm : RawTerm scope) :
    (RawTerm.etaGlueIntroSource gluedTerm).hasRootEtaSource = true := rfl

/-! ## η-inertness soundness — Step.eta is root-only -/

/-- **★ A term the η-root detector rejects fires NO root η step.**  `Step.eta` has only the five root η-rules (no
congruence arm), so a `cases` on the step fixes the subject to one of the five `etaXxxSource` shapes — each with
an η-source head, so the detector computes `true`, contradicting the `false` hypothesis.  Exact and unconditional
(contrast the β/ι side, where congruence forces HON-6 to claim only root-SOURCE falsity). -/
theorem hasRootEtaSource_false_imp_no_root_eta {scope : Nat} {subject reduct : RawTerm scope}
    (reserved : subject.hasRootEtaSource = false) (step : Step.eta subject reduct) : False := by
  cases step <;> exact Bool.noConfusion reserved

/-! ## combined βη operational-inertness soundness -/

/-- **★ Total operational inertness over β+ι+η.**  A generator the βη classifier rejects sources no root β/ι
redex (HON-6's `hasRedexHead_false_imp_no_root_redex`) AND fires no root η step (the above).  Splitting
`(hasRedexHead || hasEtaSourceHead) = false` into both `false` is propext-free `cases` on `hasRedexHead`.  This is
HON-6 extended to the full `Step.betaEta = Step ∨ Step.eta` union — the honest "βη-reserved ⟹ operationally
inert" statement. -/
theorem hasRedexHeadBetaEta_false_imp_betaEta_inert {scope : Nat} {g : Generator}
    (reserved : g.hasRedexHeadBetaEta = false)
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.hasRootStepSource (.mkGen g payload children) = false
      ∧ ∀ {reduct : RawTerm scope}, ¬ Step.eta (.mkGen g payload children) reduct := by
  have betaFalse : g.hasRedexHead = false := by
    cases headBranch : g.hasRedexHead with
    | false => rfl
    | true => rw [Generator.hasRedexHeadBetaEta, headBranch] at reserved; exact Bool.noConfusion reserved
  have etaFalse : g.hasEtaSourceHead = false := by
    cases headBranch : g.hasRedexHead with
    | false => rw [Generator.hasRedexHeadBetaEta, headBranch, Bool.false_or] at reserved; exact reserved
    | true => rw [Generator.hasRedexHeadBetaEta, headBranch] at reserved; exact Bool.noConfusion reserved
  refine ⟨hasRedexHead_false_imp_no_root_redex betaFalse payload children, ?_⟩
  intro reduct step
  exact hasRootEtaSource_false_imp_no_root_eta
    (subject := RawTerm.mkGen g payload children) etaFalse step

end FX1Poly.Core
