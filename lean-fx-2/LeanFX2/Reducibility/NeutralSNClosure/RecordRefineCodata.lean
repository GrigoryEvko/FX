import LeanFX2.Reducibility.NeutralSNClosure.IntervalSN

/-! # LeanFX2.Reducibility.NeutralSNClosure.RecordRefineCodata

K12.20.AJ record / K12.20.AL refinement / K12.20.AP codata SN
preservation: `recordIntro` / `recordProj_recordIntro` /
`recordProj` (raw + Term), `refineIntro` / `refineElim` /
`refineElim_refineIntro` (raw + Term), `codataUnfold` (raw +
Term).

## Root status

Layer 3 metatheory leaf.  Third slice of NeutralSNClosure. -/

namespace LeanFX2


/-- **K12.20.AJ.1 recordIntro SN preservation** — record value
introduction (currently single-field representative; multi-field
records desugar to nested pairs).  Pure unary cong over the
first-field witness. -/
theorem RawTerm.recordIntro_isStronglyNormalizing {scope : Nat}
    {firstField : RawTerm scope}
    (firstFieldIsSN : RawTerm.isStronglyNormalizing firstField) :
    RawTerm.isStronglyNormalizing (RawTerm.recordIntro firstField) := by
  induction firstFieldIsSN with
  | intro currentField _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordIntro currentField) ?_
    intro target progressStep
    obtain ⟨firstTarget, targetEq, firstStep⟩ :=
      RawStep.par.recordIntro_inv progressStep.1
    subst targetEq
    have firstDistinct :
        currentField ≠ firstTarget := fun firstEq =>
      progressStep.2 (congrArg RawTerm.recordIntro firstEq)
    exact inductiveHypothesis firstTarget
      ⟨firstStep, firstDistinct⟩

/-- Typed wrapper for single-field record introduction SN preservation. -/
theorem Term.recordIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  RawTerm.recordIntro_isStronglyNormalizing firstFieldIsSN

/-- Generic record-projection SN preservation.

Congruent reducts recurse through the record term.  A β reduct first
develops the record into a `recordIntro`; the projected field is SN by
the record-intro field inversion lemma. -/
theorem RawTerm.recordProj_isStronglyNormalizing {scope : Nat}
    {recordRaw : RawTerm scope}
    (recordIsSN : RawTerm.isStronglyNormalizing recordRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.recordProj recordRaw) := by
  induction recordIsSN with
  | intro currentRecord recordClosure recordIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj currentRecord) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨recordTarget, targetEq, recordStep⟩
      | ⟨firstTarget, targetEq, recordStep⟩
    · subst targetEq
      by_cases recordEq : currentRecord = recordTarget
      · subst recordEq
        exact (progressStep.2 rfl).elim
      · exact recordIH recordTarget ⟨recordStep, recordEq⟩
    · rw [targetEq]
      have developedRecordIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.recordIntro firstTarget) := by
        by_cases recordEq : currentRecord = RawTerm.recordIntro firstTarget
        · rw [← recordEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentRecord recordClosure
        · exact recordClosure (RawTerm.recordIntro firstTarget)
            ⟨recordStep, recordEq⟩
      exact RawTerm.recordIntro_field_isStronglyNormalizing
        developedRecordIsSN

/-- Direct M04 SN case for projection from any SN record term. -/
theorem Term.recordProj_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIsSN : Term.isStronglyNormalizing recordValue) :
    Term.isStronglyNormalizing (Term.recordProj recordValue) :=
  RawTerm.recordProj_isStronglyNormalizing recordIsSN

/-- Generic refinement-elimination SN preservation.

Congruent reducts recurse through the refined term.  A β reduct first
develops the refined term into a `refineIntro`; the extracted value is
SN by the refinement-intro value inversion lemma. -/
theorem RawTerm.refineElim_isStronglyNormalizing {scope : Nat}
    {refinedRaw : RawTerm scope}
    (refinedIsSN : RawTerm.isStronglyNormalizing refinedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.refineElim refinedRaw) := by
  induction refinedIsSN with
  | intro currentRefined refinedClosure refinedIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refineElim currentRefined) ?_
    intro target progressStep
    rcases RawStep.par.refineElim_inv progressStep.1 with
      ⟨refinedTarget, targetEq, refinedStep⟩
      | ⟨valueTarget, proofTarget, targetEq, refinedStep⟩
    · subst targetEq
      by_cases refinedEq : currentRefined = refinedTarget
      · subst refinedEq
        exact (progressStep.2 rfl).elim
      · exact refinedIH refinedTarget ⟨refinedStep, refinedEq⟩
    · rw [targetEq]
      have developedRefinedIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.refineIntro valueTarget proofTarget) := by
        by_cases refinedEq :
            currentRefined =
              RawTerm.refineIntro valueTarget proofTarget
        · rw [← refinedEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentRefined refinedClosure
        · exact refinedClosure
            (RawTerm.refineIntro valueTarget proofTarget)
            ⟨refinedStep, refinedEq⟩
      exact RawTerm.refineIntro_value_isStronglyNormalizing
        developedRefinedIsSN

/-- Direct M04 SN case for refinement elimination from any SN refined
term. -/
theorem Term.refineElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIsSN : Term.isStronglyNormalizing refinedValue) :
    Term.isStronglyNormalizing (Term.refineElim refinedValue) :=
  RawTerm.refineElim_isStronglyNormalizing refinedIsSN

/-- **K12.20.AJ.2 refineIntro SN preservation** — refinement-type
intro packs a value with a proof of its refinement predicate.
Binary cong; uses the pair-style universal-in-conclusion pattern. -/
theorem RawTerm.refineIntro_isStronglyNormalizing {scope : Nat}
    {rawValue : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing rawValue) :
    ∀ {predicateProof : RawTerm scope},
      RawTerm.isStronglyNormalizing predicateProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.refineIntro rawValue predicateProof) := by
  induction valueIsSN with
  | intro currentValue _ valueIH =>
    intro predicateProof proofIsSN
    induction proofIsSN with
    | intro currentProof proofClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.refineIntro currentValue currentProof) ?_
      intro target progressStep
      obtain ⟨valueTarget, proofTarget, targetEq,
              valueStep, proofStep⟩ :=
        RawStep.par.refineIntro_inv progressStep.1
      subst targetEq
      by_cases valueEq : currentValue = valueTarget
      · subst valueEq
        have proofDistinct :
            currentProof ≠ proofTarget := fun proofEq =>
          progressStep.2
            (congrArg (RawTerm.refineIntro currentValue) proofEq)
        exact innerIH proofTarget ⟨proofStep, proofDistinct⟩
      · have valueProgress :
            RawStep.parProgress currentValue valueTarget :=
          ⟨valueStep, valueEq⟩
        by_cases proofEq : currentProof = proofTarget
        · subst proofEq
          exact valueIH valueTarget valueProgress
            (RawTerm.isStronglyNormalizing.intro currentProof
              proofClosure)
        · exact valueIH valueTarget valueProgress
            (proofClosure proofTarget ⟨proofStep, proofEq⟩)

/-- Typed wrapper for refinement introduction SN preservation. -/
theorem Term.refineIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (valueIsSN : Term.isStronglyNormalizing baseValue)
    (proofIsSN : Term.isStronglyNormalizing predicateProof) :
    Term.isStronglyNormalizing
      (Term.refineIntro predicate baseValue predicateProof) :=
  RawTerm.refineIntro_isStronglyNormalizing valueIsSN proofIsSN

/-- **K12.20.AJ.3 codataUnfold SN preservation** — codata
corecursive unfold bundles an initial state with a transition
function.  Binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.codataUnfold_isStronglyNormalizing {scope : Nat}
    {initialState : RawTerm scope}
    (stateIsSN : RawTerm.isStronglyNormalizing initialState) :
    ∀ {transition : RawTerm scope},
      RawTerm.isStronglyNormalizing transition →
      RawTerm.isStronglyNormalizing
        (RawTerm.codataUnfold initialState transition) := by
  induction stateIsSN with
  | intro currentState _ stateIH =>
    intro transition transitionIsSN
    induction transitionIsSN with
    | intro currentTransition transitionClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.codataUnfold currentState currentTransition) ?_
      intro target progressStep
      obtain ⟨stateTarget, transitionTarget, targetEq,
              stateStep, transitionStep⟩ :=
        RawStep.par.codataUnfold_inv progressStep.1
      subst targetEq
      by_cases stateEq : currentState = stateTarget
      · subst stateEq
        have transitionDistinct :
            currentTransition ≠ transitionTarget :=
          fun transitionEq =>
            progressStep.2
              (congrArg (RawTerm.codataUnfold currentState)
                transitionEq)
        exact innerIH transitionTarget
          ⟨transitionStep, transitionDistinct⟩
      · have stateProgress :
            RawStep.parProgress currentState stateTarget :=
          ⟨stateStep, stateEq⟩
        by_cases transitionEq : currentTransition = transitionTarget
        · subst transitionEq
          exact stateIH stateTarget stateProgress
            (RawTerm.isStronglyNormalizing.intro currentTransition
              transitionClosure)
        · exact stateIH stateTarget stateProgress
            (transitionClosure transitionTarget
              ⟨transitionStep, transitionEq⟩)

/-- Typed wrapper for codata unfold SN preservation. -/
theorem Term.codataUnfold_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition : Term context (Ty.arrow stateType outputType) transitionRaw}
    (stateIsSN : Term.isStronglyNormalizing initialState)
    (transitionIsSN : Term.isStronglyNormalizing transition) :
    Term.isStronglyNormalizing
      (Term.codataUnfold initialState transition) :=
  RawTerm.codataUnfold_isStronglyNormalizing stateIsSN transitionIsSN

/-! ## ===== DELETED unsound hypothesis-as-postulate helpers =====

This file formerly shipped the following 14 theorems carrying a
universally-quantified `contractumIsSN` / `inlContractumIsSN` /
`inrContractumIsSN` / `uaContractumIsSN` / `composeContractumIsSN`
Pi-type hypothesis over raw scopes:

* `RawTerm.codataDest_isStronglyNormalizing`
* `Term.codataDest_isStronglyNormalizing`
* `RawTerm.listElim_isStronglyNormalizing`
* `Term.listElim_isStronglyNormalizing`
* `RawTerm.optionMatch_isStronglyNormalizing`
* `Term.optionMatch_isStronglyNormalizing`
* `RawTerm.eitherMatch_isStronglyNormalizing`
* `Term.eitherMatch_isStronglyNormalizing`
* `RawTerm.app_isStronglyNormalizing`
* `Term.app_isStronglyNormalizing`
* `Term.appPi_isStronglyNormalizing`
* `RawTerm.pathApp_isStronglyNormalizing`
* `Term.pathApp_isStronglyNormalizing`
* `RawTerm.transp_isStronglyNormalizing`
* `Term.transp_isStronglyNormalizing`

At the raw layer each hypothesis is not provable in general — for
arbitrary raw `bodyTarget` / `argumentTarget`, SN of both does NOT
imply SN of `bodyTarget.subst0 argumentTarget` (substitution can
introduce non-termination in untyped λ-calculus).  These theorems
were hypothesis-as-postulate, banned by `CLAUDE.md` "Forbidden
reasoning patterns".  All 15 have been DELETED.

The honest replacements are the Kripke step-indexed reducibility
predicate (`ReducibleK`) and the eliminator headlines in
`Reducibility/Kripke/Headline.lean` that take `ReducibleK` premises
instead of `contractumIsSN` postulates:

* `Term.codataDest_strong_normalization_via_kripke`
* `Term.listElim_strong_normalization_via_kripke`
* `Term.optionMatch_strong_normalization_via_kripke`
* `Term.eitherMatch_strong_normalization_via_kripke`
* `Term.app_strong_normalization_via_kripke`
* `Term.appPi_strong_normalization_via_kripke`
* `Term.pathApp_strong_normalization_via_kripke`

These already ship cleanly via `TermRenaming.identity` +
`ReducibleK.transport` strip pattern.  The remaining three
unstripped headlines (`natElim`, `natRec`, `transp`, `hcomp`) require
extended Kripke closure clauses for `Ty.nat` and `Ty.path` plus the
cascade through Monotone / Weaken / SNClosure / Basic / Project /
Fundamental / SNExtraction.  Those extensions are pending the M04
fundamental theorem cascade (per
`feedback_kripke_predicate_partial_closure.md`). -/
/-- **hcomp SN preservation**.  Homogeneous cubical composition: at the
raw level `hcomp sidesTerm capTerm` only admits congruence reductions
(no computational β rule on the boundary yet — that is future work
gated by #1528).  Pure 2-operand cong induction. -/
theorem RawTerm.hcomp_isStronglyNormalizing {scope : Nat}
    {sidesTerm : RawTerm scope}
    (sidesIsSN : RawTerm.isStronglyNormalizing sidesTerm) :
    ∀ {capTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing capTerm →
      RawTerm.isStronglyNormalizing
        (RawTerm.hcomp sidesTerm capTerm) := by
  induction sidesIsSN with
  | intro currentSides sidesClosure sidesIH =>
    intro capTerm capIsSN
    induction capIsSN with
    | intro currentCap capClosure capIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.hcomp currentSides currentCap) ?_
      intro target progressStep
      have congArmSN :
          ∀ (sidesTarget capTarget : RawTerm scope),
            target = RawTerm.hcomp sidesTarget capTarget →
            RawStep.par currentSides sidesTarget →
            RawStep.par currentCap capTarget →
            RawTerm.isStronglyNormalizing target := by
        intro sidesTarget capTarget targetEq sidesStep capStep
        subst targetEq
        have sidesTargetIsSN :
            RawTerm.isStronglyNormalizing sidesTarget := by
          by_cases sidesEq : currentSides = sidesTarget
          · subst sidesEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSides sidesClosure
          · exact sidesClosure sidesTarget ⟨sidesStep, sidesEq⟩
        have capTargetIsSN :
            RawTerm.isStronglyNormalizing capTarget := by
          by_cases capEq : currentCap = capTarget
          · subst capEq
            exact RawTerm.isStronglyNormalizing.intro
              currentCap capClosure
          · exact capClosure capTarget ⟨capStep, capEq⟩
        by_cases sidesEq : currentSides = sidesTarget
        · subst sidesEq
          by_cases capEq : currentCap = capTarget
          · subst capEq
            exact (progressStep.2 rfl).elim
          · exact capIH capTarget ⟨capStep, capEq⟩
        · exact sidesIH sidesTarget
            ⟨sidesStep, sidesEq⟩
            capTargetIsSN
      have betaArmSN :
          ∀ (capRawTarget : RawTerm scope),
            target = capRawTarget →
            RawStep.par currentCap capRawTarget →
            RawTerm.isStronglyNormalizing target := by
        intro capRawTarget targetEq capStep
        rw [targetEq]
        by_cases capEq : currentCap = capRawTarget
        · rw [← capEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentCap capClosure
        · exact capClosure capRawTarget ⟨capStep, capEq⟩
      rcases RawStep.par.hcomp_inv progressStep.1 with
        ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ |
        ⟨_, capTargetBeta, _, betaTargetEq, betaCapStep⟩ |
        ⟨_, capTargetDeep, deepTargetEq, _, deepCapStep⟩
      · exact congArmSN sidesTarget capTarget targetEq sidesStep capStep
      · exact betaArmSN capTargetBeta betaTargetEq betaCapStep
      · exact betaArmSN capTargetDeep deepTargetEq deepCapStep

/-- Typed wrapper for hcomp SN preservation. -/
theorem Term.hcomp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIsSN : Term.isStronglyNormalizing sidesValue)
    (capIsSN : Term.isStronglyNormalizing capValue) :
    Term.isStronglyNormalizing
      (Term.hcomp modeIsUnivalent sidesValue capValue) :=
  RawTerm.hcomp_isStronglyNormalizing sidesIsSN capIsSN

/-- Typed wrapper for `Term.hcompPath` SN preservation.  `hcompPath`
projects to the same `RawTerm.hcomp` as the unary `Term.hcomp`,
so the raw SN preservation lemma applies directly — the only
difference is that `hcompPath`'s sides argument has the
path-typed shape (`Ty.path carrierType leftEndpoint rightEndpoint`)
rather than the carrier-typed shape, supporting the future
"constant-path collapses" cubical β rule (#1528). -/
theorem Term.hcompPath_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesPathRaw capRaw : RawTerm scope}
    {sidesPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIsSN : Term.isStronglyNormalizing sidesPath)
    (capIsSN : Term.isStronglyNormalizing capValue) :
    Term.isStronglyNormalizing
      (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath capValue) :=
  RawTerm.hcomp_isStronglyNormalizing sidesIsSN capIsSN


end LeanFX2
