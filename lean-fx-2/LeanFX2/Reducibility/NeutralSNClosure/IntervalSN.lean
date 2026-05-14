import LeanFX2.Reducibility.NeutralSNClosure.TypeCodeSN

/-! # LeanFX2.Reducibility.NeutralSNClosure.IntervalSN

Raw SN witnesses for the cubical interval operations:
`intervalOpp` / `intervalMeet` / `intervalJoin`, `pathLam` (raw +
Term), `uaToEquiv`, `oeqFunext`.

## Root status

Layer 3 metatheory leaf.  Second slice of NeutralSNClosure. -/

namespace LeanFX2

/-- **K12.20.AF.1 intervalOpp SN preservation** — cubical interval
negation.  Unary cong over the interval term; intervalOpp_inv
discharges each par step. -/
theorem RawTerm.intervalOpp_isStronglyNormalizing {scope : Nat}
    {intervalTerm : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.intervalOpp intervalTerm) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.intervalOpp currentInterval) ?_
    intro target progressStep
    obtain ⟨intervalTarget, targetEq, intervalStep⟩ :=
      RawStep.par.intervalOpp_inv progressStep.1
    subst targetEq
    have intervalDistinct :
        currentInterval ≠ intervalTarget := fun intervalEq =>
      progressStep.2 (congrArg RawTerm.intervalOpp intervalEq)
    exact inductiveHypothesis intervalTarget
      ⟨intervalStep, intervalDistinct⟩

/-- **K12.20.AF.2 intervalMeet SN preservation** — cubical interval
meet (∧).  Binary cong; uses the universal-in-conclusion trick
to keep the second-argument IH universal during induction on the
first SN witness. -/
theorem RawTerm.intervalMeet_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalMeet leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalMeet currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalMeet_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalMeet currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AF.3 intervalJoin SN preservation** — cubical interval
join (∨).  Sister to intervalMeet; same binary cong shape. -/
theorem RawTerm.intervalJoin_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalJoin leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalJoin currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalJoin_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalJoin currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AG pathLam SN preservation** — cubical path lambda
binder.  Sister to lam helper — body lives in `RawTerm (scope+1)`,
induction on body's SN witness discharges each par step via
pathLam_inv + congrArg-based parProgress disequality. -/
theorem RawTerm.pathLam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.pathLam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathLam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.pathLam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.pathLam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-- Typed wrapper for cubical path-lambda SN preservation.

This packages the raw binder SN fact for `Term.pathLam`.  It is only
the SN half of the cubical path-introduction case; the full Reducible
closure still needs the interval-application endpoint. -/
theorem Term.pathLam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        bodyTerm) :=
  RawTerm.pathLam_isStronglyNormalizing bodyIsSN

/-- **K12.20.AI.1 uaToEquiv SN preservation** — univalence-to-
equivalence converter (D3.6 ua_β infrastructure).  Pure unary
cong over its proof witness; uaToEquiv_inv discharges. -/
theorem RawTerm.uaToEquiv_isStronglyNormalizing {scope : Nat}
    {proof : RawTerm scope}
    (proofIsSN : RawTerm.isStronglyNormalizing proof) :
    RawTerm.isStronglyNormalizing (RawTerm.uaToEquiv proof) := by
  induction proofIsSN with
  | intro currentProof _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.uaToEquiv currentProof) ?_
    intro target progressStep
    obtain ⟨proofTarget, targetEq, proofStep⟩ :=
      RawStep.par.uaToEquiv_inv progressStep.1
    subst targetEq
    have proofDistinct :
        currentProof ≠ proofTarget := fun proofEq =>
      progressStep.2 (congrArg RawTerm.uaToEquiv proofEq)
    exact inductiveHypothesis proofTarget
      ⟨proofStep, proofDistinct⟩

/-- **K12.20.AI.2 oeqFunext SN preservation** — observational
equality functional extensionality intro.  Pure unary cong over
the pointwise-equality witness. -/
theorem RawTerm.oeqFunext_isStronglyNormalizing {scope : Nat}
    {pointwiseEquality : RawTerm scope}
    (pointwiseIsSN : RawTerm.isStronglyNormalizing pointwiseEquality) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqFunext pointwiseEquality) := by
  induction pointwiseIsSN with
  | intro currentPointwise _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqFunext currentPointwise) ?_
    intro target progressStep
    obtain ⟨pointwiseTarget, targetEq, pointwiseStep⟩ :=
      RawStep.par.oeqFunext_inv progressStep.1
    subst targetEq
    have pointwiseDistinct :
        currentPointwise ≠ pointwiseTarget := fun pointwiseEq =>
      progressStep.2 (congrArg RawTerm.oeqFunext pointwiseEq)
    exact inductiveHypothesis pointwiseTarget
      ⟨pointwiseStep, pointwiseDistinct⟩


end LeanFX2
