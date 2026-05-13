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

/-- Head-β SN expansion for single-field record projection.

If the field is strongly normalizing, then
`recordProj (recordIntro field)` is strongly normalizing.  Congruence
reducts recurse through the record field; β reducts land on a reduct
of the field. -/
theorem RawTerm.recordProj_recordIntro_isStronglyNormalizing
    {scope : Nat}
    {firstField : RawTerm scope}
    (firstFieldIsSN : RawTerm.isStronglyNormalizing firstField) :
    RawTerm.isStronglyNormalizing
      (RawTerm.recordProj (RawTerm.recordIntro firstField)) := by
  induction firstFieldIsSN with
  | intro currentField fieldClosure fieldIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj (RawTerm.recordIntro currentField)) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨_recordTarget, targetEq, recordStep⟩
      | ⟨firstTarget, targetEq, recordStep⟩
    · obtain ⟨firstTarget, recordTargetEq, firstStep⟩ :=
        RawStep.par.recordIntro_inv recordStep
      subst recordTargetEq
      subst targetEq
      by_cases firstEq : currentField = firstTarget
      · subst firstEq
        exact False.elim (progressStep.2 rfl)
      · exact fieldIH firstTarget ⟨firstStep, firstEq⟩
    · obtain ⟨recordFirstTarget, recordTargetEq, firstStep⟩ :=
        RawStep.par.recordIntro_inv recordStep
      injection recordTargetEq with _scopeEq firstTargetEq
      rw [targetEq]
      have firstStepToTarget : RawStep.par currentField firstTarget := by
        rw [firstTargetEq]
        exact firstStep
      by_cases firstEq : currentField = firstTarget
      · subst firstEq
        exact RawTerm.isStronglyNormalizing.intro
          currentField fieldClosure
      · exact fieldClosure firstTarget ⟨firstStepToTarget, firstEq⟩

/-- Typed wrapper for `recordProj (recordIntro field)` SN expansion.

This is an SN bridge only.  The full record-intro reducibility theorem
still requires typed backward closure at the projected field type. -/
theorem Term.recordProj_recordIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing
      (Term.recordProj (Term.recordIntro firstField)) :=
  RawTerm.recordProj_recordIntro_isStronglyNormalizing firstFieldIsSN

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

/-- Head-β SN expansion for refinement elimination.

If the refined value payload and its erased proof payload are strongly
normalizing, then `refineElim (refineIntro value proof)` is strongly
normalizing.  Congruence reducts recurse through both payloads; β reducts
land on a reduct of the value payload. -/
theorem RawTerm.refineElim_refineIntro_isStronglyNormalizing
    {scope : Nat}
    {rawValue : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing rawValue) :
    ∀ {predicateProof : RawTerm scope},
      RawTerm.isStronglyNormalizing predicateProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.refineElim
          (RawTerm.refineIntro rawValue predicateProof)) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro predicateProof proofIsSN
    induction proofIsSN with
    | intro currentProof proofClosure proofIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.refineElim
          (RawTerm.refineIntro currentValue currentProof)) ?_
      intro target progressStep
      rcases RawStep.par.refineElim_inv progressStep.1 with
        ⟨refinedTarget, targetEq, refinedStep⟩
        | ⟨valueTarget, proofTarget, targetEq, refinedStep⟩
      · obtain ⟨valueTarget, proofTarget, refinedTargetEq,
            valueStep, proofStep⟩ :=
          RawStep.par.refineIntro_inv refinedStep
        subst refinedTargetEq
        subst targetEq
        by_cases valueEq : currentValue = valueTarget
        · subst valueEq
          by_cases proofEq : currentProof = proofTarget
          · subst proofEq
            exact False.elim (progressStep.2 rfl)
          · exact proofIH proofTarget ⟨proofStep, proofEq⟩
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
      · obtain ⟨refinedValueTarget, _refinedProofTarget,
            refinedTargetEq, valueStep, _proofStep⟩ :=
          RawStep.par.refineIntro_inv refinedStep
        injection refinedTargetEq with _scopeEq valueTargetEq
          _proofTargetEq
        rw [targetEq]
        have valueStepToTarget :
            RawStep.par currentValue valueTarget := by
          rw [valueTargetEq]
          exact valueStep
        by_cases valueEq : currentValue = valueTarget
        · subst valueEq
          exact RawTerm.isStronglyNormalizing.intro
            currentValue valueClosure
        · exact valueClosure valueTarget
            ⟨valueStepToTarget, valueEq⟩

/-- Typed wrapper for `refineElim (refineIntro value proof)` SN expansion.

This is an SN bridge only.  It does not claim the full `Reducible`
backward closure for refinement introduction. -/
theorem Term.refineElim_refineIntro_isStronglyNormalizing
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
      (Term.refineElim
        (Term.refineIntro predicate baseValue predicateProof)) :=
  RawTerm.refineElim_refineIntro_isStronglyNormalizing
    valueIsSN proofIsSN

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


end LeanFX2
