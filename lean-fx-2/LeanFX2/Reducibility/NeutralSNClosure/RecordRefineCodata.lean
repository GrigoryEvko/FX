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

/-- **codata destructor SN preservation**.  The destructor has a
cong arm + the β arm `codataDest (codataUnfold state transition) →
app transition state` (plus its Deep variant).  When the codataValue
reduces to `codataUnfold state' transition'`, SN of the unfold form
yields SN of state' and transition' via the SubtermSN inversions;
the contractum-SN hypothesis then discharges the β reduct. -/
theorem RawTerm.codataDest_isStronglyNormalizing {scope : Nat}
    {codataValue : RawTerm scope}
    (codataIsSN : RawTerm.isStronglyNormalizing codataValue)
    (contractumIsSN :
      ∀ {stateRaw transitionRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing stateRaw →
        RawTerm.isStronglyNormalizing transitionRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app transitionRaw stateRaw)) :
    RawTerm.isStronglyNormalizing
      (RawTerm.codataDest codataValue) := by
  induction codataIsSN with
  | intro currentCodata codataClosure inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.codataDest currentCodata) ?_
    intro target progressStep
    rcases RawStep.par.codataDest_inv progressStep.1 with
      ⟨codataTarget, targetEq, codataStep⟩
      | ⟨stateTarget, transitionTarget, targetEq, codataStep⟩
    · subst targetEq
      by_cases codataEq : currentCodata = codataTarget
      · subst codataEq
        exact (progressStep.2 rfl).elim
      · exact inductiveHypothesis codataTarget
          ⟨codataStep, codataEq⟩
    · subst targetEq
      have unfoldTargetIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.codataUnfold stateTarget transitionTarget) := by
        by_cases codataEq :
            currentCodata =
              RawTerm.codataUnfold stateTarget transitionTarget
        · rw [← codataEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentCodata codataClosure
        · exact codataClosure
            (RawTerm.codataUnfold stateTarget transitionTarget)
            ⟨codataStep, codataEq⟩
      have stateTargetIsSN :
          RawTerm.isStronglyNormalizing stateTarget :=
        RawTerm.codataUnfold_state_isStronglyNormalizing
          unfoldTargetIsSN
      have transitionTargetIsSN :
          RawTerm.isStronglyNormalizing transitionTarget :=
        RawTerm.codataUnfold_transition_isStronglyNormalizing
          unfoldTargetIsSN
      exact contractumIsSN stateTargetIsSN transitionTargetIsSN

/-- Typed wrapper for codataDest SN preservation. -/
theorem Term.codataDest_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
      Term context (Ty.codata stateType outputType) codataRaw}
    (codataIsSN : Term.isStronglyNormalizing codataValue)
    (contractumIsSN :
      ∀ {stateRaw transitionRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing stateRaw →
        RawTerm.isStronglyNormalizing transitionRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app transitionRaw stateRaw)) :
    Term.isStronglyNormalizing (Term.codataDest codataValue) :=
  RawTerm.codataDest_isStronglyNormalizing codataIsSN contractumIsSN

/-- **listElim generic-closure SN preservation**.  Cong arm steps all
three children; nil-ι arm replaces the eliminator with `nilBranch`;
cons-ι arm replaces it with `app (app consBranch head) tail` after the
scrutinee reduces to `listCons head tail`.  The contractum closure
hypothesis discharges the cons-ι arm by consuming the head/tail/cons
SN witnesses extracted from the listCons-form scrutinee and the cons
branch closure. -/
theorem RawTerm.listElim_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {nilBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing nilBranch →
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      (∀ {headRaw tailRaw consTarget : RawTerm scope},
        RawTerm.isStronglyNormalizing headRaw →
        RawTerm.isStronglyNormalizing tailRaw →
        RawTerm.isStronglyNormalizing consTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app consTarget headRaw) tailRaw)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim scrutinee nilBranch consBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro nilBranch nilIsSN
    induction nilIsSN with
    | intro currentNil nilClosure nilIH =>
      intro consBranch consIsSN contractumClosure
      induction consIsSN with
      | intro currentCons consClosure consIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.listElim currentScrutinee currentNil currentCons) ?_
        intro target progressStep
        rcases RawStep.par.listElim_inv progressStep.1 with
          ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
            scrutineeStep, nilStep, consStep⟩
          | ⟨nilTarget, targetEq, scrutineeStep, nilStep⟩
          | ⟨headTarget, tailTarget, consTarget, targetEq,
              scrutineeStep, consStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have nilTargetIsSN :
              RawTerm.isStronglyNormalizing nilTarget := by
            by_cases nilEq : currentNil = nilTarget
            · subst nilEq
              exact RawTerm.isStronglyNormalizing.intro
                currentNil nilClosure
            · exact nilClosure nilTarget ⟨nilStep, nilEq⟩
          have consTargetIsSN :
              RawTerm.isStronglyNormalizing consTarget := by
            by_cases consEq : currentCons = consTarget
            · subst consEq
              exact RawTerm.isStronglyNormalizing.intro
                currentCons consClosure
            · exact consClosure consTarget ⟨consStep, consEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases nilEq : currentNil = nilTarget
            · subst nilEq
              by_cases consEq : currentCons = consTarget
              · subst consEq
                exact (progressStep.2 rfl).elim
              · exact consIH consTarget ⟨consStep, consEq⟩
            · exact nilIH nilTarget ⟨nilStep, nilEq⟩
                consTargetIsSN contractumClosure
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              nilTargetIsSN consTargetIsSN contractumClosure
        · rw [targetEq]
          by_cases nilEq : currentNil = nilTarget
          · subst nilEq
            exact RawTerm.isStronglyNormalizing.intro
              currentNil nilClosure
          · exact nilClosure nilTarget ⟨nilStep, nilEq⟩
        · subst targetEq
          have listConsScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.listCons headTarget tailTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.listCons headTarget tailTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure
                (RawTerm.listCons headTarget tailTarget)
                ⟨scrutineeStep, scrutineeEq⟩
          have headTargetIsSN :
              RawTerm.isStronglyNormalizing headTarget :=
            RawTerm.listCons_head_isStronglyNormalizing
              listConsScrutineeIsSN
          have tailTargetIsSN :
              RawTerm.isStronglyNormalizing tailTarget :=
            RawTerm.listCons_tail_isStronglyNormalizing
              listConsScrutineeIsSN
          have consTargetIsSN :
              RawTerm.isStronglyNormalizing consTarget := by
            by_cases consEq : currentCons = consTarget
            · subst consEq
              exact RawTerm.isStronglyNormalizing.intro
                currentCons consClosure
            · exact consClosure consTarget ⟨consStep, consEq⟩
          exact contractumClosure
            headTargetIsSN tailTargetIsSN consTargetIsSN

/-- Typed wrapper for listElim generic-closure SN preservation. -/
theorem Term.listElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType)
                                    motiveType)) consRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch)
    (contractumIsSN :
      ∀ {headRaw tailRaw consTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing headRaw →
        RawTerm.isStronglyNormalizing tailRaw →
        RawTerm.isStronglyNormalizing consTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app consTargetRaw headRaw) tailRaw)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  RawTerm.listElim_isStronglyNormalizing
    scrutineeIsSN nilIsSN consIsSN contractumIsSN

/-- **optionMatch generic-closure SN preservation**.  Same shape as
listElim, with the cons-ι slot replaced by some-ι firing on a single
payload.  The contractum closure discharges
`optionMatch (optionSome v) n s → app s v`. -/
theorem RawTerm.optionMatch_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {noneBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing noneBranch →
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      (∀ {valueRaw someTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing someTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app someTargetRaw valueRaw)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch scrutinee noneBranch someBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro noneBranch noneIsSN
    induction noneIsSN with
    | intro currentNone noneClosure noneIH =>
      intro someBranch someIsSN contractumClosure
      induction someIsSN with
      | intro currentSome someClosure someIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.optionMatch currentScrutinee currentNone currentSome) ?_
        intro target progressStep
        rcases RawStep.par.optionMatch_inv progressStep.1 with
          ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
            scrutineeStep, noneStep, someStep⟩
          | ⟨noneTarget, targetEq, scrutineeStep, noneStep⟩
          | ⟨valueTarget, someTarget, targetEq, scrutineeStep, someStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have noneTargetIsSN :
              RawTerm.isStronglyNormalizing noneTarget := by
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              exact RawTerm.isStronglyNormalizing.intro
                currentNone noneClosure
            · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
          have someTargetIsSN :
              RawTerm.isStronglyNormalizing someTarget := by
            by_cases someEq : currentSome = someTarget
            · subst someEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSome someClosure
            · exact someClosure someTarget ⟨someStep, someEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact (progressStep.2 rfl).elim
              · exact someIH someTarget ⟨someStep, someEq⟩
            · exact noneIH noneTarget ⟨noneStep, noneEq⟩
                someTargetIsSN contractumClosure
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              noneTargetIsSN someTargetIsSN contractumClosure
        · rw [targetEq]
          by_cases noneEq : currentNone = noneTarget
          · subst noneEq
            exact RawTerm.isStronglyNormalizing.intro
              currentNone noneClosure
          · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
        · subst targetEq
          have optionSomeScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.optionSome valueTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.optionSome valueTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure (RawTerm.optionSome valueTarget)
                ⟨scrutineeStep, scrutineeEq⟩
          have valueTargetIsSN :
              RawTerm.isStronglyNormalizing valueTarget :=
            RawTerm.optionSome_value_isStronglyNormalizing
              optionSomeScrutineeIsSN
          have someTargetIsSN :
              RawTerm.isStronglyNormalizing someTarget := by
            by_cases someEq : currentSome = someTarget
            · subst someEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSome someClosure
            · exact someClosure someTarget ⟨someStep, someEq⟩
          exact contractumClosure valueTargetIsSN someTargetIsSN

/-- Typed wrapper for optionMatch generic-closure SN preservation. -/
theorem Term.optionMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (contractumIsSN :
      ∀ {valueRaw someTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing someTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app someTargetRaw valueRaw)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  RawTerm.optionMatch_isStronglyNormalizing
    scrutineeIsSN noneIsSN someIsSN contractumIsSN

/-- **eitherMatch generic-closure SN preservation**.  Cong arm steps
all three children; inl-ι arm replaces with `app leftTarget value`
after `scrutinee → eitherInl value`; inr-ι symmetrical for the right
side.  Each ι arm's contractum closure consumes the value-SN extracted
from the eitherInl/Inr-form scrutinee and the corresponding branch
closure. -/
theorem RawTerm.eitherMatch_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {leftBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing leftBranch →
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      (∀ {valueRaw leftTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing leftTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app leftTargetRaw valueRaw)) →
      (∀ {valueRaw rightTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing rightTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app rightTargetRaw valueRaw)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro leftBranch leftIsSN
    induction leftIsSN with
    | intro currentLeft leftClosure leftIH =>
      intro rightBranch rightIsSN inlClosure inrClosure
      induction rightIsSN with
      | intro currentRight rightClosure rightIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.eitherMatch currentScrutinee currentLeft currentRight) ?_
        intro target progressStep
        rcases RawStep.par.eitherMatch_inv progressStep.1 with
          ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
            scrutineeStep, leftStep, rightStep⟩
          | ⟨valueTarget, leftTarget, targetEq, scrutineeStep, leftStep⟩
          | ⟨valueTarget, rightTarget, targetEq, scrutineeStep, rightStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have leftTargetIsSN :
              RawTerm.isStronglyNormalizing leftTarget := by
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              exact RawTerm.isStronglyNormalizing.intro
                currentLeft leftClosure
            · exact leftClosure leftTarget ⟨leftStep, leftEq⟩
          have rightTargetIsSN :
              RawTerm.isStronglyNormalizing rightTarget := by
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact RawTerm.isStronglyNormalizing.intro
                currentRight rightClosure
            · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact (progressStep.2 rfl).elim
              · exact rightIH rightTarget ⟨rightStep, rightEq⟩
            · exact leftIH leftTarget ⟨leftStep, leftEq⟩
                rightTargetIsSN inlClosure inrClosure
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              leftTargetIsSN rightTargetIsSN inlClosure inrClosure
        · subst targetEq
          have inlScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.eitherInl valueTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.eitherInl valueTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure (RawTerm.eitherInl valueTarget)
                ⟨scrutineeStep, scrutineeEq⟩
          have valueTargetIsSN :
              RawTerm.isStronglyNormalizing valueTarget :=
            RawTerm.eitherInl_value_isStronglyNormalizing
              inlScrutineeIsSN
          have leftTargetIsSN :
              RawTerm.isStronglyNormalizing leftTarget := by
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              exact RawTerm.isStronglyNormalizing.intro
                currentLeft leftClosure
            · exact leftClosure leftTarget ⟨leftStep, leftEq⟩
          exact inlClosure valueTargetIsSN leftTargetIsSN
        · subst targetEq
          have inrScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.eitherInr valueTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.eitherInr valueTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure (RawTerm.eitherInr valueTarget)
                ⟨scrutineeStep, scrutineeEq⟩
          have valueTargetIsSN :
              RawTerm.isStronglyNormalizing valueTarget :=
            RawTerm.eitherInr_value_isStronglyNormalizing
              inrScrutineeIsSN
          have rightTargetIsSN :
              RawTerm.isStronglyNormalizing rightTarget := by
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact RawTerm.isStronglyNormalizing.intro
                currentRight rightClosure
            · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
          exact inrClosure valueTargetIsSN rightTargetIsSN

/-- Typed wrapper for eitherMatch generic-closure SN preservation. -/
theorem Term.eitherMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (inlContractumIsSN :
      ∀ {valueRaw leftTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing leftTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app leftTargetRaw valueRaw))
    (inrContractumIsSN :
      ∀ {valueRaw rightTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing rightTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app rightTargetRaw valueRaw)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  RawTerm.eitherMatch_isStronglyNormalizing
    scrutineeIsSN leftIsSN rightIsSN inlContractumIsSN inrContractumIsSN

/-- **app generic-closure SN preservation**.  Cong arm steps both
function and argument; β arm fires when function reduces to a lambda:
`app (lam body) arg → body.subst0 arg`.  The contractum closure
consumes the body SN (extracted via `lam_body_isStronglyNormalizing`
from the function-reduct lam-form) and the argument SN, returning SN
of the substituted body.  Mirrors codataDest's
contractum-closure pattern. -/
theorem RawTerm.app_isStronglyNormalizing {scope : Nat}
    {functionTerm : RawTerm scope}
    (functionIsSN : RawTerm.isStronglyNormalizing functionTerm) :
    ∀ {argumentTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing argumentTerm →
      (∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {argumentTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing argumentTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 argumentTargetRaw)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionTerm argumentTerm) := by
  induction functionIsSN with
  | intro currentFunction functionClosure functionIH =>
    intro argumentTerm argumentIsSN
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentIH =>
      intro contractumClosure
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.app currentFunction currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.app_inv progressStep.1 with
        ⟨functionTarget, argumentTarget, targetEq,
          functionStep, argumentStep⟩
        | ⟨bodyTarget, argumentTarget, targetEq,
            functionStep, argumentStep⟩
      · subst targetEq
        have functionTargetIsSN :
            RawTerm.isStronglyNormalizing functionTarget := by
          by_cases functionEq : currentFunction = functionTarget
          · subst functionEq
            exact RawTerm.isStronglyNormalizing.intro
              currentFunction functionClosure
          · exact functionClosure functionTarget
              ⟨functionStep, functionEq⟩
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        by_cases functionEq : currentFunction = functionTarget
        · subst functionEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact (progressStep.2 rfl).elim
          · exact argumentIH argumentTarget
              ⟨argumentStep, argumentEq⟩ contractumClosure
        · exact functionIH functionTarget
            ⟨functionStep, functionEq⟩
            argumentTargetIsSN contractumClosure
      · subst targetEq
        have lamFunctionIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.lam bodyTarget) := by
          by_cases functionEq :
              currentFunction = RawTerm.lam bodyTarget
          · rw [← functionEq]
            exact RawTerm.isStronglyNormalizing.intro
              currentFunction functionClosure
          · exact functionClosure (RawTerm.lam bodyTarget)
              ⟨functionStep, functionEq⟩
        have bodyTargetIsSN :
            RawTerm.isStronglyNormalizing bodyTarget :=
          RawTerm.lam_body_isStronglyNormalizing lamFunctionIsSN
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        exact contractumClosure bodyTargetIsSN argumentTargetIsSN

/-- Typed wrapper for app generic-closure SN preservation. -/
theorem Term.app_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIsSN : Term.isStronglyNormalizing functionTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {argumentTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing argumentTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 argumentTargetRaw)) :
    Term.isStronglyNormalizing (Term.app functionTerm argumentTerm) :=
  RawTerm.app_isStronglyNormalizing
    functionIsSN argumentIsSN contractumIsSN

/-- Typed wrapper for appPi generic-closure SN preservation.  Same
raw projection `RawTerm.app functionRaw argumentRaw` as `Term.app`;
only the typed signature differs (dependent codomain).  Reuses
`RawTerm.app_isStronglyNormalizing` since the raw β rule is shared
between non-dependent and dependent arrows. -/
theorem Term.appPi_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIsSN : Term.isStronglyNormalizing functionTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {argumentTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing argumentTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 argumentTargetRaw)) :
    Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm) :=
  RawTerm.app_isStronglyNormalizing
    functionIsSN argumentIsSN contractumIsSN

/-- **pathApp generic-closure SN preservation**.  Cong arm steps both
path term and interval argument; β arm fires when path develops to a
`pathLam`: `pathApp (pathLam body) interval → body.subst0 interval`.
Same closure shape as `app` modulo the constructor — uses
`pathLam_body_isStronglyNormalizing` to extract body SN. -/
theorem RawTerm.pathApp_isStronglyNormalizing {scope : Nat}
    {pathTerm : RawTerm scope}
    (pathIsSN : RawTerm.isStronglyNormalizing pathTerm) :
    ∀ {intervalTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing intervalTerm →
      (∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {intervalTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing intervalTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 intervalTargetRaw)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp pathTerm intervalTerm) := by
  induction pathIsSN with
  | intro currentPath pathClosure pathIH =>
    intro intervalTerm intervalIsSN
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalIH =>
      intro contractumClosure
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp currentPath currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq,
          pathStep, intervalStep⟩
        | ⟨bodyTarget, intervalTarget, targetEq,
            pathStep, intervalStep⟩
      · subst targetEq
        have pathTargetIsSN :
            RawTerm.isStronglyNormalizing pathTarget := by
          by_cases pathEq : currentPath = pathTarget
          · subst pathEq
            exact RawTerm.isStronglyNormalizing.intro
              currentPath pathClosure
          · exact pathClosure pathTarget ⟨pathStep, pathEq⟩
        have intervalTargetIsSN :
            RawTerm.isStronglyNormalizing intervalTarget := by
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact RawTerm.isStronglyNormalizing.intro
              currentInterval intervalClosure
          · exact intervalClosure intervalTarget
              ⟨intervalStep, intervalEq⟩
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact (progressStep.2 rfl).elim
          · exact intervalIH intervalTarget
              ⟨intervalStep, intervalEq⟩ contractumClosure
        · exact pathIH pathTarget
            ⟨pathStep, pathEq⟩
            intervalTargetIsSN contractumClosure
      · subst targetEq
        have pathLamPathIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.pathLam bodyTarget) := by
          by_cases pathEq :
              currentPath = RawTerm.pathLam bodyTarget
          · rw [← pathEq]
            exact RawTerm.isStronglyNormalizing.intro
              currentPath pathClosure
          · exact pathClosure (RawTerm.pathLam bodyTarget)
              ⟨pathStep, pathEq⟩
        have bodyTargetIsSN :
            RawTerm.isStronglyNormalizing bodyTarget :=
          RawTerm.pathLam_body_isStronglyNormalizing pathLamPathIsSN
        have intervalTargetIsSN :
            RawTerm.isStronglyNormalizing intervalTarget := by
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact RawTerm.isStronglyNormalizing.intro
              currentInterval intervalClosure
          · exact intervalClosure intervalTarget
              ⟨intervalStep, intervalEq⟩
        exact contractumClosure bodyTargetIsSN intervalTargetIsSN

/-- Typed wrapper for pathApp generic-closure SN preservation. -/
theorem Term.pathApp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (pathIsSN : Term.isStronglyNormalizing pathTerm)
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {intervalTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing intervalTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 intervalTargetRaw)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) :=
  RawTerm.pathApp_isStronglyNormalizing
    pathIsSN intervalIsSN contractumIsSN

/-- **transp generic-closure SN preservation**.  Transport has congruence
plus three computational families at the raw layer: constant-path transport
returns the source, univalence transport reduces to `equivApply`, and
composed paths reduce to nested transports.  The latter two are exposed as
contractum closures so this lemma stays independent of the later typed
β-rule packaging. -/
theorem RawTerm.transp_isStronglyNormalizing {scope : Nat}
    {pathTerm : RawTerm scope}
    (pathIsSN : RawTerm.isStronglyNormalizing pathTerm) :
    ∀ {sourceTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing sourceTerm →
      (∀ {equivRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing equivRaw →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply equivRaw sourceTargetRaw)) →
      (∀ {leftPathRaw rightPathRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing
          (RawTerm.pathCompose leftPathRaw rightPathRaw) →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightPathRaw
            (RawTerm.transp leftPathRaw sourceTargetRaw))) →
      RawTerm.isStronglyNormalizing
        (RawTerm.transp pathTerm sourceTerm) := by
  induction pathIsSN with
  | intro currentPath pathClosure pathIH =>
    intro sourceTerm sourceIsSN
    induction sourceIsSN with
    | intro currentSource sourceClosure sourceIH =>
      intro uaContractumIsSN composeContractumIsSN
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.transp currentPath currentSource) ?_
      intro target progressStep
      rcases RawStep.par.transp_inv progressStep.1 with
        ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨typeRawSource, sourceTarget, pathEq, targetEq, sourceStep⟩
        | ⟨typeRawTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨proofRawSource, proofRawTarget, sourceTarget, pathEq,
            targetEq, proofStep, sourceStep⟩
        | ⟨proofRawTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨leftRawSource, leftRawTarget, rightRawSource, rightRawTarget,
            sourceTarget, pathEq, targetEq, leftStep, rightStep,
            sourceStep⟩
        | ⟨leftRawTarget, rightRawTarget, sourceTarget, targetEq,
            pathStep, sourceStep⟩
      · subst targetEq
        have pathTargetIsSN :
            RawTerm.isStronglyNormalizing pathTarget := by
          by_cases pathEq : currentPath = pathTarget
          · subst pathEq
            exact RawTerm.isStronglyNormalizing.intro
              currentPath pathClosure
          · exact pathClosure pathTarget ⟨pathStep, pathEq⟩
        have sourceTargetIsSN :
            RawTerm.isStronglyNormalizing sourceTarget := by
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSource sourceClosure
          · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact (progressStep.2 rfl).elim
          · exact sourceIH sourceTarget ⟨sourceStep, sourceEq⟩
              uaContractumIsSN composeContractumIsSN
        · exact pathIH pathTarget ⟨pathStep, pathEq⟩
            sourceTargetIsSN uaContractumIsSN composeContractumIsSN
      · subst pathEq
        rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · subst pathEq
        subst targetEq
        have equivTargetIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.uaToEquiv proofRawTarget) := by
          by_cases equivEq :
              RawTerm.uaToEquiv proofRawSource =
                RawTerm.uaToEquiv proofRawTarget
          · rw [← equivEq]
            exact RawTerm.isStronglyNormalizing.intro
              (RawTerm.uaToEquiv proofRawSource) pathClosure
          · exact pathClosure (RawTerm.uaToEquiv proofRawTarget)
              ⟨RawStep.par.uaToEquivCong proofStep, equivEq⟩
        have sourceTargetIsSN :
            RawTerm.isStronglyNormalizing sourceTarget := by
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSource sourceClosure
          · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
        exact uaContractumIsSN equivTargetIsSN sourceTargetIsSN
      · subst targetEq
        have equivTargetIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.uaToEquiv proofRawTarget) := by
          by_cases pathEq :
              currentPath = RawTerm.uaToEquiv proofRawTarget
          · rw [← pathEq]
            exact RawTerm.isStronglyNormalizing.intro
              currentPath pathClosure
          · exact pathClosure (RawTerm.uaToEquiv proofRawTarget)
              ⟨pathStep, pathEq⟩
        have sourceTargetIsSN :
            RawTerm.isStronglyNormalizing sourceTarget := by
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSource sourceClosure
          · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
        exact uaContractumIsSN equivTargetIsSN sourceTargetIsSN
      · subst pathEq
        subst targetEq
        have composeTargetIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.pathCompose leftRawTarget rightRawTarget) := by
          by_cases composeEq :
              RawTerm.pathCompose leftRawSource rightRawSource =
                RawTerm.pathCompose leftRawTarget rightRawTarget
          · rw [← composeEq]
            exact RawTerm.isStronglyNormalizing.intro
              (RawTerm.pathCompose leftRawSource rightRawSource)
              pathClosure
          · exact pathClosure
              (RawTerm.pathCompose leftRawTarget rightRawTarget)
              ⟨RawStep.par.pathComposeCong leftStep rightStep, composeEq⟩
        have sourceTargetIsSN :
            RawTerm.isStronglyNormalizing sourceTarget := by
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSource sourceClosure
          · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
        exact composeContractumIsSN composeTargetIsSN sourceTargetIsSN
      · subst targetEq
        have composeTargetIsSN :
            RawTerm.isStronglyNormalizing
              (RawTerm.pathCompose leftRawTarget rightRawTarget) := by
          by_cases pathEq :
              currentPath = RawTerm.pathCompose leftRawTarget rightRawTarget
          · rw [← pathEq]
            exact RawTerm.isStronglyNormalizing.intro
              currentPath pathClosure
          · exact pathClosure
              (RawTerm.pathCompose leftRawTarget rightRawTarget)
              ⟨pathStep, pathEq⟩
        have sourceTargetIsSN :
            RawTerm.isStronglyNormalizing sourceTarget := by
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact RawTerm.isStronglyNormalizing.intro
              currentSource sourceClosure
          · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
        exact composeContractumIsSN composeTargetIsSN sourceTargetIsSN

/-- Typed wrapper for transp generic-closure SN preservation. -/
theorem Term.transp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIsSN : Term.isStronglyNormalizing typePath)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue)
    (uaContractumIsSN :
      ∀ {equivRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing equivRaw →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply equivRaw sourceTargetRaw))
    (composeContractumIsSN :
      ∀ {leftPathRaw rightPathRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing
          (RawTerm.pathCompose leftPathRaw rightPathRaw) →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightPathRaw
            (RawTerm.transp leftPathRaw sourceTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) :=
  RawTerm.transp_isStronglyNormalizing
    pathIsSN sourceIsSN uaContractumIsSN composeContractumIsSN

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
      obtain ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ :=
        RawStep.par.hcomp_inv progressStep.1
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


end LeanFX2
