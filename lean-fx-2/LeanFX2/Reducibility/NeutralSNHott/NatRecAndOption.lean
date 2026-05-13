import LeanFX2.Reducibility.NeutralSNHott.NatElim

/-! # LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption

K12.20.BA natRec SN preservation: `natRec_natZero` /
`natRec_natSucc` / `natRec` (raw + Term wrappers); plus
`optionSome` / `optionMatch_optionSome` (raw + Term wrappers).

## Root status

Layer 3 metatheory leaf.  Fourth and final slice of NeutralSNHott. -/

namespace LeanFX2


/-- Nat-zero ι SN expansion for `natRec`.

For a canonical zero scrutinee, `natRec` reduces to the zero branch.
The successor branch remains in the statement because congruent
reductions may step under it before the ι rule fires. -/
theorem RawTerm.natRec_natZero_isStronglyNormalizing
    {scope : Nat}
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec RawTerm.natZero zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero zeroClosure zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure succIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natRec RawTerm.natZero currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natRec_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | ⟨zeroTarget, targetEq, _scrutineeStep, zeroStep⟩
        | ⟨predecessorTarget, _zeroTarget, _succTarget, _targetEq,
            scrutineeStep, _zeroStep, _succStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact (progressStep.2 rfl).elim
          · exact succIH succTarget ⟨succStep, succEq⟩
        · have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩ succTargetIsSN
      · rw [targetEq]
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          exact RawTerm.isStronglyNormalizing.intro currentZero zeroClosure
        · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
      · have succEqZero :
            RawTerm.natSucc predecessorTarget =
              (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        nomatch succEqZero

/-- Typed nat-zero ι SN expansion for `Term.natRec`. -/
theorem Term.natRec_natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch) :
    Term.isStronglyNormalizing
      (Term.natRec Term.natZero zeroBranch succBranch) :=
  RawTerm.natRec_natZero_isStronglyNormalizing
    zeroIsSN succIsSN

/-- Nat-successor ι SN expansion for `natRec`.

For a canonical successor scrutinee, `natRec` reduces to
`succBranch predecessor (natRec predecessor zeroBranch succBranch)`.
The recursive call and the full contractum are explicit premises:
this raw lemma only transports SN backward across the ι redex and
congruent reducts. -/
theorem RawTerm.natRec_natSucc_isStronglyNormalizing
    {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec predecessor zeroBranch succBranch) →
      RawTerm.isStronglyNormalizing
        (RawTerm.app (RawTerm.app succBranch predecessor)
          (RawTerm.natRec predecessor zeroBranch succBranch)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec
          (RawTerm.natSucc predecessor) zeroBranch succBranch) := by
  induction predecessorIsSN with
  | intro currentPredecessor predecessorClosure predecessorIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN recursiveCallIsSN contractumIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natRec
            (RawTerm.natSucc currentPredecessor)
            currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natRec_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predecessorTarget, zeroTarget, succTarget, targetEq,
              scrutineeStep, zeroStep, succStep⟩
        · obtain ⟨predecessorTarget, scrutineeTargetEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          have predecessorTargetIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget := by
            by_cases predecessorEq :
                currentPredecessor = predecessorTarget
            · subst predecessorEq
              exact RawTerm.isStronglyNormalizing.intro
                currentPredecessor predecessorClosure
            · exact predecessorClosure predecessorTarget
                ⟨predecessorStep, predecessorEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have recursiveCallTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natRec
                  predecessorTarget zeroTarget succTarget) := by
            by_cases recursiveCallEq :
                RawTerm.natRec
                    currentPredecessor currentZero currentSucc =
                  RawTerm.natRec
                    predecessorTarget zeroTarget succTarget
            · rw [← recursiveCallEq]
              exact recursiveCallIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                recursiveCallIsSN
                ⟨RawStep.par.natRec predecessorStep zeroStep succStep,
                  recursiveCallEq⟩
          have contractumTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app (RawTerm.app succTarget predecessorTarget)
                  (RawTerm.natRec
                    predecessorTarget zeroTarget succTarget)) := by
            by_cases contractumEq :
                RawTerm.app
                    (RawTerm.app currentSucc currentPredecessor)
                    (RawTerm.natRec
                      currentPredecessor currentZero currentSucc) =
                  RawTerm.app
                    (RawTerm.app succTarget predecessorTarget)
                    (RawTerm.natRec
                      predecessorTarget zeroTarget succTarget)
            · rw [← contractumEq]
              exact contractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                contractumIsSN
                ⟨RawStep.par.app
                    (RawStep.par.app succStep predecessorStep)
                    (RawStep.par.natRec
                      predecessorStep zeroStep succStep),
                  contractumEq⟩
          by_cases predecessorEq : currentPredecessor = predecessorTarget
          · subst predecessorEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  recursiveCallTargetIsSN contractumTargetIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN recursiveCallTargetIsSN
                contractumTargetIsSN
          · exact predecessorIH predecessorTarget
              ⟨predecessorStep, predecessorEq⟩
              zeroTargetIsSN succTargetIsSN
              recursiveCallTargetIsSN contractumTargetIsSN
        · obtain ⟨_predecessorTarget, natZeroEq, _predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          nomatch natZeroEq
        · obtain ⟨_predecessorTargetFromScrutinee, successorEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          injection successorEq with _scopeEq predecessorTargetEq
          subst targetEq
          have predecessorStepToTarget :
              RawStep.par currentPredecessor predecessorTarget := by
            rw [predecessorTargetEq]
            exact predecessorStep
          have recursiveCallTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natRec
                  predecessorTarget zeroTarget succTarget) := by
            by_cases recursiveCallEq :
                RawTerm.natRec
                    currentPredecessor currentZero currentSucc =
                  RawTerm.natRec
                    predecessorTarget zeroTarget succTarget
            · rw [← recursiveCallEq]
              exact recursiveCallIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                recursiveCallIsSN
                ⟨RawStep.par.natRec
                    predecessorStepToTarget zeroStep succStep,
                  recursiveCallEq⟩
          have contractumTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app (RawTerm.app succTarget predecessorTarget)
                  (RawTerm.natRec
                    predecessorTarget zeroTarget succTarget)) := by
            by_cases contractumEq :
                RawTerm.app
                    (RawTerm.app currentSucc currentPredecessor)
                    (RawTerm.natRec
                      currentPredecessor currentZero currentSucc) =
                  RawTerm.app
                    (RawTerm.app succTarget predecessorTarget)
                    (RawTerm.natRec
                      predecessorTarget zeroTarget succTarget)
            · rw [← contractumEq]
              exact contractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                contractumIsSN
                ⟨RawStep.par.app
                    (RawStep.par.app succStep predecessorStepToTarget)
                    (RawStep.par.natRec
                      predecessorStepToTarget zeroStep succStep),
                  contractumEq⟩
          exact contractumTargetIsSN

/-- Typed nat-successor ι SN expansion for `Term.natRec`. -/
theorem Term.natRec_natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (recursiveCallIsSN :
      Term.isStronglyNormalizing
        (Term.natRec predecessor zeroBranch succBranch))
    (contractumIsSN :
      Term.isStronglyNormalizing
        (Term.app (Term.app succBranch predecessor)
          (Term.natRec predecessor zeroBranch succBranch))) :
    Term.isStronglyNormalizing
      (Term.natRec
        (Term.natSucc predecessor) zeroBranch succBranch) :=
  RawTerm.natRec_natSucc_isStronglyNormalizing
    predecessorIsSN zeroIsSN succIsSN recursiveCallIsSN contractumIsSN

/-- General SN preservation for `natRec`.

The successor contractum is supplied as an explicit closure over every
strongly-normalizing predecessor and every strongly-normalizing branch
candidate.  This matches the current SN-output endpoint: the theorem
transports normalization through congruent recursor reductions and the
zero/successor ι cases without claiming full recursive Reducible
closure at the motive. -/
theorem RawTerm.natRec_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      (∀ {predecessor zeroTarget succTarget : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessor →
        RawTerm.isStronglyNormalizing zeroTarget →
        RawTerm.isStronglyNormalizing succTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTarget predecessor)
            (RawTerm.natRec predecessor zeroTarget succTarget))) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec scrutinee zeroBranch succBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN contractumClosure
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natRec currentScrutinee currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natRec_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, targetEq, scrutineeStep, zeroStep⟩
          | ⟨predecessorTarget, zeroTarget, succTarget, targetEq,
              scrutineeStep, zeroStep, succStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN contractumClosure
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              zeroTargetIsSN succTargetIsSN contractumClosure
        · rw [targetEq]
          by_cases zeroEq : currentZero = zeroTarget
          · subst zeroEq
            exact RawTerm.isStronglyNormalizing.intro
              currentZero zeroClosure
          · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
        · subst targetEq
          have successorScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natSucc predecessorTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.natSucc predecessorTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (RawTerm.isStronglyNormalizing.intro
                  currentScrutinee scrutineeClosure)
                ⟨scrutineeStep, scrutineeEq⟩
          have predecessorIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget :=
            RawTerm.natSucc_predecessor_isStronglyNormalizing
              successorScrutineeIsSN
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact contractumClosure
            predecessorIsSN zeroTargetIsSN succTargetIsSN

/-- Typed wrapper for general `natRec` SN preservation. -/
theorem Term.natRec_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.natRec scrutinee zeroBranch succBranch) :=
  RawTerm.natRec_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN contractumIsSN

/-- **K12.20.W optionSome SN preservation**.  Sister to
`natSucc_isStronglyNormalizing` — unary cong-only ctor with
`optionSome_inv` for step inversion + `RawTerm.optionSome`
injectivity for the parProgress disequality. -/
theorem RawTerm.optionSome_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.optionSome valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionSome currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.optionSome_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.optionSome valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- Option-some ι SN expansion for the eliminator.

The option candidate stores the eliminator result as an SN-output
closure.  For the canonical `Some` branch, the ι target is
`app someBranch value`; this lemma lifts SN of that target through
all congruent reductions of the scrutinee and branches. -/
theorem RawTerm.optionMatch_optionSome_isStronglyNormalizing
    {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    ∀ {noneBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing noneBranch →
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app someBranch valueTerm) →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch
          (RawTerm.optionSome valueTerm) noneBranch someBranch) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro noneBranch noneIsSN
    induction noneIsSN with
    | intro currentNone noneClosure noneIH =>
      intro someBranch someIsSN someAppIsSN
      induction someIsSN with
      | intro currentSome someClosure someIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.optionMatch
            (RawTerm.optionSome currentValue) currentNone currentSome) ?_
        intro target progressStep
        rcases RawStep.par.optionMatch_inv progressStep.1 with
          ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
            scrutineeStep, noneStep, someStep⟩
          | ⟨noneTarget, targetEq, scrutineeStep, noneStep⟩
          | ⟨valueTarget, someTarget, targetEq, scrutineeStep, someStep⟩
        · obtain ⟨valueTarget, scrutineeTargetEq, valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          by_cases valueEq : currentValue = valueTarget
          · subst valueEq
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact (progressStep.2 rfl).elim
              · have someAppTargetIsSN :
                    RawTerm.isStronglyNormalizing
                      (RawTerm.app someTarget currentValue) := by
                  by_cases appEq :
                      RawTerm.app currentSome currentValue =
                        RawTerm.app someTarget currentValue
                  · rw [← appEq]
                    exact someAppIsSN
                  · exact RawTerm.isStronglyNormalizing.step_preserves
                      someAppIsSN
                      ⟨RawStep.par.app someStep
                        (RawStep.par.refl currentValue), appEq⟩
                exact someIH someTarget ⟨someStep, someEq⟩
                  someAppTargetIsSN
            · have someTargetIsSN :
                  RawTerm.isStronglyNormalizing someTarget := by
                by_cases someEq : currentSome = someTarget
                · subst someEq
                  exact RawTerm.isStronglyNormalizing.intro
                    currentSome someClosure
                · exact someClosure someTarget ⟨someStep, someEq⟩
              have someAppTargetIsSN :
                  RawTerm.isStronglyNormalizing
                    (RawTerm.app someTarget currentValue) := by
                by_cases appEq :
                    RawTerm.app currentSome currentValue =
                      RawTerm.app someTarget currentValue
                · rw [← appEq]
                  exact someAppIsSN
                · exact RawTerm.isStronglyNormalizing.step_preserves
                    someAppIsSN
                    ⟨RawStep.par.app someStep
                      (RawStep.par.refl currentValue), appEq⟩
              exact noneIH noneTarget ⟨noneStep, noneEq⟩
                someTargetIsSN someAppTargetIsSN
          · have noneTargetIsSN :
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
            have someAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app someTarget valueTarget) := by
              by_cases appEq :
                  RawTerm.app currentSome currentValue =
                    RawTerm.app someTarget valueTarget
              · rw [← appEq]
                exact someAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  someAppIsSN
                  ⟨RawStep.par.app someStep valueStep, appEq⟩
            exact valueIH valueTarget ⟨valueStep, valueEq⟩
              noneTargetIsSN someTargetIsSN someAppTargetIsSN
        · obtain ⟨valueTarget, optionSomeEq, _valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          nomatch optionSomeEq
        · obtain ⟨valueTargetFromScrutinee, optionSomeEq, valueStep⟩ :=
            RawStep.par.optionSome_inv scrutineeStep
          injection optionSomeEq with _scopeEq valueTargetEq
          subst targetEq
          have valueStepToTarget :
              RawStep.par currentValue valueTarget := by
            rw [valueTargetEq]
            exact valueStep
          have someAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app someTarget valueTarget) := by
            by_cases appEq :
                RawTerm.app currentSome currentValue =
                  RawTerm.app someTarget valueTarget
            · rw [← appEq]
              exact someAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                someAppIsSN
                ⟨RawStep.par.app someStep valueStepToTarget, appEq⟩
          exact someAppTargetIsSN

/-- Typed option-some ι SN expansion for `Term.optionMatch`. -/
theorem Term.optionMatch_optionSome_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {valueRaw noneRaw someRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (someAppIsSN :
      Term.isStronglyNormalizing (Term.app someBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.optionMatch (Term.optionSome valueTerm) noneBranch someBranch) :=
  RawTerm.optionMatch_optionSome_isStronglyNormalizing
    valueIsSN noneIsSN someIsSN someAppIsSN



end LeanFX2
