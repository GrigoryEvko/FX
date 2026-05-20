import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Reducibility.NeutralSNFoundation.BoolNat

Boolean recursor SN preservation.  Sole surviving live theorem
after the Tait `IsNeutral` cascade was retired in favour of Kripke
step-indexed reducibility: `RawTerm.boolElim_isStronglyNormalizing`
remains as the generic three-subterm SN closure used by
`Term.SN.DirectCases`. -/

namespace LeanFX2

/-- Boolean eliminator SN preservation.  Congruence arms recurse
through the three SN subterms; true/false ι arms return the
corresponding branch target. -/
theorem RawTerm.boolElim_isStronglyNormalizing {scope : Nat}
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
    ∀ {scrutinee : RawTerm scope},
      RawTerm.isStronglyNormalizing scrutinee →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim scrutinee thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen thenClosure thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure elseIH =>
      intro scrutinee scrutineeIsSN
      induction scrutineeIsSN with
      | intro currentScrutinee scrutineeClosure scrutineeIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.boolElim currentScrutinee currentThen currentElse) ?_
        intro target progressStep
        cases RawStep.par.boolElim_inv progressStep.1 with
        | inl congruentStep =>
          rcases congruentStep with
            ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
              scrutineeStep, thenStep, elseStep⟩
          subst targetEq
          by_cases thenEq : currentThen = thenTarget
          · subst thenEq
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact (progressStep.2 rfl).elim
              · exact scrutineeIH scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            · have scrutineeTargetIsSN :
                  RawTerm.isStronglyNormalizing scrutineeTarget := by
                by_cases scrutineeEq : currentScrutinee = scrutineeTarget
                · subst scrutineeEq
                  exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                    scrutineeClosure
                · exact scrutineeClosure scrutineeTarget
                    ⟨scrutineeStep, scrutineeEq⟩
              exact elseIH elseTarget ⟨elseStep, elseEq⟩
                scrutineeTargetIsSN
          · have elseTargetIsSN :
                RawTerm.isStronglyNormalizing elseTarget := by
              by_cases elseEq : currentElse = elseTarget
              · subst elseEq
                exact RawTerm.isStronglyNormalizing.intro currentElse
                  elseClosure
              · exact elseClosure elseTarget ⟨elseStep, elseEq⟩
            have scrutineeTargetIsSN :
                RawTerm.isStronglyNormalizing scrutineeTarget := by
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                  scrutineeClosure
              · exact scrutineeClosure scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            exact thenIH thenTarget ⟨thenStep, thenEq⟩
              elseTargetIsSN scrutineeTargetIsSN
        | inr iotaStep =>
          cases iotaStep with
          | inl trueStep =>
            rcases trueStep with
              ⟨thenTarget, targetEq, _scrutineeStep, thenStep⟩
            rw [targetEq]
            by_cases thenEq : currentThen = thenTarget
            · subst thenEq
              exact RawTerm.isStronglyNormalizing.intro currentThen
                thenClosure
            · exact thenClosure thenTarget ⟨thenStep, thenEq⟩
          | inr falseStep =>
            rcases falseStep with
              ⟨elseTarget, targetEq, _scrutineeStep, elseStep⟩
            rw [targetEq]
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              exact RawTerm.isStronglyNormalizing.intro currentElse
                elseClosure
            · exact elseClosure elseTarget ⟨elseStep, elseEq⟩

end LeanFX2
