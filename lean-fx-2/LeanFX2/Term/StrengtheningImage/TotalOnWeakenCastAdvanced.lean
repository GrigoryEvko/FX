import LeanFX2.Term.StrengtheningImage.TotalOnWeakenCastCore

/-! # Term/StrengtheningImage/TotalOnWeakenCastAdvanced

Total-on-weaken cast-heavy wrappers for oeqFunext, equivIntroHet, and boolElim.
-/

namespace LeanFX2

namespace Term

/-- `Term.weaken` arm reshape for `Term.oeqFunext`.

Inner cast on `pointwiseProof` via `oeqFunextPointwiseType_rename`. -/
theorem weaken_oeqFunext_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw) :
    Term.weaken newType
        (Term.oeqFunext (context := context) domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof) =
      Term.oeqFunext (context := context.cons newType)
        (domainType.rename RawRenaming.weaken)
        (codomainType.rename RawRenaming.weaken)
        (leftFunctionRaw.rename RawRenaming.weaken)
        (rightFunctionRaw.rename RawRenaming.weaken)
        ((oeqFunextPointwiseType_rename RawRenaming.weaken
          domainType codomainType leftFunctionRaw rightFunctionRaw) ▸
          (Term.rename (TermRenaming.weakenStep context newType) pointwiseProof :
            Term (context.cons newType)
              ((oeqFunextPointwiseType domainType codomainType
                leftFunctionRaw rightFunctionRaw).rename RawRenaming.weaken)
              (pointwiseRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 1-IH non-binder totality through INNER Eq.mpr cast: `Term.oeqFunext`. -/
theorem isTotalOnWeaken_oeqFunext {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw}
    (pointwiseIH : IsTotalOnWeaken pointwiseProof) :
    IsTotalOnWeaken (Term.oeqFunext (context := context)
      domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof) := by
  intro newType
  rw [weaken_oeqFunext_unfolds newType domainType codomainType
    leftFunctionRaw rightFunctionRaw pointwiseProof]
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next leftFails =>
          exfalso
          have leftSuccess :
              (leftFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftFunctionRaw := by
            have := RawTerm.partialStrengthen?_rename_some leftFunctionRaw
              RawRenaming.weaken RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back
              (fun position => rfl)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [leftSuccess] at leftFails
          cases leftFails
      · split
        · next rightFails =>
            exfalso
            have rightSuccess :
                (rightFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightFunctionRaw := by
              have := RawTerm.partialStrengthen?_rename_some rightFunctionRaw
                RawRenaming.weaken RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back
                (fun position => rfl)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [rightSuccess] at rightFails
            cases rightFails
        · split
          · next pointwiseRecurse =>
              exfalso
              -- INNER CAST: pointwiseRecurse : (eq ▸ Term.rename _ pp).partialStrengthenTyped? = none
              have totHyp := pointwiseIH newType
              dsimp only [strengthenTyped?] at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename
                    (TermRenaming.weakenStep context newType) pointwiseProof)
                  (oeqFunextPointwiseType_rename RawRenaming.weaken
                    domainType codomainType leftFunctionRaw rightFunctionRaw)
              dsimp only [strengthenTyped?] at invariance
              rw [pointwiseRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · rfl

/-- `Term.weaken` arm reshape for `Term.equivIntroHet`.

Two inner casts on `leftInv` and `rightInv`. -/
theorem weaken_equivIntroHet_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (newType : Ty level scope)
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw)
    (rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw) :
    Term.weaken newType
        (Term.equivIntroHet forward backward leftInv rightInv) =
      Term.equivIntroHet
        (Term.weaken newType forward)
        (Term.weaken newType backward)
        ((equivIntroHetLeftInverseType_rename RawRenaming.weaken
          carrierA forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) leftInv :
            Term (context.cons newType)
              ((equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (leftInvRaw.rename RawRenaming.weaken)))
        ((equivIntroHetRightInverseType_rename RawRenaming.weaken
          carrierB forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) rightInv :
            Term (context.cons newType)
              ((equivIntroHetRightInverseType carrierB forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (rightInvRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 4-IH non-binder totality through TWO INNER Eq.mpr casts: `Term.equivIntroHet`. -/
theorem isTotalOnWeaken_equivIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward : Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward : Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw}
    {rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw}
    (forwardIH : IsTotalOnWeaken forward)
    (backwardIH : IsTotalOnWeaken backward)
    (leftInvIH : IsTotalOnWeaken leftInv)
    (rightInvIH : IsTotalOnWeaken rightInv) :
    IsTotalOnWeaken (Term.equivIntroHet forward backward leftInv rightInv) := by
  intro newType
  rw [weaken_equivIntroHet_unfolds newType forward backward leftInv rightInv]
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next forwardRecurse =>
          exfalso
          have totHyp := forwardIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType forward))) = true :=
            forwardRecurse ▸ totHyp
          cases this
      · split
        · next backwardRecurse =>
            exfalso
            have totHyp := backwardIH newType
            dsimp only [strengthenTyped?] at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType backward))) = true :=
              backwardRecurse ▸ totHyp
            cases this
        · split
          · next leftInvRecurse =>
              exfalso
              -- INNER CAST on leftInv
              have totHyp := leftInvIH newType
              dsimp only [strengthenTyped?] at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename (TermRenaming.weakenStep context newType) leftInv)
                  (equivIntroHetLeftInverseType_rename RawRenaming.weaken
                    carrierA forwardRaw backwardRaw)
              dsimp only [strengthenTyped?] at invariance
              rw [leftInvRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · split
            · next rightInvRecurse =>
                exfalso
                -- INNER CAST on rightInv
                have totHyp := rightInvIH newType
                dsimp only [strengthenTyped?] at totHyp
                have invariance :=
                  strengthenTyped?_isSome_castInvariant
                    (Term.rename (TermRenaming.weakenStep context newType) rightInv)
                    (equivIntroHetRightInverseType_rename RawRenaming.weaken
                      carrierB forwardRaw backwardRaw)
                dsimp only [strengthenTyped?] at invariance
                rw [rightInvRecurse] at invariance
                rw [totHyp] at invariance
                cases invariance
            · rfl

/-- `Term.weaken` arm reshape for `Term.boolElim`.

Combined OUTER + 2 INNER casts (thenBranch, elseBranch).  Cumulative
Eq.mpr blocking; resolved by the same castInvariant strategy applied
at all three cast sites.  Proved by `rfl`. -/
theorem weaken_boolElim_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (newType : Ty level scope)
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.weaken newType (Term.boolElim scrutinee thenBranch elseBranch) =
      ((Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
          RawRenaming.weaken).symm ▸
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((motiveType.subst0 Ty.bool scrutineeRaw).rename RawRenaming.weaken)
         (RawTerm.boolElim scrutineeRaw thenRaw elseRaw).weaken) := by
  rfl

/-- 3-IH non-binder totality through OUTER + 2 INNER Eq.mpr casts: `Term.boolElim`. -/
theorem isTotalOnWeaken_boolElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term context Ty.bool scrutineeRaw}
    {thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (thenIH : IsTotalOnWeaken thenBranch)
    (elseIH : IsTotalOnWeaken elseBranch) :
    IsTotalOnWeaken (Term.boolElim scrutinee thenBranch elseBranch) := by
  intro newType
  -- Discharge OUTER cast first via suffices + castInvariant
  suffices uncastTotality :
      (strengthenTyped?
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_boolElim_unfolds newType scrutinee thenBranch elseBranch]
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next motiveFails =>
      exfalso
      have motiveSuccess :
          (motiveType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some motiveType := by
        have := Ty.partialStrengthen?_rename_some motiveType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [motiveSuccess] at motiveFails
      cases motiveFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        dsimp only [strengthenTyped?] at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next thenRecurse =>
          exfalso
          -- INNER CAST on thenBranch
          have totHyp := thenIH newType
          dsimp only [strengthenTyped?] at totHyp
          change
            (partialStrengthenTyped?
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
                RawRenaming.weaken)
          dsimp only [strengthenTyped?] at invariance
          -- invariance : isSome cast = isSome uncast
          -- totHyp : isSome uncast = true
          -- => isSome cast = true
          -- thenRecurse : cast = none
          -- => isSome cast = false (via congrArg)
          -- Combine: true = false
          have isSomeCastTrue : _ = _ := invariance.trans totHyp
          have isSomeCastFalse : _ = _ := congrArg Option.isSome thenRecurse
          have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
          cases contradiction
      · split
        · next elseRecurse =>
            exfalso
            have totHyp := elseIH newType
            dsimp only [strengthenTyped?] at totHyp
            change
              (partialStrengthenTyped?
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
            have invariance :=
              strengthenTyped?_isSome_castInvariant
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
                  RawRenaming.weaken)
            dsimp only [strengthenTyped?] at invariance
            have isSomeCastTrue : _ = _ := invariance.trans totHyp
            have isSomeCastFalse : _ = _ := congrArg Option.isSome elseRecurse
            have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
            cases contradiction
        · rfl

end Term

end LeanFX2
