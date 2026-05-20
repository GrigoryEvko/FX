import LeanFX2.Term.RenameInjective.Core
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro

/-! # Term/RenameInjective/EquivIntro

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

/-- Inversion for the shared `RawTerm.equivIntro` raw head.

The raw head is intentionally shared by the canonical identity equivalence,
its universe-Id witness, heterogeneous equivalence introduction, and
heterogeneous univalence introduction.  Keeping the target type free avoids
the dependent-elimination wall at call sites that only know the raw shape. -/
def Term.equivIntro_inv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {targetType : Ty level scope}
    {forwardRaw backwardRaw : RawTerm scope}
    (genericTerm :
      Term context targetType (RawTerm.equivIntro forwardRaw backwardRaw)) :
    (Σ' (carrier : Ty level scope)
        (_ :
          forwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          backwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ : targetType = Ty.equiv carrier carrier),
        HEq genericTerm (Term.equivReflId (context := context) carrier)) ⊕'
    (Σ' (innerLevel : UniverseLevel)
        (innerLevelLt : innerLevel.toNat + 1 ≤ level)
        (carrier : Ty level scope)
        (carrierRaw : RawTerm scope)
        (_ :
          forwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          backwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          targetType =
            Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw
              carrierRaw),
        HEq genericTerm
          (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
            carrier carrierRaw)) ⊕'
    (Σ' (carrierLeft carrierRight : Ty level scope)
        (leftInvRaw rightInvRaw : RawTerm scope)
        (forward :
          Term context (Ty.arrow carrierLeft carrierRight) forwardRaw)
        (backward :
          Term context (Ty.arrow carrierRight carrierLeft) backwardRaw)
        (leftInv :
          Term context
            (equivIntroHetLeftInverseType carrierLeft forwardRaw backwardRaw)
            leftInvRaw)
        (rightInv :
          Term context
            (equivIntroHetRightInverseType carrierRight forwardRaw backwardRaw)
            rightInvRaw)
        (_ : targetType = Ty.equiv carrierLeft carrierRight),
        HEq genericTerm
          (Term.equivIntroHet forward backward leftInv rightInv)) ⊕'
    (Σ' (innerLevel : UniverseLevel)
        (innerLevelLt : innerLevel.toNat + 1 ≤ level)
        (carrierLeft carrierRight : Ty level scope)
        (carrierLeftRaw carrierRightRaw : RawTerm scope)
        (equivWitness :
          Term context (Ty.equiv carrierLeft carrierRight)
            (RawTerm.equivIntro forwardRaw backwardRaw))
        (_ :
          targetType =
            Ty.id (Ty.universe innerLevel innerLevelLt) carrierLeftRaw
              carrierRightRaw),
        HEq genericTerm
          (Term.uaIntroHet innerLevel innerLevelLt carrierLeftRaw
            carrierRightRaw equivWitness)) := by
  cases genericTerm
  case equivReflId carrier =>
    exact PSum.inl ⟨carrier, rfl, rfl, rfl, HEq.rfl⟩
  case equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
    exact PSum.inr (PSum.inl
      ⟨innerLevel, innerLevelLt, carrier, carrierRaw, rfl, rfl, rfl,
        HEq.rfl⟩)
  case equivIntroHet forward backward leftInv rightInv =>
    exact PSum.inr (PSum.inr (PSum.inl
      ⟨_, _, _, _, forward, backward, leftInv, rightInv, rfl, HEq.rfl⟩))
  case uaIntroHet innerLevel innerLevelLt carrierLeft carrierRight
      carrierLeftRaw carrierRightRaw equivWitness =>
    exact PSum.inr (PSum.inr (PSum.inr
      ⟨innerLevel, innerLevelLt, carrierLeft, carrierRight, carrierLeftRaw,
        carrierRightRaw, equivWitness, rfl, HEq.rfl⟩))

theorem Term.rename_injective_atEquivIntroEquiv_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  have viewB := Term.equivIntro_inv termB
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrierLeft, forwardEqA, backwardEqA, typeEqA, termHEqA⟩ :=
      reflViewA
    cases typeEqA
    cases forwardEqA
    cases backwardEqA
    cases termHEqA
    cases viewB with
    | inl reflViewB =>
      obtain ⟨carrierRight, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
        reflViewB
      cases typeEqB
      cases forwardEqB
      cases backwardEqB
      cases termHEqB
      exact rfl
    | inr restViewB =>
      cases restViewB with
      | inl idViewB =>
        obtain ⟨innerLevelB, innerLevelLtB, carrierRight, carrierRawB,
          forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
        cases typeEqB
      | inr restViewB =>
        cases restViewB with
        | inl introViewB =>
          obtain ⟨carrierLeftB, carrierRightB, leftInvRawB, rightInvRawB,
            forwardB, backwardB, leftInvB, rightInvB, typeEqB,
            termHEqB⟩ := introViewB
          cases typeEqB
          cases termHEqB
          dsimp only [Term.rename] at renameEq
          cases renameEq
        | inr uaViewB =>
          obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB, carrierRightB,
            carrierLeftRawB, carrierRightRawB, equivWitnessB, typeEqB,
            termHEqB⟩ := uaViewB
          cases typeEqB
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevelA, innerLevelLtA, carrierLeft, carrierRawA,
        forwardEqA, backwardEqA, typeEqA, termHEqA⟩ := idViewA
      cases typeEqA
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeftA, carrierRightA, leftInvRawA, rightInvRawA,
          forwardA, backwardA, leftInvA, rightInvA, typeEqA,
          termHEqA⟩ := introViewA
        cases typeEqA
        cases termHEqA
        cases viewB with
        | inl reflViewB =>
          obtain ⟨carrierRight, forwardEqB, backwardEqB, typeEqB,
            termHEqB⟩ := reflViewB
          cases typeEqB
          cases forwardEqB
          cases backwardEqB
          cases termHEqB
          dsimp only [Term.rename] at renameEq
          cases renameEq
        | inr restViewB =>
          cases restViewB with
          | inl idViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierRight, carrierRawB,
              forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
            cases typeEqB
          | inr restViewB =>
            cases restViewB with
            | inl introViewB =>
              obtain ⟨carrierLeftB, carrierRightB, leftInvRawB,
                rightInvRawB, forwardB, backwardB, leftInvB, rightInvB,
                typeEqB, termHEqB⟩ := introViewB
              cases typeEqB
              cases termHEqB
              dsimp only [Term.rename] at renameEq
              injection renameEq with contextEq carrierLeftRenameEq
                carrierRightRenameEq forwardRawRenameEq backwardRawRenameEq
                backwardRawRenameEqAgain leftInvRawRenameEq rightInvRawRenameEq
                forwardRenameEq backwardRenameEq leftInvRenameEq
                rightInvRenameEq
              have leftInvRawEq : leftInvRawA = leftInvRawB :=
                RawTerm.rename_injective_under_injective_renaming leftInvRawA
                  rhoInjective leftInvRawB leftInvRawRenameEq
              have rightInvRawEq : rightInvRawA = rightInvRawB :=
                RawTerm.rename_injective_under_injective_renaming
                  rightInvRawA rhoInjective rightInvRawB rightInvRawRenameEq
              have forwardHEq : HEq forwardA forwardB :=
                childInjective forwardA forwardB (heq_of_eq forwardRenameEq)
              have backwardHEq : HEq backwardA backwardB :=
                childInjective backwardA backwardB (heq_of_eq backwardRenameEq)
              have leftInvRenameUncastHEq :
                  HEq (Term.rename termRenaming leftInvA)
                    (Term.rename termRenaming leftInvB) :=
                HEq.trans
                  (HEq.symm
                    (termRenameInjectiveCastHEq
                      (equivIntroHetLeftInverseType_rename rho carrierA
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming leftInvA)))
                  (HEq.trans leftInvRenameEq
                    (termRenameInjectiveCastHEq
                      (equivIntroHetLeftInverseType_rename rho carrierA
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming leftInvB)))
              have rightInvRenameUncastHEq :
                  HEq (Term.rename termRenaming rightInvA)
                    (Term.rename termRenaming rightInvB) :=
                HEq.trans
                  (HEq.symm
                    (termRenameInjectiveCastHEq
                      (equivIntroHetRightInverseType_rename rho carrierB
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming rightInvA)))
                  (HEq.trans rightInvRenameEq
                    (termRenameInjectiveCastHEq
                      (equivIntroHetRightInverseType_rename rho carrierB
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming rightInvB)))
              have leftInvHEq : HEq leftInvA leftInvB :=
                childInjective leftInvA leftInvB leftInvRenameUncastHEq
              have rightInvHEq : HEq rightInvA rightInvB :=
                childInjective rightInvA rightInvB rightInvRenameUncastHEq
              exact eq_of_heq
                (Term.equivIntroHet_HEq_congr rfl rfl rfl rfl
                  leftInvRawEq rightInvRawEq forwardHEq
                  backwardHEq leftInvHEq rightInvHEq)
            | inr uaViewB =>
              obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB,
                carrierRightB, carrierLeftRawB, carrierRightRawB,
                equivWitnessB, typeEqB, termHEqB⟩ := uaViewB
              cases typeEqB
      | inr uaViewA =>
        obtain ⟨innerLevelA, innerLevelLtA, carrierLeftA, carrierRightA,
          carrierLeftRawA, carrierRightRawA, equivWitnessA, typeEqA,
          termHEqA⟩ := uaViewA
        cases typeEqA

theorem Term.rename_injective_atEquivIntroUniverseId_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {leftRaw rightRaw : RawTerm sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx (Ty.id (Ty.universe innerLevel innerLevelLt)
        leftRaw rightRaw)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  have viewB := Term.equivIntro_inv termB
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrierA, forwardEqA, backwardEqA, typeEqA, termHEqA⟩ :=
      reflViewA
    cases typeEqA
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevelA, innerLevelLtA, carrierA, carrierRawA,
        forwardEqA, backwardEqA, typeEqA, termHEqA⟩ := idViewA
      cases typeEqA
      cases forwardEqA
      cases backwardEqA
      cases termHEqA
      cases viewB with
      | inl reflViewB =>
        obtain ⟨carrierB, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
          reflViewB
        cases typeEqB
      | inr restViewB =>
        cases restViewB with
        | inl idViewB =>
          obtain ⟨innerLevelB, innerLevelLtB, carrierB, carrierRawB,
            forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
          cases typeEqB
          cases forwardEqB
          cases backwardEqB
          cases termHEqB
          dsimp only [Term.rename] at renameEq
          injection renameEq with contextEq innerLevelEq innerLevelLtEq
            carrierRenameEq carrierRawRenameEq
          cases innerLevelEq
          cases innerLevelLtEq
          have carrierEq : carrierA = carrierB :=
            Ty.rename_injective_under_injective_renaming carrierA rhoInjective
              carrierB carrierRenameEq
          exact eq_of_heq
            (Term.equivReflIdAtId_HEq_congr carrierEq rfl)
        | inr restViewB =>
          cases restViewB with
          | inl introViewB =>
            obtain ⟨carrierLeftB, carrierRightB, leftInvRawB, rightInvRawB,
              forwardB, backwardB, leftInvB, rightInvB, typeEqB,
              termHEqB⟩ := introViewB
            cases typeEqB
          | inr uaViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB, carrierRightB,
              carrierLeftRawB, carrierRightRawB, equivWitnessB, typeEqB,
              termHEqB⟩ := uaViewB
            cases typeEqB
            cases termHEqB
            dsimp only [Term.rename] at renameEq
            cases renameEq
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeftA, carrierRightA, leftInvRawA, rightInvRawA,
          forwardA, backwardA, leftInvA, rightInvA, typeEqA,
          termHEqA⟩ := introViewA
        cases typeEqA
      | inr uaViewA =>
        obtain ⟨innerLevelA, innerLevelLtA, carrierLeftA, carrierRightA,
          carrierLeftRawA, carrierRightRawA, equivWitnessA, typeEqA,
          termHEqA⟩ := uaViewA
        cases typeEqA
        cases termHEqA
        cases viewB with
        | inl reflViewB =>
          obtain ⟨carrierB, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
            reflViewB
          cases typeEqB
        | inr restViewB =>
          cases restViewB with
          | inl idViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierB, carrierRawB,
              forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
            cases typeEqB
            cases forwardEqB
            cases backwardEqB
            cases termHEqB
            dsimp only [Term.rename] at renameEq
            cases renameEq
          | inr restViewB =>
            cases restViewB with
            | inl introViewB =>
              obtain ⟨carrierLeftB, carrierRightB, leftInvRawB,
                rightInvRawB, forwardB, backwardB, leftInvB, rightInvB,
                typeEqB, termHEqB⟩ := introViewB
              cases typeEqB
            | inr uaViewB =>
              obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB,
                carrierRightB, carrierLeftRawB, carrierRightRawB,
                equivWitnessB, typeEqB, termHEqB⟩ := uaViewB
              cases typeEqB
              cases termHEqB
              dsimp only [Term.rename] at renameEq
              injection renameEq with contextEq innerLevelEq innerLevelLtEq
                carrierLeftRenameEq carrierRightRenameEq carrierLeftRawRenameEq
                carrierRightRawRenameEq forwardRawRenameEq backwardRawRenameEq
                equivWitnessRenameEq
              cases innerLevelEq
              cases innerLevelLtEq
              have carrierLeftEq : carrierLeftA = carrierLeftB :=
                Ty.rename_injective_under_injective_renaming carrierLeftA
                  rhoInjective carrierLeftB carrierLeftRenameEq
              have carrierRightEq : carrierRightA = carrierRightB :=
                Ty.rename_injective_under_injective_renaming carrierRightA
                  rhoInjective carrierRightB carrierRightRenameEq
              have carrierLeftRawEq : leftRaw = leftRaw := rfl
              have carrierRightRawEq : rightRaw = rightRaw := rfl
              have equivWitnessHEq : HEq equivWitnessA equivWitnessB :=
                childInjective equivWitnessA equivWitnessB
                  equivWitnessRenameEq
              exact eq_of_heq
                (Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
                  carrierLeftEq carrierRightEq carrierLeftRawEq
                  carrierRightRawEq rfl rfl equivWitnessHEq)

theorem Term.rename_injective_atEquivIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {targetType : Ty level sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx targetType
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrier, forwardEq, backwardEq, typeEq, termHEq⟩ := reflViewA
    cases typeEq
    exact
      Term.rename_injective_atEquivIntroEquiv_of_inner termRenaming
        rhoInjective childInjective termA termB renameEq
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevel, innerLevelLt, carrier, carrierRaw, forwardEq,
        backwardEq, typeEq, termHEq⟩ := idViewA
      cases typeEq
      exact
        Term.rename_injective_atEquivIntroUniverseId_of_inner termRenaming
          rhoInjective childInjective termA termB renameEq
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeft, carrierRight, leftInvRaw, rightInvRaw,
          forwardTerm, backwardTerm, leftInv, rightInv, typeEq, termHEq⟩ :=
          introViewA
        cases typeEq
        exact
          Term.rename_injective_atEquivIntroEquiv_of_inner termRenaming
            rhoInjective childInjective termA termB renameEq
      | inr uaViewA =>
        obtain ⟨innerLevel, innerLevelLt, carrierLeft, carrierRight,
          carrierLeftRaw, carrierRightRaw, equivWitness, typeEq,
          termHEq⟩ := uaViewA
        cases typeEq
        exact
          Term.rename_injective_atEquivIntroUniverseId_of_inner termRenaming
            rhoInjective childInjective termA termB renameEq

end LeanFX2
