import LeanFX2.Term.RenameInjective.IdentityEliminators

/-! # Term/RenameInjective/ReflexivityInterval

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

theorem Term.rename_injective_atRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.id carrier rawWitness rawWitness)
        (RawTerm.refl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.refl rawWitness)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (_ : genericType = Ty.id carrier rawWitness rawWitness),
            HEq genericTerm (Term.refl carrier rawWitness) by
    obtain ⟨carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier
  exact ⟨inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atOEqRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.oeq carrier rawWitness rawWitness)
        (RawTerm.oeqRefl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.oeqRefl rawWitness)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (_ : genericType = Ty.oeq carrier rawWitness rawWitness),
            HEq genericTerm (Term.oeqRefl carrier rawWitness) by
    obtain ⟨carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier
  exact ⟨inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIdStrictRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.idStrict carrier rawWitness rawWitness)
        (RawTerm.idStrictRefl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idStrictRefl rawWitness)),
        Σ' (modeIsStrict : mode = Mode.strict),
          Σ' (carrier : Ty level sourceScope),
            Σ' (_ : genericType = Ty.idStrict carrier rawWitness rawWitness),
              HEq genericTerm
                (Term.idStrictRefl (context := sourceCtx) modeIsStrict
                  carrier rawWitness) by
    obtain ⟨modeIsStrictA, carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨modeIsStrictB, carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsStrict inferredCarrier
  exact ⟨inferredModeIsStrict, inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atInterval0
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.interval RawTerm.interval0) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.interval0),
        Σ' (_ : genericType = Ty.interval),
          HEq genericTerm (Term.interval0 (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atInterval1
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.interval RawTerm.interval1) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.interval1),
        Σ' (_ : genericType = Ty.interval),
          HEq genericTerm (Term.interval1 (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalOpp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerRaw : RawTerm sourceScope}
    (innerInjective :
      ∀ (innerA innerB : Term sourceCtx Ty.interval innerRaw),
        Term.rename termRenaming innerA = Term.rename termRenaming innerB →
        innerA = innerB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalOpp innerRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalOpp innerRaw)),
        Σ' (innerTerm : Term sourceCtx Ty.interval innerRaw),
          Σ' (_ : genericType = Ty.interval),
            HEq genericTerm (Term.intervalOpp innerTerm) by
    obtain ⟨innerA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ innerRenameEq
    exact congrArg Term.intervalOpp
      (innerInjective innerA innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalMeet_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftInjective :
      ∀ (leftA leftB : Term sourceCtx Ty.interval leftRaw),
        Term.rename termRenaming leftA = Term.rename termRenaming leftB →
        leftA = leftB)
    (rightInjective :
      ∀ (rightA rightB : Term sourceCtx Ty.interval rightRaw),
        Term.rename termRenaming rightA = Term.rename termRenaming rightB →
        rightA = rightB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalMeet leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalMeet leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalMeet leftTerm rightTerm) by
    obtain ⟨leftA, rightA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftInjective leftA leftB leftRenameEq,
      rightInjective rightA rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalJoin_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftInjective :
      ∀ (leftA leftB : Term sourceCtx Ty.interval leftRaw),
        Term.rename termRenaming leftA = Term.rename termRenaming leftB →
        leftA = leftB)
    (rightInjective :
      ∀ (rightA rightB : Term sourceCtx Ty.interval rightRaw),
        Term.rename termRenaming rightA = Term.rename termRenaming rightB →
        rightA = rightB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalJoin leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalJoin leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalJoin leftTerm rightTerm) by
    obtain ⟨leftA, rightA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftInjective leftA leftB leftRenameEq,
      rightInjective rightA rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

end LeanFX2
