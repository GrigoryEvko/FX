import LeanFX2.Term.RenameInjective.BinderInversions

/-! # Term/RenameInjective/ClosedData

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

theorem Term.rename_injective_atVar
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {position : Fin sourceScope}
    (termA termB :
      Term sourceCtx (varType sourceCtx position) (RawTerm.var position)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.var position)),
        Σ' (_ : genericType = varType sourceCtx position),
          HEq genericTerm (Term.var (context := sourceCtx) position) by
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

theorem Term.rename_injective_atUnit
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.unit RawTerm.unit) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.unit),
        Σ' (_ : genericType = Ty.unit),
          HEq genericTerm (Term.unit (context := sourceCtx)) by
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

theorem Term.rename_injective_atBoolTrue
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.bool RawTerm.boolTrue) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.boolTrue),
        Σ' (_ : genericType = Ty.bool),
          HEq genericTerm (Term.boolTrue (context := sourceCtx)) by
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

theorem Term.rename_injective_atBoolFalse
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.bool RawTerm.boolFalse) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.boolFalse),
        Σ' (_ : genericType = Ty.bool),
          HEq genericTerm (Term.boolFalse (context := sourceCtx)) by
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

theorem Term.rename_injective_atNatZero
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.nat RawTerm.natZero) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.natZero),
        Σ' (_ : genericType = Ty.nat),
          HEq genericTerm (Term.natZero (context := sourceCtx)) by
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

theorem Term.rename_injective_atNatSucc_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {predecessorRaw : RawTerm sourceScope}
    (predecessorInjective :
      ∀ (predecessorA predecessorB :
          Term sourceCtx Ty.nat predecessorRaw),
        Term.rename termRenaming predecessorA =
          Term.rename termRenaming predecessorB →
        predecessorA = predecessorB)
    (termA termB :
      Term sourceCtx Ty.nat (RawTerm.natSucc predecessorRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natSucc predecessorRaw)),
        Σ' (predecessorTerm : Term sourceCtx Ty.nat predecessorRaw),
          Σ' (_ : genericType = Ty.nat),
            HEq genericTerm (Term.natSucc predecessorTerm) by
    obtain ⟨predecessorA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨predecessorB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ predecessorRenameEq
    exact congrArg Term.natSucc
      (predecessorInjective predecessorA predecessorB predecessorRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i predecessorTerm
  exact ⟨predecessorTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atNatElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ (scrutineeA scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (zeroInjective :
      ∀ (zeroA zeroB : Term sourceCtx motiveType zeroRaw),
        Term.rename termRenaming zeroA = Term.rename termRenaming zeroB →
        zeroA = zeroB)
    (succInjective :
      ∀ (succA succB :
          Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw),
        Term.rename termRenaming succA = Term.rename termRenaming succB →
        succA = succB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.natElim scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natElim scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succTerm :
                Term sourceCtx (Ty.arrow Ty.nat genericType) succRaw),
              HEq genericTerm
                (Term.natElim scrutineeTerm zeroTerm succTerm) by
    obtain ⟨scrutineeA, zeroA, succA, termHEqA⟩ := key termA
    obtain ⟨scrutineeB, zeroB, succB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrutineeRenameEq zeroRenameEq
      succRenameEq
    rw [scrutineeInjective scrutineeA scrutineeB scrutineeRenameEq,
      zeroInjective zeroA zeroB zeroRenameEq,
      succInjective succA succB succRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroTerm succTerm
  exact ⟨scrutineeTerm, zeroTerm, succTerm, HEq.rfl⟩

theorem Term.rename_injective_atNatRec_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ (scrutineeA scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (zeroInjective :
      ∀ (zeroA zeroB : Term sourceCtx motiveType zeroRaw),
        Term.rename termRenaming zeroA = Term.rename termRenaming zeroB →
        zeroA = zeroB)
    (succInjective :
      ∀ (succA succB :
          Term sourceCtx
            (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw),
        Term.rename termRenaming succA = Term.rename termRenaming succB →
        succA = succB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.natRec scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natRec scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succTerm :
                Term sourceCtx
                  (Ty.arrow Ty.nat (Ty.arrow genericType genericType))
                  succRaw),
              HEq genericTerm
                (Term.natRec scrutineeTerm zeroTerm succTerm) by
    obtain ⟨scrutineeA, zeroA, succA, termHEqA⟩ := key termA
    obtain ⟨scrutineeB, zeroB, succB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrutineeRenameEq zeroRenameEq
      succRenameEq
    rw [scrutineeInjective scrutineeA scrutineeB scrutineeRenameEq,
      zeroInjective zeroA zeroB zeroRenameEq,
      succInjective succA succB succRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroTerm succTerm
  exact ⟨scrutineeTerm, zeroTerm, succTerm, HEq.rfl⟩

theorem Term.rename_injective_atListNil
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    (termA termB : Term sourceCtx (Ty.listType elementType) RawTerm.listNil) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.listNil),
        Σ' (elementType : Ty level sourceScope),
          Σ' (_ : genericType = Ty.listType elementType),
            HEq genericTerm
              (Term.listNil (context := sourceCtx) (elementType := elementType)) by
    obtain ⟨elementTypeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType
  exact ⟨inferredElementType, rfl, HEq.rfl⟩

theorem Term.rename_injective_atListCons_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headInjective :
      ∀ (headA headB : Term sourceCtx elementType headRaw),
        Term.rename termRenaming headA = Term.rename termRenaming headB →
        headA = headB)
    (tailInjective :
      ∀ (tailA tailB : Term sourceCtx (Ty.listType elementType) tailRaw),
        Term.rename termRenaming tailA = Term.rename termRenaming tailB →
        tailA = tailB)
    (termA termB :
      Term sourceCtx (Ty.listType elementType)
        (RawTerm.listCons headRaw tailRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listCons headRaw tailRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (headTerm : Term sourceCtx elementType headRaw),
            Σ' (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw),
              Σ' (_ : genericType = Ty.listType elementType),
                HEq genericTerm (Term.listCons headTerm tailTerm) by
    obtain ⟨elementTypeA, headA, tailA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, headB, tailB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ headRenameEq tailRenameEq
    rw [headInjective headA headB headRenameEq,
      tailInjective tailA tailB tailRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType headTerm tailTerm
  exact ⟨inferredElementType, headTerm, tailTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atPair_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstInjective :
      ∀ (firstA firstB : Term sourceCtx firstType firstRaw),
        Term.rename termRenaming firstA = Term.rename termRenaming firstB →
        firstA = firstB)
    (secondInjective :
      ∀ (secondA secondB :
          Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw),
        HEq (Term.rename termRenaming secondA)
          (Term.rename termRenaming secondB) →
        HEq secondA secondB)
    (termA termB :
      Term sourceCtx (Ty.sigmaTy firstType secondType)
        (RawTerm.pair firstRaw secondRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pair firstRaw secondRaw)),
        Σ' (inferredFirstType : Ty level sourceScope),
          Σ' (inferredSecondType : Ty level (sourceScope + 1)),
            Σ' (firstValue :
                Term sourceCtx inferredFirstType firstRaw),
              Σ' (secondValue :
                  Term sourceCtx
                    (inferredSecondType.subst0 inferredFirstType firstRaw)
                    secondRaw),
                Σ' (_ :
                    genericType =
                      Ty.sigmaTy inferredFirstType inferredSecondType),
                  HEq genericTerm (Term.pair firstValue secondValue) by
    obtain ⟨inferredFirstA, inferredSecondA, firstA, secondA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨inferredFirstB, inferredSecondB, firstB, secondB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeEq secondTypeEq
      firstRawEq secondRawEq firstRenameEq secondRenameHEq
    have secondRenameUncastHEq :
        HEq (Term.rename termRenaming secondA)
          (Term.rename termRenaming secondB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondA)))
        (HEq.trans (heq_of_eq secondRenameHEq)
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondB)))
    have secondHEq : HEq secondA secondB :=
      secondInjective secondA secondB secondRenameUncastHEq
    rw [firstInjective firstA firstB firstRenameEq]
    cases secondHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFirstType inferredSecondType firstValue secondValue
  exact ⟨inferredFirstType, inferredSecondType, firstValue, secondValue, rfl,
    HEq.rfl⟩

theorem Term.rename_injective_atFst_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {firstType : Ty level sourceScope}
    {pairRaw : RawTerm sourceScope}
    (pairInjective :
      ∀ {secondA secondB : Ty level (sourceScope + 1)}
        (pairA : Term sourceCtx (Ty.sigmaTy firstType secondA) pairRaw)
        (pairB : Term sourceCtx (Ty.sigmaTy firstType secondB) pairRaw),
        HEq (Term.rename termRenaming pairA)
          (Term.rename termRenaming pairB) →
        HEq pairA pairB)
    (termA termB : Term sourceCtx firstType (RawTerm.fst pairRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.fst pairRaw)),
        Σ' (secondType : Ty level (sourceScope + 1)),
          Σ' (pairTerm :
              Term sourceCtx (Ty.sigmaTy genericType secondType) pairRaw),
            HEq genericTerm (Term.fst pairTerm) by
    obtain ⟨secondTypeA, pairA, termHEqA⟩ := key termA
    obtain ⟨secondTypeB, pairB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeRenameEq
      secondTypeRenameEq pairRawRenameEq pairRenameHEq
    have secondTypeEq : secondTypeA = secondTypeB :=
      Ty.rename_injective_under_injective_renaming secondTypeA
        (RawRenamingInjective.lift rhoInjective) secondTypeB secondTypeRenameEq
    have pairHEq : HEq pairA pairB :=
      pairInjective pairA pairB pairRenameHEq
    cases secondTypeEq
    cases pairHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredSecondType pairTerm
  exact ⟨inferredSecondType, pairTerm, HEq.rfl⟩

theorem Term.rename_injective_snd_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairInjective :
      ∀ (pairA pairB :
          Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw),
        HEq (Term.rename termRenaming pairA)
          (Term.rename termRenaming pairB) →
        HEq pairA pairB)
    (pairA pairB :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.rename termRenaming (Term.snd pairA) =
      Term.rename termRenaming (Term.snd pairB) →
      Term.snd pairA = Term.snd pairB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  have sndRenameHEq :
      HEq
        (Term.snd (Term.rename termRenaming pairA))
        (Term.snd (Term.rename termRenaming pairB)) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute secondType firstType
            (RawTerm.fst pairRaw) rho).symm
          (Term.snd (Term.rename termRenaming pairA))))
      (HEq.trans (heq_of_eq renameEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute secondType firstType
            (RawTerm.fst pairRaw) rho).symm
          (Term.snd (Term.rename termRenaming pairB))))
  injection sndRenameHEq with scopeEq contextEq firstTypeRenameEq
    secondTypeRenameEq pairRawRenameEq pairRenameHEq
  have pairHEq : HEq pairA pairB :=
    pairInjective pairA pairB (heq_of_eq pairRenameHEq)
  cases pairHEq
  rfl

end LeanFX2
