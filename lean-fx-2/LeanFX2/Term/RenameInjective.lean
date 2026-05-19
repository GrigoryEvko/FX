import LeanFX2.Term.Rename
import LeanFX2.Foundation.RawTermInjective
import LeanFX2.Foundation.TyRenameInjective

/-! # Term/RenameInjective

Typed-term rename injectivity, built in small audited slices.

This file is the home for strength-T2.  The first slice ships the
raw-unique closed leaves: when the source raw index is a nullary raw
constructor, both typed terms are forced to be the corresponding `Term`
constructor, so the rename equality is irrelevant.
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

theorem Term.rename_injective_atOptionNone
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    (termA termB : Term sourceCtx (Ty.optionType elementType)
      RawTerm.optionNone) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.optionNone),
        Σ' (elementType : Ty level sourceScope),
          Σ' (_ : genericType = Ty.optionType elementType),
            HEq genericTerm
              (Term.optionNone (context := sourceCtx)
                (elementType := elementType)) by
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

theorem Term.rename_injective_atOptionSome_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx elementType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.optionType elementType)
        (RawTerm.optionSome valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.optionSome valueRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (valueTerm : Term sourceCtx elementType valueRaw),
            Σ' (_ : genericType = Ty.optionType elementType),
              HEq genericTerm (Term.optionSome valueTerm) by
    obtain ⟨elementTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ valueRenameEq
    exact congrArg Term.optionSome
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType valueTerm
  exact ⟨inferredElementType, valueTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEitherInl_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx leftType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInl valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherInl valueRaw)),
        Σ' (leftType : Ty level sourceScope),
          Σ' (rightType : Ty level sourceScope),
            Σ' (valueTerm : Term sourceCtx leftType valueRaw),
              Σ' (_ : genericType = Ty.eitherType leftType rightType),
                HEq genericTerm
                  (Term.eitherInl (rightType := rightType) valueTerm) by
    obtain ⟨leftTypeA, rightTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftTypeB, rightTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInl (rightType := rightType))
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType valueTerm
  exact ⟨inferredLeftType, inferredRightType, valueTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEitherInr_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx rightType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInr valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherInr valueRaw)),
        Σ' (leftType : Ty level sourceScope),
          Σ' (rightType : Ty level sourceScope),
            Σ' (valueTerm : Term sourceCtx rightType valueRaw),
              Σ' (_ : genericType = Ty.eitherType leftType rightType),
                HEq genericTerm
                  (Term.eitherInr (leftType := leftType) valueTerm) by
    obtain ⟨leftTypeA, rightTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftTypeB, rightTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInr (leftType := leftType))
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType valueTerm
  exact ⟨inferredLeftType, inferredRightType, valueTerm, rfl, HEq.rfl⟩

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

theorem Term.rename_injective_atRecordIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (fieldInjective :
      ∀ (fieldA fieldB : Term sourceCtx singleFieldType firstRaw),
        Term.rename termRenaming fieldA = Term.rename termRenaming fieldB →
        fieldA = fieldB)
    (termA termB :
      Term sourceCtx (Ty.record singleFieldType)
        (RawTerm.recordIntro firstRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.recordIntro firstRaw)),
        Σ' (singleFieldType : Ty level sourceScope),
          Σ' (fieldTerm : Term sourceCtx singleFieldType firstRaw),
            Σ' (_ : genericType = Ty.record singleFieldType),
              HEq genericTerm (Term.recordIntro fieldTerm) by
    obtain ⟨singleFieldTypeA, fieldA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨singleFieldTypeB, fieldB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ fieldRenameEq
    exact congrArg Term.recordIntro
      (fieldInjective fieldA fieldB fieldRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFieldType fieldTerm
  exact ⟨inferredFieldType, fieldTerm, rfl, HEq.rfl⟩

end LeanFX2
