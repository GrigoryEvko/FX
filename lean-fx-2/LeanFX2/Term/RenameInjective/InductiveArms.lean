import LeanFX2.Term.RenameInjective
import LeanFX2.Term.TypedInversion

/-! # Term/RenameInjective/InductiveArms

Per-ctor arm helpers for the `induction termA` driver of
`Term.rename_injective` (strength-T2, #1953).  Each arm helper takes the
childA-fixed induction hypotheses (matching what `induction termA` produces)
plus termA's children plus a generic termB, and proves
`rename termA = rename termB → termA = termB`.

Closed ctors (var, unit, bool*, natZero, listNil, optionNone, refl, oeqRefl,
idStrictRefl, interval0/1, 10 type codes, universeCode, equivReflId,
funextRefl, equivReflIdAtId, funextReflAtId, funextIntroHet) reuse the
existing standalone helpers under `Term.rename_injective_at<Ctor>` directly
in the final induction — no arm helper needed here.

Non-colliding children use the **suffices-free-type + Ty.rename_injective
+ childA-fixed IH** pattern (validated by proto_fst).

Colliding children (lam, lamPi, app, appPi, equivIntro family, hcomp family)
use the existing `Term.*_inv` propext-clean inversion defs from
`BinderInversions.lean`/`TypedInversion.lean`/`EquivIntro.lean`. -/

namespace LeanFX2

/-- `fst` arm: existential `secondType` reconciled via `Ty.rename_injective`,
    childA-fixed `pairIH`.  Non-colliding raw `RawTerm.fst`. -/
theorem Term.rename_injective_arm_fst
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {firstType : Ty level sourceScope} {secondTypeA : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairA : Term sourceCtx (Ty.sigmaTy firstType secondTypeA) pairRaw)
    (pairIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (pairB : Term sourceCtx (Ty.sigmaTy firstType secondTypeA) pairRaw),
          Term.rename innerRenaming pairA = Term.rename innerRenaming pairB →
          pairA = pairB)
    (termB : Term sourceCtx firstType (RawTerm.fst pairRaw)) :
    Term.rename termRenaming (Term.fst pairA) =
      Term.rename termRenaming termB → Term.fst pairA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.fst pairRaw)),
        Σ' (secondTypeB : Ty level (sourceScope + 1)),
          Σ' (pairB :
              Term sourceCtx (Ty.sigmaTy genericType secondTypeB) pairRaw),
            HEq genericTerm (Term.fst pairB) by
    obtain ⟨secondTypeB, pairB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeRenameEq
      secondTypeRenameEq pairRawRenameEq pairRenameHEq
    have secondTypeEq : secondTypeA = secondTypeB :=
      Ty.rename_injective_under_injective_renaming secondTypeA
        (RawRenamingInjective.lift rhoInjective) secondTypeB secondTypeRenameEq
    cases secondTypeEq
    have pairEq : pairA = pairB :=
      pairIH termRenaming rhoInjective pairB (eq_of_heq pairRenameHEq)
    cases pairEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredSecondType pairTerm
  exact ⟨inferredSecondType, pairTerm, HEq.rfl⟩

/-- `lam` arm: cast-bearing binder body at the `RawTerm.lam` collision raw.
    Uses `Term.lam_arrow_inv` to invert termB cleanly (refutes
    lamPi/funextRefl/funextReflAtId/funextIntroHet siblings via arrow type). -/
theorem Term.rename_injective_arm_lam
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (bodyIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming (sourceScope + 1) innerTargetScope}
        (innerRenaming :
          TermRenaming (sourceCtx.cons domainType) innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (bodyB :
            Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw),
          Term.rename innerRenaming body = Term.rename innerRenaming bodyB →
          body = bodyB)
    (termB :
      Term sourceCtx (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming (Term.lam body) =
      Term.rename termRenaming termB → Term.lam body = termB := by
  intro renameEq
  obtain ⟨bodyB, termHEqB⟩ := Term.lam_arrow_inv termB
  cases termHEqB
  dsimp only [Term.rename] at renameEq
  injection renameEq with contextEq domainRenameEq codomainRenameEq
    bodyRawRenameEq bodyRawRenameEqAgain bodyRenameEq
  have bodyRenameUncastHEq :
      HEq (Term.rename (termRenaming.lift domainType) body)
        (Term.rename (termRenaming.lift domainType) bodyB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) body)))
      (HEq.trans (heq_of_eq bodyRenameEq)
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) bodyB)))
  have bodyEq : body = bodyB :=
    bodyIH (termRenaming.lift domainType)
      (RawRenamingInjective.lift rhoInjective) bodyB
      (eq_of_heq bodyRenameUncastHEq)
  cases bodyEq
  rfl

/-- `optionSome` arm: single parametric child, no cast.  Uses the
    type-free suffices pattern with a packed wrapper typeEq, matching the
    standalone `atOptionSome` helper's shape. -/
theorem Term.rename_injective_arm_optionSome
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueA : Term sourceCtx elementType valueRaw)
    (valueIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (valueB : Term sourceCtx elementType valueRaw),
          Term.rename innerRenaming valueA = Term.rename innerRenaming valueB →
          valueA = valueB)
    (termB : Term sourceCtx (Ty.optionType elementType)
      (RawTerm.optionSome valueRaw)) :
    Term.rename termRenaming (Term.optionSome valueA) =
      Term.rename termRenaming termB →
      Term.optionSome valueA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.optionSome valueRaw)),
        Σ' (inferredElementType : Ty level sourceScope),
          Σ' (valueTerm : Term sourceCtx inferredElementType valueRaw),
            Σ' (_ : genericType = Ty.optionType inferredElementType),
              HEq genericTerm (Term.optionSome valueTerm) by
    obtain ⟨inferredElementType, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ valueRenameEq
    exact congrArg Term.optionSome
      (valueIH termRenaming rhoInjective valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType valueTerm
  exact ⟨inferredElementType, valueTerm, rfl, HEq.rfl⟩

/-- `eitherInl` arm: single parametric child within a binary type wrapper.
    Both `leftType` and `rightType` are existential in the ctor; only
    `leftType` flows back to the value's type. -/
theorem Term.rename_injective_arm_eitherInl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {leftCarrierType rightCarrierType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueA : Term sourceCtx leftCarrierType valueRaw)
    (valueIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (valueB : Term sourceCtx leftCarrierType valueRaw),
          Term.rename innerRenaming valueA = Term.rename innerRenaming valueB →
          valueA = valueB)
    (termB : Term sourceCtx (Ty.eitherType leftCarrierType rightCarrierType)
      (RawTerm.eitherInl valueRaw)) :
    Term.rename termRenaming (Term.eitherInl valueA) =
      Term.rename termRenaming termB →
      Term.eitherInl valueA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.eitherInl valueRaw)),
        Σ' (inferredLeftType inferredRightType : Ty level sourceScope),
          Σ' (valueTerm : Term sourceCtx inferredLeftType valueRaw),
            Σ' (_ : genericType = Ty.eitherType inferredLeftType inferredRightType),
              HEq genericTerm
                (Term.eitherInl (rightType := inferredRightType) valueTerm) by
    obtain ⟨inferredLeftType, inferredRightType, valueB, typeEqB, termHEqB⟩ :=
      key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInl (rightType := rightCarrierType))
      (valueIH termRenaming rhoInjective valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTypeInferred rightTypeInferred valueTerm
  exact ⟨leftTypeInferred, rightTypeInferred, valueTerm, rfl, HEq.rfl⟩

/-- `eitherInr` arm: mirror of `eitherInl` on the right injection. -/
theorem Term.rename_injective_arm_eitherInr
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {leftCarrierType rightCarrierType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueA : Term sourceCtx rightCarrierType valueRaw)
    (valueIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (valueB : Term sourceCtx rightCarrierType valueRaw),
          Term.rename innerRenaming valueA = Term.rename innerRenaming valueB →
          valueA = valueB)
    (termB : Term sourceCtx (Ty.eitherType leftCarrierType rightCarrierType)
      (RawTerm.eitherInr valueRaw)) :
    Term.rename termRenaming (Term.eitherInr valueA) =
      Term.rename termRenaming termB →
      Term.eitherInr valueA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.eitherInr valueRaw)),
        Σ' (inferredLeftType inferredRightType : Ty level sourceScope),
          Σ' (valueTerm : Term sourceCtx inferredRightType valueRaw),
            Σ' (_ : genericType = Ty.eitherType inferredLeftType inferredRightType),
              HEq genericTerm
                (Term.eitherInr (leftType := inferredLeftType) valueTerm) by
    obtain ⟨inferredLeftType, inferredRightType, valueB, typeEqB, termHEqB⟩ :=
      key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInr (leftType := leftCarrierType))
      (valueIH termRenaming rhoInjective valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTypeInferred rightTypeInferred valueTerm
  exact ⟨leftTypeInferred, rightTypeInferred, valueTerm, rfl, HEq.rfl⟩

/-- `listCons` arm: two non-colliding children at the same element type,
    no cast on either.  Type-free suffices with packed wrapper typeEq. -/
theorem Term.rename_injective_arm_listCons
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headA : Term sourceCtx elementType headRaw)
    (tailA : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (headB : Term sourceCtx elementType headRaw),
          Term.rename innerRenaming headA = Term.rename innerRenaming headB →
          headA = headB)
    (tailIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (tailB : Term sourceCtx (Ty.listType elementType) tailRaw),
          Term.rename innerRenaming tailA = Term.rename innerRenaming tailB →
          tailA = tailB)
    (termB : Term sourceCtx (Ty.listType elementType)
      (RawTerm.listCons headRaw tailRaw)) :
    Term.rename termRenaming (Term.listCons headA tailA) =
      Term.rename termRenaming termB →
      Term.listCons headA tailA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listCons headRaw tailRaw)),
        Σ' (inferredElementType : Ty level sourceScope),
          Σ' (headTerm : Term sourceCtx inferredElementType headRaw),
            Σ' (tailTerm :
                Term sourceCtx (Ty.listType inferredElementType) tailRaw),
              Σ' (_ : genericType = Ty.listType inferredElementType),
                HEq genericTerm (Term.listCons headTerm tailTerm) by
    obtain ⟨inferredElementType, headB, tailB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ headRenameEq tailRenameEq
    rw [headIH termRenaming rhoInjective headB headRenameEq,
        tailIH termRenaming rhoInjective tailB tailRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType headTerm tailTerm
  exact ⟨inferredElementType, headTerm, tailTerm, rfl, HEq.rfl⟩

/-- `natSucc` arm: single closed-type child (Ty.nat), no cast, no existential. -/
theorem Term.rename_injective_arm_natSucc
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {predecessorRaw : RawTerm sourceScope}
    (predecessorA : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (predecessorB : Term sourceCtx Ty.nat predecessorRaw),
          Term.rename innerRenaming predecessorA =
            Term.rename innerRenaming predecessorB →
          predecessorA = predecessorB)
    (termB : Term sourceCtx Ty.nat (RawTerm.natSucc predecessorRaw)) :
    Term.rename termRenaming (Term.natSucc predecessorA) =
      Term.rename termRenaming termB →
      Term.natSucc predecessorA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.natSucc predecessorRaw)),
        Σ' (predecessorTerm : Term sourceCtx Ty.nat predecessorRaw),
          Σ' (_ : genericType = Ty.nat),
            HEq genericTerm (Term.natSucc predecessorTerm) by
    obtain ⟨predecessorB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ predecessorRenameEq
    exact congrArg Term.natSucc
      (predecessorIH termRenaming rhoInjective predecessorB predecessorRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i predecessorTerm
  exact ⟨predecessorTerm, rfl, HEq.rfl⟩

/-- `natElim` arm: 3 children (Ty.nat scrutinee + 2 branches at motiveType),
    no cast.  motiveType IS the result type so no wrapper packing needed —
    `genericType` directly plays the role of motiveType. -/
theorem Term.rename_injective_arm_natElim
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeA : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranchA : Term sourceCtx motiveType zeroRaw)
    (succBranchA : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
          Term.rename innerRenaming scrutineeA =
            Term.rename innerRenaming scrutineeB →
          scrutineeA = scrutineeB)
    (zeroBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (zeroBranchB : Term sourceCtx motiveType zeroRaw),
          Term.rename innerRenaming zeroBranchA =
            Term.rename innerRenaming zeroBranchB →
          zeroBranchA = zeroBranchB)
    (succBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (succBranchB :
            Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw),
          Term.rename innerRenaming succBranchA =
            Term.rename innerRenaming succBranchB →
          succBranchA = succBranchB)
    (termB : Term sourceCtx motiveType
      (RawTerm.natElim scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming (Term.natElim scrutineeA zeroBranchA succBranchA) =
      Term.rename termRenaming termB →
      Term.natElim scrutineeA zeroBranchA succBranchA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natElim scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroBranchTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succBranchTerm :
                Term sourceCtx (Ty.arrow Ty.nat genericType) succRaw),
              HEq genericTerm
                (Term.natElim scrutineeTerm zeroBranchTerm succBranchTerm) by
    obtain ⟨scrutineeB, zeroBranchB, succBranchB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrTermEq zeroTermEq succTermEq
    rw [scrutineeIH termRenaming rhoInjective scrutineeB scrTermEq,
        zeroBranchIH termRenaming rhoInjective zeroBranchB zeroTermEq,
        succBranchIH termRenaming rhoInjective succBranchB succTermEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroBranchTerm succBranchTerm
  exact ⟨scrutineeTerm, zeroBranchTerm, succBranchTerm, HEq.rfl⟩

/-- `natRec` arm: 3 children, structurally identical to `natElim` modulo the
    succBranch's type carrying the recursor's two-argument arrow.  Same
    motiveType-as-result pattern, no cast, no wrapper. -/
theorem Term.rename_injective_arm_natRec
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeA : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranchA : Term sourceCtx motiveType zeroRaw)
    (succBranchA :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutineeIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
          Term.rename innerRenaming scrutineeA =
            Term.rename innerRenaming scrutineeB →
          scrutineeA = scrutineeB)
    (zeroBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (zeroBranchB : Term sourceCtx motiveType zeroRaw),
          Term.rename innerRenaming zeroBranchA =
            Term.rename innerRenaming zeroBranchB →
          zeroBranchA = zeroBranchB)
    (succBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (succBranchB :
            Term sourceCtx
              (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw),
          Term.rename innerRenaming succBranchA =
            Term.rename innerRenaming succBranchB →
          succBranchA = succBranchB)
    (termB : Term sourceCtx motiveType
      (RawTerm.natRec scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming (Term.natRec scrutineeA zeroBranchA succBranchA) =
      Term.rename termRenaming termB →
      Term.natRec scrutineeA zeroBranchA succBranchA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natRec scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroBranchTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succBranchTerm :
                Term sourceCtx
                  (Ty.arrow Ty.nat (Ty.arrow genericType genericType)) succRaw),
              HEq genericTerm
                (Term.natRec scrutineeTerm zeroBranchTerm succBranchTerm) by
    obtain ⟨scrutineeB, zeroBranchB, succBranchB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrTermEq zeroTermEq succTermEq
    rw [scrutineeIH termRenaming rhoInjective scrutineeB scrTermEq,
        zeroBranchIH termRenaming rhoInjective zeroBranchB zeroTermEq,
        succBranchIH termRenaming rhoInjective succBranchB succTermEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroBranchTerm succBranchTerm
  exact ⟨scrutineeTerm, zeroBranchTerm, succBranchTerm, HEq.rfl⟩

/-- `listElim` arm: 3 children with both elementType (existential at the
    scrutinee carrier) and motiveType (result type, hence genericType).
    The inferred elementType needs reconciling with outer elementType via
    `Ty.rename_injective` from the injection's elementType.rename equation. -/
theorem Term.rename_injective_arm_listElim
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutineeA : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranchA : Term sourceCtx motiveType nilRaw)
    (consBranchA : Term sourceCtx
      (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
      consRaw)
    (scrutineeIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (scrutineeB : Term sourceCtx (Ty.listType elementType) scrutineeRaw),
          Term.rename innerRenaming scrutineeA =
            Term.rename innerRenaming scrutineeB →
          scrutineeA = scrutineeB)
    (nilBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (nilBranchB : Term sourceCtx motiveType nilRaw),
          Term.rename innerRenaming nilBranchA =
            Term.rename innerRenaming nilBranchB →
          nilBranchA = nilBranchB)
    (consBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (consBranchB : Term sourceCtx
            (Ty.arrow elementType
              (Ty.arrow (Ty.listType elementType) motiveType))
            consRaw),
          Term.rename innerRenaming consBranchA =
            Term.rename innerRenaming consBranchB →
          consBranchA = consBranchB)
    (termB : Term sourceCtx motiveType
      (RawTerm.listElim scrutineeRaw nilRaw consRaw)) :
    Term.rename termRenaming (Term.listElim scrutineeA nilBranchA consBranchA) =
      Term.rename termRenaming termB →
      Term.listElim scrutineeA nilBranchA consBranchA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listElim scrutineeRaw nilRaw consRaw)),
        Σ' (inferredElementType : Ty level sourceScope),
          Σ' (scrutineeTerm :
              Term sourceCtx (Ty.listType inferredElementType) scrutineeRaw),
            Σ' (nilTerm : Term sourceCtx genericType nilRaw),
              Σ' (consTerm :
                  Term sourceCtx
                    (Ty.arrow inferredElementType
                      (Ty.arrow (Ty.listType inferredElementType) genericType))
                    consRaw),
                HEq genericTerm
                  (Term.listElim scrutineeTerm nilTerm consTerm) by
    obtain ⟨inferredElementType, scrutineeB, nilB, consB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ elemRenameEq _ _ _ _ scrTermHEq nilTermHEq consTermHEq
    have elementTypeEq : elementType = inferredElementType :=
      Ty.rename_injective_under_injective_renaming elementType
        rhoInjective inferredElementType elemRenameEq
    cases elementTypeEq
    rw [scrutineeIH termRenaming rhoInjective scrutineeB (eq_of_heq scrTermHEq),
        nilBranchIH termRenaming rhoInjective nilB nilTermHEq,
        consBranchIH termRenaming rhoInjective consB (eq_of_heq consTermHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType scrutineeTerm nilTerm consTerm
  exact ⟨inferredElementType, scrutineeTerm, nilTerm, consTerm, HEq.rfl⟩

/-- `optionMatch` arm: structurally identical to `listElim` with element-
    typed scrutinee + value-typed someBranch.  Same reconcile-via-
    `Ty.rename_injective` pattern. -/
theorem Term.rename_injective_arm_optionMatch
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutineeA : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranchA : Term sourceCtx motiveType noneRaw)
    (someBranchA : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (scrutineeB : Term sourceCtx (Ty.optionType elementType) scrutineeRaw),
          Term.rename innerRenaming scrutineeA =
            Term.rename innerRenaming scrutineeB →
          scrutineeA = scrutineeB)
    (noneBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (noneBranchB : Term sourceCtx motiveType noneRaw),
          Term.rename innerRenaming noneBranchA =
            Term.rename innerRenaming noneBranchB →
          noneBranchA = noneBranchB)
    (someBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (someBranchB :
            Term sourceCtx (Ty.arrow elementType motiveType) someRaw),
          Term.rename innerRenaming someBranchA =
            Term.rename innerRenaming someBranchB →
          someBranchA = someBranchB)
    (termB : Term sourceCtx motiveType
      (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)) :
    Term.rename termRenaming (Term.optionMatch scrutineeA noneBranchA someBranchA) =
      Term.rename termRenaming termB →
      Term.optionMatch scrutineeA noneBranchA someBranchA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)),
        Σ' (inferredElementType : Ty level sourceScope),
          Σ' (scrutineeTerm :
              Term sourceCtx (Ty.optionType inferredElementType) scrutineeRaw),
            Σ' (noneTerm : Term sourceCtx genericType noneRaw),
              Σ' (someTerm :
                  Term sourceCtx
                    (Ty.arrow inferredElementType genericType) someRaw),
                HEq genericTerm
                  (Term.optionMatch scrutineeTerm noneTerm someTerm) by
    obtain ⟨inferredElementType, scrutineeB, noneB, someB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ elemRenameEq _ _ _ _ scrTermHEq noneTermHEq someTermHEq
    have elementTypeEq : elementType = inferredElementType :=
      Ty.rename_injective_under_injective_renaming elementType
        rhoInjective inferredElementType elemRenameEq
    cases elementTypeEq
    rw [scrutineeIH termRenaming rhoInjective scrutineeB (eq_of_heq scrTermHEq),
        noneBranchIH termRenaming rhoInjective noneB noneTermHEq,
        someBranchIH termRenaming rhoInjective someB (eq_of_heq someTermHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType scrutineeTerm noneTerm someTerm
  exact ⟨inferredElementType, scrutineeTerm, noneTerm, someTerm, HEq.rfl⟩

/-- `eitherMatch` arm: three existentials (leftType, rightType, motiveType
    as result) plus 3 children.  Both leftType and rightType need
    reconciling via `Ty.rename_injective`. -/
theorem Term.rename_injective_arm_eitherMatch
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutineeA : Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranchA : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranchA : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (scrutineeB :
            Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw),
          Term.rename innerRenaming scrutineeA =
            Term.rename innerRenaming scrutineeB →
          scrutineeA = scrutineeB)
    (leftBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (leftBranchB :
            Term sourceCtx (Ty.arrow leftType motiveType) leftRaw),
          Term.rename innerRenaming leftBranchA =
            Term.rename innerRenaming leftBranchB →
          leftBranchA = leftBranchB)
    (rightBranchIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (rightBranchB :
            Term sourceCtx (Ty.arrow rightType motiveType) rightRaw),
          Term.rename innerRenaming rightBranchA =
            Term.rename innerRenaming rightBranchB →
          rightBranchA = rightBranchB)
    (termB : Term sourceCtx motiveType
      (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)) :
    Term.rename termRenaming
        (Term.eitherMatch scrutineeA leftBranchA rightBranchA) =
      Term.rename termRenaming termB →
      Term.eitherMatch scrutineeA leftBranchA rightBranchA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)),
        Σ' (inferredLeftType inferredRightType : Ty level sourceScope),
          Σ' (scrutineeTerm : Term sourceCtx
              (Ty.eitherType inferredLeftType inferredRightType) scrutineeRaw),
            Σ' (leftTerm : Term sourceCtx
                (Ty.arrow inferredLeftType genericType) leftRaw),
              Σ' (rightTerm : Term sourceCtx
                  (Ty.arrow inferredRightType genericType) rightRaw),
                HEq genericTerm
                  (Term.eitherMatch scrutineeTerm leftTerm rightTerm) by
    obtain ⟨inferredLeftType, inferredRightType, scrutineeB, leftB, rightB,
      termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ leftRenameEq rightRenameEq _ _ _ _
      scrTermHEq leftTermHEq rightTermHEq
    have leftTypeEq : leftType = inferredLeftType :=
      Ty.rename_injective_under_injective_renaming leftType
        rhoInjective inferredLeftType leftRenameEq
    have rightTypeEq : rightType = inferredRightType :=
      Ty.rename_injective_under_injective_renaming rightType
        rhoInjective inferredRightType rightRenameEq
    cases leftTypeEq
    cases rightTypeEq
    rw [scrutineeIH termRenaming rhoInjective scrutineeB (eq_of_heq scrTermHEq),
        leftBranchIH termRenaming rhoInjective leftB (eq_of_heq leftTermHEq),
        rightBranchIH termRenaming rhoInjective rightB (eq_of_heq rightTermHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType scrutineeTerm leftTerm rightTerm
  exact ⟨inferredLeftType, inferredRightType, scrutineeTerm, leftTerm,
    rightTerm, HEq.rfl⟩

/-- `pair` arm: two children, cast on `secondValue` via
    `Ty.subst0_rename_commute`.  Uses type-free suffices with a packed
    sigmaTy wrapper typeEq; uncasts `secondValue`'s rename HEq mirroring
    `arm_lam`'s body-uncast pattern. -/
theorem Term.rename_injective_arm_pair
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstValueA : Term sourceCtx firstType firstRaw)
    (secondValueA : Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw)
    (firstIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (firstValueB : Term sourceCtx firstType firstRaw),
          Term.rename innerRenaming firstValueA =
            Term.rename innerRenaming firstValueB →
          firstValueA = firstValueB)
    (secondIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (secondValueB :
            Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw),
          Term.rename innerRenaming secondValueA =
            Term.rename innerRenaming secondValueB →
          secondValueA = secondValueB)
    (termB : Term sourceCtx (Ty.sigmaTy firstType secondType)
      (RawTerm.pair firstRaw secondRaw)) :
    Term.rename termRenaming (Term.pair firstValueA secondValueA) =
      Term.rename termRenaming termB →
      Term.pair firstValueA secondValueA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pair firstRaw secondRaw)),
        Σ' (inferredFirstType : Ty level sourceScope),
          Σ' (inferredSecondType : Ty level (sourceScope + 1)),
            Σ' (firstValueB :
                Term sourceCtx inferredFirstType firstRaw),
              Σ' (secondValueB : Term sourceCtx
                  (inferredSecondType.subst0 inferredFirstType firstRaw)
                  secondRaw),
                Σ' (_ : genericType =
                    Ty.sigmaTy inferredFirstType inferredSecondType),
                  HEq genericTerm (Term.pair firstValueB secondValueB) by
    obtain ⟨inferredFirstType, inferredSecondType, firstValueB, secondValueB,
      typeEq, termHEqB⟩ := key termB
    cases typeEq
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ firstRenameEq secondRenameHEq
    have secondRenameUncastHEq :
        HEq (Term.rename termRenaming secondValueA)
          (Term.rename termRenaming secondValueB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondValueA)))
        (HEq.trans (heq_of_eq secondRenameHEq)
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondValueB)))
    have firstEq : firstValueA = firstValueB :=
      firstIH termRenaming rhoInjective firstValueB firstRenameEq
    have secondEq : secondValueA = secondValueB :=
      secondIH termRenaming rhoInjective secondValueB
        (eq_of_heq secondRenameUncastHEq)
    cases firstEq
    cases secondEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFirstType inferredSecondType firstValueTerm secondValueTerm
  exact ⟨inferredFirstType, inferredSecondType, firstValueTerm, secondValueTerm,
    rfl, HEq.rfl⟩

/-- `lamPi` arm: binder-η collision raw `RawTerm.lam` is shared between
    `Term.lamPi` and `Term.funextRefl` (when the codomain reduces to a
    Π-typed shape).  Uses `Term.lam_pi_inv` (BinderInversions.lean:256)
    to invert `termB` propext-cleanly into a PSum {lamPi, funextRefl} and
    refutes the funextRefl arm via the existing
    `renamedLamPi_ne_renamedFunextReflCast` cross-refutation. -/
theorem Term.rename_injective_arm_lamPi
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (bodyIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming (sourceScope + 1) innerTargetScope}
        (innerRenaming :
          TermRenaming (sourceCtx.cons domainType) innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (bodyB : Term (sourceCtx.cons domainType) codomainType bodyRaw),
          Term.rename innerRenaming body = Term.rename innerRenaming bodyB →
          body = bodyB)
    (termB :
      Term sourceCtx (Ty.piTy domainType codomainType) (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming (Term.lamPi body) =
      Term.rename termRenaming termB → Term.lamPi body = termB := by
  intro renameEq
  cases Term.lam_pi_inv termB with
  | inl lamView =>
      obtain ⟨bodyB, termHEqB⟩ := lamView
      cases termHEqB
      dsimp only [Term.rename] at renameEq
      injection renameEq with contextEq domainRenameEq codomainRenameEq
        bodyRawRenameEq bodyRawRenameEqAgain bodyRenameEq
      have bodyEq : body = bodyB :=
        bodyIH (termRenaming.lift domainType)
          (RawRenamingInjective.lift rhoInjective) bodyB bodyRenameEq
      cases bodyEq
      rfl
  | inr reflView =>
      obtain ⟨baseCodomainB, applyRawB, bodyRawEqB, codomainEqB, termHEqB⟩ :=
        reflView
      cases bodyRawEqB
      cases codomainEqB
      cases termHEqB
      exact False.elim
        (renamedLamPi_ne_renamedFunextReflCast termRenaming body
          baseCodomainB applyRawB rfl rfl
          (heq_of_eq renameEq))

-- NOTE: arm_snd / arm_boolElim / arm_appPi (and other cast-on-result ctors)
-- hit a fundamental dep-elim wall: `Ty.subst0` is not structurally injective,
-- so given `termB : Term ... (secondType.subst0 firstType ...) (RawTerm.snd pairRaw)`,
-- inverting termB to `Term.snd pairB` with pairB at `Ty.sigmaTy firstType secondType`
-- is blocked.  Existing `Term.snd_ctor` lemma assumes BOTH sides already at the
-- sigmaTy type.  The arm-helper shape (childA-fixed IH + termB-generic) needs
-- a deeper inversion infrastructure (or a different driver shape that cases on
-- both termA AND termB simultaneously) to handle these arms.  Deferring these
-- arms — they're tractable from the existing `*_ctor` helpers but need separate
-- inversion plumbing not yet in scope.  See InductiveArms.lean header for the
-- catalogue of arm patterns that DO ship cleanly via this driver.

end LeanFX2
