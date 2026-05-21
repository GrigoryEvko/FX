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

/-! ## Shared rename/context binders.

Every arm helper in this file operates over the same source-to-target
renaming setup.  Hoisted into a `section` + `variable` block to keep
each per-arm signature focused on the ctor-specific binders. -/

section InductiveArms

variable {mode : Mode} {level sourceScope targetScope : Nat}
variable {sourceCtx : Ctx mode level sourceScope}
variable {targetCtx : Ctx mode level targetScope}
variable {rho : RawRenaming sourceScope targetScope}
variable (termRenaming : TermRenaming sourceCtx targetCtx rho)

/-- `fst` arm: existential `secondType` reconciled via `Ty.rename_injective`,
    childA-fixed `pairIH`.  Non-colliding raw `RawTerm.fst`. -/
theorem Term.rename_injective_arm_fst
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

/-- `app` arm: arrow application with `RawTerm.app` collision raw (shared
    with `appPi`).  Uses `Term.app_inv` to invert termB into a disjoint sum;
    the `appPi` branch refutes via constructor-mismatch on `renameEq`
    (`Term.app … = Term.appPi …` is impossible by Term ctor noConfusion).
    `domainType` is the Ty existential (only in function child's type),
    recovered via `Ty.rename_injective_under_injective_renaming`. -/
theorem Term.rename_injective_arm_app
    (rhoInjective : RawRenamingInjective rho)
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (functionB :
            Term sourceCtx (Ty.arrow domainType codomainType) functionRaw),
          Term.rename innerRenaming functionTerm =
            Term.rename innerRenaming functionB →
          functionTerm = functionB)
    (argumentIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (argumentB : Term sourceCtx domainType argumentRaw),
          Term.rename innerRenaming argumentTerm =
            Term.rename innerRenaming argumentB →
          argumentTerm = argumentB)
    (termB :
      Term sourceCtx codomainType (RawTerm.app functionRaw argumentRaw)) :
    Term.rename termRenaming (Term.app functionTerm argumentTerm) =
      Term.rename termRenaming termB →
      Term.app functionTerm argumentTerm = termB := by
  intro renameEq
  cases Term.app_inv termB with
  | inl caseApp =>
      obtain ⟨innerDomain, fnTermB, argTermB, appHEq⟩ := caseApp
      cases appHEq
      dsimp only [Term.rename] at renameEq
      injection renameEq with _ _ domainRenameEq _ _ _ fnRenameHEq argRenameHEq
      have domainEq : domainType = innerDomain :=
        Ty.rename_injective_under_injective_renaming domainType
          rhoInjective innerDomain domainRenameEq
      cases domainEq
      rw [functionIH termRenaming rhoInjective fnTermB
            (eq_of_heq fnRenameHEq),
          argumentIH termRenaming rhoInjective argTermB
            (eq_of_heq argRenameHEq)]
  | inr caseAppPi =>
      obtain ⟨innerDomain, innerCodomain, eqProof, fnTermB, argTermB,
        appPiHEq⟩ := caseAppPi
      cases eqProof
      cases appPiHEq
      exfalso
      -- termB definitionally equals `Term.appPi fnTermB argTermB` at the
      -- shared type `(innerCodomain.subst0 innerDomain argumentRaw)`.
      -- `Term.rename` of `Term.appPi` carries a `Ty.subst0_rename_commute`
      -- cast on its result; strip it via `termRenameInjectiveCastHEq` to
      -- expose the bare `Term.appPi` ctor, then refute against `Term.app`
      -- via `Term.noConfusion`'s HEq-aware form (handles the residual
      -- Ty-index mismatch as an HEq parameter, no type-alignment needed).
      have rhsHEq :
          HEq (Term.rename termRenaming (Term.appPi fnTermB argTermB))
              (Term.appPi (Term.rename termRenaming fnTermB)
                          (Term.rename termRenaming argTermB)) :=
        termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute innerCodomain innerDomain argumentRaw rho).symm
          (Term.appPi (Term.rename termRenaming fnTermB)
                      (Term.rename termRenaming argTermB))
      have appHEq :
          HEq (Term.app (Term.rename termRenaming functionTerm)
                        (Term.rename termRenaming argumentTerm))
              (Term.appPi (Term.rename termRenaming fnTermB)
                          (Term.rename termRenaming argTermB)) :=
        HEq.trans (heq_of_eq renameEq) rhsHEq
      apply Term.noConfusion (P := False)
        (t := Term.app (Term.rename termRenaming functionTerm)
                       (Term.rename termRenaming argumentTerm))
        (t' := Term.appPi (Term.rename termRenaming fnTermB)
                          (Term.rename termRenaming argTermB))
        rfl rfl rfl HEq.rfl
        (heq_of_eq
          (Ty.subst0_rename_commute innerCodomain innerDomain argumentRaw rho))
        HEq.rfl
      exact appHEq

/-- `lam` arm: cast-bearing binder body at the `RawTerm.lam` collision raw.
    Uses `Term.lam_arrow_inv` to invert termB cleanly (refutes
    lamPi/funextRefl/funextReflAtId/funextIntroHet siblings via arrow type). -/
theorem Term.rename_injective_arm_lam
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

-- NOTE: arm_snd / arm_boolElim / arm_appPi (cast-on-result ctors) hit a
-- fundamental dep-elim wall: `Ty.subst0` is not structurally injective.
-- The suffices+free-genericType pattern succeeds for `cases genericTerm`
-- (since the type is free), but the resulting `typeEq : codomainType.subst0
-- ... = innerCodomain.subst0 ...` cannot be `cases`'d (Lean: "Dependent
-- elimination failed: Failed to solve equation
-- innerCodomain.subst (Subst.singleton ...) = codomainType.subst
-- (Subst.singleton ...)").  Working around requires either a heterogeneous
-- (HEq-style) IH or a deeper Ty-aligned inversion lemma.  Deferred — these
-- arms ARE tractable but need separate inversion plumbing (`Term.snd_inv`
-- with HEq Σ-Ty index extraction) not yet shipped.

/-! ## HoTT identity-eliminator arms (idJ / oeqJ / oeqFunext / idStrictRec).

These J-family eliminators output at `motiveType` (no cast), with a single
witness child at an `Ty.id carrier left right`-shaped existential carrier.
The arm closes via suffices+free-genericType+cases-on-genericTerm, then
aligns existentials via `Ty.rename_injective` (carrier) and
`RawTerm.rename_injective` (left/right endpoints) before firing the
witnessIH at the realigned types. -/

/-- `idJ` arm: HoTT identity-eliminator at carrier-aligned witness type. -/
theorem Term.rename_injective_arm_idJ
    (rhoInjective : RawRenamingInjective rho)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (baseB : Term sourceCtx motiveType baseRaw),
          Term.rename innerRenaming baseCase =
            Term.rename innerRenaming baseB →
          baseCase = baseB)
    (witnessIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (witnessB :
            Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint)
              witnessRaw),
          Term.rename innerRenaming witness =
            Term.rename innerRenaming witnessB →
          witness = witnessB)
    (termB :
      Term sourceCtx motiveType (RawTerm.idJ baseRaw witnessRaw)) :
    Term.rename termRenaming (Term.idJ baseCase witness) =
      Term.rename termRenaming termB →
      Term.idJ baseCase witness = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idJ baseRaw witnessRaw)),
        Σ' (inferredCarrier : Ty level sourceScope),
          Σ' (inferredLeft : RawTerm sourceScope),
            Σ' (inferredRight : RawTerm sourceScope),
              Σ' (baseB : Term sourceCtx genericType baseRaw),
                Σ' (witnessB :
                    Term sourceCtx
                      (Ty.id inferredCarrier inferredLeft inferredRight)
                      witnessRaw),
                  HEq genericTerm (Term.idJ baseB witnessB) by
    obtain ⟨inferredCarrier, inferredLeft, inferredRight, baseB, witnessB,
      termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ carrierRenameEq leftRenameEq rightRenameEq
      _ _ _ baseRenameEq witnessRenameHEq
    have carrierEq : carrier = inferredCarrier :=
      Ty.rename_injective_under_injective_renaming carrier
        rhoInjective inferredCarrier carrierRenameEq
    have leftEq : leftEndpoint = inferredLeft :=
      RawTerm.rename_injective_under_injective_renaming leftEndpoint
        rhoInjective inferredLeft leftRenameEq
    have rightEq : rightEndpoint = inferredRight :=
      RawTerm.rename_injective_under_injective_renaming rightEndpoint
        rhoInjective inferredRight rightRenameEq
    cases carrierEq
    cases leftEq
    cases rightEq
    rw [baseIH termRenaming rhoInjective baseB baseRenameEq,
        witnessIH termRenaming rhoInjective witnessB (eq_of_heq witnessRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier inferredLeft inferredRight baseTerm witnessTerm
  exact ⟨inferredCarrier, inferredLeft, inferredRight, baseTerm, witnessTerm,
    HEq.rfl⟩

/-- `oeqJ` arm: observational equality eliminator (parallel to idJ). -/
theorem Term.rename_injective_arm_oeqJ
    (rhoInjective : RawRenamingInjective rho)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (baseB : Term sourceCtx motiveType baseRaw),
          Term.rename innerRenaming baseCase =
            Term.rename innerRenaming baseB →
          baseCase = baseB)
    (witnessIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (witnessB :
            Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
              witnessRaw),
          Term.rename innerRenaming witness =
            Term.rename innerRenaming witnessB →
          witness = witnessB)
    (termB :
      Term sourceCtx motiveType (RawTerm.oeqJ baseRaw witnessRaw)) :
    Term.rename termRenaming (Term.oeqJ baseCase witness) =
      Term.rename termRenaming termB →
      Term.oeqJ baseCase witness = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.oeqJ baseRaw witnessRaw)),
        Σ' (inferredCarrier : Ty level sourceScope),
          Σ' (inferredLeft : RawTerm sourceScope),
            Σ' (inferredRight : RawTerm sourceScope),
              Σ' (baseB : Term sourceCtx genericType baseRaw),
                Σ' (witnessB :
                    Term sourceCtx
                      (Ty.oeq inferredCarrier inferredLeft inferredRight)
                      witnessRaw),
                  HEq genericTerm (Term.oeqJ baseB witnessB) by
    obtain ⟨inferredCarrier, inferredLeft, inferredRight, baseB, witnessB,
      termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ carrierRenameEq leftRenameEq rightRenameEq
      _ _ _ baseRenameEq witnessRenameHEq
    have carrierEq : carrier = inferredCarrier :=
      Ty.rename_injective_under_injective_renaming carrier
        rhoInjective inferredCarrier carrierRenameEq
    have leftEq : leftEndpoint = inferredLeft :=
      RawTerm.rename_injective_under_injective_renaming leftEndpoint
        rhoInjective inferredLeft leftRenameEq
    have rightEq : rightEndpoint = inferredRight :=
      RawTerm.rename_injective_under_injective_renaming rightEndpoint
        rhoInjective inferredRight rightRenameEq
    cases carrierEq
    cases leftEq
    cases rightEq
    rw [baseIH termRenaming rhoInjective baseB baseRenameEq,
        witnessIH termRenaming rhoInjective witnessB
          (eq_of_heq witnessRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier inferredLeft inferredRight baseTerm witnessTerm
  exact ⟨inferredCarrier, inferredLeft, inferredRight, baseTerm, witnessTerm,
    HEq.rfl⟩

/-- `idStrictRec` arm: strict-identity recursor.  Has additional
    `modeIsStrict : mode = Mode.strict` Prop equation. -/
theorem Term.rename_injective_arm_idStrictRec
    (rhoInjective : RawRenamingInjective rho)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (baseB : Term sourceCtx motiveType baseRaw),
          Term.rename innerRenaming baseCase =
            Term.rename innerRenaming baseB →
          baseCase = baseB)
    (witnessIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (witnessB :
            Term sourceCtx
              (Ty.idStrict carrier leftEndpoint rightEndpoint)
              witnessRaw),
          Term.rename innerRenaming witness =
            Term.rename innerRenaming witnessB →
          witness = witnessB)
    (termB :
      Term sourceCtx motiveType (RawTerm.idStrictRec baseRaw witnessRaw)) :
    Term.rename termRenaming (Term.idStrictRec modeIsStrict baseCase witness) =
      Term.rename termRenaming termB →
      Term.idStrictRec modeIsStrict baseCase witness = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idStrictRec baseRaw witnessRaw)),
        Σ' (inferredModeIsStrict : mode = Mode.strict),
          Σ' (inferredCarrier : Ty level sourceScope),
            Σ' (inferredLeft : RawTerm sourceScope),
              Σ' (inferredRight : RawTerm sourceScope),
                Σ' (baseB : Term sourceCtx genericType baseRaw),
                  Σ' (witnessB :
                      Term sourceCtx
                        (Ty.idStrict inferredCarrier inferredLeft inferredRight)
                        witnessRaw),
                    HEq genericTerm
                      (Term.idStrictRec inferredModeIsStrict baseB witnessB) by
    obtain ⟨_, inferredCarrier, inferredLeft, inferredRight, baseB, witnessB,
      termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ carrierRenameEq leftRenameEq rightRenameEq
      _ _ _ baseRenameEq witnessRenameHEq
    have carrierEq : carrier = inferredCarrier :=
      Ty.rename_injective_under_injective_renaming carrier
        rhoInjective inferredCarrier carrierRenameEq
    have leftEq : leftEndpoint = inferredLeft :=
      RawTerm.rename_injective_under_injective_renaming leftEndpoint
        rhoInjective inferredLeft leftRenameEq
    have rightEq : rightEndpoint = inferredRight :=
      RawTerm.rename_injective_under_injective_renaming rightEndpoint
        rhoInjective inferredRight rightRenameEq
    cases carrierEq
    cases leftEq
    cases rightEq
    rw [baseIH termRenaming rhoInjective baseB baseRenameEq,
        witnessIH termRenaming rhoInjective witnessB
          (eq_of_heq witnessRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsStrict inferredCarrier inferredLeft inferredRight
    baseTerm witnessTerm
  exact ⟨inferredModeIsStrict, inferredCarrier, inferredLeft, inferredRight,
    baseTerm, witnessTerm, HEq.rfl⟩

/-- `oeqFunext` arm: observational-funext intro with explicit domain/codomain
    type fields plus left/right function raws.  Pointwise proof is at
    `oeqFunextPointwiseType ...` which carries a `Ty.weaken`-style cast on
    rename.  Result type is `Ty.oeq (Ty.arrow domain codomain) leftFn rightFn`
    — structurally injective, so suffices+free-genericType+cases works. -/
theorem Term.rename_injective_arm_oeqFunext
    (rhoInjective : RawRenamingInjective rho)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (pointwiseB :
            Term sourceCtx
              (oeqFunextPointwiseType domainType codomainType
                leftFunctionRaw rightFunctionRaw)
              pointwiseRaw),
          Term.rename innerRenaming pointwiseProof =
            Term.rename innerRenaming pointwiseB →
          pointwiseProof = pointwiseB)
    (termB :
      Term sourceCtx
        (Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw)
        (RawTerm.oeqFunext pointwiseRaw)) :
    Term.rename termRenaming
        (Term.oeqFunext domainType codomainType leftFunctionRaw
          rightFunctionRaw pointwiseProof) =
      Term.rename termRenaming termB →
      Term.oeqFunext domainType codomainType leftFunctionRaw
        rightFunctionRaw pointwiseProof = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.oeqFunext pointwiseRaw)),
        Σ' (inferredDomain : Ty level sourceScope),
          Σ' (inferredCodomain : Ty level sourceScope),
            Σ' (inferredLeftFn : RawTerm sourceScope),
              Σ' (inferredRightFn : RawTerm sourceScope),
                Σ' (pointwiseB :
                    Term sourceCtx
                      (oeqFunextPointwiseType inferredDomain inferredCodomain
                        inferredLeftFn inferredRightFn)
                      pointwiseRaw),
                  Σ' (_ : genericType =
                      Ty.oeq (Ty.arrow inferredDomain inferredCodomain)
                        inferredLeftFn inferredRightFn),
                    HEq genericTerm
                      (Term.oeqFunext inferredDomain inferredCodomain
                        inferredLeftFn inferredRightFn pointwiseB) by
    obtain ⟨_, _, _, _, pointwiseB, typeEq, termHEqB⟩ := key termB
    cases typeEq
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ _ pointwiseRenameHEq
    have pointwiseRenameUncastHEq :
        HEq (Term.rename termRenaming pointwiseProof)
            (Term.rename termRenaming pointwiseB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (oeqFunextPointwiseType_rename rho domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.rename termRenaming pointwiseProof)))
        (HEq.trans (heq_of_eq pointwiseRenameHEq)
          (termRenameInjectiveCastHEq
            (oeqFunextPointwiseType_rename rho domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.rename termRenaming pointwiseB)))
    rw [pointwiseIH termRenaming rhoInjective pointwiseB
          (eq_of_heq pointwiseRenameUncastHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredDomain inferredCodomain inferredLeftFn inferredRightFn
    pointwiseTerm
  exact ⟨inferredDomain, inferredCodomain, inferredLeftFn, inferredRightFn,
    pointwiseTerm, rfl, HEq.rfl⟩

-- NOTE: arm_universeCode is structurally blocked by the toNat
-- non-injectivity wall (see `Foundation/Universe.lean:toNat_not_injective`).
-- `RawTerm.universeCode innerLevel.toNat` forgets the universe expression
-- structure: `UniverseLevel.max 0 0` and `UniverseLevel.imax 0 0` both
-- produce the same Nat height but are distinct constructors.  Even though
-- Term.rename is the identity on universeCode (rename doesn't see innerLevel),
-- `cases genericTerm` for a typed term whose raw is
-- `RawTerm.universeCode innerLevel.toNat` cannot pin innerLevel uniquely.
-- The induction-on-termA driver's IH does not encode an "innerLevel was
-- recovered" witness, so the arm cannot close.  Deferred to a future
-- session that ships a UniverseLevel-aware raw-inversion helper.
--
-- The Lean error message:
--   "Dependent elimination failed: Failed to solve equation
--    innerLevel.toNat = innerLevel✝.toNat"

/-- `equivApp` arm: apply a packaged equivalence to an argument.  Outputs
    `carrierB` (the equivalence's right carrier).  `carrierA` is existential
    inside the equivalence's `Ty.equiv carrierA carrierB`. -/
theorem Term.rename_injective_arm_equivApp
    (rhoInjective : RawRenamingInjective rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (equivB :
            Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw),
          Term.rename innerRenaming equivTerm =
            Term.rename innerRenaming equivB →
          equivTerm = equivB)
    (argumentTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (argumentB : Term sourceCtx carrierA argumentRaw),
          Term.rename innerRenaming argumentTerm =
            Term.rename innerRenaming argumentB →
          argumentTerm = argumentB)
    (termB :
      Term sourceCtx carrierB
        (RawTerm.equivApp equivRaw argumentRaw)) :
    Term.rename termRenaming (Term.equivApp equivTerm argumentTerm) =
      Term.rename termRenaming termB →
      Term.equivApp equivTerm argumentTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.equivApp equivRaw argumentRaw)),
        Σ' (inferredCarrierA : Ty level sourceScope),
          Σ' (equivB :
              Term sourceCtx (Ty.equiv inferredCarrierA genericType)
                equivRaw),
            Σ' (argumentB :
                Term sourceCtx inferredCarrierA argumentRaw),
              HEq genericTerm (Term.equivApp equivB argumentB) by
    obtain ⟨inferredCarrierA, equivB, argumentB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ carrierARenameEq _ _ _ equivRenameHEq
      argumentRenameHEq
    have carrierAEq : carrierA = inferredCarrierA :=
      Ty.rename_injective_under_injective_renaming carrierA
        rhoInjective inferredCarrierA carrierARenameEq
    cases carrierAEq
    rw [equivTermIH termRenaming rhoInjective equivB
          (eq_of_heq equivRenameHEq),
        argumentTermIH termRenaming rhoInjective argumentB
          (eq_of_heq argumentRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrierA equivB argumentB
  exact ⟨inferredCarrierA, equivB, argumentB, HEq.rfl⟩

/-! ## Cubical path application arm.

`pathApp` produces a unique raw `RawTerm.pathApp pathRaw intervalRaw` and
outputs at the path's `carrierType` (no cast).  Path's type `Ty.path
carrierType leftEndpoint rightEndpoint` carries existentials for left/
right endpoints (recoverable via `RawTerm.rename_injective`). -/

/-- `pathApp` arm: cubical path application at carrier-aligned path. -/
theorem Term.rename_injective_arm_pathApp
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (pathB : Term sourceCtx
            (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw),
          Term.rename innerRenaming pathTerm =
            Term.rename innerRenaming pathB →
          pathTerm = pathB)
    (intervalTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (intervalB : Term sourceCtx Ty.interval intervalRaw),
          Term.rename innerRenaming intervalTerm =
            Term.rename innerRenaming intervalB →
          intervalTerm = intervalB)
    (termB : Term sourceCtx carrierType
      (RawTerm.pathApp pathRaw intervalRaw)) :
    Term.rename termRenaming
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm) =
      Term.rename termRenaming termB →
      Term.pathApp modeIsUnivalent pathTerm intervalTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pathApp pathRaw intervalRaw)),
        Σ' (inferredModeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredLeft : RawTerm sourceScope),
            Σ' (inferredRight : RawTerm sourceScope),
              Σ' (pathB : Term sourceCtx
                  (Ty.path genericType inferredLeft inferredRight) pathRaw),
                Σ' (intervalB : Term sourceCtx Ty.interval intervalRaw),
                  HEq genericTerm
                    (Term.pathApp inferredModeIsUnivalent pathB intervalB) by
    obtain ⟨_, inferredLeft, inferredRight, pathB, intervalB, termHEqB⟩ :=
      key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ leftRenameEq rightRenameEq _ _
      pathRenameHEq intervalRenameEq
    have leftEq : leftEndpoint = inferredLeft :=
      RawTerm.rename_injective_under_injective_renaming leftEndpoint
        rhoInjective inferredLeft leftRenameEq
    have rightEq : rightEndpoint = inferredRight :=
      RawTerm.rename_injective_under_injective_renaming rightEndpoint
        rhoInjective inferredRight rightRenameEq
    cases leftEq
    cases rightEq
    rw [pathTermIH termRenaming rhoInjective pathB (eq_of_heq pathRenameHEq),
        intervalTermIH termRenaming rhoInjective intervalB intervalRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredLeft inferredRight pathInner
    intervalInner
  exact ⟨inferredModeIsUnivalent, inferredLeft, inferredRight, pathInner,
    intervalInner, HEq.rfl⟩

-- NOTE: arm_effectPerform deferred: the Effects.CanPerform proof field
-- is a Prop, and injection on `Term.rename effectPerform = Term.rename
-- effectPerform` produces a heterogeneous Prop equation
-- `Effects.CanPerform.map _ canPerformA = Effects.CanPerform.map _ canPerformB`
-- that cannot be discharged without proof irrelevance (propext-free).
-- The arm requires either a heterogeneous CanPerform.map_injective helper
-- or a Prop-stripping inversion lemma not yet shipped.

/-- `glueElim` arm: cubical glue elimination at `baseType` (no cast).
    `boundaryWitness` is a RawTerm existential recoverable via
    `RawTerm.rename_injective`. -/
theorem Term.rename_injective_arm_glueElim
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedValueIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (gluedB :
            Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw),
          Term.rename innerRenaming gluedValue =
            Term.rename innerRenaming gluedB →
          gluedValue = gluedB)
    (termB :
      Term sourceCtx baseType (RawTerm.glueElim gluedRaw)) :
    Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedValue) =
      Term.rename termRenaming termB →
      Term.glueElim modeIsUnivalent gluedValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.glueElim gluedRaw)),
        Σ' (inferredModeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredBoundary : RawTerm sourceScope),
            Σ' (gluedB :
                Term sourceCtx (Ty.glue genericType inferredBoundary)
                  gluedRaw),
              HEq genericTerm
                (Term.glueElim inferredModeIsUnivalent gluedB) by
    obtain ⟨_, inferredBoundary, gluedB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ boundaryRenameEq _ gluedRenameHEq
    have boundaryEq : boundaryWitness = inferredBoundary :=
      RawTerm.rename_injective_under_injective_renaming boundaryWitness
        rhoInjective inferredBoundary boundaryRenameEq
    cases boundaryEq
    rw [gluedValueIH termRenaming rhoInjective gluedB
          (eq_of_heq gluedRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredBoundary gluedTerm
  exact ⟨inferredModeIsUnivalent, inferredBoundary, gluedTerm, HEq.rfl⟩

/-! ## Cubical hcomp collision pair (hcomp / hcompPath).

Both produce raw `RawTerm.hcomp sidesRaw capRaw`.  hcomp's sides is at
the carrierType; hcompPath's sides is at `Ty.path carrierType leftEnd
rightEnd`.  `cases genericTerm` yields both branches; cross-refutation
between them via `Term.noConfusion` on the bare ctors after rename. -/

/-- `hcomp` arm: homogeneous cubical composition.  Collides with `hcompPath`
    at raw `RawTerm.hcomp`.  Refutes hcompPath case via noConfusion. -/
theorem Term.rename_injective_arm_hcomp
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesValueIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (sidesB : Term sourceCtx carrierType sidesRaw),
          Term.rename innerRenaming sidesValue =
            Term.rename innerRenaming sidesB →
          sidesValue = sidesB)
    (capValueIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (capB : Term sourceCtx carrierType capRaw),
          Term.rename innerRenaming capValue =
            Term.rename innerRenaming capB →
          capValue = capB)
    (termB :
      Term sourceCtx carrierType (RawTerm.hcomp sidesRaw capRaw)) :
    Term.rename termRenaming
        (Term.hcomp modeIsUnivalent sidesValue capValue) =
      Term.rename termRenaming termB →
      Term.hcomp modeIsUnivalent sidesValue capValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.hcomp sidesRaw capRaw)),
        (Σ' (inferredModeIsUnivalent : mode = Mode.univalent)
            (sidesB : Term sourceCtx genericType sidesRaw)
            (capB : Term sourceCtx genericType capRaw),
            HEq genericTerm
              (Term.hcomp inferredModeIsUnivalent sidesB capB)) ⊕'
        (Σ' (inferredModeIsUnivalent : mode = Mode.univalent)
            (leftEndpoint : RawTerm sourceScope)
            (rightEndpoint : RawTerm sourceScope)
            (sidesPath :
              Term sourceCtx
                (Ty.path genericType leftEndpoint rightEndpoint) sidesRaw)
            (capB : Term sourceCtx genericType capRaw),
            HEq genericTerm
              (Term.hcompPath inferredModeIsUnivalent leftEndpoint
                rightEndpoint sidesPath capB)) by
    cases key termB with
    | inl caseHcomp =>
        obtain ⟨_, sidesB, capB, termHEqB⟩ := caseHcomp
        cases termHEqB
        dsimp only [Term.rename] at renameEq
        injection renameEq with _ _ _ _ _ sidesRenameEq capRenameEq
        rw [sidesValueIH termRenaming rhoInjective sidesB sidesRenameEq,
            capValueIH termRenaming rhoInjective capB capRenameEq]
    | inr caseHcompPath =>
        obtain ⟨_, leftEnd, rightEnd, sidesPath, capB, termHEqB⟩ := caseHcompPath
        cases termHEqB
        exfalso
        -- Refute Term.hcomp = Term.hcompPath via noConfusion (different ctors).
        have collisionHEq :
            HEq (Term.hcomp modeIsUnivalent
                  (Term.rename termRenaming sidesValue)
                  (Term.rename termRenaming capValue))
                (Term.hcompPath modeIsUnivalent
                  (leftEnd.rename rho) (rightEnd.rename rho)
                  (Term.rename termRenaming sidesPath)
                  (Term.rename termRenaming capB)) :=
          heq_of_eq renameEq
        exact Term.noConfusion (P := False)
          (t := Term.hcomp modeIsUnivalent
                  (Term.rename termRenaming sidesValue)
                  (Term.rename termRenaming capValue))
          (t' := Term.hcompPath modeIsUnivalent
                  (leftEnd.rename rho) (rightEnd.rename rho)
                  (Term.rename termRenaming sidesPath)
                  (Term.rename termRenaming capB))
          rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl
          collisionHEq
  intro genericType genericTerm
  cases genericTerm
  case hcomp inferredModeIsUnivalent sidesB capB =>
    exact PSum.inl ⟨inferredModeIsUnivalent, sidesB, capB, HEq.rfl⟩
  case hcompPath inferredModeIsUnivalent leftEnd rightEnd sidesPath capB =>
    exact PSum.inr ⟨inferredModeIsUnivalent, leftEnd, rightEnd, sidesPath,
      capB, HEq.rfl⟩

/-- `hcompPath` arm: path-shaped homogeneous composition.  Refutes `hcomp`
    sibling via Term.noConfusion. -/
theorem Term.rename_injective_arm_hcompPath
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx
        (Ty.path carrierType leftEndpoint rightEndpoint) sidesPathRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesPathIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (sidesPathB :
            Term sourceCtx
              (Ty.path carrierType leftEndpoint rightEndpoint) sidesPathRaw),
          Term.rename innerRenaming sidesPath =
            Term.rename innerRenaming sidesPathB →
          sidesPath = sidesPathB)
    (capValueIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (capB : Term sourceCtx carrierType capRaw),
          Term.rename innerRenaming capValue =
            Term.rename innerRenaming capB →
          capValue = capB)
    (termB :
      Term sourceCtx carrierType (RawTerm.hcomp sidesPathRaw capRaw)) :
    Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
          sidesPath capValue) =
      Term.rename termRenaming termB →
      Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath capValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.hcomp sidesPathRaw capRaw)),
        (Σ' (inferredModeIsUnivalent : mode = Mode.univalent)
            (sidesB : Term sourceCtx genericType sidesPathRaw)
            (capB : Term sourceCtx genericType capRaw),
            HEq genericTerm
              (Term.hcomp inferredModeIsUnivalent sidesB capB)) ⊕'
        (Σ' (inferredModeIsUnivalent : mode = Mode.univalent)
            (leftEnd : RawTerm sourceScope)
            (rightEnd : RawTerm sourceScope)
            (sidesPathInner :
              Term sourceCtx
                (Ty.path genericType leftEnd rightEnd) sidesPathRaw)
            (capB : Term sourceCtx genericType capRaw),
            HEq genericTerm
              (Term.hcompPath inferredModeIsUnivalent leftEnd
                rightEnd sidesPathInner capB)) by
    cases key termB with
    | inl caseHcomp =>
        obtain ⟨_, sidesB, capB, termHEqB⟩ := caseHcomp
        cases termHEqB
        exfalso
        have collisionHEq :
            HEq (Term.hcompPath modeIsUnivalent
                  (leftEndpoint.rename rho) (rightEndpoint.rename rho)
                  (Term.rename termRenaming sidesPath)
                  (Term.rename termRenaming capValue))
                (Term.hcomp modeIsUnivalent
                  (Term.rename termRenaming sidesB)
                  (Term.rename termRenaming capB)) :=
          heq_of_eq renameEq
        exact Term.noConfusion (P := False)
          (t := Term.hcompPath modeIsUnivalent
                  (leftEndpoint.rename rho) (rightEndpoint.rename rho)
                  (Term.rename termRenaming sidesPath)
                  (Term.rename termRenaming capValue))
          (t' := Term.hcomp modeIsUnivalent
                  (Term.rename termRenaming sidesB)
                  (Term.rename termRenaming capB))
          rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl
          collisionHEq
    | inr caseHcompPath =>
        obtain ⟨_, inferredLeftEnd, inferredRightEnd, sidesPathInner, capB,
          termHEqB⟩ := caseHcompPath
        cases termHEqB
        dsimp only [Term.rename] at renameEq
        injection renameEq with _ _ _ leftRenameEq rightRenameEq _ _
          sidesPathRenameHEq capRenameEq
        have leftEq : leftEndpoint = inferredLeftEnd :=
          RawTerm.rename_injective_under_injective_renaming leftEndpoint
            rhoInjective inferredLeftEnd leftRenameEq
        have rightEq : rightEndpoint = inferredRightEnd :=
          RawTerm.rename_injective_under_injective_renaming rightEndpoint
            rhoInjective inferredRightEnd rightRenameEq
        cases leftEq
        cases rightEq
        rw [sidesPathIH termRenaming rhoInjective sidesPathInner
              (eq_of_heq sidesPathRenameHEq),
            capValueIH termRenaming rhoInjective capB capRenameEq]
  intro genericType genericTerm
  cases genericTerm
  case hcomp inferredModeIsUnivalent sidesB capB =>
    exact PSum.inl ⟨inferredModeIsUnivalent, sidesB, capB, HEq.rfl⟩
  case hcompPath inferredModeIsUnivalent leftEnd rightEnd sidesPathInner capB =>
    exact PSum.inr ⟨inferredModeIsUnivalent, leftEnd, rightEnd, sidesPathInner,
      capB, HEq.rfl⟩

/-! ## η-family rfl/Id rename-injectivity arms.

The η-family ctors (equivReflId, equivReflIdAtId, equivIntroHet,
uaIntroHet, funextRefl, funextReflAtId, funextIntroHet) collide on raw
`RawTerm.equivIntro id id` or `RawTerm.lam (RawTerm.refl applyRaw)`.
For closed/value ctors (equivReflId, equivReflIdAtId), the arm has no
typed children and reduces to a one-line invocation of the existing
`_atEquivIntroEquiv_of_inner` / `_atEquivIntroUniverseId_of_inner`
helpers from `EquivIntro.lean`.  The childInjective HEq predicate
required by those helpers is vacuously satisfied here since the closed
ctors have no actual typed children. -/

-- NOTE: arm_equivReflId / arm_funextRefl / arm_equivReflIdAtId /
-- arm_funextReflAtId / arm_equivIntroHet / arm_uaIntroHet /
-- arm_funextIntroHet deferred: these 4-way (equivIntro) and 3-way
-- (lam-refl) collisions require the heavy machinery from EquivIntro.lean
-- and the not-yet-shipped lam-refl inversion family.  The shipped
-- `_of_inner` helpers (atEquivIntroEquiv / atEquivIntroUniverseId) take
-- termA + termB BOTH heterogeneous + an HEq-style childInjective —
-- but the arm signature has childA-fixed IHs.  Bridging the two
-- requires either:
--   * Strengthening the IHs from childA-fixed to HEq-style (deep
--     dispatcher refactor in the rename_injective driver), or
--   * Writing a per-arm direct cases proof that re-derives the 4-way
--     PSum locally and threads childA-fixed IHs (each arm ~200-400
--     LoC of cases gymnastics).
-- Both options exceed the current session budget.  Deferred to a
-- future session focused on the η-family.

/-! ## Cubical-glue intro arm.

`glueIntro` packages a base value + partial value at a shared baseType
into a Ty.glue typed at (baseType, boundaryWitness).  Both children at
fixed baseType (explicit ctor argument).  The mode = Mode.univalent
witness is an explicit Prop equation slot. -/

/-- `glueIntro` arm: cubical glue intro with 2 children at shared baseType. -/
theorem Term.rename_injective_arm_glueIntro
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (baseB : Term sourceCtx baseType baseRaw),
          Term.rename innerRenaming baseValue =
            Term.rename innerRenaming baseB →
          baseValue = baseB)
    (partialIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (partialB : Term sourceCtx baseType partialRaw),
          Term.rename innerRenaming partialValue =
            Term.rename innerRenaming partialB →
          partialValue = partialB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw)) :
    Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue) =
      Term.rename termRenaming termB →
      Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.glueIntro baseRaw partialRaw)),
        Σ' (inferredModeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredBaseType : Ty level sourceScope),
            Σ' (inferredBoundary : RawTerm sourceScope),
              Σ' (baseB : Term sourceCtx inferredBaseType baseRaw),
                Σ' (partialB : Term sourceCtx inferredBaseType partialRaw),
                  Σ' (_ :
                      genericType =
                        Ty.glue inferredBaseType inferredBoundary),
                    HEq genericTerm
                      (Term.glueIntro inferredModeIsUnivalent
                        inferredBaseType inferredBoundary baseB partialB) by
    obtain ⟨inferredModeIsUnivalent, inferredBaseType, inferredBoundary,
      baseB, partialB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ baseRenameEq partialRenameEq
    rw [baseIH termRenaming rhoInjective baseB baseRenameEq,
        partialIH termRenaming rhoInjective partialB partialRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredBaseType inferredBoundary
    baseTerm partialTerm
  exact ⟨inferredModeIsUnivalent, inferredBaseType, inferredBoundary,
    baseTerm, partialTerm, rfl, HEq.rfl⟩

/-! ## Codata / session arms (parametric intro shapes).

* `codataUnfold` packages initial state + transition into a Ty.codata.  Two
  existential types (stateType, outputType); both children at composed shapes.
* `sessionRecv` packages a channel into a Ty.session.  Single existential
  RawTerm `protocolStep` (no Ty existential); single child at session type.

Both follow the cases-typeEqB pattern established in `refineIntro`. -/

/-- `codataUnfold` arm: codata producer wrapping initial state + transition. -/
theorem Term.rename_injective_arm_codataUnfold
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    (stateIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (stateB : Term sourceCtx stateType stateRaw),
          Term.rename innerRenaming initialState =
            Term.rename innerRenaming stateB →
          initialState = stateB)
    (transitionIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (transitionB :
            Term sourceCtx (Ty.arrow stateType outputType) transitionRaw),
          Term.rename innerRenaming transition =
            Term.rename innerRenaming transitionB →
          transition = transitionB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx (Ty.codata stateType outputType)
        (RawTerm.codataUnfold stateRaw transitionRaw)) :
    Term.rename termRenaming (Term.codataUnfold initialState transition) =
      Term.rename termRenaming termB →
      Term.codataUnfold initialState transition = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.codataUnfold stateRaw transitionRaw)),
        Σ' (inferredStateType : Ty level sourceScope),
          Σ' (inferredOutputType : Ty level sourceScope),
            Σ' (stateB : Term sourceCtx inferredStateType stateRaw),
              Σ' (transitionB :
                  Term sourceCtx
                    (Ty.arrow inferredStateType inferredOutputType)
                    transitionRaw),
                Σ' (_ : genericType =
                    Ty.codata inferredStateType inferredOutputType),
                  HEq genericTerm
                    (Term.codataUnfold stateB transitionB) by
    obtain ⟨inferredStateType, inferredOutputType, stateB, transitionB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ stateRenameEq transitionRenameEq
    rw [stateIH termRenaming rhoInjective stateB stateRenameEq,
        transitionIH termRenaming rhoInjective transitionB transitionRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredStateType inferredOutputType stateTerm transitionTerm
  exact ⟨inferredStateType, inferredOutputType, stateTerm, transitionTerm,
    rfl, HEq.rfl⟩

/-- `sessionSend` arm: session send wrapping channel + payload.  The payload
    type is existential at the Term ctor level; recovered via
    `Ty.rename_injective_under_injective_renaming`. -/
theorem Term.rename_injective_arm_sessionSend
    (rhoInjective : RawRenamingInjective rho)
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (channelIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (channelB : Term sourceCtx (Ty.session protocolStep) channelRaw),
          Term.rename innerRenaming channel =
            Term.rename innerRenaming channelB →
          channel = channelB)
    (payloadIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (payloadB : Term sourceCtx payloadType payloadRaw),
          Term.rename innerRenaming payload =
            Term.rename innerRenaming payloadB →
          payload = payloadB)
    (termB :
      Term sourceCtx (Ty.session protocolStep)
        (RawTerm.sessionSend channelRaw payloadRaw)) :
    Term.rename termRenaming (Term.sessionSend protocolStep channel payload) =
      Term.rename termRenaming termB →
      Term.sessionSend protocolStep channel payload = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sessionSend channelRaw payloadRaw)),
        Σ' (inferredProtocolStep : RawTerm sourceScope),
          Σ' (inferredPayloadType : Ty level sourceScope),
            Σ' (channelB :
                Term sourceCtx (Ty.session inferredProtocolStep) channelRaw),
              Σ' (payloadB : Term sourceCtx inferredPayloadType payloadRaw),
                Σ' (_ : genericType = Ty.session inferredProtocolStep),
                  HEq genericTerm
                    (Term.sessionSend inferredProtocolStep channelB
                      payloadB) by
    obtain ⟨inferredProtocolStep, inferredPayloadType, channelB, payloadB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ payloadTypeRenameEq _ _
      channelRenameEq payloadRenameHEq
    have payloadTypeEq : payloadType = inferredPayloadType :=
      Ty.rename_injective_under_injective_renaming payloadType
        rhoInjective inferredPayloadType payloadTypeRenameEq
    cases payloadTypeEq
    rw [channelIH termRenaming rhoInjective channelB channelRenameEq,
        payloadIH termRenaming rhoInjective payloadB
          (eq_of_heq payloadRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredProtocolStep inferredPayloadType channelTerm payloadTerm
  exact ⟨inferredProtocolStep, inferredPayloadType, channelTerm, payloadTerm,
    rfl, HEq.rfl⟩

/-- `sessionRecv` arm: session receive wrapping a channel at fixed protocol. -/
theorem Term.rename_injective_arm_sessionRecv
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (channelB : Term sourceCtx (Ty.session protocolStep) channelRaw),
          Term.rename innerRenaming channel =
            Term.rename innerRenaming channelB →
          channel = channelB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx (Ty.session protocolStep)
        (RawTerm.sessionRecv channelRaw)) :
    Term.rename termRenaming (Term.sessionRecv channel) =
      Term.rename termRenaming termB →
      Term.sessionRecv channel = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sessionRecv channelRaw)),
        Σ' (inferredProtocolStep : RawTerm sourceScope),
          Σ' (channelB :
              Term sourceCtx (Ty.session inferredProtocolStep) channelRaw),
            Σ' (_ : genericType = Ty.session inferredProtocolStep),
              HEq genericTerm (Term.sessionRecv channelB) by
    obtain ⟨inferredProtocolStep, channelB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ channelRenameEq
    exact congrArg Term.sessionRecv
      (channelIH termRenaming rhoInjective channelB channelRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredProtocolStep channelTerm
  exact ⟨inferredProtocolStep, channelTerm, rfl, HEq.rfl⟩

/-! ## Record / refine intro arms (single-existential type, intro shape).

Two intro-form ctors with outer-type `Ty.<wrapper> <existential>`:
* `recordIntro` packages one field at `singleFieldType` into a Ty.record
* `refineIntro` packages a base value + proof certificate into a Ty.refine

Both mirror the `optionSome` template (free generic outer type via
suffices, recover existential by casing the matcher's type equation).
`refineIntro` adds a raw `predicate` payload at `(scope+1)` — the
predicate is NOT a typed Term, so no IH consumed for it; raw equality
follows from injection. -/

/-- `recordIntro` arm: single-field record at `Ty.record singleFieldType`. -/
theorem Term.rename_injective_arm_recordIntro
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (firstIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (firstB : Term sourceCtx singleFieldType firstRaw),
          Term.rename innerRenaming firstField =
            Term.rename innerRenaming firstB →
          firstField = firstB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx (Ty.record singleFieldType)
        (RawTerm.recordIntro firstRaw)) :
    Term.rename termRenaming (Term.recordIntro firstField) =
      Term.rename termRenaming termB →
      Term.recordIntro firstField = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.recordIntro firstRaw)),
        Σ' (inferredFieldType : Ty level sourceScope),
          Σ' (fieldTerm : Term sourceCtx inferredFieldType firstRaw),
            Σ' (_ : genericType = Ty.record inferredFieldType),
              HEq genericTerm (Term.recordIntro fieldTerm) by
    obtain ⟨inferredFieldType, fieldB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ fieldRenameEq
    exact congrArg Term.recordIntro
      (firstIH termRenaming rhoInjective fieldB fieldRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFieldType fieldTerm
  exact ⟨inferredFieldType, fieldTerm, rfl, HEq.rfl⟩

/-- `refineIntro` arm: refinement-type intro with two children (base value,
    unit-typed proof certificate) and a raw `predicate` payload. -/
theorem Term.rename_injective_arm_refineIntro
    (rhoInjective : RawRenamingInjective rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    (baseIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (baseB : Term sourceCtx baseType valueRaw),
          Term.rename innerRenaming baseValue =
            Term.rename innerRenaming baseB →
          baseValue = baseB)
    (proofIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (proofB : Term sourceCtx Ty.unit proofRaw),
          Term.rename innerRenaming predicateProof =
            Term.rename innerRenaming proofB →
          predicateProof = proofB)
    (termB :
      Term sourceCtx (Ty.refine baseType predicate)
        (RawTerm.refineIntro valueRaw proofRaw)) :
    Term.rename termRenaming
        (Term.refineIntro predicate baseValue predicateProof) =
      Term.rename termRenaming termB →
      Term.refineIntro predicate baseValue predicateProof = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.refineIntro valueRaw proofRaw)),
        Σ' (inferredBaseType : Ty level sourceScope),
          Σ' (inferredPredicate : RawTerm (sourceScope + 1)),
            Σ' (baseB : Term sourceCtx inferredBaseType valueRaw),
              Σ' (proofB : Term sourceCtx Ty.unit proofRaw),
                Σ' (_ : genericType = Ty.refine inferredBaseType inferredPredicate),
                  HEq genericTerm
                    (Term.refineIntro inferredPredicate baseB proofB) by
    obtain ⟨inferredBaseType, inferredPredicate, baseB, proofB,
      typeEqB, termHEqB⟩ := key termB
    -- typeEqB : Ty.refine baseType predicate = Ty.refine inferredBaseType inferredPredicate
    -- Unifies inferredBaseType→baseType and inferredPredicate→predicate atomically,
    -- avoiding the dep-elim wall encountered when decomposing via `injection`.
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ baseRenameEq proofRenameEq
    rw [baseIH termRenaming rhoInjective baseB baseRenameEq,
        proofIH termRenaming rhoInjective proofB proofRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredBaseType inferredPredicate baseTerm proofTerm
  exact ⟨inferredBaseType, inferredPredicate, baseTerm, proofTerm,
    rfl, HEq.rfl⟩

/-! ## Modal-wrapper arms (`modIntro`/`modElim`/`subsume`).

Three modal-wrapper ctors share the shape: a single child at arbitrary
`innerType`, with the OUTER type equal to the child's type (no
projection, no cast).  Each maps `RawTerm.<wrapper> innerRaw` 1-1 to the
typed ctor.  No existential type leak — the matcher unifies the ctor's
local `{innerType}` directly with the arm-bound `innerType`.

NOTE: even though `Mode` lives at `Ctx`, the ctor signature treats both
input and output context as the same `{context : Ctx mode level scope}`
for the current modal kernel layer.  When the K12.25 cross-mode
extension lands (CUMUL-7.1, #1689-#1694), `modIntroCross` /
`modElimCross` will get separate arm helpers; these three are for the
same-mode case. -/

/-- `modIntro` arm: same-mode modal introduction wrapper. -/
theorem Term.rename_injective_arm_modIntro
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (innerB : Term sourceCtx innerType innerRaw),
          Term.rename innerRenaming innerTerm =
            Term.rename innerRenaming innerB →
          innerTerm = innerB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx innerType (RawTerm.modIntro innerRaw)) :
    Term.rename termRenaming (Term.modIntro innerTerm) =
      Term.rename termRenaming termB →
      Term.modIntro innerTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.modIntro innerRaw)),
        Σ' (inferredInnerType : Ty level sourceScope),
          Σ' (innerB : Term sourceCtx inferredInnerType innerRaw),
            Σ' (_ : genericType = inferredInnerType),
              HEq genericTerm (Term.modIntro innerB) by
    obtain ⟨inferredInnerType, innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.modIntro
      (innerIH termRenaming rhoInjective innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTermB
  exact ⟨genericType, innerTermB, rfl, HEq.rfl⟩

/-- `modElim` arm: same-mode modal elimination wrapper. -/
theorem Term.rename_injective_arm_modElim
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (innerB : Term sourceCtx innerType innerRaw),
          Term.rename innerRenaming innerTerm =
            Term.rename innerRenaming innerB →
          innerTerm = innerB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx innerType (RawTerm.modElim innerRaw)) :
    Term.rename termRenaming (Term.modElim innerTerm) =
      Term.rename termRenaming termB →
      Term.modElim innerTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.modElim innerRaw)),
        Σ' (inferredInnerType : Ty level sourceScope),
          Σ' (innerB : Term sourceCtx inferredInnerType innerRaw),
            Σ' (_ : genericType = inferredInnerType),
              HEq genericTerm (Term.modElim innerB) by
    obtain ⟨inferredInnerType, innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.modElim
      (innerIH termRenaming rhoInjective innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTermB
  exact ⟨genericType, innerTermB, rfl, HEq.rfl⟩

/-- `subsume` arm: cumulativity/subsumption wrapper at same mode. -/
theorem Term.rename_injective_arm_subsume
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (innerB : Term sourceCtx innerType innerRaw),
          Term.rename innerRenaming innerTerm =
            Term.rename innerRenaming innerB →
          innerTerm = innerB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx innerType (RawTerm.subsume innerRaw)) :
    Term.rename termRenaming (Term.subsume innerTerm) =
      Term.rename termRenaming termB →
      Term.subsume innerTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.subsume innerRaw)),
        Σ' (inferredInnerType : Ty level sourceScope),
          Σ' (innerB : Term sourceCtx inferredInnerType innerRaw),
            Σ' (_ : genericType = inferredInnerType),
              HEq genericTerm (Term.subsume innerB) by
    obtain ⟨inferredInnerType, innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.subsume
      (innerIH termRenaming rhoInjective innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTermB
  exact ⟨genericType, innerTermB, rfl, HEq.rfl⟩

/-! ## Interval-operation arms (closed outer type, closed child types).

Three cubical interval operations (`intervalOpp` unary, `intervalMeet`/`Join`
binary) all live at outer `Ty.interval` and take children at `Ty.interval`.
No existentials, no casts — mirrors the `natSucc`/`listCons` template with
`Ty.interval` substituted for the closed scalar type. -/

/-- `intervalOpp` arm: unary cubical opposite at `Ty.interval`. -/
theorem Term.rename_injective_arm_intervalOpp
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (innerB : Term sourceCtx Ty.interval innerRaw),
          Term.rename innerRenaming innerValue =
            Term.rename innerRenaming innerB →
          innerValue = innerB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx Ty.interval (RawTerm.intervalOpp innerRaw)) :
    Term.rename termRenaming (Term.intervalOpp innerValue) =
      Term.rename termRenaming termB →
      Term.intervalOpp innerValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.intervalOpp innerRaw)),
        Σ' (innerTerm : Term sourceCtx Ty.interval innerRaw),
          Σ' (_ : genericType = Ty.interval),
            HEq genericTerm (Term.intervalOpp innerTerm) by
    obtain ⟨innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ innerRenameEq
    exact congrArg Term.intervalOpp
      (innerIH termRenaming rhoInjective innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, rfl, HEq.rfl⟩

/-- `intervalMeet` arm: binary cubical meet at `Ty.interval`. -/
theorem Term.rename_injective_arm_intervalMeet
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (leftB : Term sourceCtx Ty.interval leftRaw),
          Term.rename innerRenaming leftValue =
            Term.rename innerRenaming leftB →
          leftValue = leftB)
    (rightIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (rightB : Term sourceCtx Ty.interval rightRaw),
          Term.rename innerRenaming rightValue =
            Term.rename innerRenaming rightB →
          rightValue = rightB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx Ty.interval (RawTerm.intervalMeet leftRaw rightRaw)) :
    Term.rename termRenaming (Term.intervalMeet leftValue rightValue) =
      Term.rename termRenaming termB →
      Term.intervalMeet leftValue rightValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.intervalMeet leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalMeet leftTerm rightTerm) by
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftIH termRenaming rhoInjective leftB leftRenameEq,
        rightIH termRenaming rhoInjective rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

/-- `intervalJoin` arm: binary cubical join at `Ty.interval`. -/
theorem Term.rename_injective_arm_intervalJoin
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (leftB : Term sourceCtx Ty.interval leftRaw),
          Term.rename innerRenaming leftValue =
            Term.rename innerRenaming leftB →
          leftValue = leftB)
    (rightIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (rightB : Term sourceCtx Ty.interval rightRaw),
          Term.rename innerRenaming rightValue =
            Term.rename innerRenaming rightB →
          rightValue = rightB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx Ty.interval (RawTerm.intervalJoin leftRaw rightRaw)) :
    Term.rename termRenaming (Term.intervalJoin leftValue rightValue) =
      Term.rename termRenaming termB →
      Term.intervalJoin leftValue rightValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.intervalJoin leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalJoin leftTerm rightTerm) by
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftIH termRenaming rhoInjective leftB leftRenameEq,
        rightIH termRenaming rhoInjective rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

/-! ## Projection-form arms (single-child elim shapes).

Three single-child projection ctors whose OUTPUT type matches a sub-component
of the child's type (no `subst0` cast on the output, distinguishing them from
the cast-wall family `appPi`/`snd`/`boolElim`/…):

* `recordProj`  : child at `Ty.record singleFieldType`, output `singleFieldType`.
  `singleFieldType` is the output type so the matcher unifies it directly with
  `genericType` — no Ty existential needed.
* `codataDest`  : child at `Ty.codata stateType outputType`, output `outputType`.
  `outputType` aligns with `genericType`; `stateType` is purely existential
  (only in child's type) and recovered via `Ty.rename_injective_under_injective_renaming`.
* `refineElim`  : child at `Ty.refine baseType predicate`, output `baseType`.
  `baseType` aligns with `genericType`; the raw `predicate` is purely
  existential and recovered via `RawTerm.rename_injective_under_injective_renaming`
  under `rho.lift` (predicate lives at `scope + 1`). -/

/-- `recordProj` arm: single-field record projection.  `singleFieldType` IS the
    output type so no Ty existential — the `cases genericTerm` matcher unifies
    the inferred field type with `genericType` directly.  Mirrors the `natElim`
    pattern (motiveType-as-result). -/
theorem Term.rename_injective_arm_recordProj
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (recordB : Term sourceCtx (Ty.record singleFieldType) recordRaw),
          Term.rename innerRenaming recordValue =
            Term.rename innerRenaming recordB →
          recordValue = recordB)
    (rhoInjective : RawRenamingInjective rho)
    (termB :
      Term sourceCtx singleFieldType (RawTerm.recordProj recordRaw)) :
    Term.rename termRenaming (Term.recordProj recordValue) =
      Term.rename termRenaming termB →
      Term.recordProj recordValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.recordProj recordRaw)),
        Σ' (recordB :
            Term sourceCtx (Ty.record genericType) recordRaw),
          HEq genericTerm (Term.recordProj recordB) by
    obtain ⟨recordB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ recordRenameEq
    exact congrArg Term.recordProj
      (recordIH termRenaming rhoInjective recordB recordRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i recordTerm
  exact ⟨recordTerm, HEq.rfl⟩

/-- `codataDest` arm: codata observation.  `outputType` aligns with
    `genericType`; `stateType` recovered as a Ty existential via the
    matcher's rename-injectivity. -/
theorem Term.rename_injective_arm_codataDest
    (rhoInjective : RawRenamingInjective rho)
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    (codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (codataB :
            Term sourceCtx (Ty.codata stateType outputType) codataRaw),
          Term.rename innerRenaming codataValue =
            Term.rename innerRenaming codataB →
          codataValue = codataB)
    (termB :
      Term sourceCtx outputType (RawTerm.codataDest codataRaw)) :
    Term.rename termRenaming (Term.codataDest codataValue) =
      Term.rename termRenaming termB →
      Term.codataDest codataValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.codataDest codataRaw)),
        Σ' (inferredStateType : Ty level sourceScope),
          Σ' (codataB :
              Term sourceCtx (Ty.codata inferredStateType genericType)
                codataRaw),
            HEq genericTerm (Term.codataDest codataB) by
    obtain ⟨inferredStateType, codataB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ stateTypeRenameEq _ _ codataRenameHEq
    have stateTypeEq : stateType = inferredStateType :=
      Ty.rename_injective_under_injective_renaming stateType
        rhoInjective inferredStateType stateTypeRenameEq
    cases stateTypeEq
    exact congrArg Term.codataDest
      (codataIH termRenaming rhoInjective codataB
        (eq_of_heq codataRenameHEq))
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredStateType codataTerm
  exact ⟨inferredStateType, codataTerm, HEq.rfl⟩

/-- `refineElim` arm: refinement-type elimination.  `baseType` aligns with
    `genericType`; raw `predicate` recovered as a RawTerm existential via
    `RawTerm.rename_injective_under_injective_renaming` under `rho.lift`
    (predicate lives at `scope + 1`). -/
theorem Term.rename_injective_arm_refineElim
    (rhoInjective : RawRenamingInjective rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (refinedIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (refinedB :
            Term sourceCtx (Ty.refine baseType predicate) refinedRaw),
          Term.rename innerRenaming refinedValue =
            Term.rename innerRenaming refinedB →
          refinedValue = refinedB)
    (termB :
      Term sourceCtx baseType (RawTerm.refineElim refinedRaw)) :
    Term.rename termRenaming (Term.refineElim refinedValue) =
      Term.rename termRenaming termB →
      Term.refineElim refinedValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.refineElim refinedRaw)),
        Σ' (inferredPredicate : RawTerm (sourceScope + 1)),
          Σ' (refinedB :
              Term sourceCtx (Ty.refine genericType inferredPredicate)
                refinedRaw),
            HEq genericTerm (Term.refineElim refinedB) by
    obtain ⟨inferredPredicate, refinedB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ predicateRenameEq _ refinedRenameHEq
    have predicateEq : predicate = inferredPredicate :=
      RawTerm.rename_injective_under_injective_renaming predicate
        (RawRenamingInjective.lift rhoInjective) inferredPredicate
        predicateRenameEq
    cases predicateEq
    exact congrArg Term.refineElim
      (refinedIH termRenaming rhoInjective refinedB
        (eq_of_heq refinedRenameHEq))
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredPredicate refinedTerm
  exact ⟨inferredPredicate, refinedTerm, HEq.rfl⟩

/-- `pathLam` arm: cubical interval binder with body in `Ty.interval`-extended
    context.  `RawTerm.pathLam` is uniquely produced by `Term.pathLam`, so the
    `suffices key ... cases genericTerm` pattern lands a single arm; no PSum
    refutation needed.  Body cast follows the `lam` template via
    `termRenameInjectiveCastHEq` over `Ty.weaken_rename_commute`. -/
theorem Term.rename_injective_arm_pathLam
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming (sourceScope + 1) innerTargetScope}
        (innerRenaming :
          TermRenaming (sourceCtx.cons Ty.interval) innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (bodyB :
            Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw),
          Term.rename innerRenaming body = Term.rename innerRenaming bodyB →
          body = bodyB)
    (termB :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw)) :
    Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint body) =
      Term.rename termRenaming termB →
      Term.pathLam modeIsUnivalent carrierType leftEndpoint
        rightEndpoint body = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.pathLam bodyRaw)),
        Σ' (inferredModeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredCarrier : Ty level sourceScope),
            Σ' (inferredLeft : RawTerm sourceScope),
              Σ' (inferredRight : RawTerm sourceScope),
                Σ' (bodyB : Term (sourceCtx.cons Ty.interval)
                    inferredCarrier.weaken bodyRaw),
                  Σ' (_ : genericType =
                      Ty.path inferredCarrier inferredLeft inferredRight),
                    HEq genericTerm
                      (Term.pathLam inferredModeIsUnivalent inferredCarrier
                        inferredLeft inferredRight bodyB) by
    obtain ⟨_, inferredCarrier, inferredLeft, inferredRight, bodyB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ bodyRenameEq
    have bodyRenameUncastHEq :
        HEq (Term.rename (termRenaming.lift Ty.interval) body)
            (Term.rename (termRenaming.lift Ty.interval) bodyB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (Ty.weaken_rename_commute rho carrierType)
            (Term.rename (termRenaming.lift Ty.interval) body)))
        (HEq.trans (heq_of_eq bodyRenameEq)
          (termRenameInjectiveCastHEq
            (Ty.weaken_rename_commute rho carrierType)
            (Term.rename (termRenaming.lift Ty.interval) bodyB)))
    have bodyEq : body = bodyB :=
      bodyIH (termRenaming.lift Ty.interval)
        (RawRenamingInjective.lift rhoInjective) bodyB
        (eq_of_heq bodyRenameUncastHEq)
    cases bodyEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredCarrier inferredLeft
    inferredRight bodyTerm
  exact ⟨inferredModeIsUnivalent, inferredCarrier, inferredLeft,
    inferredRight, bodyTerm, rfl, HEq.rfl⟩

/-! ## Tier-A unique-raw arms (cumulUp / effectPerform / uaToEquiv /
       equivApply / transp).

The remaining 25 Tier-{B,C,D} ctors (appPi/snd/boolElim/idJ/oeqJ/oeqFunext/
idStrictRec/pathApp/glueElim/hcomp/hcompPath/universeCode/equivReflId/
funextRefl/equivReflIdAtId/funextReflAtId/equivIntroHet/equivApp/uaIntroHet/
funextIntroHet) defer to deeper sessions: cast-on-result walls,
dependent-eliminator existentials, 4-way η collisions, and the toNat
non-injectivity wall demand more elaborate machinery (Term.noConfusion HEq-
aware form per `feedback_lean_noconfusion_heq_aware`, generalized
strengthening helpers).  The five Tier-A ctors below all live at distinct
RawTerm shapes with no result-type casts, so the standard
`suffices key + cases genericTerm + injection + IH` recipe closes them
zero-axiom in ~70 LoC each. -/

/-- `cumulUp` arm: universe-cumulativity wrapper.  Outer `higherLevel`
    pinned by the result `Ty.universe higherLevel levelLeHigh`; inner
    `lowerLevel`, `cumulMonotone`, `levelLeLow` are existentials carried
    in the Σ' chain.  Raw is the unique non-colliding
    `RawTerm.cumulUpMarker codeRaw`.  Discharges via `injection renameEq`
    on `Term.rename` of `cumulUp` (no result cast). -/
theorem Term.rename_injective_arm_cumulUp
    (rhoInjective : RawRenamingInjective rho)
    {higherLevel : UniverseLevel}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw : RawTerm sourceScope}
    (lowerLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (typeCodeB :
            Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw),
          Term.rename innerRenaming typeCode =
            Term.rename innerRenaming typeCodeB →
          typeCode = typeCodeB)
    (termB :
      Term sourceCtx (Ty.universe higherLevel levelLeHigh)
        (RawTerm.cumulUpMarker codeRaw)) :
    Term.rename termRenaming
        (Term.cumulUp (context := sourceCtx) lowerLevel higherLevel
          cumulMonotone levelLeLow levelLeHigh typeCode) =
      Term.rename termRenaming termB →
      Term.cumulUp (context := sourceCtx) lowerLevel higherLevel
          cumulMonotone levelLeLow levelLeHigh typeCode = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm :
          Term sourceCtx genericType (RawTerm.cumulUpMarker codeRaw)),
        Σ' (inferredLowerLevel : UniverseLevel),
          Σ' (inferredHigherLevel : UniverseLevel),
            Σ' (inferredCumulMonotone :
                inferredLowerLevel.toNat ≤ inferredHigherLevel.toNat),
              Σ' (inferredLevelLeLow :
                  inferredLowerLevel.toNat + 1 ≤ level),
                Σ' (inferredLevelLeHigh :
                    inferredHigherLevel.toNat + 1 ≤ level),
                  Σ' (typeCodeB :
                      Term sourceCtx
                        (Ty.universe inferredLowerLevel
                          inferredLevelLeLow) codeRaw),
                    Σ' (_ : genericType =
                        Ty.universe inferredHigherLevel
                          inferredLevelLeHigh),
                      HEq genericTerm
                        (Term.cumulUp (context := sourceCtx)
                          inferredLowerLevel inferredHigherLevel
                          inferredCumulMonotone inferredLevelLeLow
                          inferredLevelLeHigh typeCodeB) by
    obtain ⟨_, _, _, _, _, typeCodeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with lowerLevelEq _ cumulMonotoneEq levelLeLowEq _
      typeCodeRenameHEq
    cases lowerLevelEq
    cases cumulMonotoneEq
    cases levelLeLowEq
    have typeCodeEq : typeCode = typeCodeB :=
      typeCodeIH termRenaming rhoInjective typeCodeB
        (eq_of_heq typeCodeRenameHEq)
    cases typeCodeEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLower inferredHigher inferredCumul inferredLeLow
    inferredLeHigh inferredTypeCode
  exact ⟨inferredLower, inferredHigher, inferredCumul, inferredLeLow,
    inferredLeHigh, inferredTypeCode, rfl, HEq.rfl⟩

/-- `equivApply` arm: univalence-β application.  Outer `carrierB` pinned
    by result; inner `carrierA` is existential, recovered via
    `Ty.rename_injective_under_injective_renaming` on the renamed Ty.equiv
    head's first argument.  Two typed subterms `equivTerm`/`argumentTerm`
    discharge via their type-fixed IHs once carrierA aligns. -/
theorem Term.rename_injective_arm_equivApply
    (rhoInjective : RawRenamingInjective rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (equivB :
            Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw),
          Term.rename innerRenaming equivTerm =
            Term.rename innerRenaming equivB →
          equivTerm = equivB)
    (argumentTermIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (argumentB : Term sourceCtx carrierA argumentRaw),
          Term.rename innerRenaming argumentTerm =
            Term.rename innerRenaming argumentB →
          argumentTerm = argumentB)
    (termB :
      Term sourceCtx carrierB
        (RawTerm.equivApply equivRaw argumentRaw)) :
    Term.rename termRenaming (Term.equivApply equivTerm argumentTerm) =
      Term.rename termRenaming termB →
      Term.equivApply equivTerm argumentTerm = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.equivApply equivRaw argumentRaw)),
        Σ' (inferredCarrierA : Ty level sourceScope),
          Σ' (equivB :
              Term sourceCtx (Ty.equiv inferredCarrierA genericType)
                equivRaw),
            Σ' (argumentB :
                Term sourceCtx inferredCarrierA argumentRaw),
              HEq genericTerm (Term.equivApply equivB argumentB) by
    obtain ⟨inferredCarrierA, equivB, argumentB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ carrierARenameEq _ _ _ equivRenameHEq
      argumentRenameHEq
    have carrierAEq : carrierA = inferredCarrierA :=
      Ty.rename_injective_under_injective_renaming carrierA
        rhoInjective inferredCarrierA carrierARenameEq
    cases carrierAEq
    have equivEq : equivTerm = equivB :=
      equivTermIH termRenaming rhoInjective equivB
        (eq_of_heq equivRenameHEq)
    have argumentEq : argumentTerm = argumentB :=
      argumentTermIH termRenaming rhoInjective argumentB
        (eq_of_heq argumentRenameHEq)
    cases equivEq
    cases argumentEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrierA equivTermB argumentTermB
  exact ⟨inferredCarrierA, equivTermB, argumentTermB, HEq.rfl⟩

/-- `uaToEquiv` arm: univalence-β extractor.  Outer `leftTy`/`rightTy`
    pinned by result `Ty.equiv`; inner `innerLevel`/`innerLevelLt`/
    `leftTyRaw`/`rightTyRaw` are existentials carried in Σ' chain.
    Five raw existentials handled via `RawTerm.rename_injective_under_
    injective_renaming` after level alignment via `cases innerLevelEq`. -/
theorem Term.rename_injective_arm_uaToEquiv
    (rhoInjective : RawRenamingInjective rho)
    {leftTy rightTy : Ty level sourceScope}
    {proofRaw : RawTerm sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    (proof : Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (proofB : Term sourceCtx
            (Ty.id (Ty.universe innerLevel innerLevelLt)
              leftTyRaw rightTyRaw)
            proofRaw),
          Term.rename innerRenaming proof =
            Term.rename innerRenaming proofB →
          proof = proofB)
    (termB : Term sourceCtx (Ty.equiv leftTy rightTy)
        (RawTerm.uaToEquiv proofRaw)) :
    Term.rename termRenaming
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proof) =
      Term.rename termRenaming termB →
      Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.uaToEquiv proofRaw)),
        Σ' (inferredInnerLevel : UniverseLevel),
          Σ' (inferredInnerLevelLt :
              inferredInnerLevel.toNat + 1 ≤ level),
            Σ' (inferredLeftTy : Ty level sourceScope),
              Σ' (inferredRightTy : Ty level sourceScope),
                Σ' (inferredLeftTyRaw : RawTerm sourceScope),
                  Σ' (inferredRightTyRaw : RawTerm sourceScope),
                    Σ' (proofB : Term sourceCtx
                        (Ty.id (Ty.universe inferredInnerLevel
                            inferredInnerLevelLt)
                          inferredLeftTyRaw inferredRightTyRaw)
                        proofRaw),
                      Σ' (_ : genericType =
                          Ty.equiv inferredLeftTy inferredRightTy),
                        HEq genericTerm
                          (Term.uaToEquiv inferredInnerLevel
                            inferredInnerLevelLt inferredLeftTy
                            inferredRightTy inferredLeftTyRaw
                            inferredRightTyRaw proofB) by
    obtain ⟨inferredInnerLevel, inferredInnerLevelLt, _, _,
      inferredLeftTyRaw, inferredRightTyRaw, proofB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ _ innerLevelEq _ _ leftRawRenameEq
      rightRawRenameEq _ proofRenameHEq
    cases innerLevelEq
    have leftRawEq : leftTyRaw = inferredLeftTyRaw :=
      RawTerm.rename_injective_under_injective_renaming leftTyRaw
        rhoInjective inferredLeftTyRaw leftRawRenameEq
    have rightRawEq : rightTyRaw = inferredRightTyRaw :=
      RawTerm.rename_injective_under_injective_renaming rightTyRaw
        rhoInjective inferredRightTyRaw rightRawRenameEq
    cases leftRawEq
    cases rightRawEq
    have proofEq : proof = proofB :=
      proofIH termRenaming rhoInjective proofB
        (eq_of_heq proofRenameHEq)
    cases proofEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredInnerLevel inferredInnerLevelLt inferredLeftTy
    inferredRightTy inferredLeftTyRaw inferredRightTyRaw proofTerm
  exact ⟨inferredInnerLevel, inferredInnerLevelLt, inferredLeftTy,
    inferredRightTy, inferredLeftTyRaw, inferredRightTyRaw, proofTerm,
    rfl, HEq.rfl⟩

/-- `transp` arm: cubical transport across a `Ty.path` of universes.
    Outer `targetType` pinned by result type.  Existentials:
    `modeIsUnivalent` (Mode prop eq), `universeLevel`, `universeLevelLt`,
    `sourceType` (Ty), `sourceTypeRaw`/`targetTypeRaw` (raw payloads).
    Two typed subterms `typePath` + `sourceValue` with their own IHs.
    Discharge: cases modeEq/universeLevelEq/universeLevelLtEq, then
    Ty.rename_injective for sourceType, RawTerm.rename_injective twice
    for the raw payloads, then typed IHs via eq_of_heq. -/
theorem Term.rename_injective_arm_transp
    (rhoInjective : RawRenamingInjective rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {targetType : Ty level sourceScope}
    {pathRaw sourceRaw : RawTerm sourceScope}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (typePathIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (typePathB : Term sourceCtx
            (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw)
            pathRaw),
          Term.rename innerRenaming typePath =
            Term.rename innerRenaming typePathB →
          typePath = typePathB)
    (sourceValueIH :
      ∀ {innerTargetScope : Nat}
        {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (sourceValueB : Term sourceCtx sourceType sourceRaw),
          Term.rename innerRenaming sourceValue =
            Term.rename innerRenaming sourceValueB →
          sourceValue = sourceValueB)
    (termB : Term sourceCtx targetType
        (RawTerm.transp pathRaw sourceRaw)) :
    Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath
          sourceValue) =
      Term.rename termRenaming termB →
      Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.transp pathRaw sourceRaw)),
        Σ' (inferredModeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredUniverseLevel : UniverseLevel),
            Σ' (inferredUniverseLevelLt :
                inferredUniverseLevel.toNat + 1 ≤ level),
              Σ' (inferredSourceType : Ty level sourceScope),
                Σ' (inferredTargetType : Ty level sourceScope),
                  Σ' (inferredSourceTypeRaw : RawTerm sourceScope),
                    Σ' (inferredTargetTypeRaw : RawTerm sourceScope),
                      Σ' (typePathB :
                          Term sourceCtx
                            (Ty.path
                              (Ty.universe inferredUniverseLevel
                                inferredUniverseLevelLt)
                              inferredSourceTypeRaw
                              inferredTargetTypeRaw)
                            pathRaw),
                        Σ' (sourceValueB :
                            Term sourceCtx inferredSourceType sourceRaw),
                          Σ' (_ : genericType = inferredTargetType),
                            HEq genericTerm
                              (Term.transp inferredModeIsUnivalent
                                inferredUniverseLevel
                                inferredUniverseLevelLt
                                inferredSourceType inferredTargetType
                                inferredSourceTypeRaw
                                inferredTargetTypeRaw typePathB
                                sourceValueB) by
    obtain ⟨_, _, _, _, _, _, _, typePathB, sourceValueB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with _ universeLevelEq universeLevelLtEq
      sourceTypeRenameEq _ sourceTypeRawRenameEq targetTypeRawRenameEq
      _ _ typePathRenameHEq sourceValueRenameHEq
    cases universeLevelEq
    cases universeLevelLtEq
    have sourceTypeEq : sourceType = _ :=
      Ty.rename_injective_under_injective_renaming sourceType
        rhoInjective _ sourceTypeRenameEq
    cases sourceTypeEq
    have sourceTypeRawEq : sourceTypeRaw = _ :=
      RawTerm.rename_injective_under_injective_renaming sourceTypeRaw
        rhoInjective _ sourceTypeRawRenameEq
    cases sourceTypeRawEq
    have targetTypeRawEq : targetTypeRaw = _ :=
      RawTerm.rename_injective_under_injective_renaming targetTypeRaw
        rhoInjective _ targetTypeRawRenameEq
    cases targetTypeRawEq
    have typePathEq : typePath = typePathB :=
      typePathIH termRenaming rhoInjective typePathB
        (eq_of_heq typePathRenameHEq)
    have sourceValueEq : sourceValue = sourceValueB :=
      sourceValueIH termRenaming rhoInjective sourceValueB
        (eq_of_heq sourceValueRenameHEq)
    cases typePathEq
    cases sourceValueEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredUniverseLevel
    inferredUniverseLevelLt inferredSourceType inferredSourceTypeRaw
    inferredTargetTypeRaw typePathTerm sourceValueTerm
  exact ⟨inferredModeIsUnivalent, inferredUniverseLevel,
    inferredUniverseLevelLt, inferredSourceType, genericType,
    inferredSourceTypeRaw, inferredTargetTypeRaw, typePathTerm,
    sourceValueTerm, rfl, HEq.rfl⟩

/-! ## Closed-ctor arms (one-liners reusing existing standalone helpers)

For closed constructors (no child terms, just `Term.<ctor>` at a fixed type),
the `induction termA` IHs are vacuous (no child IHs needed).  The arm helper
is a one-line wrapper around the existing `Term.rename_injective_at<Ctor>`
standalone helper.  All of these are zero-axiom by construction since the
standalone helpers ship zero-axiom. -/

/-- `var` arm: vacuous IHs (no children).  Forwards to `atVar`. -/
theorem Term.rename_injective_arm_var
    {position : Fin sourceScope}
    (termB :
      Term sourceCtx (varType sourceCtx position) (RawTerm.var position)) :
    Term.rename termRenaming (Term.var position) =
      Term.rename termRenaming termB → Term.var position = termB :=
  Term.rename_injective_atVar termRenaming (Term.var position) termB

/-- `unit` arm: closed-type unit term. -/
theorem Term.rename_injective_arm_unit
    (termB : Term sourceCtx Ty.unit RawTerm.unit) :
    Term.rename termRenaming (Term.unit (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.unit (context := sourceCtx) = termB :=
  Term.rename_injective_atUnit termRenaming (Term.unit (context := sourceCtx))
    termB

/-- `boolTrue` arm. -/
theorem Term.rename_injective_arm_boolTrue
    (termB : Term sourceCtx Ty.bool RawTerm.boolTrue) :
    Term.rename termRenaming (Term.boolTrue (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.boolTrue (context := sourceCtx) = termB :=
  Term.rename_injective_atBoolTrue termRenaming
    (Term.boolTrue (context := sourceCtx)) termB

/-- `boolFalse` arm. -/
theorem Term.rename_injective_arm_boolFalse
    (termB : Term sourceCtx Ty.bool RawTerm.boolFalse) :
    Term.rename termRenaming (Term.boolFalse (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.boolFalse (context := sourceCtx) = termB :=
  Term.rename_injective_atBoolFalse termRenaming
    (Term.boolFalse (context := sourceCtx)) termB

/-- `natZero` arm. -/
theorem Term.rename_injective_arm_natZero
    (termB : Term sourceCtx Ty.nat RawTerm.natZero) :
    Term.rename termRenaming (Term.natZero (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.natZero (context := sourceCtx) = termB :=
  Term.rename_injective_atNatZero termRenaming
    (Term.natZero (context := sourceCtx)) termB

/-- `listNil` arm: closed at the parametric `Ty.listType elementType`. -/
theorem Term.rename_injective_arm_listNil
    {elementType : Ty level sourceScope}
    (termB : Term sourceCtx (Ty.listType elementType) RawTerm.listNil) :
    Term.rename termRenaming
        (Term.listNil (context := sourceCtx) (elementType := elementType)) =
      Term.rename termRenaming termB →
      Term.listNil (context := sourceCtx) (elementType := elementType) =
        termB :=
  Term.rename_injective_atListNil termRenaming
    (Term.listNil (context := sourceCtx) (elementType := elementType)) termB

/-- `optionNone` arm: closed at the parametric `Ty.optionType elementType`. -/
theorem Term.rename_injective_arm_optionNone
    {elementType : Ty level sourceScope}
    (termB : Term sourceCtx (Ty.optionType elementType) RawTerm.optionNone) :
    Term.rename termRenaming
        (Term.optionNone (context := sourceCtx)
          (elementType := elementType)) =
      Term.rename termRenaming termB →
      Term.optionNone (context := sourceCtx) (elementType := elementType) =
        termB :=
  Term.rename_injective_atOptionNone termRenaming
    (Term.optionNone (context := sourceCtx) (elementType := elementType))
    termB

/-- `refl` arm: HoTT-style identity reflexivity at `Ty.id`. -/
theorem Term.rename_injective_arm_refl
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (termB :
      Term sourceCtx (Ty.id carrier rawWitness rawWitness)
        (RawTerm.refl rawWitness)) :
    Term.rename termRenaming
        (Term.refl (context := sourceCtx) carrier rawWitness) =
      Term.rename termRenaming termB →
      Term.refl (context := sourceCtx) carrier rawWitness = termB :=
  Term.rename_injective_atRefl termRenaming
    (Term.refl (context := sourceCtx) carrier rawWitness) termB

/-- `oeqRefl` arm: observational-equality reflexivity at `Ty.oeq`. -/
theorem Term.rename_injective_arm_oeqRefl
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (termB :
      Term sourceCtx (Ty.oeq carrier rawWitness rawWitness)
        (RawTerm.oeqRefl rawWitness)) :
    Term.rename termRenaming
        (Term.oeqRefl (context := sourceCtx) carrier rawWitness) =
      Term.rename termRenaming termB →
      Term.oeqRefl (context := sourceCtx) carrier rawWitness = termB :=
  Term.rename_injective_atOEqRefl termRenaming
    (Term.oeqRefl (context := sourceCtx) carrier rawWitness) termB

/-- `idStrictRefl` arm: strict-mode identity reflexivity at `Ty.idStrict`.
The standalone `atIdStrictRefl` helper carries the `modeIsStrict` proof
explicitly, so the arm helper threads it through. -/
theorem Term.rename_injective_arm_idStrictRefl
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope)
    (termB :
      Term sourceCtx (Ty.idStrict carrier rawWitness rawWitness)
        (RawTerm.idStrictRefl rawWitness)) :
    Term.rename termRenaming
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
          rawWitness) =
      Term.rename termRenaming termB →
      Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
          rawWitness =
        termB :=
  Term.rename_injective_atIdStrictRefl termRenaming
    (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
      rawWitness)
    termB

/-- `interval0` arm: cubical interval endpoint 0. -/
theorem Term.rename_injective_arm_interval0
    (termB : Term sourceCtx Ty.interval RawTerm.interval0) :
    Term.rename termRenaming (Term.interval0 (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.interval0 (context := sourceCtx) = termB :=
  Term.rename_injective_atInterval0 termRenaming
    (Term.interval0 (context := sourceCtx)) termB

/-- `interval1` arm: cubical interval endpoint 1. -/
theorem Term.rename_injective_arm_interval1
    (termB : Term sourceCtx Ty.interval RawTerm.interval1) :
    Term.rename termRenaming (Term.interval1 (context := sourceCtx)) =
      Term.rename termRenaming termB →
      Term.interval1 (context := sourceCtx) = termB :=
  Term.rename_injective_atInterval1 termRenaming
    (Term.interval1 (context := sourceCtx)) termB

/-! ## Type-code arms — 10 closed wrappers at `Ty.universe` outer type.

Each type code is an encoded type living inside the universe `Ty.universe
outerLevel levelLe`.  The raw is the code-name applied to its
component code raws.  No child IH needed — the at-helpers internally
close via a free-`genericType`-via-suffices pattern with cases on the
universe constructor. -/

/-- `arrowCode` arm: encoded arrow type code. -/
theorem Term.rename_injective_arm_arrowCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)) :
    Term.rename termRenaming
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) =
      Term.rename termRenaming termB →
      Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw = termB :=
  Term.rename_injective_atArrowCode termRenaming
    (Term.arrowCode (context := sourceCtx) outerLevel levelLe
      domainCodeRaw codomainCodeRaw) termB

/-- `piTyCode` arm: encoded dependent-Π type code. -/
theorem Term.rename_injective_arm_piTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)) :
    Term.rename termRenaming
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) =
      Term.rename termRenaming termB →
      Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw = termB :=
  Term.rename_injective_atPiTyCode termRenaming
    (Term.piTyCode (context := sourceCtx) outerLevel levelLe
      domainCodeRaw codomainCodeRaw) termB

/-- `sigmaTyCode` arm: encoded dependent-Σ type code. -/
theorem Term.rename_injective_arm_sigmaTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw : RawTerm sourceScope)
    (secondCodeRaw : RawTerm (sourceScope + 1))
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw)) :
    Term.rename termRenaming
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw) =
      Term.rename termRenaming termB →
      Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw = termB :=
  Term.rename_injective_atSigmaTyCode termRenaming
    (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
      firstCodeRaw secondCodeRaw) termB

/-- `productCode` arm: encoded non-dependent product type code. -/
theorem Term.rename_injective_arm_productCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.productCode firstCodeRaw secondCodeRaw)) :
    Term.rename termRenaming
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw) =
      Term.rename termRenaming termB →
      Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw = termB :=
  Term.rename_injective_atProductCode termRenaming
    (Term.productCode (context := sourceCtx) outerLevel levelLe
      firstCodeRaw secondCodeRaw) termB

/-- `sumCode` arm: encoded non-dependent sum type code. -/
theorem Term.rename_injective_arm_sumCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.sumCode leftCodeRaw rightCodeRaw)) :
    Term.rename termRenaming
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) =
      Term.rename termRenaming termB →
      Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw = termB :=
  Term.rename_injective_atSumCode termRenaming
    (Term.sumCode (context := sourceCtx) outerLevel levelLe
      leftCodeRaw rightCodeRaw) termB

/-- `listCode` arm: encoded list type code. -/
theorem Term.rename_injective_arm_listCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.listCode elementCodeRaw)) :
    Term.rename termRenaming
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) =
      Term.rename termRenaming termB →
      Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw = termB :=
  Term.rename_injective_atListCode termRenaming
    (Term.listCode (context := sourceCtx) outerLevel levelLe
      elementCodeRaw) termB

/-- `optionCode` arm: encoded option type code. -/
theorem Term.rename_injective_arm_optionCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.optionCode elementCodeRaw)) :
    Term.rename termRenaming
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) =
      Term.rename termRenaming termB →
      Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw = termB :=
  Term.rename_injective_atOptionCode termRenaming
    (Term.optionCode (context := sourceCtx) outerLevel levelLe
      elementCodeRaw) termB

/-- `eitherCode` arm: encoded either type code. -/
theorem Term.rename_injective_arm_eitherCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.eitherCode leftCodeRaw rightCodeRaw)) :
    Term.rename termRenaming
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) =
      Term.rename termRenaming termB →
      Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw = termB :=
  Term.rename_injective_atEitherCode termRenaming
    (Term.eitherCode (context := sourceCtx) outerLevel levelLe
      leftCodeRaw rightCodeRaw) termB

/-- `idCode` arm: encoded HoTT identity type code with type-code +
endpoint-raws. -/
theorem Term.rename_injective_arm_idCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.idCode typeCodeRaw leftRaw rightRaw)) :
    Term.rename termRenaming
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw) =
      Term.rename termRenaming termB →
      Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw = termB :=
  Term.rename_injective_atIdCode termRenaming
    (Term.idCode (context := sourceCtx) outerLevel levelLe
      typeCodeRaw leftRaw rightRaw) termB

/-- `equivCode` arm: encoded equivalence type code between two type
codes. -/
theorem Term.rename_injective_arm_equivCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)) :
    Term.rename termRenaming
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw) =
      Term.rename termRenaming termB →
      Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw = termB :=
  Term.rename_injective_atEquivCode termRenaming
    (Term.equivCode (context := sourceCtx) outerLevel levelLe
      leftTypeCodeRaw rightTypeCodeRaw) termB

end InductiveArms

end LeanFX2
