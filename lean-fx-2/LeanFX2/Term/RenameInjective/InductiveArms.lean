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

end LeanFX2
