import LeanFX2.Reduction.ParRed
import LeanFX2.Term.Subst

/-! # Reduction/Compat/TypeCodes — typed compositional compat for CUMUL-2.4 type codes

#1590-CORE addition (2026-05-08).  Bundles the 10 per-ctor
`Step.par.<X>CodeCong.{rename,subst}_compatible` theorems for the
CUMUL-2.4 typed type-code constructors:

* `arrowCodeCong` — non-dependent function type code (binary)
* `piTyCodeCong` — dependent function type code (binary, codomain at scope+1)
* `sigmaTyCodeCong` — dependent pair type code (binary, second at scope+1)
* `productCodeCong` — non-dependent pair type code (binary)
* `sumCodeCong` — binary sum type code (binary)
* `listCodeCong` — list type code (unary)
* `optionCodeCong` — option type code (unary)
* `eitherCodeCong` — either type code (binary)
* `idCodeCong` — identity type code (ternary: typeCode + leftRaw + rightRaw)
* `equivCodeCong` — equivalence type code (binary)

Each ctor produces a Term at `Ty.universe outerLevel levelLe`, whose
`rename` / `subst` composition is structural — no `Ty.weaken_*_commute`
cast is needed because the universe Ty is scope-independent.

The `Step.par.<X>CodeCong` constructor takes one or more `RawStep.par`
premises (one per schematic raw payload).  Binder-shape codes
(`piTyCode`, `sigmaTyCode`) thread `rho.lift` / `sigma.forRaw.lift`
through the codomain raw at `scope + 1`; atom-shape codes use `rho`
/ `sigma.forRaw` at the outer scope.  Construction simply invokes the
constructor with the renamed/substituted raw step witnesses.

All zero-axiom under `#print axioms`.  Names exposed under
`LeanFX2.Step.par.<X>CodeCong.{rename,subst}_compatible` to satisfy
the reduction-compat coverage gate at `0`. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `arrowCodeCong` (binary, atom-shape). -/
namespace arrowCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget
     codomainCodeRawSource codomainCodeRawTarget : RawTerm sourceScope}
    (renamedDomainCodeStep :
      RawStep.par (domainCodeRawSource.rename rho)
                  (domainCodeRawTarget.rename rho))
    (renamedCodomainCodeStep :
      RawStep.par (codomainCodeRawSource.rename rho)
                  (codomainCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawSource codomainCodeRawSource))
      (Term.rename termRenaming
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawTarget codomainCodeRawTarget)) :=
  Step.par.arrowCodeCong outerLevel levelLe
    renamedDomainCodeStep renamedCodomainCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget
     codomainCodeRawSource codomainCodeRawTarget : RawTerm sourceScope}
    (substitutedDomainCodeStep :
      RawStep.par (domainCodeRawSource.subst sigma.forRaw)
                  (domainCodeRawTarget.subst sigma.forRaw))
    (substitutedCodomainCodeStep :
      RawStep.par (codomainCodeRawSource.subst sigma.forRaw)
                  (codomainCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawSource codomainCodeRawSource))
      (Term.subst termSubst
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawTarget codomainCodeRawTarget)) :=
  Step.par.arrowCodeCong outerLevel levelLe
    substitutedDomainCodeStep substitutedCodomainCodeStep

end arrowCodeCong

/-! ### `piTyCodeCong` (binary, codomain at scope+1). -/
namespace piTyCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget : RawTerm sourceScope}
    {codomainCodeRawSource codomainCodeRawTarget :
      RawTerm (sourceScope + 1)}
    (renamedDomainCodeStep :
      RawStep.par (domainCodeRawSource.rename rho)
                  (domainCodeRawTarget.rename rho))
    (renamedCodomainCodeStep :
      RawStep.par (codomainCodeRawSource.rename rho.lift)
                  (codomainCodeRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawSource codomainCodeRawSource))
      (Term.rename termRenaming
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawTarget codomainCodeRawTarget)) :=
  Step.par.piTyCodeCong outerLevel levelLe
    renamedDomainCodeStep renamedCodomainCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget : RawTerm sourceScope}
    {codomainCodeRawSource codomainCodeRawTarget :
      RawTerm (sourceScope + 1)}
    (substitutedDomainCodeStep :
      RawStep.par (domainCodeRawSource.subst sigma.forRaw)
                  (domainCodeRawTarget.subst sigma.forRaw))
    (substitutedCodomainCodeStep :
      RawStep.par (codomainCodeRawSource.subst sigma.forRaw.lift)
                  (codomainCodeRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawSource codomainCodeRawSource))
      (Term.subst termSubst
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRawTarget codomainCodeRawTarget)) :=
  Step.par.piTyCodeCong outerLevel levelLe
    substitutedDomainCodeStep substitutedCodomainCodeStep

end piTyCodeCong

/-! ### `sigmaTyCodeCong` (binary, second at scope+1). -/
namespace sigmaTyCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget : RawTerm sourceScope}
    {secondCodeRawSource secondCodeRawTarget : RawTerm (sourceScope + 1)}
    (renamedFirstCodeStep :
      RawStep.par (firstCodeRawSource.rename rho)
                  (firstCodeRawTarget.rename rho))
    (renamedSecondCodeStep :
      RawStep.par (secondCodeRawSource.rename rho.lift)
                  (secondCodeRawTarget.rename rho.lift)) :
    Step.par
      (Term.rename termRenaming
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawSource secondCodeRawSource))
      (Term.rename termRenaming
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawTarget secondCodeRawTarget)) :=
  Step.par.sigmaTyCodeCong outerLevel levelLe
    renamedFirstCodeStep renamedSecondCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget : RawTerm sourceScope}
    {secondCodeRawSource secondCodeRawTarget : RawTerm (sourceScope + 1)}
    (substitutedFirstCodeStep :
      RawStep.par (firstCodeRawSource.subst sigma.forRaw)
                  (firstCodeRawTarget.subst sigma.forRaw))
    (substitutedSecondCodeStep :
      RawStep.par (secondCodeRawSource.subst sigma.forRaw.lift)
                  (secondCodeRawTarget.subst sigma.forRaw.lift)) :
    Step.par
      (Term.subst termSubst
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawSource secondCodeRawSource))
      (Term.subst termSubst
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawTarget secondCodeRawTarget)) :=
  Step.par.sigmaTyCodeCong outerLevel levelLe
    substitutedFirstCodeStep substitutedSecondCodeStep

end sigmaTyCodeCong

/-! ### `productCodeCong` (binary, atom-shape). -/
namespace productCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget
     secondCodeRawSource secondCodeRawTarget : RawTerm sourceScope}
    (renamedFirstCodeStep :
      RawStep.par (firstCodeRawSource.rename rho)
                  (firstCodeRawTarget.rename rho))
    (renamedSecondCodeStep :
      RawStep.par (secondCodeRawSource.rename rho)
                  (secondCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawSource secondCodeRawSource))
      (Term.rename termRenaming
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawTarget secondCodeRawTarget)) :=
  Step.par.productCodeCong outerLevel levelLe
    renamedFirstCodeStep renamedSecondCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget
     secondCodeRawSource secondCodeRawTarget : RawTerm sourceScope}
    (substitutedFirstCodeStep :
      RawStep.par (firstCodeRawSource.subst sigma.forRaw)
                  (firstCodeRawTarget.subst sigma.forRaw))
    (substitutedSecondCodeStep :
      RawStep.par (secondCodeRawSource.subst sigma.forRaw)
                  (secondCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawSource secondCodeRawSource))
      (Term.subst termSubst
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRawTarget secondCodeRawTarget)) :=
  Step.par.productCodeCong outerLevel levelLe
    substitutedFirstCodeStep substitutedSecondCodeStep

end productCodeCong

/-! ### `sumCodeCong` (binary, atom-shape). -/
namespace sumCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (renamedLeftCodeStep :
      RawStep.par (leftCodeRawSource.rename rho)
                  (leftCodeRawTarget.rename rho))
    (renamedRightCodeStep :
      RawStep.par (rightCodeRawSource.rename rho)
                  (rightCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawSource rightCodeRawSource))
      (Term.rename termRenaming
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawTarget rightCodeRawTarget)) :=
  Step.par.sumCodeCong outerLevel levelLe
    renamedLeftCodeStep renamedRightCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (substitutedLeftCodeStep :
      RawStep.par (leftCodeRawSource.subst sigma.forRaw)
                  (leftCodeRawTarget.subst sigma.forRaw))
    (substitutedRightCodeStep :
      RawStep.par (rightCodeRawSource.subst sigma.forRaw)
                  (rightCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawSource rightCodeRawSource))
      (Term.subst termSubst
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawTarget rightCodeRawTarget)) :=
  Step.par.sumCodeCong outerLevel levelLe
    substitutedLeftCodeStep substitutedRightCodeStep

end sumCodeCong

/-! ### `listCodeCong` (unary, atom-shape). -/
namespace listCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (renamedElementCodeStep :
      RawStep.par (elementCodeRawSource.rename rho)
                  (elementCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawSource))
      (Term.rename termRenaming
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawTarget)) :=
  Step.par.listCodeCong outerLevel levelLe renamedElementCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (substitutedElementCodeStep :
      RawStep.par (elementCodeRawSource.subst sigma.forRaw)
                  (elementCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawSource))
      (Term.subst termSubst
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawTarget)) :=
  Step.par.listCodeCong outerLevel levelLe substitutedElementCodeStep

end listCodeCong

/-! ### `optionCodeCong` (unary, atom-shape). -/
namespace optionCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (renamedElementCodeStep :
      RawStep.par (elementCodeRawSource.rename rho)
                  (elementCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawSource))
      (Term.rename termRenaming
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawTarget)) :=
  Step.par.optionCodeCong outerLevel levelLe renamedElementCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (substitutedElementCodeStep :
      RawStep.par (elementCodeRawSource.subst sigma.forRaw)
                  (elementCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawSource))
      (Term.subst termSubst
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRawTarget)) :=
  Step.par.optionCodeCong outerLevel levelLe substitutedElementCodeStep

end optionCodeCong

/-! ### `eitherCodeCong` (binary, atom-shape). -/
namespace eitherCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (renamedLeftCodeStep :
      RawStep.par (leftCodeRawSource.rename rho)
                  (leftCodeRawTarget.rename rho))
    (renamedRightCodeStep :
      RawStep.par (rightCodeRawSource.rename rho)
                  (rightCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawSource rightCodeRawSource))
      (Term.rename termRenaming
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawTarget rightCodeRawTarget)) :=
  Step.par.eitherCodeCong outerLevel levelLe
    renamedLeftCodeStep renamedRightCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (substitutedLeftCodeStep :
      RawStep.par (leftCodeRawSource.subst sigma.forRaw)
                  (leftCodeRawTarget.subst sigma.forRaw))
    (substitutedRightCodeStep :
      RawStep.par (rightCodeRawSource.subst sigma.forRaw)
                  (rightCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawSource rightCodeRawSource))
      (Term.subst termSubst
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRawTarget rightCodeRawTarget)) :=
  Step.par.eitherCodeCong outerLevel levelLe
    substitutedLeftCodeStep substitutedRightCodeStep

end eitherCodeCong

/-! ### `idCodeCong` (ternary: typeCode + leftRaw + rightRaw). -/
namespace idCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRawSource typeCodeRawTarget
     leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm sourceScope}
    (renamedTypeCodeStep :
      RawStep.par (typeCodeRawSource.rename rho)
                  (typeCodeRawTarget.rename rho))
    (renamedLeftStep :
      RawStep.par (leftRawSource.rename rho)
                  (leftRawTarget.rename rho))
    (renamedRightStep :
      RawStep.par (rightRawSource.rename rho)
                  (rightRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRawSource leftRawSource rightRawSource))
      (Term.rename termRenaming
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRawTarget leftRawTarget rightRawTarget)) :=
  Step.par.idCodeCong outerLevel levelLe
    renamedTypeCodeStep renamedLeftStep renamedRightStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRawSource typeCodeRawTarget
     leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm sourceScope}
    (substitutedTypeCodeStep :
      RawStep.par (typeCodeRawSource.subst sigma.forRaw)
                  (typeCodeRawTarget.subst sigma.forRaw))
    (substitutedLeftStep :
      RawStep.par (leftRawSource.subst sigma.forRaw)
                  (leftRawTarget.subst sigma.forRaw))
    (substitutedRightStep :
      RawStep.par (rightRawSource.subst sigma.forRaw)
                  (rightRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRawSource leftRawSource rightRawSource))
      (Term.subst termSubst
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRawTarget leftRawTarget rightRawTarget)) :=
  Step.par.idCodeCong outerLevel levelLe
    substitutedTypeCodeStep substitutedLeftStep substitutedRightStep

end idCodeCong

/-! ### `equivCodeCong` (binary, atom-shape). -/
namespace equivCodeCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRawSource leftTypeCodeRawTarget
     rightTypeCodeRawSource rightTypeCodeRawTarget : RawTerm sourceScope}
    (renamedLeftTypeCodeStep :
      RawStep.par (leftTypeCodeRawSource.rename rho)
                  (leftTypeCodeRawTarget.rename rho))
    (renamedRightTypeCodeStep :
      RawStep.par (rightTypeCodeRawSource.rename rho)
                  (rightTypeCodeRawTarget.rename rho)) :
    Step.par
      (Term.rename termRenaming
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRawSource rightTypeCodeRawSource))
      (Term.rename termRenaming
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRawTarget rightTypeCodeRawTarget)) :=
  Step.par.equivCodeCong outerLevel levelLe
    renamedLeftTypeCodeStep renamedRightTypeCodeStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRawSource leftTypeCodeRawTarget
     rightTypeCodeRawSource rightTypeCodeRawTarget : RawTerm sourceScope}
    (substitutedLeftTypeCodeStep :
      RawStep.par (leftTypeCodeRawSource.subst sigma.forRaw)
                  (leftTypeCodeRawTarget.subst sigma.forRaw))
    (substitutedRightTypeCodeStep :
      RawStep.par (rightTypeCodeRawSource.subst sigma.forRaw)
                  (rightTypeCodeRawTarget.subst sigma.forRaw)) :
    Step.par
      (Term.subst termSubst
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRawSource rightTypeCodeRawSource))
      (Term.subst termSubst
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRawTarget rightTypeCodeRawTarget)) :=
  Step.par.equivCodeCong outerLevel levelLe
    substitutedLeftTypeCodeStep substitutedRightTypeCodeStep

end equivCodeCong

end par

end Step

end LeanFX2
