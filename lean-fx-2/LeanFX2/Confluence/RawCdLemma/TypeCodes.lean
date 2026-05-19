import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename.Main
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv

/-! # LeanFX2.Confluence.RawCdLemma.TypeCodes

Per-arm helpers for the CUMUL-2.1 per-shape type-code cong rules
inside `RawStep.par.cd_lemma`: `arrowCodeCong`, `piTyCodeCong`,
`sigmaTyCodeCong`, `productCodeCong`, `sumCodeCong`, `listCodeCong`,
`optionCodeCong`, `eitherCodeCong`, `idCodeCong`, `equivCodeCong`,
`cumulUpMarkerCong`.

Each arm `simp only [RawTerm.cd]` reduces `RawTerm.cd (XCode ...)`
to `XCode (cd ...)`, then applies the matching `*CodeCong` rule
with the inductive hypotheses.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCdLemma`
dispatcher. -/

namespace LeanFX2

/-- `arrowCodeCong` arm. -/
theorem RawStep.par.cd_lemma_arrowCodeCong {scope : Nat}
    {domainRawSource domainRawTarget
     codomainRawSource codomainRawTarget : RawTerm scope}
    (domainIH :
      RawStep.par domainRawTarget (RawTerm.cd domainRawSource))
    (codomainIH :
      RawStep.par codomainRawTarget (RawTerm.cd codomainRawSource)) :
    RawStep.par (RawTerm.arrowCode domainRawTarget codomainRawTarget)
      (RawTerm.cd (RawTerm.arrowCode domainRawSource
        codomainRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.arrowCodeCong domainIH codomainIH

/-- `piTyCodeCong` arm. -/
theorem RawStep.par.cd_lemma_piTyCodeCong {scope : Nat}
    {domainRawSource domainRawTarget : RawTerm scope}
    {codomainRawSource codomainRawTarget : RawTerm (scope + 1)}
    (domainIH :
      RawStep.par domainRawTarget (RawTerm.cd domainRawSource))
    (codomainIH :
      RawStep.par codomainRawTarget (RawTerm.cd codomainRawSource)) :
    RawStep.par (RawTerm.piTyCode domainRawTarget codomainRawTarget)
      (RawTerm.cd (RawTerm.piTyCode domainRawSource
        codomainRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.piTyCodeCong domainIH codomainIH

/-- `sigmaTyCodeCong` arm. -/
theorem RawStep.par.cd_lemma_sigmaTyCodeCong {scope : Nat}
    {domainRawSource domainRawTarget : RawTerm scope}
    {codomainRawSource codomainRawTarget : RawTerm (scope + 1)}
    (domainIH :
      RawStep.par domainRawTarget (RawTerm.cd domainRawSource))
    (codomainIH :
      RawStep.par codomainRawTarget (RawTerm.cd codomainRawSource)) :
    RawStep.par (RawTerm.sigmaTyCode domainRawTarget codomainRawTarget)
      (RawTerm.cd (RawTerm.sigmaTyCode domainRawSource
        codomainRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.sigmaTyCodeCong domainIH codomainIH

/-- `productCodeCong` arm. -/
theorem RawStep.par.cd_lemma_productCodeCong {scope : Nat}
    {firstRawSource firstRawTarget
     secondRawSource secondRawTarget : RawTerm scope}
    (firstIH : RawStep.par firstRawTarget (RawTerm.cd firstRawSource))
    (secondIH :
      RawStep.par secondRawTarget (RawTerm.cd secondRawSource)) :
    RawStep.par (RawTerm.productCode firstRawTarget secondRawTarget)
      (RawTerm.cd (RawTerm.productCode firstRawSource
        secondRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.productCodeCong firstIH secondIH

/-- `sumCodeCong` arm. -/
theorem RawStep.par.cd_lemma_sumCodeCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.sumCode leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.sumCode leftRawSource rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.sumCodeCong leftIH rightIH

/-- `listCodeCong` arm. -/
theorem RawStep.par.cd_lemma_listCodeCong {scope : Nat}
    {elementRawSource elementRawTarget : RawTerm scope}
    (elementIH :
      RawStep.par elementRawTarget (RawTerm.cd elementRawSource)) :
    RawStep.par (RawTerm.listCode elementRawTarget)
      (RawTerm.cd (RawTerm.listCode elementRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.listCodeCong elementIH

/-- `optionCodeCong` arm. -/
theorem RawStep.par.cd_lemma_optionCodeCong {scope : Nat}
    {elementRawSource elementRawTarget : RawTerm scope}
    (elementIH :
      RawStep.par elementRawTarget (RawTerm.cd elementRawSource)) :
    RawStep.par (RawTerm.optionCode elementRawTarget)
      (RawTerm.cd (RawTerm.optionCode elementRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.optionCodeCong elementIH

/-- `eitherCodeCong` arm. -/
theorem RawStep.par.cd_lemma_eitherCodeCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.eitherCode leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.eitherCode leftRawSource rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.eitherCodeCong leftIH rightIH

/-- `idCodeCong` arm. -/
theorem RawStep.par.cd_lemma_idCodeCong {scope : Nat}
    {typeRawSource typeRawTarget
     leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (typeIH : RawStep.par typeRawTarget (RawTerm.cd typeRawSource))
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.idCode typeRawTarget leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.idCode typeRawSource leftRawSource
        rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.idCodeCong typeIH leftIH rightIH

/-- `equivCodeCong` arm. -/
theorem RawStep.par.cd_lemma_equivCodeCong {scope : Nat}
    {leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm scope}
    (leftIH : RawStep.par leftRawTarget (RawTerm.cd leftRawSource))
    (rightIH : RawStep.par rightRawTarget (RawTerm.cd rightRawSource)) :
    RawStep.par (RawTerm.equivCode leftRawTarget rightRawTarget)
      (RawTerm.cd (RawTerm.equivCode leftRawSource rightRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.equivCodeCong leftIH rightIH

/-- `cumulUpMarkerCong` arm. -/
theorem RawStep.par.cd_lemma_cumulUpMarkerCong {scope : Nat}
    {innerRawSource innerRawTarget : RawTerm scope}
    (innerIH : RawStep.par innerRawTarget (RawTerm.cd innerRawSource)) :
    RawStep.par (RawTerm.cumulUpMarker innerRawTarget)
      (RawTerm.cd (RawTerm.cumulUpMarker innerRawSource)) := by
  simp only [RawTerm.cd]
  exact RawStep.par.cumulUpMarkerCong innerIH

end LeanFX2
