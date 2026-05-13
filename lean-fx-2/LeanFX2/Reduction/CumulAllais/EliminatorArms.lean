import LeanFX2.Reduction.CumulAllais.CumulPromotionArms

/-! # LeanFX2.Reduction.CumulAllais.EliminatorArms

Allais arms for the five eliminator constructors — kernel-gap closed:

* `natElim` (3-subterm: scrutinee, zero branch, succ branch)
* `natRec`  (3-subterm: same shape as natElim)
* `listElim` (3-subterm: scrutinee, nil branch, cons branch)
* `optionMatch` (3-subterm: scrutinee, none branch, some branch)
* `eitherMatch` (3-subterm: scrutinee, left branch, right branch)

These per-arm helpers mirror the cong rules at `Term.substHet`
level using the new eliminator cong rules now shipped in
`Reduction/Cumul.lean`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-! # Allais eliminator arms — kernel-gap closed

The 5 eliminator constructors (`natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`) now have `ConvCumul` cong rules in
the kernel (`Reduction/Cumul.lean`).  These per-arm helpers
mirror the cong rules at `Term.substHet` level. -/

/-- Allais arm for `natElim`: three-subterm cong via `natElimCong`. -/
theorem ConvCumul.subst_compatible_natElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (zeroCompat :
      ConvCumul (zeroBranch.substHet termSubstA) (zeroBranch.substHet termSubstB))
    (succCompat :
      ConvCumul (succBranch.substHet termSubstA) (succBranch.substHet termSubstB)) :
    ConvCumul ((Term.natElim scrutinee zeroBranch succBranch).substHet termSubstA)
              ((Term.natElim scrutinee zeroBranch succBranch).substHet termSubstB) :=
  ConvCumul.natElimCong scrutCompat zeroCompat succCompat

/-- Allais arm for `natRec`: three-subterm cong via `natRecCong`. -/
theorem ConvCumul.subst_compatible_natRec_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (zeroCompat :
      ConvCumul (zeroBranch.substHet termSubstA) (zeroBranch.substHet termSubstB))
    (succCompat :
      ConvCumul (succBranch.substHet termSubstA) (succBranch.substHet termSubstB)) :
    ConvCumul ((Term.natRec scrutinee zeroBranch succBranch).substHet termSubstA)
              ((Term.natRec scrutinee zeroBranch succBranch).substHet termSubstB) :=
  ConvCumul.natRecCong scrutCompat zeroCompat succCompat

/-- Allais arm for `listElim`: three-subterm cong via `listElimCong`. -/
theorem ConvCumul.subst_compatible_listElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch :
      Term sourceCtx (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (nilCompat :
      ConvCumul (nilBranch.substHet termSubstA) (nilBranch.substHet termSubstB))
    (consCompat :
      ConvCumul (consBranch.substHet termSubstA) (consBranch.substHet termSubstB)) :
    ConvCumul ((Term.listElim scrutinee nilBranch consBranch).substHet termSubstA)
              ((Term.listElim scrutinee nilBranch consBranch).substHet termSubstB) :=
  ConvCumul.listElimCong scrutCompat nilCompat consCompat

/-- Allais arm for `optionMatch`: three-subterm cong via `optionMatchCong`. -/
theorem ConvCumul.subst_compatible_optionMatch_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (noneCompat :
      ConvCumul (noneBranch.substHet termSubstA) (noneBranch.substHet termSubstB))
    (someCompat :
      ConvCumul (someBranch.substHet termSubstA) (someBranch.substHet termSubstB)) :
    ConvCumul
      ((Term.optionMatch scrutinee noneBranch someBranch).substHet termSubstA)
      ((Term.optionMatch scrutinee noneBranch someBranch).substHet termSubstB) :=
  ConvCumul.optionMatchCong scrutCompat noneCompat someCompat

/-- Allais arm for `eitherMatch`: three-subterm cong via `eitherMatchCong`. -/
theorem ConvCumul.subst_compatible_eitherMatch_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (leftCompat :
      ConvCumul (leftBranch.substHet termSubstA) (leftBranch.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightBranch.substHet termSubstA) (rightBranch.substHet termSubstB)) :
    ConvCumul
      ((Term.eitherMatch scrutinee leftBranch rightBranch).substHet termSubstA)
      ((Term.eitherMatch scrutinee leftBranch rightBranch).substHet termSubstB) :=
  ConvCumul.eitherMatchCong scrutCompat leftCompat rightCompat

end LeanFX2
