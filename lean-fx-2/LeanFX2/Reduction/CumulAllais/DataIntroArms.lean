import LeanFX2.Reduction.CumulAllais.TypeCodeArms

/-! # LeanFX2.Reduction.CumulAllais.DataIntroArms

Allais arms for the data-introduction Term ctors with subterm
recursion:

* Equiv / UA family: `equivIntroHet`, `equivApp`, `uaIntroHet`,
  `uaToEquiv`, `equivApply`.
* Single-subterm data ctors: `natSucc`, `optionSome`, `eitherInl`,
  `eitherInr`, `modIntro`, `modElim`, `subsume`.

Each arm recurses on its substituent ConvCumul subterms via the
structural `compat` IHs, then reassembles via the matching
ctor-level cong rule on `ConvCumul`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-- Allais arm for `equivIntroHet`: two-subterm cong via
`equivIntroHetCong`.  Mirrors the structure of
`subst_compatible_pair_allais` / `subst_compatible_listCons_allais`:
both subterms recurse via the `compat` IH, and the ctor-level cong
rule reassembles the pair. -/
theorem ConvCumul.subst_compatible_equivIntroHet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty sourceLevel sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    (forward : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardCompat :
      ConvCumul (forward.substHet termSubstA)
                (forward.substHet termSubstB))
    (backwardCompat :
      ConvCumul (backward.substHet termSubstA)
                (backward.substHet termSubstB)) :
    ConvCumul ((Term.equivIntroHet forward backward leftInv rightInv).substHet termSubstA)
              ((Term.equivIntroHet forward backward leftInv rightInv).substHet termSubstB) :=
  ConvCumul.equivIntroHetCong forwardCompat backwardCompat

/-- Allais arm for `equivApp`: two-subterm congruence over the packaged
equivalence and its argument. -/
theorem ConvCumul.subst_compatible_equivApp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty sourceLevel sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivCompat :
      ConvCumul (equivTerm.substHet termSubstA)
                (equivTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.equivApp equivTerm argumentTerm).substHet termSubstA)
              ((Term.equivApp equivTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.equivAppCong equivCompat argumentCompat

/-- Allais arm for `uaIntroHet`: single-subterm cong via
`uaIntroHetCong`.  Mirrors the structure of
`subst_compatible_optionSome_allais` / `subst_compatible_natSucc_allais`:
the equivWitness subterm recurses via the `compat` IH, and the
ctor-level cong rule reassembles.  The carrierARaw/carrierBRaw
substitute structurally via `sigma.forRaw` (identical on both A and B
sides since both share `sigma`); only the equivWitness differs.
Phase 12.A.B8.5b. -/
theorem ConvCumul.subst_compatible_uaIntroHet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ sourceLevel)
    {carrierA carrierB : Ty sourceLevel sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessCompat :
      ConvCumul (equivWitness.substHet termSubstA)
                (equivWitness.substHet termSubstB)) :
    ConvCumul ((Term.uaIntroHet (context := sourceCtx)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitness).substHet termSubstA)
              ((Term.uaIntroHet (context := sourceCtx)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitness).substHet termSubstB) :=
  ConvCumul.uaIntroHetCong (context := targetCtx) innerLevel
    (Nat.le_trans innerLevelLt sigma.cumulOk)
    (carrierARaw.subst sigma.forRaw) (carrierBRaw.subst sigma.forRaw)
    equivWitnessCompat

/-- Allais arm for `uaToEquiv` (Phase D3.6-P3): single-subterm cong via
`uaToEquivCong`.  Mirrors the structure of
`subst_compatible_uaIntroHet_allais` — the proof subterm recurses via
the `compat` IH, and the ctor-level cong rule reassembles.  The
leftTyRaw/rightTyRaw substitute structurally via `sigma.forRaw`
(identical on both A and B sides since both share `sigma`); only the
proof differs. -/
theorem ConvCumul.subst_compatible_uaToEquiv_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ sourceLevel)
    (leftTy rightTy : Ty sourceLevel sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
               (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
               proofRaw)
    (proofCompat :
      ConvCumul (proof.substHet termSubstA)
                (proof.substHet termSubstB)) :
    ConvCumul ((Term.uaToEquiv (context := sourceCtx)
                               innerLevel innerLevelLt
                               leftTy rightTy
                               leftTyRaw rightTyRaw
                               proof).substHet termSubstA)
              ((Term.uaToEquiv (context := sourceCtx)
                               innerLevel innerLevelLt
                               leftTy rightTy
                               leftTyRaw rightTyRaw
                               proof).substHet termSubstB) :=
  ConvCumul.uaToEquivCong (context := targetCtx) innerLevel
    (Nat.le_trans innerLevelLt sigma.cumulOk)
    (leftTy.substHet sigma) (rightTy.substHet sigma)
    (leftTyRaw.subst sigma.forRaw) (rightTyRaw.subst sigma.forRaw)
    proofCompat

/-- Allais arm for `equivApply` (Phase D3.6-P4): binary-subterm cong
via `equivApplyCong`.  Mirrors the structure of
`subst_compatible_equivApp_allais` — both equivTerm and argumentTerm
recurse via the structural `compat` IHs, and the ctor-level cong
rule reassembles. -/
theorem ConvCumul.subst_compatible_equivApply_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty sourceLevel sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivCompat :
      ConvCumul (equivTerm.substHet termSubstA)
                (equivTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.equivApply equivTerm argumentTerm).substHet termSubstA)
              ((Term.equivApply equivTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.equivApplyCong equivCompat argumentCompat

/-- Allais arm for `natSucc`: single-subterm cong via `natSuccCong`. -/
theorem ConvCumul.subst_compatible_natSucc_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorCompat :
      ConvCumul (predecessor.substHet termSubstA)
                (predecessor.substHet termSubstB)) :
    ConvCumul ((Term.natSucc predecessor).substHet termSubstA)
              ((Term.natSucc predecessor).substHet termSubstB) :=
  ConvCumul.natSuccCong predecessorCompat

/-- Allais arm for `optionSome`: single-subterm cong via `optionSomeCong`. -/
theorem ConvCumul.subst_compatible_optionSome_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.optionSome valueTerm).substHet termSubstA)
              ((Term.optionSome valueTerm).substHet termSubstB) :=
  ConvCumul.optionSomeCong valueCompat

/-- Allais arm for `eitherInl`: single-subterm cong via `eitherInlCong`. -/
theorem ConvCumul.subst_compatible_eitherInl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.eitherInl (rightType := rightType) valueTerm).substHet termSubstA)
              ((Term.eitherInl (rightType := rightType) valueTerm).substHet termSubstB) :=
  ConvCumul.eitherInlCong valueCompat

/-- Allais arm for `eitherInr`: single-subterm cong via `eitherInrCong`. -/
theorem ConvCumul.subst_compatible_eitherInr_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.eitherInr (leftType := leftType) valueTerm).substHet termSubstA)
              ((Term.eitherInr (leftType := leftType) valueTerm).substHet termSubstB) :=
  ConvCumul.eitherInrCong valueCompat

/-- Allais arm for `modIntro`: single-subterm cong via `modIntroCong`. -/
theorem ConvCumul.subst_compatible_modIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.modIntro innerTerm).substHet termSubstA)
              ((Term.modIntro innerTerm).substHet termSubstB) :=
  ConvCumul.modIntroCong innerCompat

/-- Allais arm for `modElim`: single-subterm cong via `modElimCong`. -/
theorem ConvCumul.subst_compatible_modElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.modElim innerTerm).substHet termSubstA)
              ((Term.modElim innerTerm).substHet termSubstB) :=
  ConvCumul.modElimCong innerCompat

/-- Allais arm for `subsume`: single-subterm cong via `subsumeCong`. -/
theorem ConvCumul.subst_compatible_subsume_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.subsume innerTerm).substHet termSubstA)
              ((Term.subsume innerTerm).substHet termSubstB) :=
  ConvCumul.subsumeCong innerCompat

end LeanFX2
