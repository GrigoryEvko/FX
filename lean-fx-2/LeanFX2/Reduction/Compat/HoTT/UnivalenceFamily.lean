import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Term.Subst

/-! # LeanFX2.Reduction.Compat.HoTT.UnivalenceFamily

Typed compositional `rename`/`subst` compat lemmas for the
univalence family of HoTT cong constructors:

* `uaIntroHetCong` — heterogeneous univalence introduction (unary)
* `uaToEquivCong` — D3.6-P5 typed univalence-β extractor (unary)
* `equivApplyCong` — D3.6-P5 typed univalence-β application (binary)

Split from `LeanFX2/Reduction/Compat/HoTT.lean` (REFACTOR-COMPAT
#1556) — keeps the parent module under the 1000-line ceiling.

## Root status

Layer 2 reduction-compat HoTT helper.  All declarations remain
zero-axiom under `#print axioms` and preserve their original
fully-qualified namespace `LeanFX2.Step.par.XCong.{rename,subst}_compatible`. -/

namespace LeanFX2

namespace Step

namespace par

/-! ### `uaIntroHetCong` (unary, heterogeneous univalence intro).

Unary exemplar with one inner Step.par premise on the
equivalence-witness term.  The witness's raw index is the
structured form `RawTerm.equivIntro forwardRaw backwardRaw`,
which renames/substitutes structurally via the corresponding
RawSubst equations, so the typed-Term step composes directly
through `Step.par.uaIntroHetCong`. -/
namespace uaIntroHetCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {equivWitnessSource :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawSource backwardRawSource)}
    {equivWitnessTarget :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawTarget backwardRawTarget)}
    (renamedEquivWitnessStep :
      Step.par (Term.rename termRenaming equivWitnessSource)
               (Term.rename termRenaming equivWitnessTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessSource))
      (Term.rename termRenaming
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessTarget)) :=
  Step.par.uaIntroHetCong (context := targetCtx)
    innerLevel innerLevelLt
    (carrierARaw.rename rho) (carrierBRaw.rename rho)
    renamedEquivWitnessStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {equivWitnessSource :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawSource backwardRawSource)}
    {equivWitnessTarget :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawTarget backwardRawTarget)}
    (substitutedEquivWitnessStep :
      Step.par (Term.subst termSubst equivWitnessSource)
               (Term.subst termSubst equivWitnessTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessSource))
      (Term.subst termSubst
        (Term.uaIntroHet (context := sourceCtx)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw
                         equivWitnessTarget)) :=
  Step.par.uaIntroHetCong (context := targetCtx)
    innerLevel innerLevelLt
    (carrierARaw.subst sigma.forRaw) (carrierBRaw.subst sigma.forRaw)
    substitutedEquivWitnessStep

end uaIntroHetCong

/-! ### `uaToEquivCong` (D3.6-P5, unary, single typed subterm).

Phase D3.6-P5 ships the typed-compat mirror of D3.6-P3's
`Step.par.uaToEquivCong` (single-subterm cong rule for the typed
univalence-β extractor `Term.uaToEquiv`).  The cong rule's premise
is one inner `Step.par` on the typed `proof : Term context (Ty.id
(Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
proofRaw` subterm; the universe level + cumul witness, the leftTy/
rightTy carriers, and the schematic `leftTyRaw/rightTyRaw` payloads
are fixed.

`Term.uaToEquiv` lives at result type `Ty.equiv leftTy rightTy`,
which is non-binder.  No `Ty.weaken_*_commute` cast is needed —
same precedent as `equivIntroHetCong` / `uaIntroHetCong`'s
non-binder cascade arms.  The proof is a one-line application of
the constructor with the renamed/substituted carriers + raw
payloads + the witnessed inner step. -/
namespace uaToEquivCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRawSource proofRawTarget : RawTerm sourceScope}
    {proofSource :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawSource}
    {proofTarget :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawTarget}
    (renamedProofStep :
      Step.par (Term.rename termRenaming proofSource)
               (Term.rename termRenaming proofTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaToEquiv (context := sourceCtx)
                        innerLevel innerLevelLt
                        leftTy rightTy
                        leftTyRaw rightTyRaw
                        proofSource))
      (Term.rename termRenaming
        (Term.uaToEquiv (context := sourceCtx)
                        innerLevel innerLevelLt
                        leftTy rightTy
                        leftTyRaw rightTyRaw
                        proofTarget)) :=
  Step.par.uaToEquivCong (context := targetCtx)
    innerLevel innerLevelLt
    (leftTy.rename rho) (rightTy.rename rho)
    (leftTyRaw.rename rho) (rightTyRaw.rename rho)
    renamedProofStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRawSource proofRawTarget : RawTerm sourceScope}
    {proofSource :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawSource}
    {proofTarget :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawTarget}
    (substitutedProofStep :
      Step.par (Term.subst termSubst proofSource)
               (Term.subst termSubst proofTarget)) :
    Step.par
      (Term.subst termSubst
        (Term.uaToEquiv (context := sourceCtx)
                        innerLevel innerLevelLt
                        leftTy rightTy
                        leftTyRaw rightTyRaw
                        proofSource))
      (Term.subst termSubst
        (Term.uaToEquiv (context := sourceCtx)
                        innerLevel innerLevelLt
                        leftTy rightTy
                        leftTyRaw rightTyRaw
                        proofTarget)) :=
  Step.par.uaToEquivCong (context := targetCtx)
    innerLevel innerLevelLt
    (leftTy.subst sigma) (rightTy.subst sigma)
    (leftTyRaw.subst sigma.forRaw) (rightTyRaw.subst sigma.forRaw)
    substitutedProofStep

end uaToEquivCong

/-! ### `equivApplyCong` (D3.6-P5, binary, two typed subterms).

Phase D3.6-P5 ships the typed-compat mirror of D3.6-P4's
`Step.par.equivApplyCong` (binary-subterm cong rule for the typed
univalence-β application `Term.equivApply`).  The cong rule's
premises are two inner `Step.par`s: one on the packaged equivalence
`equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw`,
one on the source-side argument `argumentTerm : Term context
carrierA argumentRaw`.

Architectural twin of `equivAppCong.{rename,subst}_compatible`:
both `Term.equivApp` and `Term.equivApply` are binary cong rules
at non-binder result types (`carrierB` for both), so the rename/
subst arms recurse structurally without `Ty.weaken_*_commute`
casts.  The proof is a one-line application of the constructor
with the renamed/substituted inner steps. -/
namespace equivApplyCong

theorem rename_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget argumentRawSource argumentRawTarget :
      RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (renamedEquivStep :
      Step.par (Term.rename termRenaming equivSource)
               (Term.rename termRenaming equivTarget))
    (renamedArgumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.equivApply equivSource argumentSource))
      (Term.rename termRenaming (Term.equivApply equivTarget argumentTarget)) :=
  Step.par.equivApplyCong renamedEquivStep renamedArgumentStep

theorem subst_compatible
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget argumentRawSource argumentRawTarget :
      RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (substitutedEquivStep :
      Step.par (Term.subst termSubst equivSource)
               (Term.subst termSubst equivTarget))
    (substitutedArgumentStep :
      Step.par (Term.subst termSubst argumentSource)
               (Term.subst termSubst argumentTarget)) :
    Step.par
      (Term.subst termSubst (Term.equivApply equivSource argumentSource))
      (Term.subst termSubst (Term.equivApply equivTarget argumentTarget)) :=
  Step.par.equivApplyCong substitutedEquivStep substitutedArgumentStep

end equivApplyCong

end par

end Step

end LeanFX2
