import LeanFX2.Reducibility.FundamentalAliases

/-! # LeanFX2.Reducibility.FundamentalCubical.RecordRefineCodataEndpoints

Fundamental SN endpoints for the record / refine / codata family:
`Term.recordIntro` at `Ty.record`, `Term.refineIntro` at
`Ty.refine`, `Term.codataUnfold` at `Ty.codata`, `Term.codataDest`
at `Ty.codata`.

## Root status

Layer 3 metatheory leaf.  Second slice of `FundamentalCubical`. -/

namespace LeanFX2


/-- Fundamental SN endpoint: `Term.recordIntro` at `Ty.record` (K12.26).

Single-field record introduction is strongly normalizing whenever its
field is reducible at the substituted field type.  Multi-field records
are represented by the schema layer as nested single-field records, so
this is the M04-facing introduction endpoint for the current raw kernel
constructor. -/
theorem Reducible.fundamental_recordIntro_at_record
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (firstIH :
        Reducible (singleFieldType.subst sigma)
          (Term.subst termSubst firstField)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.recordIntro firstField)) :=
  Term.recordIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstIH)

/-- Fundamental SN endpoint: `Term.refineIntro` at `Ty.refine` (K12.26).

Refinement introduction is strongly normalizing when both the base value
and erased proof payload are reducible after substitution.  This endpoint
supports M04 strong normalization; it does not assert the full refinement
Reducible introduction closure. -/
theorem Reducible.fundamental_refineIntro_at_refine
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (valueIH :
        Reducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (proofIH :
        Reducible (Ty.unit.subst sigma)
          (Term.subst termSubst predicateProof)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.refineIntro predicate baseValue predicateProof)) :=
  Term.refineIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing valueIH)
    (Reducible.isStronglyNormalizing proofIH)

/-- Fundamental SN endpoint: `Term.codataUnfold` at `Ty.codata` (K12.26).

Codata unfold is strongly normalizing whenever the initial state and
state-to-output transition are reducible after substitution.  The full
codata Reducible observation closure is supplied separately by the
destructor endpoint. -/
theorem Reducible.fundamental_codataUnfold_at_codata
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
        Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateIH :
        Reducible (stateType.subst sigma)
          (Term.subst termSubst initialState))
    (transitionIH :
        Reducible ((Ty.arrow stateType outputType).subst sigma)
          (Term.subst termSubst transition)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.codataUnfold initialState transition)) :=
  Term.codataUnfold_isStronglyNormalizing
    (Reducible.isStronglyNormalizing stateIH)
    (Reducible.isStronglyNormalizing transitionIH)

/-- Fundamental case: `Term.codataDest` at `Ty.codata` (K12.26.A).

The codata reducibility arm stores the full observation closure at
the strict sub-type `outputType`; `stateType` is carried by the
codata value but is not exposed by the current one-observation
destructor.  This fundamental case is the direct projection of that
closure after `Term.subst` distributes over `codataDest`. -/
theorem Reducible.fundamental_codataDest_at_codata
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
        Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataIH :
        Reducible ((Ty.codata stateType outputType).subst sigma)
                  (Term.subst termSubst codataValue)) :
    Reducible (outputType.subst sigma)
              (Term.subst termSubst (Term.codataDest codataValue)) :=
  codataIH.2

/-- Codata observation preserves fundamental stability. -/
theorem Reducible.fundamental_codataDest_at_codata_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
        Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataIsStable :
      IsRenamingStableReducible
        ((Ty.codata stateType outputType).subst sigma)
        (Term.subst termSubst codataValue)) :
    IsRenamingStableReducible (outputType.subst sigma)
      (Term.subst termSubst (Term.codataDest codataValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (codataIsStable rhoIsInjective termRenaming).2

/-- Direct M04 SN endpoint for codata observation.

The codata candidate already stores the observation closure at the
output type.  This bridge exposes the exact M04 consequence at the
typed `Term.codataDest` surface. -/
theorem Term.codataDest_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
        Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataReducible :
        Reducible (Ty.codata stateType outputType) codataValue) :
    Term.isStronglyNormalizing (Term.codataDest codataValue) :=
  Reducible.isStronglyNormalizing codataReducible.2


/-! ## Renaming-stable mirrors of the record / refine / codata intros

Three SN-output `_stable` companions of the SN endpoints above.  Each
rebuilds SN at every injective-renamed future world by projecting SN
from `IsRenamingStableReducible` premises at the renamed world and
feeding the renamed-world raw SN witnesses to the corresponding raw
helper.  The renamed-world raw helper application matches the goal
because `Term.subst` distributes definitionally over each constructor's
intro form. -/

/-- Renaming-stable SN of `Term.recordIntro` at `Ty.record` —
`IsRenamingStableIsSN` mirror of `fundamental_recordIntro_at_record`. -/
theorem Reducible.fundamental_recordIntro_at_record_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (firstIsStable :
        IsRenamingStableReducible (singleFieldType.subst sigma)
          (Term.subst termSubst firstField)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.recordIntro firstField)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have firstReducibleAtRho :=
    firstIsStable rhoIsInjective termRenaming
  exact Term.recordIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing firstReducibleAtRho)

/-- Renaming-stable SN of `Term.refineIntro` at `Ty.refine` —
`IsRenamingStableIsSN` mirror of `fundamental_refineIntro_at_refine`. -/
theorem Reducible.fundamental_refineIntro_at_refine_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (valueIsStable :
        IsRenamingStableReducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (proofIsStable :
        IsRenamingStableReducible (Ty.unit.subst sigma)
          (Term.subst termSubst predicateProof)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.refineIntro predicate baseValue predicateProof)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have valueReducibleAtRho :=
    valueIsStable rhoIsInjective termRenaming
  have proofReducibleAtRho :=
    proofIsStable rhoIsInjective termRenaming
  exact Term.refineIntro_isStronglyNormalizing
    (Reducible.isStronglyNormalizing valueReducibleAtRho)
    (Reducible.isStronglyNormalizing proofReducibleAtRho)

/-- Renaming-stable SN of `Term.codataUnfold` at `Ty.codata` —
`IsRenamingStableIsSN` mirror of `fundamental_codataUnfold_at_codata`. -/
theorem Reducible.fundamental_codataUnfold_at_codata_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
        Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateIsStable :
        IsRenamingStableReducible (stateType.subst sigma)
          (Term.subst termSubst initialState))
    (transitionIsStable :
        IsRenamingStableReducible
          ((Ty.arrow stateType outputType).subst sigma)
          (Term.subst termSubst transition)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.codataUnfold initialState transition)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have stateReducibleAtRho :=
    stateIsStable rhoIsInjective termRenaming
  have transitionReducibleAtRho :=
    transitionIsStable rhoIsInjective termRenaming
  exact Term.codataUnfold_isStronglyNormalizing
    (Reducible.isStronglyNormalizing stateReducibleAtRho)
    (Reducible.isStronglyNormalizing transitionReducibleAtRho)

end LeanFX2
