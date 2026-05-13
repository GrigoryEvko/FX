import LeanFX2.Reducibility.FundamentalAliases
import LeanFX2.Reducibility.FundamentalCubical.CubicalGlueEliminators
import LeanFX2.Reducibility.FundamentalCubical.RecordRefineCodataEndpoints

/-! # LeanFX2.Reducibility.FundamentalCubical.IdentitySubstIntroForms

Identity-substitution SN endpoints for introduction / projection
forms: `equivApp`, `pathApp`, `codataDest`, `equivApply`,
`equivIntroHet`, `codataUnfold`, `glueIntro`, `recordIntro`,
`refineIntro`.  These ship the M04-facing closure under the
identity substitution, used to project SN of a reducible witness
through identity substitution.

## Root status

Layer 3 metatheory leaf.  Third slice of `FundamentalCubical`. -/

namespace LeanFX2


/-- **K12.27 identity-substitution equivalence application SN endpoint**.

The identity-only M04 route gets the internal equivalence application
case by projecting the existing `Ty.equiv` closure at identity and then
erasing identity substitution from the raw index. -/
theorem Reducible.fundamental_identity_equivApp_at_equiv_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIdentityReducible :
        Reducible ((Ty.equiv carrierA carrierB).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) equivTerm))
    (argumentIdentityReducible :
        Reducible (carrierA.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) argumentTerm)) :
    Term.isStronglyNormalizing (Term.equivApp equivTerm argumentTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.equivApp equivTerm argumentTerm)
    (Reducible.isStronglyNormalizing
      (Reducible.fundamental_equivApp_at_equiv
        (termSubst := TermSubst.identity sourceCtx)
        equivIdentityReducible argumentIdentityReducible))

/-- **K12.27 identity-substitution path application SN endpoint**.

This is the cubical eliminator sibling of the identity application
bridge: the existing `Ty.path` fundamental endpoint supplies reducibility
of the identity-substituted path application, and the raw-index identity
lemma transports that result back to the original `Term.pathApp`. -/
theorem Reducible.fundamental_identity_pathApp_at_path_sn
    {level scope : Nat}
    {sourceCtx : Ctx Mode.univalent level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
        Term sourceCtx
          (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathIdentityReducible :
        Reducible
          ((Ty.path carrierType leftEndpoint rightEndpoint).subst
            Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) pathTerm))
    (intervalIdentityReducible :
        Reducible (Ty.interval.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) intervalTerm)) :
    Term.isStronglyNormalizing
      (Term.pathApp rfl pathTerm intervalTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.pathApp rfl pathTerm intervalTerm)
    (Reducible.isStronglyNormalizing
      (Reducible.fundamental_pathApp_at_path
        (termSubst := TermSubst.identity sourceCtx)
        rfl pathIdentityReducible intervalIdentityReducible))

/-- **K12.27 identity-substitution codata observation SN endpoint**.

The codata candidate stores a reducible observation closure.  This
identity-only wrapper exposes the corresponding original-term SN fact
for the M04 induction without introducing any generic weakening theorem. -/
theorem Reducible.fundamental_identity_codataDest_at_codata_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
        Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataIdentityReducible :
        Reducible ((Ty.codata stateType outputType).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) codataValue)) :
    Term.isStronglyNormalizing (Term.codataDest codataValue) :=
  Term.strong_normalization_of_identity_subst
    (Term.codataDest codataValue)
    (Reducible.isStronglyNormalizing
      (Reducible.fundamental_codataDest_at_codata
        (termSubst := TermSubst.identity sourceCtx)
        codataIdentityReducible))

/-- **K12.27 identity-substitution equivalence apply SN endpoint**.

`equivApply` has only an M04-facing SN fundamental endpoint in the
current univalence-target raw fragment.  This identity bridge applies
that endpoint at identity substitution and erases the identity raw
index back to the original typed constructor. -/
theorem Reducible.fundamental_identity_equivApply_at_equiv_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIdentityReducible :
        Reducible ((Ty.equiv carrierA carrierB).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) equivTerm))
    (argumentIdentityReducible :
        Reducible (carrierA.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.equivApply equivTerm argumentTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.equivApply equivTerm argumentTerm)
    (Reducible.fundamental_equivApply_at_equiv
      (termSubst := TermSubst.identity sourceCtx)
      equivIdentityReducible argumentIdentityReducible)

/-- **K12.27 identity-substitution equivalence-intro SN endpoint**.

This exposes the equivalence-introduction SN fundamental at the
identity route.  The current SN endpoint depends on reducibility of the
forward and backward functions; inverse-proof payloads remain typed
children of the constructor but are erased from the raw SN obligation. -/
theorem Reducible.fundamental_identity_equivIntroHet_at_equiv_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIdentityReducible :
      Reducible ((Ty.arrow carrierA carrierB).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) forward))
    (backwardIdentityReducible :
      Reducible ((Ty.arrow carrierB carrierA).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) backward)) :
    Term.isStronglyNormalizing
      (Term.equivIntroHet forward backward leftInv rightInv) :=
  Term.strong_normalization_of_identity_subst
    (Term.equivIntroHet forward backward leftInv rightInv)
    (Reducible.fundamental_equivIntroHet_at_equiv
      (termSubst := TermSubst.identity sourceCtx)
      forwardIdentityReducible backwardIdentityReducible)

/-- **K12.27 identity-substitution codata unfold SN endpoint**.

The codata-introduction fundamental remains SN-output: the full
observation closure is supplied by `codataDest`.  This bridge makes the
identity induction case consume state and transition reducibility
witnesses directly, without claiming full codata-introduction
reducibility. -/
theorem Reducible.fundamental_identity_codataUnfold_at_codata_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
        Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateIdentityReducible :
        Reducible (stateType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) initialState))
    (transitionIdentityReducible :
        Reducible ((Ty.arrow stateType outputType).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) transition)) :
    Term.isStronglyNormalizing
      (Term.codataUnfold initialState transition) :=
  Term.strong_normalization_of_identity_subst
    (Term.codataUnfold initialState transition)
    (Reducible.fundamental_codataUnfold_at_codata
      (termSubst := TermSubst.identity sourceCtx)
      stateIdentityReducible transitionIdentityReducible)

/-- **K12.27 identity-substitution Glue introduction SN endpoint**.

Glue introduction is still an SN-output fundamental case: building full
`Ty.glue` reducibility for introductions would require the eliminator
backward bridge.  The identity route only needs the honest SN
consequence, obtained from reducibility of the base and partial
payloads. -/
theorem Reducible.fundamental_identity_glueIntro_at_glue_sn
    {level scope : Nat}
    {sourceCtx : Ctx Mode.univalent level scope}
    {baseType : Ty level scope}
    {boundaryWitness baseRaw partialRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseIdentityReducible :
        Reducible (baseType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseValue))
    (partialIdentityReducible :
        Reducible (baseType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) partialValue)) :
    Term.isStronglyNormalizing
      (Term.glueIntro rfl baseType boundaryWitness
        baseValue partialValue) :=
  Term.strong_normalization_of_identity_subst
    (Term.glueIntro rfl baseType boundaryWitness baseValue partialValue)
    (Reducible.fundamental_glueIntro_at_glue
      (termSubst := TermSubst.identity sourceCtx)
      rfl baseIdentityReducible partialIdentityReducible)

/-- **K12.27 identity-substitution record introduction SN endpoint**.

The one-field record introduction fundamental is SN-output in the
current kernel.  This wrapper lets the identity induction consume the
field's reducibility witness directly. -/
theorem Reducible.fundamental_identity_recordIntro_at_record_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (fieldIdentityReducible :
        Reducible (singleFieldType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) firstField)) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  Term.strong_normalization_of_identity_subst
    (Term.recordIntro firstField)
    (Reducible.fundamental_recordIntro_at_record
      (termSubst := TermSubst.identity sourceCtx)
      fieldIdentityReducible)

/-- **K12.27 identity-substitution refinement introduction SN endpoint**.

Refinement introduction carries both the runtime value and erased proof
payload through the raw SN relation.  This bridge exposes the exact
identity-route SN consequence from their reducibility witnesses without
asserting a full refinement-introduction candidate. -/
theorem Reducible.fundamental_identity_refineIntro_at_refine_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (valueIdentityReducible :
        Reducible (baseType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseValue))
    (proofIdentityReducible :
        Reducible (Ty.unit.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) predicateProof)) :
    Term.isStronglyNormalizing
      (Term.refineIntro predicate baseValue predicateProof) :=
  Term.strong_normalization_of_identity_subst
    (Term.refineIntro predicate baseValue predicateProof)
    (Reducible.fundamental_refineIntro_at_refine
      (termSubst := TermSubst.identity sourceCtx)
      valueIdentityReducible proofIdentityReducible)

end LeanFX2
