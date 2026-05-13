import LeanFX2.Reducibility.FundamentalAliases

/-! # LeanFX2.Reducibility.FundamentalCubical — K12.24 cubical cases

The fundamental-theorem cases for cubical type-theory
eliminators (the K12.24 cascade).

## What ships

* K12.24 fundamental cubical-eliminator cases — `Term.pathLam`,
  `Term.pathApp`, `Term.transp`, `Term.hcomp`,
  `Term.glueIntro`, `Term.glueElim`, plus their associated
  SN-output endpoint aliases.

This is the final piece of the fundamental theorem alongside the
K12.25 modal cases (in `FundamentalWrappers`).  The K12.26 (cumul,
refine, type-code, session, effect cases) are split across
`FundamentalAliases` and other modules — full M04 close-out lands
in `K12.27` ticket #1784.

## Root status

Layer 3 metatheory leaf.  Final cubical chapter of the K12.20–K12.27
fundamental-theorem cascade. -/

namespace LeanFX2


/-! ## K12.24 fundamental cubical-eliminator cases -/

/-- Fundamental case: `Term.pathApp` at `Ty.path` (K12.24.A).

Cubical path application — `Term.pathApp` consumes a path
witness at `Ty.path carrierType leftEndpoint rightEndpoint` plus
an interval point and produces a value at carrierType.  The
`modeIsUnivalent : mode = Mode.univalent` data parameter on the
ctor (`Term.lean:348`) is the univalent-mode gate that protects
the cubical β rule from firing in non-univalent modes.

K12.12's path closure (`Reducibility.lean:476-483`) carries a
quantified eliminator-output Reducible witness, threading the
SAME mode gate plus an interval-SN argument hypothesis:

    Reducible (Ty.path carrier _ _) pathTerm =
      SN(pathTerm) ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent) intervalTerm,
        SN(intervalTerm) →
        Reducible carrier (Term.pathApp modeIsUnivalent pathTerm intervalTerm)

The fundamental atomic projects the second conjunct and supplies
all three pieces from the IHs:

* `modeIsUnivalent` comes directly from the ctor parameter
  (threaded as `modeIsUnivalent` here).
* `Term.subst termSubst intervalTerm` is the post-substitution
  interval point.
* `intervalIH` is `Reducible (Ty.interval.subst sigma)
  (subst intervalTerm)`; Ty.interval is a closed type so
  `Ty.interval.subst sigma = Ty.interval` definitionally
  (`Foundation/Subst.lean:127`), and K12.4's interval closure
  (`Reducibility.lean:329`) is literally `SN(...)`, so intervalIH
  IS the SN witness K12.12 demands.

Term.subst commutes definitionally over `.pathApp`
(`Term/Subst.lean:322` — no cast); Ty.path.subst is also
definitional (`Foundation/Subst.lean:128-131`), so the substituted
goal `(Ty.path c l r).subst sigma` unifies with the closure's
LHS without rewriting.

Same projection pattern as K12.23.A equivApp.  The interval-SN
demand sets this atomic apart from K12.23.A's Reducible-argument
demand — path's argument lives at the closed type Ty.interval
where Reducible degenerates to SN. -/
theorem Reducible.fundamental_pathApp_at_path
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
        Term sourceCtx
             (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathIH :
        Reducible
          ((Ty.path carrierType leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst pathTerm))
    (intervalIH :
        Reducible (Ty.interval.subst sigma)
                  (Term.subst termSubst intervalTerm)) :
    Reducible (carrierType.subst sigma)
              (Term.subst termSubst
                 (Term.pathApp modeIsUnivalent pathTerm intervalTerm)) :=
  pathIH.2 modeIsUnivalent (Term.subst termSubst intervalTerm) intervalIH

/-- Cubical path application preserves fundamental stability. -/
theorem Reducible.fundamental_pathApp_at_path_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
        Term sourceCtx
             (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathIsStable :
      IsRenamingStableReducible
        ((Ty.path carrierType leftEndpoint rightEndpoint).subst sigma)
        (Term.subst termSubst pathTerm))
    (intervalIsStable :
      IsRenamingStableReducible (Ty.interval.subst sigma)
        (Term.subst termSubst intervalTerm)) :
    IsRenamingStableReducible (carrierType.subst sigma)
      (Term.subst termSubst
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (pathIsStable rhoIsInjective termRenaming).2 modeIsUnivalent
    (Term.rename termRenaming (Term.subst termSubst intervalTerm))
    (Reducible.isStronglyNormalizing
      (intervalIsStable rhoIsInjective termRenaming))

/-- Direct M04 SN endpoint for cubical path application.

Path application exposes the path body's endpoint when the path is a
canonical path lambda, so the M04-facing premise is the path
reducibility closure plus SN of the interval argument. -/
theorem Term.pathApp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
        Term sourceCtx
          (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathReducible :
        Reducible
          (Ty.path carrierType leftEndpoint rightEndpoint) pathTerm)
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) :=
  Reducible.isStronglyNormalizing
    (pathReducible.2 modeIsUnivalent intervalTerm intervalIsSN)

/-- Fundamental case: `Term.glueElim` at `Ty.glue` (K12.24.B).

`Ty.glue` carries a full eliminator-output closure in K12.12:
reducibility of a glued value includes reducibility of
`Term.glueElim` at the strict sub-type `baseType`, gated by the
same univalent-mode witness.  The fundamental case is therefore a
direct projection of that closure after substitution. -/
theorem Reducible.fundamental_glueElim_at_glue
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (glueIH :
        Reducible ((Ty.glue baseType boundaryWitness).subst sigma)
                  (Term.subst termSubst gluedValue)) :
    Reducible (baseType.subst sigma)
              (Term.subst termSubst
                (Term.glueElim modeIsUnivalent gluedValue)) :=
  glueIH.2 modeIsUnivalent

/-- Glue elimination preserves fundamental stability. -/
theorem Reducible.fundamental_glueElim_at_glue_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (glueIsStable :
      IsRenamingStableReducible
        ((Ty.glue baseType boundaryWitness).subst sigma)
        (Term.subst termSubst gluedValue)) :
    IsRenamingStableReducible (baseType.subst sigma)
      (Term.subst termSubst
        (Term.glueElim modeIsUnivalent gluedValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (glueIsStable rhoIsInjective termRenaming).2 modeIsUnivalent

/-- Fundamental SN endpoint: `Term.glueIntro` at `Ty.glue` (K12.24).

Glue introduction is strongly normalizing whenever both payloads are
reducible at the substituted base type.  This is the M04-facing intro
endpoint for the current cubical fragment; the full `Ty.glue`
Reducible introduction closure still needs the `glueElim/glueIntro`
backward bridge at the base type. -/
theorem Reducible.fundamental_glueIntro_at_glue
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness baseRaw partialRaw : RawTerm scope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseIH :
        Reducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (partialIH :
        Reducible (baseType.subst sigma)
          (Term.subst termSubst partialValue)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue)) :=
  Term.glueIntro_isStronglyNormalizing
    modeIsUnivalent
    (baseType.subst sigma)
    (boundaryWitness.subst sigma.forRaw)
    (Reducible.isStronglyNormalizing baseIH)
    (Reducible.isStronglyNormalizing partialIH)

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

/-- **K12.27 identity-substitution boolean eliminator SN endpoint**.

Boolean elimination is SN-output at the current motive boundary.  This
identity wrapper exposes the exact M04 consequence from reducibility of
the scrutinee and both branches. -/
theorem Reducible.fundamental_identity_boolElim_at_bool_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.bool : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (thenIdentityReducible :
      Reducible
        ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) thenBranch))
    (elseIdentityReducible :
      Reducible
        ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) elseBranch)) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.boolElim scrutinee thenBranch elseBranch)
    (Reducible.fundamental_boolElim_at_bool
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible thenIdentityReducible
      elseIdentityReducible)

/-- **K12.27 identity-substitution natural eliminator SN endpoint**.

The current natural eliminator fundamental is SN-output and keeps the
successor-application closure explicit.  This identity wrapper only erases
the identity substitution from that exact endpoint; it does not claim a
full motive-type reducibility closure. -/
theorem Reducible.fundamental_identity_natElim_at_nat_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.nat : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (zeroIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) zeroBranch))
    (succIdentityReducible :
      Reducible ((Ty.arrow Ty.nat motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) succBranch))
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succRaw predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.natElim scrutinee zeroBranch succBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.natElim scrutinee zeroBranch succBranch)
    (Reducible.fundamental_natElim_at_nat
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible zeroIdentityReducible
      succIdentityReducible
      (by
        intro predecessorRaw predecessorIsSN
        rw [RawTerm.subst_identity succRaw]
        exact succAppIsSN predecessorIsSN))

/-- **K12.27 identity-substitution natural recursor SN endpoint**.

As with `fundamental_identity_natElim_at_nat_sn`, the recursive
contractum closure is an explicit M04 obligation.  The theorem is an
identity-route bridge, not a full recursive-motive reducibility theorem. -/
theorem Reducible.fundamental_identity_natRec_at_nat_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.nat : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (zeroIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) zeroBranch))
    (succIdentityReducible :
      Reducible
        ((Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) succBranch))
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.natRec scrutinee zeroBranch succBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.natRec scrutinee zeroBranch succBranch)
    (Reducible.fundamental_natRec_at_nat
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible zeroIdentityReducible
      succIdentityReducible
      (by
        intro predecessorRaw zeroTargetRaw succTargetRaw
          predecessorIsSN zeroTargetIsSN succTargetIsSN
        exact contractumIsSN predecessorIsSN zeroTargetIsSN
          succTargetIsSN))

/-- **K12.27 identity-substitution list eliminator SN endpoint**.

The current list eliminator endpoint keeps the cons-application closure
explicit because the list candidate tracks the tail at SN only.  This
identity wrapper preserves that exact obligation. -/
theorem Reducible.fundamental_identity_listElim_at_listType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.listType elementType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (nilIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) nilBranch))
    (consIdentityReducible :
      Reducible
        ((Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)).subst
            Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) consBranch))
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm scope}
        (headTerm :
          Term sourceCtx (elementType.subst Subst.identity) headRaw)
        (tailTerm :
          Term sourceCtx ((Ty.listType elementType).subst Subst.identity)
            tailRaw),
        Reducible (elementType.subst Subst.identity) headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app
            (Term.app
              (Term.subst (TermSubst.identity sourceCtx) consBranch)
              headTerm)
            tailTerm)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.listElim scrutinee nilBranch consBranch)
    (Reducible.fundamental_listElim_at_listType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible nilIdentityReducible
      consIdentityReducible
      (by
        intro headRaw tailRaw headTerm tailTerm headReducible tailIsSN
        exact consAppIsSN headTerm tailTerm headReducible tailIsSN))

/-- **K12.27 identity-substitution option match SN endpoint**. -/
theorem Reducible.fundamental_identity_optionMatch_at_optionType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.optionType elementType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (noneIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) noneBranch))
    (someIdentityReducible :
      Reducible ((Ty.arrow elementType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) someBranch)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.optionMatch scrutinee noneBranch someBranch)
    (Reducible.fundamental_optionMatch_at_optionType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible noneIdentityReducible
      someIdentityReducible)

/-- **K12.27 identity-substitution either match SN endpoint**. -/
theorem Reducible.fundamental_identity_eitherMatch_at_eitherType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.eitherType leftType rightType).subst
        Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (leftIdentityReducible :
      Reducible ((Ty.arrow leftType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) leftBranch))
    (rightIdentityReducible :
      Reducible ((Ty.arrow rightType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) rightBranch)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.eitherMatch scrutinee leftBranch rightBranch)
    (Reducible.fundamental_eitherMatch_at_eitherType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible leftIdentityReducible
      rightIdentityReducible)

/-- **K12.27 identity-substitution modal introduction SN endpoint**.

Layer-1 `modIntro` is type-preserving, so the M04 identity route only
needs SN of the identity-substituted inner term.  This theorem does not
claim a full modal reducibility introduction principle. -/
theorem Reducible.fundamental_identity_modIntro_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.modIntro innerTerm)
    (Term.modIntro_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution modal elimination SN endpoint**.

This is the SN-output identity bridge for the current Layer-1
type-preserving `modElim` constructor.  Full cross-modal eliminator
reducibility remains a separate K12.25/K12.20.U4 problem. -/
theorem Reducible.fundamental_identity_modElim_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.modElim innerTerm)
    (Term.modElim_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution modal subsumption SN endpoint**.

`subsume` is also type-preserving in the present Layer-1 kernel, so this
bridge only packages the M04 SN consequence of the child identity
reducibility witness. -/
theorem Reducible.fundamental_identity_subsume_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIdentityReducible :
      Reducible (innerType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) innerTerm)) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.subsume innerTerm)
    (Term.subsume_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIdentityReducible))

/-- **K12.27 identity-substitution identity eliminator SN endpoint**. -/
theorem Reducible.fundamental_identity_idJ_at_id_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst
          Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.idJ baseCase witness)
    (Reducible.fundamental_idJ_at_id
      (termSubst := TermSubst.identity sourceCtx)
      baseIdentityReducible witnessIdentityReducible)

/-- **K12.27 identity-substitution observational equality eliminator SN
endpoint**. -/
theorem Reducible.fundamental_identity_oeqJ_at_oeq_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst
          Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.oeqJ baseCase witness)
    (Reducible.fundamental_oeqJ_at_oeq
      (termSubst := TermSubst.identity sourceCtx)
      baseIdentityReducible witnessIdentityReducible)

/-- **K12.27 identity-substitution strict identity eliminator SN
endpoint**. -/
theorem Reducible.fundamental_identity_idStrictRec_at_idStrict_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIdentityReducible :
        Reducible (motiveType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) baseCase))
    (witnessIdentityReducible :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst
            Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) witness)) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  Term.strong_normalization_of_identity_subst
    (Term.idStrictRec modeIsStrict baseCase witness)
    (Reducible.fundamental_idStrictRec_at_idStrict
      (termSubst := TermSubst.identity sourceCtx)
      modeIsStrict baseIdentityReducible witnessIdentityReducible)


end LeanFX2
