import LeanFX2.Reducibility.FundamentalAliases

/-! # LeanFX2.Reducibility.FundamentalCubical.CubicalGlueEliminators

Fundamental cases for the K12.24 cubical-eliminator family:
`Term.pathApp` at `Ty.path`, `Term.glueElim` at `Ty.glue`,
`Term.glueIntro` at `Ty.glue`.  Each ships SN-output endpoint +
renaming-stable companion + `Term.X_isStronglyNormalizing`
direct SN endpoints where applicable.

## Root status

Layer 3 metatheory leaf.  First slice of `FundamentalCubical`. -/

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

/-- Renaming-stable SN of `Term.glueIntro` at `Ty.glue` —
`IsRenamingStableIsSN` mirror of `fundamental_glueIntro_at_glue`.
The ambient `modeIsUnivalent` witness is mode-invariant; the renamed-
world raw SN witnesses are projected from the two `IsRenamingStableReducible`
premises at the current renaming. -/
theorem Reducible.fundamental_glueIntro_at_glue_sn_stable
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
    (baseIsStable :
        IsRenamingStableReducible (baseType.subst sigma)
          (Term.subst termSubst baseValue))
    (partialIsStable :
        IsRenamingStableReducible (baseType.subst sigma)
          (Term.subst termSubst partialValue)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue)) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have baseReducibleAtRho :=
    baseIsStable rhoIsInjective termRenaming
  have partialReducibleAtRho :=
    partialIsStable rhoIsInjective termRenaming
  exact Term.glueIntro_isStronglyNormalizing
    modeIsUnivalent
    ((baseType.subst sigma).rename rho)
    ((boundaryWitness.subst sigma.forRaw).rename rho)
    (Reducible.isStronglyNormalizing baseReducibleAtRho)
    (Reducible.isStronglyNormalizing partialReducibleAtRho)

end LeanFX2
