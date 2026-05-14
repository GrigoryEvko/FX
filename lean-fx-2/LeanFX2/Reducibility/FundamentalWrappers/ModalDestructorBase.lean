import LeanFX2.Reducibility.TypedCR2Wrapup

/-! # LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

Base SN-direct and renaming-stable fundamental cases for the
three modal Term destructors (`Term.subsume`, `Term.modIntro`,
`Term.modElim`).  Each provides the foundation closure under SN
that per-type cases in the sibling sub-modules specialize.

## Root status

Layer 3 metatheory leaf.  First slice of `FundamentalWrappers`. -/

namespace LeanFX2


/-! ## K12.20.BC SN-direct fundamental cases for `Term.subsume`

`Term.subsume` is the Layer 1 modal-cumulativity coercion: a
type-preserving wrapper `Term ctx innerType innerRaw → Term ctx
innerType (RawTerm.subsume innerRaw)`.  Its `Term.subst` commute
is definitional (`LeanFX2/Term/Subst.lean:303-304` — substitution
distributes componentwise over the wrapper).

For SN-direct `innerType` arms — those where `Reducible ty term`
unfolds to `Term.isStronglyNormalizing term` (i.e. unit / bool /
nat / empty / interval / universe / session / effect / modal —
all closed-leaf or raw-payload-shaped) — the fundamental case
ships as a one-line composition of the K12.20.AB raw SN helper
with the `innerIH`.  No per-Ty case analysis is needed because
the substituted innerType retains its SN-direct shape under
`Ty.subst`.

This batch covers four representative SN-direct arms (unit,
universe, session, modal) spanning closed-leaf / level-
parameterized / raw-payload-carrying / K12.25-modal targets.
The remaining SN-direct arms (bool / nat / empty / interval /
effect) follow the identical 1-line pattern and ship in a
future K12.20.BD tick when the modIntro companion cases land.

Compound-Ty `innerType` arms (arrow / sigmaTy / listType / etc.)
are NOT covered here — those require the full
`Reducible.subsume_intro` framework with case analysis on the
substituted Ty and step-closure under elimination forms.  Such
arms ship at K12.25 alongside the full modal-cases milestone. -/

/-- Type-preserving subsumption preserves reducibility at any SN-direct
candidate arm. -/
theorem Reducible.fundamental_subsume_SNDirect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIH :
      Reducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    Reducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) :=
  Reducible.of_isStronglyNormalizing_when_SNDirect
    sourceTypeIsSNDirect
    (RawTerm.subsume_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIH))

/-- Type-preserving modal introduction preserves reducibility at any
SN-direct candidate arm. -/
theorem Reducible.fundamental_modIntro_SNDirect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIH :
      Reducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    Reducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) :=
  Reducible.of_isStronglyNormalizing_when_SNDirect
    sourceTypeIsSNDirect
    (RawTerm.modIntro_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIH))

/-- Type-preserving modal elimination preserves reducibility at any
SN-direct candidate arm. -/
theorem Reducible.fundamental_modElim_SNDirect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIH :
      Reducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    Reducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) :=
  Reducible.of_isStronglyNormalizing_when_SNDirect
    sourceTypeIsSNDirect
    (Term.modElim_isStronglyNormalizing
      (Reducible.isStronglyNormalizing innerIH))

/-- Stable subsumption uses only the SN-direct candidate classifier,
not one theorem per closed type. -/
theorem Reducible.fundamental_subsume_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIsStable :
      IsRenamingStableReducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact IsRenamingStableReducible.of_stableSN_when_SNDirect
    sourceTypeIsSNDirect
    (by
      intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
      exact RawTerm.subsume_isStronglyNormalizing
        (Reducible.isStronglyNormalizing
          (innerIsStable rhoIsInjective termRenaming)))

/-- Stable modal introduction uses only the SN-direct candidate
classifier, not one theorem per closed type. -/
theorem Reducible.fundamental_modIntro_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIsStable :
      IsRenamingStableReducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact IsRenamingStableReducible.of_stableSN_when_SNDirect
    sourceTypeIsSNDirect
    (by
      intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
      exact RawTerm.modIntro_isStronglyNormalizing
        (Reducible.isStronglyNormalizing
          (innerIsStable rhoIsInjective termRenaming)))

/-- Stable modal elimination uses only the SN-direct candidate
classifier, not one theorem per closed type. -/
theorem Reducible.fundamental_modElim_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {sourceType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx sourceType innerRaw}
    (sourceTypeIsSNDirect :
      Reducible.IsSNDirect (sourceType.subst sigma))
    (innerIsStable :
      IsRenamingStableReducible (sourceType.subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible (sourceType.subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact IsRenamingStableReducible.of_stableSN_when_SNDirect
    sourceTypeIsSNDirect
    (by
      intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
      exact Term.modElim_isStronglyNormalizing
        (Reducible.isStronglyNormalizing
          (innerIsStable rhoIsInjective termRenaming)))

end LeanFX2
