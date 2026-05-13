import LeanFX2.Reducibility.TypedCR2Wrapup

/-! # LeanFX2.Reducibility.FundamentalWrappers — modal / cumulUp cases

The fundamental-theorem cases for modal wrappers (`subsume`,
`modIntro`, `modElim`) plus K12.25's 8-modality modal destructor
cases.

## What ships

* K12.20.BC SN-direct fundamental cases for `Term.subsume` at
  every admitting Ty arm.  These are the cases that benefited
  from the propext-clean classifier in `Classifier.lean` (no
  longer leak propext through `IsSNDirect`'s wildcard form).
* K12.20.BD SN-direct fundamental cases for `Term.modIntro` at
  every admitting Ty arm.
* K12.20.BE remaining SN-direct fundamental cases (combinations
  of subsume / modIntro at the universe / session / effect / modal
  arms).
* K12.25 modal destructor cases — the fundamental theorem for
  `Term.modElim` at each of the 8 modalities (♭, ◇, □, ♯, ghost,
  cap, later, clock).

## Root status

Layer 3 metatheory leaf.  Part of the K12.20.U4 / K12.25
fundamental-theorem cascade.  Consumed by `FundamentalAliases`
and the eventual M04 close-out. -/

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
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact Reducible.of_isStronglyNormalizing_when_SNDirect
    (Reducible.IsSNDirect.rename sourceTypeIsSNDirect)
    (RawTerm.subsume_isStronglyNormalizing
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
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact Reducible.of_isStronglyNormalizing_when_SNDirect
    (Reducible.IsSNDirect.rename sourceTypeIsSNDirect)
    (RawTerm.modIntro_isStronglyNormalizing
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
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact Reducible.of_isStronglyNormalizing_when_SNDirect
    (Reducible.IsSNDirect.rename sourceTypeIsSNDirect)
    (Term.modElim_isStronglyNormalizing
      (Reducible.isStronglyNormalizing
        (innerIsStable rhoIsInjective termRenaming)))

/-- **K12.20.BC.1 subsume fundamental case at `Ty.unit`** —
canonical SN-direct closed-leaf coverage.  Layer 1
type-preserving wrapper at the unit type.  `(Ty.unit).subst
sigma = Ty.unit` (`Foundation/Subst.lean:102` — definitional);
`Reducible Ty.unit term = Term.isStronglyNormalizing term`
(`Reducibility.lean:325`); `Term.subst termSubst (Term.subsume
inner) = Term.subsume (Term.subst termSubst inner)`
(`Term/Subst.lean:303-304` — definitional).  The K12.20.AB
`RawTerm.subsume_isStronglyNormalizing` lifts SN of the inner
to SN of the wrapped form in one composition. -/
theorem Reducible.fundamental_subsume_at_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIH : Reducible ((Ty.unit : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Unit subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_unit_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (sourceType := (Ty.unit : Ty level scope))
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BC.2 subsume fundamental case at `Ty.universe`** —
SN-direct level-parameterized coverage.  `(Ty.universe lvl
levelLe).subst sigma = Ty.universe lvl levelLe`
(`Foundation/Subst.lean:123` — definitional, sigma doesn't see
the level parameter); the SN-direct invariant carries through
the level parameter identically to the closed-leaf case.  Same
single-line composition as the unit case. -/
theorem Reducible.fundamental_subsume_at_universe
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIH :
        Reducible ((Ty.universe outerLevel levelLe).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Universe subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_universe_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BC.3 subsume fundamental case at `Ty.session`** —
SN-direct raw-payload coverage.  `(Ty.session protocolStep).subst
sigma = Ty.session (protocolStep.subst sigma.forRaw)`
(`Foundation/Subst.lean:150-151`) — substitution recurses on
the raw payload via `sigma.forRaw`, but the outer `Ty.session`
constructor is preserved, so the resulting Ty is still
SN-direct (`Reducibility.lean:588-589`).  Same one-line
composition as the closed-leaf case; the raw-payload
substitution lives transparently inside `innerIH`'s type. -/
theorem Reducible.fundamental_subsume_at_session
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIH :
        Reducible ((Ty.session protocolStep).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Session subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_session_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BC.4 subsume fundamental case at `Ty.modal`** —
SN-direct modal coverage (K12.25 milestone target).
`(Ty.modal modalityTag carrierType).subst sigma = Ty.modal
modalityTag (carrierType.subst sigma)`
(`Foundation/Subst.lean:154-155`) — substitution recurses on
the carrier Ty but preserves the outer `Ty.modal` constructor,
keeping the SN-direct invariant.  Per Layer 1 modal scaffolding
(`Reducibility.lean:604-627`), no Term ctor currently inhabits
`Ty.modal _ _`, but the `Reducible` arm is shipped for
forward-compat with Layer 6 typed `modIntroCross` / `modElimCross`
(CUMUL-7.1.{1,2}, #1689-1691); when those land,
`fundamental_subsume_at_modal` is the unchanged single-line
modal-subsume case. -/
theorem Reducible.fundamental_subsume_at_modal
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIH :
        Reducible ((Ty.modal modalityTag carrierType).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.modal modalityTag carrierType).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Modal subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_modal_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible
        ((Ty.modal modalityTag carrierType).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible
      ((Ty.modal modalityTag carrierType).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-! ## K12.20.BD SN-direct fundamental cases for `Term.modIntro`

`Term.modIntro` is the Layer 1 modal-introduction wrapper —
sister to `Term.subsume`, with identical type-preserving
structure: `Term ctx innerType innerRaw → Term ctx innerType
(RawTerm.modIntro innerRaw)`.  `Term.subst` commute is
definitional (`LeanFX2/Term/Subst.lean:299-300`).

Per Layer 1 modal scaffolding (`Reducibility.lean:604-627` +
`Term.lean:295-300`), modIntro preserves innerType rather than
producing `Ty.modal _ innerType`; Layer 6 will refactor to take
a Modality and produce `Ty.modal modality innerType` via the
CUMUL-7.1.{1,2} `modIntroCross` / `modElimCross` ctors
(#1689-1691).  This batch covers the Layer 1 SN-direct
fragment; the per-modality Tait closure ships at K12.25
alongside Layer 6's typed modIntroCross.

Four representative SN-direct arms mirroring K12.20.BC's
subsume quartet (unit / universe / session / modal — closed-
leaf / level-parameterized / raw-payload-carrying / K12.25
modal target).  Each ships as a 1-line composition of the
K12.20.Y `RawTerm.modIntro_isStronglyNormalizing` helper with
the `innerIH`. -/

/-- **K12.20.BD.1 modIntro fundamental case at `Ty.unit`** —
Layer 1 modal-introduction wrapper at the unit type.
`(Ty.unit).subst sigma = Ty.unit` (definitional); `Reducible
Ty.unit term = Term.isStronglyNormalizing term` (def-unfold);
`Term.subst termSubst (Term.modIntro inner) = Term.modIntro
(Term.subst termSubst inner)` (`Term/Subst.lean:299-300` —
definitional).  K12.20.Y `RawTerm.modIntro_isStronglyNormalizing`
lifts SN of the inner to SN of the wrapped form. -/
theorem Reducible.fundamental_modIntro_at_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIH : Reducible ((Ty.unit : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Unit modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_unit_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BD.2 modIntro fundamental case at `Ty.universe`** —
SN-direct level-parameterized.  `(Ty.universe outerLevel
levelLe).subst sigma = Ty.universe outerLevel levelLe`
(`Foundation/Subst.lean:123`) — substitution doesn't touch the
level parameter.  Same 1-line composition as the unit case. -/
theorem Reducible.fundamental_modIntro_at_universe
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIH :
        Reducible ((Ty.universe outerLevel levelLe).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Universe modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_universe_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BD.3 modIntro fundamental case at `Ty.session`** —
SN-direct raw-payload-carrying.  `(Ty.session protocolStep).subst
sigma = Ty.session (protocolStep.subst sigma.forRaw)`
(`Foundation/Subst.lean:150-151`) — the outer `Ty.session`
constructor is preserved under subst, keeping the SN-direct
invariant.  The raw-payload substitution lives inside
innerIH's type. -/
theorem Reducible.fundamental_modIntro_at_session
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIH :
        Reducible ((Ty.session protocolStep).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Session modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_session_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BD.4 modIntro fundamental case at `Ty.modal`** —
SN-direct modal (K12.25 milestone target).  `(Ty.modal
modalityTag carrierType).subst sigma = Ty.modal modalityTag
(carrierType.subst sigma)` (`Foundation/Subst.lean:154-155`)
— the outer `Ty.modal` constructor is preserved, keeping the
SN-direct invariant.  Per Layer 1 scaffolding, no Term ctor
currently inhabits `Ty.modal _ _`; this case is shipped for
forward-compat with Layer 6's typed modIntroCross / modElimCross
(CUMUL-7.1.{1,2}, #1689-1691).  When those ctors land, this
single-line modal-modIntro case carries through unchanged. -/
theorem Reducible.fundamental_modIntro_at_modal
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIH :
        Reducible ((Ty.modal modalityTag carrierType).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.modal modalityTag carrierType).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_modal_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible
        ((Ty.modal modalityTag carrierType).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible
      ((Ty.modal modalityTag carrierType).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-! ## K12.20.BE Remaining SN-direct fundamental cases — subsume / modIntro

Five additional SN-direct arms covering the closed-leaf and
raw-payload-carrying types not in K12.20.BC/BD's
representative quartet: `Ty.bool`, `Ty.nat`, `Ty.empty`,
`Ty.interval`, and `Ty.effect`.  All five preserve their outer
Ty constructor under substitution (`Foundation/Subst.lean:103,
104, 126, 127, 152-153` respectively), keeping the SN-direct
invariant per `Reducibility.lean:326-329, 602-603`.

Ten total cases (5 subsume + 5 modIntro) closing the SN-direct
fragment of `Reducible.fundamental_subsume` and
`fundamental_modIntro` at Layer 1.  Same single-line composition
pattern as K12.20.BC/BD: `RawTerm.{subsume,modIntro}_isStronglyNormalizing
innerIH`.

After K12.20.BE, the full SN-direct coverage matrix is:

| Ty           | subsume | modIntro |
| ------------ | ------- | -------- |
| unit         | BC.1    | BD.1     |
| bool         | BE.1    | BE.6     |
| nat          | BE.2    | BE.7     |
| empty        | BE.3    | BE.8     |
| interval     | BE.4    | BE.9     |
| universe     | BC.2    | BD.2     |
| session      | BC.3    | BD.3     |
| effect       | BE.5    | BE.10    |
| modal        | BC.4    | BD.4     |

`Ty.tyVar` is intentionally excluded: substitution maps
`tyVar position → sigma.forTy position` (`Foundation/Subst.lean:111-112`)
to an arbitrary Ty, breaking the SN-direct invariant.  The
tyVar case ships at K12.25 alongside the compound-Ty machinery.

Compound-Ty innerType arms (arrow / sigmaTy / listType /
optionType / eitherType / id / oeq / idStrict / path / glue /
equiv / refine / record / codata / piTy) require the full
`Reducible.subsume_intro` / `Reducible.modIntro_intro`
framework with case analysis on the substituted Ty and step-
closure under elimination forms — those ship at K12.25. -/

/-- **K12.20.BE.1 subsume at `Ty.bool`** — SN-direct closed-leaf.
`(Ty.bool).subst sigma = .bool` (`Foundation/Subst.lean:103`). -/
theorem Reducible.fundamental_subsume_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Boolean subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_bool_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.2 subsume at `Ty.nat`** — SN-direct closed-leaf.
`(Ty.nat).subst sigma = .nat` (`Foundation/Subst.lean:104`). -/
theorem Reducible.fundamental_subsume_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Natural subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.3 subsume at `Ty.empty`** — SN-direct closed-leaf.
`(Ty.empty).subst sigma = .empty` (`Foundation/Subst.lean:126`). -/
theorem Reducible.fundamental_subsume_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Empty-type subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_empty_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.4 subsume at `Ty.interval`** — SN-direct cubical
closed-leaf.  `(Ty.interval).subst sigma = .interval`
(`Foundation/Subst.lean:127`). -/
theorem Reducible.fundamental_subsume_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Interval subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_interval_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.5 subsume at `Ty.effect`** — SN-direct
raw-payload-carrying.  `(Ty.effect carrier tag).subst sigma =
.effect (carrier.subst sigma) (tag.subst sigma.forRaw)`
(`Foundation/Subst.lean:152-153`) — the outer `Ty.effect`
constructor is preserved.  Sister to K12.20.BC.3 session. -/
theorem Reducible.fundamental_subsume_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Effect subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_effect_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.6 modIntro at `Ty.bool`** — sister to BE.1 via
K12.20.Y `RawTerm.modIntro_isStronglyNormalizing`. -/
theorem Reducible.fundamental_modIntro_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Boolean modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_bool_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.7 modIntro at `Ty.nat`** — sister to BE.2. -/
theorem Reducible.fundamental_modIntro_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Natural modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.8 modIntro at `Ty.empty`** — sister to BE.3. -/
theorem Reducible.fundamental_modIntro_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Empty-type modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_empty_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.9 modIntro at `Ty.interval`** — sister to BE.4. -/
theorem Reducible.fundamental_modIntro_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Interval modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_interval_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.10 modIntro at `Ty.effect`** — sister to BE.5. -/
theorem Reducible.fundamental_modIntro_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Effect modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_effect_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-! ## K12.25 modal destructor cases -/

/-- **K12.25 modElim fundamental case at `Ty.unit`**.

Layer-1 `Term.modElim` is type-preserving.  At the closed unit type,
`Reducible` unfolds to SN, so the fundamental case is exactly the
typed modal-elimination SN preservation lemma. -/
theorem Reducible.fundamental_modElim_at_unit
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIH : Reducible ((Ty.unit : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.unit : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.bool`**. -/
theorem Reducible.fundamental_modElim_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.nat`**. -/
theorem Reducible.fundamental_modElim_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.empty`**. -/
theorem Reducible.fundamental_modElim_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.interval`**. -/
theorem Reducible.fundamental_modElim_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.universe`**. -/
theorem Reducible.fundamental_modElim_at_universe
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIH :
        Reducible ((Ty.universe outerLevel levelLe).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.session`**. -/
theorem Reducible.fundamental_modElim_at_session
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIH :
        Reducible ((Ty.session protocolStep).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.effect`**. -/
theorem Reducible.fundamental_modElim_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- **K12.25 modElim fundamental case at `Ty.modal`**. -/
theorem Reducible.fundamental_modElim_at_modal
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIH :
        Reducible ((Ty.modal modalityTag carrierType).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.modal modalityTag carrierType).subst sigma)
              (Term.subst termSubst (Term.modElim innerTerm)) :=
  Term.modElim_isStronglyNormalizing innerIH

/-- Unit modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_unit_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.unit innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Boolean modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_bool_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Natural modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Empty-type modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_empty_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Interval modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_interval_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Universe modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_universe_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.universe outerLevel levelLe) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Session modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_session_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx (Ty.session protocolStep) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Effect modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_effect_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- Modal elimination preserves fundamental stability. -/
theorem Reducible.fundamental_modElim_at_modal_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modalityTag : Nat) {carrierType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.modal modalityTag carrierType) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible
        ((Ty.modal modalityTag carrierType).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible
      ((Ty.modal modalityTag carrierType).subst sigma)
      (Term.subst termSubst (Term.modElim innerTerm)) := by
  exact Reducible.fundamental_modElim_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable


end LeanFX2
