import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

/-! # LeanFX2.Reducibility.FundamentalWrappers.SubsumeAtRichTypes

Fundamental cases for `Term.subsume` at the rich-former closed
types: `Ty.unit` (modal-leaf canonical SN-direct closure),
`Ty.universe` (universe-polymorphism modal coercion), `Ty.session`
(session-type modal wrapper), and `Ty.modal` (modal-on-modal
composition).  Each ships the SN-direct case; renaming-stable
transport is handled once by `Reducible.fundamental_subsume_stable`.

## Root status

Layer 3 metatheory leaf.  Second slice of `FundamentalWrappers`. -/

namespace LeanFX2


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


end LeanFX2
