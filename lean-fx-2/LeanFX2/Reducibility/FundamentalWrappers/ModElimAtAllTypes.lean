import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

/-! # LeanFX2.Reducibility.FundamentalWrappers.ModElimAtAllTypes

Fundamental cases for `Term.modElim` at every closed-leaf type:
`Ty.unit`, `Ty.bool`, `Ty.nat`, `Ty.empty`, `Ty.interval`,
`Ty.universe`, `Ty.session`, `Ty.effect`, and `Ty.modal`.  Each
ships the SN-direct case; renaming-stable transport is handled once by
`Reducible.fundamental_modElim_stable`.

## Root status

Layer 3 metatheory leaf.  Fifth slice of `FundamentalWrappers`. -/

namespace LeanFX2


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

end LeanFX2
