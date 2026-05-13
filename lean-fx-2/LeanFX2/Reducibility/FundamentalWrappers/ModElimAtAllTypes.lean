import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

/-! # LeanFX2.Reducibility.FundamentalWrappers.ModElimAtAllTypes

Fundamental cases for `Term.modElim` at every closed-leaf type:
`Ty.unit`, `Ty.bool`, `Ty.nat`, `Ty.empty`, `Ty.interval`,
`Ty.universe`, `Ty.session`, `Ty.effect`, and `Ty.modal`.  Each
ships an SN-direct case plus a renaming-stable companion.

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
