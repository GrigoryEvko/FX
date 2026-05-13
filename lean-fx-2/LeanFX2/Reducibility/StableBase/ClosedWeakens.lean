import LeanFX2.Reducibility.Foundation

/-! # LeanFX2.Reducibility.StableBase.ClosedWeakens

K12.20.U4 stable fundamental base cases for the closed-leaf
arms (`fundamental_unit_stable` etc.) plus the
`Reducible.weaken_X` SN-fallback weakening lemmas for unit /
bool / nat / empty / interval / universe / tyVar / session /
effect / modal — the 10 closed-leaf weakening arms.

## Root status

Layer 3 metatheory leaf.  First slice of K12.20.U4 stable base. -/

namespace LeanFX2


/-- Unit fundamental result is stable under future-world renamings. -/
theorem Reducible.fundamental_unit_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.unit (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.unit_isStronglyNormalizing

/-- Boolean true fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_boolTrue_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.boolTrue (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.boolTrue_isStronglyNormalizing

/-- Boolean false fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_boolFalse_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.boolFalse (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.boolFalse_isStronglyNormalizing

/-- Natural zero fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_natZero_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.natZero (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.natZero_isStronglyNormalizing

/-- **K12.20.U3.monotone SN-fallback arm**: unit reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.unit : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.unit : Ty level scope) sourceTerm) :
    Reducible ((Ty.unit : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: bool reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.bool : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.bool : Ty level scope) sourceTerm) :
    Reducible ((Ty.bool : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: nat reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.nat : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.nat : Ty level scope) sourceTerm) :
    Reducible ((Ty.nat : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: empty reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.empty : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.empty : Ty level scope) sourceTerm) :
    Reducible ((Ty.empty : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: interval reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.interval : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.interval : Ty level scope) sourceTerm) :
    Reducible ((Ty.interval : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: universe-code
reducibility is stable under one-binder weakening. -/
theorem Reducible.weaken_universe
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.universe universeLevel levelLe : Ty level scope)
        sourceRaw}
    (sourceReducible :
      Reducible (Ty.universe universeLevel levelLe : Ty level scope)
        sourceTerm) :
    Reducible
      ((Ty.universe universeLevel levelLe : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: type-variable fallback
reducibility is stable under one-binder weakening. -/
theorem Reducible.weaken_tyVar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {position : Fin scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.tyVar position) sourceRaw}
    (sourceReducible : Reducible (Ty.tyVar position) sourceTerm) :
    Reducible ((Ty.tyVar position).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: session reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_session
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {protocolStep sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.session protocolStep) sourceRaw}
    (sourceReducible : Reducible (Ty.session protocolStep) sourceTerm) :
    Reducible ((Ty.session protocolStep).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: effect reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_effect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {effectTag sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.effect carrierType effectTag) sourceRaw}
    (sourceReducible : Reducible (Ty.effect carrierType effectTag) sourceTerm) :
    Reducible ((Ty.effect carrierType effectTag).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: modal reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_modal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {modalityTag : Nat}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.modal modalityTag carrierType) sourceRaw}
    (sourceReducible :
      Reducible (Ty.modal modalityTag carrierType) sourceTerm) :
    Reducible ((Ty.modal modalityTag carrierType).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible


end LeanFX2
