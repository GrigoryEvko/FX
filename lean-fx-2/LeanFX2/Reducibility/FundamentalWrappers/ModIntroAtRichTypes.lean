import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

/-! # LeanFX2.Reducibility.FundamentalWrappers.ModIntroAtRichTypes

Fundamental cases for `Term.modIntro` at the rich-former closed
types: `Ty.unit`, `Ty.universe`, `Ty.session`, and `Ty.modal`.
Each ships the SN-direct case; renaming-stable transport is handled
once by `Reducible.fundamental_modIntro_stable`.

## Root status

Layer 3 metatheory leaf.  Third slice of `FundamentalWrappers`. -/

namespace LeanFX2


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

end LeanFX2
