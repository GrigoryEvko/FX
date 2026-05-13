import LeanFX2.Reducibility.NeutralSNClosure

/-! # LeanFX2.Reducibility.TypedCR2Direct.VarShapeDirect

K12.20.E + K12.20.U2 SN-direct closures.  Variables at every
SN-direct `Ty` arm are Reducible by combining their CR3 base
facts (vacuous progress closure) with
`Reducible.of_isStronglyNormalizing_when_SNDirect`.

## What ships

* `Term.isStronglyNormalizing_of_varShape` — universal SN for every
  varShape Term regardless of Ty.
* `Reducible.X_of_varShape` for each SN-direct arm (X ∈ unit /
  bool / nat / empty / interval / universe / tyVar / session /
  effect / modal).
* `Reducible.X_of_progress_closure` — the matching SN-direct CR3
  arms keyed on the raw progress-closure predicate.

## Root status

Layer 3 metatheory leaf.  Second slice of `TypedCR2Direct`. -/

namespace LeanFX2

/-! ## K12.20.E typed neutral-var reducibility at SN-direct arms

Variables-as-reducible: every typed `Term` whose raw projection is
`RawTerm.var position` is reducible at any SN-direct Reducible arm.
Foundational for the K12.20.F `ReducibleSubst.singleton` /
`ReducibleSubst.lift` constructors, where var-shaped Terms (cast
through `Ty.weaken_subst_singleton` / `Ty.weaken_subst_commute`
equalities) need to be exhibited reducible at the substituted-out
type.

Generic over the Term's type-level index — the lemmas accept ANY
`Term context ty (RawTerm.var position)` (i.e. anything whose raw
form is a var), not specifically `Term.var position`.  This covers:
* The canonical `Term.var position` form when `ty = varType context
  position` matches by definition.
* `▸`-cast forms `h ▸ Term.var position` used in TermSubst.lift /
  .singleton, where `h : varType context position = ty`.  The `▸`
  preserves the raw index, so the casted term still has raw form
  `RawTerm.var position`.

Body across all 10 arms is identical: `RawTerm.var_isStronglyNormalizing
position`.  Works by Reducible's definitional unfolding:
`Reducible Ty.X term = Term.isStronglyNormalizing term = RawTerm.
isStronglyNormalizing term.toRaw = RawTerm.isStronglyNormalizing
(RawTerm.var position)` — exactly the type of
`var_isStronglyNormalizing`.

Compound Reducible arms split into two families.  Weak/SN-output
arms whose closures only ask for SN of eliminator results can be
closed directly from the raw neutral-eliminator SN helpers once their
branch-SN premises are explicit.  Strong-output arms (arrow, sigmaTy,
path, glue, equiv, refine, record, codata) use the higher-order
varShape pattern: each arm takes the CR3 hook for its strict sub-Ty
as an explicit parameter, mirroring `Reducible.step_preserves`'
higher-order CR2 structure without pretending that arbitrary neutral
CR3 has already shipped.
-/

/-- **K12.20.E foundation**: any Term whose raw projection is
`RawTerm.var position` is strongly normalizing, regardless of its
declared type.  Body uses raw `var_isStronglyNormalizing` directly;
`Term.isStronglyNormalizing` definitionally unfolds to the raw SN
at the term's raw index, which is `RawTerm.var position` by the
type-level index discipline. -/
theorem Term.isStronglyNormalizing_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {ty : Ty level scope}
    {position : Fin scope}
    (_term : Term context ty (RawTerm.var position)) :
    Term.isStronglyNormalizing _term :=
  RawTerm.var_isStronglyNormalizing position

/-- **K12.20.E unit arm**: variables are reducible at Ty.unit. -/
theorem Reducible.unit_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.unit (RawTerm.var position)) :
    Reducible Ty.unit term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E bool arm**. -/
theorem Reducible.bool_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.bool (RawTerm.var position)) :
    Reducible Ty.bool term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E nat arm**. -/
theorem Reducible.nat_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.nat (RawTerm.var position)) :
    Reducible Ty.nat term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E empty arm**. -/
theorem Reducible.empty_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.empty (RawTerm.var position)) :
    Reducible Ty.empty term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E interval arm**. -/
theorem Reducible.interval_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    (term : Term context Ty.interval (RawTerm.var position)) :
    Reducible Ty.interval term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E universe arm**. -/
theorem Reducible.universe_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {position : Fin scope}
    (term :
        Term context (Ty.universe universeLevel levelLe)
          (RawTerm.var position)) :
    Reducible (Ty.universe universeLevel levelLe) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E tyVar arm**. -/
theorem Reducible.tyVar_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {tyVarPosition : Fin scope}
    {position : Fin scope}
    (term :
        Term context (Ty.tyVar tyVarPosition) (RawTerm.var position)) :
    Reducible (Ty.tyVar tyVarPosition) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E session arm**. -/
theorem Reducible.session_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.session protocolStep) (RawTerm.var position)) :
    Reducible (Ty.session protocolStep) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E effect arm**. -/
theorem Reducible.effect_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.effect carrierType effectTag)
          (RawTerm.var position)) :
    Reducible (Ty.effect carrierType effectTag) term :=
  Term.isStronglyNormalizing_of_varShape term

/-- **K12.20.E modal arm**. -/
theorem Reducible.modal_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.modal modalityTag carrierType)
          (RawTerm.var position)) :
    Reducible (Ty.modal modalityTag carrierType) term :=
  Term.isStronglyNormalizing_of_varShape term

/-! ### K12.20.U2 SN-direct CR3 arms

For SN-direct Reducible arms, typed CR3 reduces to the raw SN
constructor direction: if every non-trivial raw reduct is SN, then
the source term is SN, hence Reducible at that type.  These lemmas
do not claim the compound-Ty CR3 theorem; they establish exactly the
ten arms whose Reducible definition has no additional closure field. -/

/-- **K12.20.U2 unit arm**: CR3 for the unit SN-direct arm. -/
theorem Reducible.unit_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.unit sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.unit sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 bool arm**. -/
theorem Reducible.bool_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.bool sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.bool sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 nat arm**. -/
theorem Reducible.nat_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.nat sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.nat sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 empty arm**. -/
theorem Reducible.empty_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.empty sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.empty sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 interval arm**. -/
theorem Reducible.interval_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context Ty.interval sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible Ty.interval sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 universe arm**. -/
theorem Reducible.universe_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.universe universeLevel levelLe) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.universe universeLevel levelLe) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 tyVar arm**. -/
theorem Reducible.tyVar_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {tyVarPosition : Fin scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.tyVar tyVarPosition) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.tyVar tyVarPosition) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 session arm**. -/
theorem Reducible.session_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.session protocolStep) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.session protocolStep) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 effect arm**. -/
theorem Reducible.effect_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.effect carrierType effectTag) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.effect carrierType effectTag) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure

/-- **K12.20.U2 modal arm**. -/
theorem Reducible.modal_of_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.modal modalityTag carrierType) sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Reducible (Ty.modal modalityTag carrierType) sourceTerm :=
  Term.isStronglyNormalizing.of_raw_progress_closure sourceTerm closure



end LeanFX2
