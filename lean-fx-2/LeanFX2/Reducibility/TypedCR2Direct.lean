import LeanFX2.Reducibility.NeutralSNClosure

/-! # LeanFX2.Reducibility.TypedCR2Direct — K12.20.D / E / U2 / AZ

The typed forward-step closure for SN-direct Reducible arms and
the varShape compound CR3 closure (Codex's K12.12 architectural
insight per `feedback_lean_varshape_pattern.md`: parameterize
compound-arm CR3 over a `subTyCR3` hypothesis instead of
recursing on Ty).

## What ships

* K12.20.D — typed CR2 lift for each SN-direct Reducible arm
  (unit / bool / nat / empty / interval / universe / session /
  effect / modal).  Each takes a typed `Step` and shows the target
  remains Reducible at the same arm.
* K12.20.E — typed neutral-var reducibility: variables at every
  SN-direct Ty arm are Reducible by combining their CR3 base
  facts (vacuous progress closure) with
  `Reducible.of_isStronglyNormalizing_when_SNDirect`.
* K12.20.U2 SN-direct CR3 arms — Reducible.cr3 typed closure for
  each SN-direct arm; pairs with the raw IsNeutral cascade.
* K12.20.AZ compound varShape CR3 — the parameterized closure for
  arrow / sigmaTy / piTy / id family / parametric inductive arms.
  Takes `subTyCR3` evidence as hypothesis (sidesteps the
  structural-recursion wall in `Reducible`).

## Root status

Layer 3 metatheory leaf.  Consumed by `TypedCR2Generic` (U3
dispatch), `TypedCR2Compound` (per-ctor cases), and `TypedCR2Wrapup`
(unified `Reducible.step_preserves`). -/

namespace LeanFX2


/-! ## K12.20.D typed CR2 lift for SN-direct Reducible arms

CR2 at the typed `Reducible` level for the ten SN-direct arms.  Each
arm's `Reducible Ty.X _ = Term.isStronglyNormalizing _` unfolds
definitionally to `RawTerm.isStronglyNormalizing _.toRaw`, so the
typed-level CR2 statement reduces — definitionally, no rewriting —
to K12.20.B's raw `step_preserves`.  Each theorem body is a single
application of `RawTerm.isStronglyNormalizing.step_preserves`.

These 10 lemmas cover the SN-direct closures shipped in K12.2-K12.4
(closed leaves: unit / bool / nat / empty / interval / universe /
tyVar) plus K12.13/K12.15 (Layer-1 SN-fallback for session / effect /
modal — no destructor available at Layer 1, so closure cannot enrich
beyond SN).  The remaining 15 compound arms (arrow / piTy / Σ / id /
list / option / either / path / glue / oeq / idStrict / equiv /
refine / record / codata) need per-Ty case analysis on the closure
structure (preserving both SN AND the eliminator closures); those
land in K12.20.G.

Note: these typed CR2 lemmas use the raw step `RawStep.parProgress
sourceRaw targetRaw` directly rather than a typed-Step relation,
because (1) Reducible's SN-direct unfolding bypasses the typed step
entirely — only `sourceRaw` and `targetRaw` are needed; (2) any
typed Step at the relevant ctors projects down to a parProgress on
the raw forms via the typed→raw bridge (which downstream cascade
steps invoke); (3) keeping the K12.20.D signature raw-only means
zero dependency on the typed Step relation, so the lemmas compose
freely with K12.20.A/B/C in the K12.20.H Term.lam case.
-/

/-- **K12.20.D unit arm**: Reducible at Ty.unit is closed under raw
parallel-progress reduction. -/
theorem Reducible.step_preserves_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.unit sourceRaw}
    {target : Term context Ty.unit targetRaw}
    (sourceReducible : Reducible Ty.unit source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.unit target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D bool arm**. -/
theorem Reducible.step_preserves_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.bool sourceRaw}
    {target : Term context Ty.bool targetRaw}
    (sourceReducible : Reducible Ty.bool source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.bool target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D nat arm**. -/
theorem Reducible.step_preserves_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.nat sourceRaw}
    {target : Term context Ty.nat targetRaw}
    (sourceReducible : Reducible Ty.nat source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.nat target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D empty arm**.  Vacuous in practice (no Term inhabits
`Ty.empty` at the typed layer), but the closure ships uniformly with
the other SN-direct arms for cascade symmetry. -/
theorem Reducible.step_preserves_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.empty sourceRaw}
    {target : Term context Ty.empty targetRaw}
    (sourceReducible : Reducible Ty.empty source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.empty target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D interval arm**.  Cubical-mode-only interval terms;
the closure preserves SN under reduction.  Per K12.4, Ty.interval is
a closed leaf shipping SN directly. -/
theorem Reducible.step_preserves_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context Ty.interval sourceRaw}
    {target : Term context Ty.interval targetRaw}
    (sourceReducible : Reducible Ty.interval source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible Ty.interval target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D universe arm**.  Universe-coded types ship SN directly
per K12.4; the closure preserves SN through type-code reductions
(e.g. `Step.eqType` reducing identity-of-universe to equiv). -/
theorem Reducible.step_preserves_universe
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.universe universeLevel levelLe) sourceRaw}
    {target : Term context (Ty.universe universeLevel levelLe) targetRaw}
    (sourceReducible :
        Reducible (Ty.universe universeLevel levelLe) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.universe universeLevel levelLe) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D tyVar arm**.  Abstract type-variable inhabitants ship
SN directly; the closure preserves SN under reduction.  Used by the
fundamental lemma when threading through polymorphic type
parameters. -/
theorem Reducible.step_preserves_tyVar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.tyVar position) sourceRaw}
    {target : Term context (Ty.tyVar position) targetRaw}
    (sourceReducible : Reducible (Ty.tyVar position) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.tyVar position) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D session arm**.  Layer-1 SN-fallback per K12.15 (no
projection eliminator exists at Layer 1).  Session protocol-state
reductions preserve SN — the typed Sessions layer (#1268 K09) will
ship per-step closures requiring per-step CR2 case analysis. -/
theorem Reducible.step_preserves_session
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.session protocolStep) sourceRaw}
    {target : Term context (Ty.session protocolStep) targetRaw}
    (sourceReducible : Reducible (Ty.session protocolStep) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.session protocolStep) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D effect arm**.  Layer-1 SN-fallback per K12.15 (no
`Term.effectHandle` destructor exists at Layer 1).  Effectful-term
reductions preserve SN — the Effects layer (#1345 D5.9, #1346 D5.10)
will ship handler-discharge closures requiring per-handler CR2. -/
theorem Reducible.step_preserves_effect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.effect carrierType effectTag) sourceRaw}
    {target : Term context (Ty.effect carrierType effectTag) targetRaw}
    (sourceReducible :
        Reducible (Ty.effect carrierType effectTag) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.effect carrierType effectTag) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

/-- **K12.20.D modal arm**.  Layer-1 SN-fallback per K12.13 (no
typed `Term` ctor inhabits `Ty.modal _ _` at Layer 1 — the type
former is structurally uninhabited until Layer 6's modIntroCross /
modElimCross land).  The closure remains uniformly statable for
cascade symmetry — vacuous in practice at Layer 1, real once
Layer 6 ships. -/
theorem Reducible.step_preserves_modal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.modal modalityTag carrierType) sourceRaw}
    {target : Term context (Ty.modal modalityTag carrierType) targetRaw}
    (sourceReducible :
        Reducible (Ty.modal modalityTag carrierType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.modal modalityTag carrierType) target :=
  RawTerm.isStronglyNormalizing.step_preserves sourceReducible rawStep

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

/-! ### K12.20.AZ compound varShape — SN-only-closure compound types

Four compound-Ty `_of_varShape` lemmas where Reducible's closure
clause demands only SN of the eliminator result (not full
Reducible).  These extend K12.20.E's SN-direct batch with the
SN-only-closure compound arms — dependent Π, HoTT identity,
observational equality, strict identity — each discharged by ONE
Stage 1 neutral-head SN helper.  Compound arms with
Reducible-on-sub-Ty closures (arrow / sigmaTy / listType /
optionType / eitherType / path / glue / equiv / refine / record)
require induction-on-Ty and ship later in K12.20.BA+. -/

/-- **K12.20.U2 arrow varShape arm**: variables are reducible at
function type once the codomain CR3 step is available.

This is the binder-lift entry point for the arrow candidate.  The
function variable itself is SN by `Term.isStronglyNormalizing_of_varShape`.
For the application closure, `app (var position) argumentRaw` is neutral;
the raw Stage-1 lemma `RawTerm.app_var_isStronglyNormalizing` supplies the
progress-closure needed by the codomain CR3 hook. -/
theorem Reducible.arrow_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.arrow domainType codomainType)
          (RawTerm.var position))
    (codomainCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context codomainType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType sourceTerm) :
    Reducible (Ty.arrow domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     codomainCR3 (Term.app term argumentTerm)
       (RawTerm.IsNeutral.app (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.app_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 arrow CR3 arm**: a neutral function is reducible at
`Ty.arrow domain codomain` when every raw progress reduct is SN and
the codomain CR3 hook is available.

The function itself is SN by the neutral progress-closure wrapper.
For an argument, `app neutral argument` is neutral and strongly
normalizing by `RawTerm.app_neutral_isStronglyNormalizing`; that SN
witness supplies the codomain CR3 hook's progress-closure premise. -/
theorem Reducible.arrow_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.arrow domainType codomainType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (codomainCR3 :
      ∀ {codomainRaw : RawTerm scope}
        (codomainTerm : Term context codomainType codomainRaw),
        RawTerm.IsNeutral codomainRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress codomainRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType codomainTerm) :
    Reducible (Ty.arrow domainType codomainType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro argumentRaw argumentTerm argumentIsReducible
  have appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app sourceRaw argumentRaw) :=
    RawTerm.app_neutral_isStronglyNormalizing
      sourceIsNeutral
      sourceIsSN
      (Reducible.isStronglyNormalizing argumentIsReducible)
  exact codomainCR3 (Term.app sourceTerm argumentTerm)
    (RawTerm.IsNeutral.app sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves appIsSN progressStep)

/-- **K12.20.U2 sigmaTy varShape arm**: variables are reducible at
dependent-pair type once the first-projection CR3 step is available.

The sigma candidate demands SN of the pair-shaped term, full Reducible
for `fst`, and SN for `snd`.  The raw `fst_var` / `snd_var` lemmas
provide the neutral projection SN closures; the full first projection
is delegated to the recursive CR3 hook for `firstType`. -/
theorem Reducible.sigmaTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.sigmaTy firstType secondType)
          (RawTerm.var position))
    (firstTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context firstType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType sourceTerm) :
    Reducible (Ty.sigmaTy firstType secondType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   firstTypeCR3 (Term.fst term)
     (RawTerm.IsNeutral.fst (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.fst_var_isStronglyNormalizing position) progressStep),
   RawTerm.snd_var_isStronglyNormalizing position⟩

/-- **K12.20.U2 sigmaTy CR3 arm**: a neutral dependent pair is
reducible at `Ty.sigmaTy firstType secondType` when every raw
progress reduct is SN and the first-projection CR3 hook is available.

This matches the asymmetric sigma candidate: SN for the pair itself,
full Reducible for `fst`, and SN for `snd`.  The second projection
remains SN-only by the current K12.7 closure shape. -/
theorem Reducible.sigmaTy_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.sigmaTy firstType secondType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (firstTypeCR3 :
      ∀ {firstRaw : RawTerm scope}
        (firstTerm : Term context firstType firstRaw),
        RawTerm.IsNeutral firstRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress firstRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType firstTerm) :
    Reducible (Ty.sigmaTy firstType secondType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_, ?_⟩
  · have fstIsSN :
        RawTerm.isStronglyNormalizing (RawTerm.fst sourceRaw) :=
      RawTerm.fst_neutral_isStronglyNormalizing
        sourceIsNeutral sourceIsSN
    exact firstTypeCR3 (Term.fst sourceTerm)
      (RawTerm.IsNeutral.fst sourceIsNeutral)
      (fun _targetRaw progressStep =>
        RawTerm.isStronglyNormalizing.step_preserves fstIsSN progressStep)
  · exact RawTerm.snd_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN

/-- **K12.20.U2 path varShape arm**: variables are reducible at cubical
path type once carrier CR3 is available.

The path candidate's eliminator closure returns full Reducible at the
carrier type.  `pathApp (var position) interval` is neutral, and the
existing raw helper supplies the progress-closure SN needed by the
carrier CR3 hook. -/
theorem Reducible.path_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          (RawTerm.var position))
    (carrierCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType sourceTerm) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent {_intervalRaw} intervalTerm intervalIsSN =>
     carrierCR3 (Term.pathApp modeIsUnivalent term intervalTerm)
       (RawTerm.IsNeutral.pathApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.pathApp_var_isStronglyNormalizing position intervalIsSN)
           progressStep)⟩

/-- **K12.20.U2 path CR3 arm**: a neutral path is reducible at
`Ty.path carrierType leftEndpoint rightEndpoint` when every raw
progress reduct is SN and the carrier CR3 hook is available.

The path candidate's output closure is full Reducible at the carrier
type.  The interval argument remains SN-only, matching the current
K12.12 closure where `Ty.interval` is a closed leaf rather than a
structural sub-Ty of the path type. -/
theorem Reducible.path_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (carrierCR3 :
      ∀ {carrierRaw : RawTerm scope}
        (carrierTerm : Term context carrierType carrierRaw),
        RawTerm.IsNeutral carrierRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress carrierRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType carrierTerm) :
    Reducible
      (Ty.path carrierType leftEndpoint rightEndpoint) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent intervalRaw intervalTerm intervalIsSN
  have pathAppIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp sourceRaw intervalRaw) :=
    RawTerm.pathApp_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN intervalIsSN
  exact carrierCR3
    (Term.pathApp modeIsUnivalent sourceTerm intervalTerm)
    (RawTerm.IsNeutral.pathApp sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves pathAppIsSN progressStep)

/-- **K12.20.U2 glue CR3 arm**: a neutral glued value is reducible at
`Ty.glue baseType boundaryWitness` when every raw progress reduct is
SN and the base-type CR3 hook is available.

The Glue candidate demands full Reducible at the base type for
`glueElim`.  Since `baseType` is a strict sub-Ty of the Glue type,
the proof delegates that projection result to the recursive CR3 hook;
`RawTerm.glueElim_neutral_isStronglyNormalizing` supplies the raw
progress-closure SN premise for the neutral projection. -/
theorem Reducible.glue_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.glue baseType boundaryWitness) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (baseTypeCR3 :
      ∀ {baseRaw : RawTerm scope}
        (baseTerm : Term context baseType baseRaw),
        RawTerm.IsNeutral baseRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress baseRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType baseTerm) :
    Reducible (Ty.glue baseType boundaryWitness) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent
  have glueElimIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.glueElim sourceRaw) :=
    RawTerm.glueElim_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact baseTypeCR3
    (Term.glueElim modeIsUnivalent sourceTerm)
    (RawTerm.IsNeutral.glueElim sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves glueElimIsSN progressStep)

/-- **K12.20.U2 glue varShape arm**: variables are reducible at Glue
type once base-type CR3 is available. -/
theorem Reducible.glue_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.glue baseType boundaryWitness)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.glue baseType boundaryWitness) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent =>
     baseTypeCR3 (Term.glueElim modeIsUnivalent term)
       (RawTerm.IsNeutral.glueElim (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.glueElim_var_isStronglyNormalizing position)
           progressStep)⟩

/-- **K12.20.U2 equiv varShape arm**: variables are reducible at
equivalence type once codomain CR3 is available. -/
theorem Reducible.equiv_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.var position))
    (carrierBCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierB sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierB sourceTerm) :
    Reducible (Ty.equiv carrierA carrierB) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     carrierBCR3 (Term.equivApp term argumentTerm)
       (RawTerm.IsNeutral.equivApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.equivApp_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 equiv CR3 arm**: a neutral equivalence is reducible at
`Ty.equiv carrierA carrierB` when every raw progress reduct is SN and
the codomain CR3 hook is available.

The equivalence candidate mirrors the arrow candidate: for every
reducible argument at `carrierA`, `equivApp neutral argument` is a
neutral term at `carrierB`.  The raw neutral application helper gives
the progress-closure SN premise, and the recursive `carrierB` CR3 hook
upgrades that neutral result to full Reducible. -/
theorem Reducible.equiv_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.equiv carrierA carrierB) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (carrierBCR3 :
      ∀ {carrierBRaw : RawTerm scope}
        (carrierBTerm : Term context carrierB carrierBRaw),
        RawTerm.IsNeutral carrierBRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress carrierBRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierB carrierBTerm) :
    Reducible (Ty.equiv carrierA carrierB) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro argumentRaw argumentTerm argumentIsReducible
  have equivAppIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.equivApp sourceRaw argumentRaw) :=
    RawTerm.equivApp_neutral_isStronglyNormalizing
      sourceIsNeutral
      sourceIsSN
      (Reducible.isStronglyNormalizing argumentIsReducible)
  exact carrierBCR3
    (Term.equivApp sourceTerm argumentTerm)
    (RawTerm.IsNeutral.equivApp sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        equivAppIsSN progressStep)

/-- **K12.20.U2 refine CR3 arm**: a neutral refined value is reducible
at `Ty.refine baseType predicate` when every raw progress reduct is SN
and the base-type CR3 hook is available.

The refinement candidate demands full Reducible at the base type for
`refineElim`.  The raw neutral helper supplies SN for the neutral
projection, and the recursive base-type CR3 hook upgrades that neutral
projection to the required Reducible witness. -/
theorem Reducible.refine_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.refine baseType predicate) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (baseTypeCR3 :
      ∀ {baseRaw : RawTerm scope}
        (baseTerm : Term context baseType baseRaw),
        RawTerm.IsNeutral baseRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress baseRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType baseTerm) :
    Reducible (Ty.refine baseType predicate) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have refineElimIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refineElim sourceRaw) :=
    RawTerm.refineElim_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact baseTypeCR3
    (Term.refineElim sourceTerm)
    (RawTerm.IsNeutral.refineElim sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        refineElimIsSN progressStep)

/-- **K12.20.U2 refine varShape arm**: variables are reducible at
refinement type once base-type CR3 is available. -/
theorem Reducible.refine_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.refine baseType predicate)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.refine baseType predicate) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   baseTypeCR3 (Term.refineElim term)
     (RawTerm.IsNeutral.refineElim (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.refineElim_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 record CR3 arm**: a neutral single-field record is
reducible at `Ty.record singleFieldType` when every raw progress reduct
is SN and the field-type CR3 hook is available.

The record candidate demands full Reducible for the projected field.
The raw neutral projection helper supplies SN for `recordProj`, and the
recursive field-type CR3 hook upgrades that neutral projection to the
required Reducible witness. -/
theorem Reducible.record_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.record singleFieldType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (singleFieldTypeCR3 :
      ∀ {fieldRaw : RawTerm scope}
        (fieldTerm : Term context singleFieldType fieldRaw),
        RawTerm.IsNeutral fieldRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress fieldRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible singleFieldType fieldTerm) :
    Reducible (Ty.record singleFieldType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have recordProjIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.recordProj sourceRaw) :=
    RawTerm.recordProj_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact singleFieldTypeCR3
    (Term.recordProj sourceTerm)
    (RawTerm.IsNeutral.recordProj sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        recordProjIsSN progressStep)

/-- **K12.20.U2 record varShape arm**: variables are reducible at
single-field record type once field-type CR3 is available. -/
theorem Reducible.record_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.record singleFieldType)
          (RawTerm.var position))
    (singleFieldTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context singleFieldType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible singleFieldType sourceTerm) :
    Reducible (Ty.record singleFieldType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   singleFieldTypeCR3 (Term.recordProj term)
     (RawTerm.IsNeutral.recordProj (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.recordProj_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 codata CR3 arm**: a neutral codata value is reducible
at `Ty.codata stateType outputType` when every raw progress reduct is
SN and the output-type CR3 hook is available.

The codata candidate demands full Reducible for the observed output.
The raw neutral observation helper supplies SN for `codataDest`, and
the recursive output-type CR3 hook upgrades that neutral observation to
the required Reducible witness. -/
theorem Reducible.codata_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.codata stateType outputType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (outputTypeCR3 :
      ∀ {outputRaw : RawTerm scope}
        (outputTerm : Term context outputType outputRaw),
        RawTerm.IsNeutral outputRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress outputRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible outputType outputTerm) :
    Reducible (Ty.codata stateType outputType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have codataDestIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.codataDest sourceRaw) :=
    RawTerm.codataDest_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact outputTypeCR3
    (Term.codataDest sourceTerm)
    (RawTerm.IsNeutral.codataDest sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        codataDestIsSN progressStep)

/-- **K12.20.U2 codata varShape arm**: variables are reducible at
codata type once output-type CR3 is available. -/
theorem Reducible.codata_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.codata stateType outputType)
          (RawTerm.var position))
    (outputTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context outputType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible outputType sourceTerm) :
    Reducible (Ty.codata stateType outputType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   outputTypeCR3 (Term.codataDest term)
     (RawTerm.IsNeutral.codataDest (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.codataDest_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 listType CR3 arm**: a neutral list is reducible at
`Ty.listType elementType` when every raw progress reduct is SN.

The K12.8 list candidate asks for SN of each eliminator result under
SN branches and the cons-application closure.  With a neutral scrutinee
the cons/nil ι arms cannot fire, so `RawTerm.listElim_neutral...`
closes from scrutinee SN plus branch SN; the cons-application premise is
reserved for canonical-cons fundamentals, not this neutral CR3 arm. -/
theorem Reducible.listType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.listType elementType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.listType elementType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _nilRaw _consRaw _nilBranch _consBranch
    nilIsSN consIsSN _consApplied
  exact RawTerm.listElim_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN nilIsSN consIsSN

/-- **K12.20.U2 listType varShape arm**: variables are reducible at
list type.

The strengthened K12.8 list closure includes SN for both eliminator
branches.  That is exactly what the raw neutral-list eliminator helper
needs for `listElim (var position) nilBranch consBranch`; the branch
application hypothesis remains available for canonical cons ι-cases but
is not needed for the stuck-variable case. -/
theorem Reducible.listType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.listType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.listType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_nilRaw} {_consRaw}
       _nilBranch _consBranch nilIsSN consIsSN _consApplied =>
     RawTerm.listElim_var_isStronglyNormalizing position nilIsSN consIsSN⟩

/-- **K12.20.U2 optionType CR3 arm**: a neutral option value is reducible
at `Ty.optionType elementType` when every raw progress reduct is SN.

The K12.8 option candidate asks for SN of each match result under SN
branches and the some-application closure.  With a neutral scrutinee the
none/some ι arms cannot fire, so the raw neutral option-match helper
closes from scrutinee SN plus branch SN. -/
theorem Reducible.optionType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.optionType elementType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.optionType elementType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _noneRaw _someRaw _noneBranch _someBranch
    noneIsSN someIsSN _someApplied
  exact RawTerm.optionMatch_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN noneIsSN someIsSN

/-- **K12.20.U2 optionType varShape arm**: variables are reducible at
option type.

The some-branch SN premise is load-bearing for neutral scrutinees:
`optionMatch` can reduce the some branch by congruence even when the
scrutinee is stuck at a variable. -/
theorem Reducible.optionType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.optionType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.optionType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_noneRaw} {_someRaw}
       _noneBranch _someBranch noneIsSN someIsSN _someApplied =>
     RawTerm.optionMatch_var_isStronglyNormalizing position noneIsSN someIsSN⟩

/-- **K12.20.U2 eitherType CR3 arm**: a neutral either value is
reducible at `Ty.eitherType leftType rightType` when every raw progress
reduct is SN.

The K12.8 either candidate asks for SN of each match result under SN
branches and both branch-application closures.  With a neutral scrutinee
the left/right ι arms cannot fire, so the raw neutral either-match
helper closes from scrutinee SN plus branch SN. -/
theorem Reducible.eitherType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.eitherType leftType rightType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.eitherType leftType rightType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _leftRaw _rightRaw _leftBranch _rightBranch
    leftIsSN rightIsSN _leftApplied _rightApplied
  exact RawTerm.eitherMatch_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN leftIsSN rightIsSN

/-- **K12.20.U2 eitherType varShape arm**: variables are reducible at
either type.

Both branches must be SN because `eitherMatch` reduces both branch
positions by congruence under a stuck variable scrutinee. -/
theorem Reducible.eitherType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.eitherType leftType rightType)
          (RawTerm.var position)) :
    Reducible (Ty.eitherType leftType rightType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_leftRaw} {_rightRaw}
       _leftBranch _rightBranch leftIsSN rightIsSN
       _leftApplied _rightApplied =>
     RawTerm.eitherMatch_var_isStronglyNormalizing position
       leftIsSN rightIsSN⟩

/-- **K12.20.AZ.1 piTy arm**: variables are reducible at the
dependent-Π type.  Closure: SN(var) + ∀ argTerm, Reducible
domainType argTerm → SN(Term.appPi (var) argTerm).  The second
clause reduces (via Reducible.isStronglyNormalizing CR1) to
SN(argRaw), then Stage 1's `RawTerm.app_var_isStronglyNormalizing`
closes — Term.appPi's raw form is `RawTerm.app functionRaw
argumentRaw`, matching app_var's signature. -/
theorem Reducible.piTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.piTy domainType codomainType)
          (RawTerm.var position)) :
    Reducible (Ty.piTy domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argRaw} _argTerm argIsReducible =>
     RawTerm.app_var_isStronglyNormalizing position
       (Reducible.isStronglyNormalizing argIsReducible)⟩

/-- **K12.20.U2 piTy CR3 arm**: a neutral dependent function is
reducible at `Ty.piTy domainType codomainType` when every raw
progress reduct is SN.

K12.6's current dependent-Π candidate is SN-output: it stores SN of
the function plus SN of every `Term.appPi` result under a reducible
domain argument.  Since `Term.appPi` erases to `RawTerm.app`, the raw
neutral-app SN helper closes the eliminator result directly. -/
theorem Reducible.piTy_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.piTy domainType codomainType) functionTerm := by
  have sourceIsSN : Term.isStronglyNormalizing functionTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      functionTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _argumentRaw argumentTerm argumentIsReducible
  exact RawTerm.app_neutral_isStronglyNormalizing
    sourceIsNeutral
    sourceIsSN
    (Reducible.isStronglyNormalizing argumentIsReducible)

/-- **K12.20.U2 id CR3 arm**: a neutral identity witness is reducible
at `Ty.id carrier leftEndpoint rightEndpoint` when every raw progress
reduct is SN.

The current K12.9 identity candidate is SN-output: it stores SN of the
witness and SN preservation through `idJ` for any SN base case.  With a
neutral witness, the refl-ι arm cannot fire, so the raw neutral J helper
closes from witness SN plus base-case SN. -/
theorem Reducible.id_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.id carrier leftEndpoint rightEndpoint) witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idJ_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.2 id arm**: variables are reducible at the HoTT
propositional identity type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.idJ baseCase var).  Stage 1's
`RawTerm.idJ_var_isStronglyNormalizing` discharges directly —
Term.idJ's raw form is `RawTerm.idJ baseRaw witnessRaw` with var
in the witness slot. -/
theorem Reducible.id_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.id carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.id carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.U2 oeq CR3 arm**: a neutral observational-equality
witness is reducible at `Ty.oeq carrier leftEndpoint rightEndpoint`
when every raw progress reduct is SN.

The current K12.10 observational-equality candidate is SN-output and
the raw `oeqJ` fragment is congruence-only, so the raw neutral helper
closes from witness SN plus base-case SN. -/
theorem Reducible.oeq_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.oeq carrier leftEndpoint rightEndpoint) witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.oeqJ_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.3 oeq arm**: variables are reducible at the
observational equality type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.oeqJ baseCase var).  Discharged by Stage 1's
`RawTerm.oeqJ_var_isStronglyNormalizing` (cong-only inversion;
oeq-ι deferred at raw layer).  Same shape as `id_of_varShape`. -/
theorem Reducible.oeq_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.oeq carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.oeqJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.U2 idStrict CR3 arm**: a neutral strict-identity
witness is reducible at `Ty.idStrict carrier leftEndpoint
rightEndpoint` when every raw progress reduct is SN.

The current K12.10 strict-identity candidate is SN-output.  Its
recursor carries a typed proof that the ambient mode is strict, but
the raw computation only sees `idStrictRec baseCase witness`.  With a
neutral witness, the strict-refl ι arm cannot fire, so the raw neutral
helper closes from witness SN plus base-case SN. -/
theorem Reducible.idStrict_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
        sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.idStrict carrier leftEndpoint rightEndpoint)
      witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _modeIsStrict _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idStrictRec_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.4 idStrict arm**: variables are reducible at the
strict identity type.  Closure: SN(var) + ∀ (modeIsStrict : mode =
Mode.strict) baseCase, SN(baseCase) → SN(Term.idStrictRec
modeIsStrict baseCase var).  Discharged by Stage 1's
`RawTerm.idStrictRec_var_isStronglyNormalizing`; the typed mode
witness is universally quantified and consumed silently — the raw
form drops it. -/
theorem Reducible.idStrict_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.idStrict carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun (_modeIsStrict : mode = Mode.strict)
       {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idStrictRec_var_isStronglyNormalizing position baseIsSN⟩


end LeanFX2
