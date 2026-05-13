import LeanFX2.Reducibility.NeutralSNClosure

/-! # LeanFX2.Reducibility.TypedCR2Direct.StepPreservesDirect

K12.20.D — typed CR2 lift for each SN-direct `Reducible` arm:
unit / bool / nat / empty / interval / universe / tyVar / session /
effect / modal.  Each theorem takes a typed `Step` and lifts the
underlying raw-SN closure to the corresponding Reducible arm at the
target term.

## Root status

Layer 3 metatheory leaf.  First slice of `TypedCR2Direct`; consumed
by `TypedCR2Compound` (per-ctor cases) and by the unified
`Reducible.step_preserves` dispatcher in `TypedCR2Wrapup`. -/

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



end LeanFX2
