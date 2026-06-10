import FX1Poly.Typed.TypeDirectedUnitReadback

/-! # FX1Poly/Typed/UnitReadbackArgumentBoundary
   — ★ the 6th boundary: classifiers do not flow into APPLICATION ARGUMENTS (#481 brick-3 verdict)

The mandated pre-construction analysis for brick 3, machine-checked — TWO verdicts:

**Σ is BLOCKED (recorded, not re-proved)**: mirroring the Π η-expansion at Σ would emit
`pair (fst t) (snd t)` — but `HasTypeDescPi.pairCellHasNoTyping` (the ULC-1 gap module) shows
the grown engine types NO pair cell, so `DefEqUnitEta.ofBetaEtaConv`'s both-endpoints-typed
presupposition is unsatisfiable for the expansion.  Σ-η waits on a grown pair-intro rule
(#361 re-gated on the engine, not on the readback).

**The 6th boundary (THIS module)**: in `(f : Π(_:Π(_:Unit).Unit).Type@0, g : Π(_:Unit).Unit)`,
the applications `app(f, g)` and `app(f, λx.((weaken g) x))` are congruently unit-η-equal —
one `congGen` descent, the arguments related by the η pair (`ofBetaEtaConv` + `etaLam`).  But
at the OPAQUE result classifier `Type@0` the shipped readback degrades to the deep collapse at
EVERY fuel (`Type@0` is neither `unitTypeCell` nor a Π code), and the collapses are distinct
βη-normal forms that never join: the η-redex argument sits INSIDE the application, where root-η
cannot fire and no classifier reaches it.

## The verdict — the readback needs its NEUTRAL-SPINE mode

The classifier flows top-down through λ-binders (brick 2) but STOPS at application nodes: the
argument's classifier is the DOMAIN of the function's type, which the readback never computes.
Recovering it is spine synthesis — `detectSpineType` (shipped, unconditionally sound) at the
function position.  Architecturally this is the missing half of the classic NbE quote pair:
`quoteNormal` (type-directed, η-expands — shipped as `readbackAtClassifier`) mutually with
`quoteNeutral` (spine-directed, synthesizes — the next brick): at an application, keep the
spine head, read back each ARGUMENT at its synthesized domain.

## Zero-axiom verification

The typings are `piElim`/`var`/`etaExpansionPreservesTypingGrown` applications over a wf context
built from `hasTypeDesc_piFormation_viaGenArm` + `universeFormation`; the readback degradations
are `rfl` per fuel shape; non-joinability is the `reduceOnceBetaEta_complete`-at-`rfl` leaf
discipline; the inequality is `decide` on concrete cells via the `show`-coercion (free-profile
guard).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The context `(f : Π(_:Π(_:Unit).Unit).Type@0, g : Π(_:Unit).Unit)` — a higher-order function
with an OPAQUE result type, so the application classifier drives no readback arm. -/
def appArgumentContext (profile : PolyProfile) : TypingContext profile 2 :=
  ((TypingContext.empty : TypingContext profile 0).cons
    (piTyCodeCell (piTyCodeCell unitTypeCell unitTypeCell)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard))).cons
    (piTyCodeCell unitTypeCell unitTypeCell)

/-- The application context is formation-well-formed — nested Π formation via the generic arm,
with `universeFormation` typing the opaque codomain. -/
theorem appArgumentContextWellFormed (profile : PolyProfile) :
    WfContextDesc (appArgumentContext profile) :=
  WfContextDesc.cons
    (WfContextDesc.cons WfContextDesc.emptyIsWellFormed
      ⟨_, _, hasTypeDesc_piFormation_viaGenArm TypingContext.empty
        (piTyCodeCell unitTypeCell unitTypeCell)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (LevelExpr.lmax LevelExpr.lzero LevelExpr.lzero) LevelExpr.lzero.lsucc
        UniverseFlag.standard
        (hasTypeDesc_piFormation_viaGenArm TypingContext.empty
          unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
          (unitTypeCellFormationTyped TypingContext.empty)
          (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell)))
        (HasTypeDesc.universeFormation
          (TypingContext.empty.cons (piTyCodeCell unitTypeCell unitTypeCell))
          LevelExpr.lzero UniverseFlag.standard)⟩)
    ⟨_, _, hasTypeDesc_piFormation_viaGenArm
      (TypingContext.empty.cons
        (piTyCodeCell (piTyCodeCell unitTypeCell unitTypeCell)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard)))
      unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
      (unitTypeCellFormationTyped _)
      (unitTypeCellFormationTyped _)⟩

/-- The left application `app(f, g)` — the function variable applied to the BARE function
argument. -/
def appliedToBareArgument : RawTerm 2 :=
  appCell (variableCell ⟨1, Nat.le.refl⟩) (variableCell ⟨0, Nat.le.step Nat.le.refl⟩)

/-- The right application `app(f, λx.((weaken g) x))` — the same function applied to the
η-EXPANSION of the argument. -/
def appliedToEtaExpandedArgument : RawTerm 2 :=
  appCell (variableCell ⟨1, Nat.le.refl⟩)
    (RawTerm.etaLamSource unitTypeCell (variableCell ⟨0, Nat.le.step Nat.le.refl⟩))

/-- Both applications are grown-typed at the opaque result `Type@0` — `piElim` of `f`, the right
side's argument via `etaExpansionPreservesTypingGrown`. -/
theorem appliedToBareArgumentTyped (profile : PolyProfile) :
    HasTypeDescPi profile (appArgumentContext profile) appliedToBareArgument
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (appArgumentContext profile) ⟨1, Nat.le.refl⟩))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (appArgumentContext profile) ⟨0, Nat.le.step Nat.le.refl⟩))

theorem appliedToEtaExpandedArgumentTyped (profile : PolyProfile) :
    HasTypeDescPi profile (appArgumentContext profile) appliedToEtaExpandedArgument
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (appArgumentContext profile) ⟨1, Nat.le.refl⟩))
    (HasTypeDescPi.etaExpansionPreservesTypingGrown
      (WfContextDescPi.ofWfContextDesc (appArgumentContextWellFormed profile))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var (appArgumentContext profile) ⟨0, Nat.le.step Nat.le.refl⟩)))

/-- **The applications are congruently unit-η-equal**: one `congGen` descent through the
application — the function is SHARED, the arguments are the η pair (`ofBetaEtaConv` over the
one-step `etaLam` contraction, both endpoints typed). -/
theorem appArgumentPair_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (appArgumentContext profile)
      appliedToBareArgument appliedToEtaExpandedArgument :=
  DefEqUnitEtaCong.congGen (generator := Generator.gen_app) ()
    (.consEqualZero
      (.consZero
        (.ofDefEq (.ofBetaEtaConv (appArgumentContextWellFormed profile)
          (HasTypeDescPi.ofFormation
            (HasTypeDesc.var (appArgumentContext profile) ⟨0, Nat.le.step Nat.le.refl⟩))
          (HasTypeDescPi.etaExpansionPreservesTypingGrown
            (WfContextDescPi.ofWfContextDesc (appArgumentContextWellFormed profile))
            (HasTypeDescPi.ofFormation
              (HasTypeDesc.var (appArgumentContext profile) ⟨0, Nat.le.step Nat.le.refl⟩)))
          ⟨variableCell ⟨0, Nat.le.step Nat.le.refl⟩,
            Step.betaEtaStar.refl _,
            Step.betaEtaStar.trans
              (Or.inr (Step.eta.etaLam unitTypeCell
                (variableCell ⟨0, Nat.le.step Nat.le.refl⟩)))
              (Step.betaEtaStar.refl _)⟩))
        .nil))

/-- The deep collapse of the η-expanded application: the bound variable INSIDE the η-expansion is
unit-typed under the binder, so the collapse rewrites it — but the η-redex shape survives. -/
def collapsedEtaExpandedApplication : RawTerm 2 :=
  appCell (variableCell ⟨1, Nat.le.refl⟩)
    (lamCell unitTypeCell
      (appCell (variableCell ⟨1, Nat.le.step Nat.le.refl⟩) unitCell))

theorem deepCollapse_appliedToEtaExpanded (profile : PolyProfile) :
    collapseUnitVariablesDeep (appArgumentContext profile) appliedToEtaExpandedArgument
      = collapsedEtaExpandedApplication := rfl

theorem deepCollapse_appliedToBare (profile : PolyProfile) :
    collapseUnitVariablesDeep (appArgumentContext profile) appliedToBareArgument
      = appliedToBareArgument := rfl

/-- **The collapsed applications never βη-join**: both are βη-normal (application heads are
variables; the inner λ's body applies to `unitCell`, not `var₀`, so root η cannot fire anywhere)
and they are distinct. -/
theorem collapsedAppArgumentPair_notBetaEtaConv :
    ¬ BetaEtaConv appliedToBareArgument collapsedEtaExpandedApplication := by
  intro convertible
  obtain ⟨commonTerm, bareChain, expandedChain⟩ := convertible
  have bareEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        appliedToBareArgument.reduceOnceBetaEta = none))
      bareChain
  have expandedEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        collapsedEtaExpandedApplication.reduceOnceBetaEta = none))
      expandedChain
  exact absurd (bareEq.trans expandedEq.symm) (by decide)

/-- **★ The 6th boundary — every binder-fenced/collapse-mode procedure is incomplete at
APPLICATION-ARGUMENT positions**: a congruently unit-η-equal pair (the η pair, injected at an
argument position under an OPAQUE result classifier) whose DEEP COLLAPSES are distinct βη-normal
forms that never join — root-η cannot reach an η-redex inside an application, and no bottom-up
traversal supplies the argument's classifier.  This boundary FORCED the neutral-spine arm. -/
theorem deepCollapseMode_isIncompleteAtApplicationArguments (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 2),
      DefEqUnitEtaCong profile (appArgumentContext profile) leftTerm rightTerm ∧
      collapseUnitVariablesDeep (appArgumentContext profile) leftTerm
        ≠ collapseUnitVariablesDeep (appArgumentContext profile) rightTerm ∧
      ¬ BetaEtaConv
          (collapseUnitVariablesDeep (appArgumentContext profile) leftTerm)
          (collapseUnitVariablesDeep (appArgumentContext profile) rightTerm) :=
  ⟨appliedToBareArgument, appliedToEtaExpandedArgument,
    appArgumentPair_congruentlyEqual profile,
    fun collapsesEqual =>
      absurd
        (show appliedToBareArgument = collapsedEtaExpandedApplication from collapsesEqual)
        (by decide),
    collapsedAppArgumentPair_notBetaEtaConv⟩

/-- **★ THE 6TH-BOUNDARY PAIR, DECIDED — the neutral-spine arm resolves it**: the readback now
recovers the argument's classifier from the head variable's looked-up Π code, so BOTH sides read
back to `app(f, λ(x:Unit).unitCell)` — the η-long argument form — and `ofReadbackEqual` closes
the pair at `rfl`.  The spine arm composes with η-expansion (left: the bare `g` η-expands at the
recovered `Π(_:Unit).Unit`) and with the unit collapse (the expansion body at the codomain). -/
theorem appArgumentPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (appArgumentContext profile)
      appliedToBareArgument appliedToEtaExpandedArgument :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 3) (rightFuel := 3)
    (appArgumentContextWellFormed profile)
    (appliedToBareArgumentTyped profile)
    (appliedToEtaExpandedArgumentTyped profile)
    (HasTypeDesc.universeFormation (appArgumentContext profile)
      LevelExpr.lzero UniverseFlag.standard)
    rfl

/-- **The spine arm computes the η-long argument form** — the recovered classifier drives the
argument all the way to `λ(x:Unit).unitCell`, by `rfl` (fuel 4: one level pays the delegation
into the mutual spine readback). -/
theorem readback_recoversArgumentClassifier (profile : PolyProfile) :
    readbackAtClassifier 4 (appArgumentContext profile)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) appliedToBareArgument
      = appCell (variableCell ⟨1, Nat.le.refl⟩) (lamCell unitTypeCell unitCell) := rfl

end FX1Poly.Typed
