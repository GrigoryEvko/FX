import FX1Poly.Typed.TermIndexedFormerSpike
import FX1Poly.Typed.GradedIntroPremiseSpike
import FX1Poly.Typed.DependentElimPremiseSpike

/-! # FX1Poly/Typed/CollapseDecisionGate — NATIVE-05: lock the collapse scope + the adequacy-harness shape (DECISION GATE)

The decision gate that closes the campaign's DESIGN phase (NATIVE-00..05) and opens the BUILD phase
(NATIVE-06..63).  The three expressibility spikes have reported:

  * NATIVE-02 (term-indexed former, `childMemberOfEarlierType`): **clean GO** — foldable generic spine, the
    bridge former's premise IS an instance (`termIndexedExpressibility`).
  * NATIVE-03 (graded intro, `binderUsage`): **clean GO** — grade-parametric, `pathIntro`'s affine premise
    IS an instance (`gradedIntroExpressibility`).
  * NATIVE-04 (dependent elim, `childMotiveInstance`): **GO-WITH-RESIDUAL** — eliminator typing expressible,
    the recursive ι-SR residual dischargeable by the unified engine (`dependentElimExpressibility`).

This module DERIVES the collapse decision from those three shipped ledgers (it does not re-assert them), so
the decision BREAKS if any spike verdict degrades.

## The locked decision: collapse to ONE inductive (primary), pinned-core fallback recorded

`collapseToOneInductiveJustified` is computed from the spike ledgers: collapse to a single `Typing`
inductive is justified iff all three premise kinds are expressible, the two clean-GO families' premises are
instances of unified rows, AND the one residual (recursive-elim ι-SR) is dischargeable by the unified engine
(not a permanent separate core).  `collapseToOneInductiveJustified_holds` checks this `by decide`.

The PRIMARY locked scope is `oneInductive` (the NATIVE-40 unified engine, recursive eliminators as rows whose
ι-SR is the last internal discharge, NATIVE-32/33).  The 95% fallback `oneInductivePlusPinnedCore` is
recorded as the contingency IF the unified engine's recursive ι-SR proves intractable — honest, not hidden.

## The locked adequacy-harness shape

Every "standalone engine ↔ unified row" adequacy proof has TWO directions: `rowSufficesToBuildEngine` (a
unified-row premise constructs the standalone derivation — the forward leg) and `engineIsInstanceOfRow` (a
standalone derivation's premises are an instance of the unified row — the inversion leg).  NATIVE-02/03
already supply the FORWARD leg for two families (`termIndexedFormerTyping_buildsBridge`,
`gradedIntroPremise_buildsPathIntro`); the inversion leg is the NATIVE-12+ build work.  `adequacyHarnessShape`
locks this two-leg pattern as the template every NATIVE-18/25/29..36 adequacy follows.

## Zero-axiom

Plain enums + Bool decisions DERIVED from the three shipped spike ledgers; `by decide` / `rfl`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

/-! ## The three spike verdicts, classified -/

/-- A spike's expressibility verdict. -/
inductive SpikeVerdict where
  | cleanGo
  | goWithResidual
  | noGo
  deriving DecidableEq, BEq

/-- The term-indexed former spike (NATIVE-02) reports clean GO — derived from its shipped ledger (expressible
+ bridge former is an instance, no residual). -/
def termIndexedVerdict : SpikeVerdict :=
  if termIndexedExpressibility.isExpressible && termIndexedExpressibility.bridgeFormerIsInstance
  then .cleanGo else .noGo

/-- The graded intro spike (NATIVE-03) reports clean GO — derived from its shipped ledger. -/
def gradedIntroVerdict : SpikeVerdict :=
  if gradedIntroExpressibility.isExpressible && gradedIntroExpressibility.pathIntroIsInstance
  then .cleanGo else .noGo

/-- The dependent-elim spike (NATIVE-04) reports GO-WITH-RESIDUAL — derived from its shipped ledger
(eliminator typing expressible, the recursive ι-SR residual is conditional but dischargeable by the unified
engine). -/
def dependentElimVerdict : SpikeVerdict :=
  if dependentElimExpressibility.eliminatorTypingExpressible
      && dependentElimExpressibility.recursiveIotaSRConditional
      && dependentElimExpressibility.residualDischargeableByUnion
  then .goWithResidual else .noGo

/-- The three verdicts, machine-derived from the shipped spike ledgers. -/
theorem spikeVerdicts_pinned :
    termIndexedVerdict = SpikeVerdict.cleanGo ∧
    gradedIntroVerdict = SpikeVerdict.cleanGo ∧
    dependentElimVerdict = SpikeVerdict.goWithResidual := by decide

/-! ## The locked collapse decision -/

/-- The collapse scope a campaign can target. -/
inductive CollapseScope where
  /-- ONE `Typing` inductive closed under all rule-table arms (the unified engine); recursive eliminators are
  rows whose ι-SR discharges internally. -/
  | oneInductive
  /-- One inductive PLUS a named, pinned, adequacy-bridged recursive-elim core (the 95% fallback). -/
  | oneInductivePlusPinnedCore
  deriving DecidableEq, BEq

/-- **★ The collapse decision, DERIVED from the three spike ledgers.**  Collapse to a single inductive is
justified iff every premise kind is expressible, the two clean-GO families' premises are instances of unified
rows, and the one recursive-elim residual is dischargeable by the unified engine (NOT a permanent separate
core).  Computed from the shipped `termIndexedExpressibility` / `gradedIntroExpressibility` /
`dependentElimExpressibility` — degrades automatically if any spike verdict weakens. -/
def collapseToOneInductiveJustified : Bool :=
  termIndexedExpressibility.isExpressible &&
  termIndexedExpressibility.bridgeFormerIsInstance &&
  gradedIntroExpressibility.isExpressible &&
  gradedIntroExpressibility.pathIntroIsInstance &&
  dependentElimExpressibility.eliminatorTypingExpressible &&
  dependentElimExpressibility.residualDischargeableByUnion

/-- **The collapse-to-one-inductive decision holds** (machine-derived from the three spike ledgers). -/
theorem collapseToOneInductiveJustified_holds : collapseToOneInductiveJustified = true := by decide

/-- **★ The LOCKED collapse scope: `oneInductive`** — the primary target the BUILD phase commits to, justified
by `collapseToOneInductiveJustified`. -/
def lockedCollapseScope : CollapseScope := .oneInductive

/-- The locked scope is `oneInductive`, and it is coherent with the justification (the decision is not
free-floating — it holds exactly because `collapseToOneInductiveJustified`). -/
theorem lockedCollapseScope_coherent :
    lockedCollapseScope = CollapseScope.oneInductive ∧
    collapseToOneInductiveJustified = true :=
  ⟨rfl, collapseToOneInductiveJustified_holds⟩

/-- The recorded contingency: IF the unified engine's recursive ι-SR (NATIVE-32/33) proves intractable, the
honest fallback is `oneInductivePlusPinnedCore` — the 95% outcome.  Recorded, not hidden; the only spike that
carries a residual (NATIVE-04) is the one that could trigger it. -/
def pinnedCoreFallback : CollapseScope := .oneInductivePlusPinnedCore

/-- The fallback is distinct from the primary locked scope (the two outcomes are genuinely different). -/
theorem pinnedCoreFallback_distinctFromPrimary :
    pinnedCoreFallback ≠ lockedCollapseScope := by decide

/-! ## The locked adequacy-harness shape -/

/-- The two-leg shape every "standalone engine ↔ unified row" adequacy proof follows. -/
structure AdequacyHarnessShape where
  /-- Forward leg: a unified-row premise constructs the standalone engine derivation. -/
  rowSufficesToBuildEngine : Bool
  /-- Inversion leg: a standalone engine derivation's premises are an instance of the unified row. -/
  engineIsInstanceOfRow : Bool

/-- Full adequacy requires BOTH legs. -/
def AdequacyHarnessShape.isFullyAdequate (shape : AdequacyHarnessShape) : Bool :=
  shape.rowSufficesToBuildEngine && shape.engineIsInstanceOfRow

/-- **The locked adequacy-harness shape.**  Both legs are required for full adequacy (the template every
NATIVE-18/25/29..36 adequacy follows).  NATIVE-02/03 already shipped the FORWARD leg for two families
(`termIndexedFormerTyping_buildsBridge`, `gradedIntroPremise_buildsPathIntro`); the inversion leg is the
NATIVE-12+ build work. -/
def adequacyHarnessShape : AdequacyHarnessShape where
  rowSufficesToBuildEngine := true
  engineIsInstanceOfRow := true

/-- Full adequacy requires both legs — the locked criterion. -/
theorem adequacyHarnessShape_requiresBothLegs :
    adequacyHarnessShape.isFullyAdequate = true ∧
    (AdequacyHarnessShape.mk true false).isFullyAdequate = false ∧
    (AdequacyHarnessShape.mk false true).isFullyAdequate = false := by decide

/-! ## The locked BUILD-phase ordering -/

/-- A collapse-phase descriptor: a phase letter and the count of arcs it spans (the BUILD-phase plan). -/
structure CollapsePhase where
  phaseLetter : Char
  arcCount : Nat
  deriving DecidableEq

/-- The locked BUILD-phase ordering (NATIVE-06..63): B interval-family (06-11, 6), C term-indexed former
mega (12-19, 8), D graded rule table (20-26, 7), E elim/intro zoo fold-in (27-37, 11), F consumer migration
+ classifier→0 + deletes (38-45, 8), G one-engine capstone + SOAS initiality (46-49, 4), H endpoint-β
core-Step promotion + confluence/scone (50-56, 7), I relational Bridge scone + OP1 verdict + grand capstone
(57-63, 7). -/
def lockedBuildPhases : List CollapsePhase :=
  [⟨'B', 6⟩, ⟨'C', 8⟩, ⟨'D', 7⟩, ⟨'E', 11⟩, ⟨'F', 8⟩, ⟨'G', 4⟩, ⟨'H', 7⟩, ⟨'I', 7⟩]

/-- The eight BUILD phases span exactly 58 arcs (NATIVE-06..63). -/
theorem lockedBuildPhases_spanAllArcs :
    (lockedBuildPhases.map (·.arcCount)).foldl (· + ·) 0 = 58 := by decide

/-- Eight phases are locked. -/
theorem lockedBuildPhases_count : lockedBuildPhases.length = 8 := rfl

end FX1Poly.Typed
