import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.LevelingBridge
import FX1Poly.Typed.ConsistentStratification

/-! # FX1Poly/Typed/ValidTypingConvArm
    — the conv-VARIABLE arm of the total-bridge motive (SN-027; ingredient of the assembly #662)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) inducts on `HasTypeDescPi`
against `TotalBridgeConclusion` (`ValidTypingRefinedMotive.lean`).  The `conv` arm splits on whether the
reclassifier the subject was converted to is a context VARIABLE:

* a NON-VARIABLE reclassifier (universe code / Π-Σ-gen former) is LEVEL-FLEXIBLE — handled by
  `TotalBridgeConclusion.convNonVariableReclassifier` (`ValidTypingRefinedMotive.lean`);
* a VARIABLE reclassifier `variableCell index` is PINNED to `contextLevels index` by `ValidTyping.var` — handled
  by THIS file's `convVariableReclassifier`, which consumes the leveling equation
  `contextLevels index = subjectLevel + 1` (the residual the assembly's level synthesis supplies).

`RawTerm.isVariableOrNot` routes between the two in the assembly; together they discharge the whole `conv` arm
modulo the leveling equation.

## What is proved

* `TotalBridgeConclusion.convVariableReclassifier` — the variable-reclassifier conv arm: conjunct-1 via
  `validTypingBridgeConvPinnedReclassifier` (consuming the leveling equation), conjunct-2 vacuous (a variable is
  never convertible to a universe code, `variableCell_not_conv_universeCodeCell`).
* `TotalBridgeConclusion.convBoundVariableReclassifier` — the freshly-bound `⟨0,_⟩` base case (equation `rfl`).
* `TotalBridgeConclusion.convVariableReclassifierOfStratified` — the deeper tower step: a subject `var termIndex`
  whose looked-up type IS the reclassifier type variable, with the leveling equation discharged by the
  `ConsistentStratification` invariant (the assembly's synthesized-level payoff for the `x : A : Type` tower).

## Zero-axiom verification

`validTypingBridgeConvPinnedReclassifier` + `variableCell_not_conv_universeCodeCell` + `absurd`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The conv-VARIABLE arm of the motive.**  Twin of `convNonVariableReclassifier` for the case where the
reclassifier the subject was converted to is a context VARIABLE `variableCell index` whose looked-up type is a
universe code.  Conjunct-1: the reclassified subject is valid at `subjectLevel` via
`validTypingBridgeConvPinnedReclassifier`, which consumes the leveling equation
`contextLevels index = subjectLevel + 1` — the single residual the assembly's leveling discipline supplies for the
variable case.  Conjunct-2 is vacuous: the convertibility guard `Conv (variableCell index) (universeCodeCell …)` is
unsatisfiable (`variableCell_not_conv_universeCodeCell`), so the level-flexibility obligation has no hypotheses to
discharge.  Routed alongside `convNonVariableReclassifier` by `RawTerm.isVariableOrNot`; together they COMPLETE the
conv arm of the totalBridge modulo the leveling equation. -/
theorem TotalBridgeConclusion.convVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat) {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {index : Fin scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectValid : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier (variableCell index))
    (reclassifierIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (levelMatch : contextLevels index = subjectLevel + 1) :
    TotalBridgeConclusion profile contextLevels context subject (variableCell index) := by
  refine ⟨⟨subjectLevel, validTypingBridgeConvPinnedReclassifier contextLevels subjectLevel
    subjectValid converts reclassifierIsUniverse levelMatch⟩, ?_⟩
  intro outLevel outFlag reclassifierConvUniverse _subjectNotVariable
  exact absurd reclassifierConvUniverse (variableCell_not_conv_universeCodeCell index outLevel outFlag)

/-- **The conv-variable arm for a FRESHLY-BOUND type variable — the base case of the level synthesis.**  When the
reclassifier is the de-Bruijn-`⟨0,_⟩` variable just introduced by a binder (its context level vector has the form
`levelCons (predLevel + 1) tailLevels`), the leveling equation `contextLevels ⟨0,_⟩ = subjectLevel + 1` that
`convVariableReclassifier` consumes is discharged BY COMPUTATION: `levelCons`'s `⟨0,_⟩` branch reduces to the head
`predLevel + 1`, so taking the subject at `subjectLevel = predLevel` makes the equation `rfl`.  This is where the
totalBridge-assembly's level synthesis bottoms out — a binder PINS its variable's level, so the conv-to-bound-
type-variable coordination needs no hypothesis.  (The general arm `convVariableReclassifier` still carries the
equation for DEEPER variables, whose level the synthesis threads inductively through the `levelCons` tail.) -/
theorem TotalBridgeConclusion.convBoundVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (tailLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile (scope + 1)}
    {subject classifier : RawTerm (scope + 1)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (isLt : 0 < scope + 1)
    (subjectValid : ValidTyping profile (levelCons (predLevel + 1) tailLevels) predLevel context
      subject classifier)
    (converts : Conv classifier (variableCell ⟨0, isLt⟩))
    (reclassifierIsUniverse : context.lookup ⟨0, isLt⟩ = universeCodeCell levelExpr flag) :
    TotalBridgeConclusion profile (levelCons (predLevel + 1) tailLevels) context
      subject (variableCell ⟨0, isLt⟩) :=
  TotalBridgeConclusion.convVariableReclassifier (levelCons (predLevel + 1) tailLevels) predLevel
    subjectValid converts reclassifierIsUniverse rfl

/-- **The conv-variable arm for a DEEPER type-tower variable — the leveling equation discharged by the
stratification invariant.**  Where `convBoundVariableReclassifier` handles the freshly-bound `⟨0,_⟩` variable
(equation `rfl` by `levelCons`), this handles the general tower step: a SUBJECT that is itself a term variable
`var termIndex` whose looked-up type IS the reclassifier type variable (`lookup termIndex = variableCell index`,
e.g. `x : A` with `x = termIndex`, `A = index`).  The subject is typed at `contextLevels termIndex` by
`ValidTyping.var` (its classifier `lookup termIndex` rewritten to `variableCell index`), and the leveling
equation `contextLevels index = contextLevels termIndex + 1` that `convVariableReclassifier` consumes is
exactly the `ConsistentStratification` invariant at this edge.  This is the arm where the assembly's synthesized
level vector pays off: the tower `x : A : Type` is leveled `A ↦ k+1, x ↦ k`, and consistency reads that `+1` off
the looked-up type-variable edge — no per-derivation hypothesis, just the static stratification. -/
theorem TotalBridgeConclusion.convVariableReclassifierOfStratified {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {termIndex index : Fin scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTypeIsReclassifier : context.lookup termIndex = variableCell index)
    (reclassifierIsUniverse : context.lookup index = universeCodeCell levelExpr flag) :
    TotalBridgeConclusion profile contextLevels context
      (variableCell termIndex) (variableCell index) := by
  refine TotalBridgeConclusion.convVariableReclassifier contextLevels (contextLevels termIndex)
    (classifier := variableCell index) ?subjectValid ?converts reclassifierIsUniverse
    (consistent termIndex index subjectTypeIsReclassifier)
  case subjectValid =>
    rw [← subjectTypeIsReclassifier]
    exact ValidTyping.var contextLevels context termIndex
  case converts =>
    exact Conv.refl _

end FX1Poly.Typed
