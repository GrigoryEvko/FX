import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.LevelingBridge

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

end FX1Poly.Typed
