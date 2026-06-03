import FX1Poly.Typed.ValidTypingTermArms
import FX1Poly.Typed.LevelingBridge

/-! # FX1Poly/Typed/ValidTypingConvArm
    — the conversion arm of the refined-motive total bridge (SN-027, #673; ingredient of the assembly #662)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) inducts on `HasTypeDescPi`
against `RefinedTotalBridgeConclusion`.  Its five constructors are `ofFormation` / `conv` / `piIntro` / `piElim`
/ `genFormationPi`.  The `piIntro` / `piElim` / `genFormationPi` arms are shipped (`ValidTypingTermArms.lean`,
`ValidTypingFormerArms.lean`); this file ships the `conv` arm.

The conv arm is the PAYOFF of the refined motive's level-flexibility conjunct.  In `HasTypeDescPi.conv` the
subject is reclassified from `classifier` to a `reclassifier` typed at `universeCodeCell levelExpr flag`.  The
induction supplies:

* the subject valid at a single level (`subjectTyped`);
* the reclassifier — a universe-code-classified TYPE CODE — at EVERY level (`reclassifierAllLevel`), which is
  exactly the reclassifier's refined-motive conjunct-2 (its level-flexibility).

The conv rule needs the reclassifier at exactly `subjectLevel + 1`, which is the `subjectLevel`-instance of the
`∀ level` premise — so `validTypingBridgeConvFromAllLevelReclassifier` discharges conjunct-1 of the output.  The
output's conjunct-2 is vacuous WHEN the reclassifier is not itself a universe code (the reclassified subject is a
term, not a type) — `reclassifierNotUniverse`.  The type-output case (the reclassifier IS a universe code, so the
subject is a type being reclassified to a higher universe) is the env-routed neutral case, identical to
`piElim`'s type-family and `var`'s type-variable cases; it does not flow through this arm.

## What is proved

* `RefinedTotalBridgeConclusion.conv` — the conv arm: conjunct-1 by the all-level conv coordination, conjunct-2
  vacuous in the term-output case.

## Zero-axiom verification

`obtain` the reclassified `ValidTyping` from `validTypingBridgeConvFromAllLevelReclassifier`, then
`ofTermValidity` with `reclassifierNotUniverse`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The conversion arm of the refined motive (term-output case).**  Given the subject valid at one level, a
conversion of its classifier to a reclassifier supplied at EVERY level (the reclassifier's level-flexibility,
available because the reclassifier is a universe-code-classified type code), and a proof that the reclassifier is
NOT a universe code, the reclassified subject satisfies the refined motive: conjunct-1 from the all-level conv
coordination (`validTypingBridgeConvFromAllLevelReclassifier`, which picks the `subjectLevel` instance), conjunct-2
vacuous.  The type-output case (reclassifier a universe code) is the env-routed neutral case. -/
theorem RefinedTotalBridgeConclusion.conv {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierAllLevel : ∀ level : Nat,
      ValidTyping profile contextLevels (level + 1) context reclassifier
        (universeCodeCell levelExpr flag))
    (reclassifierNotUniverse : ∀ (le : LevelExpr) (fl : UniverseFlag),
      reclassifier ≠ universeCodeCell le fl) :
    RefinedTotalBridgeConclusion profile contextLevels context subject reclassifier := by
  obtain ⟨resultLevel, reclassifiedTyped⟩ :=
    validTypingBridgeConvFromAllLevelReclassifier contextLevels subjectLevel
      subjectTyped converts reclassifierAllLevel
  exact RefinedTotalBridgeConclusion.ofTermValidity reclassifiedTyped reclassifierNotUniverse

end FX1Poly.Typed
