import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ValidTypingRefinedMotive
    — the refined-motive total-bridge conclusion (SN-027, #655)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027, the only remaining gap to
SN-043 now that the ValidTyping fundamental theorem is proved) is an induction on `HasTypeDescPi`.  Its residual
difficulty is per-arm LEVEL coordination: the `conv` / `piElim` arms need their sub-derivations at a SHARED
`contextLevels` and at ALIGNED levels, which a bare `∃ subjectLevel` conclusion (one existential per derivation)
cannot force.

This file defines the REFINED MOTIVE that does force it: under a shared `contextLevels`, every subject is valid
at SOME single level, AND a TYPE-CODE-classified subject (classifier a universe code) is additionally
LEVEL-FLEXIBLE — valid at every positive level.  The level-flexible witnesses are produced by the formers
(`ValidTypingLevelFlexible.lean`'s `universeFormation_isLevelFlexible` / `pi`/`sigmaFormation_isLevelFlexible`);
this file wires them into the motive (`ofLevelFlexible`) and exposes the two projections the arms consume.

## What is proved

* `RefinedTotalBridgeConclusion` — the refined motive: single-level validity ∧ (universe-classifier ⟹
  level-flexible).
* `RefinedTotalBridgeConclusion.singleLevel` — projects the bare `∃ subjectLevel` validity (the total-bridge
  target's shape).
* `RefinedTotalBridgeConclusion.flexibleOfUniverseClassifier` — projects the level-flexibility of a
  universe-classified subject.
* `RefinedTotalBridgeConclusion.ofLevelFlexible` — **the producer**: a level-flexible type code satisfies the
  refined motive (single level at fuel 0; the all-level form via `universeCodeCell_inj`).  This is how the
  former arms (`*_isLevelFlexible`) feed the induction.

## Zero-axiom verification

The projections are field accesses; `ofLevelFlexible` is an anonymous constructor plus `universeCodeCell_inj`
(propext-free `cases` injectivity).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The refined-motive total-bridge conclusion.**  The subject is valid at SOME single level under its
classifier, AND if the classifier is a universe code the subject is a LEVEL-FLEXIBLE type code (valid at every
positive level).  The second conjunct lets the `conv` / `piElim` arms align levels — a type-code subject carries
its all-level form, which the bare `∃` shape cannot supply. -/
def RefinedTotalBridgeConclusion (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  (∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier) ∧
  (∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
    classifier = universeCodeCell levelExpr flag →
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag)

/-- Project the single-level validity (the bare existential the total-bridge target consumes). -/
theorem RefinedTotalBridgeConclusion.singleLevel {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (conclusion : RefinedTotalBridgeConclusion profile contextLevels context subject classifier) :
    ∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier :=
  conclusion.1

/-- Project the level-flexibility of a universe-classified (type-code) subject. -/
theorem RefinedTotalBridgeConclusion.flexibleOfUniverseClassifier {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (conclusion : RefinedTotalBridgeConclusion profile contextLevels context subject
      (universeCodeCell levelExpr flag)) :
    IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag :=
  conclusion.2 levelExpr flag rfl

/-- **A level-flexible type code satisfies the refined motive** (the producer side).  The formers
(`universeFormation` / `piFormation` / `sigmaFormation`, via `*_isLevelFlexible`) build
`IsLevelFlexibleTypeCode`, which gives both conjuncts: single-level validity by instantiating at fuel 0, and the
all-level form via universe-code injectivity (`universeCodeCell_inj`). -/
theorem RefinedTotalBridgeConclusion.ofLevelFlexible {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {context : TypingContext profile scope}
    {subject : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (flexible : IsLevelFlexibleTypeCode profile contextLevels context subject levelExpr flag) :
    RefinedTotalBridgeConclusion profile contextLevels context subject
      (universeCodeCell levelExpr flag) :=
  ⟨⟨0 + 1, flexible 0⟩, fun _le _fl eq => by
    obtain ⟨rfl, rfl⟩ := universeCodeCell_inj eq
    exact flexible⟩

end FX1Poly.Typed
