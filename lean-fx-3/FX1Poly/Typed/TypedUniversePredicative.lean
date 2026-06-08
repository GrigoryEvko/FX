import FX1Poly.Typed.TypedUniverseNoTop

/-! # FX1Poly/Typed/TypedUniversePredicative — universe classification IS the successor relation; the engine is predicative

The universe arc so far: `Type@n : Type@(n+1)` (the tower, #1010), the classifier is exactly the successor with
no conv slack and there is no top (#1011), the relation is irreflexive (#941) and well-founded (#945).  This file
delivers the CAPSTONE — the full BOTH-DIRECTIONS characterization, and its design-critical consequence
(predicativity / non-cumulativity):

  * **`universeClassificationCharacterization` (★)** — universe-code classification is EXACTLY the successor
    relation: `HasTypeDescPi Γ (Type@m, sf) (Type@n, cf) ↔ (n = m.lsucc ∧ cf = sf)`.  The forward direction is
    `universeCodeClassifierIsSuccessor` (#1011); the backward direction is `ofFormation ∘ universeFormation`
    (the formation rule IS the only way a universe code classifies into another).  So `_:_` restricted to
    universe codes is a decidable, exact copy of `(ℕ, successor)`.

  * **`universeClassificationNotTransitive`** — predicativity exhibited as NON-TRANSITIVITY: `Type@0 : Type@1`
    and `Type@1 : Type@2`, but NOT `Type@0 : Type@2`.  A cumulative or impredicative hierarchy would make the
    relation transitive (or reflexive); FX's does neither.

  * **`universeNotCumulativeBySkip` (★)** — predicativity in GENERAL: for every level `e` and flag, there is no
    typing `Type@e : Type@(e+2)`.  The engine NEVER lets a universe code skip a level — it mechanizes FX §1.1's
    commitment to a strictly predicative hierarchy.  Via the exact characterization plus the level-algebra
    predicativity guard `LevelExpr.ne_lsucc_self` (`e.lsucc ≠ e.lsucc.lsucc`).

Together with the prior universe results, the universe-code classification relation is now COMPLETELY
characterized: it is the successor relation on `ℕ` — irreflexive (#941), non-transitive + non-cumulative (here),
rigid / functional (#1011), well-founded (#945), top-less (#1011), and inhabited at every level (#1010).  Every
property that distinguishes a strictly-predicative tower from an impredicative `Type : Type` is mechanized,
zero-axiom.

## Zero-axiom verification

`universeClassificationCharacterization` is `constructor` + the shipped forward inversion (#1011) + a `subst`/
`ofFormation`/`universeFormation` backward arm.  `universeClassificationNotTransitive` reuses
`universeLevelTower_hasTypeDescPi` (#1010) for the two positive conjuncts and the exact characterization +
`universeLevelOfNat_injective` + `decide ¬(2=1)` for the refutation.  `universeNotCumulativeBySkip` is the exact
characterization composed with `LevelExpr.ne_lsucc_self` (the predicativity guard from `LevelExpr.lean`).  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- ★ **Universe-code classification is exactly the successor relation.**  A universe code is typed at another
universe code iff the classifier's level is the subject's successor and the flags agree — both directions.  The
forward arm is the rigidity inversion (`universeCodeClassifierIsSuccessor`, #1011); the backward arm is the
formation rule `Type@e : Type@(e+1)` wrapped by `ofFormation`.  So `_:_` on universe codes is a faithful copy of
`(ℕ, successor)`. -/
theorem universeClassificationCharacterization {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag} :
    HasTypeDescPi profile context
        (universeCodeCell subjectLevel subjectFlag) (universeCodeCell classifierLevel classifierFlag)
      ↔ (classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag) := by
  constructor
  · intro typed
    exact universeCodeClassifierIsSuccessor typed
  · intro hyp
    cases hyp with
    | intro levelEq flagEq =>
        subst levelEq
        subst flagEq
        exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context subjectLevel classifierFlag)

/-- **Predicativity as non-transitivity.**  `Type@0 : Type@1` and `Type@1 : Type@2`, yet NOT `Type@0 : Type@2` —
the classification relation does not compose.  A cumulative/impredicative hierarchy would make it transitive;
FX's strictly-predicative tower does not.  The two positive rungs are `universeLevelTower_hasTypeDescPi` (#1010);
the negative is the exact characterization (`Type@0 : Type@2` would force `level 2 = level 1`, refuted by level
injectivity). -/
theorem universeClassificationNotTransitive {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 0) (universeLevelTower flag 1)
      ∧ HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 1) (universeLevelTower flag 2)
      ∧ ¬ HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 0) (universeLevelTower flag 2) := by
  refine ⟨universeLevelTower_hasTypeDescPi flag 0, universeLevelTower_hasTypeDescPi flag 1, ?_⟩
  intro typed
  have depthEq : universeLevelOfNat 2 = universeLevelOfNat 1 :=
    (universeCodeClassifierIsSuccessor typed).left
  exact absurd (universeLevelOfNat_injective depthEq) (by decide)

/-- ★ **The engine is non-cumulative: no universe code is typed two levels up.**  For every level `e` and flag,
`Type@e : Type@(e+2)` is underivable — the engine never lets a universe code skip a level.  This mechanizes FX
§1.1's commitment to a strictly predicative hierarchy: the exact characterization forces `e.lsucc.lsucc =
e.lsucc`, refuted by the level-algebra predicativity guard `LevelExpr.ne_lsucc_self`. -/
theorem universeNotCumulativeBySkip {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (subjectLevel : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context
        (universeCodeCell subjectLevel flag) (universeCodeCell subjectLevel.lsucc.lsucc flag) := by
  intro typed
  exact LevelExpr.ne_lsucc_self subjectLevel.lsucc (universeCodeClassifierIsSuccessor typed).left.symm

end FX1Poly.Typed
