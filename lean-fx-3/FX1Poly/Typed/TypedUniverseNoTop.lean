import FX1Poly.Typed.TypedUniverseTower
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion

/-! # FX1Poly/Typed/TypedUniverseNoTop — the universe-code classifier is exactly the successor; no top universe

`UNIV-TOWER-INFINITE` (#1010) established the predicative hierarchy as an infinite, non-collapsing tower:
`Type@n : Type@(n+1)` and distinct rungs are non-convertible.  This file sharpens both ends:

  * **`universeCodeClassifierIsSuccessor`** — the universe-code classifier is EXACTLY its successor: if a
    universe code `Type@(subjectLevel, subjectFlag)` is typed at ANOTHER universe code
    `Type@(classifierLevel, classifierFlag)`, then `classifierLevel = subjectLevel.lsucc` AND
    `classifierFlag = subjectFlag` — there is no conversion slack at a universe-code classifier.  This is a
    RIGIDITY fact: the formation rule's `Type@e : Type@(e+1)` is the only way a universe code classifies into
    another universe code.

  * **`universeCodeClassifierUnique`** — the classifier of a universe code is unique up to conversion (a
    concrete instance of typing-uniqueness #469, computed directly via the inversion: any two classifiers are
    each convertible to `Type@(subjectLevel+1)`, hence to each other).

  * **`universeHierarchyHasNoTop` (★)** — there is NO closed term that classifies the whole tower: no single
    `topClassifier : RawTerm 0` satisfies `∀ n, Type@n : topClassifier`.  If one did, instantiating at `n = 0`
    and `n = 1` (via `HasTypeDescPi.inversionUniverseCode`) would force `Type@1 ≡ Type@2`, refuted by universe-
    code conversion injectivity + level injectivity.  So the predicative tower has no maximal universe — the
    exact antithesis of an impredicative `Type : Type`, whose top classifies itself (and re-enables Girard).

The engine input is the shipped grown inversion `HasTypeDescPi.inversionUniverseCode`
(`HasTypeDescPiUniverseCodeInversion.lean`): any classifier a universe code receives is convertible to its
successor.  Combined with `universeCodeCell_inj_of_conv` (#1010's conv-rigidity of universe codes) and
`universeLevelOfNat_injective`, these give the sharp characterization and the no-top non-existence.

This sits alongside `L1-GIRARD-ACYCLIC` (#941, irreflexive — no classification cycle) and `UNIV-CLASS-WF`
(#945, well-founded — no infinite descent): together the classification relation on universe codes is a
strict, rigid, well-founded, unbounded-above order with no top — a discrete copy of `(ℕ, successor)`.

## Zero-axiom verification

`universeCodeClassifierIsSuccessor` / `universeCodeClassifierUnique` are direct compositions of the shipped
inversion with `universeCodeCell_inj_of_conv` / `Conv.trans`/`Conv.sym` (the raw-Conv equivalence package,
#421/#714).  `universeHierarchyHasNoTop` is a `cases` on the existential + two inversion instances + the
conv-injectivity split, closed by `universeLevelOfNat_injective` and a `decide` of `¬ (1 = 2)` (clean
`Nat.decEq`).  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **The universe-code classifier is exactly the successor.**  If a universe code is typed at ANOTHER universe
code, the classifier's level is precisely the subject's successor and the flags agree — no conversion slack.
Directly: the grown universe-code inversion gives `Conv classifier (Type@(subject+1))`, and universe codes are
conv-rigid (`universeCodeCell_inj_of_conv`), so the classifier's level/flag are pinned. -/
theorem universeCodeClassifierIsSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag}
    (typed : HasTypeDescPi profile context
      (universeCodeCell subjectLevel subjectFlag) (universeCodeCell classifierLevel classifierFlag)) :
    classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag :=
  universeCodeCell_inj_of_conv (HasTypeDescPi.inversionUniverseCode typed)

/-- **The classifier of a universe code is unique up to conversion.**  Any two classifiers a universe code
receives are each convertible to its successor `Type@(subject+1)`, hence to each other — a concrete instance of
typing-uniqueness (#469) computed directly through the inversion. -/
theorem universeCodeClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag} {classifierLeft classifierRight : RawTerm scope}
    (typedLeft : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierLeft)
    (typedRight : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierRight) :
    Conv classifierLeft classifierRight :=
  Conv.trans (HasTypeDescPi.inversionUniverseCode typedLeft)
    (Conv.sym (HasTypeDescPi.inversionUniverseCode typedRight))

/-- ★ **The predicative universe hierarchy has NO top.**  There is no closed term that classifies the entire
tower `Type@0, Type@1, Type@2, …`: a hypothetical `topClassifier` would, by the universe-code inversion at
`n = 0` and `n = 1`, be convertible to BOTH `Type@1` and `Type@2`, forcing `Type@1 ≡ Type@2` — refuted by
universe-code conversion injectivity and level injectivity.  So the ascent is unbounded with no maximal
universe, the exact antithesis of an impredicative `Type : Type` (whose self-classifying top re-enables Girard's
paradox). -/
theorem universeHierarchyHasNoTop {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ ∃ topClassifier : RawTerm 0,
      ∀ n : Nat, HasTypeDescPi profile TypingContext.empty (universeLevelTower flag n) topClassifier := by
  intro existsTop
  cases existsTop with
  | intro topClassifier classifiesAll =>
      have convAtZero : Conv topClassifier (universeCodeCell (universeLevelOfNat 0).lsucc flag) :=
        HasTypeDescPi.inversionUniverseCode (classifiesAll 0)
      have convAtOne : Conv topClassifier (universeCodeCell (universeLevelOfNat 1).lsucc flag) :=
        HasTypeDescPi.inversionUniverseCode (classifiesAll 1)
      have levelCollision :
          Conv (universeCodeCell (universeLevelOfNat 0).lsucc flag)
            (universeCodeCell (universeLevelOfNat 1).lsucc flag) :=
        Conv.trans (Conv.sym convAtZero) convAtOne
      have depthCollision : universeLevelOfNat 1 = universeLevelOfNat 2 :=
        (universeCodeCell_inj_of_conv levelCollision).left
      exact absurd (universeLevelOfNat_injective depthCollision) (by decide)

end FX1Poly.Typed
