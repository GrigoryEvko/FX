import FX1Poly.Typed.UnitReadbackFormerChildBoundary

/-! # FX1Poly/Typed/UnitReadbackDeepSpineBoundary
   — ★ the 8th boundary: the spine arm stops at depth 1 (#481 brick-6 verdict)

The corrected brick-5 fact-check relocated the in-fragment completeness frontier: typed former
children are all TYPES today, so the genuine remaining gap inside the TYPEABLE fragment is
application spines of depth ≥ 2 — the shipped spine arm requires the head to be a VARIABLE, and
an app-headed function position falls back to the deep collapse.  Witness, fully grown-typed,
in `(g : Π(_:Unit).Π(_:Unit).Type@0, f : Π(_:Unit).Unit, x : Unit)`:

  * `app(app(g, app(f,x)), x)` and `app(app(g, unit), x)` are congruently unit-η-equal — two
    nested `congGen` descents through the applications, the inner arguments related by `unitEta`
    (the compound neutral grown-typed at `unitTypeCell`, the value data-intro-typed) — and the
    NEUTRAL side is fully grown-typed at `Type@0` (a nested `piElim` chain); the value side's
    whole-spine typing is blocked by the standing `unitCell` engine separation, exactly as in
    the prior boundaries.
  * At the classifier `Type@0` the readback's spine arm sees the function position
    `app(g, ...)` — an APPLICATION, not a variable — refuses, and degrades to the deep collapse
    at EVERY fuel; the collapses are distinct βη-normal forms that never join (the deep collapse
    rewrites the unit VARIABLES but cannot see the compound neutral is unit-typed).

## The verdict — the recursive spine (true `quoteNeutral`)

Depth-2+ spines need the RECURSIVE spine readback — at `app(fn, arg)` recurse into `fn` as a
spine and read `arg` back at the domain of `fn`'s SYNTHESIZED type (`detectSpineType`, shipped).
The soundness wall mapped at brick 4 stands: at depth ≥ 2 the recovered domain is
`subst0(codomain, earlier-argument)` — a SUBSTITUTED code, not a context entry, hence not
formation-typed in general.  Discharging the recursive classifier hypothesis needs either a
grown-validity variant of the soundness (classifier valid rather than formation-typed — with
the wf-extension obligation re-routed) or formation-substitution threading.  That is the
brick-6 build decision.

## Zero-axiom verification

The typings are `piElim` chains over `var` lookups (all `rfl`-computing closed codes); the
`congGen` witness composes shipped leaves; degradations are `rfl` per fuel shape; the collapse
computations are `rfl`; non-joinability is the `reduceOnceBetaEta_complete`-at-`rfl` leaf
discipline; inequalities are `decide`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The depth-2 context `(g : Π(_:Unit).Π(_:Unit).Type@0, f : Π(_:Unit).Unit, x : Unit)` —
a CURRIED higher-order function, so reaching its second argument requires spine depth 2. -/
def deepSpineContext (profile : PolyProfile) : TypingContext profile 3 :=
  (((TypingContext.empty : TypingContext profile 0).cons
    (piTyCodeCell unitTypeCell
      (piTyCodeCell unitTypeCell
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)))).cons
    (piTyCodeCell unitTypeCell unitTypeCell)).cons unitTypeCell

/-- The compound unit-typed neutral `app(f,x)` at scope 3. -/
def deepSpineInnerNeutral : RawTerm 3 :=
  appCell (variableCell ⟨1, Nat.le.step Nat.le.refl⟩)
    (variableCell ⟨0, Nat.le.step (Nat.le.step Nat.le.refl)⟩)

/-- `app(app(g, app(f,x)), x)` — the unit difference buried at the INNER argument of a depth-2
spine. -/
def deepSpineOverNeutral : RawTerm 3 :=
  appCell
    (appCell (variableCell ⟨2, Nat.le.refl⟩) deepSpineInnerNeutral)
    (variableCell ⟨0, Nat.le.step (Nat.le.step Nat.le.refl)⟩)

/-- `app(app(g, unit), x)` — the η-long target. -/
def deepSpineOverUnitValue : RawTerm 3 :=
  appCell
    (appCell (variableCell ⟨2, Nat.le.refl⟩) unitCell)
    (variableCell ⟨0, Nat.le.step (Nat.le.step Nat.le.refl)⟩)

/-- The inner neutral is grown-typed at `unitTypeCell` — `piElim` of `f` at `x`. -/
theorem deepSpineInnerNeutralTyped (profile : PolyProfile) :
    HasTypeDescPi profile (deepSpineContext profile) deepSpineInnerNeutral unitTypeCell :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (deepSpineContext profile) ⟨1, Nat.le.step Nat.le.refl⟩))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (deepSpineContext profile)
        ⟨0, Nat.le.step (Nat.le.step Nat.le.refl)⟩))

/-- **The neutral-side depth-2 spine is fully grown-typed at `Type@0`** — a nested `piElim`
chain (the deepest fully-grown-typed boundary witness so far). -/
theorem deepSpineOverNeutralTyped (profile : PolyProfile) :
    HasTypeDescPi profile (deepSpineContext profile) deepSpineOverNeutral
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.piElim
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var (deepSpineContext profile) ⟨2, Nat.le.refl⟩))
      (deepSpineInnerNeutralTyped profile))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (deepSpineContext profile)
        ⟨0, Nat.le.step (Nat.le.step Nat.le.refl)⟩))

/-- **The depth-2 spines are congruently unit-η-equal**: two nested `congGen` descents — outer
function position differs, inner argument is the `unitEta` pair, everything else shared. -/
theorem deepSpinePair_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (deepSpineContext profile)
      deepSpineOverNeutral deepSpineOverUnitValue :=
  DefEqUnitEtaCong.congGen (generator := Generator.gen_app) ()
    (.consZero
      (DefEqUnitEtaCong.congGen (generator := Generator.gen_app) ()
        (.consEqualZero
          (.consZero
            (.ofDefEq (.unitEta (Or.inr (deepSpineInnerNeutralTyped profile))
              (Or.inl (HasTypeDescDataIntro.unitValueTyped (deepSpineContext profile)))))
            .nil)))
      (.consEqualZero .nil))

/-- At `Type@0` the readback degrades to the deep collapse on BOTH depth-2 spines at EVERY
fuel — the spine arm refuses an app-headed function position. -/
theorem readback_deepSpineNeutral_isDeepCollapse (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (deepSpineContext profile)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard) deepSpineOverNeutral
        = collapseUnitVariablesDeep (deepSpineContext profile) deepSpineOverNeutral
  | 0 => rfl
  | _ + 1 => rfl

theorem readback_deepSpineValue_isDeepCollapse (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (deepSpineContext profile)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard) deepSpineOverUnitValue
        = collapseUnitVariablesDeep (deepSpineContext profile) deepSpineOverUnitValue
  | 0 => rfl
  | _ + 1 => rfl

/-- The deep collapse of the neutral side: the unit VARIABLES are rewritten everywhere, but the
compound neutral survives — un-seen unit-typedness at spine depth 2. -/
def collapsedDeepSpineOverNeutral : RawTerm 3 :=
  appCell
    (appCell (variableCell ⟨2, Nat.le.refl⟩)
      (appCell (variableCell ⟨1, Nat.le.step Nat.le.refl⟩) unitCell))
    unitCell

def collapsedDeepSpineOverUnitValue : RawTerm 3 :=
  appCell (appCell (variableCell ⟨2, Nat.le.refl⟩) unitCell) unitCell

theorem deepCollapse_deepSpineNeutral (profile : PolyProfile) :
    collapseUnitVariablesDeep (deepSpineContext profile) deepSpineOverNeutral
      = collapsedDeepSpineOverNeutral := rfl

theorem deepCollapse_deepSpineValue (profile : PolyProfile) :
    collapseUnitVariablesDeep (deepSpineContext profile) deepSpineOverUnitValue
      = collapsedDeepSpineOverUnitValue := rfl

/-- **The collapsed depth-2 spines never βη-join** — variable-headed stuck spines, distinct. -/
theorem collapsedDeepSpinePair_notBetaEtaConv :
    ¬ BetaEtaConv collapsedDeepSpineOverNeutral collapsedDeepSpineOverUnitValue := by
  intro convertible
  obtain ⟨commonTerm, neutralChain, valueChain⟩ := convertible
  have neutralEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        collapsedDeepSpineOverNeutral.reduceOnceBetaEta = none))
      neutralChain
  have valueEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        collapsedDeepSpineOverUnitValue.reduceOnceBetaEta = none))
      valueChain
  exact absurd (neutralEq.trans valueEq.symm) (by decide)

/-- **★ The 8th boundary — the spine arm stops at depth 1**: a congruently unit-η-equal pair of
depth-2 spines (the neutral side fully grown-typed at `Type@0`) whose readbacks at EVERY fuel
are distinct βη-normal forms that never join.  The recursive spine readback (true
`quoteNeutral`) with its substituted-domain soundness obligation is the brick-6 build. -/
theorem readback_isIncompleteAtDeepSpines (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 3),
      DefEqUnitEtaCong profile (deepSpineContext profile) leftTerm rightTerm ∧
      HasTypeDescPi profile (deepSpineContext profile) leftTerm
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) ∧
      (∀ leftFuel rightFuel : Nat,
        readbackAtClassifier leftFuel (deepSpineContext profile)
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard) leftTerm
          ≠ readbackAtClassifier rightFuel (deepSpineContext profile)
              (universeCodeCell LevelExpr.lzero UniverseFlag.standard) rightTerm) ∧
      ¬ BetaEtaConv
          (collapseUnitVariablesDeep (deepSpineContext profile) leftTerm)
          (collapseUnitVariablesDeep (deepSpineContext profile) rightTerm) :=
  ⟨deepSpineOverNeutral, deepSpineOverUnitValue,
    deepSpinePair_congruentlyEqual profile,
    deepSpineOverNeutralTyped profile,
    fun leftFuel rightFuel readbacksEqual =>
      absurd
        (show collapsedDeepSpineOverNeutral = collapsedDeepSpineOverUnitValue from
          (readback_deepSpineNeutral_isDeepCollapse profile leftFuel).symm.trans
            (readbacksEqual.trans
              (readback_deepSpineValue_isDeepCollapse profile rightFuel)))
        (by decide),
    collapsedDeepSpinePair_notBetaEtaConv⟩

end FX1Poly.Typed
