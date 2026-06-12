import FX1Poly.Typed.UnitReadbackFormerChildBoundary

/-! # FX1Poly/Typed/UnitReadbackDeepSpineBoundary
   — ★ the 8th boundary, DECIDED: the recursive spine readback reaches depth-2 spines (#481 brick 6)

The corrected brick-5 fact-check relocated the in-fragment completeness frontier to application
spines of depth ≥ 2: the depth-1 spine arm required the head to be a VARIABLE, so an app-headed
function position degraded to the deep collapse.  Witness, in
`(g : Π(_:Unit).Π(_:Unit).Type@0, f : Π(_:Unit).Unit, x : Unit)`:

  * `app(app(g, app(f,x)), x)` and `app(app(g, unit), x)` are congruently unit-η-equal — two
    nested `congGen` descents through the applications, the inner arguments related by `unitEta`
    (the compound neutral grown-typed at `unitTypeCell`, the value nullary-value-typed) — and the
    NEUTRAL side is fully grown-typed at `Type@0` (a nested `piElim` chain); the value side's
    whole-spine typing is blocked by the standing `unitCell` engine separation, exactly as in
    the prior boundaries.
  * Against the FROZEN deep-collapse ingredient the boundary stands permanently
    (`deepCollapseMode_isIncompleteAtDeepSpines`): the collapses rewrite the unit VARIABLES but
    cannot see the compound neutral is unit-typed, and the results are distinct βη-normal forms
    that never join.

## The resolution — the recursive spine (brick 6)

The mutual `readbackSpine` recursion dissolved the depth restriction WITHOUT meeting the
substituted-domain soundness wall: at an app-headed function position the spine recurses into
the HEAD (same context — `invertApp` alone feeds the IH) and deep-collapses that level's
argument; classifier-directed argument readback happens only at var-headed levels, where the
domain is a context entry (formation-typed via the wf lookup).  At fuel 4 BOTH depth-2 spines
compute to the η-long form `app(app(g, unit), unit)` (`readback_identifiesDeepSpines`, `rfl` —
fuel 3 is insufficient: the inner argument needs one level for the unit arm, not just the
collapse), and the typed soundness canonicalizes the neutral side to that form directly
(`deepSpine_canonicalizedByReadback`).

## Zero-axiom verification

The typings are `piElim` chains over `var` lookups; the wf witness is nested
`hasTypeDesc_piFormation_viaGenArm` + `universeFormation`; the `congGen` witness composes
shipped leaves; the identification and collapse computations are `rfl`; non-joinability is the
`reduceOnceBetaEta_complete`-at-`rfl` leaf discipline; inequalities are `decide`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
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

/-- The depth-2 context is formation-well-formed — `g`'s curried type through two nested generic
Π-formation arms with `universeFormation` at the leaf, `f`'s through the unit rows. -/
theorem deepSpineContextWellFormed (profile : PolyProfile) :
    WfContextDesc (deepSpineContext profile) :=
  WfContextDesc.cons
    (WfContextDesc.cons
      (WfContextDesc.cons WfContextDesc.emptyIsWellFormed
        ⟨_, _, hasTypeDesc_piFormation_viaGenArm TypingContext.empty
          unitTypeCell
          (piTyCodeCell unitTypeCell
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
          LevelExpr.lzero (LevelExpr.lmax LevelExpr.lzero LevelExpr.lzero.lsucc)
          UniverseFlag.standard
          (unitTypeCellFormationTyped TypingContext.empty)
          (hasTypeDesc_piFormation_viaGenArm (TypingContext.empty.cons unitTypeCell)
            unitTypeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
            LevelExpr.lzero LevelExpr.lzero.lsucc UniverseFlag.standard
            (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell))
            (HasTypeDesc.universeFormation
              ((TypingContext.empty.cons unitTypeCell).cons unitTypeCell)
              LevelExpr.lzero UniverseFlag.standard))⟩)
      ⟨_, _, hasTypeDesc_piFormation_viaGenArm
        (TypingContext.empty.cons
          (piTyCodeCell unitTypeCell
            (piTyCodeCell unitTypeCell
              (universeCodeCell LevelExpr.lzero UniverseFlag.standard))))
        unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
        (unitTypeCellFormationTyped _)
        (unitTypeCellFormationTyped _)⟩)
    (unitTypeCellIsTypeDesc
      (((TypingContext.empty : TypingContext profile 0).cons
        (piTyCodeCell unitTypeCell
          (piTyCodeCell unitTypeCell
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard)))).cons
        (piTyCodeCell unitTypeCell unitTypeCell)))

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

/-- `app(app(g, unit), x)` — the η-long target at the inner argument. -/
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
              (Or.inl (NullaryDataValueTyped.unitValueTyped (deepSpineContext profile)))))
            .nil)))
      (.consEqualZero .nil))

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

/-- **★ The 8th boundary, against the FROZEN deep-collapse ingredient**: a congruently
unit-η-equal pair of depth-2 spines (the neutral side fully grown-typed at `Type@0`) whose deep
collapses are distinct βη-normal forms that never join — the collapse mode cannot see
unit-typedness of a compound neutral at spine depth 2.  This boundary FORCED the recursive
spine readback (brick 6), which decides the pair below. -/
theorem deepCollapseMode_isIncompleteAtDeepSpines (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 3),
      DefEqUnitEtaCong profile (deepSpineContext profile) leftTerm rightTerm ∧
      HasTypeDescPi profile (deepSpineContext profile) leftTerm
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) ∧
      collapseUnitVariablesDeep (deepSpineContext profile) leftTerm
        ≠ collapseUnitVariablesDeep (deepSpineContext profile) rightTerm ∧
      ¬ BetaEtaConv
          (collapseUnitVariablesDeep (deepSpineContext profile) leftTerm)
          (collapseUnitVariablesDeep (deepSpineContext profile) rightTerm) :=
  ⟨deepSpineOverNeutral, deepSpineOverUnitValue,
    deepSpinePair_congruentlyEqual profile,
    deepSpineOverNeutralTyped profile,
    fun collapsesEqual =>
      absurd
        (show collapsedDeepSpineOverNeutral = collapsedDeepSpineOverUnitValue from
          collapsesEqual)
        (by decide),
    collapsedDeepSpinePair_notBetaEtaConv⟩

/-- **★ The recursive spine identifies the depth-2 spines (brick-6 payoff)**: at fuel 4 BOTH
sides compute to the η-long form `app(app(g, unit), unit)` — the spine recursion crosses the
app-headed function position and the recovered domain collapses the inner compound neutral.
By `rfl`.  (Fuel 3 is insufficient: the inner argument's readback needs the unit ARM, which
costs one more level than the collapse.) -/
theorem readback_identifiesDeepSpines (profile : PolyProfile) :
    readbackAtClassifier 4 (deepSpineContext profile)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) deepSpineOverNeutral
      = readbackAtClassifier 4 (deepSpineContext profile)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard) deepSpineOverUnitValue :=
  rfl

/-- **★ The depth-2 spine, canonicalized by the readback** — direct soundness form: the typed
neutral side is congruently unit-η-equal to `app(app(g, unit), unit)`, the η-long form its
fuel-4 readback computes — exactly what the deep collapse could not produce (it left the
compound neutral `app(f, unit)` at the inner argument). -/
theorem deepSpine_canonicalizedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (deepSpineContext profile)
      deepSpineOverNeutral collapsedDeepSpineOverUnitValue :=
  readbackAtClassifier_congruent 4 (deepSpineContext profile)
    (universeCodeCell LevelExpr.lzero UniverseFlag.standard) deepSpineOverNeutral
    (deepSpineContextWellFormed profile)
    (deepSpineOverNeutralTyped profile)
    (HasTypeDesc.universeFormation (deepSpineContext profile)
      LevelExpr.lzero UniverseFlag.standard)

end FX1Poly.Typed
