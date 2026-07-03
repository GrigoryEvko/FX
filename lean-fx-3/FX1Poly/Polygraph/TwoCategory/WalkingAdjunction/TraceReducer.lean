import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.TraceDecision

/-! # mode-3 floor — the trace reducer: the SN obligation is REFUTED, and the corrected (oriented) engine wiring

`FreeTwoCellTraceDecision` shipped `adjunctionTraceDecisionOfReducer`: it claims that a sound + complete +
TERMINATING + confluent deterministic reducer for the positionwise Godement step
(`SpineGodementAtAnyPosition adjunctionModeSignature`) decides `SpineTraceEquiv`, by feeding the bundle to the
abstract engine `decidableEquationalTheoryOfReducerSN`.  This file discharges the residual that pass left open —
the convergent swap reducer — by first establishing the decisive structural fact about it.

## The finding: the engine's termination obligation is NOT merely hard, it is FALSE

The `terminating` argument the harness demands is

```
{sourceMode targetMode} → ∀ value,
  Acc (fun reduct origin => SpineGodementAtAnyPosition adjunctionModeSignature origin reduct) value
```

i.e. STRONG NORMALIZATION of the FULL positionwise Godement step.  But that relation is **reflexive**:
`SpineGodementStep.godement` is universally quantified over the four interchanged cells, and instantiating ALL
FOUR at the identity 2-cell collapses BOTH of its spine difference-lists to the bare tail `rest` (`id.spineDiff
_ _ acc = acc` by definition).  So `SpineGodementStep adjunctionModeSignature rest rest` holds for every `rest`
(`adjunctionGodementSelfLoop`), hence `SpineGodementAtAnyPosition … rest rest` via `here`.  A relation with a
self-loop has an infinite descending chain `rest ↝ rest ↝ …`, so NO element is accessible: `Acc … value → rel
value value → False` (`selfLoopBlocksAccessibility`).  Therefore the harness's `terminating` is uninhabitable —
supplying it would PROVE `False` (`adjunctionTraceReducerTerminatingRefuted`), and likewise the `WellFounded`
form the Knuth-Bendix engine variant takes (`adjunctionTraceReducerWellFoundedRefuted`).

The all-identity self-loop is a degenerate interchange (`id` whiskered both ways), not a genuine independence
swap; the OBSTRUCTION it creates is nevertheless real — the engine universally quantifies the `Acc` over EVERY
`value`, so one self-loop on `[]` already refutes it.  Conclusion: **the trace word problem cannot be decided by
running the abstract SN-reducer engine on `SpineGodementAtAnyPosition` itself.**  The relation must first be
ORIENTED.

## What this file ships (each piece zero-axiom, machine-checked)

  ★ `selfLoopBlocksAccessibility` — the general well-founded fact: a self-loop blocks `Acc` (`Acc.rec`, axiom-free).
  ★ `adjunctionGodementSelfLoop` / `…AtAnyPosition` — the all-identity Godement self-loop on any tail, the
    concrete reflexivity witness of the positionwise step at the seed.
  ★ `adjunctionTraceReducerTerminatingRefuted` / `…WellFoundedRefuted` — the OBSTRUCTION: the engine's SN
    obligation (in both the `Acc` and `WellFounded` forms) is refutable, so `adjunctionTraceDecisionOfReducer`
    cannot be fed as written.
  ★ `equationalTheoryAbsorb` — generic: if every `rel1`-step is already a `rel2`-conversion then `⟷*_{rel1} ⊆
    ⟷*_{rel2}` (the reusable equational-theory containment lemma the bridge needs).
  ★ `spineTraceEquivIffOrientedTheory` — the CORRECTED bridge: `SpineTraceEquiv` equals the equational theory of
    ANY oriented swap relation `orientedSwap` SANDWICHED between the positionwise Godement step and its own
    equational theory (`orientedSwap ⊆ SpineGodementAtAnyPosition ⊆ ⟷*_{orientedSwap}`).  Built from the shipped
    `spineTraceEquiv_iff_equationalTheory` plus `equationalTheoryAbsorb` both ways — orientation does NOT change
    the theory (`equationalTheory_orientationInvariant` is the abstract reason).
  ★ `adjunctionTraceDecisionViaOrientedReducer` (★) — the CORRECTED harness, replacing
    `adjunctionTraceDecisionOfReducer`: a sound + complete + terminating + confluent reducer for an ORIENTED
    sub-relation `orientedSwap`, PLUS the two sandwich legs (`orientedSwap` steps are Godement steps;
    Godement steps lie in `⟷*_{orientedSwap}`), DECIDES `SpineTraceEquiv` — inhabiting `AdjunctionSpineTraceDecision`
    exactly.  Its `terminating` / `confluent` obligations are now over `orientedSwap`, which CAN be strongly
    normalizing (the reflexive self-loops live in `SpineGodementAtAnyPosition`, not in an order-oriented
    sub-relation).  This is the API the keystone's `traceDecision` slot should target.

## What is DEFERRED (the precise residual) — gates stay `false`

`traceDecision` is NOT discharged here.  The corrected harness reduces it to a SINGLE well-shaped obligation: an
`orientedSwap` relation with the six fields above.  The genuinely hard content is exactly the three pieces the
spine-floor docstrings name, now correctly attached to the ORIENTED relation rather than the reflexive one:

  * the ORIENTED reducer + its `terminating` — a deterministic source-anchored Foata canonicalization whose
    Guiraud–Malbos polygraphic measure strictly decreases on each swap (the naive sum-of-context-lengths is
    NON-monotone: a counit transposition LENGTHENS the moved atom's whisker context);
  * its `confluent` — the trace-monoid hexagon with the context shifts (Gratzer confluence-modulo-interchange);
  * `godementInOrientedTheory` — the completeness leg: every BLOCK Godement step decomposes into oriented
    adjacent atom swaps (bubble-sort decomposition over the four spine blocks).

The `orientedSwap`-step-is-Godement leg (`orientedIsGodement`) is the EASY sandwich half, already reusable from
`singleAtomGodementStep`.  Until the oriented reducer is supplied, `fxMode_hasConvergentGodementReducer` (and the
predecessors' `fxMode_hasSpineTraceDecision` / `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality`) stay `false`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the self-loop is one `godement` constructor whose spines compute by `rfl`; the obstruction is `Acc.rec`; the
bridge is induction on the `EquationalTheory` closure; the harness is `decidable_of_iff` over the shipped
engine).  Verified zero-axiom via a scratch `#print axioms` twin. -/

namespace FX1Poly.Polygraph

open FX1Poly.Core (EquationalTheory Confluent decidableEquationalTheoryOfReducerSN)

/-! ## The obstruction: the positionwise Godement step is reflexive, so its SN obligation is refutable -/

/-- A **self-loop blocks accessibility**: if `rel value value` then `value` is not `Acc`-accessible (an infinite
descending chain `value ↝ value ↝ …` exists).  By induction on the accessibility witness — at `Acc.intro` the
recursor applied to the loop feeds itself.  `Acc.rec`, axiom-free (no `WellFounded.fix`). -/
theorem selfLoopBlocksAccessibility {Carrier : Type} {rel : Carrier → Carrier → Prop} :
    ∀ {value : Carrier}, Acc rel value → rel value value → False := by
  intro value accessibility
  induction accessibility with
  | intro witness _accessStep recurse => intro loop; exact recurse witness loop loop

/-- ★ **The all-identity Godement self-loop.**  Instantiating `SpineGodementStep.godement` at the identity 2-cell
in all four interchanged slots collapses both spine difference-lists to the bare tail `rest` (each `id.spineDiff
_ _ acc = acc`), so the positionwise Godement step relates every spine list to ITSELF.  This degenerate
interchange (`id` whiskered both ways) is the concrete reflexivity witness that breaks strong normalization. -/
def adjunctionGodementSelfLoop
    (rest : List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base)) :
    SpineGodementStep adjunctionModeSignature rest rest :=
  @SpineGodementStep.godement adjunctionModeSignature
    AdjunctionMode.base AdjunctionMode.base
    AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
    adjunctionBaseIdentity adjunctionBaseIdentity adjunctionBaseIdentity
    adjunctionBaseIdentity adjunctionBaseIdentity adjunctionBaseIdentity
    adjunctionIdentityTwoCellOnBase adjunctionIdentityTwoCellOnBase
    adjunctionIdentityTwoCellOnBase adjunctionIdentityTwoCellOnBase
    adjunctionBaseIdentity adjunctionBaseIdentity rest

/-- The positionwise Godement step is reflexive at the seed: `SpineGodementAtAnyPosition … rest rest` for every
tail (lift the self-loop through `here`). -/
def adjunctionGodementSelfLoopAtAnyPosition
    (rest : List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.base)) :
    SpineGodementAtAnyPosition adjunctionModeSignature rest rest :=
  SpineGodementAtAnyPosition.here (adjunctionGodementSelfLoop rest)

/-- ★ **The obstruction (`Acc` form).**  The `terminating` argument of `adjunctionTraceDecisionOfReducer` — strong
normalization of the FULL positionwise Godement step — is uninhabitable: it would yield `False`, because the
relation is reflexive (`adjunctionGodementSelfLoopAtAnyPosition`) and a self-loop blocks `Acc`.  So that harness
(and a direct call to `decidableEquationalTheoryOfReducerSN` on this relation) CANNOT be fed; the relation must be
oriented first. -/
theorem adjunctionTraceReducerTerminatingRefuted
    (terminating : {sourceMode targetMode : AdjunctionMode} →
      ∀ value : List (SpineAtom adjunctionModeSignature sourceMode targetMode),
      Acc (fun reduct origin => SpineGodementAtAnyPosition adjunctionModeSignature origin reduct) value) :
    False :=
  selfLoopBlocksAccessibility (terminating []) (adjunctionGodementSelfLoopAtAnyPosition [])

/-- ★ **The obstruction (`WellFounded` form).**  Likewise the `WellFounded` termination the Knuth-Bendix engine
variant (`knuthBendixDecidesWordProblem`) takes is refutable on the positionwise Godement step. -/
theorem adjunctionTraceReducerWellFoundedRefuted
    (wellFounded : WellFounded (fun reduct origin =>
      SpineGodementAtAnyPosition adjunctionModeSignature
        (overallSource := AdjunctionMode.base) (overallTarget := AdjunctionMode.base) origin reduct)) :
    False :=
  selfLoopBlocksAccessibility (wellFounded.apply []) (adjunctionGodementSelfLoopAtAnyPosition [])

/-! ## The corrected route: decide via an ORIENTED sub-relation with the same equational theory -/

/-- If every `rel1`-step is already a `rel2`-CONVERSION, then `rel1`'s equational theory is contained in `rel2`'s:
`⟷*_{rel1} ⊆ ⟷*_{rel2}`.  Induction on the closure — reflexivity / symmetry / transitivity map across, a single
step uses the embedding.  Free-variable indices, so propext-clean. -/
theorem equationalTheoryAbsorb {Carrier : Type} {rel1 rel2 : Carrier → Carrier → Prop}
    (embed : ∀ {origin reduct : Carrier}, rel1 origin reduct → EquationalTheory rel2 origin reduct)
    {leftValue rightValue : Carrier} (conv : EquationalTheory rel1 leftValue rightValue) :
    EquationalTheory rel2 leftValue rightValue := by
  induction conv with
  | rule step => exact embed step
  | refl point => exact EquationalTheory.refl point
  | symm _ inductionHypothesis => exact EquationalTheory.symm inductionHypothesis
  | trans _ _ firstHypothesis secondHypothesis => exact EquationalTheory.trans firstHypothesis secondHypothesis

/-- ★ **The corrected bridge.**  `SpineTraceEquiv` equals the equational theory of ANY oriented swap relation
`orientedSwap` that is SANDWICHED between the positionwise Godement step and its own equational theory:
`orientedSwap ⊆ SpineGodementAtAnyPosition` (`orientedIsGodement`) and `SpineGodementAtAnyPosition ⊆
⟷*_{orientedSwap}` (`godementInOrientedTheory`).  Forward: `SpineTraceEquiv = ⟷*_{Godement}` (the shipped
`spineTraceEquiv_iff_equationalTheory`), then `equationalTheoryAbsorb` along `godementInOrientedTheory`.
Backward: `equationalTheoryAbsorb` along `orientedIsGodement`, then back through the shipped bridge.  Orientation
leaves the theory invariant. -/
theorem spineTraceEquivIffOrientedTheory {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (orientedSwap : List (SpineAtom signature overallSource overallTarget) →
      List (SpineAtom signature overallSource overallTarget) → Prop)
    (orientedIsGodement : ∀ {origin reduct},
      orientedSwap origin reduct → SpineGodementAtAnyPosition signature origin reduct)
    (godementInOrientedTheory : ∀ {origin reduct},
      SpineGodementAtAnyPosition signature origin reduct → EquationalTheory orientedSwap origin reduct)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
    SpineTraceEquiv signature firstList secondList ↔ EquationalTheory orientedSwap firstList secondList := by
  constructor
  · intro traceEquiv
    exact equationalTheoryAbsorb godementInOrientedTheory (spineTraceEquiv_iff_equationalTheory.mp traceEquiv)
  · intro orientedTheory
    exact spineTraceEquiv_iff_equationalTheory.mpr
      (equationalTheoryAbsorb (fun step => EquationalTheory.rule (orientedIsGodement step)) orientedTheory)

/-- ★ **The corrected reducer harness** — the replacement for `adjunctionTraceDecisionOfReducer`.  A deterministic
reducer (`reduceStep`, sound + complete) for an ORIENTED sub-relation `orientedSwap` that is STRONGLY NORMALIZING
(`terminating`) and CONFLUENT (`confluent`), together with the two sandwich legs (`orientedIsGodement`,
`godementInOrientedTheory`), DECIDES `SpineTraceEquiv` on every cell pair — inhabiting `AdjunctionSpineTraceDecision`.
The engine `decidableEquationalTheoryOfReducerSN` decides `⟷*_{orientedSwap}` (its `Acc` normalizer + Church-Rosser),
and `spineTraceEquivIffOrientedTheory` transports that onto `SpineTraceEquiv`.  Crucially, the `terminating` /
`confluent` obligations are now over `orientedSwap` — which CAN be SN (the reflexive self-loops that refuted the
previous harness live only in the un-oriented `SpineGodementAtAnyPosition`). -/
@[reducible] def adjunctionTraceDecisionViaOrientedReducer
    (orientedSwap : {sourceMode targetMode : AdjunctionMode} →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) → Prop)
    (reduceStep : {sourceMode targetMode : AdjunctionMode} →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
      Option (List (SpineAtom adjunctionModeSignature sourceMode targetMode)))
    (reduceStep_sound : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = some reduct → orientedSwap origin reduct)
    (reduceStep_complete : {sourceMode targetMode : AdjunctionMode} →
      {origin : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = none → ∀ next, ¬ orientedSwap origin next)
    (terminating : {sourceMode targetMode : AdjunctionMode} →
      ∀ value : List (SpineAtom adjunctionModeSignature sourceMode targetMode),
      Acc (fun reduct origin => orientedSwap origin reduct) value)
    (confluent : {sourceMode targetMode : AdjunctionMode} →
      Confluent (orientedSwap (sourceMode := sourceMode) (targetMode := targetMode)))
    (orientedIsGodement : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      orientedSwap origin reduct → SpineGodementAtAnyPosition adjunctionModeSignature origin reduct)
    (godementInOrientedTheory : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      SpineGodementAtAnyPosition adjunctionModeSignature origin reduct →
      EquationalTheory orientedSwap origin reduct) :
    AdjunctionSpineTraceDecision :=
  fun {sourceMode targetMode} {_sourcePath _targetPath} cellFirst cellSecond =>
    letI : Decidable (EquationalTheory (orientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
        cellFirst.spine cellSecond.spine) :=
      @decidableEquationalTheoryOfReducerSN
        (List (SpineAtom adjunctionModeSignature sourceMode targetMode))
        (orientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
        (@adjunctionSpineListDecEq sourceMode targetMode)
        (@reduceStep sourceMode targetMode)
        (@reduceStep_sound sourceMode targetMode)
        (@reduceStep_complete sourceMode targetMode)
        (@terminating sourceMode targetMode)
        (@confluent sourceMode targetMode)
        cellFirst.spine cellSecond.spine
    decidable_of_iff
      (EquationalTheory (orientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
        cellFirst.spine cellSecond.spine)
      (spineTraceEquivIffOrientedTheory (orientedSwap (sourceMode := sourceMode) (targetMode := targetMode))
        (orientedIsGodement (sourceMode := sourceMode) (targetMode := targetMode))
        (godementInOrientedTheory (sourceMode := sourceMode) (targetMode := targetMode))).symm

/-! ## Honesty marker -/

/-- **Honesty marker.**  `traceDecision` is NOT discharged.  This file proves the previous harness's SN obligation
REFUTABLE (`adjunctionTraceReducerTerminatingRefuted`) and ships the CORRECTED harness
(`adjunctionTraceDecisionViaOrientedReducer`) targeting an ORIENTED sub-relation, reducing `traceDecision` to one
well-shaped obligation: an oriented swap relation that is a strongly-normalizing, confluent reducer with the
Godement sandwich.  The genuinely hard residual — the Guiraud–Malbos SN measure, the trace-monoid hexagon
confluence, and the block-step decomposition (`godementInOrientedTheory`) — remains.  Hence
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasConvergentGodementReducer : Bool := false

end FX1Poly.Polygraph
