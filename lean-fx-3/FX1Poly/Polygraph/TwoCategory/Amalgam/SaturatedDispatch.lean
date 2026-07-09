import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver

/-! # Polygraph/TwoCategory/Amalgam/SaturatedDispatch — the SATURATED categorical Nelson-Oppen dispatch
(WP-AMALG r3, piece 3: statement + the thin fragment that closes + the exact residual)

`Dispatch.lean` (r1) stated the dispatch over the FREE `DecidableTwoCellConvFor` interface; `DispatchLocallyThin`
(r2) inhabited it for two no-2-generator components.  The r2 finding: that FREE interface is the WRONG target —
the shipped walker decisions decide the doctrine-SATURATED relation.  This file re-bases the combination theorem
at the CORRECT interface: `SaturatedDispatchDecidability` records the same Nelson-Oppen hypotheses over the
generic `DecidableSaturatedConvForRel` deciders (`SaturatedOver.lean`), and the thin fragment closes here.

## The saturated re-basing (Pigozzi / Baader-Tinelli, lifted to 2-cells)

The governing prior art stays the disjoint-signature word-problem combination (Pigozzi 1974; Baader-Tinelli
1998, "Deciding the Word Problem in the Union of Equational Theories"): two theories over disjoint signatures
with decidable word problems have a decidable union word problem, PROVIDED no relation crosses the signature
boundary (a shared associative symbol is undecidable).  Here the components share the mode set and have DISJOINT
generators; the pushout's relations are the retagged component relations (component-pure at the split point,
`computadGeneratorsDisjoint`).  This is the FIRST mechanization of that combination at 2-categorical / computad
granularity — a novel 2-dimensional lift; the string-diagram / PROP literature (Bonchi et al., *String Diagram
Rewrite Theory II*) supplies only the single-theory word-problem-via-confluence machinery and the coproduct
construction, NOT a modular decidability transfer.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`SaturatedDispatchDecidability`** — the saturated dispatch STATEMENT: two component saturated deciders + the
    disjoint-generator condition + the combined saturated decider over the pushout, each at the generic
    `DecidableSaturatedConvForRel` interface (parameterized by the three law relations).
  * **`saturatedLocallyThinDispatch`** — the THIN fragment INHABITED: two no-2-generator components (empty law
    relations) give a genuine `SaturatedDispatchDecidability` (the pushout inherits no 2-generators, so its
    combined decider is locally thin too).  The saturated analog of r2's `locallyThinDispatch`, now at the
    correct interface.
  * **`involutionSecondSaturatedDispatch`** + **`saturatedMixedThinVerdict`** — the concrete inhabitant at
    `involution +_M semiring` and a genuine MIXED 2-cell pair over that real pushout decided `isTrue` at the
    SATURATED interface (`#eval`'d).

## The exact residual (why the FULL dispatch stays open)

A REAL-relation pushout (a component contributing genuine laws, e.g. `involution +_M idempotentMonad`) needs the
pushout's `baseRelPushout` to be the disjoint union of the retagged component law relations.  That retag at the
2-cell EXPRESSION level needs a cell-functor `RawTwoCellExpr comp_i.toModeSignature -> RawTwoCellExpr
pushout.toModeSignature` along the coprojection — which does NOT exist (`Pushout.lean`'s coprojections act on
modes + 1-generators only).  Even with it, the cross-component block dispatch needs the disjoint-support Godement
block-commutation (`fxMode_hasArcBlockCommuteProof = false`, the SAME open residual `DispatchLocallyThin` names).
So the real-relation non-vacuity lives at the COMPONENT decider (`SaturatedComponentDecider.lean`, piece 2a); at
the PUSHOUT only the thin fragment closes, and `fxAmalg_hasSaturatedDispatchTheorem = false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The saturated dispatch statement -/

/-- ★ **The SATURATED categorical Nelson-Oppen dispatch statement.**  The saturated analog of
`DispatchDecidability` — the disjoint-signature word-problem combination at the CORRECT (doctrine-saturated)
interface: two component saturated deciders (`DecidableSaturatedConvForRel` for the components' own law
relations), the disjoint-generator condition (the load-bearing Baader-Tinelli hypothesis — no relation crosses
the boundary), and the CONCLUSION, a decider for the pushout's saturated convertibility at the combined law
relation.  Parameterized by the three law relations (the pushout's is, in the genuine case, the disjoint union of
the retagged component relations — see the residual). -/
structure SaturatedDispatchDecidability (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (baseRelOne : CellRel comp1.toModeSignature)
    (baseRelTwo : CellRel comp2.toModeSignature)
    (baseRelPushout : CellRel (pushoutShared comp1 comp2 sameModes).toModeSignature) where
  /-- Component 1's saturated word problem is decided. -/
  componentOneDecider : DecidableSaturatedConvForRel comp1.toModeSignature baseRelOne
  /-- Component 2's saturated word problem is decided. -/
  componentTwoDecider : DecidableSaturatedConvForRel comp2.toModeSignature baseRelTwo
  /-- The disjoint-generator condition — no relation mentions both components' generators. -/
  generatorsDisjoint :
    computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true
  /-- The CONCLUSION — a decider for the pushout's saturated convertibility. -/
  combinedDecider :
    DecidableSaturatedConvForRel (pushoutShared comp1 comp2 sameModes).toModeSignature baseRelPushout

/-! ## The thin fragment, inhabited -/

/-- ★ **The doubly-thin SATURATED dispatch** — `SaturatedDispatchDecidability` INHABITED for two no-2-generator
components (all three law relations empty).  Both component deciders are `saturatedLocallyThinDecider`; the
pushout inherits no 2-generators (`pushout_twoGenLenZero_of_components`), so its combined saturated decider is
locally thin too; the disjoint-generator precondition holds vacuously (empty 2-generator list).  The saturated
analog of r2's `locallyThinDispatch` — the block-stable (both-thin) fragment, now at the correct interface. -/
def saturatedLocallyThinDispatch {comp1 comp2 : ModeComputad} (sameModes : comp1.modeCount = comp2.modeCount)
    (leftLenZero : comp1.twoCellGenerators.length = 0)
    (rightLenZero : comp2.twoCellGenerators.length = 0)
    (disjoint :
      computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true) :
    SaturatedDispatchDecidability comp1 comp2 sameModes
      (emptyCellRel comp1.toModeSignature) (emptyCellRel comp2.toModeSignature)
      (emptyCellRel (pushoutShared comp1 comp2 sameModes).toModeSignature) where
  componentOneDecider := saturatedLocallyThinDecider (noGen_of_twoGenLenZero leftLenZero)
  componentTwoDecider := saturatedLocallyThinDecider (noGen_of_twoGenLenZero rightLenZero)
  generatorsDisjoint := disjoint
  combinedDecider :=
    saturatedLocallyThinDecider
      (noGen_of_twoGenLenZero (pushout_twoGenLenZero_of_components sameModes leftLenZero rightLenZero))

/-! ## The concrete inhabitant + a mixed pair decided at the saturated interface -/

/-- ★ **The saturated dispatch INHABITED at the concrete involution + semiring pushout** — a genuine
`SaturatedDispatchDecidability` assembled from two real locally-thin walking-doctrine saturated deciders. -/
def involutionSecondSaturatedDispatch :
    SaturatedDispatchDecidability involutionComputad secondThinComputad involutionSecondSameModes
      (emptyCellRel involutionComputad.toModeSignature)
      (emptyCellRel secondThinComputad.toModeSignature)
      (emptyCellRel thinPushout.toModeSignature) :=
  saturatedLocallyThinDispatch involutionSecondSameModes rfl rfl thinPushout_disjoint

/-- The combined SATURATED decider of the concrete dispatch, applied to the mixed pair (the same genuinely-mixed
pair `DispatchLocallyThin` uses — a boundary over BOTH components' letters, two DISTINCT expressions), read off as
a `Bool`.  Expect `true`: the two mixed expressions are saturated-convertible (locally thin), and the saturated
combined decider COMPUTES the verdict. -/
def saturatedMixedThinVerdict : Bool :=
  match involutionSecondSaturatedDispatch.combinedDecider thinMixedAlpha thinMixedBeta with
  | isTrue _ => true
  | isFalse _ => false

-- The mixed pair over the real thin pushout, decided at the SATURATED interface: expect `true`.
#eval saturatedMixedThinVerdict

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the SATURATED dispatch STATEMENT + thin fragment SHIP (r3 piece 3).**
`SaturatedDispatchDecidability` records the disjoint-signature combination at the CORRECT doctrine-saturated
interface (the r2 finding's fix); `saturatedLocallyThinDispatch` inhabits it for two no-2-generator components,
witnessed concretely at `involution +_M semiring` (`involutionSecondSaturatedDispatch`) with a genuine MIXED
2-cell pair decided at the saturated interface (`saturatedMixedThinVerdict`, `#eval`'d).  `= true`. -/
def fxAmalg_hasSaturatedThinDispatch : Bool := true

/-- **Honesty marker.**  The FULL cross-component saturated dispatch — the arrow inhabiting
`SaturatedDispatchDecidability` for a REAL-relation pushout (a component with genuine laws) — stays open.  Two
exact residuals: (1) the pushout's `baseRelPushout` must be the disjoint union of the RETAGGED component law
relations, needing a cell-functor `RawTwoCellExpr comp_i.toModeSignature -> RawTwoCellExpr pushout.toModeSignature`
along the coprojection, which does NOT exist (the coprojections act on modes + 1-generators only); (2) the
cross-component block dispatch needs the disjoint-support Godement block-commutation
(`fxMode_hasArcBlockCommuteProof = false`, the same open residual `DispatchLocallyThin` names).  So the
real-relation non-vacuity lives at the COMPONENT decider (`decideSaturatedConvOverIdempotent`, piece 2a); at the
PUSHOUT only the thin fragment closes.  `= false`. -/
def fxAmalg_hasSaturatedDispatchTheorem : Bool := false

end FX1Poly.Polygraph.Amalgam
