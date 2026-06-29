import FX1Poly.Tier0.Mode.AdjunctionTwoCellDecidable
import FX1Poly.Tier0.Mode.ComputadWordProblem

/-! # mode-3 floor — the FULL `TwoCellConv` decision at the seed, reduced to EXACTLY the Godement residual

`AdjunctionTwoCellDecidable` shipped the POSITIVE half of the affine walking-adjunction seed's 2-cell decision:
interchange-FREE convertibility is decidable (`adjunctionDecidableInterchangeFreeConv`), and equal interchange-free
normal forms imply FULL convertibility (`normalFormEq_imp_twoCellConv`).  `ComputadWordProblem` shipped the
count-based NEGATIVE half: distinct generator counts imply NOT convertible (`TwoCellConv.not_of_generatorCount_ne`).
Between them, the FULL `TwoCellConv` decision (the equivalence closure of the full `TwoCellStep`, Godement
`interchange` INCLUDED) is reduced to EXACTLY the **modulo-interchange residual**: cells of EQUAL generator count
whose interchange-free normal forms DIFFER.  This file settles whether that residual is empty at the seed (it is
NOT) and assembles the full decision down to that one residual.

## Scouting verdict — interchange is NON-DEGENERATE at the walking-adjunction seed

The Godement / Eckmann–Hilton non-confluence needs a configuration `hcomp (vcomp α α') (vcomp β β')` with
genuinely composable parallel 2-cells.  The seed HAS one, because the unit `1_base ⇒ (left then right)` can be
both whiskered and vertically stacked: take

    redex  = hcomp (id_{1_base} ⊟ unit) (unit ⊟ id_{LR})   :  1_base ⇒ LRLR
    reduct = (hcomp id_{1_base} unit) ⊟ (hcomp unit id_{LR})

(`adjunctionParallelUnitsRedex` / `adjunctionParallelUnitsReduct`) — the two parallel units inserted in the two
orders.  They are related by ONE `interchange` step (`adjunctionParallelUnitsInterchangeStep`), hence `TwoCellConv`
(`adjunctionParallelUnitsConv`), have EQUAL generator count 2 (`adjunctionParallelUnitsGeneratorCountEq`), yet their
interchange-free normal forms `(wR_nil unit) ⊟ (wL_LR unit)` and `(wL_nil unit) ⊟ (wR_LR unit)` are DISTINCT —
machine-checked `decide = false` over the shipped free-2-cell `DecidableEq`
(`adjunctionParallelUnitsNormalFormsDiffer`).  Hence `adjunctionInterchangeIsNonDegenerate`: there are cells that
are `TwoCellConv` but NOT interchange-free-convertible — the positive half ALONE cannot decide `TwoCellConv`, and
the modulo-interchange residual is genuinely non-empty at the seed.  (So the short route the keystone could have
taken — "interchange-free convertibility already IS `TwoCellConv` at this thin seed" — is CLOSED off, honestly.)

## What this file ships (each piece zero-axiom)

  * the non-degeneracy witness above (the scouting verdict, machine-checked);
  * ★ `adjunctionDecidableTwoCellConvModuloResidual` — the FULL `Decidable (TwoCellConv …)` at the seed, ASSEMBLED
    from the two shipped halves down to a single hypothesis `residual` (the Godement decision): distinct count ⟹
    `isFalse` (count negative half); equal interchange-free normal forms ⟹ `isTrue` (the positive half); the only
    case handed to `residual` is EXACTLY equal-count-distinct-normal-forms, the modulo-interchange residual.
  * ★ `adjunctionTwoCellWordProblemModuloResidual` — packaged as a `DecidableTwoCellConvFor adjunctionModeSignature`
    (the `mode-3` interface) modulo the same `residual`.  Supplying `residual` (the trace-monoid / Mazurkiewicz
    decision deciding interchange-equivalence of two interchange-free normal forms) inhabits the interface and is
    PRECISELY what would flip `fxMode_hasModeRelativeConvDecision` — no other obligation is owed.

## The precise remaining gap (gates stay `false`)

`residual` is the genuine Godement / confluence-modulo-interchange (Gratzer coherence) hurdle: deciding whether two
interchange-free normal forms with equal generator count are related by the interchange equation — the trace
monoid (Mazurkiewicz) word problem on the whiskered-atom spine (`FreeTwoCellSpine`), where adjacent
horizontally-independent atoms commute with a context shift.  It is NOT discharged here (its source-anchor
canonical form over the dependently-typed, context-shifting spine is a substantial zero-axiom development).  So
`fxMode_hasModeRelativeConvDecision` and `fxMode_hasDecidableTwoCellEquality` stay `false`; the convergent-3-polygraph
route stays blocked (`fxMode_hasConvergentThreeCellSystem = false`, correct — the base rules are non-confluent).
What this file adds is the machine-checked PROOF that the residual is real plus the assembly of everything else
around it, so the keystone now awaits exactly one named decision and nothing more.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
witness computes by `rfl` on the shipped `Acc.rec` normalizer + free-2-cell `DecidableEq`; the assembly is `dite`
on the two shipped decisions).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The seed boundary 1-cells of the witness -/

/-- The source boundary of the witness: the identity 1-cell at `base` (`nil`). -/
abbrev adjunctionBaseIdentity : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  identityPath (graph := adjunctionGraph) AdjunctionMode.base

/-- The target boundary of the witness: `LRLR` — `(left then right)` twice, the codomain both parallel units
build up to. -/
abbrev adjunctionLeftRightTwice : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  composePath adjunctionLeftThenRight adjunctionLeftThenRight

/-! ## The Eckmann–Hilton witness cells -/

/-- The identity 2-cell on the base identity 1-cell. -/
def adjunctionIdentityTwoCellOnBase :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionBaseIdentity :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) adjunctionBaseIdentity

/-- The identity 2-cell on the `left then right` 1-cell. -/
def adjunctionIdentityTwoCellOnLeftRight :
    RawTwoCellExpr adjunctionModeSignature adjunctionLeftThenRight adjunctionLeftThenRight :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) adjunctionLeftThenRight

/-- ★ The **Godement redex** at the seed: `hcomp (id ⊟ unit) (unit ⊟ id)` — the two parallel units horizontally
composed, the canonical `interchange` redex `hcomp (vcomp α α') (vcomp β β')` with `α = id`, `α' = β = unit`,
`β' = id`.  Both slots that interchange permutes (`α'` and `β`) are genuine generators, so the step is
NON-degenerate. -/
def adjunctionParallelUnitsRedex :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  RawTwoCellExpr.hcomp
    (RawTwoCellExpr.vcomp adjunctionIdentityTwoCellOnBase adjunctionUnitTwoCell)
    (RawTwoCellExpr.vcomp adjunctionUnitTwoCell adjunctionIdentityTwoCellOnLeftRight)

/-- ★ The **interchange reduct** of the redex: `(hcomp id unit) ⊟ (hcomp unit id)` — the same two units, built in
the exchanged order. -/
def adjunctionParallelUnitsReduct :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.hcomp adjunctionIdentityTwoCellOnBase adjunctionUnitTwoCell)
    (RawTwoCellExpr.hcomp adjunctionUnitTwoCell adjunctionIdentityTwoCellOnLeftRight)

/-- The single `interchange` 3-cell connecting redex and reduct — the genuine Godement step at the seed. -/
def adjunctionParallelUnitsInterchangeStep :
    TwoCellStep adjunctionModeSignature adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  TwoCellStep.interchange adjunctionIdentityTwoCellOnBase adjunctionUnitTwoCell
    adjunctionUnitTwoCell adjunctionIdentityTwoCellOnLeftRight

/-- Hence redex and reduct are `TwoCellConv` (a one-step conversion). -/
def adjunctionParallelUnitsConv :
    TwoCellConv adjunctionModeSignature adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  TwoCellConv.ofStep adjunctionParallelUnitsInterchangeStep

/-- Redex and reduct have EQUAL generator count (2) — so the shipped count-based negative half does NOT separate
them: the residual case is the only one left. -/
theorem adjunctionParallelUnitsGeneratorCountEq :
    adjunctionParallelUnitsRedex.generatorCount = adjunctionParallelUnitsReduct.generatorCount := rfl

/-! ## The two interchange-free normal forms — distinct -/

/-- The interchange-free normal form of the redex (`(wR_nil unit) ⊟ (wL_LR unit)`). -/
abbrev adjunctionParallelUnitsRedexNormalForm :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  (interchangeFreeNormalizer adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice).normalize
    adjunctionParallelUnitsRedex

/-- The interchange-free normal form of the reduct (`(wL_nil unit) ⊟ (wR_LR unit)`). -/
abbrev adjunctionParallelUnitsReductNormalForm :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  (interchangeFreeNormalizer adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice).normalize
    adjunctionParallelUnitsReduct

/-- ★ **The two interchange-free normal forms DIFFER** — machine-checked `decide = false` over the shipped
free-2-cell `DecidableEq` (the `Acc.rec` normalizer reduces, `decEq` reduces).  The redex normalizes to the
right-whisker-then-left-whisker spine, the reduct to the left-whisker-then-right-whisker spine: the two
decompositions of the 2×2 Godement pasting, equal only by the interchange equation. -/
theorem adjunctionParallelUnitsNormalFormsDiffer :
    adjunctionParallelUnitsRedexNormalForm ≠ adjunctionParallelUnitsReductNormalForm :=
  of_decide_eq_false
    (inst := adjunctionRawTwoCellDecidableEq
      adjunctionParallelUnitsRedexNormalForm adjunctionParallelUnitsReductNormalForm) rfl

/-- ★ **Scouting verdict: interchange is NON-DEGENERATE at the walking-adjunction seed.**  The redex and reduct
are `TwoCellConv` (via the interchange step) but NOT interchange-free-convertible (their normal forms differ, by
`interchangeFreeConv_iff_normalFormEq`).  So the modulo-interchange residual is genuinely non-empty here, and the
positive half (interchange-free convertibility) does NOT coincide with the full `TwoCellConv` — the Godement
decision is required, not bypassable. -/
theorem adjunctionInterchangeIsNonDegenerate :
    TwoCellConv adjunctionModeSignature adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct ∧
      ¬ Core.EquationalTheory
          (fun (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature
              adjunctionBaseIdentity adjunctionLeftRightTwice) =>
            TwoCellStepInterchangeFree adjunctionModeSignature cellFirst cellSecond)
          adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  ⟨adjunctionParallelUnitsConv,
   fun convertible => adjunctionParallelUnitsNormalFormsDiffer
     ((interchangeFreeConv_iff_normalFormEq adjunctionModeSignature
        adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct).mp convertible)⟩

/-! ## The full decision, assembled down to the Godement residual -/

/-- ★ **The full `TwoCellConv` decision at the seed, modulo the Godement residual.**  Decides
`TwoCellConv adjunctionModeSignature cellFirst cellSecond` from the two shipped halves and ONE hypothesis
`residual`:

  * generator counts DIFFER ⟹ `isFalse` (the count negative half, `TwoCellConv.not_of_generatorCount_ne`);
  * counts agree AND interchange-free normal forms agree ⟹ `isTrue` (the positive half,
    `normalFormEq_imp_twoCellConv`);
  * counts agree but normal forms DIFFER ⟹ delegated to `residual` — and `adjunctionInterchangeIsNonDegenerate`
    shows this case is genuinely reachable.

`residual` is EXACTLY the modulo-interchange (Godement) decision: decide convertibility of two cells whose
interchange-free normal forms differ — equivalently, decide interchange-equivalence of those two normal forms (the
trace-monoid word problem).  This is the sole remaining obligation; everything else is discharged here. -/
def adjunctionDecidableTwoCellConvModuloResidual
    (residual : {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
      (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
      cellFirst.generatorCount = cellSecond.generatorCount →
      (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellFirst ≠
        (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellSecond →
      Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond))
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond) :=
  if countsAgree : cellFirst.generatorCount = cellSecond.generatorCount then
    letI : DecidableEq (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
      adjunctionRawTwoCellDecidableEq
    if normalFormsAgree :
        (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellFirst =
          (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellSecond then
      isTrue (normalFormEq_imp_twoCellConv adjunctionModeSignature normalFormsAgree)
    else
      residual cellFirst cellSecond countsAgree normalFormsAgree
  else
    isFalse (TwoCellConv.not_of_generatorCount_ne countsAgree)

/-- ★ **The seed's 2-cell word problem, modulo the Godement residual.**  Packages
`adjunctionDecidableTwoCellConvModuloResidual` as a `DecidableTwoCellConvFor adjunctionModeSignature` (the `mode-3`
decidability interface) under the same single `residual` hypothesis.  Supplying `residual` — the trace-monoid
decision of interchange-equivalence of interchange-free normal forms — inhabits the interface and is PRECISELY what
flips `fxMode_hasModeRelativeConvDecision`; this file owes nothing else. -/
def adjunctionTwoCellWordProblemModuloResidual
    (residual : {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
      (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
      cellFirst.generatorCount = cellSecond.generatorCount →
      (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellFirst ≠
        (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellSecond →
      Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond)) :
    DecidableTwoCellConvFor adjunctionModeSignature :=
  fun cellFirst cellSecond =>
    adjunctionDecidableTwoCellConvModuloResidual residual cellFirst cellSecond

/-! ## Honesty marker -/

/-- **Honesty marker.**  The FULL `TwoCellConv` decision at the seed is NOT realized: the Godement `residual`
(deciding interchange-equivalence of two interchange-free normal forms — the trace-monoid word problem) is left
open, so `adjunctionTwoCellWordProblemModuloResidual` is CONDITIONAL on it.  `adjunctionInterchangeIsNonDegenerate`
proves the residual is genuinely non-empty at the seed (interchange does NOT collapse into the interchange-free
fragment here), so it cannot be bypassed.  Hence `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasGodementResidualDecision : Bool := false

end FX1Poly.Tier0
