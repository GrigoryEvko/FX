import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvFullTraceRoute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvDecidable

/-! # mode-3 floor — the BARE `TwoCellConv` Goldilocks candidate: sound + decidable over-approximation, and the
whiskerSum-family INCOMPLETENESS wall upgraded from a SECOND (order) direction

The bare `TwoCellConv` (the free strict-2-category 2-cell congruence MINUS whisker-by-1-cell functoriality,
`fxMode_hasInterchangeAndWhiskerFunctoriality = false`) sits STRICTLY BELOW two shipped decided relations: the
FAITHFUL `TwoCellConvFull` (decided ungated by `adjunctionDecideTwoCellConvFull`) and the SATURATED
`SaturatedTwoCellConv` (decided).  Its OWN decidability is genuinely open — the interchange critical-pair
convergence, Gratzer's coherence hurdle.  TWO natural readback carriers were already machine-refuted from opposite
sides (`RealizedChain`): the TRACE/spine carrier is too COARSE (over-identifies — `whiskerSum` scores `2` vs `0` on
`adjunctionUnitFrame_not_twoCellConv_unit`), and the interchange-free `nfCell` is too FINE (over-separates the
Eckmann–Hilton pair).

This file pursues the GOLDILOCKS refinement: combine the FAITHFUL decision with the bare-invariant moment family.
The moment `whiskerSum` (shipped in `RealizedChain`) is one separating invariant; here we add two MORE bare-conv
moments of the same whisker-word shape and use them to (a) DEFINE the sound, decidable candidate, and (b) prove
`whiskerSum` ALONE is INCOMPLETE, from a NEW (order, not count) direction.

## The whisker word of a generator, and its three linear moments

Read a generator's whisker context OUTERMOST-first as a word over `{L, R}` (left/right whiskers enclosing it).
Three linear moments, each summed over generators:

  * `whiskerSum`  = Σ (word length)            — the number of whisker incidences (shipped, `RealizedChain`).
  * `rSum`        = Σ (# of R in the word)      — the right-whisker incidences.
  * `crossSum`    = Σ (# of L-before-R inversions) — the L-outside-R crossings (an ORDER moment `whiskerSum`
                                                    cannot see).

## What this file ships (each piece zero-axiom)

  ★ `RawTwoCellExpr.rSum` / `RawTwoCellExpr.crossSum` — the two new moments (structural recursion, constant `Nat`
    motive, propext-free).  `crossSum (whiskerLeft _ body) = crossSum body + rSum body` — every new OUTER left
    whisker crosses every trailing right whisker; `crossSum (whiskerRight _ body) = crossSum body` — an outer
    right whisker adds no L-outside-R crossing.
  ★ `TwoCellStep.rSum_eq` / `TwoCellConv.rSum_eq` and `TwoCellStep.crossSum_eq` / `TwoCellConv.crossSum_eq` — both
    are GENUINE BARE-conv invariants: preserved by EVERY `TwoCellStep`, INCLUDING interchange (the make-or-break
    Godement critical pair, discharged by a six-term `Nat.add` reassociation — both Godement orders sum the same
    six moment atoms).  Same induction shape as `TwoCellConv.whiskerSum_eq`.
  ★ `whiskerExchangeLHS` / `whiskerExchangeRHS` — the disjoint-whisker EXCHANGE pair on the unit
    (`nil ◁ (nil ▷ unit)` vs `nil ▷ (nil ◁ unit)`, SAME boundary, no cast needed): `TwoCellConvFull` (via
    `TwoCellConvFull.whiskerExchange`), EQUAL `whiskerSum` (`2 = 2`), yet `crossSum` `1 ≠ 0` — hence NOT bare
    `TwoCellConv`.  This is the SECOND machine-checked refutation of the `whiskerSum` carrier, from the ORDER
    direction (the existing `RealizedChain` refutation was a COUNT distinction).
  ★ `bareConvCandidateWS` / `bareConvCandidate` — the whiskerSum-only candidate and the full-family candidate
    (`TwoCellConvFull` AND equal `whiskerSum`/`rSum`/`crossSum`), with SOUNDNESS (`bareConvCandidate_of_twoCellConv`:
    bare ⟹ candidate, three shipped-invariant conjuncts) and DECIDABILITY at the seed
    (`adjunctionDecideBareConvCandidate`).
  ★ `bareConvCandidateWS_not_complete` — the whiskerExchange pair is `bareConvCandidateWS` yet NOT bare
    `TwoCellConv`: the whiskerSum-only candidate OVER-ACCEPTS, machine-checked incompleteness.
  ★ `bareConvCandidate_excludes_whiskerExchange` — the FULL family candidate correctly REJECTS the whiskerExchange
    pair (its `crossSum` conjunct fails), so `crossSum` STRICTLY refines the candidate past the `whiskerSum`
    blind spot.

## What is DEFERRED — and WHY (the honest, characterized wall) — `fxMode_hasModeRelativeConvDecision` stays `false`

The FULL-family candidate `bareConvCandidate` is a SOUND, DECIDABLE OVER-approximation of bare `TwoCellConv`
(bare ⟹ candidate; candidate decidable).  Its COMPLETENESS (candidate ⟹ bare) — equivalently, whether the finite
moment family (`whiskerSum`, `rSum`, `crossSum`) is a COMPLETE invariant separating the bare-conv sub-classes
inside each `TwoCellConvFull` class — is the interchange-critical-pair coherence (Gratzer's hurdle), and remains
GENUINELY OPEN.  What is now MACHINE-CHECKED past the prior wall: the `whiskerSum` carrier alone is INCOMPLETE
(the whiskerExchange pair, ORDER direction), and `crossSum` is the genuinely-independent SECOND invariant that
recovers it.  The moment family catches EVERY single whisker-functoriality generating law — the four count-changing
laws (`whiskerLeftUnit`/`whiskerRightUnit`/`whiskerLeftComp`/`whiskerRightComp`) by `whiskerSum`, and the
count-preserving `whiskerExchange` by `crossSum` — but global completeness over COMPOSITES stays the deferred
coherence.  So the wall is UPGRADED from route-walled to invariant-characterized from BOTH count and order
directions, and `fxMode_hasBareConvSeparatingFamilyCharacterized` records exactly that; the strictly-finer bare
flag `fxMode_hasModeRelativeConvDecision` is NOT touched and stays `false` (its terminal disposition in
`ModeRelativeMetatheory` is unchanged and not weakened).

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
moments are constant-`Nat`-motive full-enum matches; the `_eq` lemmas are `induction` + explicit `Nat.add_*`
rewrites — never `omega`/`simp`/`ac_rfl`; the whiskerExchange refutation is `Nat.noConfusion` on `1 = 0`; the
decision is nested `match` on the shipped faithful decision + `Nat.decEq`).  Per-declaration `#assert_no_axioms`
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two new bare-conv moments -/

/-- The **right-whisker incidence sum** of a free 2-cell — Σ over generators of the number of RIGHT whiskers in
its whisker word.  A generator / identity scores `0`; a `vcomp` sums the factors; a LEFT whisker passes through
(it is not a right whisker); a RIGHT whisker adds one incidence per generator in its body (`+ generatorCount`).
Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.rSum {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.rSum + cellBeta.rSum
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.rSum
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.rSum + cellBeta.generatorCount

/-- The **left-outside-right crossing sum** of a free 2-cell — Σ over generators of the number of (L, R)
inversions in its whisker word where the LEFT whisker encloses (is outside) a RIGHT whisker.  A generator /
identity scores `0`; a `vcomp` sums the factors; a RIGHT whisker adds no new crossing (it is outermost, so no
enclosing structure is created towards its right whiskers); a LEFT whisker adds one crossing per RIGHT whisker
already present under it (`+ rSum body`) — the new outer L crosses every trailing R.  This is the ORDER moment
`whiskerSum` (a pure count) cannot see.  Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.crossSum {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 0
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.crossSum + cellBeta.crossSum
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.crossSum + cellBeta.rSum
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.crossSum

/-! ## `Nat` reassociation shapes for the interchange rebracketing -/

/-- Middle-four exchange for `Nat` addition — the arithmetic shape whisker distribution takes on the moments.
Propext-free (`Nat.add_assoc` / `Nat.add_left_comm`). -/
private theorem nat_add_middle_four_bcg (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm second third fourth]

/-- Six-term reassociation for `rSum` under interchange: both Godement orders sum the same six atoms
`(rα, rα', gα, gα', rβ, rβ')`.  Two fully-instantiated middle-four exchanges, propext-free. -/
private theorem nat_add_shuffle_six_r (a b c d e f : Nat) :
    ((a + b) + (c + d)) + (e + f) = ((a + c) + e) + ((b + d) + f) := by
  rw [nat_add_middle_four_bcg a b c d, nat_add_middle_four_bcg (a + c) (b + d) e f]

/-- Six-term reassociation for `crossSum` under interchange: both Godement orders sum the same six atoms
`(cα, cα', cβ, cβ', rβ, rβ')`.  Two fully-instantiated middle-four exchanges, propext-free. -/
private theorem nat_add_shuffle_six_cross (a b c d e f : Nat) :
    (a + b) + ((c + d) + (e + f)) = (a + (c + e)) + (b + (d + f)) := by
  rw [nat_add_middle_four_bcg c d e f, nat_add_middle_four_bcg a b (c + e) (d + f)]

/-! ## `rSum` is a bare-conv invariant -/

/-- ★ **`rSum` is invariant under one 3-cell rewrite — INCLUDING interchange.**  Identity removal drops a `0`
factor; re-association / whisker distribution rearrange the sum; the INTERCHANGE law rebrackets the six moment
atoms (`nat_add_shuffle_six_r`).  Left whiskering passes `rSum` through (its congruence needs only the inductive
hypothesis); right whiskering adds `generatorCount`, so its congruence also threads
`TwoCellStep.generatorCount_eq`.  By induction on the step. -/
theorem TwoCellStep.rSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.rSum = reduct.rSum := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.rSum
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.rSum cellBeta.rSum cellGamma.rSum
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ cellAlpha cellBeta =>
      dsimp only [RawTwoCellExpr.rSum, RawTwoCellExpr.generatorCount]
      exact nat_add_middle_four_bcg cellAlpha.rSum cellBeta.rSum
        cellAlpha.generatorCount cellBeta.generatorCount
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.rSum]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.rSum]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.rSum]
      rw [inductionHypothesis, subStep.generatorCount_eq]
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.rSum, RawTwoCellExpr.generatorCount]
      exact nat_add_shuffle_six_r
        cellAlpha.rSum cellAlphaUpper.rSum
        cellAlpha.generatorCount cellAlphaUpper.generatorCount
        cellBeta.rSum cellBetaUpper.rSum

/-- **`rSum` is invariant under 2-cell convertibility.**  A single step is `rSum_eq`; reflexivity is `rfl`;
symmetry / transitivity chain through `Eq`. -/
theorem TwoCellConv.rSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.rSum = reduct.rSum := by
  induction conv with
  | ofStep step => exact step.rSum_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## `crossSum` is a bare-conv invariant -/

/-- ★ **`crossSum` is invariant under one 3-cell rewrite — INCLUDING interchange.**  Identity removal drops a `0`
factor; re-association / whisker distribution rearrange the sum (`nat_add_middle_four_bcg` on the whisker-left
distribution, `rfl` on the whisker-right one); the INTERCHANGE law rebrackets the six moment atoms
(`nat_add_shuffle_six_cross`).  Right whiskering passes `crossSum` through (its congruence needs only the
inductive hypothesis); left whiskering adds `rSum`, so its congruence threads `TwoCellStep.rSum_eq`.  By induction
on the step. -/
theorem TwoCellStep.crossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.crossSum = reduct.crossSum := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.crossSum
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.crossSum cellBeta.crossSum cellGamma.crossSum
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ cellBeta cellGamma =>
      dsimp only [RawTwoCellExpr.crossSum, RawTwoCellExpr.rSum]
      exact nat_add_middle_four_bcg cellBeta.crossSum cellGamma.crossSum
        cellBeta.rSum cellGamma.rSum
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.crossSum]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.crossSum]; rw [inductionHypothesis]
  | whiskerLeftCongr _ subStep inductionHypothesis =>
      dsimp only [RawTwoCellExpr.crossSum]
      rw [inductionHypothesis, subStep.rSum_eq]
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.crossSum, RawTwoCellExpr.rSum,
        RawTwoCellExpr.generatorCount]
      exact nat_add_shuffle_six_cross
        cellAlpha.crossSum cellAlphaUpper.crossSum
        cellBeta.crossSum cellBetaUpper.crossSum
        cellBeta.rSum cellBetaUpper.rSum

/-- **`crossSum` is invariant under 2-cell convertibility.**  A single step is `crossSum_eq`; reflexivity is
`rfl`; symmetry / transitivity chain through `Eq`.  A genuine BARE-conv ORDER invariant surviving interchange,
unlike the whisker-blind `generatorCount` and the order-blind `whiskerSum`. -/
theorem TwoCellConv.crossSum_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.crossSum = reduct.crossSum := by
  induction conv with
  | ofStep step => exact step.crossSum_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## The whiskerExchange separating pair (the ORDER-direction refutation of the whiskerSum carrier) -/

/-- The disjoint-whisker EXCHANGE LEFT side on the unit: `nil ◁ (nil ▷ unit)` — an outer left whisker over an
inner right whisker, both by the identity 1-cell.  Its whisker word is `[L, R]` (one L-outside-R crossing).
Boundary inferred: `nil ⇒ composePath adjunctionLeftThenRight nil`. -/
abbrev whiskerExchangeLHS :=
  RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      adjunctionUnitTwoCell)

/-- The disjoint-whisker EXCHANGE RIGHT side on the unit: `nil ▷ (nil ◁ unit)` — the exchanged order, SAME
boundary as `whiskerExchangeLHS` (both identity 1-cells make the two composite boundaries coincide
definitionally, so NO cast is needed).  Its whisker word is `[R, L]` (zero L-outside-R crossings). -/
abbrev whiskerExchangeRHS :=
  RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
      adjunctionUnitTwoCell)

/-- ★ The exchange pair is `TwoCellConvFull` — via the shipped disjoint-whisker exchange constructor (the cast
along the two reflexive-typed associativity equalities collapses by definitional proof irrelevance, so the
constructor lands exactly on the cast-free `whiskerExchangeRHS`). -/
theorem whiskerExchange_convFull :
    TwoCellConvFull adjunctionModeSignature whiskerExchangeLHS whiskerExchangeRHS :=
  TwoCellConvFull.whiskerExchange (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
    (identityPath (graph := adjunctionGraph) AdjunctionMode.base) adjunctionUnitTwoCell

/-- ★ The exchange pair has EQUAL `whiskerSum` (`2 = 2`) — the whiskerSum carrier CANNOT tell them apart. -/
theorem whiskerExchange_whiskerSum_eq :
    whiskerExchangeLHS.whiskerSum = whiskerExchangeRHS.whiskerSum := rfl

/-- The exchange LEFT side scores `1` L-outside-R crossing (`crossSum`). -/
theorem whiskerExchangeLHS_crossSum : whiskerExchangeLHS.crossSum = 1 := rfl

/-- The exchange RIGHT side scores `0` L-outside-R crossings (`crossSum`). -/
theorem whiskerExchangeRHS_crossSum : whiskerExchangeRHS.crossSum = 0 := rfl

/-- ★ The exchange pair has DISTINCT `crossSum` (`1 ≠ 0`) — the ORDER moment the whiskerSum carrier is blind to. -/
theorem whiskerExchange_crossSum_differs :
    whiskerExchangeLHS.crossSum ≠ whiskerExchangeRHS.crossSum := by
  rw [whiskerExchangeLHS_crossSum, whiskerExchangeRHS_crossSum]
  exact fun contradiction => Nat.noConfusion contradiction

/-- ★★ **The exchange pair is NOT bare `TwoCellConv`.**  `crossSum` — a genuine bare-conv invariant
(`TwoCellConv.crossSum_eq`, preserved by every `TwoCellStep` including interchange) — scores them `1` versus `0`.
So a disjoint-whisker exchange (whisker functoriality law 5) is NOT bare-convertible, witnessed by the ORDER
invariant that survives the interchange critical pair. -/
theorem whiskerExchange_not_twoCellConv :
    ¬ TwoCellConv adjunctionModeSignature whiskerExchangeLHS whiskerExchangeRHS :=
  fun conv => whiskerExchange_crossSum_differs conv.crossSum_eq

/-! ## The Goldilocks candidate: sound, decidable over-approximation of bare `TwoCellConv` -/

/-- The **whiskerSum-only candidate** (rung 1, the minimal proposal): faithful `TwoCellConvFull` PLUS equal
`whiskerSum`.  Sound but INCOMPLETE (over-accepts — see `bareConvCandidateWS_not_complete`). -/
def bareConvCandidateWS {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) : Prop :=
  TwoCellConvFull signature cellFirst cellSecond ∧ cellFirst.whiskerSum = cellSecond.whiskerSum

/-- ★ The **full-family Goldilocks candidate** (rung 2): faithful `TwoCellConvFull` PLUS equal `whiskerSum`,
`rSum`, and `crossSum`.  A SOUND, DECIDABLE OVER-approximation of bare `TwoCellConv`. -/
def bareConvCandidate {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) : Prop :=
  TwoCellConvFull signature cellFirst cellSecond
    ∧ cellFirst.whiskerSum = cellSecond.whiskerSum
    ∧ cellFirst.rSum = cellSecond.rSum
    ∧ cellFirst.crossSum = cellSecond.crossSum

/-- ★ **Soundness (whiskerSum-only): bare ⟹ candidate.**  `ofConv` supplies the faithful conjunct;
`TwoCellConv.whiskerSum_eq` (shipped) the moment conjunct. -/
theorem bareConvCandidateWS_of_twoCellConv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellFirst cellSecond) :
    bareConvCandidateWS cellFirst cellSecond :=
  ⟨TwoCellConvFull.ofConv conv, conv.whiskerSum_eq⟩

/-- ★★ **Soundness (full family): bare ⟹ candidate.**  Nearly free: `ofConv` gives the faithful conjunct, and
`whiskerSum_eq` / `rSum_eq` / `crossSum_eq` (all bare-conv invariants) give the three moment conjuncts. -/
theorem bareConvCandidate_of_twoCellConv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellFirst cellSecond) :
    bareConvCandidate cellFirst cellSecond :=
  ⟨TwoCellConvFull.ofConv conv, conv.whiskerSum_eq, conv.rSum_eq, conv.crossSum_eq⟩

/-! ## Decidability of the candidate at the walking-adjunction seed -/

/-- ★ **The full candidate is DECIDABLE at the seed.**  `TwoCellConvFull` is decided ungated by the shipped
faithful decision `adjunctionDecideTwoCellConvFull`; the three moment equalities are `Nat.decEq`.  Nested `match`
— propext-free. -/
def adjunctionDecideBareConvCandidate
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (bareConvCandidate cellFirst cellSecond) :=
  match adjunctionDecideTwoCellConvFull cellFirst cellSecond with
  | isFalse notFull => isFalse (fun candidate => notFull candidate.1)
  | isTrue convFull =>
      match Nat.decEq cellFirst.whiskerSum cellSecond.whiskerSum with
      | isFalse whiskerDiffers => isFalse (fun candidate => whiskerDiffers candidate.2.1)
      | isTrue whiskerAgrees =>
          match Nat.decEq cellFirst.rSum cellSecond.rSum with
          | isFalse rDiffers => isFalse (fun candidate => rDiffers candidate.2.2.1)
          | isTrue rAgrees =>
              match Nat.decEq cellFirst.crossSum cellSecond.crossSum with
              | isFalse crossDiffers => isFalse (fun candidate => crossDiffers candidate.2.2.2)
              | isTrue crossAgrees => isTrue ⟨convFull, whiskerAgrees, rAgrees, crossAgrees⟩

/-! ## Incompleteness of the whiskerSum-only candidate, and the crossSum refinement -/

/-- ★★ **The whiskerSum-only candidate is INCOMPLETE (over-accepts).**  The whiskerExchange pair is
`bareConvCandidateWS` (faithful `TwoCellConvFull` + EQUAL `whiskerSum` `2 = 2`) yet is NOT bare `TwoCellConv`.
This is the SECOND machine-checked refutation of the whiskerSum carrier — the FIRST
(`adjunctionSpineTraceReconstruction_refuted`, in `RealizedChain`) was a COUNT distinction (`2` vs `0`); this is
an ORDER distinction (`crossSum` `1` vs `0`) whiskerSum is blind to.  A finite moment family therefore needs at
least `crossSum` beyond `whiskerSum`. -/
theorem bareConvCandidateWS_not_complete :
    bareConvCandidateWS whiskerExchangeLHS whiskerExchangeRHS
      ∧ ¬ TwoCellConv adjunctionModeSignature whiskerExchangeLHS whiskerExchangeRHS :=
  ⟨⟨whiskerExchange_convFull, whiskerExchange_whiskerSum_eq⟩, whiskerExchange_not_twoCellConv⟩

/-- ★ **The full-family candidate correctly REJECTS the whiskerExchange pair.**  Adding `crossSum` STRICTLY
refines the candidate past the whiskerSum blind spot: the `crossSum` conjunct fails (`1 ≠ 0`), so the refined
candidate excludes the non-bare pair the whiskerSum-only candidate wrongly accepted. -/
theorem bareConvCandidate_excludes_whiskerExchange :
    ¬ bareConvCandidate whiskerExchangeLHS whiskerExchangeRHS :=
  fun candidate => whiskerExchange_crossSum_differs candidate.2.2.2

/-! ## Non-vacuity: the candidate genuinely accepts bare pairs and rejects non-related pairs -/

/-- ★ **The candidate ACCEPTS a genuine bare-conv pair.**  The Eckmann–Hilton parallel-units pair IS bare
`TwoCellConv` (one `interchange` step, `adjunctionParallelUnitsConv`), so by soundness it satisfies
`bareConvCandidate` — the candidate is not a reject-everything relation. -/
theorem bareConvCandidate_accepts_parallelUnits :
    bareConvCandidate adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  bareConvCandidate_of_twoCellConv adjunctionParallelUnitsConv

/-- ★ **The candidate REJECTS a genuinely-non-related pair.**  The snake and the identity are not even
`TwoCellConvFull` (different generator count), so the faithful conjunct fails — the candidate is not an
accept-everything relation. -/
theorem bareConvCandidate_rejects_snake :
    ¬ bareConvCandidate snakeOnLeft identityOnLeft :=
  fun candidate => snake_not_convFull_identity candidate.1

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the bare-conv whiskerSum-carrier wall is UPGRADED to invariant-characterized from BOTH
count and order directions, and the Goldilocks candidate is a sound, decidable over-approximation.**

Delivered: two new bare-conv moments `rSum` / `crossSum` with full bare-conv invariance
(`TwoCellConv.rSum_eq` / `TwoCellConv.crossSum_eq`, machine-checked through the interchange critical pair); the
whiskerExchange separating pair (`whiskerExchange_convFull` faithful, `whiskerExchange_whiskerSum_eq` equal
whiskerSum `2 = 2`, `whiskerExchange_not_twoCellConv` via `crossSum` `1 ≠ 0`) proving the whiskerSum carrier is
INCOMPLETE from the ORDER direction (`bareConvCandidateWS_not_complete`) — the SECOND refutation, complementing the
COUNT-direction `adjunctionSpineTraceReconstruction_refuted`; the sound, decidable full-family candidate
(`bareConvCandidate` / `adjunctionDecideBareConvCandidate`) with soundness `bareConvCandidate_of_twoCellConv`
(bare ⟹ candidate) and non-vacuity (accepts the genuine bare Eckmann–Hilton pair, rejects the snake/identity);
and the crossSum refinement excluding the whiskerExchange pair (`bareConvCandidate_excludes_whiskerExchange`).

Deferred (the genuine, honest wall): COMPLETENESS of the candidate (candidate ⟹ bare) — whether the finite moment
family (`whiskerSum`, `rSum`, `crossSum`) is a COMPLETE invariant separating the bare-conv sub-classes inside each
`TwoCellConvFull` class — is the interchange-critical-pair coherence (Gratzer's hurdle) and stays GENUINELY OPEN.
The family catches every SINGLE whisker-functoriality generating law (four by `whiskerSum` count, `whiskerExchange`
by `crossSum` order), but global completeness over COMPOSITES is not established; no separating pair for the FULL
family is exhibited (that would name a needed FOURTH invariant), nor is the family proven complete.  So
`fxMode_hasModeRelativeConvDecision` is NOT flipped and NOT touched (its terminal disposition in
`ModeRelativeMetatheory` is unchanged, not weakened), the disposed trace/nfCell carriers are NOT re-flipped, and
the saturated/faithful decisions are untouched.  This flag records ONLY the characterized wall upgrade.  `= true`. -/
def fxMode_hasBareConvSeparatingFamilyCharacterized : Bool := true

end FX1Poly.Polygraph
