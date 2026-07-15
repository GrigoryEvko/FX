import FX1Poly.Polygraph.Computad.WordProblem
import FX1Poly.Polygraph.Rewriting.WordSystems.Word
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingDecisionAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvDecisionReconciliation
import FX1Poly.Axis.Mode.Mode

/-! # mode-9 — Gratzer canonicity + the mode-relative metatheory + the computad→ωcE word bridge

`mode-8` framed the free 2-category on a computad and pointed its word problem at the OmegacE engine, leaving
the encoding as a marker.  `mode-9` BUILDS that bridge for dimension 1 (no marker) and states the mode-relative
metatheory it serves.

## What the mode-relative metatheory is (Gratzer)

Multimodal dependent type theory's metatheory is MODE-RELATIVE: conversion / canonicity / decidability of the
object theory are parameterised by the MODE THEORY, and the keystone is that object-theory conversion
decidability REDUCES to decidability of the mode theory's cell equality (the full "Conv-dec = mode-dec" is the
cross-axis `fib-3`).  So the metatheoretic obligation at the mode axis is: DECIDE the mode cells.  Dimension 1
(the 1-cells = the free monoid) is decided here; dimension 2 (the 2-cells modulo the 3-polygraph) is the
deferred convergence.

## The bridge, built (dimension 1) — reusing the OmegacE word engine

The computad's 1-cells (`ModalityPath`) are free-monoid words; OmegacE already ships words with a propext-free
`DecidableEq` (`OmegacEWordCode`).  This file ENCODES the 1-cells into those word codes and reuses the engine:

  * **`ComputadGeneratorTagging`** + **`ModalityPath.encodeWordCode`** — tag each 1-cell generator with a `Nat`
    and fold a path to an `OmegacEWordCode` (the dimension-independent ωcE word serialization).
  * **`ModalityPath.encodeWordCode_composePath`** — the encoding is a MONOID HOMOMORPHISM: mode composition
    (`composePath`) maps to ωcE word append (`OmegacEWordCode.append`).  Plus `_identityPath` (unit ↦ empty)
    and `_length` (length preserved).  The free 1-cell monoid embeds in the ωcE word monoid.
  * **`FaithfulComputadTagging.decidableOneCellEq`** — with a FAITHFUL (injective) tagging, the 1-cell word
    problem is DECIDABLE: `decidable_of_iff` over `OmegacEWordCode`'s `DecidableEq` (the same propext-free
    decision the OmegacE `WordProblem` engine uses).  The mode-relative metatheory's dimension-1 base, decided
    by the existing engine — not a marker.
  * **`ModalityPath.ne_of_encodeWordCode_ne`** — the unconditional sound distinguisher (differing word codes ⟹
    differing 1-cells), no faithfulness needed.

## Multimodal canonicity (the degenerate-mode base case)

  * **`trivialComputad_oneCell_length_zero`** — over the trivial (single-mode, no-generator) computad — i.e.
    ordinary single-mode type theory — every 1-cell is the identity (length 0).  The canonical-forms base case:
    the degenerate mode theory has only trivial mode-data.

## What is DEFERRED (markers) — only the genuinely-blocked dimension-2 core

  * full multimodal canonicity at dimension 2 (`hasMultimodalCanonicity`) and the full mode-relative conversion
    decision / `fib-3` keystone (`hasModeRelativeConvDecision`) need the 2-cell convergence, which is blocked by
    TWO concrete obstacles `mode-3` identified: 2-cell `DecidableEq` is blocked by the whisker-split ambiguity
    (`composePath f g` does not determine `(f, g)`), and confluence is blocked by the interchange critical
    pairs.  Both are the real Gratzer hurdle; the dimension-1 bridge above is what IS achievable now.

Raw Lean 4 + Init, plus the OmegacE word layer (the bridge target).
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

open FX1Poly.OmegacE

/-! ## The computad → ωcE word encoding (the bridge, dimension 1) -/

/-- A **generator tagging** of a computad: a `Nat` tag for every 1-cell generator.  This is the alphabet map
that lets the computad's 1-cells be serialized as ωcE word codes (`OmegacEWordCode`, lists of `Nat` slots). -/
structure ComputadGeneratorTagging (computad : Computad) where
  /-- The tag of a 1-cell generator. -/
  tagOf : {sourceMode targetMode : computad.graph.Mode} →
    computad.graph.Modality sourceMode targetMode → Nat

/-- Fold a 1-cell (modality path) to the list of its generator tags. -/
def _root_.FX1Poly.Polygraph.ModalityPath.encodeSlots {computad : Computad} (tagging : ComputadGeneratorTagging computad) :
    {sourceMode targetMode : computad.graph.Mode} →
    ModalityPath computad.graph sourceMode targetMode → List Nat
  | _, _, .nil _ => []
  | _, _, .cons modality rest =>
      tagging.tagOf modality :: FX1Poly.Polygraph.ModalityPath.encodeSlots tagging rest

/-- ★ **Encode a 1-cell as an ωcE word code** — the bridge from the mode axis's free 1-cells into the OmegacE
word layer (`OmegacEWordCode`, the dimension-independent word serialization with a propext-free `DecidableEq`). -/
def _root_.FX1Poly.Polygraph.ModalityPath.encodeWordCode {computad : Computad} (tagging : ComputadGeneratorTagging computad)
    {sourceMode targetMode : computad.graph.Mode}
    (path : ModalityPath computad.graph sourceMode targetMode) : OmegacEWordCode :=
  { slotValues := ModalityPath.encodeSlots tagging path }

/-- The slot-encoding is a list homomorphism: composing 1-cells concatenates their tag lists. -/
theorem _root_.FX1Poly.Polygraph.ModalityPath.encodeSlots_composePath {computad : Computad}
    (tagging : ComputadGeneratorTagging computad)
    {sourceMode middleMode targetMode : computad.graph.Mode}
    (first : ModalityPath computad.graph sourceMode middleMode)
    (second : ModalityPath computad.graph middleMode targetMode) :
    ModalityPath.encodeSlots tagging (composePath first second) =
      ModalityPath.encodeSlots tagging first ++ ModalityPath.encodeSlots tagging second := by
  induction first with
  | nil _ => rfl
  | cons modality _ inductionHypothesis =>
      dsimp only [composePath, ModalityPath.encodeSlots]
      exact congrArg (List.cons (tagging.tagOf modality)) (inductionHypothesis second)

/-- ★ **The encoding is a MONOID HOMOMORPHISM**: mode composition (`composePath`) maps to ωcE word append
(`OmegacEWordCode.append`).  The free 1-cell monoid of the computad embeds into the ωcE word monoid
(`WordFreeMonoid`) — the structural heart of the dimension-1 bridge. -/
theorem _root_.FX1Poly.Polygraph.ModalityPath.encodeWordCode_composePath {computad : Computad}
    (tagging : ComputadGeneratorTagging computad)
    {sourceMode middleMode targetMode : computad.graph.Mode}
    (first : ModalityPath computad.graph sourceMode middleMode)
    (second : ModalityPath computad.graph middleMode targetMode) :
    ModalityPath.encodeWordCode tagging (composePath first second) =
      OmegacEWordCode.append (ModalityPath.encodeWordCode tagging first)
        (ModalityPath.encodeWordCode tagging second) :=
  congrArg OmegacEWordCode.mk (ModalityPath.encodeSlots_composePath tagging first second)

/-- The encoding sends the identity 1-cell (empty path) to the empty ωcE word code — the unit half of the
homomorphism. -/
theorem _root_.FX1Poly.Polygraph.ModalityPath.encodeWordCode_identityPath {computad : Computad}
    (tagging : ComputadGeneratorTagging computad) (mode : computad.graph.Mode) :
    ModalityPath.encodeWordCode tagging (identityPath mode) = OmegacEWordCode.empty := rfl

/-- The encoding preserves length: the ωcE word code's length is the 1-cell's word length. -/
theorem _root_.FX1Poly.Polygraph.ModalityPath.encodeWordCode_length {computad : Computad}
    (tagging : ComputadGeneratorTagging computad)
    {sourceMode targetMode : computad.graph.Mode}
    (path : ModalityPath computad.graph sourceMode targetMode) :
    (ModalityPath.encodeWordCode tagging path).length = path.length := by
  induction path with
  | nil _ => rfl
  | cons _ rest inductionHypothesis => exact congrArg Nat.succ inductionHypothesis

/-- The **sound dimension-1 word distinguisher** (unconditional): 1-cells with different ωcE word codes are
distinct.  Combined with `OmegacEWordCode`'s `DecidableEq`, this soundly DECIDES 1-cell inequality through the
ωcE word equality — no faithfulness hypothesis needed. -/
theorem _root_.FX1Poly.Polygraph.ModalityPath.ne_of_encodeWordCode_ne {computad : Computad}
    (tagging : ComputadGeneratorTagging computad)
    {sourceMode targetMode : computad.graph.Mode}
    {first second : ModalityPath computad.graph sourceMode targetMode}
    (codesDiffer : ModalityPath.encodeWordCode tagging first ≠ ModalityPath.encodeWordCode tagging second) :
    first ≠ second :=
  fun pathsEqual =>
    codesDiffer (congrArg
      (fun (path : ModalityPath computad.graph sourceMode targetMode) =>
        ModalityPath.encodeWordCode tagging path) pathsEqual)

/-! ## The dimension-1 word problem DECIDED (mode-relative metatheory base) -/

/-- A **faithful** generator tagging — one whose induced 1-cell encoding is INJECTIVE.  Faithfulness is exactly
what turns the ωcE word `DecidableEq` into a decision of the mode 1-cell word problem. -/
structure FaithfulComputadTagging (computad : Computad) where
  /-- The underlying tagging. -/
  tagging : ComputadGeneratorTagging computad
  /-- The encoding separates distinct 1-cells. -/
  encodeInjective : {sourceMode targetMode : computad.graph.Mode} →
    (first second : ModalityPath computad.graph sourceMode targetMode) →
    ModalityPath.encodeWordCode tagging first = ModalityPath.encodeWordCode tagging second → first = second

/-- ★ **The dimension-1 word problem is DECIDABLE** for a faithfully-tagged computad — `decidable_of_iff` over
`OmegacEWordCode`'s propext-free `DecidableEq` (the SAME decision primitive the OmegacE `WordProblem` engine
uses).  VERIFICATION NOTE: `mode-1`'s `modalityPathDecEq` ALREADY decides 1-cell equality directly and MORE
GENERALLY — for any computad with decidable modes + modality generators, with NO faithfulness/injectivity needed
— so the dimension-1 word problem was already decided there.  THIS route is the Path-B-style CROSSCHECK that the
ωcE word encoding preserves enough structure to reproduce the decision; the bridge's genuine new content is the
HOMOMORPHISM (`encodeWordCode_composePath`), not the decision. -/
def FaithfulComputadTagging.decidableOneCellEq {computad : Computad}
    (faithful : FaithfulComputadTagging computad)
    {sourceMode targetMode : computad.graph.Mode}
    (first second : ModalityPath computad.graph sourceMode targetMode) : Decidable (first = second) :=
  decidable_of_iff
    (ModalityPath.encodeWordCode faithful.tagging first =
      ModalityPath.encodeWordCode faithful.tagging second)
    ⟨faithful.encodeInjective first second,
      fun pathsEqual => congrArg
        (fun (path : ModalityPath computad.graph sourceMode targetMode) =>
          ModalityPath.encodeWordCode faithful.tagging path) pathsEqual⟩

/-! ## A concrete tagging: the adjunction seed -/

/-- The adjunction seed's generator tagging — `left ↦ 0`, `right ↦ 1` (the two-slot scaffold). -/
def adjunctionTagging : ComputadGeneratorTagging adjunctionModeSignature where
  tagOf := fun modality =>
    match modality with
    | AdjunctionModality.left => 0
    | AdjunctionModality.right => 1

/-- Smoke: the composite 1-cell `left then right` encodes to the ωcE word code `[0, 1]` — the bridge computes on
a genuine non-degenerate 1-cell. -/
theorem adjunctionLeftThenRight_encodeWordCode :
    (ModalityPath.encodeWordCode adjunctionTagging adjunctionLeftThenRight).slotValues = [0, 1] := rfl

/-! ## Multimodal canonicity (the degenerate-mode base case) -/

/-- ★ **Canonicity at the trivial mode theory**: over the trivial (single-mode, no-generator) computad — i.e.
ordinary single-mode type theory — every 1-cell has word length 0, i.e. IS the identity.  The mode-relative
metatheory's canonical-forms base case: the degenerate mode theory carries only trivial mode-data.  (`cons` is
impossible — its modality generator inhabits `Empty`.) -/
theorem trivialComputad_oneCell_length_zero
    {sourceMode targetMode : trivialModeSignature.graph.Mode}
    (path : ModalityPath trivialModeSignature.graph sourceMode targetMode) : path.length = 0 := by
  cases path with
  | nil _ => rfl
  | cons modality _ => exact (modality : Empty).elim

/-- Over the trivial computad any two parallel 1-cells are EQUAL (both are the identity — `cons` is impossible).
The uniqueness behind the trivial faithful tagging below. -/
theorem trivialComputad_oneCell_unique
    {sourceMode targetMode : trivialModeSignature.graph.Mode}
    (first second : ModalityPath trivialModeSignature.graph sourceMode targetMode) : first = second := by
  cases first with
  | nil _ =>
      cases second with
      | nil _ => rfl
      | cons modality _ => exact (modality : Empty).elim
  | cons modality _ => exact (modality : Empty).elim

/-- ★ A CONCRETE faithful tagging — the trivial computad — so the bridge's `decidableOneCellEq` is NON-VACUOUS:
it genuinely produces a `Decidable` 1-cell equality (degenerate here, since all 1-cells coincide; the general
non-degenerate decision is `mode-1`'s `modalityPathDecEq`). -/
def trivialFaithfulComputadTagging : FaithfulComputadTagging trivialModeSignature where
  tagging := { tagOf := fun modality => (modality : Empty).elim }
  encodeInjective := fun first second _ => trivialComputad_oneCell_unique first second

/-! ## The mode-relative metatheory parameter -/

/-- The **mode-relative metatheory parameter** (Gratzer): the object theory's conversion metatheory is
parameterised by decidability of the mode 2-cells — exactly `mode-3`'s `DecidableTwoCellConvFor`.  Dimension 1
(`decidableOneCellEq`) is discharged via the word bridge above; this is the dimension-2 obligation the full
metatheory (`fib-3`) consumes. -/
abbrev _root_.FX1Poly.Polygraph.Computad.modeRelativeParameter (computad : Computad) : Type :=
  DecidableTwoCellConvFor computad

/-! ## The SATURATED mode-relative decision at the walking adjunction (scoped, per-presentation)

The general parameter above asks for decidability of the FREE `TwoCellConv` over ANY computad — that stays
undecided (`fxMode_hasModeRelativeConvDecision = false`, bound to the deferred free trace route
`(traceDecision, reconstruct)` of `AdjunctionTwoCellWordProblem`).  But for the walking adjunction WITH its
triangle identities, the categorically-correct notion of "mode 2-cell equality" is the SATURATED convertibility
`SaturatedTwoCellConv` (the free convertibility augmented with the two snake equations as generating relations,
where the snakes provably collapse — `leftSnakeSaturatedButNotFree` shows they do NOT collapse freely).  That
per-presentation relation IS decided, unconditionally and zero-axiom, by the shipped fib-3 matching decision.
This section reconciles that shipped decision into the mode-relative route as a SCOPED marker — no new math,
backed by a named proven term — WITHOUT overclaiming the general/free flag. -/

/-- The **saturated mode-relative parameter at the walking adjunction** — the per-presentation instance of the
Gratzer mode-relative parameter for the adjunction mode theory `μ_affine ⊣ μ_affine†` WITH its triangle
identities.  Where the general `Computad.modeRelativeParameter` demands decidability of the FREE `TwoCellConv`,
this demands decidability of the SATURATED `SaturatedTwoCellConv` — the coarser, categorically-correct relation
for a genuine adjunction (the snakes are identities).  Its type is `mode-3`'s saturated interface
`DecidableSaturatedTwoCellConvFor`. -/
abbrev adjunctionSaturatedModeRelativeParameter : Type :=
  DecidableSaturatedTwoCellConvFor

/-- ★ **The saturated mode-relative conversion decision at the walking adjunction, DISCHARGED.**  The shipped
unconditional `decideSaturatedTwoCellConv_ofSeed` (the fib-3 saturated matching decision, zero-axiom via the
boundary `matchingOf` `DecidableEq`) inhabits the saturated mode-relative parameter: every parallel pair of free
2-cells at the seed is decided against the saturated (triangle-augmented) relation.  This is the honest, backed
reconciliation of the shipped saturated decision into the mode-relative route — scoped to the walking adjunction
and to the saturated relation.  It does NOT inhabit the general/free `Computad.modeRelativeParameter` (that is
the finer `TwoCellConv`, general over any computad), so it correctly does NOT flip
`fxMode_hasModeRelativeConvDecision`. -/
@[reducible] def adjunctionSaturatedModeRelativeConvDecision : adjunctionSaturatedModeRelativeParameter :=
  decideSaturatedTwoCellConv_ofSeed

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the SATURATED mode-relative conversion decision at the walking adjunction.**  The
per-presentation, saturated instance of the mode-relative conv decision is DECIDED unconditionally and
zero-axiom by `adjunctionSaturatedModeRelativeConvDecision` (= the shipped `decideSaturatedTwoCellConv_ofSeed`):
the adjunction mode theory WITH its triangle identities has decidable mode 2-cell equality.  This is the honest
SCOPED true statement.  It does NOT flip the general/free `fxMode_hasModeRelativeConvDecision` below — that
flag's parameter is the FREE `TwoCellConv` (finer: the snakes provably do NOT collapse,
`leftSnakeSaturatedButNotFree`) over ANY computad, bound to the deferred free trace route
`(traceDecision, reconstruct)`.  Nor does it flip the general `fxMode_hasDecidableTwoCellEquality`, which is
walled by the rung-3 undecidability of arbitrary finite presentations (Markov 1947 / Post 1947).  `= true`. -/
def fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction : Bool := true

/-- **Honesty marker.**  Full multimodal CANONICITY at dimension 2 (canonical forms for the free 2-cells modulo
the 3-polygraph) needs the 2-cell convergence, blocked by the whisker-split ambiguity (`DecidableEq`) and the
interchange critical pairs (confluence) `mode-3` identified.  The dimension-1 base
(`trivialComputad_oneCell_length_zero`, `decidableOneCellEq`) IS shipped.  `= false`. -/
def fxMode_hasMultimodalCanonicity : Bool := false

/-- **Honesty marker — PERMANENT-AS-STATED disposition; a RELATION MISMATCH now MECHANIZED from BOTH sides
(fib-3 Wave-1(b) TERMINAL).**  The full, GENERAL
mode-relative conversion DECISION over the FREE `TwoCellConv` (object conversion ⟺ mode 2-cell equality, the
`fib-3` keystone) is owed `(traceDecision, reconstruct)` of `AdjunctionTwoCellWordProblem` at the BARE
`TwoCellConv` parameter; the dimension-1 reduction (`decidableOneCellEq`, reusing the ωcE word `DecidableEq`) IS
shipped.  The BARE parameter is an OVER-FINE congruence — the free strict-2-category 2-cell congruence MINUS
whisker-by-1-cell functoriality (`fxMode_hasInterchangeAndWhiskerFunctoriality = false`) — and BOTH natural
readback carriers are machine-witnessed to MISS it, from opposite sides:

  * `traceDecision` (an UNCONDITIONAL `Decidable (SpineTraceEquiv …)`) is now DISCHARGED ungated —
    `adjunctionSpineTraceDecision` (via `decideAtomicTraceEquivOfChainedSeed` + FREE-5
    `spineTraceEquiv_iff_atomicTraceEquiv`), with NO arc gate.  (The arc-gated `decidableSpineTraceEquiv_of` is now
    a non-blocking alternative, not this leg's wall.)
  * the SPINE carrier is strictly COARSER than the cell: the `reconstruct` leg `SpineTraceEquiv → TwoCellConv` at
    BARE `TwoCellConv` is provably FALSE — now MECHANIZED as `adjunctionSpineTraceReconstruction_refuted` (FREE-2):
    `atomFrame adjunctionUnitSpineAtom` shares the unit's spine yet is NOT `TwoCellConv` to the bare `gen unit`,
    proven via the bare-conv invariant `RawTwoCellExpr.whiskerSum` (`TwoCellConv.whiskerSum_eq`, preserved by every
    `TwoCellStep` including interchange — it scores the two `2` vs `0`), the `¬` earlier passes only argued.
  * the interchange-free NORMAL FORM `nfCell` carrier is strictly FINER than bare conv: the Eckmann–Hilton
    parallel-units pair is `TwoCellConv` yet has DISTINCT normal forms — machine-checked
    `interchangeFreeNormalForm_notCompleteInvariantForBareConv` (= `adjunctionInterchangeIsNonDegenerate`), so a
    "normalize both, compare" decision returns FALSE NEGATIVES.  (The shipped FREE-4
    `RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` lands in the categorically-FAITHFUL `TwoCellConvFull`, where
    the FAITHFUL decision IS unconditional — `adjunctionDecideTwoCellConvFull`,
    `fxMode_hasFaithfulTwoCellDecisionModuloTrace = true` — but bare `TwoCellConv` is strictly finer, the snakes
    provably not collapsing, `leftSnakeSaturatedButNotFree`.)
  * the additive whisker word-code `RawTwoCellExpr.wordCode` — COMPLETE on the single-generator nil-whisker
    fragment (`frameWord_twoCellConv_iff`, `wordCode = phi` injective there) — is strictly COARSER than bare conv on
    GENERAL cells: machine-refuted `wordCode_not_complete` (a two-generator Godement pair `wordCodeCollisionLeft` /
    `wordCodeCollisionRight`, both `isInterchangeNormal`, `TwoCellConvFull` with EQUAL `wordCode` `5 = 5` yet
    `coCrossSum` `1` vs `0`, hence NOT bare — `wordCodeCollision_not_twoCellConv`), so NO additive
    `Σ_gen φ(pattern)` word-code decides bare conv either; the complete invariant is strictly the per-generator
    pattern MULTISET.
  * the per-generator pattern MULTISET `RawTwoCellExpr.patternMultiplicity` — the SUP of that whole additive
    scalar tower (`whiskerSum` / `rSum` / `crossSum` / `leftCount` / `coCrossSum` / `nestedCrossSum` / `wordCode`
    each factor through it) — is now SHIPPED as a machine-checked SOUND bare-conv invariant
    (`TwoCellConv.patternMultiplicity_eq`, preserved by every `TwoCellStep` including interchange, which PERMUTES
    generators while preserving each pattern, so the order-forgetting multiset is the invariant residual — the
    Eckmann–Hilton order-collapse), and it SEPARATES the r4 `wordCode` collision where every additive scalar
    collided (`wcc_not_conv_viaMultiset`, coordinate `[L]` scoring `1` vs `0`), with its equality DECIDABLE
    zero-axiom via the sorted canonical carrier `RawTwoCellExpr.sortedPatternMultiset` + `listListBoolDecEq`
    (NEVER `Multiset` / `Quot`).  This is the CEILING of the scalar tower — the first non-additive bare invariant —
    but it is NOT proven complete: per the trace-monoid settlement the complete invariant is the strictly FINER
    ordered Cartier–Foata clique-SEQUENCE (a flat order-forgetting bag is the same species of shadow one level up),
    and flat-multiset completeness within a full-conv class is the interchange critical-pair coherence (Gratzer),
    NOT fabricated.  Crucially the general decision is NOT beyond structural methods — Makkai's free-strict-ω-cat
    word-problem procedure and Delpeuch–Vicary's strongly-normalizing exchange-move rewriting (quadratic) DECIDE
    the planar interchange word problem via that clique-sequence normal form; the only research-open frontier is
    the dimension-3 braided / Gray lift (unknotting-hard), which the PLANAR bare 2-cell never reaches
    (`fxMode_hasBareConvFlatPatternMultisetSoundAndSeparating = true`).

fib-3 is NOT blocked on this flag: its keystone is discharged at the granularity the MTT fibration consumes — the
SATURATED modulo-triangles relation `SaturatedTwoCellConv`
(`fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction = true`,
`adjunctionSaturatedModeRelativeConvDecision`) — and the faithful free relation is decided too; bare `TwoCellConv`
sits strictly below both and is kept honestly live as an over-fine relation, per Gratzer Cor. 8.10 (conversion is
decided when 2-cell EQUALITY is, which the faithful/saturated decisions supply).  Bare `TwoCellConv`'s decidability
is GENUINELY OPEN (the interchange critical-pair convergence, Gratzer's coherence hurdle) — re-openable, NOT
undecidability-walled (that is FLAG A, rung-3 Markov/Post over ARBITRARY presentations).  The owed statement is
UNCHANGED (no weakening); the flag stays `false` as a permanent-as-stated terminal disposition.  The r7
TERMINAL reconciliation — the master flag is NOT dischargeable by any shipped decision, because bare
`TwoCellConv` is STRICTLY FINER than every decided notion — is consolidated and machine-backed in
`BareConvDecisionReconciliation` (`fxMode_hasBareConvDecisionDeepWall = true`,
`bareConvDecisionReconciliation`).  `= false`. -/
def fxMode_hasModeRelativeConvDecision : Bool := false

/-- ★ **The flag-B r7 TERMINAL link (machine-checked): the master flag is an HONEST DEEP WALL, not a discharge.**
`fxMode_hasModeRelativeConvDecision` (the BARE `TwoCellConv` decision) STAYS `false`, and the consolidated
reconciliation marker `fxMode_hasBareConvDecisionDeepWall` (`BareConvDecisionReconciliation`, backed by
`bareConvDecisionReconciliation`: the faithful `TwoCellConvFull` and saturated decisions are total, the Godement
pair witnesses bare ⊊ `TwoCellConvFull`, and the realizable readback lands at `TwoCellConvFull` not bare) is
`true`.  Both by `rfl` — the honest terminal of the flag-B arc: the shipped faithful / saturated decisions
decide STRICTLY COARSER (categorically-correct) relations, so they do NOT discharge the strictly-finer bare
flag, which is re-openable but NOT undecidability-walled. -/
theorem modeRelativeConvDecision_isDeepWall_notDischargeable :
    fxMode_hasModeRelativeConvDecision = false
    ∧ fxMode_hasBareConvDecisionDeepWall = true :=
  ⟨rfl, rfl⟩

end FX1Poly.Axis
