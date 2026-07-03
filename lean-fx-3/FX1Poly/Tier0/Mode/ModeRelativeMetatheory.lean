import FX1Poly.Polygraph.Computad.WordProblem
import FX1Poly.Polygraph.OmegacE.Word
import FX1Poly.Tier0.Mode.Mode

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

namespace FX1Poly.Tier0
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

/-! ## Honesty markers -/

/-- **Honesty marker.**  Full multimodal CANONICITY at dimension 2 (canonical forms for the free 2-cells modulo
the 3-polygraph) needs the 2-cell convergence, blocked by the whisker-split ambiguity (`DecidableEq`) and the
interchange critical pairs (confluence) `mode-3` identified.  The dimension-1 base
(`trivialComputad_oneCell_length_zero`, `decidableOneCellEq`) IS shipped.  `= false`. -/
def fxMode_hasMultimodalCanonicity : Bool := false

/-- **Honesty marker.**  The full mode-relative conversion DECISION (object conversion ⟺ mode 2-cell equality,
the `fib-3` keystone) needs the dimension-2 2-cell decision, blocked as above; the dimension-1 reduction
(`decidableOneCellEq`, reusing the ωcE word `DecidableEq`) IS shipped.  `= false`. -/
def fxMode_hasModeRelativeConvDecision : Bool := false

end FX1Poly.Tier0
