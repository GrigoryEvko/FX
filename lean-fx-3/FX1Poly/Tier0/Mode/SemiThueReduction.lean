import FX1Poly.Polygraph.Computad.Signature
import FX1Poly.Polygraph.Rewriting.Confluence.KnuthBendixCompletion

/-! # Tier0/Mode/SemiThueReduction — the Burroni bridge: semi-Thue systems ARE one-object 2-polygraphs

FLAG A (`FX1Poly.Tier0.fxMode_hasDecidableTwoCellEquality = false`, `Mode.lean`) is the rung-3 wall of the
2-cell word problem: 1-cell convertibility under the 2-cells of an ARBITRARY finite one-object 2-polygraph is
the word problem of the finitely presented monoid it presents, which is undecidable (Markov 1947, Post 1947;
the polygraphic framing is Burroni's, *Higher-dimensional word problems*, Theoret. Comput. Sci. 115 (1993)).

Until now the wall rested on a PROSE citation.  This file STRENGTHENS it to a machine-checked reduction: the
Burroni embedding *semi-Thue system ⟷ one-object 2-polygraph 1-cell convertibility*, mechanized over the SAME
generic computad carrier (`ModalityPath` + `composePath`, from `Polygraph/Computad/Signature`) the mode-axis
walkers use.  The classical undecidable INSTANCE stays cited (see the honest boundary below); what is
mechanized is the BRIDGE that makes the wall a reduction, not an analogy.

## The three pieces

  * **`SemiThueSystem` shape** — an alphabet `Letter` (fully generic; NO `DecidableEq`, because the point is
    undecidability at arbitrary alphabets), words `List Letter`, rules `List (List Letter × List Letter)`, the
    classical single monoid-presentation step `SemiThueStep` (a rule fires in a two-sided sandwich
    `pref ++ lhs ++ suf ↦ pref ++ rhs ++ suf`, deliberately ONE constructor), and the Thue CONGRUENCE
    `ThueCong` = the equivalence closure `⟷*` (REUSING the shipped `FX1Poly.Core.EquationalTheory`, so
    `ThueCong` is definitionally the same shape as the walking-involution `EquationalTheory InvolutionRewrite`
    of Tier C).  The symmetric closure is essential — the word problem is the CONGRUENCE, not directed
    reachability (which is all the Coq `SR` predicate mechanizes; see the boundary note).

  * **The 2-polygraph encoding** — a one-object quiver `encodedGraph Letter` whose 1-cell GENERATORS ARE the
    alphabet (`Modality point point := Letter`), so its free 1-cells `ModalityPath (encodedGraph Letter)` are
    the free monoid `Letter*` and `composePath` is word concatenation.  Words embed as `encodeWord` (with
    inverse `decodeWord`, a monoid iso: `encodeWord_append`, `decodeWord_compose`, `decode_encode`).  The
    encoded convertibility `EncodedConv` is the genuine 2-category congruence: a rule fires as an atomic
    `rule`, and CONTEXT is rebuilt by SEPARATE left/right WHISKER constructors (`whiskerLeft` / `whiskerRight`)
    plus `refl`/`symm`/`trans` — exactly the one-object specialization where whiskering degenerates to word
    concatenation.  The rules land as ACTUAL generating 2-cells of a `ModeSignature` value
    (`encodedModeSignature`, `ruleGivesTwoCell` / `twoCellGivesRule`): the Burroni identification made a
    concrete `ModeSignature`.

  * **The reduction** — `semiThue_iff_encodedTwoCell` : `ThueCong rules u v ↔ EncodedConv rules (encodeWord u)
    (encodeWord v)`, BOTH directions by induction.  It is CONTENTFUL, not `Iff.rfl`: forward, the Thue
    two-sided sandwich (one constructor) is rebuilt as `whiskerLeft ∘ whiskerRight ∘ rule` and the carriers
    are reconciled by `encodeWord_append` + `composePath_assoc` (`encodeWord_sandwich`); backward, the whisker
    constructors are pushed back through `decodeWord_compose` and closed on `decode_encode`.  This is the
    honest Burroni faithfulness content.

## Non-vacuity — the involution 1-rule system (tied to Tier C)

`involutionThueRules := [([s, s], [])]` is the semi-Thue form of the Tier-C oriented rule `InvolutionRewrite`
(`s.s ↦ id`).  `involutionThue_positive` decides `s.s ~ id` TRUE (one rule application), and
`involutionThue_separation` decides `s ~ id` FALSE via the Z/2 parity homomorphism `involutionWordParity`
(the SAME invariant `involutionParityOf` that Tiers B and C use).  So the reduction genuinely discriminates,
and the instance is an explicitly DECIDABLE point of the otherwise-undecidable general semi-Thue family —
the rung-2/Tier-C-vs-rung-3 boundary made concrete.  (The tie to Tier C is prose + shared invariant: the two
carriers differ — `involutionGraph` uses the `InvolutionModality` inductive, this encoding uses
`Modality := fun _ _ => InvolutionLetter` — so a machine graph-iso is not attempted here; the mechanized
content is `semiThue_iff_encodedTwoCell` on the involution words.)

## Honest boundary (do NOT overclaim)

MECHANIZED here = the BRIDGE (Burroni faithfulness): `ThueCong ⟷ EncodedConv`.  CITED, not mechanized = the
EXISTENCE of a finite semi-Thue system whose `ThueCong` is undecidable (Post 1947 / Markov 1947; Markov's
construction yields a 2-generator/33-relation semigroup, Matiyasevich–Sénizergues a 2-generator/3-relation
one).  Mechanizing that undecidability needs a COMPUTABILITY SUBSTRATE — a Turing-machine (or tag-system)
halting problem reduced INTO string rewriting.  That is exactly what the Coq undecidability library does
(Forster–Heiter–Smolka, ITP 2018, `TM ⪯ SRH ⪯ SR`): it mechanizes the halting-to-string-rewriting reduction,
but stays at the STRING level and does NOT build the polygraph/2-category bridge.  This file is the
complementary half — the polygraph bridge — leaving the undecidable instance correctly CITED.  The two
markers state the boundary exactly: `fxMode_hasSemiThueReductionMechanized = true` (the bridge) vs the
ledger's `fxMode_hasArbitraryTwoCellUndecidabilityReduction = false` (the full reduction to a known-undecidable
instance).  FLAG A itself stays `false` — the general decision genuinely does not exist.

Lives in `Tier0/Mode/` (cross-layer top file — the ledger pins it) although its declarations are in
`FX1Poly.Polygraph`, mirroring `DecidableCeilingLedger` / `ExhibitedConvergentDecision`.  Raw Lean 4 + Init;
core `List.append_assoc` / `List.append_nil` leak `propext` in this Init-only setting, so this file provides
its own structural `appendAssocClean` / `appendNilClean`; every other step is a structural induction over the
shipped audit-clean `composePath_assoc` and the `EquationalTheory` / `EncodedConv` inductives.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Core

/-! ## Clean local list-append helpers (core `append_assoc` / `append_nil` leak propext) -/

/-- `l ++ [] = l`, by structural induction — the propext-free replacement for core `List.append_nil`. -/
theorem appendNilClean {Letter : Type} (word : List Letter) : word ++ [] = word := by
  induction word with
  | nil => rfl
  | cons head tail inductiveHypothesis => exact congrArg (fun rest => head :: rest) inductiveHypothesis

/-- `(a ++ b) ++ c = a ++ (b ++ c)`, by structural induction — the propext-free replacement for core
`List.append_assoc`. -/
theorem appendAssocClean {Letter : Type} (first second third : List Letter) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  induction first with
  | nil => rfl
  | cons head tail inductiveHypothesis => exact congrArg (fun rest => head :: rest) inductiveHypothesis

/-! ## The semi-Thue system: single step + Thue congruence -/

/-- ★ A **single semi-Thue rewrite step**: some rule `(lhs, rhs)` fires inside a two-sided context
`pref ++ _ ++ suf`.  This is the classical monoid-presentation step — deliberately ONE constructor with a
sandwich, so it is contentful against `EncodedConv`'s SEPARATE left/right whiskers. -/
inductive SemiThueStep {Letter : Type} (rules : List (List Letter × List Letter)) :
    List Letter → List Letter → Prop where
  /-- A rule `(lhs, rhs) ∈ rules` fires with prefix `pref` and suffix `suf`. -/
  | rewrite (pref suf lhs rhs : List Letter) (mem : (lhs, rhs) ∈ rules) :
      SemiThueStep rules (pref ++ lhs ++ suf) (pref ++ rhs ++ suf)

/-- ★ The **Thue congruence** `⟷*` generated by a semi-Thue system — the equivalence closure of the single
step, REUSING the shipped `FX1Poly.Core.EquationalTheory`.  This is the genuine monoid word problem (the
SYMMETRIC closure, not merely directed reachability). -/
abbrev ThueCong {Letter : Type} (rules : List (List Letter × List Letter)) :
    List Letter → List Letter → Prop :=
  EquationalTheory (SemiThueStep rules)

/-- A rule membership yields a single-step Thue conversion `lhs ~ rhs` (empty prefix and suffix). -/
theorem thueCong_of_mem {Letter : Type} {rules : List (List Letter × List Letter)}
    {lhs rhs : List Letter} (mem : (lhs, rhs) ∈ rules) : ThueCong rules lhs rhs := by
  have raw : SemiThueStep rules (lhs ++ []) (rhs ++ []) := SemiThueStep.rewrite [] [] lhs rhs mem
  rw [appendNilClean, appendNilClean] at raw
  exact EquationalTheory.rule raw

/-! ## Congruence of the single step and of the Thue closure under whiskering -/

/-- Reassociate a left-whiskered sandwich onto the sandwich shape: `w ++ (pref ++ mid ++ suf)` groups as
`(w ++ pref) ++ mid ++ suf`. -/
theorem whiskerLeftReassoc {Letter : Type} (whiskerWord pref mid suf : List Letter) :
    whiskerWord ++ (pref ++ mid ++ suf) = (whiskerWord ++ pref) ++ mid ++ suf := by
  rw [appendAssocClean pref mid suf, appendAssocClean (whiskerWord ++ pref) mid suf,
      appendAssocClean whiskerWord pref (mid ++ suf)]

/-- Reassociate a right-whiskered sandwich onto the sandwich shape: `(pref ++ mid ++ suf) ++ w` groups as
`pref ++ mid ++ (suf ++ w)`. -/
theorem whiskerRightReassoc {Letter : Type} (pref mid suf whiskerWord : List Letter) :
    (pref ++ mid ++ suf) ++ whiskerWord = pref ++ mid ++ (suf ++ whiskerWord) := by
  rw [appendAssocClean (pref ++ mid) suf whiskerWord]

/-- A single semi-Thue step is preserved by LEFT whiskering (prepending a word). -/
theorem semiThueStep_whiskerLeft {Letter : Type} {rules : List (List Letter × List Letter)}
    {before after : List Letter} (step : SemiThueStep rules before after) (whiskerWord : List Letter) :
    SemiThueStep rules (whiskerWord ++ before) (whiskerWord ++ after) := by
  cases step with
  | rewrite pref suf lhs rhs mem =>
      rw [whiskerLeftReassoc whiskerWord pref lhs suf, whiskerLeftReassoc whiskerWord pref rhs suf]
      exact SemiThueStep.rewrite (whiskerWord ++ pref) suf lhs rhs mem

/-- A single semi-Thue step is preserved by RIGHT whiskering (appending a word). -/
theorem semiThueStep_whiskerRight {Letter : Type} {rules : List (List Letter × List Letter)}
    {before after : List Letter} (step : SemiThueStep rules before after) (whiskerWord : List Letter) :
    SemiThueStep rules (before ++ whiskerWord) (after ++ whiskerWord) := by
  cases step with
  | rewrite pref suf lhs rhs mem =>
      rw [whiskerRightReassoc pref lhs suf whiskerWord, whiskerRightReassoc pref rhs suf whiskerWord]
      exact SemiThueStep.rewrite pref (suf ++ whiskerWord) lhs rhs mem

/-- The Thue congruence is preserved by LEFT whiskering (by induction on the equivalence closure). -/
theorem thueCong_whiskerLeft {Letter : Type} {rules : List (List Letter × List Letter)}
    (whiskerWord : List Letter) {before after : List Letter} (conv : ThueCong rules before after) :
    ThueCong rules (whiskerWord ++ before) (whiskerWord ++ after) := by
  induction conv with
  | rule step => exact EquationalTheory.rule (semiThueStep_whiskerLeft step whiskerWord)
  | refl point => exact EquationalTheory.refl _
  | symm _ inductiveHypothesis => exact EquationalTheory.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EquationalTheory.trans firstInductiveHypothesis secondInductiveHypothesis

/-- The Thue congruence is preserved by RIGHT whiskering (by induction on the equivalence closure). -/
theorem thueCong_whiskerRight {Letter : Type} {rules : List (List Letter × List Letter)}
    {before after : List Letter} (conv : ThueCong rules before after) (whiskerWord : List Letter) :
    ThueCong rules (before ++ whiskerWord) (after ++ whiskerWord) := by
  induction conv with
  | rule step => exact EquationalTheory.rule (semiThueStep_whiskerRight step whiskerWord)
  | refl point => exact EquationalTheory.refl _
  | symm _ inductiveHypothesis => exact EquationalTheory.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EquationalTheory.trans firstInductiveHypothesis secondInductiveHypothesis

/-! ## The one-object 2-polygraph carrier: the alphabet AS 1-cell generators -/

/-- The single 0-cell of the encoding polygraph. -/
inductive EncodedMode where
  /-- The unique object. -/
  | point

/-- ★ The **one-object quiver** whose 1-cell GENERATORS ARE the alphabet: one mode `point`, and
`Modality point point := Letter`.  Its free 1-cells `ModalityPath (encodedGraph Letter) point point` are the
free monoid `Letter*`, and `composePath` is word concatenation — Burroni's "a monoid presentation is a
one-0-cell 2-polygraph". -/
def encodedGraph (Letter : Type) : ModeGraph where
  Mode := EncodedMode
  Modality := fun _ _ => Letter

/-- Embed a word as a free 1-cell (the identity 1-cell for the empty word, `cons` for each letter). -/
def encodeWord {Letter : Type} :
    List Letter → ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point
  | [] => ModalityPath.nil (graph := encodedGraph Letter) EncodedMode.point
  | letter :: rest => ModalityPath.cons letter (encodeWord rest)

/-- Read a free 1-cell back to a word (the inverse of `encodeWord`).  Generic over the endpoints because the
one-object quiver forces every mode to `point`; defined through `ModalityPath.rec` so it reduces DEFINITIONALLY
on `nil` / `cons` (an indexed-family `match` would only give propositional equations).  `noncomputable`
because the kernel recursor has no compiled code — this is a proof-only readback, never run. -/
noncomputable def decodeWord {Letter : Type} {source target : EncodedMode}
    (path : ModalityPath (encodedGraph Letter) source target) : List Letter :=
  ModalityPath.rec (motive := fun _ _ _ => List Letter)
    (fun _mode => [])
    (fun letterModality _rest tailDecoded => letterModality :: tailDecoded)
    path

/-- `decodeWord` inverts `encodeWord` on words (the "back" half of the monoid iso). -/
theorem decode_encode {Letter : Type} (word : List Letter) : decodeWord (encodeWord word) = word := by
  induction word with
  | nil => rfl
  | cons letter rest inductiveHypothesis =>
      exact congrArg (fun tail => letter :: tail) inductiveHypothesis

/-- `encodeWord` is a monoid homomorphism: word concatenation is `composePath`. -/
theorem encodeWord_append {Letter : Type} (first second : List Letter) :
    encodeWord (first ++ second) = composePath (encodeWord first) (encodeWord second) := by
  induction first with
  | nil => rfl
  | cons letter rest inductiveHypothesis =>
      exact congrArg (ModalityPath.cons letter) inductiveHypothesis

/-- The sandwich hom: a two-sided context encodes as a doubly-whiskered composite.  This is where
`encodeWord_append` and the audit-clean `composePath_assoc` reconcile the Thue sandwich with the 2-category
left/right whiskers. -/
theorem encodeWord_sandwich {Letter : Type} (pref mid suf : List Letter) :
    encodeWord (pref ++ mid ++ suf)
      = composePath (encodeWord pref) (composePath (encodeWord mid) (encodeWord suf)) := by
  rw [encodeWord_append, encodeWord_append, composePath_assoc]

/-- `decodeWord` reduces on `nil` (the readback of the identity 1-cell is the empty word). -/
theorem decodeWord_nil {Letter : Type} (mode : EncodedMode) :
    decodeWord (ModalityPath.nil (graph := encodedGraph Letter) mode) = [] := rfl

/-- `decodeWord` reduces on `cons` (the head modality IS a letter — the `.rec` definition makes this `rfl`). -/
theorem decodeWord_cons {Letter : Type} {sourceMode middleMode targetMode : EncodedMode}
    (letterModality : (encodedGraph Letter).Modality sourceMode middleMode)
    (rest : ModalityPath (encodedGraph Letter) middleMode targetMode) :
    decodeWord (ModalityPath.cons letterModality rest)
      = (letterModality : Letter) :: decodeWord rest := rfl

/-- `decodeWord` is a monoid homomorphism, proved by induction on the LENGTH of the first path (a plain `Nat`
recursion, so no `induction` on the concretely-graphed indexed family — the repo's `…_ofLength` idiom). -/
theorem decodeWord_compose_ofLength {Letter : Type} :
    ∀ (bound : Nat) {source middle target : EncodedMode}
      (first : ModalityPath (encodedGraph Letter) source middle)
      (second : ModalityPath (encodedGraph Letter) middle target),
      first.length = bound →
      decodeWord (composePath first second) = decodeWord first ++ decodeWord second := by
  intro bound
  induction bound with
  | zero =>
      intro _source _middle _target first second lengthZero
      match first with
      | .nil _ => rfl
      | .cons _letter _rest => exact absurd lengthZero (by intro contra; cases contra)
  | succ predecessor inductiveHypothesis =>
      intro _source _middle _target first second lengthSucc
      match first with
      | .nil _ => exact absurd lengthSucc (by intro contra; cases contra)
      | .cons letter rest =>
          have restLength : rest.length = predecessor := Nat.succ.inj lengthSucc
          have recurse : decodeWord (composePath rest second) = decodeWord rest ++ decodeWord second :=
            inductiveHypothesis rest second restLength
          let letterAsLetter : Letter := letter
          show decodeWord (ModalityPath.cons letter (composePath rest second))
            = decodeWord (ModalityPath.cons letter rest) ++ decodeWord second
          exact congrArg (fun tail => letterAsLetter :: tail) recurse

/-- `decodeWord` is a monoid homomorphism: `composePath` reads back to word concatenation. -/
theorem decodeWord_compose {Letter : Type} {source middle target : EncodedMode}
    (first : ModalityPath (encodedGraph Letter) source middle)
    (second : ModalityPath (encodedGraph Letter) middle target) :
    decodeWord (composePath first second) = decodeWord first ++ decodeWord second :=
  decodeWord_compose_ofLength first.length first second rfl

/-! ## The encoded 2-cell convertibility (the one-object 2-polygraph congruence) -/

/-- ★ The **encoded convertibility** — the 1-cell convertibility of the one-object 2-polygraph.  A rule fires
as the atomic `rule`; CONTEXT is rebuilt by SEPARATE left/right whisker constructors (in a one-object
polygraph, whiskering IS word concatenation); `refl`/`symm`/`trans` close it into the congruence.  Keeping the
whiskers separate from the rule is exactly the 2-category structure, and is why the reduction is contentful
(not `Iff.rfl`). -/
inductive EncodedConv {Letter : Type} (rules : List (List Letter × List Letter)) :
    ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point →
    ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point → Prop where
  /-- A rule `(lhs, rhs) ∈ rules` is a generating 2-cell between the encoded words. -/
  | rule {lhs rhs : List Letter} (mem : (lhs, rhs) ∈ rules) :
      EncodedConv rules (encodeWord lhs) (encodeWord rhs)
  /-- Left whiskering by a 1-cell prefix. -/
  | whiskerLeft (prefixCell : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point)
      {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
      (inner : EncodedConv rules left right) :
      EncodedConv rules (composePath prefixCell left) (composePath prefixCell right)
  /-- Right whiskering by a 1-cell suffix. -/
  | whiskerRight {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
      (inner : EncodedConv rules left right)
      (suffixCell : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) :
      EncodedConv rules (composePath left suffixCell) (composePath right suffixCell)
  /-- Reflexivity. -/
  | refl (word : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) :
      EncodedConv rules word word
  /-- Symmetry. -/
  | symm {left right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point} :
      EncodedConv rules left right → EncodedConv rules right left
  /-- Transitivity. -/
  | trans {left middle right : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point} :
      EncodedConv rules left middle → EncodedConv rules middle right → EncodedConv rules left right

/-! ## Faithful landing: the rules ARE the generating 2-cells of a `ModeSignature` -/

/-- The generating 2-cells of the encoded signature at a parallel pair of 1-cells: the rules whose encoded
boundary is exactly that pair.  An `abbrev` so the `Subtype` projections read through it. -/
abbrev encodedRuleTwoCell {Letter : Type} (rules : List (List Letter × List Letter))
    (source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point) : Type :=
  { pair : List Letter × List Letter //
      pair ∈ rules ∧ encodeWord pair.1 = source ∧ encodeWord pair.2 = target }

/-- ★ The **encoded 2-polygraph** — the semi-Thue system AS an actual `ModeSignature` value: the one-object
quiver `encodedGraph`, with the rules as generating 2-cells boundaried by their encoded words.  This IS the
Burroni identification "semi-Thue systems are one-object 2-polygraphs", inhabited. -/
def encodedModeSignature {Letter : Type} (rules : List (List Letter × List Letter)) : ModeSignature where
  graph := encodedGraph Letter
  twoCell {source target} :=
    match source, target with
    | .point, .point => encodedRuleTwoCell rules

/-- Faithfulness (rules → 2-cells): every rule gives a generating 2-cell between its encoded words. -/
def ruleGivesTwoCell {Letter : Type} (rules : List (List Letter × List Letter))
    {lhs rhs : List Letter} (mem : (lhs, rhs) ∈ rules) :
    (encodedModeSignature rules).twoCell (encodeWord lhs) (encodeWord rhs) :=
  ⟨(lhs, rhs), mem, rfl, rfl⟩

/-- Faithfulness (2-cells → rules): every generating 2-cell of the encoded signature comes from a rule. -/
theorem twoCellGivesRule {Letter : Type} (rules : List (List Letter × List Letter))
    {source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
    (cell : (encodedModeSignature rules).twoCell source target) : cell.val ∈ rules :=
  cell.property.1

/-! ## The reduction — both directions -/

/-- ★ FORWARD: a Thue conversion embeds as an encoded 2-cell convertibility.  Induction on the equivalence
closure; the only contentful case is `rule`, where the Thue two-sided sandwich (one constructor) is rebuilt as
`whiskerLeft ∘ whiskerRight ∘ rule` after `encodeWord_sandwich` reconciles the carriers. -/
theorem thue_to_encoded {Letter : Type} {rules : List (List Letter × List Letter)} {u v : List Letter}
    (conv : ThueCong rules u v) : EncodedConv rules (encodeWord u) (encodeWord v) := by
  induction conv with
  | rule step =>
      cases step with
      | rewrite pref suf lhs rhs mem =>
          rw [encodeWord_sandwich, encodeWord_sandwich]
          exact EncodedConv.whiskerLeft (encodeWord pref)
            (EncodedConv.whiskerRight (EncodedConv.rule mem) (encodeWord suf))
  | refl point => exact EncodedConv.refl _
  | symm _ inductiveHypothesis => exact EncodedConv.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EncodedConv.trans firstInductiveHypothesis secondInductiveHypothesis

/-- ★ BACKWARD: an encoded 2-cell convertibility reads back to a Thue conversion.  Induction on `EncodedConv`;
the whisker cases push back through `decodeWord_compose` to the Thue whisker-congruences, and the `rule` case
closes on `decode_encode`. -/
theorem encoded_to_thue {Letter : Type} {rules : List (List Letter × List Letter)}
    {source target : ModalityPath (encodedGraph Letter) EncodedMode.point EncodedMode.point}
    (conv : EncodedConv rules source target) :
    ThueCong rules (decodeWord source) (decodeWord target) := by
  induction conv with
  | rule mem =>
      rw [decode_encode, decode_encode]
      exact thueCong_of_mem mem
  | whiskerLeft prefixCell _ inductiveHypothesis =>
      rw [decodeWord_compose, decodeWord_compose]
      exact thueCong_whiskerLeft (decodeWord prefixCell) inductiveHypothesis
  | whiskerRight _ suffixCell inductiveHypothesis =>
      rw [decodeWord_compose, decodeWord_compose]
      exact thueCong_whiskerRight inductiveHypothesis (decodeWord suffixCell)
  | refl word => exact EquationalTheory.refl _
  | symm _ inductiveHypothesis => exact EquationalTheory.symm inductiveHypothesis
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact EquationalTheory.trans firstInductiveHypothesis secondInductiveHypothesis

/-- ★ **THE REDUCTION** (Burroni bridge, mechanized).  The Thue congruence of a semi-Thue system is exactly the
1-cell convertibility of the one-object 2-polygraph it encodes: `ThueCong rules u v ↔ EncodedConv rules
(encodeWord u) (encodeWord v)`.  This ties the classical Post/Markov citation to a walker-style 2-cell
congruence with a machine-checked iff. -/
theorem semiThue_iff_encodedTwoCell {Letter : Type} (rules : List (List Letter × List Letter))
    (u v : List Letter) :
    ThueCong rules u v ↔ EncodedConv rules (encodeWord u) (encodeWord v) := by
  constructor
  · exact thue_to_encoded
  · intro encoded
    have readBack := encoded_to_thue encoded
    rw [decode_encode, decode_encode] at readBack
    exact readBack

/-! ## Non-vacuity — the involution 1-rule system (Tier-C form) + a separation -/

/-- The one-letter alphabet of the walking involution (`s`), as a semi-Thue alphabet. -/
inductive InvolutionLetter where
  /-- The single generator `s` (session-duality `dual`). -/
  | s

/-- ★ The **involution semi-Thue system** `[s.s ↦ id]` — the string-rewriting form of the Tier-C oriented rule
`InvolutionRewrite` (`s.s ↦ id`). -/
def involutionThueRules : List (List InvolutionLetter × List InvolutionLetter) :=
  [([InvolutionLetter.s, InvolutionLetter.s], [])]

/-- The sole rule is a member of the involution rule set. -/
theorem involutionThueRule_mem :
    (([InvolutionLetter.s, InvolutionLetter.s], ([] : List InvolutionLetter))) ∈ involutionThueRules :=
  List.Mem.head _

/-- ★ Positive witness — `s.s ~ id` is DECIDED TRUE in the involution Thue congruence (one rule application). -/
theorem involutionThue_positive :
    ThueCong involutionThueRules [InvolutionLetter.s, InvolutionLetter.s] [] :=
  thueCong_of_mem involutionThueRule_mem

/-- The reduction, instantiated at the involution: `s.s ~ id` on the Thue side iff its encoded 2-cell
convertibility holds. -/
theorem involutionThue_reductionInstance :
    ThueCong involutionThueRules [InvolutionLetter.s, InvolutionLetter.s] []
      ↔ EncodedConv involutionThueRules
          (encodeWord [InvolutionLetter.s, InvolutionLetter.s]) (encodeWord ([] : List InvolutionLetter)) :=
  semiThue_iff_encodedTwoCell involutionThueRules [InvolutionLetter.s, InvolutionLetter.s] []

/-- The Z/2 parity of an involution word (`false` for the identity, each letter FLIPS) — the SAME invariant as
the Tier-B/C `involutionParityOf`, here as the semi-Thue separation homomorphism. -/
def involutionWordParity : List InvolutionLetter → Bool
  | [] => false
  | _ :: rest => !(involutionWordParity rest)

/-- `xor` on `Bool` distributes negation on the left: `!(xor a b) = xor (!a) b`. -/
theorem boolNotXor (leftBit rightBit : Bool) :
    (!(Bool.xor leftBit rightBit)) = Bool.xor (!leftBit) rightBit := by
  cases leftBit <;> cases rightBit <;> rfl

/-- `xor false b = b`. -/
theorem xorFalseLeft (bit : Bool) : Bool.xor false bit = bit := by cases bit <;> rfl

/-- Parity is a monoid homomorphism into `(Bool, xor)`: `parity (u ++ v) = xor (parity u) (parity v)`. -/
theorem involutionWordParity_append (first second : List InvolutionLetter) :
    involutionWordParity (first ++ second)
      = Bool.xor (involutionWordParity first) (involutionWordParity second) := by
  induction first with
  | nil => exact (xorFalseLeft (involutionWordParity second)).symm
  | cons headLetter rest inductiveHypothesis =>
      have stepLeft : involutionWordParity ((headLetter :: rest) ++ second)
          = !(involutionWordParity (rest ++ second)) := rfl
      have stepRight : involutionWordParity (headLetter :: rest) = !(involutionWordParity rest) := rfl
      rw [stepLeft, stepRight, inductiveHypothesis, boolNotXor]

/-- The involution rule is parity-balanced: both sides of `s.s ↦ id` have EVEN parity. -/
theorem involutionRuleParityBalanced {lhs rhs : List InvolutionLetter}
    (mem : (lhs, rhs) ∈ involutionThueRules) : involutionWordParity lhs = involutionWordParity rhs := by
  cases mem with
  | head => rfl
  | tail _ memberOfTail => cases memberOfTail

/-- ★ Parity is a Thue-congruence INVARIANT for the involution system (the separation classifier is
well-defined on classes): the prefix/suffix cancel by the append hom, and the rule is parity-balanced. -/
theorem involutionThue_preservesParity {u v : List InvolutionLetter}
    (conv : ThueCong involutionThueRules u v) : involutionWordParity u = involutionWordParity v := by
  induction conv with
  | rule step =>
      cases step with
      | rewrite pref suf lhs rhs mem =>
          rw [involutionWordParity_append, involutionWordParity_append,
              involutionWordParity_append, involutionWordParity_append, involutionRuleParityBalanced mem]
  | refl point => rfl
  | symm _ inductiveHypothesis => exact inductiveHypothesis.symm
  | trans _ _ firstInductiveHypothesis secondInductiveHypothesis =>
      exact firstInductiveHypothesis.trans secondInductiveHypothesis

/-- ★ Negative witness — `s ~ id` is DECIDED FALSE in the involution Thue congruence: `s` has ODD parity, `id`
has EVEN parity, and parity is a congruence invariant.  Together with `involutionThue_positive` the decision
genuinely discriminates (not always-true, not always-false). -/
theorem involutionThue_separation :
    ¬ ThueCong involutionThueRules [InvolutionLetter.s] [] := by
  intro conv
  have parityEqual : (true : Bool) = false := involutionThue_preservesParity conv
  exact Bool.noConfusion parityEqual

/-! ## The marker + the honest boundary -/

/-- ★ **STRENGTHENED (WP-CEIL-UNDEC).**  The Burroni bridge is MECHANIZED: `semiThue_iff_encodedTwoCell`
proves, over the shipped generic computad carrier, that the Thue congruence of an arbitrary semi-Thue system
is exactly the 1-cell convertibility of the one-object 2-polygraph it encodes (a monoid presentation IS a
one-0-cell 2-polygraph; Burroni, Theoret. Comput. Sci. 115 (1993)).  So FLAG A's rung-3 wall now rests on a
machine-checked REDUCTION plus the cited undecidability of the embedded word problem, not on an analogy.
HONEST BOUNDARY: what is mechanized is the BRIDGE only; the EXISTENCE of a finite semi-Thue system whose
`ThueCong` is undecidable (Post 1947 / Markov 1947) stays CITED — mechanizing it needs a computability
substrate (halting ⪯ string rewriting, as the Coq undecidability library does; Forster–Heiter–Smolka, ITP
2018), which is out of scope.  `= true` (the bridge); the full reduction to a known-undecidable instance is
the ledger's `fxMode_hasArbitraryTwoCellUndecidabilityReduction = false`; FLAG A itself stays `false`. -/
def fxMode_hasSemiThueReductionMechanized : Bool := true

/-- The mechanized bridge is a genuine iff (non-vacuity of the marker): the reduction theorem exists and
discriminates, witnessed by `involutionThue_positive` (a decided TRUE pair) and `involutionThue_separation`
(a decided FALSE pair) transported across `semiThue_iff_encodedTwoCell`. -/
theorem fxMode_hasSemiThueReductionMechanized_isBridge : fxMode_hasSemiThueReductionMechanized = true := rfl

end FX1Poly.Polygraph
