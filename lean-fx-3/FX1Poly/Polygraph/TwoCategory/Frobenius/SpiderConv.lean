import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderPresentation
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConv
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction

/-! # WP-FROB r3 (FROB-3) — `SpiderConv`, the partition-sound convertibility over the spider presentation

The special / extraspecial commutative-Frobenius presentation ships as data with per-row seed soundness
(`SpiderPresentation.lean`).  This file turns those witnesses into an inductive CONVERTIBILITY relation
`SpiderConv` on generator words and proves it PARTITION-SOUND: convertible words induce the same boundary
partition (the extraspecial / corelation invariant `extraSpiderDiagramOf`).

## What `SpiderConv` contains (each constructor genuinely partition-sound, zero-axiom)

  * **The equivalence closure** — `refl` / `symm` / `trans` (soundness by `Eq.refl` / `Eq.symm` / `Eq.trans`).
  * **The thirteen special rows at their boundary** — `frobAssoc` / … / `frobSpecial` (soundness by the shipped
    `frob*_sound` witnesses, projected through `forgetSpiderClosed`).
  * ★ **The interchange (Godement) move, IN ARBITRARY CONTEXT** — `interchange`: two generators fired at an
    in-range disjoint pair AFTER any prefix word commute.  Discharged STATE-PARAMETRICALLY by the shared Brauer
    reachable interchange `brauer_reachable_interchange` (Brauer `extractDiagram` equality), whose connectivity view
    is reconstructed (`matchingConnectivityViewSim_ofExtractEq`) and fed to the spider forget-extract view lemma.
  * ★ **The contextual WHISKER (congruence) move** — `whisker`: two words fired after ANY prefix are convertible
    when, at the two post-prefix states, they preserve the BOUNDARY partition view (equal open-wire count, same
    boundary same-component relation on the in-range indices).  It gates on the STRUCTURAL union-find view
    (`matchingSameComponent`, the SAME boundary connectivity the spider `blockLabels` read off — the spider
    `boundaryNodes` is definitionally `matchingBoundaryNodes`), NOT on the diagram conclusion, so it is non-circular.

## The partition invariant, not the full Cospan one

The whisker gates on the boundary PARTITION view only — it drops the closed-component count.  So `SpiderConv` is
proven sound for the extraspecial (corelation) invariant `extraSpiderDiagramOf` (`SpiderPartitionType`), NOT the full
special (`Cospan(FinSet)`) invariant `spiderDiagramOf` (which additionally tracks the isolated-component count).  The
partition is exactly what the Coya–Fong corelation walker keeps; lifting to the full Cospan invariant needs the
closed-component preservation under the boundary view (the recon's file-4 residual, ledgered).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Field-determination for the partition carriers -/

/-- A `SpiderPartitionType` is determined by its three fields.  `cases` on the structures and on each field
equality (recursor / `Eq.rec` only), so `propext`-free — the mirror of `diagramType_eq_of_fields`. -/
theorem spiderPartitionType_eq_of_fields {first second : SpiderPartitionType}
    (bottomCountsAgree : first.bottomCount = second.bottomCount)
    (topCountsAgree : first.topCount = second.topCount)
    (blockLabelsAgree : first.blockLabels = second.blockLabels) : first = second := by
  cases first; cases second
  cases bottomCountsAgree; cases topCountsAgree; cases blockLabelsAgree
  rfl

/-- A `SpiderDiagramType` is determined by its four fields. -/
theorem spiderDiagramType_eq_of_fields {first second : SpiderDiagramType}
    (bottomCountsAgree : first.bottomCount = second.bottomCount)
    (topCountsAgree : first.topCount = second.topCount)
    (blockLabelsAgree : first.blockLabels = second.blockLabels)
    (closedAgree : first.closedComponents = second.closedComponents) : first = second := by
  cases first; cases second
  cases bottomCountsAgree; cases topCountsAgree; cases blockLabelsAgree; cases closedAgree
  rfl

/-! ## Renaming-invariance of the block-label read-off -/

/-- ★ **`firstIndexWithRoot` reads its boundary nodes only through the per-candidate root-equality boolean.**  Two
scans whose root-equality booleans agree on every candidate return the same least-index representative — regardless
of the actual node ids / link lists / root values.  Structural recursion on the candidate list.  The mirror of
`findPartnerScan_congr` (simpler: no `excludeIndex` guard).  This is the renaming-invariance of the block-label
read-off. -/
theorem firstIndexWithRoot_congr
    (firstLinks : List (Nat × Nat)) (firstBoundaryNodes : List Nat) (firstTargetRoot : Nat)
    (secondLinks : List (Nat × Nat)) (secondBoundaryNodes : List Nat) (secondTargetRoot : Nat) :
    (cands : List Nat) →
    (∀ candidate ∈ cands,
        (unionFindRootOf firstLinks (natListGetAt firstBoundaryNodes candidate) == firstTargetRoot)
          = (unionFindRootOf secondLinks (natListGetAt secondBoundaryNodes candidate) == secondTargetRoot)) →
    firstIndexWithRoot firstLinks firstBoundaryNodes firstTargetRoot cands
      = firstIndexWithRoot secondLinks secondBoundaryNodes secondTargetRoot cands
  | [], _ => rfl
  | head :: tail, rootEqualityAgrees => by
      show (if unionFindRootOf firstLinks (natListGetAt firstBoundaryNodes head) == firstTargetRoot
              then head else firstIndexWithRoot firstLinks firstBoundaryNodes firstTargetRoot tail)
         = (if unionFindRootOf secondLinks (natListGetAt secondBoundaryNodes head) == secondTargetRoot
              then head else firstIndexWithRoot secondLinks secondBoundaryNodes secondTargetRoot tail)
      rw [rootEqualityAgrees head (List.Mem.head _),
        firstIndexWithRoot_congr firstLinks firstBoundaryNodes firstTargetRoot
          secondLinks secondBoundaryNodes secondTargetRoot tail
          (fun candidate inTail => rootEqualityAgrees candidate (List.Mem.tail _ inTail))]

/-! ## The spider extract is determined by the boundary-connectivity view -/

/-- ★ **The spider PARTITION extract is determined by the boundary-connectivity view.**  Two wire states with equal
open-wire count and the same boundary same-component relation on the in-range indices project (via
`forgetSpiderClosed`) to the same `SpiderPartitionType`.  The block-label partition closes by `firstIndexWithRoot_congr`
+ `listMapCongr` over the agreeing same-component relation; the bottom / top counts are direct.  The spider
`boundaryNodes` is definitionally `matchingBoundaryNodes`, so the hypothesis reuses `matchingSameComponent` verbatim.
Closed-component count is NOT read (it is forgotten), so no loop / closed-count hypothesis is needed. -/
theorem extractSpiderDiagram_forget_eq_of_connectivityView (bottomCount : Nat)
    (firstState secondState : WireState)
    (lengthsAgree : firstState.openWires.length = secondState.openWires.length)
    (relationAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + firstState.openWires.length →
        secondIndex < bottomCount + firstState.openWires.length →
        matchingSameComponent bottomCount firstState firstIndex secondIndex
          = matchingSameComponent bottomCount secondState firstIndex secondIndex) :
    forgetSpiderClosed (extractSpiderDiagram bottomCount firstState)
      = forgetSpiderClosed (extractSpiderDiagram bottomCount secondState) := by
  have totalsAgree : bottomCount + firstState.openWires.length = bottomCount + secondState.openWires.length := by
    rw [lengthsAgree]
  apply spiderPartitionType_eq_of_fields
  · rfl
  · exact lengthsAgree
  · show (List.range (bottomCount + firstState.openWires.length)).map
            (fun index => firstIndexWithRoot firstState.links
              (List.range bottomCount ++ firstState.openWires)
              (unionFindRootOf firstState.links
                (natListGetAt (List.range bottomCount ++ firstState.openWires) index))
              (List.range (bottomCount + firstState.openWires.length)))
       = (List.range (bottomCount + secondState.openWires.length)).map
            (fun index => firstIndexWithRoot secondState.links
              (List.range bottomCount ++ secondState.openWires)
              (unionFindRootOf secondState.links
                (natListGetAt (List.range bottomCount ++ secondState.openWires) index))
              (List.range (bottomCount + secondState.openWires.length)))
    rw [← totalsAgree]
    apply listMapCongr
    intro candidateIndex candidateInRange
    have candidateBelow : candidateIndex < bottomCount + firstState.openWires.length :=
      mem_range_imp_lt candidateInRange
    apply firstIndexWithRoot_congr
    intro scanIndex scanInRange
    exact relationAgrees scanIndex candidateIndex (mem_range_imp_lt scanInRange) candidateBelow

/-! ## The convertibility relation -/

/-- ★ **`SpiderConv n a b`** — the partition-sound convertibility of two generator words over `n` bottom wires: the
equivalence closure of the thirteen special-Frobenius relations (at their boundary) together with the fully-contextual
interchange (Godement) move and the boundary-partition-preserving contextual whisker. -/
inductive SpiderConv : Nat → List BrauerAtom → List BrauerAtom → Prop
  /-- Reflexivity. -/
  | refl (bottomCount : Nat) (word : List BrauerAtom) : SpiderConv bottomCount word word
  /-- Symmetry. -/
  | symm {bottomCount : Nat} {leftWord rightWord : List BrauerAtom} :
      SpiderConv bottomCount leftWord rightWord → SpiderConv bottomCount rightWord leftWord
  /-- Transitivity. -/
  | trans {bottomCount : Nat} {leftWord midWord rightWord : List BrauerAtom} :
      SpiderConv bottomCount leftWord midWord → SpiderConv bottomCount midWord rightWord →
      SpiderConv bottomCount leftWord rightWord
  /-- Associativity μ(μ⊗1) = μ(1⊗μ). -/
  | frobAssoc : SpiderConv frobAssoc.boundaryCount frobAssoc.lhs frobAssoc.rhs
  /-- Left unit μ(η⊗1) = 1. -/
  | frobUnitLeft : SpiderConv frobUnitLeft.boundaryCount frobUnitLeft.lhs frobUnitLeft.rhs
  /-- Right unit μ(1⊗η) = 1. -/
  | frobUnitRight : SpiderConv frobUnitRight.boundaryCount frobUnitRight.lhs frobUnitRight.rhs
  /-- Coassociativity (δ⊗1)δ = (1⊗δ)δ. -/
  | frobCoassoc : SpiderConv frobCoassoc.boundaryCount frobCoassoc.lhs frobCoassoc.rhs
  /-- Left counit (ε⊗1)δ = 1. -/
  | frobCounitLeft : SpiderConv frobCounitLeft.boundaryCount frobCounitLeft.lhs frobCounitLeft.rhs
  /-- Right counit (1⊗ε)δ = 1. -/
  | frobCounitRight : SpiderConv frobCounitRight.boundaryCount frobCounitRight.lhs frobCounitRight.rhs
  /-- Frobenius law (μ⊗1)(1⊗δ) = δμ. -/
  | frobLeft : SpiderConv frobLeft.boundaryCount frobLeft.lhs frobLeft.rhs
  /-- Frobenius law, other orientation (1⊗μ)(δ⊗1) = δμ. -/
  | frobRight : SpiderConv frobRight.boundaryCount frobRight.lhs frobRight.rhs
  /-- Commutativity of μ: μσ = μ. -/
  | frobCommMult : SpiderConv frobCommMult.boundaryCount frobCommMult.lhs frobCommMult.rhs
  /-- Cocommutativity of δ: σδ = δ. -/
  | frobCommComult : SpiderConv frobCommComult.boundaryCount frobCommComult.lhs frobCommComult.rhs
  /-- Symmetry involutivity σσ = 1⊗1. -/
  | frobCrossingInvolution :
      SpiderConv frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs frobCrossingInvolution.rhs
  /-- Yang–Baxter (R3) on three strands. -/
  | frobYangBaxter : SpiderConv frobYangBaxter.boundaryCount frobYangBaxter.lhs frobYangBaxter.rhs
  /-- The special law μδ = 1. -/
  | frobSpecial : SpiderConv frobSpecial.boundaryCount frobSpecial.lhs frobSpecial.rhs
  /-- ★ The interchange (Godement) move, IN ARBITRARY CONTEXT: after any prefix word, two generators fired at an
  in-range disjoint pair commute. -/
  | interchange (bottomCount : Nat) (prefixAtoms : List BrauerAtom) (positionA positionB : Nat)
      (descA descB : WiringDesc) :
      0 < bottomCount →
      positionA + descA.inputCount ≤ positionB →
      positionB + descB.inputCount
          ≤ (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length →
      SpiderConv bottomCount
        (prefixAtoms ++ [⟨positionA, descA⟩,
          ⟨positionB - descA.inputCount + descA.outputCount, descB⟩])
        (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩])
  /-- ★ The **contextual whisker (congruence) move**: two generator words fired after ANY prefix are convertible when,
  at the two post-prefix states, they preserve the BOUNDARY PARTITION view — equal open-wire count and the SAME
  boundary same-component relation on the in-range indices.  Gates on the STRUCTURAL union-find boundary view
  (`matchingSameComponent`), NOT on the diagram conclusion, so it is non-circular. -/
  | whisker (bottomCount : Nat) (prefixAtoms wordLeft wordRight : List BrauerAtom) :
      (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length
          = (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight).openWires.length →
      (∀ firstIndex secondIndex,
          firstIndex < bottomCount
              + (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length →
          secondIndex < bottomCount
              + (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft).openWires.length →
          matchingSameComponent bottomCount
              (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft) firstIndex secondIndex
            = matchingSameComponent bottomCount
              (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)
                firstIndex secondIndex) →
      SpiderConv bottomCount (prefixAtoms ++ wordLeft) (prefixAtoms ++ wordRight)

/-! ## Soundness — the partition (corelation) invariant -/

/-- ★ **`SpiderConv` is partition-sound.**  Convertible words induce the SAME boundary partition
(`extraSpiderDiagramOf`, the extraspecial / corelation invariant).  By induction on the derivation: the equivalence
closure by `Eq`, the thirteen special rows by their shipped `frob*_sound` witnesses (projected through
`forgetSpiderClosed`), the interchange move by reducing through `processBrauer_append` to the shared reachable
interchange `brauer_reachable_interchange` (Brauer extract equality reconstructed to the connectivity view), and the
whisker move uniformly by `processBrauer_append` + `extractSpiderDiagram_forget_eq_of_connectivityView`. -/
theorem spiderConv_partitionSound {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (conv : SpiderConv bottomCount leftWord rightWord) :
    extraSpiderDiagramOf bottomCount leftWord = extraSpiderDiagramOf bottomCount rightWord := by
  induction conv with
  | refl _ _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight
  | frobAssoc => exact congrArg forgetSpiderClosed frobAssoc_sound
  | frobUnitLeft => exact congrArg forgetSpiderClosed frobUnitLeft_sound
  | frobUnitRight => exact congrArg forgetSpiderClosed frobUnitRight_sound
  | frobCoassoc => exact congrArg forgetSpiderClosed frobCoassoc_sound
  | frobCounitLeft => exact congrArg forgetSpiderClosed frobCounitLeft_sound
  | frobCounitRight => exact congrArg forgetSpiderClosed frobCounitRight_sound
  | frobLeft => exact congrArg forgetSpiderClosed frobLeft_sound
  | frobRight => exact congrArg forgetSpiderClosed frobRight_sound
  | frobCommMult => exact congrArg forgetSpiderClosed frobCommMult_sound
  | frobCommComult => exact congrArg forgetSpiderClosed frobCommComult_sound
  | frobCrossingInvolution => exact congrArg forgetSpiderClosed frobCrossingInvolution_sound
  | frobYangBaxter => exact congrArg forgetSpiderClosed frobYangBaxter_sound
  | frobSpecial => exact congrArg forgetSpiderClosed frobSpecial_sound
  | interchange bottomCount prefixAtoms positionA positionB descA descB bottomPos disjoint windowB =>
      have brauerEq : extractDiagram bottomCount
            (processBrauer (brauerSeed bottomCount)
              (prefixAtoms ++ [⟨positionA, descA⟩,
                ⟨positionB - descA.inputCount + descA.outputCount, descB⟩]))
          = extractDiagram bottomCount
            (processBrauer (brauerSeed bottomCount)
              (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩])) := by
        rw [processBrauer_append prefixAtoms (brauerSeed bottomCount)
              [⟨positionA, descA⟩, ⟨positionB - descA.inputCount + descA.outputCount, descB⟩],
          processBrauer_append prefixAtoms (brauerSeed bottomCount)
              [⟨positionB, descB⟩, ⟨positionA, descA⟩]]
        exact brauer_reachable_interchange bottomCount bottomPos prefixAtoms positionA positionB descA descB
          disjoint windowB
      have view := matchingConnectivityViewSim_ofExtractEq bottomCount
        (processBrauer (brauerSeed bottomCount)
          (prefixAtoms ++ [⟨positionA, descA⟩, ⟨positionB - descA.inputCount + descA.outputCount, descB⟩]))
        (processBrauer (brauerSeed bottomCount) (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩]))
        brauerEq
      show forgetSpiderClosed (extractSpiderDiagram bottomCount
          (processBrauer (brauerSeed bottomCount)
            (prefixAtoms ++ [⟨positionA, descA⟩,
              ⟨positionB - descA.inputCount + descA.outputCount, descB⟩])))
        = forgetSpiderClosed (extractSpiderDiagram bottomCount
          (processBrauer (brauerSeed bottomCount)
            (prefixAtoms ++ [⟨positionB, descB⟩, ⟨positionA, descA⟩])))
      exact extractSpiderDiagram_forget_eq_of_connectivityView bottomCount _ _ view.lengthEq
        (fun firstIndex secondIndex firstBelow secondBelow =>
          view.viewAgrees firstIndex secondIndex (view.lengthEq ▸ firstBelow) (view.lengthEq ▸ secondBelow))
  | whisker bottomCount prefixAtoms wordLeft wordRight lengthsAgree relationAgrees =>
      show forgetSpiderClosed (extractSpiderDiagram bottomCount
          (processBrauer (brauerSeed bottomCount) (prefixAtoms ++ wordLeft)))
        = forgetSpiderClosed (extractSpiderDiagram bottomCount
          (processBrauer (brauerSeed bottomCount) (prefixAtoms ++ wordRight)))
      rw [processBrauer_append prefixAtoms (brauerSeed bottomCount) wordLeft,
        processBrauer_append prefixAtoms (brauerSeed bottomCount) wordRight]
      exact extractSpiderDiagram_forget_eq_of_connectivityView bottomCount
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft)
        (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight)
        lengthsAgree relationAgrees

/-! ## Non-vacuity -/

/-- `SpiderConv` genuinely relates DISTINCT words: the Frobenius law identifies `[comultAt 1, multAt 0]` and
`[multAt 0, comultAt 0]` (different lists) as convertible. -/
theorem spiderConv_frobLeft : SpiderConv 2 frobLeft.lhs frobLeft.rhs := SpiderConv.frobLeft

/-- ★ **`SpiderConv` identifies GENUINELY DIFFERENT words.**  The Frobenius "S=X" law relates the distinct generator
words `[comultAt 1, multAt 0]` and `[multAt 0, comultAt 0]` — so the convertibility is not merely reflexive. -/
theorem spiderConv_frobLeft_identifies_distinct :
    frobLeft.lhs ≠ frobLeft.rhs ∧ SpiderConv 2 frobLeft.lhs frobLeft.rhs :=
  ⟨by decide, SpiderConv.frobLeft⟩

/-- The partition discriminator genuinely SEPARATES: the Frobenius "H" element δμ (all four ports one block) and the
identity on two strands (two separate blocks) induce DIFFERENT boundary partitions. -/
theorem extraSpiderDiagram_H_ne_identity :
    extraSpiderDiagramOf 2 [multAt 0, comultAt 0]
      ≠ extraSpiderDiagramOf 2 [identityStrandAt 0, identityStrandAt 1] := by decide

/-- ★ **`SpiderConv` is a PROPER relation** — the Frobenius "H" element δμ is NOT convertible to the identity pair.
If it were, `spiderConv_partitionSound` would equate their genuinely-distinct partitions
(`extraSpiderDiagram_H_ne_identity`).  So partition soundness is non-vacuous: it genuinely constrains which words are
convertible. -/
theorem spiderConv_H_not_identity :
    ¬ SpiderConv 2 [multAt 0, comultAt 0] [identityStrandAt 0, identityStrandAt 1] :=
  fun conv => extraSpiderDiagram_H_ne_identity (spiderConv_partitionSound conv)

/-! ### Non-vacuity of the whisker move — a relation whiskered IN CONTEXT

The whisker constructor is genuinely inhabited beyond the seed relations: here cocommutativity of δ (`σδ = δ`) fired
at OFFSET 1 (on strands 1,2 of a two-strand boundary comultiplication context) AFTER a non-trivial prefix
comultiplication, discharged by `decide` on the concrete post-prefix states. -/

/-- The boundary same-component agreement for `σδ = δ` whiskered at offset `1` after a prefix comultiplication, in the
`Nat.decidableBallLT`-friendly order (guard immediately after each binder), discharged by `decide`. -/
private theorem whiskerCommComult_relationAgrees_ordered : ∀ firstIndex,
    firstIndex < 1
        + (processBrauer (processBrauer (brauerSeed 1) [comultAt 0]) [comultAt 1, crossingAt 1]).openWires.length →
    ∀ secondIndex,
    secondIndex < 1
        + (processBrauer (processBrauer (brauerSeed 1) [comultAt 0]) [comultAt 1, crossingAt 1]).openWires.length →
    matchingSameComponent 1
        (processBrauer (processBrauer (brauerSeed 1) [comultAt 0]) [comultAt 1, crossingAt 1])
        firstIndex secondIndex
      = matchingSameComponent 1
        (processBrauer (processBrauer (brauerSeed 1) [comultAt 0]) [comultAt 1])
        firstIndex secondIndex := by decide

/-- ★ **The whisker move is NON-VACUOUS: cocommutativity whiskered in a non-trivial context.**  After a prefix
comultiplication on strand `0`, cocommutativity fired at offset `1` (`σδ = δ` on the produced right leg) is convertible
— a genuinely contextual whiskering (offset `1`, non-empty prefix) that the seed constructors do not supply.  Its two
connectivity obligations are discharged concretely by `decide` on the post-prefix states. -/
theorem spiderConv_whisker_commComult_inContext :
    SpiderConv 1 ([comultAt 0] ++ [comultAt 1, crossingAt 1]) ([comultAt 0] ++ [comultAt 1]) :=
  SpiderConv.whisker 1 [comultAt 0] [comultAt 1, crossingAt 1] [comultAt 1] (by decide)
    (fun firstIndex secondIndex hfirst hsecond =>
      whiskerCommComult_relationAgrees_ordered firstIndex hfirst secondIndex hsecond)

/-- The contextual whiskering above genuinely relates DISTINCT words. -/
theorem spiderConv_whisker_inContext_distinct :
    ([comultAt 0] ++ [comultAt 1, crossingAt 1]) ≠ ([comultAt 0] ++ [comultAt 1]) := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — `SpiderConv` ships with a PARTITION-soundness proof.**  `spiderConv_partitionSound` proves
convertible words induce the same boundary partition (`extraSpiderDiagramOf`, the extraspecial / corelation
invariant); the relation is the equivalence closure of the thirteen special-Frobenius relations (at their boundary)
plus the fully-contextual interchange (Godement) move and the boundary-partition-preserving contextual whisker.  The
interchange is discharged state-parametrically via `brauer_reachable_interchange` + the connectivity-view
reconstruction; the whisker uniformly via `extractSpiderDiagram_forget_eq_of_connectivityView`.  NON-VACUOUS: it
relates distinct words (`spiderConv_frobLeft_identifies_distinct`), the discriminator separates
(`extraSpiderDiagram_H_ne_identity`), the relation is proper (`spiderConv_H_not_identity`), and the whisker is
inhabited in context (`spiderConv_whisker_commComult_inContext`).  `= true`. -/
def fxFrob_hasSpiderConvSoundness : Bool := true

/-- **Honesty marker — the contextual interchange (Godement) move is discharged via the shared Brauer reachable
interchange.**  Unlike the thirteen relations (partition-sound only at their own boundary/seed), the interchange
constructor is discharged after ANY prefix word by reducing to `brauer_reachable_interchange` (Brauer `extractDiagram`
equality), whose connectivity view is reconstructed (`matchingConnectivityViewSim_ofExtractEq`) and fed to the spider
forget-extract view lemma — so the Godement law is a genuine contextual partition-convertibility move for the spider
alphabet.  `= true`. -/
def fxFrob_hasSpiderConvContextualInterchange : Bool := true

end FX1Poly.Polygraph
