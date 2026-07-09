import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvPatternMultiset

/-! # mode-3 floor — the ORDERED Cartier–Foata clique-SEQUENCE for bare `TwoCellConv`: the strictly-finer
upgrade of r5's flat pattern-multiset, machine-REFUTED as a bare-conv invariant — the genuine last flip attempt
for `fxMode_hasModeRelativeConvDecision` closes as a WALL

`BareConvPatternMultiset` (r5) shipped the flat per-generator pattern MULTISET: a SOUND, order-forgetting
bare-conv invariant that SEPARATES the r4 `wordCode` collision (where every additive scalar collided), the ceiling
of the additive scalar tower — but NOT proven complete.  Its docstring, and the master-flag disposition in
`ModeRelativeMetatheory`, named the exact completeness candidate: the strictly FINER **ordered Cartier–Foata
clique-SEQUENCE** (Diekert–Muscholl — two Mazurkiewicz traces are equal IFF their clique-sequences are), which
retains the per-level / adjacency structure a flat order-forgetting bag discards.  This file BUILDS that ordered
clique-sequence and settles its exact status — NEGATIVELY, and mechanically: the ordered clique-sequence is NOT a
bare-conv invariant, because INTERCHANGE permutes the vcomp LEVEL order, so retaining the clique ORDER
over-separates bare-convertible cells.  Hence the r6 thesis — "bare-conv is a fixed-alphabet Mazurkiewicz trace
congruence whose complete NF is the Cartier–Foata clique-sequence" — is REFUTED, and
`fxMode_hasModeRelativeConvDecision` stays `false` as its permanent-as-stated terminal.

## Why the ordered clique-sequence and why it fails (the exact wall)

The interchange law relates vertical `⊟` (vcomp) and horizontal `⊠` (hcomp) composition:
`(α ⊟ α') ⊠ (β ⊟ β') ⟶ (α ⊠ β) ⊟ (α' ⊠ β')`.  A Mazurkiewicz-trace reading would call two 2-cells on DISJOINT
1-cell columns INDEPENDENT and pack a maximal antichain of mutually-independent generators into each successive
vcomp step (the Cartier–Foata / Foata normal form).  r5's flat multiset FORGETS the step order (it had to — the
soundness proof `TwoCellConv.patternMultiplicity_eq` shows interchange PERMUTES generators across the vcomp
boundary, the Eckmann–Hilton order-collapse).  The ordered clique-sequence tries to KEEP the step order.

  ★ **`RawTwoCellExpr.cliqueSequence`** — the ordered per-vcomp-LEVEL clique-sequence as a `List (List (List Bool))`
    (a SEQUENCE of cliques; each clique a list of `{L, R}` whisker-patterns).  `vcomp` STACKS levels
    (`++`, sequential composition = concatenation of clique-sequences — the essential difference from the flat
    multiset, which MERGES); `gen` is one singleton level; `id` is empty; a `whiskerLeft` / `whiskerRight` prepends
    `L` / `R` to every pattern in every clique.  Strictly FINER than the flat multiset (the flat multiset is its
    merge-collapse), and its equality is DECIDABLE zero-axiom (`listListListBoolDecEq`, cons-only, NEVER
    `Multiset` / `Quot`).  So — exactly as with r5 — decidability is NOT the obstruction; INVARIANCE is.

  ★★ **`cliqueSequence_not_bareConvInvariant`** — the ordered clique-sequence is NOT preserved by bare conv.  The
    concrete `interchange` step (over a minimal single-scalar signature, all four sub-cells the scalar `dot`) takes
    `cliqueInterchangeSource` (clique-sequence `[[R], [R], [L], [L]]`) to `cliqueInterchangeReduct`
    (clique-sequence `[[R], [L], [R], [L]]`) — a genuine `TwoCellConv` (bare, one interchange step) whose ordered
    clique-sequences DIFFER at level 1.  So the ordered clique-sequence OVER-separates: it distinguishes
    bare-convertible cells, hence "equal ordered clique-sequence" is a false-negative decision (returns NOT-conv on
    conv cells).  The FLAT multiset agrees on the very same pair (`cliqueInterchange_sortedPatternMultiset_eq`,
    both `[[L], [L], [R], [R]]`) — precisely because it forgets the level order that interchange permutes.  The
    ordered refinement's extra information (the clique ORDER) is exactly the UNSOUND part.

## The status — a WALL, not a flip (the honest terminal of the flag-B arc)

The ordered clique-sequence is caught between the two r5 facts and cannot escape:

  * A SOUND bare-conv invariant must be invariant under interchange, which PERMUTES the vcomp levels — so it must
    FORGET the level order, collapsing to r5's flat multiset (order-forgetting), which is INCOMPLETE (r5).
  * KEEPING the order (the ordered clique-sequence) is machine-refuted NOT invariant
    (`cliqueSequence_not_bareConvInvariant`) — it over-separates.

So no PLAIN per-level Cartier–Foata clique-sequence over a fixed independence alphabet is BOTH sound and complete
for bare conv.  The only remaining candidate is the GREEDY-repacked Foata NF (merge mutually-independent
generators into cliques via a fixed column-independence relation) — and that repacking's column-independence is
ALSO machine-refuted, from two sides already in-repo:

  * the Eckmann–Hilton width-change: the greedy per-level minimal-extraction NF is NOT swap-invariant —
    `normalizeSpine_isNotSwapInvariant` (`FreeTwoCell/TraceNormalFormNonInvariance`): a scalar bubble slides around
    a width-changing creation through its nil boundary (`atomicTraceEquiv_isNotLeftCancellable`), so the naive
    column coordinate is dynamic and the fixed independence relation is ill-defined (the free interchange structure
    is NOT a trace monoid — Forest–Mimram: "lack of an ordering", "no canonical representative"; Lafont;
    Guiraud–Malbos: finite convergent 3-polygraphs without finite derivation type);
  * whisker-non-functoriality: bare conv is STRICTLY finer than the full/trace congruence — the r4 Godement pair
    (`wordCodeCollisionLeft` / `wordCodeCollisionRight`) is `TwoCellConvFull` yet NOT bare `TwoCellConv`
    (`wordCodeCollision_not_twoCellConv`), because bare conv cannot move an `L` across the generator boundary
    (= whisker functoriality, which bare lacks = the trace independence a congruence needs).

The genuinely complete invariant is therefore the STRING-DIAGRAM / connected-component structure (Makkai;
Delpeuch–Vicary — the `arcStructureOf` route, quadratic), NOT any fixed-alphabet clique-sequence: two cells with
the same generators at the same levels can still have distinct WIRING.  Bare conv IS decidable in principle; its
mechanised total decider owes that string-diagram normal form (the deferred Gratzer interchange critical-pair
coherence), NOT the clique-sequence.  `fxMode_hasCartierFoataCliqueSequenceComplete` stays `false`;
`fxMode_hasBareConvOrderedCliqueSequenceRefutedByInterchange := true` records the machine-refutation;
`fxMode_hasModeRelativeConvDecision` (terminal disposition in `ModeRelativeMetatheory`) STAYS `false` — re-openable,
NOT undecidability-walled.  r1 / r2 / r3 / r4 / r5 soundness and shipped statements are NOT weakened; the saturated
/ faithful decisions are untouched.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
carrier is a constant-`List`-motive full-enum match; the refutation is a concrete `interchange` step plus `rfl`
computations of the two clique-sequences and an `injection` chain landing on `true = false`; the decidable equality
is hand-rolled cons-only, NEVER `Multiset` / `Quot`).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The ordered per-level clique-sequence carrier -/

/-- ★ The **ordered Cartier–Foata clique-SEQUENCE** of a free 2-cell, as a `List (List (List Bool))` — a SEQUENCE
of cliques, one per vertical level, each clique a list of `{L, R}` whisker-patterns (`false = L = whiskerLeft`,
`true = R = whiskerRight`, outermost-first — the same reading as `patternMultiplicity`).  A generator is one
singleton level holding the empty pattern `[]`; an identity is the empty sequence; a `vcomp` STACKS the two
sub-sequences (`++` — sequential composition = concatenation of clique-sequences, the ordered upgrade of the flat
multiset's MERGE); a LEFT / RIGHT whisker prepends `L` / `R` to every pattern in every clique.  Structural on the
EXPRESSION, constant-`List` motive, full five-case — propext-free.  Strictly FINER than
`sortedPatternMultiset` (which is its merge-collapse), retaining the per-level / adjacency order. -/
def RawTwoCellExpr.cliqueSequence {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → List (List (List Bool))
  | _, _, _, _, .gen _ => [[[]]]
  | _, _, _, _, .id _ => []
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      cellAlpha.cliqueSequence ++ cellBeta.cliqueSequence
  | _, _, _, _, .whiskerLeft _ body =>
      body.cliqueSequence.map (fun clique => clique.map (fun pat => false :: pat))
  | _, _, _, _, .whiskerRight _ body =>
      body.cliqueSequence.map (fun clique => clique.map (fun pat => true :: pat))

/-- Hand-rolled structural `DecidableEq (List (List (List Bool)))` — cons-only, reusing the inner
`listListBoolDecEq` (r5) and `List.noConfusion`; NEVER `Multiset` / `Quot` / `Quot.sound`.  So ordered
clique-sequence equality is DECIDABLE zero-axiom: decidability is not the obstruction, invariance is. -/
def listListListBoolDecEq :
    (leftList rightList : List (List (List Bool))) → Decidable (leftList = rightList)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by injection h)
  | _ :: _, [] => isFalse (fun h => by injection h)
  | headLeft :: tailLeft, headRight :: tailRight =>
      match listListBoolDecEq headLeft headRight with
      | isFalse headDiffers => isFalse (fun h => by injection h with hHead _; exact headDiffers hHead)
      | isTrue headAgrees =>
          match listListListBoolDecEq tailLeft tailRight with
          | isFalse tailDiffers => isFalse (fun h => by injection h with _ hTail; exact tailDiffers hTail)
          | isTrue tailAgrees => isTrue (by cases headAgrees; cases tailAgrees; rfl)

/-! ## The clique-sequence is strictly finer than the flat multiset — it still separates the r4 collision -/

/-- The LEFT r4 member's ordered clique-sequence is `[[[R, L]], [[L]]]` (its two Godement levels: the first unit
whiskered `R` then `L`, the second whiskered `L`). -/
theorem wcc_left_cliqueSequence :
    wordCodeCollisionLeft.cliqueSequence = [[[true, false]], [[false]]] := rfl

/-- The RIGHT r4 member's ordered clique-sequence is `[[[R]], [[L, L]]]` (the first unit whiskered `R`, the second
whiskered `L` then `L`). -/
theorem wcc_right_cliqueSequence :
    wordCodeCollisionRight.cliqueSequence = [[[true]], [[false, false]]] := rfl

/-- The r4 pair's ordered clique-sequences DIFFER (level 0: `[R, L]` vs `[R]`) — the strictly-finer ordered
carrier separates the r4 collision too, reproducing the r5 flat-multiset separation one level of structure up. -/
theorem wordCodeCollision_cliqueSequence_differs :
    wordCodeCollisionLeft.cliqueSequence ≠ wordCodeCollisionRight.cliqueSequence := by
  rw [wcc_left_cliqueSequence, wcc_right_cliqueSequence]
  intro cliquesEqual
  injection cliquesEqual with headEqual _
  injection headEqual with patternEqual _
  injection patternEqual with _ tailEqual
  have lengthClash : (1 : Nat) = 0 := congrArg List.length tailEqual
  exact Nat.noConfusion lengthClash

/-! ## The minimal single-scalar signature carrying the interchange counterexample -/

/-- The single mode of the scalar signature. -/
inductive ScalarMode where
  /-- The only mode. -/
  | pt

/-- The scalar signature has NO 1-cell generators — the only 1-cell is the identity path.  (An empty indexed
inductive; every `ScalarModality` fiber is uninhabited.) -/
inductive ScalarModality : ScalarMode → ScalarMode → Type

/-- The scalar-signature quiver: one mode, no modality generators. -/
def scalarGraph : ModeGraph :=
  { Mode := ScalarMode, Modality := ScalarModality }

/-- The only 1-cell — the identity path at the single mode. -/
abbrev scalarNil : ModalityPath scalarGraph ScalarMode.pt ScalarMode.pt :=
  ModalityPath.nil (graph := scalarGraph) ScalarMode.pt

/-- The single generating 2-cell: a SCALAR `dot : nil ⇒ nil` (freely vcomp- and hcomp-composable with itself,
since every whisker 1-cell is the identity path — exactly the shape the interchange counterexample needs). -/
inductive ScalarTwoCell : {sourceMode targetMode : ScalarMode} →
    ModalityPath scalarGraph sourceMode targetMode →
    ModalityPath scalarGraph sourceMode targetMode → Type where
  /-- The scalar 2-cell. -/
  | dot : ScalarTwoCell scalarNil scalarNil

/-- The scalar 2-polygraph. -/
def scalarSignature : ModeSignature :=
  { graph := scalarGraph,
    twoCell := fun {_sourceMode _targetMode} domPath codPath => ScalarTwoCell domPath codPath }

/-- The scalar generator as a free 2-cell `nil ⇒ nil`. -/
def scalarDot : RawTwoCellExpr scalarSignature scalarNil scalarNil :=
  RawTwoCellExpr.gen ScalarTwoCell.dot

/-! ## ★★ The interchange refutation: the ordered clique-sequence is NOT a bare-conv invariant -/

/-- The interchange SOURCE `(dot ⊟ dot) ⊠ (dot ⊟ dot)` — a Godement product of two vertical composites.  Its
ordered clique-sequence reads the two `R`-whiskered left-factor levels THEN the two `L`-whiskered right-factor
levels: `[[R], [R], [L], [L]]`. -/
abbrev cliqueInterchangeSource :=
  RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp scalarDot scalarDot)
    (RawTwoCellExpr.vcomp scalarDot scalarDot)

/-- The interchange REDUCT `(dot ⊠ dot) ⊟ (dot ⊠ dot)` — the vertical composite of two Godement products.  Its
ordered clique-sequence interleaves `R` then `L` per Godement, twice: `[[R], [L], [R], [L]]`. -/
abbrev cliqueInterchangeReduct :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp scalarDot scalarDot)
    (RawTwoCellExpr.hcomp scalarDot scalarDot)

/-- The two cells are related by ONE interchange 3-cell (all four sub-cells the scalar `dot`) — hence bare
`TwoCellConv`. -/
theorem cliqueInterchange_step :
    TwoCellStep scalarSignature cliqueInterchangeSource cliqueInterchangeReduct :=
  TwoCellStep.interchange scalarDot scalarDot scalarDot scalarDot

/-- Hence the pair is bare `TwoCellConv` (a one-step conversion). -/
theorem cliqueInterchange_conv :
    TwoCellConv scalarSignature cliqueInterchangeSource cliqueInterchangeReduct :=
  TwoCellConv.ofStep cliqueInterchange_step

/-- The SOURCE's ordered clique-sequence: `[[R], [R], [L], [L]]` (the two `R`-levels before the two `L`-levels). -/
theorem cliqueInterchangeSource_cliqueSequence :
    cliqueInterchangeSource.cliqueSequence = [[[true]], [[true]], [[false]], [[false]]] := rfl

/-- The REDUCT's ordered clique-sequence: `[[R], [L], [R], [L]]` (Godement `R`-then-`L`, twice). -/
theorem cliqueInterchangeReduct_cliqueSequence :
    cliqueInterchangeReduct.cliqueSequence = [[[true]], [[false]], [[true]], [[false]]] := rfl

/-- ★ The two ordered clique-sequences DIFFER (level 1: `R` vs `L`) — even though the cells are bare
`TwoCellConv`. -/
theorem cliqueInterchange_cliqueSequence_differs :
    cliqueInterchangeSource.cliqueSequence ≠ cliqueInterchangeReduct.cliqueSequence := by
  rw [cliqueInterchangeSource_cliqueSequence, cliqueInterchangeReduct_cliqueSequence]
  intro cliquesEqual
  injection cliquesEqual with _ tailEqual
  injection tailEqual with secondCliqueEqual _
  injection secondCliqueEqual with patternEqual _
  injection patternEqual with bitEqual _
  exact Bool.noConfusion bitEqual

/-- The FLAT pattern-multiset (r5, the SOUND order-forgetting invariant) AGREES on the very same pair
(`[[L], [L], [R], [R]]` both sides) — precisely because it forgets the vcomp-level order that interchange permutes.
So the ordered clique-sequence's extra information (the clique ORDER) is exactly the UNSOUND part. -/
theorem cliqueInterchange_sortedPatternMultiset_eq :
    cliqueInterchangeSource.sortedPatternMultiset = cliqueInterchangeReduct.sortedPatternMultiset := rfl

/-- ★★ **The ordered Cartier–Foata clique-SEQUENCE is NOT a bare-conv invariant.**  There exist bare
`TwoCellConv`-related cells (one interchange step) whose ordered clique-sequences DIFFER.  So "equal ordered
clique-sequence" over-separates — it is a FALSE-NEGATIVE decision for bare conv — and the r6 completeness thesis
("bare conv is a fixed-alphabet Mazurkiewicz trace congruence whose complete NF is the Cartier–Foata
clique-sequence") is REFUTED: retaining the clique ORDER is unsound, yet forgetting it collapses to r5's flat
multiset, which is incomplete (r5).  No plain per-level clique-sequence is both sound and complete. -/
theorem cliqueSequence_not_bareConvInvariant :
    ∃ (cellFirst cellSecond : RawTwoCellExpr scalarSignature scalarNil scalarNil),
      TwoCellConv scalarSignature cellFirst cellSecond
        ∧ cellFirst.cliqueSequence ≠ cellSecond.cliqueSequence :=
  ⟨cliqueInterchangeSource, cliqueInterchangeReduct, cliqueInterchange_conv,
    cliqueInterchange_cliqueSequence_differs⟩

/-! ## Honesty markers -/

/-- **Honesty marker — the r6 thesis is REFUTED, NOT flipped.**  The ordered Cartier–Foata clique-SEQUENCE
(`RawTwoCellExpr.cliqueSequence`) is the strictly-finer upgrade r5 named as the completeness candidate, but it is
machine-checked NOT a bare-conv invariant (`cliqueSequence_not_bareConvInvariant` — the interchange step permutes
the vcomp levels), so it over-separates; and the sound refinement collapses to r5's incomplete flat multiset.  No
PLAIN fixed-alphabet clique-sequence decides bare conv, and the GREEDY-repacked variant's column-independence is
ALSO refuted (Eckmann–Hilton `normalizeSpine_isNotSwapInvariant`; whisker-non-functoriality
`wordCodeCollision_not_twoCellConv`).  `= false`. -/
def fxMode_hasCartierFoataCliqueSequenceComplete : Bool := false

/-- **★ ESTABLISHED — the ordered Cartier–Foata clique-SEQUENCE is machine-REFUTED as a bare-conv invariant by the
interchange critical pair, closing the flag-B arc as a WALL.**

Delivered (each zero-axiom): the ordered per-level clique-sequence carrier `RawTwoCellExpr.cliqueSequence`
(`List (List (List Bool))`, `vcomp` = concatenation of clique-sequences — the ordered upgrade of r5's flat
merge-multiset) with DECIDABLE equality `listListListBoolDecEq` (cons-only, NEVER `Multiset` / `Quot`); its strict
refinement of the flat multiset, still SEPARATING the r4 Godement collision
(`wordCodeCollision_cliqueSequence_differs`, level 0 `[R, L]` vs `[R]`); and the machine-REFUTATION
`cliqueSequence_not_bareConvInvariant` — the concrete `interchange` step (single-scalar signature, all four
sub-cells the scalar `dot`) relates bare `TwoCellConv` cells `cliqueInterchangeSource` / `cliqueInterchangeReduct`
whose ordered clique-sequences DIFFER (`[[R], [R], [L], [L]]` vs `[[R], [L], [R], [L]]`, level 1 `R` vs `L`), while
the SOUND flat multiset AGREES (`cliqueInterchange_sortedPatternMultiset_eq`, both `[[L], [L], [R], [R]]`).

Reading (the exact terminal): a SOUND bare-conv invariant must survive interchange, which PERMUTES the vcomp
levels, so it must FORGET the level order — collapsing to r5's flat multiset, which is INCOMPLETE.  KEEPING the
order (the ordered clique-sequence) is machine-refuted NOT invariant.  So no plain per-level Cartier–Foata
clique-sequence over a fixed independence alphabet is BOTH sound and complete for bare conv — the r6 thesis is
refuted.  The GREEDY-repacked Foata NF (a fixed column-independence relation) is also refuted, in-repo from two
sides: the Eckmann–Hilton width-change (`normalizeSpine_isNotSwapInvariant` — a scalar bubble slides around a
width-changing creation, so the column coordinate is dynamic; the free interchange structure is NOT a trace
monoid — Forest–Mimram "no canonical representative", Lafont, Guiraud–Malbos), and whisker-non-functoriality (the
r4 pair `wordCodeCollision_not_twoCellConv`: `TwoCellConvFull` yet NOT bare, because bare cannot move `L` across
the generator boundary = the missing trace independence).  The genuinely complete invariant is the string-diagram /
connected-component structure (Makkai; Delpeuch–Vicary — quadratic), NOT any clique-sequence: same generators at
same levels can still differ in WIRING.

Untouched / not weakened: `fxMode_hasCartierFoataCliqueSequenceComplete` STAYS `false`;
`fxMode_hasModeRelativeConvDecision` (terminal disposition in `ModeRelativeMetatheory`) STAYS `false` — the general
bare decision remains the open Gratzer interchange critical-pair coherence, re-openable, NOT undecidability-walled;
r1 / r2 / r3 / r4 / r5 soundness and shipped statements are NOT weakened; the disposed trace / nfCell carriers are
NOT re-flipped; the saturated / faithful decisions are untouched.  This flag records the machine-refutation of the
ordered clique-sequence as a bare-conv invariant.  `= true`. -/
def fxMode_hasBareConvOrderedCliqueSequenceRefutedByInterchange : Bool := true

end FX1Poly.Polygraph
