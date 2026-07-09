import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence

/-! # WP-BRAUER COMPLETENESS r1 — the decision procedure + the permutation standard-form layer

Soundness ships (`brauerConv_sound`: `BrauerConv n a b → brauerDiagramOf n a = brauerDiagramOf n b`).  This file
opens the CONVERSE (completeness) rung and lands its first, fully-closed sub-pieces. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The connectivity-congruence DECISION (completeness via the shipped `whisker` primitive) -/

/-- ★ **`BrauerConv` completeness w.r.t. the connectivity congruence (UNCONDITIONAL).**  Two words that induce the
SAME `DiagramType` are `BrauerConv`-convertible.  The three whisker premises (equal open-wire count, equal loops, and
the agreeing boundary same-component view) come out of `matchingConnectivityViewSim_ofExtractEq` on the diagram
equality alone, fired through the shipped `BrauerConv.whisker` constructor at the EMPTY prefix — no positivity /
in-range / zero-internal side condition needed.  Together with `brauerConv_sound` this makes `BrauerConv` provably
equal to diagram equality.  HONEST SCOPE: this closes completeness for the connectivity-congruence relation whose
`whisker` constructor already supplies the boundary-view move; it is NOT the pure five-relation straightening
(deriving that `whisker` move from the five relations is `fxBrauer_hasFreeBrauerStraighteningNF`, still `false`). -/
theorem brauerConv_complete (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight) :
    BrauerConv bottomCount wordLeft wordRight := by
  have viewSim := matchingConnectivityViewSim_ofExtractEq bottomCount
    (processBrauer (brauerSeed bottomCount) wordLeft)
    (processBrauer (brauerSeed bottomCount) wordRight) diagramEq
  exact BrauerConv.whisker bottomCount [] wordLeft wordRight
    viewSim.lengthEq viewSim.loopsEq
    (fun firstIndex secondIndex firstBound secondBound =>
      viewSim.viewAgrees firstIndex secondIndex
        (viewSim.lengthEq ▸ firstBound) (viewSim.lengthEq ▸ secondBound))

/-- ★ **`BrauerConv` is EXACTLY diagram equality.**  Soundness (`brauerConv_sound`) and completeness
(`brauerConv_complete`) together: two words are `BrauerConv`-convertible iff they induce the same `DiagramType`. -/
theorem brauerConv_iff_diagram (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom) :
    BrauerConv bottomCount wordLeft wordRight
      ↔ brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight :=
  ⟨brauerConv_sound, brauerConv_complete bottomCount wordLeft wordRight⟩

/-- ★ **`BrauerConv` is DECIDABLE.**  The decision is diagram equality (`DiagramType` has a computing `DecidableEq`):
`isTrue` via `brauerConv_complete`, `isFalse` via `brauerConv_sound` on the contrapositive.  This is the full
decision procedure for the connectivity-congruence Brauer word problem — finite matchings, no search. -/
instance decidableBrauerConv (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom) :
    Decidable (BrauerConv bottomCount wordLeft wordRight) :=
  if diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight then
    isTrue (brauerConv_complete bottomCount wordLeft wordRight diagramEq)
  else
    isFalse (fun conv => diagramEq (brauerConv_sound conv))

/-- The decision as a `Bool` — `true` exactly when the two words induce the same diagram. -/
def decideBrauerConvBool (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom) : Bool :=
  decide (brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight)

/-- Decision smoke: a double crossing IS convertible to the identity (the decision returns `true`) — kept cheap
(two strands) since comparing two deep Yang–Baxter union-find reductions blows up the kernel. -/
theorem decideBrauerConvBool_double_crossing :
    decideBrauerConvBool 2 [crossingAt 0, crossingAt 0] [] = true := by decide

/-- Decision smoke: the crossing is NOT convertible to the identity pair (the decision returns `false`). -/
theorem decideBrauerConvBool_crossing_ne_identity :
    decideBrauerConvBool 2 [crossingAt 0] [identityStrandAt 0, identityStrandAt 1] = false := by
  decide

/-! ## Local subtraction-free arithmetic (propext-free) -/

/-- `value + 2 - 2 = value` — a single `rfl` (the two `Nat.pred`s cancel the two `Nat.succ`s). -/
private theorem addTwoSubTwoLocal (value : Nat) : value + 2 - 2 = value := rfl

/-- `value - 2 + 2 = value` when `2 ≤ value` — the missing crossing-arity round-trip.  Structural on the
`value + 2` shape (`2 ≤ value` rules out `0` / `1`). -/
private theorem subTwoAddTwoLocal : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | value + 2, _ => by rw [addTwoSubTwoLocal value]

/-- `atoms ++ [] = atoms` — cons-only structural copy (Init's `List.append_nil` route is avoided). -/
private theorem appendNilLocal : (atoms : List BrauerAtom) → atoms ++ [] = atoms
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (appendNilLocal rest)

/-! ## The permutation standard-form layer — definitions

A crossing-only word straightens to a normal form determined solely by the permutation of its through-strands
(Matsumoto for `S_n`; Lehrer–Zhang arXiv:1207.5889 §2, the symmetric-group sub-block of the Brauer presentation).
This section defines the permutation infrastructure the straightening consumes: the one-line permutation, the
crossing-word / permutation translation, and the diagram a permutation induces. -/

/-- ★ **One adjacent transposition on a one-line permutation** — swap the entries at positions `position` and
`position + 1` (a no-op past the end).  Structural on the list, full-enum matches, propext-free. -/
def applyAdjacentSwap : List Nat → Nat → List Nat
  | [], _ => []
  | first :: [], _ => first :: []
  | first :: second :: rest, 0 => second :: first :: rest
  | first :: second :: rest, position + 1 => first :: applyAdjacentSwap (second :: rest) position

/-- ★ **A crossing-only word from a list of adjacent-transposition positions** — each position becomes a crossing
generator. -/
def crossingWord : List Nat → List BrauerAtom
  | [] => []
  | position :: rest => crossingAt position :: crossingWord rest

/-- ★ **The through-strand permutation a crossing word realizes** — fold the adjacent transpositions over the
identity permutation `[0, 1, …, bottomCount - 1]`, bottom-to-top (head first, matching `processBrauer`). -/
def permuteOfCrossingWord (bottomCount : Nat) (positions : List Nat) : List Nat :=
  positions.foldl applyAdjacentSwap (List.range bottomCount)

/-- The 0-based index of the first occurrence of `target` in a `Nat` list (`0` if absent — for a genuine
permutation every value in `[0, bottomCount)` occurs, so the fallback is never taken).  Full-enum match on the
`Bool` equality, propext-free. -/
def natIndexOfValue : List Nat → Nat → Nat
  | [], _ => 0
  | head :: rest, target =>
      match head == target with
      | true => 0
      | false => natIndexOfValue rest target + 1

/-- ★ **The diagram a through-strand permutation induces** — a crossing-only Brauer diagram: `bottomCount` bottom
ports, `bottomCount` top ports, no loops.  `perm` is the TOP→BOTTOM reading `permuteOfCrossingWord` computes
(`perm[j]` = which bottom strand ends at top port `j`), so top port `j` (boundary index `bottomCount + …` on the
top side) is matched to bottom port `perm[j]`, and bottom port `i` is matched to top port `perm⁻¹[i]`
(`natIndexOfValue perm i`, boundary index `bottomCount + perm⁻¹[i]`). -/
def permutationDiagram (bottomCount : Nat) (perm : List Nat) : DiagramType :=
  { bottomCount := bottomCount,
    topCount := bottomCount,
    partner := (List.range bottomCount).map (fun bottomPort => bottomCount + natIndexOfValue perm bottomPort)
             ++ (List.range bottomCount).map (fun topPort => natListGetAt perm topPort),
    loops := 0 }

/-! ## Standard-form structural lemmas (fully closed) -/

/-- ★ **An adjacent swap preserves permutation length.**  Structural on the swap's own matcher. -/
theorem applyAdjacentSwap_length : (perm : List Nat) → (position : Nat) →
    (applyAdjacentSwap perm position).length = perm.length
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 => by
      show (first :: applyAdjacentSwap (second :: rest) position).length = (first :: second :: rest).length
      show (applyAdjacentSwap (second :: rest) position).length + 1 = (second :: rest).length + 1
      rw [applyAdjacentSwap_length (second :: rest) position]

/-- The crossing word has one generator per input position. -/
theorem crossingWord_length : (positions : List Nat) → (crossingWord positions).length = positions.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (crossingWord_length rest)

/-- Folding adjacent swaps preserves length (each swap does). -/
theorem foldlAdjacentSwap_length : (positions perm : List Nat) →
    (positions.foldl applyAdjacentSwap perm).length = perm.length
  | [], _ => rfl
  | position :: rest, perm => by
      show (rest.foldl applyAdjacentSwap (applyAdjacentSwap perm position)).length = perm.length
      rw [foldlAdjacentSwap_length rest (applyAdjacentSwap perm position),
        applyAdjacentSwap_length perm position]

/-- ★ **The realized permutation has exactly `bottomCount` entries** — a well-formed one-line permutation of the
strands.  From `foldlAdjacentSwap_length` over the identity `List.range bottomCount`. -/
theorem permuteOfCrossingWord_length (bottomCount : Nat) (positions : List Nat) :
    (permuteOfCrossingWord bottomCount positions).length = bottomCount := by
  show (positions.foldl applyAdjacentSwap (List.range bottomCount)).length = bottomCount
  rw [foldlAdjacentSwap_length positions (List.range bottomCount), rangeLength_local bottomCount]

/-- The permutation diagram declares the crossing-only shape: equal bottom / top counts, zero loops. -/
theorem permutationDiagram_shape (bottomCount : Nat) (perm : List Nat) :
    (permutationDiagram bottomCount perm).bottomCount = bottomCount
      ∧ (permutationDiagram bottomCount perm).topCount = bottomCount
      ∧ (permutationDiagram bottomCount perm).loops = 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ## The readback direction — SMOKES (the general theorem is named as the r2 residual)

`brauerDiagramOf n (crossingWord w) = permutationDiagram n (permuteOfCrossingWord n w)`: the union-find boundary
read-off tracks the permutation graph.  Both sides COMPUTE, so the alignment is validated concretely here; the
general structural induction (a state invariant relating the union-find connectivity to the permutation through
one `stepWiring` crossing) is the r2 residual `fxBrauer_hasCrossingOnlyReadback`. -/

/-- Readback smoke — the empty word straightens to the identity permutation diagram (`bottomCount = 2`). -/
theorem readback_smoke_identity_two :
    brauerDiagramOf 2 (crossingWord []) = permutationDiagram 2 (permuteOfCrossingWord 2 []) := by decide

/-- Readback smoke — one crossing realizes the transposition `[1, 0]`. -/
theorem readback_smoke_single_crossing :
    brauerDiagramOf 2 (crossingWord [0]) = permutationDiagram 2 (permuteOfCrossingWord 2 [0]) := by decide

/-- Readback smoke — a double crossing (R2 cancellation) straightens to the identity permutation diagram. -/
theorem readback_smoke_double_crossing :
    brauerDiagramOf 2 (crossingWord [0, 0]) = permutationDiagram 2 (permuteOfCrossingWord 2 [0, 0]) := by decide

/-- Readback smoke — a two-crossing three-strand word realizes the 3-cycle `[1, 2, 0]`. -/
theorem readback_smoke_three_strand :
    brauerDiagramOf 3 (crossingWord [0, 1]) = permutationDiagram 3 (permuteOfCrossingWord 3 [0, 1]) := by decide

/-- Readback smoke — the Yang–Baxter word straightens to the full reversal `[2, 1, 0]`. -/
theorem readback_smoke_yangBaxter :
    brauerDiagramOf 3 (crossingWord [0, 1, 0]) = permutationDiagram 3 (permuteOfCrossingWord 3 [0, 1, 0]) := by
  decide

/-! ## The crossing-word COXETER moves — real relation firings through the shipped context machinery

The three generators of Matsumoto's theorem for `S_n` (relate two crossing words iff equal permutation), each a
reusable `BrauerConv` convertibility fired through the shipped contextual relation machinery:

  * **cancel** (R2, `s² = 1`) — a trailing double crossing after any prefix straightens away;
  * **braid** (R3, `s_p s_{p+1} s_p = s_{p+1} s_p s_{p+1}`) — a trailing braid triple after any prefix;
  * **commute** (`s_p s_q = s_q s_p` for `q ≥ p + 2`) — two distant crossings after any prefix swap, via the
    shipped `interchange` (Godement) constructor.

Each fires a REAL relation (`crossingInvolution_diagram_sound` / `yangBaxter_diagram_sound` / the interchange move)
in arbitrary horizontal context via `brauerConv_relation_inContext` / `BrauerConv.interchange`. -/

/-- ★ **Coxeter CANCEL (R2 in context).**  After any in-range prefix leaving post-prefix width
`offset + (2 + rightPad)`, a trailing double crossing at `offset` is convertible to the empty tail — the crossing
involution `s² = 1` whiskered in arbitrary horizontal context, via `brauerConv_relation_inContext`. -/
theorem brauerConv_crossing_cancel (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (offset rightPad : Nat)
    (widthEq : (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
                = offset + (2 + rightPad)) :
    BrauerConv bottomCount (prefixAtoms ++ [crossingAt offset, crossingAt offset]) prefixAtoms := by
  have base : BrauerConv bottomCount
      (prefixAtoms ++ [crossingAt offset, crossingAt offset]) (prefixAtoms ++ ([] : List BrauerAtom)) :=
    brauerConv_relation_inContext bottomCount bottomPos prefixAtoms prefixInRange
      offset 2 rightPad crossingInvolutionRelation.lhs crossingInvolutionRelation.rhs widthEq
      (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
      (BrauerWordInRange.nil 2) rfl rfl crossingInvolution_diagram_sound
  rw [appendNilLocal prefixAtoms] at base
  exact base

/-- ★ **Coxeter BRAID (R3 in context).**  After any in-range prefix leaving post-prefix width
`offset + (3 + rightPad)`, a trailing braid triple `s_offset s_{offset+1} s_offset` is convertible to
`s_{offset+1} s_offset s_{offset+1}` — Yang–Baxter whiskered in arbitrary horizontal context. -/
theorem brauerConv_crossing_braid (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (offset rightPad : Nat)
    (widthEq : (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
                = offset + (3 + rightPad)) :
    BrauerConv bottomCount
      (prefixAtoms ++ [crossingAt offset, crossingAt (offset + 1), crossingAt offset])
      (prefixAtoms ++ [crossingAt (offset + 1), crossingAt offset, crossingAt (offset + 1)]) :=
  brauerConv_relation_inContext bottomCount bottomPos prefixAtoms prefixInRange
    offset 3 rightPad yangBaxterRelation.lhs yangBaxterRelation.rhs widthEq
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3))))
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3))))
    rfl rfl yangBaxter_diagram_sound

/-- ★ **Coxeter COMMUTE (distant transpositions, via the interchange constructor).**  After any prefix, two
crossings at positions `positionLeft` and `positionRight` with `positionLeft + 2 ≤ positionRight` (disjoint
windows) commute — the shipped fully-contextual `BrauerConv.interchange` (Godement) move at two crossing
generators.  The interchange's output position `positionRight - 2 + 2` is normalized back to `positionRight`. -/
theorem brauerConv_crossing_commute (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (positionLeft positionRight : Nat)
    (disjoint : positionLeft + 2 ≤ positionRight)
    (windowRight : positionRight + 2
                    ≤ (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) :
    BrauerConv bottomCount
      (prefixAtoms ++ [crossingAt positionLeft, crossingAt positionRight])
      (prefixAtoms ++ [crossingAt positionRight, crossingAt positionLeft]) := by
  have twoLe : 2 ≤ positionRight := Nat.le_trans (Nat.le_add_left 2 positionLeft) disjoint
  have base : BrauerConv bottomCount
      (prefixAtoms ++ [crossingAt positionLeft, ⟨positionRight - 2 + 2, crossingWiring⟩])
      (prefixAtoms ++ [crossingAt positionRight, crossingAt positionLeft]) :=
    BrauerConv.interchange bottomCount prefixAtoms positionLeft positionRight
      crossingWiring crossingWiring bottomPos disjoint windowRight
  rw [subTwoAddTwoLocal positionRight twoLe] at base
  exact base

/-! ### Coxeter-move non-vacuity (concrete inhabitants) -/

/-- Non-vacuity — R2 cancel at the seed: a double crossing on two strands straightens to nothing. -/
theorem brauerConv_crossing_cancel_smoke : BrauerConv 2 [crossingAt 0, crossingAt 0] [] :=
  brauerConv_crossing_cancel 2 (by decide) [] (BrauerWordInRange.nil 2) 0 0 (by decide)

/-- Non-vacuity — R3 braid at the seed: the two Yang–Baxter words on three strands are convertible. -/
theorem brauerConv_crossing_braid_smoke :
    BrauerConv 3 [crossingAt 0, crossingAt 1, crossingAt 0] [crossingAt 1, crossingAt 0, crossingAt 1] :=
  brauerConv_crossing_braid 3 (by decide) [] (BrauerWordInRange.nil 3) 0 0 (by decide)

/-- Non-vacuity — distant commute at the seed: crossings at positions `0` and `2` on four strands commute. -/
theorem brauerConv_crossing_commute_smoke :
    BrauerConv 4 [crossingAt 0, crossingAt 2] [crossingAt 2, crossingAt 0] :=
  brauerConv_crossing_commute 4 (by decide) [] 0 2 (by decide) (by decide)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the connectivity-congruence DECISION is SHIPPED.**  `brauerConv_complete` (unconditional:
diagram equality `→ BrauerConv`, via the shipped `whisker` primitive at the empty prefix) plus `brauerConv_sound`
give `brauerConv_iff_diagram` and the `decidableBrauerConv` instance — the full decision procedure for the Brauer
word problem over the connectivity-congruence relation `BrauerConv`, decided by `DiagramType` equality (finite
matchings, no search).  HONEST SCOPE: this is completeness w.r.t. the relation whose `whisker` constructor already
supplies the boundary-view congruence move; deriving that move from the five relations (the pure straightening NF)
is `fxBrauer_hasFreeBrauerStraighteningNF`, still `false`.  `= true`. -/
def fxBrauer_hasConnectivityCongruenceDecision : Bool := true

/-- ★ **Honesty marker — the permutation standard-form layer is SHIPPED (definitions + closed structural
lemmas).**  `applyAdjacentSwap` / `crossingWord` / `permuteOfCrossingWord` / `permutationDiagram` define the
crossing-only normal-form infrastructure; `applyAdjacentSwap_length`, `crossingWord_length`,
`permuteOfCrossingWord_length`, `permutationDiagram_shape` are the closed well-formedness lemmas.  The readback
`brauerDiagramOf n (crossingWord w) = permutationDiagram n (permuteOfCrossingWord n w)` is validated on concrete
words (`readback_smoke_*`); its general structural proof is the r2 residual.  `= true`. -/
def fxBrauer_hasPermutationStandardForm : Bool := true

/-- ★ **Honesty marker — the three crossing-word COXETER moves are SHIPPED as reusable `BrauerConv` lemmas
(real relation firings).**  `brauerConv_crossing_cancel` (R2 `s² = 1`), `brauerConv_crossing_braid`
(R3 braid), and `brauerConv_crossing_commute` (distant `s_p s_q = s_q s_p`) each fire a genuine relation
(`crossingInvolution_diagram_sound` / `yangBaxter_diagram_sound` / the shipped `interchange` constructor) in
arbitrary horizontal context via `brauerConv_relation_inContext` / `BrauerConv.interchange` — the exact
generators Matsumoto's insertion induction consumes.  Non-vacuous: `brauerConv_crossing_{cancel,braid,commute}_smoke`.
`= true`. -/
def fxBrauer_hasCrossingWordCoxeterMoves : Bool := true

/-- **Honesty marker — the crossing-only STRAIGHTENING (full Matsumoto for `S_n`) is NOT yet assembled.**  The
Coxeter moves + the permutation standard form are shipped, but the insertion induction (`insert_adjacent_conv`:
inserting one adjacent transposition into the canonical reduced word of a permutation, driven by the three Coxeter
moves) and the canonical reduced word `canonicalCrossingWord` (a selection-sort of the permutation) are NOT built.
It additionally needs a crossing-only SUFFIX congruence (`BrauerConv n a b → BrauerConv n (a ++ s) (b ++ s)`,
whiskerRight — currently only whiskerLeft / trailing moves are shipped), which requires a `MatchingConnectivityViewSim`
preservation lemma through `processBrauer` (the Brauer analog of `matchingConnectivityViewSim_processSpine`).  These
three — canonical word, insertion induction, suffix congruence — are the exact r2 residual.  `= false`. -/
def fxBrauer_hasCrossingOnlyStraightening : Bool := false

/-- **Honesty marker — the DEEP free-Brauer straightening NF (deriving the `whisker` congruence primitive from the
five relations) is NOT built.**  The connectivity-congruence decision (`fxBrauer_hasConnectivityCongruenceDecision`)
closes completeness for `BrauerConv` including its `whisker` constructor; the classical Lehrer–Zhang straightening
(arXiv:1207.5889 §2: regular-expression form + raising/lowering `R ∘ L ∼ id` + permutation conjugation, reducing
every diagram to the canonical scaled generator via the Lemma-2.13 trichotomy) would show the five relations +
equivalence + interchange GENERATE all diagram equalities WITHOUT the `whisker` primitive — the honest sense in
which `fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean`) stays `false`.  `= false`. -/
def fxBrauer_hasFreeBrauerStraighteningNF : Bool := false

end FX1Poly.Polygraph
