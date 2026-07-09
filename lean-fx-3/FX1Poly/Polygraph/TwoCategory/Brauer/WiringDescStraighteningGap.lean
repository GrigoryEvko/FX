import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm

/-! # WP-BRAUER-4 r2 — the free-straightening UNDER-GENERATION WALL (machine-refuted)

Soundness ships (`brauerConv_sound`, r15) and the connectivity-congruence decision ships
(`brauerConv_complete` / `decidableBrauerConv`, r1), the latter closing completeness for the relation `BrauerConv`
*including its diagram-gated `whisker` constructor*.  The residual `fxBrauer_hasBrauerCompleteness` names the strictly
harder classical straightening: derive the diagram equality WITHOUT the `whisker` cheat — from the five relations
(two snakes, R2 involutivity, R3 Yang–Baxter, R1 cap-slide) plus the interchange (Godement) plus contextual
whiskering.  This file proves that residual is a genuine WALL: **the five relations UNDER-GENERATE the free Brauer
category.**

## The invariant — total crossing-count parity (a Z/2 that the five relations cannot move)

Read a generator word to `crossingParity` = (number of `crossing` generators) mod 2, folded as a `boolXor`.  Every
generating move of the five-relation contextual closure preserves it:

  * **S1 / S2 snake** `[cup, cap] = []` — `0 ≡ 0` (no crossings either side);
  * **R2 involutivity** `[crossing, crossing] = []` — `2 ≡ 0` (both even);
  * **R3 Yang–Baxter** `[X,X,X] = [X,X,X]` — `3 ≡ 3` (both odd);
  * **R1 cap-slide** `[X, cap] = [X, cap]` — `1 ≡ 1` (one crossing each side);
  * **interchange** permutes the generator multiset (crossing count exact);
  * **whiskering** (prepend / append / offset-shift) cancels a common prefix/suffix in the parity difference.

So `crossingParity` is invariant along ANY derivation in `BrauerConvFree` — the honest syntactic over-approximation
of "what the five relations generate" (equivalence + the five relations at any horizontal offset + interchange +
vertical congruence; strictly LARGER than the true closure, so `not (BrauerConvFree a b)` a fortiori refutes
derivability in the true closure).

## The exhibited unreachable pair — the cup untwist `σ ∘ cup = cup`

`[cupAt 0, crossingAt 0]` and `[cupAt 0]` (over `0` bottom wires) induce the SAME Brauer diagram
(`{ bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }`, `brauerUntwist_diagramEq` by `decide`) — a
genuine diagram equality, and hence a genuine `BrauerConv` (`brauerUntwist_isBrauerConv`, via the shipped
`brauerConv_complete`).  But their crossing parities differ (`1 ≠ 0`, `brauerUntwist_parity_ne`), so they are NOT
`BrauerConvFree` (`brauerUntwist_not_brauerConvFree`).  Therefore the untwist `σ ∘ cup = cup` — the missing generator
of the framed / spin cover — is INDEPENDENT of the five relations: the shipped presentation presents a proper Z/2
cover of the Brauer category, not the Brauer category itself (Lehrer–Zhang arXiv:1207.5889 use SEVEN relations
counting the ∗/♯ transforms — the FX five omit the cup untwist and its dual cap untwist).

## Verdict

`fxBrauer_hasBrauerStraighteningGap := true` records the wall; `fxBrauer_hasBrauerCompleteness` STAYS `false`
(honestly, not fabricated).  Soundness (`fxBrauer_hasBrauerSoundness`, r15) and the connectivity-congruence decision
(`fxBrauer_hasConnectivityCongruenceDecision`, r1) are untouched.  The fix is a design choice for the user: add the
two untwist relations `σ ∘ cup = cup` and `cap ∘ σ = cap` (the seven-relation presentation), after which
completeness is classically true — but the straightening PROOF additionally needs the crossing-only Matsumoto
insertion + whiskerRight congruence (`fxBrauer_hasCrossingOnlyStraightening`, still `false`), i.e. further rounds.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A propext-free Boolean parity (`boolXor`) -/

/-- Boolean exclusive-or, matched on the first argument (full-enum, propext-free). -/
def boolXor : Bool → Bool → Bool
  | true, other => not other
  | false, other => other

/-- `boolXor a false = a`. -/
theorem boolXor_false_right (leftBit : Bool) : boolXor leftBit false = leftBit := by
  cases leftBit <;> rfl

/-- `boolXor` is commutative. -/
theorem boolXor_comm (leftBit rightBit : Bool) : boolXor leftBit rightBit = boolXor rightBit leftBit := by
  cases leftBit <;> cases rightBit <;> rfl

/-- `boolXor` is associative. -/
theorem boolXor_assoc (firstBit secondBit thirdBit : Bool) :
    boolXor (boolXor firstBit secondBit) thirdBit = boolXor firstBit (boolXor secondBit thirdBit) := by
  cases firstBit <;> cases secondBit <;> cases thirdBit <;> rfl

/-! ## The crossing-count parity of a generator word -/

/-- Is this wiring the crossing generator?  A structural `Nat.beq` field comparison against `crossingWiring`
(`inputCount = 2`, `outputCount = 2`, `internalLoops = 0`, `arcs = [(0,3),(1,2)]`), correct for ANY `WiringDesc`,
using only `Nat.beq` / `Bool.and` (no `DecidableEq`, propext-free). -/
def arcsAreCrossing : List (Nat × Nat) → Bool
  | [] => false
  | _ :: [] => false
  | firstArc :: secondArc :: [] =>
      Nat.beq firstArc.fst 0 && Nat.beq firstArc.snd 3 && Nat.beq secondArc.fst 1 && Nat.beq secondArc.snd 2
  | _ :: _ :: _ :: _ => false

/-- Whether a `WiringDesc` is the crossing generator — a position-independent Boolean test. -/
def isCrossingWiring (desc : WiringDesc) : Bool :=
  Nat.beq desc.inputCount 2 && Nat.beq desc.outputCount 2
    && Nat.beq desc.internalLoops 0 && arcsAreCrossing desc.arcs

/-- Whether a Brauer atom is a crossing — depends only on its wiring, never on its position. -/
def isCrossingAtom (atom : BrauerAtom) : Bool := isCrossingWiring atom.wiring

/-- ★ **The crossing-count parity of a word** — the `boolXor` fold of "is this atom a crossing?" over the word. -/
def crossingParity : List BrauerAtom → Bool
  | [] => false
  | atom :: rest => boolXor (isCrossingAtom atom) (crossingParity rest)

/-- `crossingParity` splits over concatenation into a `boolXor` (the fold is a monoid homomorphism to `(Bool, xor)`).
Structural on the first word. -/
theorem crossingParity_append : (wordLeft wordRight : List BrauerAtom) →
    crossingParity (wordLeft ++ wordRight) = boolXor (crossingParity wordLeft) (crossingParity wordRight)
  | [], _ => rfl
  | atom :: rest, wordRight => by
      show boolXor (isCrossingAtom atom) (crossingParity (rest ++ wordRight))
         = boolXor (boolXor (isCrossingAtom atom) (crossingParity rest)) (crossingParity wordRight)
      rw [crossingParity_append rest wordRight]
      exact (boolXor_assoc (isCrossingAtom atom) (crossingParity rest) (crossingParity wordRight)).symm

/-- The parity of a two-atom word is the `boolXor` of its two atoms' crossing bits. -/
theorem crossingParity_pair (firstAtom secondAtom : BrauerAtom) :
    crossingParity [firstAtom, secondAtom] = boolXor (isCrossingAtom firstAtom) (isCrossingAtom secondAtom) := by
  show boolXor (isCrossingAtom firstAtom) (boolXor (isCrossingAtom secondAtom) false)
     = boolXor (isCrossingAtom firstAtom) (isCrossingAtom secondAtom)
  rw [boolXor_false_right]

/-! ## Position-shift preserves crossing parity (horizontal whiskering) -/

/-- Shift an atom's boundary position by `shift`, keeping its wiring. -/
def shiftAtom (shift : Nat) (atom : BrauerAtom) : BrauerAtom :=
  { position := atom.position + shift, wiring := atom.wiring }

/-- Shift every atom's position by `shift` — the word "the same generators, `shift` strands to the right",
i.e. firing the word at horizontal offset `shift`.  Structural on the word. -/
def shiftWord (shift : Nat) : List BrauerAtom → List BrauerAtom
  | [] => []
  | atom :: rest => shiftAtom shift atom :: shiftWord shift rest

/-- Shifting an atom's position leaves its crossing bit unchanged (`isCrossingAtom` reads only the wiring). -/
theorem isCrossingAtom_shiftAtom (shift : Nat) (atom : BrauerAtom) :
    isCrossingAtom (shiftAtom shift atom) = isCrossingAtom atom := rfl

/-- ★ **A horizontal offset shift preserves crossing parity** — firing a relation at any offset does not change how
many crossings it contains.  Structural on the word. -/
theorem crossingParity_shiftWord (shift : Nat) : (word : List BrauerAtom) →
    crossingParity (shiftWord shift word) = crossingParity word
  | [] => rfl
  | atom :: rest => by
      show boolXor (isCrossingAtom (shiftAtom shift atom)) (crossingParity (shiftWord shift rest))
         = boolXor (isCrossingAtom atom) (crossingParity rest)
      rw [isCrossingAtom_shiftAtom, crossingParity_shiftWord shift rest]

/-! ## `BrauerConvFree` — the honest syntactic over-approximation of the five-relation closure

The relation generated by { equivalence, the five relations at ANY horizontal offset, the interchange (Godement),
vertical congruence (prepend / append an arbitrary word) }.  It contains the true five-relation contextual closure
(every true move is one of these), and it is DELIBERATELY generous (no boundary / soundness side-condition on
whiskering) — so `not (BrauerConvFree a b)` refutes derivability in the true, smaller closure a fortiori.  It does
NOT include the diagram-gated `whisker` primitive of `BrauerConv` — that primitive is exactly what this wall shows
is INDEPENDENT of the five relations. -/
inductive BrauerConvFree : List BrauerAtom → List BrauerAtom → Prop
  /-- Reflexivity. -/
  | refl (word : List BrauerAtom) : BrauerConvFree word word
  /-- Symmetry. -/
  | symm {wordLeft wordRight : List BrauerAtom} :
      BrauerConvFree wordLeft wordRight → BrauerConvFree wordRight wordLeft
  /-- Transitivity. -/
  | trans {wordLeft wordMid wordRight : List BrauerAtom} :
      BrauerConvFree wordLeft wordMid → BrauerConvFree wordMid wordRight → BrauerConvFree wordLeft wordRight
  /-- S1 snake at horizontal offset `shift`. -/
  | snake (shift : Nat) :
      BrauerConvFree (shiftWord shift snakeRelation.lhs) (shiftWord shift snakeRelation.rhs)
  /-- S2 mirror snake at horizontal offset `shift`. -/
  | snakeMirror (shift : Nat) :
      BrauerConvFree (shiftWord shift snakeMirrorRelation.lhs) (shiftWord shift snakeMirrorRelation.rhs)
  /-- R2 crossing involutivity at horizontal offset `shift`. -/
  | crossingInvolution (shift : Nat) :
      BrauerConvFree (shiftWord shift crossingInvolutionRelation.lhs)
        (shiftWord shift crossingInvolutionRelation.rhs)
  /-- R3 Yang–Baxter at horizontal offset `shift`. -/
  | yangBaxter (shift : Nat) :
      BrauerConvFree (shiftWord shift yangBaxterRelation.lhs) (shiftWord shift yangBaxterRelation.rhs)
  /-- R1 cap slides past a crossing at horizontal offset `shift`. -/
  | capSlide (shift : Nat) :
      BrauerConvFree (shiftWord shift capSlideRelation.lhs) (shiftWord shift capSlideRelation.rhs)
  /-- The interchange (Godement) move: two generators at disjoint positions commute. -/
  | interchange (positionA positionB : Nat) (descA descB : WiringDesc) :
      positionA + descA.inputCount ≤ positionB →
      BrauerConvFree
        [⟨positionA, descA⟩, ⟨positionB - descA.inputCount + descA.outputCount, descB⟩]
        [⟨positionB, descB⟩, ⟨positionA, descA⟩]
  /-- Vertical congruence on the left: prepend a common word. -/
  | whiskerLeft {wordLeft wordRight : List BrauerAtom} (prefixWord : List BrauerAtom) :
      BrauerConvFree wordLeft wordRight → BrauerConvFree (prefixWord ++ wordLeft) (prefixWord ++ wordRight)
  /-- Vertical congruence on the right: append a common word. -/
  | whiskerRight {wordLeft wordRight : List BrauerAtom} (suffixWord : List BrauerAtom) :
      BrauerConvFree wordLeft wordRight → BrauerConvFree (wordLeft ++ suffixWord) (wordRight ++ suffixWord)

/-! ## Each of the five relations has parity-equal sides (the invariant is sound for the presentation) -/

/-- S1 snake: both sides have `0` crossings. -/
theorem crossingParity_snake_sound :
    crossingParity snakeRelation.lhs = crossingParity snakeRelation.rhs := rfl

/-- S2 mirror snake: both sides have `0` crossings. -/
theorem crossingParity_snakeMirror_sound :
    crossingParity snakeMirrorRelation.lhs = crossingParity snakeMirrorRelation.rhs := rfl

/-- R2 involutivity: `2 ≡ 0` crossings (both even). -/
theorem crossingParity_crossingInvolution_sound :
    crossingParity crossingInvolutionRelation.lhs = crossingParity crossingInvolutionRelation.rhs := rfl

/-- R3 Yang–Baxter: `3 ≡ 3` crossings (both odd). -/
theorem crossingParity_yangBaxter_sound :
    crossingParity yangBaxterRelation.lhs = crossingParity yangBaxterRelation.rhs := rfl

/-- R1 cap-slide: `1 ≡ 1` crossings (one each side). -/
theorem crossingParity_capSlide_sound :
    crossingParity capSlideRelation.lhs = crossingParity capSlideRelation.rhs := rfl

/-! ## The invariant is preserved along ANY `BrauerConvFree` derivation -/

/-- ★ **`crossingParity` is a `BrauerConvFree` invariant.**  By induction on the derivation: the equivalence closure
by `Eq`; each of the five relations by its parity-equal sides through the horizontal-offset lemma
`crossingParity_shiftWord`; the interchange by `boolXor` commutativity (it permutes the generator multiset); the two
whiskerings by `crossingParity_append` cancelling the common prefix / suffix. -/
theorem crossingParity_brauerConvFree {wordLeft wordRight : List BrauerAtom}
    (conv : BrauerConvFree wordLeft wordRight) : crossingParity wordLeft = crossingParity wordRight := by
  induction conv with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight
  | snake shift =>
      rw [crossingParity_shiftWord, crossingParity_shiftWord, crossingParity_snake_sound]
  | snakeMirror shift =>
      rw [crossingParity_shiftWord, crossingParity_shiftWord, crossingParity_snakeMirror_sound]
  | crossingInvolution shift =>
      rw [crossingParity_shiftWord, crossingParity_shiftWord, crossingParity_crossingInvolution_sound]
  | yangBaxter shift =>
      rw [crossingParity_shiftWord, crossingParity_shiftWord, crossingParity_yangBaxter_sound]
  | capSlide shift =>
      rw [crossingParity_shiftWord, crossingParity_shiftWord, crossingParity_capSlide_sound]
  | interchange positionA positionB descA descB _disjoint =>
      rw [crossingParity_pair, crossingParity_pair]
      exact boolXor_comm _ _
  | whiskerLeft prefixWord _ ih =>
      rw [crossingParity_append, crossingParity_append, ih]
  | whiskerRight suffixWord _ ih =>
      rw [crossingParity_append, crossingParity_append, ih]

/-! ## `BrauerConvFree` is a genuine, inhabited relation (non-vacuity + it embeds the seed relations) -/

/-- R2 at the seed IS a `BrauerConvFree` move (`shiftWord 0` is the identity up to `+ 0`). -/
theorem brauerConvFree_crossingInvolution_seed :
    BrauerConvFree [crossingAt 0, crossingAt 0] [] :=
  BrauerConvFree.crossingInvolution 0

/-- R3 Yang–Baxter at the seed IS a `BrauerConvFree` move — it genuinely relates two DISTINCT words. -/
theorem brauerConvFree_yangBaxter_seed :
    BrauerConvFree [crossingAt 0, crossingAt 1, crossingAt 0] [crossingAt 1, crossingAt 0, crossingAt 1] :=
  BrauerConvFree.yangBaxter 0

/-! ## The WALL — the cup untwist is an equal diagram unreachable by the five relations -/

/-- ★ **The untwist pair induces the SAME Brauer diagram.**  A cup then a crossing on its two legs
(`[cupAt 0, crossingAt 0]`) and a bare cup (`[cupAt 0]`) over `0` bottom wires both read off
`{ bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }` — a genuine diagram equality. -/
theorem brauerUntwist_diagramEq :
    brauerDiagramOf 0 [cupAt 0, crossingAt 0] = brauerDiagramOf 0 [cupAt 0] := by decide

/-- The untwist pair IS therefore a genuine `BrauerConv` (via the shipped connectivity-congruence completeness).  So
the pair is a real diagram equality of the full relation — the five relations simply cannot reach it. -/
theorem brauerUntwist_isBrauerConv :
    BrauerConv 0 [cupAt 0, crossingAt 0] [cupAt 0] :=
  brauerConv_complete 0 [cupAt 0, crossingAt 0] [cupAt 0] brauerUntwist_diagramEq

/-- ★ **The untwist pair has DIFFERENT crossing parity** — `1 ≠ 0`.  This is the finer invariant beyond
matching + loops: it is NOT a Brauer-diagram invariant (the untwist witnesses that), yet it IS a sound invariant of
the five-relation closure. -/
theorem brauerUntwist_parity_ne :
    crossingParity [cupAt 0, crossingAt 0] ≠ crossingParity [cupAt 0] := by decide

/-- ★★ **THE WALL** — the untwist `σ ∘ cup = cup` is NOT derivable from the five relations.  Since `crossingParity`
is a `BrauerConvFree` invariant (`crossingParity_brauerConvFree`) but the pair's parities differ
(`brauerUntwist_parity_ne`), no derivation using { equivalence, the five relations at any offset, interchange,
whiskering } relates them.  As `BrauerConvFree` strictly OVER-approximates the true five-relation closure, the true
closure cannot reach the pair either.  Yet the pair is an equal diagram (`brauerUntwist_diagramEq`) — hence the five
relations UNDER-GENERATE the free Brauer category. -/
theorem brauerUntwist_not_brauerConvFree :
    ¬ BrauerConvFree [cupAt 0, crossingAt 0] [cupAt 0] :=
  fun conv => brauerUntwist_parity_ne (crossingParity_brauerConvFree conv)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the free-straightening WALL is MACHINE-REFUTED.**  The five relations (two snakes, R2, R3,
R1 cap-slide) UNDER-GENERATE the free Brauer category: `crossingParity` (total crossing count mod 2) is invariant
along `BrauerConvFree` — the honest syntactic over-approximation of their contextual closure
(`crossingParity_brauerConvFree`, discharged via the per-relation parity-equal sides + `crossingParity_shiftWord` +
`crossingParity_append` + `boolXor_comm`) — but the cup untwist `[cupAt 0, crossingAt 0]` vs `[cupAt 0]` is an EQUAL
Brauer diagram (`brauerUntwist_diagramEq`, `decide`) whose crossing parity FLIPS (`1 ≠ 0`,
`brauerUntwist_parity_ne`), so it is `not BrauerConvFree` (`brauerUntwist_not_brauerConvFree`) yet a genuine
`BrauerConv` (`brauerUntwist_isBrauerConv`).  The missing generator is the cup untwist `σ ∘ cup = cup` (and its dual
`cap ∘ σ = cap`): the shipped presentation presents a proper Z/2 cover of the Brauer category (Lehrer–Zhang
arXiv:1207.5889 use SEVEN relations; the FX five omit both untwists).  `= true`. -/
def fxBrauer_hasBrauerStraighteningGap : Bool := true

/-- **Honesty marker — the crossing-count parity invariant is SOUND for the five relations.**  Each relation's two
sides have equal `crossingParity` (`crossingParity_{snake,snakeMirror,crossingInvolution,yangBaxter,capSlide}_sound`),
so the invariant genuinely bounds the presentation from above; it separates the untwist pair only because that pair
needs the ABSENT untwist relation.  `= true`. -/
def fxBrauer_hasCrossingParityInvariant : Bool := true

end FX1Poly.Polygraph
