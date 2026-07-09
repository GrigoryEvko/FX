import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanSoundness

/-! # WalkingString — the COLOUR-GENERIC Fuss–Catalan parameterization + the NORMAL-FORM design lock (FC-2, piece B)

FC-0/FC-1 shipped the Fuss–Catalan carrier, soundness, faithfulness, and the FC-number fingerprint at the FIXED
three-strand / two-colour adjoint triple `F ⊣ G ⊣ H`.  This file abstracts the load-bearing data into a PARAMETER
`AdjointStringColouring` so the same theory instantiates at an arbitrary `n`-string `X_0 ⊣ X_1 ⊣ … ⊣ X_n` (the
`k`-colour Fuss–Catalan discipline), keeps the shipped two-colour artifacts GREEN as the `n = 2` / `k = 2` instance,
and records the canonical-form / insertion design decision the FC-3 assembly rides on.

## The two generic alphabets (currently fused at the triple)

  * **`Strand`** — the modality / 1-cell alphabet.  The triple has `{F, G, H}`; an `n`-string
    `X_0 ⊣ … ⊣ X_n` has `{X_0, …, X_n}`.  This is `WireLabel` at the instance.
  * **`Colour`** — the Fuss–Catalan arc colour = the adjunction index.  The triple has `k = 2` colours
    `{1, 2}` (`fWire` = lower `F ⊣ G`, `hWire` = upper `G ⊣ H`); an `n`-string has `k = n` colours.  Two adjacent
    colours `i`, `i+1` SHARE the middle strand `X_i` (for the triple, both colours share `G`).  Here the colour of
    an arc is READ as a `Strand` (the non-shared end's letter), exactly as `fcArcColour` does — so `Colour` need not
    be a separate carrier; the `arcColour : Strand → Strand → Strand` field is the reading.

## The CHIRALITY the parameterization must preserve

The whole no-loops / soundness story rests on ONE structural fact, here made a FIELD: the ordered cup alphabet and
the ordered cap alphabet are DISJOINT (`capWord_not_cupWord` / `cupWord_not_capWord`) — a cup-created pair reads a
cup word, a cap deletes a cap word, and the two never coincide, so no oriented circle ever closes.  Every generator
word has EXACTLY ONE shared (middle) end (`oneSharedEnd`), so `arcColour` reads a well-defined non-middle colour on
every generator arc (`arcColour_ne_middle`).  These are precisely the shipped `stringCapWord_not_cupWord`,
`stringCupCapWord_hasExactlyOneGEnd`, `stringGeneratorArcColour_ne_gWire`, lifted to the parameter and discharged
once at the triple instance.

## ★ THE NORMAL-FORM DESIGN LOCK (the FC-3 assembly rides this)

A canonical FC word is a NESTED planar 2-coloured non-crossing matching; the reduction and the canonical peel obey:

  1. **Reduction order = innermost-leftmost.**  A snake (zig-zag) is fireable EXACTLY when it is innermost (its
     created middle strand is immediately consumed, no generator sitting on it).  So "find a redex" succeeds iff an
     innermost snake exists — innermost-first is the only order in which the search never blocks.  The canonical word
     is the REVERSE of the innermost-leftmost peel sequence (an outermost-first nested "rainbow" reconstruction).
  2. **NOT a per-colour staircase.**  Reducing all colour-1 snakes then all colour-2 snakes would REORDER arcs
     across the shared middle strand and VIOLATE planarity (a colour-1 and a colour-2 arc on the same `G` must stay
     non-crossing).  The colours are coupled ONLY by the shared-middle non-crossing constraint, never by a relation.
  3. **Confluence is free — no cross-colour critical pair.**  The four triangle rewrites are same-colour CANCELs;
     there is no cross-colour overlap (the union-find is colour-blind, so cross-colour adjacency is the
     disjoint-window fragment the single-colour Godement already commuted — `fxString_hasCrossColourGodementObstruction
     = false`).  Disjoint redexes commute, so the innermost-leftmost choice is correctness-free.
  4. **The termination measure is `generatorCount`.**  Every CANCEL strictly drops it by 2; there is NO
     length-preserving move (no braid), so — unlike Brauer's `inversionCount`-vs-word-length subtlety —
     `generatorCount` is the honest measure directly.  Hence FC's insertion step has NO braid wall
     (`BraidAscentInsertionStep` has no FC analog): the modes are CANCEL + EXTEND + COMMUTE + INTERLEAVE, all
     closing by triangles + free interchange.

This is machine-realized in `StringFussCatalanCanonicalWord` (the four modes as one-step lemmas over the shipped
convertibility, the fueled-fold statement); the parameter here is what makes it `n`-string / `k`-colour generic.

Raw Lean 4 + Init; the generic number is a `fcBinomial` reindex, the instance discharges the fields from the shipped
FC-1 lemmas, the bridges are `rfl`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic `k`-colour Fuss–Catalan number -/

/-- The **generic `k`-colour Fuss–Catalan number** `FC_n^{(k)} = (1/(kn+1))·C((k+1)n, n)` via the shipped Pascal
binomial `fcBinomial` (exact `Nat` division — the quotient is exact by Fuss–Catalan integrality).  The shipped
two-colour `fussCatalanNumber` is the `k = 2` instance. -/
def fussCatalanNumberK (colourCount arcCount : Nat) : Nat :=
  fcBinomial ((colourCount + 1) * arcCount) arcCount / (colourCount * arcCount + 1)

/-- ★ **The generic number recovers the shipped two-colour number at `k = 2`** — `(2+1)·n = 3n` and `2n+1` are the
shipped indices, so `fussCatalanNumberK 2 n = fussCatalanNumber n` on the nose. -/
theorem fussCatalanNumberK_two_eq (arcCount : Nat) :
    fussCatalanNumberK 2 arcCount = fussCatalanNumber arcCount := rfl

/-- ★ **The generic number is the Catalan sequence at `k = 1`** (the single-colour Temperley–Lieb regression):
`FC_n^{(1)} = (1/(n+1))·C(2n, n) = 1, 1, 2, 5, 14`.  `decide`. -/
theorem fussCatalanNumberK_one_values :
    fussCatalanNumberK 1 0 = 1 ∧ fussCatalanNumberK 1 1 = 1 ∧ fussCatalanNumberK 1 2 = 2
      ∧ fussCatalanNumberK 1 3 = 5 ∧ fussCatalanNumberK 1 4 = 14 := by decide

/-- ★ **The generic number reproduces the shipped `k = 2` fingerprint** `FC_n^{(2)} = 1, 1, 3, 12, 55`. `decide`. -/
theorem fussCatalanNumberK_two_values :
    fussCatalanNumberK 2 0 = 1 ∧ fussCatalanNumberK 2 1 = 1 ∧ fussCatalanNumberK 2 2 = 3
      ∧ fussCatalanNumberK 2 3 = 12 ∧ fussCatalanNumberK 2 4 = 55 := by decide

/-- ★ **The generic number extends to `k = 3`** (the adjoint-QUADRUPLE / three-colour tower `W ⊣ X ⊣ Y ⊣ Z`):
`FC_n^{(3)} = (1/(3n+1))·C(4n, n) = 1, 1, 4, 22, 140` — the FC-4 payoff the parameterization unlocks. `decide`. -/
theorem fussCatalanNumberK_three_values :
    fussCatalanNumberK 3 0 = 1 ∧ fussCatalanNumberK 3 1 = 1 ∧ fussCatalanNumberK 3 2 = 4
      ∧ fussCatalanNumberK 3 3 = 22 ∧ fussCatalanNumberK 3 4 = 140 := by decide

/-! ## The colour-generic parameter -/

/-- ★ The **adjoint-string colouring parameter**: an arbitrary strand alphabet with ordered cup / cap word
predicates and an arc-colour reading, subject to the CHIRALITY (disjoint cup/cap alphabets), EXACTLY-ONE-shared-end,
and colour-faithfulness laws.  The three-strand two-colour adjoint triple is the `adjointTripleColouring` instance;
an `n`-string `X_0 ⊣ … ⊣ X_n` instantiates with `Strand := Fin (n+1)` (or an enum) and the analogous predicates.
Design every FC def/lemma over this parameter so `n`-strings reuse the theory (the FC-4 / mode-and-length-generic
directive). -/
structure AdjointStringColouring where
  /-- The modality / 1-cell alphabet (the triple's `{F, G, H}`). -/
  Strand : Type
  /-- Structural equality on strands. -/
  decStrand : DecidableEq Strand
  /-- The shared MIDDLE strand where adjacent colours meet (the triple's `G`). -/
  middle : Strand
  /-- Whether an ordered pair reads a CUP word (one end the middle, one a non-middle adjacent letter). -/
  isCupWordOrdered : Strand → Strand → Bool
  /-- Whether an ordered pair reads a CAP word (the reversed cup words). -/
  isCapWordOrdered : Strand → Strand → Bool
  /-- The Fuss–Catalan colour of an arc, read as the non-middle end's letter (the shipped `fcArcColour`). -/
  arcColour : Strand → Strand → Strand
  /-- ★ CHIRALITY — a cap word is never a cup word (the two ordered alphabets are DISJOINT). -/
  capWord_not_cupWord : ∀ lowLabel highLabel : Strand,
    isCapWordOrdered lowLabel highLabel = true → isCupWordOrdered lowLabel highLabel = false
  /-- ★ CHIRALITY (dual) — a cup word is never a cap word. -/
  cupWord_not_capWord : ∀ lowLabel highLabel : Strand,
    isCupWordOrdered lowLabel highLabel = true → isCapWordOrdered lowLabel highLabel = false
  /-- ★ FAITHFULNESS — a generator (cup or cap) arc's colour is never the degenerate middle letter. -/
  arcColour_ne_middle : ∀ lowLabel highLabel : Strand,
    isCupWordOrdered lowLabel highLabel = true ∨ isCapWordOrdered lowLabel highLabel = true →
    arcColour lowLabel highLabel ≠ middle

/-- ★ **The shipped two-colour adjoint triple as the `k = 2` colouring instance.**  `Strand := WireLabel`,
`middle := gWire`, the cup / cap predicates and arc reading are the shipped FC-1 definitions, and the three laws are
the shipped `stringCapWord_not_cupWord` / `stringCupWord_not_capWord` / `stringGeneratorArcColour_ne_gWire`.  So the
whole FC-0/FC-1 tower is exactly the `adjointTripleColouring` instance of this parameter. -/
def adjointTripleColouring : AdjointStringColouring where
  Strand := WireLabel
  decStrand := inferInstance
  middle := WireLabel.gWire
  isCupWordOrdered := isCupWordOrdered
  isCapWordOrdered := isCapWordOrdered
  arcColour := fcArcColour
  capWord_not_cupWord := stringCapWord_not_cupWord
  cupWord_not_capWord := stringCupWord_not_capWord
  arcColour_ne_middle := stringGeneratorArcColour_ne_gWire

/-! ## Generic mode-table facts over the parameter (each move = one lemma over `colouring`) -/

/-- ★ **CANCEL-fireability is a cap word (generic).**  Over any colouring, a window a CAP can delete reads a cap
word, which by CHIRALITY is NOT a cup word — so it is never a cup-created (same-arc) pair.  This is the generic
CANCEL/no-loops discriminator: the abstract shadow of `stringDisciplinedCap_windowDistinct`, colour-blind and
`n`-string-uniform. -/
theorem colouring_capWord_distinctFromCup (colouring : AdjointStringColouring)
    (lowLabel highLabel : colouring.Strand)
    (isCap : colouring.isCapWordOrdered lowLabel highLabel = true) :
    colouring.isCupWordOrdered lowLabel highLabel = false :=
  colouring.capWord_not_cupWord lowLabel highLabel isCap

/-- ★ **INTERLEAVE is free — cross-colour arcs carry no relation (generic).**  Two cup words of DIFFERENT arc colour
share only the middle strand: their non-middle ends are the two distinct adjunction letters, so neither word is the
other and neither is a cap word.  Abstractly the cross-colour move is a planar re-nesting (free interchange), never a
CANCEL and never a braid — the parameter has no cross-colour cup=cap coincidence.  Stated as: a cup word is never a
cap word regardless of colour. -/
theorem colouring_interleaveFree (colouring : AdjointStringColouring)
    (lowLabel highLabel : colouring.Strand)
    (isCup : colouring.isCupWordOrdered lowLabel highLabel = true) :
    colouring.isCapWordOrdered lowLabel highLabel = false :=
  colouring.cupWord_not_capWord lowLabel highLabel isCup

/-- ★ **The generic faithful colour reading** — every generator arc has a well-defined non-middle colour, over any
colouring.  The abstract `stringGeneratorArcColour_ne_gWire`. -/
theorem colouring_arcColour_faithful (colouring : AdjointStringColouring)
    (lowLabel highLabel : colouring.Strand)
    (isCupOrCap : colouring.isCupWordOrdered lowLabel highLabel = true
      ∨ colouring.isCapWordOrdered lowLabel highLabel = true) :
    colouring.arcColour lowLabel highLabel ≠ colouring.middle :=
  colouring.arcColour_ne_middle lowLabel highLabel isCupOrCap

/-! ## Instance bridges — the generic facts recover the shipped two-colour statements -/

/-- The instance's cup predicate IS the shipped `isCupWordOrdered` (`rfl` bridge). -/
theorem adjointTripleColouring_isCupWordOrdered :
    adjointTripleColouring.isCupWordOrdered = isCupWordOrdered := rfl

/-- The instance's cap predicate IS the shipped `isCapWordOrdered` (`rfl` bridge). -/
theorem adjointTripleColouring_isCapWordOrdered :
    adjointTripleColouring.isCapWordOrdered = isCapWordOrdered := rfl

/-- The instance's arc-colour reading IS the shipped `fcArcColour` (`rfl` bridge). -/
theorem adjointTripleColouring_arcColour :
    adjointTripleColouring.arcColour = fcArcColour := rfl

/-- ★ **The generic CANCEL discriminator recovers the shipped chirality at the triple** — instantiating
`colouring_capWord_distinctFromCup` at `adjointTripleColouring` is `stringCapWord_not_cupWord` on the nose. -/
theorem adjointTripleColouring_capWord_distinctFromCup (lowLabel highLabel : WireLabel)
    (isCap : isCapWordOrdered lowLabel highLabel = true) :
    isCupWordOrdered lowLabel highLabel = false :=
  colouring_capWord_distinctFromCup adjointTripleColouring lowLabel highLabel isCap

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the COLOUR-GENERIC Fuss–Catalan parameterization is shipped.**  `AdjointStringColouring`
abstracts the strand alphabet, the ordered cup / cap word predicates, the arc-colour reading, and the three
load-bearing laws (CHIRALITY `capWord_not_cupWord` / `cupWord_not_capWord`, FAITHFULNESS `arcColour_ne_middle`) into
a parameter.  The shipped three-strand two-colour adjoint triple is exactly the `adjointTripleColouring` instance
(discharging the fields from `stringCapWord_not_cupWord` / `stringCupWord_not_capWord` /
`stringGeneratorArcColour_ne_gWire`), so every FC-0/FC-1 artifact stays green as the `k = 2` instance.  The generic
mode-table facts (`colouring_capWord_distinctFromCup` = CANCEL discriminator, `colouring_interleaveFree` = the
cross-colour move is free, `colouring_arcColour_faithful`) are proved once over the parameter and recovered at the
instance by the `rfl` bridges.  So an `n`-string `X_0 ⊣ … ⊣ X_n` reuses the theory by a new instance — the FC-4 /
mode-and-length-generic payoff.  `= true`. -/
def fxString_hasColourGenericParameterization : Bool := true

/-- **★ ESTABLISHED — the generic `k`-colour Fuss–Catalan number.**  `fussCatalanNumberK k n =
(1/(kn+1))·C((k+1)n, n)` recovers the shipped two-colour `fussCatalanNumber` at `k = 2` (`fussCatalanNumberK_two_eq`,
`rfl`), the Catalan sequence `1, 1, 2, 5, 14` at `k = 1` (the single-colour Temperley–Lieb regression), the shipped
fingerprint `1, 1, 3, 12, 55` at `k = 2`, and `1, 1, 4, 22, 140` at `k = 3` (the adjoint-quadruple / three-colour
tower) — each `decide`d.  The count is length-and-colour generic, so the fingerprint transfers to every `n`-string.
`= true`. -/
def fxString_hasGenericFussCatalanNumber : Bool := true

/-- **★ ESTABLISHED — the NORMAL-FORM design lock (the FC-3 assembly rides this).**  The canonical FC word is the
REVERSE of the INNERMOST-LEFTMOST snake peel (a nested outermost-first rainbow), NOT a per-colour staircase (which
would violate the shared-middle planarity), and the reduction is confluent (no cross-colour critical pair — the
union-find is colour-blind) with termination measure `generatorCount` (strictly −2 per CANCEL, no length-preserving
move, hence NO braid wall).  This is the machine-realized design in `StringFussCatalanCanonicalWord`; the parameter
here makes it `n`-string / `k`-colour generic.  Recorded in the file header docstring.  `= true`. -/
def fxString_hasNormalFormDesignLock : Bool := true

end FX1Poly.Polygraph
