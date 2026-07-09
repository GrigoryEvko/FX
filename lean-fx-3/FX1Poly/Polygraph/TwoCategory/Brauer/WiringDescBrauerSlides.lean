import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness

/-! # BREACH r4 — EXTRACT slide moves (P2): the distant cup/cap-past-generator commutes + the straddle finding

The cellular extraction fold (Graham–Lehrer standard form: caps-bottom / crossing-middle / cups-top) sorts a
generator word by sliding cups upward and caps downward past crossings.  Three slide shapes arise:

  * **DISTANT / disjoint-support** — a cup (or cap) and a crossing whose two windows do not overlap.  This is the
    ⊗-bifunctor interchange, and the shipped `BrauerConvFree.interchange` constructor is FULLY GENERIC in its two
    `WiringDesc`s — so every disjoint-support slide is ONE `ofFree (BrauerConvFree.interchange …)` application.  We
    ship them here as named `BrauerConvFree7` lemmas (cup left of crossing / cap / cup), banking the distant leg of
    the fold's move set.  Lehrer–Zhang (arXiv:1207.5889, Remark 2.9): in the CATEGORICAL presentation the distant
    commute is DERIVED from the interchange law, not a separate axiom — exactly what `interchange` gives.

  * **ADJACENT (crossing on the arc's own two legs)** — the untwist redex, shipped as
    `cupFootSwap_conv` / `capFootSwap_conv` (T1, `cupUntwistAbsorb` / `capUntwistAbsorb`).  No gap.

  * **ADJACENT-STRADDLE (crossing braids ONE cup leg + one external strand)** — the ∗-dual of the shipped
    `capSlideRelation` (R1).  See the honesty finding `fxBrauer_hasCupSlideStraddleFinding` below: this is the ONE
    slide shape the shipped seven-relation ctor set does NOT provide, and the literature marks it as a PRIMITIVE
    axiom, not a derived move (Lehrer–Zhang relation (2.7) "Sliding"; Kudryavtseva–Mazorchuk (3.3)–(3.4)).

## Honest scope

This file is ADDITIVE — no shipped theorem or marker is edited.  It banks the distant slides (derivable, shipped)
and records the straddle finding (the minimal instance, the literature verdict, the row-addition bequest).  It does
NOT add a cup-slide relation row.

Raw Lean 4 + Init; the distant slides are single-constructor terms.  Per-declaration `#assert_no_axioms` in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The DISTANT slides — disjoint-support commutation via the generic interchange -/

/-- ★ **Distant cup / crossing slide** — a cup at `cupPos` left of a crossing whose window is disjoint above it
(`cupPos ≤ crossingPos`) slides past it: `[cupAt cupPos, crossingAt (crossingPos + 2)]` is `BrauerConvFree7` to
`[crossingAt crossingPos, cupAt cupPos]`.  The `+ 2` is the `outputCount - inputCount` shift of the crossing window
after the cup inserts its two legs.  ONE `ofFree (BrauerConvFree.interchange …)` — `cupWiring.inputCount = 0`, so
`cupPos + 0 ≤ crossingPos` is exactly `cupPos ≤ crossingPos` and the produced right position `crossingPos - 0 + 2`
is definitionally `crossingPos + 2`. -/
theorem distantCupCrossingSlideFree (cupPos crossingPos : Nat) (disjoint : cupPos ≤ crossingPos) :
    BrauerConvFree7 [cupAt cupPos, crossingAt (crossingPos + 2)] [crossingAt crossingPos, cupAt cupPos] :=
  BrauerConvFree7.ofFree (BrauerConvFree.interchange cupPos crossingPos cupWiring crossingWiring disjoint)

/-- ★ **Distant cup / cap slide** — a cup left of a disjoint cap slides past it. -/
theorem distantCupCapSlideFree (cupPos capPos : Nat) (disjoint : cupPos ≤ capPos) :
    BrauerConvFree7 [cupAt cupPos, capAt (capPos + 2)] [capAt capPos, cupAt cupPos] :=
  BrauerConvFree7.ofFree (BrauerConvFree.interchange cupPos capPos cupWiring capWiring disjoint)

/-- ★ **Distant cup / cup slide** — two disjoint cups commute. -/
theorem distantCupCupSlideFree (cupPosLeft cupPosRight : Nat) (disjoint : cupPosLeft ≤ cupPosRight) :
    BrauerConvFree7 [cupAt cupPosLeft, cupAt (cupPosRight + 2)] [cupAt cupPosRight, cupAt cupPosLeft] :=
  BrauerConvFree7.ofFree (BrauerConvFree.interchange cupPosLeft cupPosRight cupWiring cupWiring disjoint)

/-- ★ **Distant crossing / cup slide (the reverse orientation)** — moving a cup at `cupPos` LEFT past a crossing at
`crossingPos` above it (`cupPos ≤ crossingPos`), read right-to-left: `[crossingAt crossingPos, cupAt cupPos]` is
`BrauerConvFree7` to `[cupAt cupPos, crossingAt (crossingPos + 2)]`.  The `symm` of the cup/crossing slide — so the
disjoint cup slides past a crossing in BOTH directions. -/
theorem distantCrossingCupSlideFree (cupPos crossingPos : Nat) (disjoint : cupPos ≤ crossingPos) :
    BrauerConvFree7 [crossingAt crossingPos, cupAt cupPos] [cupAt cupPos, crossingAt (crossingPos + 2)] :=
  BrauerConvFree7.symm (distantCupCrossingSlideFree cupPos crossingPos disjoint)

/-- Distant slides whisker into arbitrary horizontal / vertical context (the fold applies them inside a window). -/
theorem distantCupCrossingSlideFree_inContext (prefixWord suffixWord : List BrauerAtom)
    (cupPos crossingPos : Nat) (disjoint : cupPos ≤ crossingPos) :
    BrauerConvFree7 (prefixWord ++ ([cupAt cupPos, crossingAt (crossingPos + 2)] ++ suffixWord))
      (prefixWord ++ ([crossingAt crossingPos, cupAt cupPos] ++ suffixWord)) :=
  BrauerConvFree7.whiskerLeft prefixWord
    (BrauerConvFree7.whiskerRight suffixWord (distantCupCrossingSlideFree cupPos crossingPos disjoint))

/-- Non-vacuity — the distant cup/crossing slide fires at a real instance (cup at `0`, crossing window at `2`). -/
theorem distantCupCrossingSlideFree_smoke :
    BrauerConvFree7 [cupAt 0, crossingAt 2] [crossingAt 0, cupAt 0] :=
  distantCupCrossingSlideFree 0 0 (Nat.le_refl 0)

/-! ## The ADJACENT-STRADDLE cup slide — the FINDING (the one shipped-ctor gap, NOT a wall) -/

/-- The minimal straddle instance, as a diagram equality: `[cupAt 0, crossingAt 1]` (cup's far leg braided with the
external bottom strand) and `[cupAt 1, crossingAt 0]` induce the SAME Brauer diagram over one bottom wire — a genuine
`BrauerConv` (via the shipped connectivity-congruence completeness).  So the straddle slide is a TRUE diagram
identity; the finding is only that its FREE syntactic derivation in `BrauerConvFree7` from the shipped ctors is not
provided.  `decide`. -/
theorem cupSlideStraddle_diagramEq :
    brauerDiagramOf 1 [cupAt 0, crossingAt 1] = brauerDiagramOf 1 [cupAt 1, crossingAt 0] := by decide

/-- Hence the straddle pair is a genuine `BrauerConv` (diagram-gated congruence) — the slide is SOUND. -/
theorem cupSlideStraddle_isBrauerConv :
    BrauerConv 1 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] :=
  brauerConv_complete 1 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] cupSlideStraddle_diagramEq

/-- The straddle pair has EQUAL crossing parity (one crossing each side), so — unlike the r2 untwist wall — it is NOT
separated from the shipped closure by the `crossingParity` character.  There is therefore NO falsification: the pair
is diagram-equal, equal-parity, and lies in the (classically complete) seven-relation closure.  The finding is a
derivation gap in the shipped CTOR set, not an obstruction to truth.  `decide`. -/
theorem cupSlideStraddle_parity_eq :
    crossingParity [cupAt 0, crossingAt 1] = crossingParity [cupAt 1, crossingAt 0] := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the DISTANT slides are SHIPPED (the disjoint-support leg of the fold move set).**  Every
disjoint-support cup/cap-past-generator commute is ONE `ofFree (BrauerConvFree.interchange …)` — the shipped
interchange constructor is fully generic in its two `WiringDesc`s, so `distantCupCrossingSlideFree` /
`distantCupCapSlideFree` / `distantCupCupSlideFree` (and the reverse `distantCrossingCupSlideFree` via `symm`, and
the contextual `_inContext`) bank the distant leg.  Lehrer–Zhang Remark 2.9: in the categorical presentation the
distant commute is DERIVED from the interchange law, matching the shipped ctor.  Non-vacuous:
`distantCupCrossingSlideFree_smoke`.  `= true`. -/
def fxBrauer_hasDistantSlideMoves : Bool := true

/-- ★ **Honesty marker — the ADJACENT-STRADDLE cup slide is the ONE shipped-ctor gap (a FINDING, not a wall).**  The
straddle slide `[cupAt 0, crossingAt 1] ~ [cupAt 1, crossingAt 0]` (a crossing braiding one cup leg with an external
strand) is a TRUE diagram identity (`cupSlideStraddle_diagramEq`, hence a genuine `BrauerConv`
`cupSlideStraddle_isBrauerConv`), with EQUAL crossing parity (`cupSlideStraddle_parity_eq`) — so there is NO
`crossingParity` falsification and it lies in the (classically complete) seven-relation closure.  It is the ∗-dual of
the shipped `capSlideRelation` (R1 cap-slide `[crossingAt 1, capAt 0] = [crossingAt 0, capAt 1]`), for which the FX
seven-relation ctor set ships ONLY the cap direction — the cup-mirror is absent.  The literature marks the cup/cap
slide as a PRIMITIVE defining axiom, not a derived move: Lehrer–Zhang (arXiv:1207.5889, JEMS 17 (2015)) relation
(2.7) "Sliding" `(A⊗I)∘(I⊗X) = (I⊗A)∘(X⊗I)` (load-bearing in the Lemma-2.13 standard-form normalization);
Kudryavtseva–Mazorchuk (arXiv:math/0511730, Thm 3) relations (3.3)–(3.4).  BEQUEST (a design choice for the user, NOT
taken here): add a `cupSlideRelation` DATA row `[crossingAt 1, cupAt 0] = [crossingAt 0, cupAt 1]` (the ∗-dual of
`capSlideRelation`) with its `decide` diagram-soundness, mirroring how the r3 untwist rows closed the r2 parity wall
— after which the straddle slide is a first-class `BrauerConvFree7` ctor and the cellular EXTRACT fold's cup-sinking
step is complete.  This file adds NO row.  `= true`. -/
def fxBrauer_hasCupSlideStraddleFinding : Bool := true

end FX1Poly.Polygraph
