import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraightening
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerLedger

/-! # BREACH r3 — the cellular standard form + the stabilizer-generator identification (P1 / P3a)

Full Brauer completeness (the arc finale) targets: every pair of generator words that induce the SAME Brauer
diagram is convertible in the (seven-relation) presentation congruence.  The soundness leg is total; the
crossing-only `S_n` block is straightened (`crossingWords_equalPerm_conv`, `Brauer/WiringDescStaircaseCanonical.lean`);
what remains is the CELLULAR STANDARD FORM — Graham–Lehrer's involution/permutation triple (a cap half-diagram, an
`S_k` permutation on the through-strands, a cup half-diagram; *Cellular algebras*, Invent. math. 123 (1996)) — and
the two named residuals it consumes: the crossing-only READBACK (T2) and the cup/cap connectivity leg.

This file lands the two pieces that CLOSE cleanly and additively this round:

  * **P1 — the cellular standard-form datatype + its word realization + evals.**  `BrauerStandardForm` is the
    flat triple `(bottomCount, capBlock, middle, cupBlock)`; `standardFormWord` reads it out as a generator word
    (caps at the bottom, the crossing staircase in the middle, cups at the top).  Both compute; the smokes are
    `rfl` / `decide`.

  * **P3a — the STABILIZER GENERATOR is the untwist row (Graham–Lehrer's `(Z/2)^c × (Z/2)^{c'}` coset symmetry).**
    A crossing on a cup's two produced legs (`[cupAt p, crossingAt p]`), or on a cap's two consumed legs
    (`[crossingAt p, capAt p]`), leaves the induced Brauer diagram unchanged — the crossing is an automorphism of
    the SAME arc.  So each generator of the middle-permutation stabilizer (the coset subtlety P3) IS exactly a
    Lehrer–Zhang untwist row (`cupUntwistRelation` / `capUntwistRelation`), which `untwistNormalize` already
    quotients.  We ship both the DIAGRAM-equality version (`cupFootSwap_preserves_diagram` /
    `capFootSwap_preserves_diagram`, via `brauerConv_relation_inContext` + `brauerConv_sound`, in ANY wider
    boundary) and the CONVERTIBILITY version (re-exported from the shipped `cupUntwistAbsorb` / `capUntwistAbsorb`,
    in arbitrary horizontal context, `BrauerConvFree7`).

## Honest scope

`fxBrauer_hasBrauerCompleteness` stays whatever the ledger records — this file adds the datatype and the
stabilizer identification, NOT the full extraction fold + well-definedness (those consume the T2 readback, still a
state-invariant residual, and the cup/cap connectivity leg).  ADDITIVE: no shipped theorem or marker is edited.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## P1 — the cellular standard form (Graham–Lehrer involution/permutation triple) -/

/-- ★ **The Brauer cellular standard form** — Graham–Lehrer's triple presentation of a Brauer diagram: over
`bottomCount` bottom wires, a `capBlock` (bottom half-diagram, cap positions read bottom-up), a `middle` crossing
staircase (the `S_k` permutation on the through-strands), and a `cupBlock` (top half-diagram, cup positions).  A
flat `Nat` / `List Nat` datum, so its equality decides and it computes. -/
structure BrauerStandardForm where
  /-- The number of bottom boundary wires the form acts on. -/
  bottomCount : Nat
  /-- The cap half-diagram: the cap generator positions, bottom-to-top. -/
  capBlock : List Nat
  /-- The middle `S_k` permutation, as a crossing-staircase word (the `recComb` output). -/
  middle : List Nat
  /-- The cup half-diagram: the cup generator positions, bottom-to-top. -/
  cupBlock : List Nat
deriving DecidableEq

/-- A **cap word** from a list of positions — each position becomes a cap generator (the mirror of `crossingWord`). -/
def capWord : List Nat → List BrauerAtom
  | [] => []
  | position :: rest => capAt position :: capWord rest

/-- A **cup word** from a list of positions — each position becomes a cup generator. -/
def cupWord : List Nat → List BrauerAtom
  | [] => []
  | position :: rest => cupAt position :: cupWord rest

/-- ★ **The generator word a standard form realizes** — caps at the bottom, then the crossing staircase, then cups
at the top (bottom-to-top reading order, matching `processBrauer`). -/
def standardFormWord (form : BrauerStandardForm) : List BrauerAtom :=
  capWord form.capBlock ++ crossingWord form.middle ++ cupWord form.cupBlock

/-- The **Brauer diagram of a standard form** — run its realized word through the wiring engine. -/
def standardFormDiagram (form : BrauerStandardForm) : DiagramType :=
  brauerDiagramOf form.bottomCount (standardFormWord form)

/-! ### P1 length lemmas -/

/-- The cap word has one generator per position. -/
theorem capWord_length : (positions : List Nat) → (capWord positions).length = positions.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (capWord_length rest)

/-- The cup word has one generator per position. -/
theorem cupWord_length : (positions : List Nat) → (cupWord positions).length = positions.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (cupWord_length rest)

/-! ### P1 evals / smokes -/

/-- Smoke — the empty standard form over two bottom wires reads out the empty word, whose diagram is the straight
identity matching `[2, 3, 0, 1]`. -/
theorem standardFormWord_empty_two :
    standardFormDiagram { bottomCount := 2, capBlock := [], middle := [], cupBlock := [] }
      = { bottomCount := 2, topCount := 2, partner := [2, 3, 0, 1], loops := 0 } := by decide

/-- Smoke — a single-crossing middle over two bottom wires reads out `[crossingAt 0]`, the transposition
`[3, 2, 1, 0]`. -/
theorem standardFormWord_crossing_two :
    standardFormDiagram { bottomCount := 2, capBlock := [], middle := [0], cupBlock := [] }
      = { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 } := by decide

/-- Smoke — a cap-then-cup standard form over two bottom wires (`[capAt 0, cupAt 0]`) reads out the "cup–cap"
diagram: the two bottom wires cap together and two fresh top wires cup together (partner `[1, 0, 3, 2]`). -/
theorem standardFormWord_capCup_two :
    standardFormDiagram { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0] }
      = { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 } := by decide

/-- Smoke — the realized word of a fully-populated small form is exactly caps ++ crossings ++ cups. -/
theorem standardFormWord_concat :
    standardFormWord { bottomCount := 4, capBlock := [0], middle := [1], cupBlock := [2] }
      = [capAt 0, crossingAt 1, cupAt 2] := rfl

/-! ## P3a — the stabilizer generator IS the untwist row (the coset symmetry P3)

Graham–Lehrer's middle permutation is well-defined only modulo the hyperoctahedral stabilizer
`(Z/2)^c × (Z/2)^{c'}` — swapping the two strands of any single cup / cap composes with the middle without
changing the matching.  Each such foot-swap is a crossing on the arc's own two legs, i.e. exactly a Lehrer–Zhang
untwist redex.  We identify them as diagram-preserving here (the coset generators are consumed by
`untwistNormalize`). -/

/-- ★ **The cup-foot-swap preserves the Brauer diagram (P3a, at any position in any wider boundary).**  A crossing
on a cup's two produced legs (`[cupAt footPos, crossingAt footPos]`, whiskered at offset `footPos` in a boundary
`bottomCount = footPos + rightPad`, `0 < bottomCount`) is diagram-equal to the bare cup: the crossing is an
automorphism of the cup arc.  Discharged by the relation-agnostic keystone `brauerConv_relation_inContext` fed
`cupUntwist_diagram_sound`, then `brauerConv_sound`. -/
theorem cupFootSwap_preserves_diagram (bottomCount footPos rightPad : Nat)
    (bottomPos : 0 < bottomCount) (widthEq : bottomCount = footPos + (0 + rightPad)) :
    brauerDiagramOf bottomCount ([] ++ shiftBrauerWord footPos cupUntwistRelation.lhs)
      = brauerDiagramOf bottomCount ([] ++ shiftBrauerWord footPos cupUntwistRelation.rhs) :=
  brauerConv_sound
    (brauerConv_relation_inContext bottomCount bottomPos [] (BrauerWordInRange.nil bottomCount)
      footPos 0 rightPad cupUntwistRelation.lhs cupUntwistRelation.rhs
      (by show (List.range bottomCount).length = footPos + (0 + rightPad)
          rw [rangeLength_local]; exact widthEq)
      (BrauerWordInRange.cons (cupAt 0) 0 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
      (BrauerWordInRange.cons (cupAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))
      rfl rfl cupUntwist_diagram_sound)

/-- ★ **The cap-foot-swap preserves the Brauer diagram (P3a, mirror).**  A crossing on a cap's two consumed legs
(`[crossingAt footPos, capAt footPos]`) whiskered at offset `footPos` in a boundary `bottomCount = footPos + (2 +
rightPad)` is diagram-equal to the bare cap. -/
theorem capFootSwap_preserves_diagram (bottomCount footPos rightPad : Nat)
    (bottomPos : 0 < bottomCount) (widthEq : bottomCount = footPos + (2 + rightPad)) :
    brauerDiagramOf bottomCount ([] ++ shiftBrauerWord footPos capUntwistRelation.lhs)
      = brauerDiagramOf bottomCount ([] ++ shiftBrauerWord footPos capUntwistRelation.rhs) :=
  brauerConv_sound
    (brauerConv_relation_inContext bottomCount bottomPos [] (BrauerWordInRange.nil bottomCount)
      footPos 2 rightPad capUntwistRelation.lhs capUntwistRelation.rhs
      (by show (List.range bottomCount).length = footPos + (2 + rightPad)
          rw [rangeLength_local]; exact widthEq)
      (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
        (BrauerWordInRange.cons (capAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 0)))
      (BrauerWordInRange.cons (capAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 0))
      rfl rfl capUntwist_diagram_sound)

/-- ★ **The cup-foot-swap convertibility (P3a, `BrauerConvFree7`, arbitrary horizontal context).**  Re-export of the
shipped `cupUntwistAbsorb`: the coset generator (cup then crossing on its legs) is `BrauerConvFree7` to the bare cup
between ANY prefix / suffix — so the stabilizer symmetry is quotiented by the presentation. -/
theorem cupFootSwap_conv (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7 (prefixWord ++ ([cupAt position, crossingAt position] ++ suffixWord))
      (prefixWord ++ ([cupAt position] ++ suffixWord)) :=
  cupUntwistAbsorb prefixWord suffixWord position

/-- ★ **The cap-foot-swap convertibility (P3a, mirror).** -/
theorem capFootSwap_conv (prefixWord suffixWord : List BrauerAtom) (position : Nat) :
    BrauerConvFree7 (prefixWord ++ ([crossingAt position, capAt position] ++ suffixWord))
      (prefixWord ++ ([capAt position] ++ suffixWord)) :=
  capUntwistAbsorb prefixWord suffixWord position

/-- Non-vacuity — the cup-foot-swap fires at the seed (`[cupAt 0, crossingAt 0]` diagram-equal to `[cupAt 0]` over
one bottom wire). -/
theorem cupFootSwap_preserves_diagram_smoke :
    brauerDiagramOf 1 ([] ++ shiftBrauerWord 1 cupUntwistRelation.lhs)
      = brauerDiagramOf 1 ([] ++ shiftBrauerWord 1 cupUntwistRelation.rhs) :=
  cupFootSwap_preserves_diagram 1 1 0 (by decide) (by decide)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cellular STANDARD-FORM datatype is SHIPPED (P1).**  `BrauerStandardForm` is the
Graham–Lehrer involution/permutation triple (cap half-diagram, `S_k` middle staircase, cup half-diagram) as a flat
decidable-eq datum; `standardFormWord` realizes it as a generator word (caps · crossings · cups) and
`standardFormDiagram` runs it through the wiring engine.  Both compute (`standardFormWord_*` smokes, `rfl` / `decide`);
`capWord_length` / `cupWord_length` are the closed well-formedness lemmas.  This is the datatype the extraction fold
(P2) and well-definedness (P3) target; the fold itself is NOT built here.  `= true`. -/
def fxBrauer_hasCellularStandardFormDatatype : Bool := true

/-- ★ **Honesty marker — the STABILIZER GENERATOR = untwist row identification is SHIPPED (P3a).**  The coset
symmetry the middle permutation is defined modulo (Graham–Lehrer's hyperoctahedral `(Z/2)^c × (Z/2)^{c'}`) is
generated by cup / cap foot swaps, each a Lehrer–Zhang untwist redex.  `cupFootSwap_preserves_diagram` /
`capFootSwap_preserves_diagram` prove each foot-swap DIAGRAM-preserving at any position in any wider boundary (via
`brauerConv_relation_inContext` + `brauerConv_sound`), and `cupFootSwap_conv` / `capFootSwap_conv` re-export the
`BrauerConvFree7` convertibility in arbitrary horizontal context (from `cupUntwistAbsorb` / `capUntwistAbsorb`).  So
the stabilizer is quotiented by the presentation, resolving the P3 coset subtlety at the generator level:
`untwistNormalize` consumes exactly these generators.  Non-vacuous: `cupFootSwap_preserves_diagram_smoke`.  `= true`. -/
def fxBrauer_hasStabilizerGeneratorIsUntwist : Bool := true

end FX1Poly.Polygraph
