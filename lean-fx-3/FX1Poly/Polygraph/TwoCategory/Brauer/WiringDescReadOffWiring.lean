import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPartnerReadOff
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartnered
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldR5Ledger

/-! # BRAUER-MIDDLE r11 B3 + B5 — the WIRED read-off firing (fold-lift ⨾ read-off) and the machine-checked r11
ledger (the master flip HELD honestly false)

The master markers `fxBrauer_hasTagCorrDisjoint` (`Brauer/WiringDescBoundedBoundaryComponents.lean`) and
`fxBrauer_hasTagCorrExtraction` (`Brauer/WiringDescBoundedBoundaryFold.lean`) demand the extraction read-off
WIRED to a specific diagram `d` over the six-phase standard-form word: `extractDiagram foldState = d`, with
`partnerShares` supplied at every `d`-arc from the T-CONNECT existence witnesses, over a state carrying
T-DISJOINT.  That "two-source assembly" needs T-ENUM (the `d`-arc enumeration `capArcFeet` / `throughStrandPerm`
/ `cupArcTops`, which the r5 ledger scoped as its OWN round) plus T-CLOSE (target closure) plus the
partner-TOTALITY FOLD (only the SEED shipped, B1).  None of those is met, so NO master flip is fabricated — the
r11 round holds both masters honestly `false`.

What r11 DOES ship at B3 is the WIRING itself, exercised end-to-end on concrete diagrams: the r10 fold lift
(`boundedBoundaryComponents_reachable`, T-DISJOINT at every reachable state of a well-formed word) feeding the
r11 read-off (`partnerIndexOf_reads_matchingPartner`), producing the actual extracted partner from the invariant
plus a same-component existence witness.  This is the composition the master flip performs at EVERY `d`-arc;
here it is demonstrated at two concrete arcs, showing every ingredient composes.  It also constructs the explicit
crossing `WellFormedBrauerFold` witness (`wellFormedBrauerFold_crossingSeed`) that the standard-form fold lift
needs per phase.

  * ★ `wellFormedBrauerFold_crossingSeed` — the explicit per-atom well-formedness witness for a crossing phase
    (generator disjunct + window-fit), the crossing analogue of the shipped `wellFormedBrauerFold_capThenCup`.

  * ★ `readOffWired_capThenCup` / `readOffWired_crossing` — the WIRED firings: over the reachable fold state of a
    well-formed word, the read-off pins `partnerIndexOf` at boundary index `0` to its true `d`-partner (`1` for
    the cap-then-cup arc, `3` for the crossing arc), proved THROUGH `boundedBoundaryComponents_reachable` +
    `partnerIndexOf_reads_matchingPartner` (NOT by direct `decide`).

  * ★★★ `fxBrauer_r11Ledger` — the machine-checked terminal r11 ledger: the shipped r11 markers (fold lift,
    read-off, partner-totality seed, wired firing) are `true`; every wall (partner-totality fold, both tag-corr
    masters, the roundtrip nodes, the completeness masters) is `false`.

Raw Lean 4 + Init; `decide` only on closed decidable literals (Nat order / `Bool` eq), never on
`WellFormedBrauerFold` or any instance-less inductive `Prop` (explicit witnesses).
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The explicit crossing phase well-formedness witness -/

/-- ★ **The explicit `WellFormedBrauerFold` witness for a single crossing phase.**  `[crossingAt 0]` over
`brauerSeed 2` is well-formed: the crossing is a Brauer generator (`Or.inr (Or.inr rfl)`) firing in range
(`0 + 2 ≤ 2`), then the empty tail is trivially well-formed.  The crossing analogue of the shipped two-atom
`wellFormedBrauerFold_capThenCup`; the `decide` lands only on the closed Nat window-fit, never on the predicate. -/
theorem wellFormedBrauerFold_crossingSeed :
    WellFormedBrauerFold (brauerSeed 2) [crossingAt 0] :=
  ⟨Or.inr (Or.inr rfl), by decide, trivial⟩

/-! ## The wired read-off firings -/

/-- ★ **WIRED firing (cap then cup).**  Over the reachable fold state of the well-formed word `[capAt 0, cupAt 0]`,
`partnerIndexOf` at boundary index `0` is pinned to the `d`-partner `1` (the closed bottom arc) — proved THROUGH
the r10 fold lift `boundedBoundaryComponents_reachable` (T-DISJOINT at the reachable state, via the shipped
`wellFormedBrauerFold_capThenCup`) feeding the r11 read-off `partnerIndexOf_reads_matchingPartner`, with the
same-component existence witness supplied.  This is the exact composition the master flip performs at each
`d`-arc, at a concrete arc. -/
theorem readOffWired_capThenCup :
    partnerIndexOf (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]).links
        (matchingBoundaryNodes 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]))
        (2 + (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]).openWires.length) 0
      = 1 :=
  partnerIndexOf_reads_matchingPartner 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0])
    (boundedBoundaryComponents_reachable 2 (by decide) [capAt 0, cupAt 0] wellFormedBrauerFold_capThenCup)
    0 1 (by decide) (by decide) (by decide) (by decide)

/-- ★ **WIRED firing (crossing).**  Over the reachable fold state of the well-formed word `[crossingAt 0]`,
`partnerIndexOf` at boundary index `0` is pinned to the `d`-partner `3` (the crossing arc `0-3`) — proved THROUGH
`boundedBoundaryComponents_reachable` (via the explicit `wellFormedBrauerFold_crossingSeed`) feeding
`partnerIndexOf_reads_matchingPartner`.  A mixed alphabet second witness that the wiring composes for the
crossing phase too. -/
theorem readOffWired_crossing :
    partnerIndexOf (processBrauer (brauerSeed 2) [crossingAt 0]).links
        (matchingBoundaryNodes 2 (processBrauer (brauerSeed 2) [crossingAt 0]))
        (2 + (processBrauer (brauerSeed 2) [crossingAt 0]).openWires.length) 0
      = 3 :=
  partnerIndexOf_reads_matchingPartner 2 (processBrauer (brauerSeed 2) [crossingAt 0])
    (boundedBoundaryComponents_reachable 2 (by decide) [crossingAt 0] wellFormedBrauerFold_crossingSeed)
    0 3 (by decide) (by decide) (by decide) (by decide)

/-! ## The honesty marker + the machine-checked r11 ledger -/

/-- ★ **Honesty marker — the WIRED read-off firing is SHIPPED (r11 B3).**  The r10 fold lift feeds the r11
read-off end-to-end on concrete diagrams (`readOffWired_capThenCup`, `readOffWired_crossing`): over the reachable
fold state of a well-formed word, the read-off pins `partnerIndexOf` at a boundary index to its true `d`-partner,
purely from T-DISJOINT plus a same-component existence witness.  Plus the explicit crossing phase well-formedness
witness (`wellFormedBrauerFold_crossingSeed`).

  What this does NOT do (no master flip): the GENERAL master flip
  (`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`) needs the read-off wired at EVERY `d`-arc over
  the six-phase standard-form word — the two-source assembly requiring T-ENUM (its own round), T-CLOSE, and the
  partner-totality FOLD (only the seed shipped).  Those stay `false`.  `= true`. -/
def fxBrauer_hasReadOffWiredFiring : Bool := true

/-- ★★★ **The BRAUER-MIDDLE r11 GRAND LEDGER — MACHINE-CHECKED.**  The four shipped r11 markers — the r10
T-DISJOINT fold lift (`fxBrauer_hasBoundedBoundaryFoldLift`), the extraction read-off
(`fxBrauer_hasPartnerReadOff`), the partner-totality seed (`fxBrauer_hasBoundaryPartneredSeed`), and the wired
firing (`fxBrauer_hasReadOffWiredFiring`) — are `true`; and EVERY wall — the partner-totality FOLD
(`fxBrauer_hasBoundaryPartneredFold`), both tag-correspondence masters (`fxBrauer_hasTagCorrDisjoint`,
`fxBrauer_hasTagCorrExtraction`), the extractor-totality roundtrip nodes, and the master completeness flags — is
`false`.  A `rfl`-conjunction the kernel checks over the shipped markers: r11 shipped the uniqueness read-off,
the existence seed, and the wired composition, but the two-source master assembly (T-ENUM ∧ T-CLOSE ∧ the
partner-totality fold) is unbuilt, so no master flip is fabricated and #2013 does NOT close. -/
theorem fxBrauer_r11Ledger :
    (fxBrauer_hasBoundedBoundaryFoldLift = true
      ∧ fxBrauer_hasPartnerReadOff = true
      ∧ fxBrauer_hasBoundaryPartneredSeed = true
      ∧ fxBrauer_hasReadOffWiredFiring = true)
    ∧ (fxBrauer_hasBoundaryPartneredFold = false
      ∧ fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- ★★ **Honesty marker — BRAUER-MIDDLE r11 did NOT close #2013.**  The round shipped the uniqueness EXTRACTION
read-off (`partnerIndexOf` reads the exhibited same-component partner over any T-DISJOINT state), the partner-
totality EXISTENCE seed, and the wired fold-lift ⨾ read-off composition on concrete diagrams — each zero-axiom
and structural.  But the tag-correspondence masters need the read-off wired at EVERY `d`-arc over the six-phase
standard-form word (T-ENUM ∧ T-CLOSE ∧ the partner-totality FOLD, T-ENUM being its own round), which is unbuilt;
above stand R3-B-INNER ∧ R3-C-DRIVER.  So both masters, the roundtrip nodes, and the completeness flags stay
`false`, and #2013 does not close — every residual a ROUTE / totality gap, never a truth gap.  `= false`. -/
def fxBrauer_hasBrauerMiddleR11Complete : Bool := false

end FX1Poly.Polygraph
