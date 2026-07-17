import FX1Poly.Polygraph.TwoCategory.Table.WordProblemBeyondCensusWalls
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemCostLedger
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedGroupDecision
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidPureCupSort
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudication

/-! # Polygraph/TwoCategory/Table/WordProblemBeyondCensusWitnessBundle — flip-bill item (1)

★ **The BEYOND-CENSUS analogue of `WordProblemDecisionWitnessBundle` + `WordProblemCostLedger`
(WP-LEDGER #2048 grand-ledger flip bill, item 1).**

`WordProblemBeyondCensusWalls` enumerated the thirteen rungs the programme attacked beyond the decided-16
census, three of which carry a SHIPPED total (or indexed-scope) decision:

  * the braid GROUP `B_3` (`decidedBeyondCensus`),
  * the adjoint-triple string walker (`decidedBeyondCensus`),
  * the Brauer category on the valid-involution boundary scope (`indexedScopeDecided`).

The grand marker `fxWpLedger_grandLedgerClosed` records the "remaining flip bill"; its item (1) is verbatim
"witness aliases + cost tags for the THREE beyond-census DECIDED rungs".  THIS FILE DISCHARGES ITEM (1) and
nothing else: it HOLDS each decided rung's decision witness as a definitional alias (so a rename/removal
breaks the build — the anchor-rot countermeasure from `WordProblemDecisionWitnessBundle`), and it TAGS each
with an honest cost class + evidence (reusing the census `WordProblemCostClass` / `WordProblemCostEvidence`
taxonomy of `WordProblemCostLedger`, so the two lanes share one epistemic discipline).

It does NOT touch `fxWpLedger_grandLedgerClosed` (bill items 2+3 — the per-wall "held witness" adjudication
and the proved-tag flip — remain owed), it does NOT extend the census enum/counts (these are beyond-census
rungs, not decided-16 rungs), and it introduces NO new proof content: definitional aliases, one three-rung
enum, two total cost maps, `rfl` rows, and Bool markers.

The audit twin runs `#assert_no_axioms` on every alias, which — transitively — MACHINE-CHECKS that the three
beyond-census deciders themselves are zero-axiom, not merely that these wrappers are.

Raw Lean 4 + Init; definitional aliases + a three-rung cost table, no new proof content. -/

namespace FX1Poly.Polygraph.Table

/-! ## The witness aliases (one decision per rung; Brauer carries its normal form too) -/

/-- Braid GROUP `B_3` — the total signed-Garside word-problem decider on ARBITRARY signed words
(`Δ^m · f1 · … · fk`, `m : ℤ` Int-free; WP-BRAID-4).  `@` keeps the binders explicit so the alias does not
eagerly saturate the decl's word arguments.  `@[reducible]` (like the underlying decider) since the alias's
type ends in the `Decidable` class. -/
@[reducible] def wpBeyondBraidGroupDecider := @FX1Poly.Polygraph.decideBraidThreeGroupConv

/-- Adjoint-triple string — the total UNCONDITIONAL saturated-2-cell decider (the r45 brick short-route
`decidableStringSaturatedConv_holds`, boundary coloured-matching invariant; the FC-3 r45 residual
discharged).  `@[reducible]` since the alias's type ends in the `Decidable` class. -/
@[reducible] def wpBeyondAdjointTripleStringDecider :=
  @FX1Poly.Polygraph.decidableStringSaturatedConv_holds

/-- Brauer category (indexed scope) — the boundary-indexed `BrauerConv` decision as a `Bool`
(`decideBrauerConvBool`: decide diagram equality, cite completeness + soundness). -/
def wpBeyondBrauerIndexedDecider := @FX1Poly.Polygraph.decideBrauerConvBool

/-- Brauer category (indexed scope) — the NORMAL FORM `classRepresentativeOf`: a computable, idempotent,
scope-preserving complete invariant for the indexed Brauer word problem (r56).  The Brauer rung's "indexed
normal form" witness, alongside its `Bool` decider above. -/
def wpBeyondBrauerClassRepresentative := @FX1Poly.Polygraph.classRepresentativeOf

/-! ## The three decided beyond-census rungs (the cost-table carrier) -/

/-- The **beyond-census rungs that carry a shipped decision** — exactly the three flagged
`decidedBeyondCensus` / `indexedScopeDecided` in `beyondCensusDisposition`.  A three-element carrier for the
cost table, disjoint from the decided-16 census enum. -/
inductive BeyondCensusDecidedRung
  /-- The braid GROUP `B_3` — `decideBraidThreeGroupConv` (signed Garside NF). -/
  | braidGroup
  /-- The adjoint-triple string walker — `decidableStringSaturatedConv_holds` (coloured matching). -/
  | adjointTripleString
  /-- The Brauer category on the valid-involution scope — `decideBrauerConvBool` / `classRepresentativeOf`. -/
  | brauerIndexedScope

/-- The complete enumeration of the decided beyond-census rungs — THREE, listed. -/
def allBeyondCensusDecidedRungs : List BeyondCensusDecidedRung :=
  [.braidGroup, .adjointTripleString, .brauerIndexedScope]

/-- ★ **The decided beyond-census rung count is exactly THREE** — kernel-checked (`rfl`). -/
theorem beyondCensusDecidedRungCountIsThree : allBeyondCensusDecidedRungs.length = 3 := rfl

/-- ★ **The decided beyond-census enumeration is EXHAUSTIVE** — every rung appears (full case split,
`List.Mem` ctors, propext-free). -/
theorem allBeyondCensusDecidedRungsExhaustive :
    ∀ rung : BeyondCensusDecidedRung, rung ∈ allBeyondCensusDecidedRungs
  | .braidGroup => List.Mem.head _
  | .adjointTripleString => List.Mem.tail _ (List.Mem.head _)
  | .brauerIndexedScope => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-! ## The cost tags (reusing the census taxonomy `WordProblemCostClass` / `WordProblemCostEvidence`) -/

/-- The **cost class of each decided beyond-census rung's decider**, read off its algorithmic structure
(full enumeration, no wildcard arm — propext-free).

  * braid group `decideBraidThreeGroupConv` — `.quadratic`: `braidSignedNormalizeWord` folds
    `braidSignedPrependAtom`, whose Δ-power carry walks up to the accumulated `deltaPower ≤ word length`
    (the classical fixed-strand Garside O(n²) bound, matching the census positive rung
    `walkingBraidPositive`'s `decideBraidThreeConv` tag) plus the four local cancellation arms; then the
    structural `braidSignedCanonDecEq`.
  * adjoint-triple string `decidableStringSaturatedConv_holds` — `.polynomial`: the decision compares the two
    cells' `colouredMatchingOf`, the two-level (coloured) boundary-matching extraction — the same
    link-scanning matching machinery the census adjunction rung `walkingAdjunction`
    (`decideSaturatedTwoCellConv_ofSeed`) is tagged `.polynomial` for; then the structural
    `ColouredDiagramType` `DecidableEq`.
  * Brauer indexed scope `decideBrauerConvBool` / `classRepresentativeOf` — `.polynomial` (CONSERVATIVE):
    `decideBrauerConvBool` decides `brauerDiagramOf` equality, and `brauerDiagramOf` reduces the wiring by a
    Yang–Baxter union-find over the boundary strands (the source docstring warns deep reductions "blow up the
    kernel"), while `classRepresentativeOf` folds that diagram back into the extended standard form
    (`reconstructStandardFormExt5Corrected`) with per-block boundary scans.  NO tight in-repo bound exists for
    the union-find reduction, so this is the most conservative honest class supported by the code's nested
    boundary scans — not a linear tag the union-find could not justify. -/
def beyondCensusDecidedCostClass : BeyondCensusDecidedRung → WordProblemCostClass
  | .braidGroup => .quadratic
  | .adjointTripleString => .polynomial
  | .brauerIndexedScope => .polynomial

/-- The **cost evidence of each decided beyond-census rung's tag** — `.cited` at ALL THREE (honest): every
class above is READ OFF the decider's structure and recorded by decl-name citation; NO in-repo cost theorem
or measurement bounds any beyond-census decider (the `PolyBound` cost-declaration language is itself still
`.openProblem`, COST-7).  Full enumeration (no wildcard arm). -/
def beyondCensusDecidedCostEvidence : BeyondCensusDecidedRung → WordProblemCostEvidence
  | .braidGroup => .cited
  | .adjointTripleString => .cited
  | .brauerIndexedScope => .cited

/-- ★ **The cost-class row over the decided beyond-census enumeration** — mapping `beyondCensusDecidedCostClass`
over `allBeyondCensusDecidedRungs` yields exactly the table's class column.  Kernel-checked (`rfl`). -/
theorem allBeyondCensusDecidedRungsCostClassRow :
    allBeyondCensusDecidedRungs.map beyondCensusDecidedCostClass =
      [.quadratic, .polynomial, .polynomial] := rfl

/-- ★ **The cost-evidence row over the decided beyond-census enumeration** — every entry `.cited`.
Kernel-checked (`rfl`). -/
theorem allBeyondCensusDecidedRungsCostEvidenceRow :
    allBeyondCensusDecidedRungs.map beyondCensusDecidedCostEvidence =
      [.cited, .cited, .cited] := rfl

/-- ★ **Every decided beyond-census rung's cost tag is CITED** — full case split, `rfl` per arm.  The honest
"nothing is proved" statement for the beyond-census cost lane. -/
theorem allBeyondCensusDecidedRungsCostEvidenceCited :
    ∀ rung : BeyondCensusDecidedRung, beyondCensusDecidedCostEvidence rung = .cited
  | .braidGroup => rfl
  | .adjointTripleString => rfl
  | .brauerIndexedScope => rfl

/-! ## The discharge marker (flip-bill item 1) -/

/-- ★★ **FLIP-BILL ITEM (1) IS DISCHARGED.**  `= true` records that the THREE beyond-census DECIDED rungs
(braid group, adjoint-triple string, Brauer indexed scope) now each hold a definitional WITNESS ALIAS of
their shipped decision (`wpBeyondBraidGroupDecider`, `wpBeyondAdjointTripleStringDecider`,
`wpBeyondBrauerIndexedDecider` + the Brauer normal form `wpBeyondBrauerClassRepresentative`) AND an honest
COST TAG (`beyondCensusDecidedCostClass` / `beyondCensusDecidedCostEvidence`, total over
`BeyondCensusDecidedRung`, all `.cited`: braid `.quadratic`, string `.polynomial`, Brauer `.polynomial`).
The beyond-census counterpart of the census `fxWpLedger_sixteenDecidersHeldAndGrounded` (witnesses) and
`fxWpCost_allRungsTagged` (tags), combined into the one flip-bill line.

This discharges ONLY item (1); it does NOT flip `fxWpLedger_grandLedgerClosed` (items 2+3 — the per-wall
held-witness adjudication and the proved-tag flip — remain owed). -/
def fxWpBeyond_hasThreeDecidedRungWitnessesAndCostTags : Bool := true

/-- ★ **Item (1) discharged, grand ledger STILL open (honest coupling, read-only).**  Pins that this file's
discharge marker is `true` while the grand marker `fxWpLedger_grandLedgerClosed` stays `false` and the
enumeration clause `fxWpBeyond_beyondCensusWallsTabulated` stays `true` — a `rfl` conjunction that reads the
existing flags without altering them, so the coupling is kernel-checked and a stray future flip of the grand
marker that forgets this bill line breaks the build. -/
theorem fxWpBeyond_decidedRungBillItemOneDischargedGrandStillOpen :
    fxWpBeyond_hasThreeDecidedRungWitnessesAndCostTags = true
      ∧ fxWpBeyond_beyondCensusWallsTabulated = true
      ∧ fxWpLedger_grandLedgerClosed = false :=
  ⟨rfl, rfl, rfl⟩

end FX1Poly.Polygraph.Table
