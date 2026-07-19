import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormCensus
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormLadder

/-! # Polygraph/Omega/ZXPhaseFree/ExchangeCompleteness — THE RIGHT-FIRST EXCHANGE MOVE,
the gate re-run, and GENERAL-k PARALLEL FUSION

The commissioned 4-item bill toward the phase-free ZX completeness push, executed in
arc order (each stage decided before the next):

## (A) THE EXCHANGE MOVE — `ZxeConv`

The ladder's wall (`zxnRightFirstExchangeStatement`, owner false) named the ONE missing
configuration: disjoint blocks placed RIGHT-FIRST, `[[wire^domL, R], [L, wire^codR]]`,
which no move of {published rows, splitLayer, zFuse, xFuse} produces or merges.  This
brick adds it as a NEW MOVE (the census commission's option "candidate NEW MOVE"), in
the LIST form generalizing the wall's single-cell shape: for arbitrary cell lists
`leftCells`/`rightCells`,

    [[wire^dom(L), R], [L, wire^cod(R)]]  ~  [[L, R]]

(`zxeExchangeLhs`/`zxeExchangeRhs`; the wall's shape is the singleton instance).
SOUNDNESS IS STRUCTURAL AT ALL ARITIES (`zxeExchangeBundle`): both sides denote the
tensor `L (x) R` — the two-layer side is `(id (x) R) ; (L (x) id)` by the layer-split
lemma and the wire-identity lemma, which the seed's `zxpTensorComposeInterchange`
collapses to `(id ; L) (x) (R ; id) = L (x) R`.  No kernel evaluation, no disjointness
side condition: disjointness is structural in the shape (the two blocks occupy disjoint
wire intervals by construction).  `ZxeConv` = `ZxrConv`'s moves + the exchange family,
in the seed's exact pad/groupoid shapes; `zxrPadBundle` (already factored over an
arbitrary window bundle) gives step soundness verbatim; `zxeConvSound` /
`zxeConvSpanEqB` / `zxeOfZxrConv` / `zxeOfZxpConv` mirror the FusionRepair layer.
The pad-lifting congruence is ported (`zxeConvLift`), and the ladder's k = 1/2/3
fusions and eta expansions transport along `zxeOfZxrConv`.

HONESTY: the exchange is added, NOT derived.  Whether the exchange is ADMISSIBLE in
`ZxrConv` (derivable from rows + splitLayer + fusion) remains OPEN
(`zxeExchangeAdmissibleInZxrConvIsProven := false`); consequently
`zxnRightFirstExchangeStatement` (the ZxrConv-quantified wall) stays owner-false in the
ladder, byte-intact.  Note the extension cannot be separated from `ZxrConv` by ANY of
this workstream's refutation instruments: both congruences are span-sound (no semantic
separator can exist between them), and the collapse theorem below kills every per-cell
counting separator — so "proper extension vs admissible" is a genuinely open syntactic
question, recorded as such.

## (B) THE GATE RE-RUN (arc law: refutation pass before any completeness push)

* THE EXCHANGE IS INVISIBLE TO THE WEIGHT FAMILY: every wire-vanishing per-cell Nat
  weight is exchange-balanced (`zxeExchangeFoldBalanced` — both sides carry exactly the
  cells of `leftCells` and `rightCells` plus wires).  So the fold-engine hypotheses for
  `ZxeConv` (`zxeConvFoldEq`) are THE SAME FOUR as for `ZxrConv`, and the FusionRepair
  collapse theorem carries verbatim: every admissible weight is identically zero
  (`zxeBalancedWeightCollapse`), fold constant zero (`zxeBalancedWeightFoldZero`) — the
  per-cell count family holds NO separator for `ZxeConv`.
* THE BASE 7-VECTOR MOD-2 RE-RUN: the general saturation lemma
  (`zxeExchangeDeltaGeneral`) pins every exchange instance's delta on
  [zCount, xCount, wireCount, crossingCount, layerCount, zLegs, xLegs] to
  `[0, 0, parity(dom(L) + cod(R)), 0, 1, 0, 0]` — exactly the `splitLayer` delta family
  (the two literals `zxeExchangeDeltaEven`/`zxeExchangeDeltaOdd` are byte-identical to
  the gate's split witnesses).  The exchange-extended table spans the SAME 6-dimensional
  basis (`zxeExtendedDeltaSpanBasisPin`, kernel); the 128-functional enumeration
  re-classifies the preserved lattice as still exactly {0, legs-parity}
  (`zxePreservedLatticeReclassified`, kernel); the survivor is boundary-determined by
  the gate's per-diagram theorem (untouched by any move-set extension) and orthogonal
  to every exchange delta at every arity (`zxeLegsParityOrthogonalExchangeDelta`).
* THE INSTRUMENT STILL BITES: span-distinct diagrams stay non-convertible
  (`zxeBigColourNotConv`).  VERDICT: GATE CLEAN (`zxeGateVerdictIsClean := true`).

## (C) GENERAL-k PARALLEL FUSION — `zxeParallelFusionZ` / `zxeParallelFusionX`

    [[spider a (k+1)], [spider (k+1) d]]  ~  [[spider a d]]    (all k, a, d, both colours)

by structural induction, THE k = 3 PATTERN ITERATED exactly as the ladder predicted
once the exchange is granted.  Engine: the right-corner absorption family
`zxeParallelFusionStepZ/X`

    [[wire^p, spider 1 2], [spider (p+2) d]]  ~  [[spider (p+1) d]]

with a THREE-CASE recursion on the pass-wire count `p`: p = 0 is the shipped
fully-shared k = 2 fusion; p = 1 is the FROBENIUS route (fission the bottom spider,
the Frobenius row re-associates, fully-shared k = 2 + k = 1 finish) — the middle pair
`[[wire, s12],[s21, wire]]` is CONNECTED there, so the exchange must not (and does not)
fire; p >= 2 is the EXCHANGE route: fission the bottom spider, the middle pair
`[[wire^p, s12],[s21, wire^p]]` is DISJOINT right-first, ONE exchange move merges it,
one splitLayer re-splits it left-first, and the recursion descends to p - 1 before one
primitive fusion finishes.  The general theorem then falls by fissioning the top spider
one output at a time (`zxeParallelFusionZ`: fission + step + induct).  Fires: k = 4
(first instance beyond the ladder's wall) and the commissioned k = 5 instance with an
independent kernel span cross-check.

HONESTY: this lands general-k fusion over `ZxeConv`.  Over `ZxrConv` it remains open
(the ladder's `zxnLadderGeneralKWireFusionLanded` stays byte-intact false) — it would
follow from exchange admissibility in `ZxrConv`, the recorded open question.

## (D) THE COMPLETENESS PUSH — statement minted, absorption partials, owner FALSE

`zxeCompletenessStatement` is minted VERBATIM in the shape of FusionRepair's
`zxrCompletenessStatement` with `ZxeConv` in the conclusion — NOT a silent restatement:
the ZxrConv-quantified original stays owner-false in FusionRepair, and the precise
delta between the two is the exchange-admissibility lemma recorded above.  What ships
of the Kissinger Lemma 3.2/3.3 absorption induction: the identity-wire absorption
lemmas (`zxeStripLeadingWireLayer` / `zxeStripTrailingWireLayer`, the trivial-cell
case), spider absorption for fully-shared same-colour chains (= (C)), and the
conditional decision corollary `zxeDecisionUnderCompleteness` (under the statement,
`ZxeConv`-convertibility of WF boundary-matched diagrams is DECIDED by `zxpSpanEqB` —
the full phase-free word-problem decision, awaiting the induction).  THE EXACT
REMAINING BILL for the induction, per the census commission: (iii) the leg-permutation
engine (crossing conjugation for arbitrary-arity side-by-side spiders — NOT shipped
here), then (iv) the absorption induction over the census `zxnNormalForm` (init bases,
per-generator combs with crossing walks, kill collectors).  Both are structurally
beyond this brick's move set; `zxeCompletenessIsProven := false`.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`, no
`Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive scrutinees;
width-only top-level Nat matches. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage A0 — the exchange window family and its structural soundness -/

/-- Right-first exchange, LEFT side (the blocked orientation): the RIGHT block fires
first under `dom(L)` pass wires; the LEFT block fires second over `cod(R)` pass wires. -/
def zxeExchangeLhs (leftCells rightCells : List ZxpCell) : ZxpDiagram :=
  { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
    layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells,
      zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))] }

/-- Right-first exchange, RIGHT side: the merged one-layer tensor `[[L, R]]`. -/
def zxeExchangeRhs (leftCells rightCells : List ZxpCell) : ZxpDiagram :=
  { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
    layers := [zxpCatCells leftCells rightCells] }

theorem zxeExchangeLhsCodArity (leftCells rightCells : List ZxpCell) :
    zxpDiagramCodArity (zxeExchangeLhs leftCells rightCells)
      = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells := by
  show zxpLayerCodArity
      (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))
    = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity]

theorem zxeExchangeRhsCodArity (leftCells rightCells : List ZxpCell) :
    zxpDiagramCodArity (zxeExchangeRhs leftCells rightCells)
      = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells := by
  show zxpLayerCodArity (zxpCatCells leftCells rightCells)
    = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells
  rw [zxpCatCellsCodArity]

theorem zxeExchangeLhsWF (leftCells rightCells : List ZxpCell) :
    ZxpDiagramWF (zxeExchangeLhs leftCells rightCells) := by
  refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
  · show zxpLayerDomArity
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
      = zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  · show zxpLayerDomArity
        (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))
      = zxpLayerCodArity
          (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxpCatCellsCodArity,
      zxpWireCellsCodArity]

theorem zxeExchangeRhsWF (leftCells rightCells : List ZxpCell) :
    ZxpDiagramWF (zxeExchangeRhs leftCells rightCells) :=
  ZxpLayersWF.cons (zxpCatCellsDomArity leftCells rightCells) (ZxpLayersWF.nil _)

/-- The right-first two-layer side denotes the tensor `L (x) R` — through the
layer-split lemma, the wire-identity lemma, and THE INTERCHANGE
(`zxpTensorComposeInterchange`): `(id (x) R) ; (L (x) id) = (id ; L) (x) (R ; id)`. -/
theorem zxeExchangeLhsDenoteEquiv (leftCells rightCells : List ZxpCell) :
    ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpDiagramDenote (zxeExchangeLhs leftCells rightCells))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote leftCells) (zxpLayerDenote rightCells)) := by
  have hL1Dom : zxpLayerDomArity
      (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
      = zxpLayerDomArity leftCells + zxpLayerDomArity rightCells := by
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  have hL1Cod : zxpLayerCodArity
      (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
      = zxpLayerDomArity leftCells + zxpLayerCodArity rightCells := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  have hL2Dom : zxpLayerDomArity
      (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))
      = zxpLayerDomArity leftCells + zxpLayerCodArity rightCells := by
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  have hL2Cod : zxpLayerCodArity
      (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))
      = zxpLayerCodArity leftCells + zxpLayerCodArity rightCells := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  -- layer 1 denotes id (x) R
  have hSplitOne := zxpLayerDenoteCatSplit
    (zxpWireCells (zxpLayerDomArity leftCells)) rightCells
  rw [zxpWireCellsDomArity (zxpLayerDomArity leftCells),
    zxpWireCellsCodArity (zxpLayerDomArity leftCells)] at hSplitOne
  have hLayerOneEquiv : ZxpRelEquiv
      (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerDenote
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerDomArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpIdRows (zxpLayerDomArity leftCells)) (zxpLayerDenote rightCells)) := by
    refine zxpRelEquivTrans hSplitOne ?_
    exact zxpTensorRowsCong (zxpLayerDomArity leftCells) (zxpLayerDomArity leftCells)
      (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
        (zxpLayerDenoteWidth (zxpWireCells (zxpLayerDomArity leftCells))))
      (zxpIdRowsWidth (zxpLayerDomArity leftCells))
      (zxpLayerDenoteWidth rightCells) (zxpLayerDenoteWidth rightCells)
      (zxpWireCellsDenoteId (zxpLayerDomArity leftCells))
      (zxpRelEquivRefl (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote rightCells))
  -- layer 2 denotes L (x) id
  have hSplitTwo := zxpLayerDenoteCatSplit leftCells
    (zxpWireCells (zxpLayerCodArity rightCells))
  rw [zxpWireCellsDomArity (zxpLayerCodArity rightCells),
    zxpWireCellsCodArity (zxpLayerCodArity rightCells)] at hSplitTwo
  have hLayerTwoEquiv : ZxpRelEquiv
      (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerDenote
        (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerCodArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerCodArity rightCells))) := by
    refine zxpRelEquivTrans hSplitTwo ?_
    exact zxpTensorRowsCong (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
      (zxpLayerCodArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerDenoteWidth leftCells) (zxpLayerDenoteWidth leftCells)
      (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
        (zxpLayerDenoteWidth (zxpWireCells (zxpLayerCodArity rightCells))))
      (zxpIdRowsWidth (zxpLayerCodArity rightCells))
      (zxpRelEquivRefl (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDenote leftCells))
      (zxpWireCellsDenoteId (zxpLayerCodArity rightCells))
  -- width bookkeeping
  have hDenL1All : ZxpAllWidth
      ((zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        + (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells))
      (zxpLayerDenote
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)) :=
    zxpAllWidthCast (by rw [hL1Dom, hL1Cod])
      (zxpLayerDenoteWidth
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells))
  have hDenL2All : ZxpAllWidth
      ((zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
        + (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
      (zxpLayerDenote
        (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))) :=
    zxpAllWidthCast (by rw [hL2Dom, hL2Cod])
      (zxpLayerDenoteWidth
        (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
  have hTensorOneAll := zxpTensorRowsWidth (zxpLayerDomArity leftCells)
    (zxpLayerDomArity leftCells) (zxpLayerDomArity rightCells)
    (zxpLayerCodArity rightCells)
    (zxpIdRows (zxpLayerDomArity leftCells)) (zxpLayerDenote rightCells)
    (zxpIdRowsWidth (zxpLayerDomArity leftCells)) (zxpLayerDenoteWidth rightCells)
  have hTensorTwoAll := zxpTensorRowsWidth (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerCodArity rightCells)
    (zxpLayerCodArity rightCells)
    (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerCodArity rightCells))
    (zxpLayerDenoteWidth leftCells) (zxpIdRowsWidth (zxpLayerCodArity rightCells))
  have hInnerComposeAll := zxpComposeRowsWidth
    (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerDenote
      (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
    (zxpIdRows (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
    hDenL2All
    (zxpIdRowsWidth (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
  have hInnerEquiv : ZxpRelEquiv
      (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpComposeRows
        (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerDenote
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
        (zxpIdRows (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerCodArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote leftCells) (zxpIdRows (zxpLayerCodArity rightCells))) :=
    zxpRelEquivTrans
      (zxpComposeIdRight
        (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
        (zxpLayerDenote
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
        hDenL2All)
      hLayerTwoEquiv
  show ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpComposeRows (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells))
      (zxpLayerCodArity
        (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
      (zxpLayerDenote
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells))
      (zxpComposeRows
        (zxpLayerCodArity
          (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells))
        (zxpLayerCodArity
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
        (zxpLayerCodArity
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
        (zxpLayerDenote
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))))
        (zxpIdRows (zxpLayerCodArity
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells)))))))
    (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
      (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerDenote leftCells) (zxpLayerDenote rightCells))
  rw [hL1Cod, hL2Cod]
  refine zxpRelEquivTrans (zxpComposeRowsCong
    (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    hDenL1All hTensorOneAll hInnerComposeAll hTensorTwoAll
    hLayerOneEquiv hInnerEquiv) ?_
  refine zxpRelEquivTrans (zxpTensorComposeInterchange
    (zxpLayerDomArity leftCells) (zxpLayerDomArity leftCells)
    (zxpLayerCodArity leftCells) (zxpLayerDomArity rightCells)
    (zxpLayerCodArity rightCells) (zxpLayerCodArity rightCells)
    (zxpIdRows (zxpLayerDomArity leftCells)) (zxpLayerDenote leftCells)
    (zxpLayerDenote rightCells) (zxpIdRows (zxpLayerCodArity rightCells))
    (zxpIdRowsWidth (zxpLayerDomArity leftCells)) (zxpLayerDenoteWidth leftCells)
    (zxpLayerDenoteWidth rightCells)
    (zxpIdRowsWidth (zxpLayerCodArity rightCells))) ?_
  exact zxpTensorRowsCong (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
    (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
    (zxpComposeRowsWidth (zxpLayerDomArity leftCells) (zxpLayerDomArity leftCells)
      (zxpLayerCodArity leftCells) (zxpIdRows (zxpLayerDomArity leftCells))
      (zxpLayerDenote leftCells) (zxpIdRowsWidth (zxpLayerDomArity leftCells))
      (zxpLayerDenoteWidth leftCells))
    (zxpLayerDenoteWidth leftCells)
    (zxpComposeRowsWidth (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerCodArity rightCells) (zxpLayerDenote rightCells)
      (zxpIdRows (zxpLayerCodArity rightCells)) (zxpLayerDenoteWidth rightCells)
      (zxpIdRowsWidth (zxpLayerCodArity rightCells)))
    (zxpLayerDenoteWidth rightCells)
    (zxpComposeIdLeft (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
      (zxpLayerDenote leftCells) (zxpLayerDenoteWidth leftCells))
    (zxpComposeIdRight (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerDenote rightCells) (zxpLayerDenoteWidth rightCells))

/-- The merged side denotes the same tensor `L (x) R`. -/
theorem zxeExchangeRhsDenoteEquiv (leftCells rightCells : List ZxpCell) :
    ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpDiagramDenote (zxeExchangeRhs leftCells rightCells))
      (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
        (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
        (zxpLayerDenote leftCells) (zxpLayerDenote rightCells)) := by
  have hMergedAll : ZxpAllWidth
      ((zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
        + (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells))
      (zxpLayerDenote (zxpCatCells leftCells rightCells)) :=
    zxpAllWidthCast (by rw [zxpCatCellsDomArity, zxpCatCellsCodArity])
      (zxpLayerDenoteWidth (zxpCatCells leftCells rightCells))
  show ZxpRelEquiv (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpComposeRows (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity (zxpCatCells leftCells rightCells))
      (zxpLayerCodArity (zxpCatCells leftCells rightCells))
      (zxpLayerDenote (zxpCatCells leftCells rightCells))
      (zxpIdRows (zxpLayerCodArity (zxpCatCells leftCells rightCells))))
    (zxpTensorRows (zxpLayerDomArity leftCells) (zxpLayerCodArity leftCells)
      (zxpLayerDomArity rightCells) (zxpLayerCodArity rightCells)
      (zxpLayerDenote leftCells) (zxpLayerDenote rightCells))
  rw [zxpCatCellsCodArity leftCells rightCells]
  refine zxpRelEquivTrans (zxpComposeIdRight
    (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
    (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
    (zxpLayerDenote (zxpCatCells leftCells rightCells)) hMergedAll) ?_
  exact zxpLayerDenoteCatSplit leftCells rightCells

/-- SOUNDNESS OF THE EXCHANGE MOVE at every arity, every pair of cell lists — the
bundle shape of the seed. -/
theorem zxeExchangeBundle (leftCells rightCells : List ZxpCell) :
    ZxpConvBundle (zxeExchangeLhs leftCells rightCells)
      (zxeExchangeRhs leftCells rightCells) := by
  have hEquiv : ZxpRelEquiv
      (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxpLayerCodArity leftCells + zxpLayerCodArity rightCells)
      (zxpDiagramDenote (zxeExchangeLhs leftCells rightCells))
      (zxpDiagramDenote (zxeExchangeRhs leftCells rightCells)) :=
    zxpRelEquivTrans (zxeExchangeLhsDenoteEquiv leftCells rightCells)
      (zxpRelEquivSymm (zxeExchangeRhsDenoteEquiv leftCells rightCells))
  refine And.intro rfl (And.intro ?_ (And.intro (zxeExchangeLhsWF leftCells rightCells)
    (And.intro (zxeExchangeRhsWF leftCells rightCells) ?_)))
  · exact (zxeExchangeLhsCodArity leftCells rightCells).trans
      (zxeExchangeRhsCodArity leftCells rightCells).symm
  · exact zxpRelEquivCast rfl (zxeExchangeLhsCodArity leftCells rightCells).symm hEquiv

/-! ## Stage A1 — THE EXCHANGE-EXTENDED CONGRUENCE `ZxeConv` -/

/-- Exchange-extended window move: any `ZxrConv` window move (published row,
splitLayer, or one-wire fusion), or a right-first exchange instance. -/
inductive ZxeWindowMove : ZxpDiagram -> ZxpDiagram -> Prop where
  | base {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxrWindowMove firstWindow secondWindow) :
      ZxeWindowMove firstWindow secondWindow
  | rightFirstExchange (leftCells rightCells : List ZxpCell) :
      ZxeWindowMove (zxeExchangeLhs leftCells rightCells)
        (zxeExchangeRhs leftCells rightCells)

/-- Every exchange-extended window move is sound (bundle form). -/
theorem zxeWindowMoveBundle {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxeWindowMove firstWindow secondWindow) :
    ZxpConvBundle firstWindow secondWindow := by
  cases hMove with
  | base hBaseMove => exact zxrWindowMoveBundle hBaseMove
  | rightFirstExchange leftCells rightCells => exact zxeExchangeBundle leftCells rightCells

/-- One exchange-extended rewriting step: an extended window move fired inside the
seed's pad combinator (identical constructor shape to `ZxrStep`). -/
inductive ZxeStep : ZxpDiagram -> ZxpDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List ZxpCell))
      {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxeWindowMove firstWindow secondWindow)
      (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
      (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : ZxpLayersWF
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
      ZxeStep
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Soundness of one exchange-extended padded step (rides FusionRepair's
`zxrPadBundle`, already factored over an arbitrary window bundle). -/
theorem zxeStepBundle {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxeStep firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      exact zxrPadBundle contextSource leftWires rightWires beforeLayers afterLayers
        (zxeWindowMoveBundle hMove) hBeforeWF hBeforeCod hAfterWF

/-- THE EXCHANGE-EXTENDED CONGRUENCE: exchange-aware steps under the seed's groupoid
closure. -/
inductive ZxeConv : ZxpDiagram -> ZxpDiagram -> Prop where
  | step {firstDiagram secondDiagram : ZxpDiagram}
      (hStep : ZxeStep firstDiagram secondDiagram) : ZxeConv firstDiagram secondDiagram
  | refl (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) : ZxeConv diagram diagram
  | symm {firstDiagram secondDiagram : ZxpDiagram}
      (hConv : ZxeConv firstDiagram secondDiagram) : ZxeConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : ZxpDiagram}
      (hFirst : ZxeConv firstDiagram secondDiagram)
      (hSecond : ZxeConv secondDiagram thirdDiagram) : ZxeConv firstDiagram thirdDiagram

/-- SOUNDNESS AT ALL ARITIES: exchange-extended-convertible diagrams share boundaries,
are well-formed, and denote the same F2 linear relation. -/
theorem zxeConvSound {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxeConv firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact zxeStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (zxpRelEquivRefl diagram.sourceArity (zxpDiagramCodArity diagram)
          (zxpDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact zxpConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact zxpConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE for the exchange-extended congruence. -/
theorem zxeConvSpanEqB {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxeConv firstDiagram secondDiagram) :
    zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
      = true := by
  have hBundle := zxeConvSound hConv
  exact zxpSpanEqBOfRelEquiv
    (zxpDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (zxpAllWidthCast (by rw [hBundle.left, hBundle.right.left])
      (zxpDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-- EVERY `ZxrConv` CONVERSION EMBEDS: the fusion congruence is a sub-congruence of
the exchange-extended one. -/
theorem zxeOfZxrConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxrConv firstDiagram secondDiagram) :
    ZxeConv firstDiagram secondDiagram := by
  induction hConv with
  | step hStep =>
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
          hBeforeCod hAfterWF =>
          exact ZxeConv.step (ZxeStep.pad contextSource leftWires rightWires
            beforeLayers afterLayers (ZxeWindowMove.base hMove) hBeforeWF hBeforeCod
            hAfterWF)
  | refl diagram hWF => exact ZxeConv.refl diagram hWF
  | symm _hConv innerConv => exact ZxeConv.symm innerConv
  | trans _hFirst _hSecond firstConv secondConv =>
      exact ZxeConv.trans firstConv secondConv

/-- Every seed conversion embeds (through the FusionRepair embedding). -/
theorem zxeOfZxpConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    ZxeConv firstDiagram secondDiagram :=
  zxeOfZxrConv (zxrOfZxpConv hConv)

/-! ## Stage A2 — the pad-lifting congruence for `ZxeConv` (the ladder's lift ported) -/

/-- THE PAD-LIFTING CONGRUENCE: an exchange-extended derivation between windows lifts
into any padding context (the ladder's `zxnConvLift` ported verbatim to `ZxeConv`). -/
theorem zxeConvLift (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hConv : ZxeConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (firstWindow.sourceArity + rightWires))
    (hAfterWF : ZxpLayersWF
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
    ZxeConv
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow)
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        secondWindow) := by
  revert hBeforeCod hAfterWF
  induction hConv with
  | step hStep =>
      intro hBeforeCod hAfterWF
      cases hStep with
      | pad innerSource innerLeft innerRight innerBefore innerAfter hMove hInnerBWF
          hInnerBCod hInnerAWF =>
          rename_i innerWinFirst innerWinSecond
          have hPadSourceEq : (zxpPadDiagram innerSource innerLeft innerRight
              innerBefore innerAfter innerWinFirst).sourceArity = innerSource := rfl
          rw [hPadSourceEq] at hBeforeCod
          have hPadCodEq := zxpPadDiagramCodArity innerSource innerLeft innerRight
            innerBefore innerAfter innerWinFirst hInnerBCod
          rw [hPadCodEq] at hAfterWF
          rw [zxnPadDiagramCompose contextSource leftWires rightWires beforeLayers
              afterLayers innerSource innerLeft innerRight innerBefore innerAfter
              innerWinFirst,
            zxnPadDiagramCompose contextSource leftWires rightWires beforeLayers
              afterLayers innerSource innerLeft innerRight innerBefore innerAfter
              innerWinSecond]
          have hWhiskBeforeWF := zxpWhiskerLayersWF leftWires rightWires
            innerBefore hInnerBWF
          have hEBeforeWF : ZxpLayersWF contextSource
              (zxpCatLayers beforeLayers
                (zxpWhiskerLayers leftWires rightWires innerBefore)) := by
            refine zxpLayersWFCat beforeLayers _ hBeforeWF ?_
            rw [hBeforeCod]
            exact hWhiskBeforeWF
          have hEBeforeCod : zxpLayersCodArity contextSource
              (zxpCatLayers beforeLayers
                (zxpWhiskerLayers leftWires rightWires innerBefore))
              = (leftWires + innerLeft)
                + (innerWinFirst.sourceArity + (innerRight + rightWires)) := by
            rw [zxpLayersCodArityCat, hBeforeCod,
              zxpWhiskerLayersCodArity leftWires rightWires innerBefore innerSource,
              hInnerBCod]
            exact zxnLiftArityShuffle leftWires innerLeft
              innerWinFirst.sourceArity innerRight rightWires
          have hWhiskAfterWF := zxpWhiskerLayersWF leftWires rightWires
            innerAfter hInnerAWF
          have hEAfterWF : ZxpLayersWF ((leftWires + innerLeft)
              + (zxpDiagramCodArity innerWinFirst + (innerRight + rightWires)))
              (zxpCatLayers (zxpWhiskerLayers leftWires rightWires innerAfter)
                afterLayers) := by
            refine zxpLayersWFCat _ afterLayers ?_ ?_
            · rw [<- zxnLiftArityShuffle leftWires innerLeft
                (zxpDiagramCodArity innerWinFirst) innerRight rightWires]
              exact hWhiskAfterWF
            · rw [<- zxnLiftArityShuffle leftWires innerLeft
                (zxpDiagramCodArity innerWinFirst) innerRight rightWires,
                zxpWhiskerLayersCodArity leftWires rightWires innerAfter
                  (innerLeft + (zxpDiagramCodArity innerWinFirst + innerRight))]
              exact hAfterWF
          exact ZxeConv.step (ZxeStep.pad contextSource (leftWires + innerLeft)
            (innerRight + rightWires)
            (zxpCatLayers beforeLayers
              (zxpWhiskerLayers leftWires rightWires innerBefore))
            (zxpCatLayers (zxpWhiskerLayers leftWires rightWires innerAfter)
              afterLayers)
            hMove hEBeforeWF hEBeforeCod hEAfterWF)
  | refl diagram hWF =>
      intro hBeforeCod hAfterWF
      exact ZxeConv.refl _ (zxpPadDiagramWF contextSource leftWires rightWires
        beforeLayers afterLayers diagram hBeforeWF hBeforeCod hWF hAfterWF)
  | symm hInnerConv innerIH =>
      intro hBeforeCod hAfterWF
      have hBundle := zxeConvSound hInnerConv
      refine ZxeConv.symm (innerIH ?_ ?_)
      · rw [hBeforeCod, hBundle.left]
      · rw [hBundle.right.left]
        exact hAfterWF
  | trans hFirstConv _hSecondConv firstIH secondIH =>
      intro hBeforeCod hAfterWF
      have hFirstBundle := zxeConvSound hFirstConv
      refine ZxeConv.trans (firstIH hBeforeCod hAfterWF) (secondIH ?_ ?_)
      · rw [hBeforeCod, hFirstBundle.left]
      · rw [<- hFirstBundle.right.left]
        exact hAfterWF

/-! ## Stage A3 — plain-context helpers (whisker-free pad, single-step and lift) -/

/-- A pad with zero whisker wires is plain layer concatenation. -/
theorem zxePadPlainLayers (contextSource : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram) :
    zxpPadDiagram contextSource 0 0 beforeLayers afterLayers window
      = { sourceArity := contextSource
          layers := zxpCatLayers beforeLayers
            (zxpCatLayers window.layers afterLayers) } := by
  show ZxpDiagram.mk contextSource
      (zxpCatLayers beforeLayers
        (zxpCatLayers (zxpWhiskerLayers 0 0 window.layers) afterLayers))
    = ZxpDiagram.mk contextSource
        (zxpCatLayers beforeLayers (zxpCatLayers window.layers afterLayers))
  rw [zxpWhiskerLayersZero window.layers]

/-- One window move fired between plain (whisker-free) context layer lists. -/
theorem zxeStepConv (contextSource : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxeWindowMove firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = firstWindow.sourceArity)
    (hAfterWF : ZxpLayersWF (zxpDiagramCodArity firstWindow) afterLayers) :
    ZxeConv
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers firstWindow.layers afterLayers) }
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers secondWindow.layers afterLayers) } := by
  have hBeforeCodPadded : zxpLayersCodArity contextSource beforeLayers
      = 0 + (firstWindow.sourceArity + 0) :=
    hBeforeCod.trans (Nat.zero_add firstWindow.sourceArity).symm
  have hAfterWFPadded : ZxpLayersWF (0 + (zxpDiagramCodArity firstWindow + 0))
      afterLayers := by
    rw [Nat.zero_add]
    exact hAfterWF
  have hStep := ZxeConv.step (ZxeStep.pad contextSource 0 0 beforeLayers afterLayers
    hMove hBeforeWF hBeforeCodPadded hAfterWFPadded)
  rw [zxePadPlainLayers contextSource beforeLayers afterLayers firstWindow,
    zxePadPlainLayers contextSource beforeLayers afterLayers secondWindow] at hStep
  exact hStep

/-- A whole window derivation fired between plain (whisker-free) context layer lists. -/
theorem zxeLiftConv (contextSource : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hConv : ZxeConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = firstWindow.sourceArity)
    (hAfterWF : ZxpLayersWF (zxpDiagramCodArity firstWindow) afterLayers) :
    ZxeConv
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers firstWindow.layers afterLayers) }
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers secondWindow.layers afterLayers) } := by
  have hBeforeCodPadded : zxpLayersCodArity contextSource beforeLayers
      = 0 + (firstWindow.sourceArity + 0) :=
    hBeforeCod.trans (Nat.zero_add firstWindow.sourceArity).symm
  have hAfterWFPadded : ZxpLayersWF (0 + (zxpDiagramCodArity firstWindow + 0))
      afterLayers := by
    rw [Nat.zero_add]
    exact hAfterWF
  have hLifted := zxeConvLift contextSource 0 0 beforeLayers afterLayers hConv
    hBeforeWF hBeforeCodPadded hAfterWFPadded
  rw [zxePadPlainLayers contextSource beforeLayers afterLayers firstWindow,
    zxePadPlainLayers contextSource beforeLayers afterLayers secondWindow] at hLifted
  exact hLifted

/-! ## Stage A4 — the exchange as a fired conversion + the wall's statement over
`ZxeConv` + ladder transports -/

/-- The exchange move fired in the empty context: the window pair converts. -/
theorem zxeExchangeConv (leftCells rightCells : List ZxpCell) :
    ZxeConv (zxeExchangeLhs leftCells rightCells)
      (zxeExchangeRhs leftCells rightCells) := by
  have hStep := ZxeStep.pad
    (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells) 0 0 [] []
    (ZxeWindowMove.rightFirstExchange leftCells rightCells)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt
      (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxeExchangeLhs leftCells rightCells) rfl,
    zxpPadDiagramIdentityAt
      (zxpLayerDomArity leftCells + zxpLayerDomArity rightCells)
      (zxeExchangeRhs leftCells rightCells) rfl] at hStep
  exact ZxeConv.step hStep

/-- The ladder's walled single-cell statement shape, re-quantified over `ZxeConv`
(the `ZxrConv` original `zxnRightFirstExchangeStatement` stays owner-false). -/
def zxeRightFirstExchangeStatement : Prop :=
  (leftCell rightCell : ZxpCell) ->
    ZxeConv
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity [leftCell])) [rightCell],
          zxpCatCells [leftCell] (zxpWireCells (zxpLayerCodArity [rightCell]))] }
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell] [rightCell]] }

/-- THE WALL FALLS OVER `ZxeConv`: the right-first exchange holds — by construction,
as the new move's singleton instance. -/
theorem zxeRightFirstExchangeHolds : zxeRightFirstExchangeStatement :=
  fun leftCell rightCell => zxeExchangeConv [leftCell] [rightCell]

/-- Ladder transport: k = 1 parallel fusion (Z). -/
theorem zxeParallelFusionOneWireZ (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionOneWireZ topLegs botLegs)

/-- Ladder transport: k = 1 parallel fusion (X). -/
theorem zxeParallelFusionOneWireX (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionOneWireX topLegs botLegs)

/-- Ladder transport: k = 2 parallel fusion (Z). -/
theorem zxeParallelFusionTwoWireZ (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionTwoWireZ topLegs botLegs)

/-- Ladder transport: k = 2 parallel fusion (X). -/
theorem zxeParallelFusionTwoWireX (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionTwoWireX topLegs botLegs)

/-- Ladder transport: k = 3 parallel fusion (Z). -/
theorem zxeParallelFusionThreeWireZ (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 3], [ZxpCell.zSpider 3 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionThreeWireZ topLegs botLegs)

/-- Ladder transport: k = 3 parallel fusion (X). -/
theorem zxeParallelFusionThreeWireX (topLegs botLegs : Nat) :
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 3], [ZxpCell.xSpider 3 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } :=
  zxeOfZxrConv (zxnParallelFusionThreeWireX topLegs botLegs)

/-- Ladder transport: eta expansion of the wire into the Z identity spider. -/
theorem zxeEtaExpandWireZ : ZxeConv zxnWireDiagram zxnZIdentitySpiderDiagram :=
  zxeOfZxrConv zxnEtaExpandWireZ

/-- Ladder transport: eta expansion of the wire into the X identity spider. -/
theorem zxeEtaExpandWireX : ZxeConv zxnWireDiagram zxnXIdentitySpiderDiagram :=
  zxeOfZxrConv zxnEtaExpandWireX

/-! ## Stage B — THE GATE RE-RUN over `ZxeConv` (arc law: refutation pass first)

The fold-engine analysis extended to the exchange move.  THE KEY FACT: the exchange is
INVISIBLE to the entire wire-vanishing weight family — both sides carry exactly the
cells of `leftCells` and `rightCells` plus wires — so the engine's admissibility
hypotheses for `ZxeConv` are THE SAME FOUR as for `ZxrConv`, and the FusionRepair
collapse carries verbatim. -/

/-- THE EXCHANGE IS INVISIBLE: every wire-vanishing per-cell weight is balanced on
every exchange instance — no row-balance hypotheses needed at all. -/
theorem zxeExchangeFoldBalanced (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0) (leftCells rightCells : List ZxpCell) :
    zxgLayersFold cellWeight (zxeExchangeLhs leftCells rightCells).layers
      = zxgLayersFold cellWeight (zxeExchangeRhs leftCells rightCells).layers := by
  show zxgCellFold cellWeight
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
      + (zxgCellFold cellWeight
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))) + 0)
    = zxgCellFold cellWeight (zxpCatCells leftCells rightCells) + 0
  rw [zxgCellFoldCat cellWeight (zxpWireCells (zxpLayerDomArity leftCells)) rightCells,
    zxgCellFoldCat cellWeight leftCells (zxpWireCells (zxpLayerCodArity rightCells)),
    zxgCellFoldCat cellWeight leftCells rightCells,
    zxgCellFoldWires cellWeight hWireZero (zxpLayerDomArity leftCells),
    zxgCellFoldWires cellWeight hWireZero (zxpLayerCodArity rightCells),
    Nat.zero_add (zxgCellFold cellWeight rightCells)]
  exact Nat.add_comm (zxgCellFold cellWeight rightCells)
    (zxgCellFold cellWeight leftCells)

/-- INVARIANCE, window level, exchange-extended move set: the SAME four hypotheses as
FusionRepair's engine — the exchange case is discharged from wire-vanishing alone. -/
theorem zxeWindowMoveFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxeWindowMove firstWindow secondWindow) :
    zxgLayersFold cellWeight firstWindow.layers
      = zxgLayersFold cellWeight secondWindow.layers := by
  cases hMove with
  | base hBaseMove =>
      exact zxrWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
        hXFuseBalanced hBaseMove
  | rightFirstExchange leftCells rightCells =>
      exact zxeExchangeFoldBalanced cellWeight hWireZero leftCells rightCells

/-- INVARIANCE, step level (padded contexts cancel). -/
theorem zxeStepFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxeStep firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      rename_i firstWindow secondWindow
      rw [zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers firstWindow,
        zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers secondWindow,
        zxeWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
          hXFuseBalanced hMove]

/-- INVARIANCE, full exchange-extended congruence: any wire-vanishing weight balanced
on rows + both fusion families is conserved by `ZxeConv` (exchange balance is FREE). -/
theorem zxeConvFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxeConv firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  induction hConv with
  | step hStep =>
      exact zxeStepFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
        hXFuseBalanced hStep
  | refl diagram hWF => exact rfl
  | symm _hConv innerEq => exact innerEq.symm
  | trans _hFirst _hSecond firstEq secondEq => exact firstEq.trans secondEq

/-- THE COLLAPSE CARRIES: every wire-vanishing weight admissible for the `ZxeConv`
engine is identically zero — the hypotheses are the same four as FusionRepair's, so
the whole per-cell count family still holds NO separator (now for `ZxeConv`). -/
theorem zxeBalancedWeightCollapse (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight) :
    (cell : ZxpCell) -> cellWeight cell = 0 :=
  zxrBalancedWeightCollapse cellWeight hWireZero hRowsBalanced hZFuseBalanced
    hXFuseBalanced

/-- Corollary: every engine-admissible weight folds to constant zero on every diagram. -/
theorem zxeBalancedWeightFoldZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (diagram : ZxpDiagram) : zxgDiagramFold cellWeight diagram = 0 :=
  zxrBalancedWeightFoldZero cellWeight hWireZero hRowsBalanced hZFuseBalanced
    hXFuseBalanced diagram

/-- Even the gate's original separator (the big-spider count) cannot see the exchange
move — it is wire-vanishing, hence exchange-balanced at every instance. -/
theorem zxeBigSpiderExchangeBalanced (leftCells rightCells : List ZxpCell) :
    zxgLayersFold zxgCellBigSpiderWeight (zxeExchangeLhs leftCells rightCells).layers
      = zxgLayersFold zxgCellBigSpiderWeight
          (zxeExchangeRhs leftCells rightCells).layers :=
  zxeExchangeFoldBalanced zxgCellBigSpiderWeight rfl leftCells rightCells

/-! ### The base 7-vector mod-2 re-run -/

/-- The wire-count fold shift of an exchange instance: the two-layer side carries
exactly `dom(L) + cod(R)` extra wire cells. -/
theorem zxeExchangeWireFoldShift (leftCells rightCells : List ZxpCell) :
    zxgLayersFold zxgCellWireCountWeight (zxeExchangeLhs leftCells rightCells).layers
      = zxgLayersFold zxgCellWireCountWeight
          (zxeExchangeRhs leftCells rightCells).layers
        + (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells) := by
  show zxgCellFold zxgCellWireCountWeight
        (zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells)
      + (zxgCellFold zxgCellWireCountWeight
          (zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))) + 0)
    = zxgCellFold zxgCellWireCountWeight (zxpCatCells leftCells rightCells) + 0
      + (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)
  rw [zxgCellFoldCat zxgCellWireCountWeight
      (zxpWireCells (zxpLayerDomArity leftCells)) rightCells,
    zxgCellFoldCat zxgCellWireCountWeight leftCells
      (zxpWireCells (zxpLayerCodArity rightCells)),
    zxgCellFoldCat zxgCellWireCountWeight leftCells rightCells,
    zxrWireCountFoldWires (zxpLayerDomArity leftCells),
    zxrWireCountFoldWires (zxpLayerCodArity rightCells),
    Nat.add_zero (zxgCellFold zxgCellWireCountWeight leftCells
      + zxgCellFold zxgCellWireCountWeight rightCells),
    Nat.add_zero (zxgCellFold zxgCellWireCountWeight leftCells
      + zxpLayerCodArity rightCells),
    zxgAddMedial (zxpLayerDomArity leftCells)
      (zxgCellFold zxgCellWireCountWeight rightCells)
      (zxgCellFold zxgCellWireCountWeight leftCells) (zxpLayerCodArity rightCells),
    zxgAddMedial (zxgCellFold zxgCellWireCountWeight leftCells)
      (zxgCellFold zxgCellWireCountWeight rightCells)
      (zxpLayerDomArity leftCells) (zxpLayerCodArity rightCells),
    Nat.add_comm (zxpLayerDomArity leftCells)
      (zxgCellFold zxgCellWireCountWeight leftCells)]

/-- THE GENERAL EXCHANGE DELTA (proved saturation, all cell lists): the mod-2 delta of
every exchange instance on the base count vector is
`[0, 0, parity(dom(L) + cod(R)), 0, 1, 0, 0]` — exactly the splitLayer delta family. -/
theorem zxeExchangeDeltaGeneral (leftCells rightCells : List ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxeExchangeLhs leftCells rightCells))
        (zxgCountVector (zxeExchangeRhs leftCells rightCells))
      = [false, false,
          zxgParityB (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells),
          false, true, false, false] := by
  have hZEq := zxeExchangeFoldBalanced zxgCellZCountWeight rfl leftCells rightCells
  have hXEq := zxeExchangeFoldBalanced zxgCellXCountWeight rfl leftCells rightCells
  have hCrossEq := zxeExchangeFoldBalanced zxgCellCrossCountWeight rfl
    leftCells rightCells
  have hZLegsEq := zxeExchangeFoldBalanced zxgCellZLegsWeight rfl leftCells rightCells
  have hXLegsEq := zxeExchangeFoldBalanced zxgCellXLegsWeight rfl leftCells rightCells
  have hWireShift := zxeExchangeWireFoldShift leftCells rightCells
  show [zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZCountWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellZCountWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXCountWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellXCountWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayerCount (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayerCount (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight
        (zxeExchangeLhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight
        (zxeExchangeRhs leftCells rightCells).layers))]
    = [false, false,
        zxgParityB (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells),
        false, true, false, false]
  rw [hZEq, hXEq, hCrossEq, hZLegsEq, hXLegsEq, hWireShift,
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZCountWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXCountWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZLegsWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXLegsWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxgParityBAdd (zxgLayersFold zxgCellWireCountWeight
      (zxeExchangeRhs leftCells rightCells).layers)
      (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells),
    zxpXorBComm (zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxeExchangeRhs leftCells rightCells).layers))
      (zxgParityB (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells)),
    zxpXorBAssoc
      (zxgParityB (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells))
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxeExchangeRhs leftCells rightCells).layers))
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxeExchangeRhs leftCells rightCells).layers)),
    zxpXorBFalseRight
      (zxgParityB (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells))]
  exact rfl

/-- Exchange delta literal, even pass-wire count (byte-identical to the gate's
crossing split witness). -/
def zxeExchangeDeltaEven : List Bool := [false, false, false, false, true, false, false]

/-- Exchange delta literal, odd pass-wire count (byte-identical to the gate's wire
split witness). -/
def zxeExchangeDeltaOdd : List Bool := [false, false, true, false, true, false, false]

/-- SATURATION, case form: every exchange instance's delta is one of the two literals. -/
theorem zxeExchangeDeltaCases (leftCells rightCells : List ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxeExchangeLhs leftCells rightCells))
        (zxgCountVector (zxeExchangeRhs leftCells rightCells))
      = zxeExchangeDeltaEven
    \/ zxgVectorDeltaMod2 (zxgCountVector (zxeExchangeLhs leftCells rightCells))
        (zxgCountVector (zxeExchangeRhs leftCells rightCells))
      = zxeExchangeDeltaOdd := by
  cases hPassParity : zxgParityB
      (zxpLayerDomArity leftCells + zxpLayerCodArity rightCells) with
  | false =>
      refine Or.inl ?_
      rw [zxeExchangeDeltaGeneral leftCells rightCells, hPassParity]
      exact rfl
  | true =>
      refine Or.inr ?_
      rw [zxeExchangeDeltaGeneral leftCells rightCells, hPassParity]
      exact rfl

/-- THE EXCHANGE-EXTENDED DELTA TABLE: FusionRepair's 39-row table plus the two
exchange literals (which saturate the whole exchange family by the case lemma). -/
def zxeExtendedDeltaTable : List (List Bool) :=
  zxpCatRows zxrExtendedDeltaTable [zxeExchangeDeltaEven, zxeExchangeDeltaOdd]

/-- KERNEL PIN: the exchange-extended delta row space equals the gate's SAME
6-dimensional basis — the exchange adds a move but NO new mod-2 direction. -/
theorem zxeExtendedDeltaSpanBasisPin :
    zxpSpanEqB zxeExtendedDeltaTable zxgDeltaSpanBasis = true := rfl

/-- Classifier over the exchange-extended table: orthogonality holds exactly for the
zero functional and the legs-parity functional. -/
def zxeIsPreservedExactlyLegsParityB : List (List Bool) -> Bool
  | [] => true
  | headFunctional :: restFunctionals =>
      cond (zxgBoolEqB (zxgIsOrthogonalToAllB headFunctional zxeExtendedDeltaTable)
          (cond (zxgRowEqB headFunctional zxgZeroFunctional) true
            (zxgRowEqB headFunctional zxgLegsParityFunctional)))
        (zxeIsPreservedExactlyLegsParityB restFunctionals) false

/-- KERNEL PIN: over ALL 128 mod-2 functionals, the preserved lattice of the
exchange-extended move set is STILL exactly {0, legs-parity} — and the survivor stays
boundary-determined by the gate's per-diagram theorem
(`zxgLegsParityFunctionalBoundaryDetermined`), untouched by any move-set extension. -/
theorem zxePreservedLatticeReclassified :
    zxeIsPreservedExactlyLegsParityB (zxgAllBoolVectors 7) = true := rfl

/-- The survivor is orthogonal to EVERY exchange delta at every arity. -/
theorem zxeLegsParityOrthogonalExchangeDelta (leftCells rightCells : List ZxpCell) :
    zxgDotB zxgLegsParityFunctional
        (zxgVectorDeltaMod2 (zxgCountVector (zxeExchangeLhs leftCells rightCells))
          (zxgCountVector (zxeExchangeRhs leftCells rightCells)))
      = false := by
  cases zxeExchangeDeltaCases leftCells rightCells with
  | inl hEven =>
      rw [hEven]
      exact rfl
  | inr hOdd =>
      rw [hOdd]
      exact rfl

/-- THE GATE RE-RUN VERDICT MARKER: outcome CLEAN.  Checked precisely: (1) the exchange
is invisible to every wire-vanishing per-cell weight (`zxeExchangeFoldBalanced`), so
(2) the engine hypotheses are unchanged and the FusionRepair collapse carries verbatim
(`zxeBalancedWeightCollapse` — the whole per-cell count family, home of BOTH prior
refutations of this workstream, holds no `ZxeConv` separator); (3) the general delta
saturation lemma pins every exchange instance to the two splitLayer literals, the
extended table spans the same 6-dimensional basis (`zxeExtendedDeltaSpanBasisPin`),
the 128-functional lattice is still exactly {0, legs-parity}
(`zxePreservedLatticeReclassified`), and the survivor is boundary-determined and
orthogonal to every exchange delta; (4) the refutation instrument still bites
(`zxeBigColourNotConv` below).  No separator exists in the commissioned families;
the extension is semantically sound at all arities by construction. -/
def zxeGateVerdictIsClean : Bool := true

/-! ## Stage C — GENERAL-k PARALLEL FUSION over `ZxeConv`

The engine is the right-corner absorption family: a splitter (`spider 1 2`) feeding
the LAST TWO inputs of a same-colour spider under `p` pass wires absorbs into it.
Recursion on `p`: p = 0 is the shipped fully-shared k = 2 fusion; p = 1 fissions the
bottom spider and crosses the CONNECTED middle with THE FROBENIUS ROW; p >= 2 fissions
the bottom spider, merges the DISJOINT right-first middle with ONE EXCHANGE MOVE,
re-splits it left-first with one splitLayer, and descends. -/

/-- Right-corner splitter absorption (Z):
`[[wire^p, zSpider 1 2], [zSpider (p+2) d]] ~ [[zSpider (p+1) d]]`. -/
theorem zxeParallelFusionStepZ (botOutputs : Nat) : (passWires : Nat) ->
    ZxeConv
      { sourceArity := passWires + 1
        layers := [zxpCatCells (zxpWireCells passWires) [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider (passWires + 2) botOutputs]] }
      { sourceArity := passWires + 1
        layers := [[ZxpCell.zSpider (passWires + 1) botOutputs]] }
  | 0 => zxeParallelFusionTwoWireZ 1 botOutputs
  | 1 => by
      -- THE FROBENIUS ROUTE: the middle pair is CONNECTED, the exchange must not fire.
      -- E0 = [[w, z12], [z 3 d]] ~ E1 = [[w, z12], [z21, w], [z 2 d]] (fission bottom)
      have hFissionRaw : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider 3 (0 + botOutputs)]] } :=
        zxeStepConv 2 [[ZxpCell.wire, ZxpCell.zSpider 1 2]] []
          (ZxeWindowMove.base (ZxrWindowMove.zFuse 2 0 1 botOutputs))
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFissionRaw
      -- E1 ~ E2 = [[z21], [z12], [z 2 d]] (THE FROBENIUS ROW on the middle pair)
      have hFrobenius : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider 2 botOutputs]] } :=
        zxeStepConv 2 [] [[ZxpCell.zSpider 2 botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.row ZxpRowTag.frobeniusZRight)))
          (ZxpLayersWF.nil _) rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
      -- E2 ~ E3 = [[z21], [z 1 d]] (fully-shared k = 2 fusion on the bottom pair)
      have hBottomFuse : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 botOutputs]] } :=
        zxeLiftConv 2 [[ZxpCell.zSpider 2 1]] []
          (zxeParallelFusionTwoWireZ 1 botOutputs)
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      -- E3 ~ E4 = [[z 2 d]] (the final one-wire fusion)
      have hFinalFuse := zxeParallelFusionOneWireZ 2 botOutputs
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw) (ZxeConv.trans hFrobenius
        (ZxeConv.trans hBottomFuse hFinalFuse))
  | passPred + 2 => by
      -- THE EXCHANGE ROUTE: the middle pair is DISJOINT right-first.
      -- Arity fixups for the pass block
      have hDomR : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
          = passPred + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        exact rfl
      have hCodR : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
          = passPred + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        exact rfl
      -- D0 ~ E1: fission the bottom spider at its first input
      have hFissionRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.zSpider 1 2],
              ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 2),
              [ZxpCell.zSpider (1 + (passPred + 2)) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider (2 + (passPred + 2)) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + 1)
          [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.zSpider 1 2]] []
          (ZxeWindowMove.base (ZxrWindowMove.zFuse 2 0 (passPred + 2) botOutputs))
          (ZxpLayersWF.cons
            (by
              rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
              exact rfl)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity
                (zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.zSpider 1 2])
              = 2 + (passPred + 2)
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact Nat.add_comm (passPred + 2) 2)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs, Nat.add_comm 2 (passPred + 2),
        Nat.add_comm 1 (passPred + 2)] at hFissionRaw
      -- E1 ~ E2: THE EXCHANGE merges the disjoint right-first middle pair
      have hExchange : ZxeConv
          { sourceArity := 2 + zxpLayerDomArity
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
            layers := [ZxpCell.wire :: ZxpCell.wire
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2],
              ZxpCell.zSpider 2 1 :: zxpWireCells (zxpLayerCodArity
                (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2]))] }
          { sourceArity := 2 + zxpLayerDomArity
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
            layers := [ZxpCell.zSpider 2 1
              :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2]] } :=
        zxeExchangeConv [ZxpCell.zSpider 2 1]
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
      rw [hDomR, hCodR, Nat.add_comm 2 (passPred + 1)] at hExchange
      have hExchangeInContext : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.wire :: ZxpCell.wire
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2],
              ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 2),
              [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + 1) []
          [[ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]] hExchange
          (ZxpLayersWF.nil _) rfl
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]
                = 1 + zxpLayerCodArity (zxpWireCells (passPred + 2))
              rw [zxpWireCellsCodArity (passPred + 2)]
              exact (Nat.add_comm 1 (passPred + 2)).symm)
            (ZxpLayersWF.nil _))
      -- E2 ~ E3: one splitLayer re-splits the merged middle LEFT-FIRST
      have hSplitRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1 :: zxpWireCells (zxpLayerDomArity
                (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])),
              ZxpCell.wire :: zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]] } :=
        zxeStepConv ((passPred + 2) + 1) []
          [[ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.splitLayer [ZxpCell.zSpider 2 1]
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2]))))
          (ZxpLayersWF.nil _)
          (by
            show zxpLayersCodArity ((passPred + 2) + 1) []
              = zxpLayerDomArity [ZxpCell.zSpider 2 1] + zxpLayerDomArity
                  (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
            rw [hDomR]
            exact Nat.add_comm (passPred + 1) 2)
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.zSpider ((passPred + 2) + 1) botOutputs]
                = 1 + zxpLayerCodArity
                    (zxpCatCells (zxpWireCells passPred) [ZxpCell.zSpider 1 2])
              rw [hCodR]
              exact (Nat.add_comm 1 (passPred + 2)).symm)
            (ZxpLayersWF.nil _))
      rw [hDomR] at hSplitRaw
      -- E3 ~ E4: the recursion descends to passPred + 1 pass wires
      have hRecurse : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 1),
              zxpCatCells (zxpWireCells (passPred + 1)) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider ((passPred + 1) + 2) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 1),
              [ZxpCell.zSpider ((passPred + 1) + 1) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + 1)
          [ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 1)] []
          (zxeParallelFusionStepZ botOutputs (passPred + 1))
          (ZxpLayersWF.cons
            (by
              show 2 + zxpLayerDomArity (zxpWireCells (passPred + 1))
                = (passPred + 2) + 1
              rw [zxpWireCellsDomArity (passPred + 1)]
              exact Nat.add_comm 2 (passPred + 1))
            (ZxpLayersWF.nil _))
          (by
            show 1 + zxpLayerCodArity (zxpWireCells (passPred + 1))
              = (passPred + 1) + 1
            rw [zxpWireCellsCodArity (passPred + 1)]
            exact Nat.add_comm 1 (passPred + 1))
          (ZxpLayersWF.nil _)
      -- E4 ~ E5: the final primitive one-wire fusion
      have hFinalRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + 1),
              [ZxpCell.zSpider (1 + (passPred + 1)) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [[ZxpCell.zSpider (2 + (passPred + 1)) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + 1) [] []
          (ZxeWindowMove.base (ZxrWindowMove.zFuse 2 0 (passPred + 1) botOutputs))
          (ZxpLayersWF.nil _) (Nat.add_comm (passPred + 1) 2) (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs, Nat.add_comm 2 (passPred + 1),
        Nat.add_comm 1 (passPred + 1)] at hFinalRaw
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw)
        (ZxeConv.trans hExchangeInContext (ZxeConv.trans hSplitRaw
          (ZxeConv.trans hRecurse hFinalRaw)))

/-- Right-corner splitter absorption (X), the colour mirror through
`frobeniusXRight` and `xFuse`. -/
theorem zxeParallelFusionStepX (botOutputs : Nat) : (passWires : Nat) ->
    ZxeConv
      { sourceArity := passWires + 1
        layers := [zxpCatCells (zxpWireCells passWires) [ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider (passWires + 2) botOutputs]] }
      { sourceArity := passWires + 1
        layers := [[ZxpCell.xSpider (passWires + 1) botOutputs]] }
  | 0 => zxeParallelFusionTwoWireX 1 botOutputs
  | 1 => by
      have hFissionRaw : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider 3 (0 + botOutputs)]] } :=
        zxeStepConv 2 [[ZxpCell.wire, ZxpCell.xSpider 1 2]] []
          (ZxeWindowMove.base (ZxrWindowMove.xFuse 2 0 1 botOutputs))
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFissionRaw
      have hFrobenius : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.wire, ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider 2 botOutputs]] } :=
        zxeStepConv 2 [] [[ZxpCell.xSpider 2 botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.row ZxpRowTag.frobeniusXRight)))
          (ZxpLayersWF.nil _) rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
      have hBottomFuse : ZxeConv
          { sourceArity := 2
            layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider 2 botOutputs]] }
          { sourceArity := 2
            layers := [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 botOutputs]] } :=
        zxeLiftConv 2 [[ZxpCell.xSpider 2 1]] []
          (zxeParallelFusionTwoWireX 1 botOutputs)
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      have hFinalFuse := zxeParallelFusionOneWireX 2 botOutputs
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw) (ZxeConv.trans hFrobenius
        (ZxeConv.trans hBottomFuse hFinalFuse))
  | passPred + 2 => by
      have hDomR : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
          = passPred + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        exact rfl
      have hCodR : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
          = passPred + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        exact rfl
      have hFissionRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.xSpider 1 2],
              ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 2),
              [ZxpCell.xSpider (1 + (passPred + 2)) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider (2 + (passPred + 2)) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + 1)
          [zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.xSpider 1 2]] []
          (ZxeWindowMove.base (ZxrWindowMove.xFuse 2 0 (passPred + 2) botOutputs))
          (ZxpLayersWF.cons
            (by
              rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
              exact rfl)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity
                (zxpCatCells (zxpWireCells (passPred + 2)) [ZxpCell.xSpider 1 2])
              = 2 + (passPred + 2)
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact Nat.add_comm (passPred + 2) 2)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs, Nat.add_comm 2 (passPred + 2),
        Nat.add_comm 1 (passPred + 2)] at hFissionRaw
      have hExchange : ZxeConv
          { sourceArity := 2 + zxpLayerDomArity
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
            layers := [ZxpCell.wire :: ZxpCell.wire
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2],
              ZxpCell.xSpider 2 1 :: zxpWireCells (zxpLayerCodArity
                (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2]))] }
          { sourceArity := 2 + zxpLayerDomArity
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
            layers := [ZxpCell.xSpider 2 1
              :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2]] } :=
        zxeExchangeConv [ZxpCell.xSpider 2 1]
          (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
      rw [hDomR, hCodR, Nat.add_comm 2 (passPred + 1)] at hExchange
      have hExchangeInContext : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.wire :: ZxpCell.wire
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2],
              ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 2),
              [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + 1) []
          [[ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]] hExchange
          (ZxpLayersWF.nil _) rfl
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]
                = 1 + zxpLayerCodArity (zxpWireCells (passPred + 2))
              rw [zxpWireCellsCodArity (passPred + 2)]
              exact (Nat.add_comm 1 (passPred + 2)).symm)
            (ZxpLayersWF.nil _))
      have hSplitRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1
                :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1 :: zxpWireCells (zxpLayerDomArity
                (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])),
              ZxpCell.wire :: zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]] } :=
        zxeStepConv ((passPred + 2) + 1) []
          [[ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.splitLayer [ZxpCell.xSpider 2 1]
              (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2]))))
          (ZxpLayersWF.nil _)
          (by
            show zxpLayersCodArity ((passPred + 2) + 1) []
              = zxpLayerDomArity [ZxpCell.xSpider 2 1] + zxpLayerDomArity
                  (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
            rw [hDomR]
            exact Nat.add_comm (passPred + 1) 2)
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.xSpider ((passPred + 2) + 1) botOutputs]
                = 1 + zxpLayerCodArity
                    (zxpCatCells (zxpWireCells passPred) [ZxpCell.xSpider 1 2])
              rw [hCodR]
              exact (Nat.add_comm 1 (passPred + 2)).symm)
            (ZxpLayersWF.nil _))
      rw [hDomR] at hSplitRaw
      have hRecurse : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 1),
              zxpCatCells (zxpWireCells (passPred + 1)) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider ((passPred + 1) + 2) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 1),
              [ZxpCell.xSpider ((passPred + 1) + 1) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + 1)
          [ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 1)] []
          (zxeParallelFusionStepX botOutputs (passPred + 1))
          (ZxpLayersWF.cons
            (by
              show 2 + zxpLayerDomArity (zxpWireCells (passPred + 1))
                = (passPred + 2) + 1
              rw [zxpWireCellsDomArity (passPred + 1)]
              exact Nat.add_comm 2 (passPred + 1))
            (ZxpLayersWF.nil _))
          (by
            show 1 + zxpLayerCodArity (zxpWireCells (passPred + 1))
              = (passPred + 1) + 1
            rw [zxpWireCellsCodArity (passPred + 1)]
            exact Nat.add_comm 1 (passPred + 1))
          (ZxpLayersWF.nil _)
      have hFinalRaw : ZxeConv
          { sourceArity := (passPred + 2) + 1
            layers := [ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + 1),
              [ZxpCell.xSpider (1 + (passPred + 1)) botOutputs]] }
          { sourceArity := (passPred + 2) + 1
            layers := [[ZxpCell.xSpider (2 + (passPred + 1)) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + 1) [] []
          (ZxeWindowMove.base (ZxrWindowMove.xFuse 2 0 (passPred + 1) botOutputs))
          (ZxpLayersWF.nil _) (Nat.add_comm (passPred + 1) 2) (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs, Nat.add_comm 2 (passPred + 1),
        Nat.add_comm 1 (passPred + 1)] at hFinalRaw
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw)
        (ZxeConv.trans hExchangeInContext (ZxeConv.trans hSplitRaw
          (ZxeConv.trans hRecurse hFinalRaw)))

/-- GENERAL-k PARALLEL FUSION (Z), all shared-wire counts `sharedPred + 1`, all
boundary arities: fission the top spider one output at a time, absorb the splitter
with the right-corner engine, descend. -/
theorem zxeParallelFusionZ (topLegs botLegs : Nat) : (sharedPred : Nat) ->
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs (sharedPred + 1)],
          [ZxpCell.zSpider (sharedPred + 1) botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] }
  | 0 => zxeParallelFusionOneWireZ topLegs botLegs
  | sharedPredPred + 1 => by
      -- fission the top spider at its last output
      have hFissionRaw : ZxeConv
          { sourceArity := topLegs
            layers := [[ZxpCell.zSpider topLegs (sharedPredPred + 1)],
              zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider (sharedPredPred + 2) botLegs]] }
          { sourceArity := topLegs
            layers := [[ZxpCell.zSpider topLegs (sharedPredPred + 2)],
              [ZxpCell.zSpider (sharedPredPred + 2) botLegs]] } :=
        zxeStepConv topLegs [] [[ZxpCell.zSpider (sharedPredPred + 2) botLegs]]
          (ZxeWindowMove.base (ZxrWindowMove.zFuse topLegs sharedPredPred 0 2))
          (ZxpLayersWF.nil _) rfl
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.zSpider (sharedPredPred + 2) botLegs]
                = zxpLayerCodArity
                    (zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.zSpider 1 2])
              rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
              exact rfl)
            (ZxpLayersWF.nil _))
      -- absorb the splitter into the bottom spider
      have hAbsorb : ZxeConv
          { sourceArity := topLegs
            layers := [[ZxpCell.zSpider topLegs (sharedPredPred + 1)],
              zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.zSpider 1 2],
              [ZxpCell.zSpider (sharedPredPred + 2) botLegs]] }
          { sourceArity := topLegs
            layers := [[ZxpCell.zSpider topLegs (sharedPredPred + 1)],
              [ZxpCell.zSpider (sharedPredPred + 1) botLegs]] } :=
        zxeLiftConv topLegs [[ZxpCell.zSpider topLegs (sharedPredPred + 1)]] []
          (zxeParallelFusionStepZ botLegs sharedPredPred)
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw)
        (ZxeConv.trans hAbsorb (zxeParallelFusionZ topLegs botLegs sharedPredPred))

/-- GENERAL-k PARALLEL FUSION (X), the colour mirror. -/
theorem zxeParallelFusionX (topLegs botLegs : Nat) : (sharedPred : Nat) ->
    ZxeConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs (sharedPred + 1)],
          [ZxpCell.xSpider (sharedPred + 1) botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] }
  | 0 => zxeParallelFusionOneWireX topLegs botLegs
  | sharedPredPred + 1 => by
      have hFissionRaw : ZxeConv
          { sourceArity := topLegs
            layers := [[ZxpCell.xSpider topLegs (sharedPredPred + 1)],
              zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider (sharedPredPred + 2) botLegs]] }
          { sourceArity := topLegs
            layers := [[ZxpCell.xSpider topLegs (sharedPredPred + 2)],
              [ZxpCell.xSpider (sharedPredPred + 2) botLegs]] } :=
        zxeStepConv topLegs [] [[ZxpCell.xSpider (sharedPredPred + 2) botLegs]]
          (ZxeWindowMove.base (ZxrWindowMove.xFuse topLegs sharedPredPred 0 2))
          (ZxpLayersWF.nil _) rfl
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity [ZxpCell.xSpider (sharedPredPred + 2) botLegs]
                = zxpLayerCodArity
                    (zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.xSpider 1 2])
              rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
              exact rfl)
            (ZxpLayersWF.nil _))
      have hAbsorb : ZxeConv
          { sourceArity := topLegs
            layers := [[ZxpCell.xSpider topLegs (sharedPredPred + 1)],
              zxpCatCells (zxpWireCells sharedPredPred) [ZxpCell.xSpider 1 2],
              [ZxpCell.xSpider (sharedPredPred + 2) botLegs]] }
          { sourceArity := topLegs
            layers := [[ZxpCell.xSpider topLegs (sharedPredPred + 1)],
              [ZxpCell.xSpider (sharedPredPred + 1) botLegs]] } :=
        zxeLiftConv topLegs [[ZxpCell.xSpider topLegs (sharedPredPred + 1)]] []
          (zxeParallelFusionStepX botLegs sharedPredPred)
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      exact ZxeConv.trans (ZxeConv.symm hFissionRaw)
        (ZxeConv.trans hAbsorb (zxeParallelFusionX topLegs botLegs sharedPredPred))

/-- THE COMBINED GENERAL-k FUSION: all shared-wire counts, both colours, all arities. -/
theorem zxeParallelFusion :
    ((topLegs botLegs sharedPred : Nat) ->
      ZxeConv
        { sourceArity := topLegs
          layers := [[ZxpCell.zSpider topLegs (sharedPred + 1)],
            [ZxpCell.zSpider (sharedPred + 1) botLegs]] }
        { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] })
    /\ ((topLegs botLegs sharedPred : Nat) ->
      ZxeConv
        { sourceArity := topLegs
          layers := [[ZxpCell.xSpider topLegs (sharedPred + 1)],
            [ZxpCell.xSpider (sharedPred + 1) botLegs]] }
        { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] }) :=
  And.intro (fun topLegs botLegs sharedPred => zxeParallelFusionZ topLegs botLegs
    sharedPred)
    (fun topLegs botLegs sharedPred => zxeParallelFusionX topLegs botLegs sharedPred)

/-! ### Stage C fires -/

/-- FIRE k = 4 (Z): the FIRST parallel-fusion instance beyond the ladder's k = 3 wall. -/
theorem zxeParallelFusionFourWireZFire :
    ZxeConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 4], [ZxpCell.zSpider 4 1]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 1]] } :=
  zxeParallelFusionZ 1 1 3

/-- FIRE k = 5 (Z), the commissioned instance: `[[zSpider 2 5],[zSpider 5 3]]`
converts to `[[zSpider 2 3]]`. -/
theorem zxeParallelFusionFiveWireZFire :
    ZxeConv
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 2 5], [ZxpCell.zSpider 5 3]] }
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 3]] } :=
  zxeParallelFusionZ 2 3 4

/-- FIRE k = 5 (X), the colour mirror. -/
theorem zxeParallelFusionFiveWireXFire :
    ZxeConv
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 2 5], [ZxpCell.xSpider 5 3]] }
      { sourceArity := 2, layers := [[ZxpCell.xSpider 2 3]] } :=
  zxeParallelFusionX 2 3 4

set_option maxRecDepth 8192 in
/-- Independent kernel cross-check of the k = 5 fire: the pair is span-equal by direct
span decision (the conversion is honest). -/
theorem zxeParallelFusionFiveWireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.zSpider 2 5], [ZxpCell.zSpider 5 3]] })
      (zxpDiagramDenote
        { sourceArity := 2, layers := [[ZxpCell.zSpider 2 3]] }) = true := rfl

/-! ## Stage D — the completeness statement over `ZxeConv`, absorption partials,
the conditional decision corollary, and the honest owner ledger -/

/-- COMPLETENESS statement over the EXCHANGE-EXTENDED congruence — VERBATIM the shape
of FusionRepair's `zxrCompletenessStatement` with `ZxeConv` in the conclusion.

NOT a silent restatement of the `ZxrConv` original: that statement stays owner-false
in FusionRepair, and THE PRECISE DELTA between the two is the exchange-admissibility
lemma (is the right-first exchange derivable in `ZxrConv`?), recorded open below.

OWNER FALSE — NOT PROVEN.  The invariant-first gate for THIS statement ran CLEAN
(Stage B).  What a push MAY now assume on top of FusionRepair's ledger: the right-first
exchange at all cell lists (`zxeExchangeConv`), general-k parallel fusion both colours
all arities (`zxeParallelFusionZ/X`), the pad lift (`zxeConvLift`), and the identity-
wire absorptions below.  THE REMAINING BILL, per the census commission: (iii) the
leg-permutation engine (crossing conjugation for arbitrary-arity side-by-side
spiders), then (iv) the Kissinger Lemma 3.2/3.3 absorption induction over the census
`zxnNormalForm` (init bases, per-generator combs with crossing walks, kill
collectors), using `zxnNormalFormDenotes` to know the target. -/
def zxeCompletenessStatement : Prop :=
  (firstDiagram secondDiagram : ZxpDiagram) ->
    ZxpDiagramWF firstDiagram -> ZxpDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram ->
    ZxpRelEquiv firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
      (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram) ->
    ZxeConv firstDiagram secondDiagram

/-- OWNER MARKER: completeness over `ZxeConv` is NOT proven. -/
def zxeCompletenessIsProven : Bool := false

/-- OWNER MARKER: whether the right-first exchange is ADMISSIBLE in `ZxrConv`
(derivable from rows + splitLayer + fusion) is OPEN — neither proven nor refuted.
Both congruences are span-sound, so no semantic separator between them can exist, and
Stage B shows no per-cell counting separator exists either: the question is genuinely
syntactic.  While it stays open, `zxnRightFirstExchangeStatement` (ZxrConv form) stays
owner-false in the ladder and `zxrCompletenessStatement` cannot inherit this brick's
(C). -/
def zxeExchangeAdmissibleInZxrConvIsProven : Bool := false

/-- ABSORPTION (trivial cell, leading): a full wire layer before any layer strips —
one `splitLayer` read backwards. -/
theorem zxeStripLeadingWireLayer (cells : List ZxpCell) :
    ZxeConv
      { sourceArity := zxpLayerDomArity cells
        layers := [zxpWireCells (zxpLayerDomArity cells), cells] }
      { sourceArity := zxpLayerDomArity cells, layers := [cells] } := by
  have hStep := ZxeStep.pad (0 + zxpLayerDomArity cells) 0 0 [] []
    (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer [] cells)))
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt (0 + zxpLayerDomArity cells)
      { sourceArity := zxpLayerDomArity ([] : List ZxpCell) + zxpLayerDomArity cells
        layers := [zxpCatCells [] cells] } rfl,
    zxpPadDiagramIdentityAt (0 + zxpLayerDomArity cells)
      { sourceArity := zxpLayerDomArity ([] : List ZxpCell) + zxpLayerDomArity cells
        layers := [zxpCatCells [] (zxpWireCells (zxpLayerDomArity cells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity ([] : List ZxpCell))) cells] }
      rfl] at hStep
  have hConv : ZxeConv
      { sourceArity := 0 + zxpLayerDomArity cells
        layers := [zxpWireCells (zxpLayerDomArity cells), cells] }
      { sourceArity := 0 + zxpLayerDomArity cells, layers := [cells] } :=
    ZxeConv.symm (ZxeConv.step hStep)
  rw [Nat.zero_add (zxpLayerDomArity cells)] at hConv
  exact hConv

/-- ABSORPTION (trivial cell, trailing): a full wire layer after any layer strips —
one `splitLayer` read backwards on the other side. -/
theorem zxeStripTrailingWireLayer (cells : List ZxpCell) :
    ZxeConv
      { sourceArity := zxpLayerDomArity cells
        layers := [cells, zxpWireCells (zxpLayerCodArity cells)] }
      { sourceArity := zxpLayerDomArity cells, layers := [cells] } := by
  have hStep := ZxeStep.pad (zxpLayerDomArity cells + 0) 0 0 [] []
    (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer cells [])))
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt (zxpLayerDomArity cells + 0)
      { sourceArity := zxpLayerDomArity cells + zxpLayerDomArity ([] : List ZxpCell)
        layers := [zxpCatCells cells []] } rfl,
    zxpPadDiagramIdentityAt (zxpLayerDomArity cells + 0)
      { sourceArity := zxpLayerDomArity cells + zxpLayerDomArity ([] : List ZxpCell)
        layers := [zxpCatCells cells
            (zxpWireCells (zxpLayerDomArity ([] : List ZxpCell))),
          zxpCatCells (zxpWireCells (zxpLayerCodArity cells)) []] } rfl] at hStep
  have hConv : ZxeConv
      { sourceArity := zxpLayerDomArity cells + 0
        layers := [zxpCatCells cells [],
          zxpCatCells (zxpWireCells (zxpLayerCodArity cells)) []] }
      { sourceArity := zxpLayerDomArity cells + 0
        layers := [zxpCatCells cells []] } :=
    ZxeConv.symm (ZxeConv.step hStep)
  rw [zxpCatCellsNilRight cells, zxpCatCellsNilRight
    (zxpWireCells (zxpLayerCodArity cells))] at hConv
  exact hConv

/-- THE CONDITIONAL DECISION COROLLARY: under the completeness statement, `ZxeConv`
convertibility of well-formed boundary-matched diagrams IS the kernel span decision —
the full phase-free ZX word problem, awaiting the absorption induction. -/
theorem zxeDecisionUnderCompleteness (hCompleteness : zxeCompletenessStatement)
    (firstDiagram secondDiagram : ZxpDiagram)
    (hFirstWF : ZxpDiagramWF firstDiagram) (hSecondWF : ZxpDiagramWF secondDiagram)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram) :
    Iff (ZxeConv firstDiagram secondDiagram)
      (zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
        = true) := by
  refine Iff.intro ?_ ?_
  · intro hConv
    exact zxeConvSpanEqB hConv
  · intro hSpan
    refine hCompleteness firstDiagram secondDiagram hFirstWF hSecondWF hSourceEq
      hCodEq ?_
    exact zxpRelEquivOfSpanEqB
      (zxpDiagramDenoteWidth firstDiagram hFirstWF)
      (zxpAllWidthCast (by rw [hSourceEq, hCodEq])
        (zxpDiagramDenoteWidth secondDiagram hSecondWF))
      hSpan

/-- NEGATIVE CONTROL: the refutation instrument survives the exchange extension —
span-distinct diagrams stay non-convertible in `ZxeConv` (the seed's big-arity
colour pair). -/
theorem zxeBigColourNotConv : Not (ZxeConv zxrZPentaDiagram zxrXPentaDiagram) :=
  fun hConv =>
    Bool.noConfusion ((zxeConvSpanEqB hConv).symm.trans zxrBigColourSpanDistinct)

/-! ## Stage E — the honest marker ledger -/

/-- MARKER: the right-first exchange move family is shipped with structural all-arity
soundness (`zxeExchangeBundle`) and fires as a conversion (`zxeExchangeConv`); the
ladder's walled statement shape holds over `ZxeConv`
(`zxeRightFirstExchangeHolds`). -/
def zxeHasExchangeMove : Bool := true

/-- MARKER: general-k parallel fusion is shipped over `ZxeConv` — all shared-wire
counts, both colours, all boundary arities (`zxeParallelFusionZ` /
`zxeParallelFusionX`), with the k = 4 and k = 5 fires and the independent kernel span
cross-check.  Over `ZxrConv` the ladder's `zxnLadderGeneralKWireFusionLanded` stays
byte-intact FALSE — the delta is exactly exchange admissibility. -/
def zxeGeneralKFusionLanded : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
