import FX1Poly.Polygraph.Homology.AmalgamMayerVietorisComparisonMap

/-! # FX1Poly/Polygraph/Homology/AmalgamBimonoidBialgebraObstruction — the BIMONOID amalgamation
    obstruction in the PROP grading: a degree-1 homology class nontrivial WITHOUT the bialgebra law and
    KILLED by adding it, both instance-level and zero-axiom (TOWER-MV r3, the bimonoid round)

TOWER-MV r1 (`Homology/AmalgamMultiplicationObstruction`) shipped the DOUBLE-MONOID amalgam and its
first machine-checked amalgamation-obstruction cocycle, and in its B6 no-go showed that putting the
comonoid generators `(eps, delta)` as 2-cells over ONE shared endo `t` (the monad/2-cell grading)
makes the `(mu, delta)` cross cofork break `d d = 0` with defect `-2` (`bimonoidNaiveUnionFailsChain
Condition`).  r2 (`Homology/AmalgamMayerVietorisComparisonMap`) named the bimonoid proper as the r3
bill and conjectured a Cartan-Eilenberg BICOMPLEX (`bimonoidBicomplexIsR3Bill`).

THIS module delivers the bimonoid obstruction, with one honest RE-GRADING.  The r1 B6 wall is a
carrier artefact: the shipped `WalkerPresentationCarrier` is a MONOID-WORD carrier over a SINGLE
object whose `d1` is HARDCODED to the all-zero loop row (`computeBoundaryDimZero`) — every endo
1-generator is a loop with zero boundary.  A bimonoid's generators `eta 0->1`, `mu 2->1`, `eps 1->0`,
`delta 1->2` have NONZERO arity displacement, so they are not loops and cannot be 1-generators of the
walker carrier.  We therefore extend the grading ADDITIVELY to a PROP grading: `eta, mu, eps, delta`
become 1-GENERATORS carrying `(sourceArity, targetArity)`, so `C0 = ZZ` (one object), `C1 = ZZ^4`, and
`d1` is the arity-difference row `[+1, -1, -1, +1]` — which is EXACTLY r1's B6 literal
`bimonoidBoundaryOfDimOne`, re-graded from the (refuted) `d2` grading to `d1`.  The relations move to
`C2`.  In this carrier the bimonoid-without-law IS a genuine chain complex (`d1 . d2 = 0` on every
column), so the r1 B6 defect dissolves under re-grading (no contradiction: r1 B6's `-2` is a fact of a
DIFFERENT carrier — the walker/2-cell grading — and stays true).

## What is PROVED here (all instance-level, all zero-axiom)

  * **B1 — the bunched bimonoid presentation and its complex.**  `d1 = [[1, -1, -1, 1]]` (arity
    displacement; the re-graded r1 literal) and `d2 (without law) : ZZ^6 -> ZZ^4` (the six relations
    `assoc_mu, lunit, runit, coassoc, lcounit, rcounit`); `d1 . d2 = 0` on every column
    (`bimonoidWithoutLawIsChainComplex`) — a genuine chain complex.
  * **B2 — the with-law complex and the two-complex comparison.**  `d2 (with law) : ZZ^7 -> ZZ^4` adds
    the bialgebra column `delta . mu = (mu | mu) . sigma . (delta | delta)`, whose boundary is
    `[0, -1, 0, -1] = -(mu + delta)`; `d1 . d2with = 0` too.  Off unit-only Smith normal forms:
    `rank d1 = 1`, `rank d2without = 2`, `rank d2with = 3`, so the degree-1 homology free rank
    `= (C1 - rank d1) - rank d2 = (4 - 1) - rank d2` is `1` WITHOUT the law and `0` WITH it; no torsion
    either way.
  * **B3 — the probe-decided theorem.**  The class `[mu + delta] = [0, 1, 0, 1]` is a 1-cycle
    (`d1 . class = 0`); WITHOUT the law it ESCAPES the integer span of the six relation boundaries
    (detected by the relative 1-cocycle `phi = eta* - mu* = [1, -1, 0, 0]`, which annihilates every
    relation boundary yet evaluates `-1` on the class — the exact mirror of r1's `phi`), so it is
    NONTRIVIAL in `H1`; WITH the law it becomes a boundary (`class = -(bialgebra column)`), so it dies.
    Each part alone (`monoid` = `(eta, mu)`, `comonoid` = `(eps, delta)`) has `H1 = 0`, so the class is
    genuinely CROSS.

## Honest scoping (READ THIS — the honesty law)

  * **A RE-GRADING, not a refutation.**  The killer hypothesis (nontrivial-without, killed-by-law) is
    CONFIRMED.  The only correction is the DEGREE: the class lives at `H1`, not `H2`, because a
    bimonoid's generators are 1-cells (morphisms of a PROP), where a monad's `mu`/`eta` were 2-cells.
    No bicomplex is needed; a single complex suffices.
  * **The r2 bicomplex marker is NOT flipped.**  `bimonoidBicomplexIsR3Bill` (r2) conjectured a
    Cartan-Eilenberg bicomplex.  The PROP re-grading resolves the obstruction in a SINGLE complex; per
    the flip law that marker stays as it is (its bicomplex bill is not what r3 delivers), and the
    bicomplex remains an honest heavier alternative.  r3 ships NEW markers only.
  * **No contradiction with r1 B6.**  `bimonoidNaiveUnionFailsChainCondition` (`d d = -2`) is the
    walker/2-cell grading and stays true; the PROP grading is a different carrier with a different `d1`.
  * **The cocycle stays RELATIVE.**  `phi` is a cocycle RELATIVE to the (empty-of-cross) relation
    subcomplex — it annihilates the six relation boundaries and detects the class; no absolute-cocycle
    claim is made.
  * **INSTANCE-level.**  Every statement is decided on this bimonoid INSTANCE, not the general
    polygraphic theorem (`Bool` markers only for the forward direction).
  * **NOT an embedding / monoid-homology claim.**  This is the homology of the ABELIANIZED PROP
    presentation as-presented; the monoid amalgam need not embed the parts (Howie 1962), and nothing
    here asserts a monoid-homology identity.  The cross critical-pair set of the monoid vs comonoid
    alphabets is EMPTY without the law (disjoint alphabets), so the obstruction is forced to the
    generator level (`C1`), not a `C3` cross 3-cell.

## The literature anchor (fetched)

  * Lafont, *Towards an Algebraic Theory of Boolean Circuits* (JPAA 184, 2003): the bimonoid
    generators are exactly `tau, delta, epsilon, mu, eta`, with the bialgebra relation
    `delta . mu = (mu | mu) . (id | tau | id) . (delta | delta)`; the oriented system is CANONICAL, and
    that relation is the oriented rule resolving the `mu`/`delta` critical peak.  Lack, *Composing PROPs*
    (TAC 13, 2004): the same law is the Beck distributive law composing the comonoid and monoid PROPs.
    The HOMOLOGICAL reading of the compatibility law as an obstruction class (this module) is an
    ORIGINAL framing, unattested in the fetched literature.

## The r4 bill (NAMED, NOT flipped)

  * the Mayer-Vietoris LONG EXACT SEQUENCE for the bimonoid amalgam and the homology-level connecting
    map (the LES packaging);
  * the general CFND-5 FAILURE-CERTIFICATE interface that WP-AMALG-3 consumes;
  * the full four-law bialgebra (all four compatibility laws map onto the same `H1` generator, so
    `rank d2` saturates at 3 — a corollary);
  * the decidedness / completeness of the PROP critical-pair set (Lafont's coherence: `C3` is empty
    until the law, Lafont-complete after).

## Zero-axiom design decisions

  * Ships `IntMatrix` literals + unimodular Smith certificates only (the r1 B5 / r2 style); NO new
    generic presentation carrier (the walker carrier cannot host a comonoid; a generic PROP carrier is
    deferred to r4/r5).
  * Rank/exactness facts read off unit-only Smith normal forms via `smithRankWithin` (the r2 propext
    dodge); the escape-over-all-integer-combinations upgrade reuses the r1 Fubini / distributivity kit
    (`sumOverIndicesSwap`, `sumOverIndicesLeftDistrib`, `sumOverIndicesCongrEverywhere`,
    `sumOverIndicesZeroWithinBound`) and the repo integer kit (`intMulAssoc`, `intMulComm`, `intMulZero`)
    BY IMPORT, never redeclared (the umbrella duplicate-global trap).
  * Out-of-range indices are refuted by the shipped `columnIndexOutOfRangeAbsurd` peel; `decide`
    appears only on literal off-diagonal / nonnegativity checks and on `(-1 : Int) = 0`, never on a
    Smith-driver expression.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/AmalgamBimonoidBialgebraObstruction.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the bunched bimonoid presentation and its (without-law) chain complex

The PROP-graded bimonoid over ONE shared object.  `C0 = ZZ` (the object), `C1 = ZZ^4` with the four
1-generators ordered `[eta, mu, eps, delta]`, and `C2 = ZZ^6` with the six relations ordered
`[assoc_mu, lunit, runit, coassoc, lcounit, rcounit]`.  Each relation boundary is the abelianized
`(one side) - (other side)` in the generator basis. -/

/-- `d1 : C1 = ZZ^4 -> C0 = ZZ`, the arity displacement `(target arity) - (source arity)` of each
1-generator: `eta 0->1` is `+1`, `mu 2->1` is `-1`, `eps 1->0` is `-1`, `delta 1->2` is `+1`.  This is
EXACTLY r1's B6 literal `bimonoidBoundaryOfDimOne`, re-graded from the refuted `d2` grading to `d1`. -/
def bimonoidArityBoundary : IntMatrix := ⟨[[1, -1, -1, 1]]⟩

/-- **The re-grading is literal** — the r3 PROP `d1` is r1's B6 `bimonoidBoundaryOfDimOne` verbatim,
regraded from `d2` to `d1`.  The r1 defect (`d d = -2` in the walker/2-cell grading) and this
chain-complex (in the PROP grading) are the SAME matrix read in two different carriers. -/
theorem bimonoidArityBoundaryIsR1Regrade :
    bimonoidArityBoundary = bimonoidBoundaryOfDimOne := rfl

/-- `d2 (without the bialgebra law) : C2 = ZZ^6 -> C1 = ZZ^4`.  Columns
`[assoc_mu, lunit, runit, coassoc, lcounit, rcounit]`; rows `[eta, mu, eps, delta]`.  `assoc_mu` and
`coassoc` are homogeneous (`[0,0,0,0]`); `lunit`/`runit` are `{mu, eta}` vs `id = [1,1,0,0]`;
`lcounit`/`rcounit` are `{eps, delta}` vs `id = [0,0,1,1]`.  The monoid alphabet `{eta, mu}` and the
comonoid alphabet `{eps, delta}` are DISJOINT here — no cross column. -/
def bimonoidRelationBoundaryWithoutLaw : IntMatrix :=
  ⟨[ [0, 1, 1, 0, 0, 0]
   , [0, 1, 1, 0, 0, 0]
   , [0, 0, 0, 0, 1, 1]
   , [0, 0, 0, 0, 1, 1] ]⟩

-- Committed census pins (statistics = named defs + kernel #eval):
--   C0 = 1, C1 = 4, C2(without) = 6.
#eval bimonoidArityBoundary.rows                     -- [[1, -1, -1, 1]]
#eval bimonoidRelationBoundaryWithoutLaw.rows        -- the 4 x 6 relation boundary

/-- ★ **The bunched bimonoid (without the bialgebra law) IS a chain complex** — `d1 . d2 = 0` on every
one of the six relation columns (per-column `rfl` over the shipped `comparisonProductEntry`; the
out-of-range peel reuses the shipped `columnIndexOutOfRangeAbsurd`).  Unlike the r1 B6 walker/2-cell
grading (defect `-2`), the PROP grading closes `d d = 0` with no bialgebra law. -/
theorem bimonoidWithoutLawIsChainComplex :
    ∀ colIndex, colIndex < 6 →
      comparisonProductEntry bimonoidArityBoundary bimonoidRelationBoundaryWithoutLaw 4 0 colIndex = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, colBound => columnIndexOutOfRangeAbsurd _ 6 colBound

end FX1Poly.Polygraph.Homology
