import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfSchema

/-! # LinearAlgebra/BialgebraBoundaryLedger — the bialgebra/Hopf boundary ledger
    (WP-PROP-4)

A single machine-checked ledger over the two committed decided/gated
linear-relation substrates:

  * the F2 phase-free ZX span kit
    (`FX1Poly/Polygraph/Omega/ZXPhaseFree/SpiderRelationSeed.lean`):
    `zxpSpanEqB` (two-sided span decision), `ZxpConv` (the padded congruence),
    and the refutation bridge `zxpConvSpanEqB` (convertibility forces the
    decision `true`, so a kernel `false` refutes convertibility);
  * the IH_Q (interacting-Hopf over the rationals) substrate
    (`InteractingHopfSeed`/`Whisker`/`Schema`): `ihqSpanEqB`, the schema
    congruence `IhzConv`, and its refutation bridge `ihzConvSpanEqB`, with the
    embedding `IhzConv.ofSeedConv` from the row-level `IhsConv`.

The ledger records POSITIVE fires (what fuses / holds) and NEGATIVE
refutations (what does not) at the bialgebra/Hopf boundary, each tagged to its
boundary question.  It is deliberately fire-heavy and proof-light: every fire
is either a kernel `rfl` on the executable span decision, a committed gate
(`ihsRowSpanGate`), or a one-line congruence embedding.

Colour dictionary: ZX-Z = IH-black = COPY comonoid/monoid; ZX-X = IH-white =
ADD/parity monoid/comonoid.  "Same-colour" = the two legs of a would-be law
share a colour (Frobenius / special); "cross-colour" = the two interacting
structures (bialgebra / Hopf).

THE SUMMARY MATRIX (rows = laws, columns = {F2 same-colour, F2 cross-colour,
Q same-colour, Q cross-colour}; entries HOLDS(cite) / FAILS(pin) /
OUT-OF-FRAGMENT):

| law         | F2 same-colour        | F2 cross-colour     | Q same-colour           | Q cross-colour        |
|-------------|-----------------------|---------------------|-------------------------|-----------------------|
| special     | HOLDS (specialZ/X)    | N/A (same-colour)   | HOLDS (white/blackSpec) | N/A (same-colour)     |
| Frobenius   | HOLDS (frobeniusZ/X)  | FAILS (pin, L2)     | HOLDS (white/blackFrob) | FAILS (pin, L2)       |
| bialgebra   | N/A (cross-colour)    | HOLDS (bialgSquare) | N/A (cross-colour)      | HOLDS (bimonoid)      |
| Hopf        | HOLDS antipode = id   | (= cross-colour)    | FAILS antipode = id;    | HOLDS antipode = -1   |
|             | (zxpHopf, L3)         |                     | HOLDS antipode = -1(L3) |                       |
| cancel      | OUT-OF-FRAGMENT       | OUT-OF-FRAGMENT     | HOLDS k != 0; FAILS     | (scalar law, not      |
|             | (no scalar cell)      | (no scalar cell)    | k = 0 (L5)              | colour-indexed)       |

The NON-COMMUTATIVE wall (free Hopf algebras, undecidability frontier) is OUT
of BOTH fragments — see `wblNoncommutativeWallStatement` (owner false) and the
committed bicommutative-bimonoid decision it cites.

Sources: Bonchi-Sobocinski-Zanasi, Interacting Hopf Algebras (JPAA 2017,
arXiv:1403.7048), Def 6.1 / Rem 3.4 (antipode = scalar -1) / Thm 6.4
(IH_Q = LinRel_Q); Kissinger arXiv:2204.14038 Thm 3.4 (phase-free ZX
completeness); Bergman, The diamond lemma for ring theory (Adv. Math. 1978) and
the undecidability of the word problem for general (non-commutative) algebras
(Bergman-style; free Hopf-algebra word problem).

Every declaration is zero-axiom (no `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`); the audit twin re-checks per declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open FX1Poly.Polygraph.Omega.ZXPhaseFree

namespace FX1Poly.ComputerAlgebra

/-! ## L1 — SPECIAL vs NON-SPECIAL: `comult ; mult = id` holds in BOTH calculi.

The special law (a comultiplication followed by the same-colour multiplication
collapses to the identity wire) is a genuine axiom of BOTH decided calculi.
Over F2 it is `specialZ`/`specialX` (Kissinger's spider fusion, degree-1
instance); over Q it is `whiteSpecial`/`blackSpecial` (BSZ Def 6.1 I7/I8, new
in the interacting presentation). -/

/-- L1 · F2 · Z: the Z (copy) special law `delta_Z ; mu_Z = id` fires. -/
theorem wblSpecialF2ZFires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.specialZ))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.specialZ)) = true := rfl

/-- L1 · F2 · X: the X (parity) special law `delta_X ; mu_X = id` fires. -/
theorem wblSpecialF2XFires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.specialX))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.specialX)) = true := rfl

/-- L1 · F2 · Z: the special law as one step in the ZX congruence. -/
theorem wblSpecialF2ZConv :
    ZxpConv (zxpRowLhs ZxpRowTag.specialZ) (zxpRowRhs ZxpRowTag.specialZ) :=
  zxpRowConv ZxpRowTag.specialZ

/-- L1 · Q · white: `coadd ; add = id` (BSZ I7) fires the span decision. -/
theorem wblSpecialQWhiteFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.whiteSpecial))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.whiteSpecial)) = true :=
  ihsRowSpanGate IhsRowTag.whiteSpecial

/-- L1 · Q · black: `copy ; cocopy = id` (BSZ I8) fires the span decision. -/
theorem wblSpecialQBlackFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.blackSpecial))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.blackSpecial)) = true :=
  ihsRowSpanGate IhsRowTag.blackSpecial

/-- L1 · Q · white: the special law as one step in the schema congruence. -/
theorem wblSpecialQWhiteConv :
    IhzConv (ihsRowLhs IhsRowTag.whiteSpecial) (ihsRowRhs IhsRowTag.whiteSpecial) :=
  ihzConvOfSeedConv (IhsConv.row IhsRowTag.whiteSpecial)

/-! ## L2 — BIALGEBRA vs FROBENIUS: same-colour is Frobenius, cross-colour is
bialgebra; the CROSS-colour Frobenius law FAILS.

Same-colour pairs (both legs Z, or both white) satisfy the Frobenius law; the
two interacting colours satisfy the bialgebra square.  But swapping the
multiplication of a Frobenius law to the OTHER colour breaks it: the
would-be cross-colour Frobenius equation is refuted by the span decision in
BOTH calculi, and hence is not convertible. -/

/-- L2 · F2 · same-colour Frobenius (Z) HOLDS. -/
theorem wblFrobeniusF2SameColourFires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.frobeniusZLeft))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.frobeniusZLeft)) = true := rfl

/-- L2 · Q · same-colour Frobenius (white) HOLDS. -/
theorem wblFrobeniusQSameColourFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.whiteFrobeniusLeft))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.whiteFrobeniusLeft)) = true :=
  ihsRowSpanGate IhsRowTag.whiteFrobeniusLeft

/-- L2 · F2 · cross-colour bialgebra square (A8) HOLDS. -/
theorem wblBialgebraF2CrossColourFires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.bialgSquare))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.bialgSquare)) = true := rfl

/-- L2 · Q · cross-colour bialgebra square (BSZ A8) HOLDS. -/
theorem wblBialgebraQCrossColourFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.bimonoid))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.bimonoid)) = true :=
  ihsRowSpanGate IhsRowTag.bimonoid

/-- L2 · F2 · cross-colour Frobenius LHS: `(delta_Z (x) id) ; (id (x) mu_X)` —
the committed `frobeniusZLeft` LHS with its multiplication recoloured to X. -/
def wblZxCrossColourFrobeniusLhs : ZxpDiagram :=
  { sourceArity := 2
    layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] }

/-- L2 · F2 · cross-colour Frobenius RHS: `mu_X ; delta_Z`. -/
def wblZxCrossColourFrobeniusRhs : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 2]] }

/-- L2 · F2 · NEGATIVE: the cross-colour Frobenius law FAILS — both sides are
well-formed on matching boundaries, yet the span decision fires `false`. -/
theorem wblZxCrossColourFrobeniusFails :
    zxpSpanEqB (zxpDiagramDenote wblZxCrossColourFrobeniusLhs)
      (zxpDiagramDenote wblZxCrossColourFrobeniusRhs) = false := rfl

/-- L2 · F2 · NEGATIVE (congruence): the cross-colour Frobenius sides are NOT
convertible (via the refutation bridge). -/
theorem wblZxCrossColourFrobeniusNotConv :
    Not (ZxpConv wblZxCrossColourFrobeniusLhs wblZxCrossColourFrobeniusRhs) :=
  fun hConv =>
    Bool.noConfusion ((zxpConvSpanEqB hConv).symm.trans wblZxCrossColourFrobeniusFails)

/-- L2 · Q · cross-colour Frobenius LHS: `(coadd (x) id) ; (id (x) cocopy)` —
the committed `whiteFrobeniusLeft` LHS with its multiplication recoloured
black. -/
def wblIhCrossColourFrobeniusLhs : IhsDiagram :=
  { sourceArity := 2
    layers := [[IhsCell.whiteComult, IhsCell.wire], [IhsCell.wire, IhsCell.blackMult]] }

/-- L2 · Q · cross-colour Frobenius RHS: `cocopy ; coadd`. -/
def wblIhCrossColourFrobeniusRhs : IhsDiagram :=
  { sourceArity := 2, layers := [[IhsCell.blackMult], [IhsCell.whiteComult]] }

set_option maxHeartbeats 4000000 in
/-- L2 · Q · NEGATIVE: the cross-colour Frobenius law FAILS over the rationals —
the span decision fires `false`. -/
theorem wblIhCrossColourFrobeniusFails :
    ihqSpanEqB (ihsDiagramDenote wblIhCrossColourFrobeniusLhs)
      (ihsDiagramDenote wblIhCrossColourFrobeniusRhs) = false := rfl

/-- L2 · Q · NEGATIVE (congruence): the cross-colour Frobenius sides are NOT
`IhzConv`-related (via the refutation bridge). -/
theorem wblIhCrossColourFrobeniusNotConv :
    Not (IhzConv wblIhCrossColourFrobeniusLhs wblIhCrossColourFrobeniusRhs) :=
  fun hConv =>
    Bool.noConfusion ((ihzConvSpanEqB hConv).symm.trans wblIhCrossColourFrobeniusFails)

/-! ## L3 — THE HOPF LAW boundary: F2 antipode is the identity; over Q the
antipode is scalar -1 and the Hopf law with the IDENTITY antipode FAILS.

Over F2 the phase-free Hopf equation `copy ; add = discard ; prepare` holds
with NO antipode box (the antipode is the identity — BSZ Rem 3.4, D3, trivial
over Z2).  Over Q, the same identity-antipode composite `copy ; add` does NOT
equal `discard ; zero`; the Hopf law is recovered ONLY with the scalar-(-1)
antipode on the middle wire. -/

/-- L3 · F2: the Hopf composite `delta_Z ; mu_X = eps_Z ; eta_X`
(copy-then-add = discard-then-prepare) fires — the antipode is the identity. -/
theorem wblHopfF2AntipodeIdentityFires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.hopf))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.hopf)) = true := rfl

/-- L3 · F2: the Hopf law as one step in the ZX congruence. -/
theorem wblHopfF2Conv :
    ZxpConv (zxpRowLhs ZxpRowTag.hopf) (zxpRowRhs ZxpRowTag.hopf) :=
  zxpRowConv ZxpRowTag.hopf

/-- L3 · Q · the target of the Hopf law: `discard ; zero` (1 -> 1). -/
def wblIhDiscardZero : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.blackCounit], [IhsCell.whiteUnit]] }

/-- L3 · Q · the Hopf composite with the IDENTITY in place of the antipode:
`copy ; add` (no scalar box). -/
def wblIhHopfIdentityAntipodeLhs : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.blackComult], [IhsCell.whiteMult]] }

set_option maxHeartbeats 4000000 in
/-- L3 · Q · NEGATIVE: with the identity antipode the Hopf law FAILS over Q —
`copy ; add` does not span-equal `discard ; zero`. -/
theorem wblHopfQIdentityAntipodeFails :
    ihqSpanEqB (ihsDiagramDenote wblIhHopfIdentityAntipodeLhs)
      (ihsDiagramDenote wblIhDiscardZero) = false := rfl

/-- L3 · Q · NEGATIVE (congruence): with the identity antipode the two sides are
NOT `IhzConv`-related (via the refutation bridge). -/
theorem wblHopfQIdentityAntipodeNotConv :
    Not (IhzConv wblIhHopfIdentityAntipodeLhs wblIhDiscardZero) :=
  fun hConv =>
    Bool.noConfusion ((ihzConvSpanEqB hConv).symm.trans wblHopfQIdentityAntipodeFails)

/-- L3 · Q · the Hopf composite with the CORRECT scalar-(-1) antipode on the
lower leg: `copy ; (id (x) antipode) ; add` (BSZ Rem 3.4). -/
def wblIhHopfScalarAntipodeLhs : IhsDiagram :=
  { sourceArity := 1
    layers := [[IhsCell.blackComult],
      [IhsCell.wire, IhsCell.scalarBox ihsAntipodeScalar],
      [IhsCell.whiteMult]] }

set_option maxHeartbeats 4000000 in
/-- L3 · Q · POSITIVE: with the scalar-(-1) antipode the Hopf law HOLDS over Q —
`copy ; (id (x) -1) ; add` span-equals `discard ; zero`.  Together with
`wblHopfQIdentityAntipodeFails` this pins the sharp boundary: the antipode over
Q is exactly the scalar -1, never the identity. -/
theorem wblHopfQScalarAntipodeFires :
    ihqSpanEqB (ihsDiagramDenote wblIhHopfScalarAntipodeLhs)
      (ihsDiagramDenote wblIhDiscardZero) = true := rfl

/-! ## L4 — COMMUTATIVITY boundary and the NON-COMMUTATIVE wall.

Both calculi are bicommutative: the ZX rows `xMonoidComm`/`zMonoidComm`
(and their comonoid cocommutativity mirrors) and the IH_Q rows
`addComm`/`copyCocomm` (and mirrors) are all committed axioms.  The
NON-commutative wall — free (non-commutative) Hopf algebras and the
undecidability frontier — is OUT of both fragments: neither the F2 phase-free
ZX syntax nor the IH_Q self-dual signature carries a non-commutative
multiplication, and both decision procedures rest on commutative F2/Q linear
algebra (Gaussian echelonization over a field).

`wblNoncommutativeWallStatement` names what a non-commutative extension would
need: it is the conjunction of the two committed COMMUTATIVE completeness
statements (`zxpCompletenessStatement` and `ihsCompletenessStatement`, both
owner-false upstream) — the commutative ceiling.  A non-commutative refinement
lies STRICTLY beyond this ceiling: dropping the commutativity rows turns the
span/echelon decision procedure invalid (row spaces no longer classify the
relation), and the word problem for the free non-commutative structure is the
undecidability frontier (Bergman, diamond lemma / word-problem literature; the
free Hopf-algebra word problem).  Cf. the committed WP-PROP-2
bicommutative-bimonoid decision and its star-retraction census in
`FX1Poly/Polygraph/Omega/WalkingBunchedBimonoidNormalFormCensus.lean`
(`bunchedBimonoidStarStatement`) and
`.../WalkingBunchedBimonoidStarAssembly.lean`
(`fxBunchedBimonoid_correctedWellTypedStarStillOpen : Bool := false`) — cited,
not touched.

OWNER FALSE — NOT PROVEN, NOT COMMISSIONED (see `wblNoncommutativeWallIsProven`). -/

/-- L4 · F2: bicommutativity witness — the X monoid commutativity row fires. -/
theorem wblCommutativityF2Fires :
    zxpSpanEqB (zxpDiagramDenote (zxpRowLhs ZxpRowTag.xMonoidComm))
      (zxpDiagramDenote (zxpRowRhs ZxpRowTag.xMonoidComm)) = true := rfl

/-- L4 · Q: bicommutativity witness — the additive commutativity row fires. -/
theorem wblCommutativityQFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.addComm))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.addComm)) = true :=
  ihsRowSpanGate IhsRowTag.addComm

/-- L4 · the non-commutative wall statement: the commutative completeness
ceiling of BOTH calculi (span-equality decides convertibility).  A
non-commutative extension lies strictly beyond it. -/
def wblNoncommutativeWallStatement : Prop :=
  zxpCompletenessStatement /\ ihsCompletenessStatement

/-- OWNER FALSE — `wblNoncommutativeWallStatement` is NOT proven (both conjuncts
are owner-false upstream, and the non-commutative frontier is undecidable). -/
def wblNoncommutativeWallIsProven : Bool := false

/-! ## L5 — SCALAR boundary (Q only): the k = 0 cancel failure is the ledger's
sharpest boundary fire.

The cancel law `l ; l-mirror = id` (BSZ I1 forward-cancel) holds for every
NONZERO scalar `l` (fired committed at l = 2, and freshly at l = 4).  At l = 0
it FAILS decisively: the composite `scalar 0 ; mirror 0` is the graph of
`{(x, 0)}` post-composed with `{(0, y)}`, i.e. the TOTAL relation on Q^1 x Q^1
(rank 2, all of Q^2), not the diagonal wire (rank 1).  This is the k = 0
route-note finding, re-pinned here as the span inequality. -/

/-- L5 · Q · the k = 0 forward-cancel composite `scalar 0 ; mirror 0` (1 -> 1). -/
def wblIhZeroScalarCancel : IhsDiagram :=
  { sourceArity := 1
    layers := [[IhsCell.scalarBox qnfZero], [IhsCell.scalarBoxMirror qnfZero]] }

/-- L5 · Q · the identity wire (1 -> 1), the intended cancel target. -/
def wblIhWire : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.wire]] }

set_option maxHeartbeats 4000000 in
/-- L5 · Q · NEGATIVE (the sharpest boundary fire): at k = 0 the cancel law
FAILS — `scalar 0 ; mirror 0` is the TOTAL relation, not the wire, so the span
decision fires `false`. -/
theorem wblZeroScalarCancelFails :
    ihqSpanEqB (ihsDiagramDenote wblIhZeroScalarCancel)
      (ihsDiagramDenote wblIhWire) = false := rfl

/-- L5 · Q · NEGATIVE (congruence): the k = 0 cancel composite is NOT
`IhzConv`-related to the wire (via the refutation bridge). -/
theorem wblZeroScalarCancelNotConv :
    Not (IhzConv wblIhZeroScalarCancel wblIhWire) :=
  fun hConv =>
    Bool.noConfusion ((ihzConvSpanEqB hConv).symm.trans wblZeroScalarCancelFails)

/-- L5 · Q · CONTRAST: at the nonzero scalar l = 2 the cancel law HOLDS
(committed `forwardCancel` row) — the boundary is exactly `l != 0`. -/
theorem wblNonzeroScalarCancelFires :
    ihqSpanEqB (ihsDiagramDenote (ihsRowLhs IhsRowTag.forwardCancel))
      (ihsDiagramDenote (ihsRowRhs IhsRowTag.forwardCancel)) = true :=
  ihsRowSpanGate IhsRowTag.forwardCancel

/-! ## Marker -/

/-- The bialgebra/Hopf boundary ledger is shipped: L1 (special holds both
calculi), L2 (Frobenius/bialgebra split + cross-colour Frobenius refuted),
L3 (Hopf antipode = id over F2, = -1 over Q, identity refuted), L4
(bicommutative; non-commutative wall owner-false), L5 (scalar cancel holds
k != 0, refuted at k = 0). -/
def wblHasBoundaryLedger : Bool := true

end FX1Poly.ComputerAlgebra
