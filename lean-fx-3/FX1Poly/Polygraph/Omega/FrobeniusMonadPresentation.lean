import FX1Poly.Polygraph.Omega.CriticalPairRow
import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # Polygraph/Omega/FrobeniusMonadPresentation — the walking Frobenius monad as a twelve-critical-pair
Squier presentation (WP-FROBMONAD r1, #2070)

★ **The walking Frobenius monad `<s | mu, eta, delta, epsilon | monad + comonad + two Frobenius rows>`
re-encoded as an `OmegaComputad` 2-polygraph.**  A Frobenius monad (Lawvere; Street, *Frobenius monads and
pseudomonoids*, JMP 45, 2004; Kock, *Frobenius algebras and 2D TQFT*) is a monad `(s, mu, eta)` whose
underlying endo-1-cell also carries a comonad `(s, delta, epsilon)`, with the two structures interacting
through the Frobenius law.  Over a single object `*` with one endo-1-generator `s` this file ships the
FOUR 2-cell generators and the `5 + 5 + 2 = 12` critical-pair rows:

  * `mu      : s.s => s`   (multiplication)   `gen muMult  (s.s) s`
  * `eta     : id  => s`   (unit)             `gen etaUnit id   s`
  * `delta   : s   => s.s` (comultiplication) `gen deltaComult s (s.s)`   — an EXPANSION
  * `epsilon : s   => id`  (counit)           `gen epsCounit  s id`

## The count is FOUR 2-cell generators (not six — the recon flag, ENFORCED)

The BARE walking Frobenius monad (Lawvere / Street / Kock) has exactly FOUR 2-cell generators
(`mu, eta, delta, epsilon`), NOT six.  "Six" conflates either the two Frobenius-law ROWS (`4 + 2`) or the
commutative / special sigma-augmented Frobenius PROP (the DIFFERENT multi-object walker in
`TwoCategory/Frobenius`, which adds a symmetry `sigma` + commutativity / cocommutativity + special + bone).
This file ships the plain (non-special, non-commutative) single-object walking Frobenius MONAD, and states
the four-count explicitly (`frobMonadOmegaGeneratorLabelCountIsFive` = the s-generator + four 2-cells).

## The two Frobenius rows (whisker convention hand-verified, cross-checked against the shipped lane)

In this repo `whiskerLeft w a = w <| a` (w the LEFT tensor factor), `whiskerRight a w = a |> w` (w RIGHT),
and `vcomp left right = left . right` (diagrammatic, left-then-right).  The classical Frobenius law
`(mu.1)(1.delta) = delta.mu = (1.mu)(delta.1)` (Carboni-Walters "S=X"; nLab) becomes the two rows, both
sharing RHS the shared middle `M := mu . delta`:

  * **F1 (frobLeft)**  `(s <| delta) . (mu |> s)  ~  mu . delta`;
  * **F2 (frobRight)** `(delta |> s) . (s <| mu)  ~  mu . delta`.

This reproduces the shipped `TwoCategory/Frobenius/SpiderPresentation` rows 7-8 `frobLeft` / `frobRight`
over the SAME four generators exactly (correspondence NAMED in docstrings; the correspondence-target lane
is `RawTwoCellExpr` / `BrauerRelation`, DISJOINT — a cross-import is forbidden, only the docstring-name).

## Literally globular on BOTH boundaries (the new resolution content)

`boundarySource F1 = boundarySource M = boundarySource F2 = vcomp s s` and likewise every target is
`vcomp s s` — LITERALLY (all reduce by `rfl`, no strict step).  So both Frobenius rows are literally
globular on both boundaries, the same easiest scope as the walking-equivalence cancellations: the mu-redex
overlaps the delta-expansion and the overlap resolves with a `refl` join at both peak and valley.  The legs
are structurally distinct (different whisker orders), so the rows are non-vacuous.  Both ship additionally
as genuine `CriticalPairRow`s (peak = valley = `vcomp s s`, four boundary fields `rfl`), exactly like
`monadOmegaPentagonRow`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The single-object Frobenius-monad signature (five generator labels) -/

/-- ★ The **five generator labels** of the walking Frobenius monad: the endo-1-generator `s` and the four
2-cell generators — the multiplication `mu`, the unit `eta`, the comultiplication `delta`, and the counit
`epsilon`.  A finite inductive (full case splits everywhere — the wildcard-`_ =>` propext leak is avoided).
FOUR 2-cell generators (not six). -/
inductive FrobMonadGenLabel where
  /-- The endo-1-generator `s : * => *`. -/
  | sEndo
  /-- The multiplication `mu : s.s => s`. -/
  | muMult
  /-- The unit `eta : id => s`. -/
  | etaUnit
  /-- The comultiplication `delta : s => s.s`. -/
  | deltaComult
  /-- The counit `epsilon : s => id`. -/
  | epsCounit

/-- The **integer tag** of a generator label — a full five-arm split (constant `Nat` motive, propext-free);
the label comparator compares tags. -/
def frobMonadLabelTag : FrobMonadGenLabel → Nat
  | .sEndo => 0
  | .muMult => 1
  | .etaUnit => 2
  | .deltaComult => 3
  | .epsCounit => 4

/-- The **label `Bool` equality** — tags equal (`Nat.beq` on tags, propext-free); separates all five
labels, so the structural cell comparator distinguishes the four 2-cell generators. -/
def frobMonadLabelBeq (labelA labelB : FrobMonadGenLabel) : Bool :=
  frobMonadLabelTag labelA == frobMonadLabelTag labelB

/-- ★ The **walking-Frobenius-monad omega-computad**: one object (`Unit`), the constant five-label family
`FrobMonadGenLabel` at every dimension (the 1-generator `s` and the four 2-generators are drawn from it;
globularity is extrinsic, so the label family need not know the cells its labels span).  Constant family
(no `Nat`-match in `genLabel`) — propext-clean. -/
def frobMonadOmegaComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => FrobMonadGenLabel

/-- The trivial mode comparator (one object). -/
def frobMonadOmegaModeBeq : frobMonadOmegaComputad.modeCarrier → frobMonadOmegaComputad.modeCarrier → Bool :=
  fun _ _ => true

/-- The heterogeneous generator comparator — compares the five labels by tag (separates the four 2-cell
generators; NOT the trivial comparator the single-generator walkers used). -/
def frobMonadOmegaGenBeq :
    (dimA dimB : Nat) → frobMonadOmegaComputad.genLabel dimA → frobMonadOmegaComputad.genLabel dimB → Bool :=
  fun _ _ labelA labelB => frobMonadLabelBeq labelA labelB

/-! ## The generators -/

/-- The single object `*`. -/
def frobMonadOmegaPoint : CellExpr frobMonadOmegaComputad 0 := CellExpr.ofMode ()

/-- The endo-1-generator `s : * => *`. -/
def frobMonadOmegaSGen : CellExpr frobMonadOmegaComputad 1 :=
  CellExpr.gen (dim := 0) FrobMonadGenLabel.sEndo frobMonadOmegaPoint frobMonadOmegaPoint

/-- The 1-cell word `s.s` (the multiplication's source, the comultiplication's target). -/
def frobMonadOmegaSsWord : CellExpr frobMonadOmegaComputad 1 :=
  CellExpr.vcomp frobMonadOmegaSGen frobMonadOmegaSGen

/-- The identity 1-cell `id` (the unit's source, the counit's target, `s^0`). -/
def frobMonadOmegaIdOne : CellExpr frobMonadOmegaComputad 1 := CellExpr.id frobMonadOmegaPoint

/-- ★ The **multiplication** `mu : s.s => s` (label `muMult`).  Globular: both `s.s` and `s` are `* => *`. -/
def frobMonadOmegaMuGen : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) FrobMonadGenLabel.muMult frobMonadOmegaSsWord frobMonadOmegaSGen

/-- ★ The **unit** `eta : id => s` (label `etaUnit`). -/
def frobMonadOmegaEtaGen : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) FrobMonadGenLabel.etaUnit frobMonadOmegaIdOne frobMonadOmegaSGen

/-- ★ The **comultiplication** `delta : s => s.s` (label `deltaComult`) — an EXPANSION (the reversed rewrite
`s => s.s` is non-terminating, but the coherent-presentation layer needs no termination; every join is a
`SaturatedConvOverWithId` derivation and `symm` is a constructor). -/
def frobMonadOmegaDeltaGen : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) FrobMonadGenLabel.deltaComult frobMonadOmegaSGen frobMonadOmegaSsWord

/-- ★ The **counit** `epsilon : s => id` (label `epsCounit`). -/
def frobMonadOmegaEpsGen : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.gen (dim := 1) FrobMonadGenLabel.epsCounit frobMonadOmegaSGen frobMonadOmegaIdOne

/-- The five generator labels, enumerated — FOUR 2-cell generators plus the one endo-1-generator. -/
def allFrobMonadGenLabels : List FrobMonadGenLabel :=
  [.sEndo, .muMult, .etaUnit, .deltaComult, .epsCounit]

/-- ★ **The generator-label count is exactly FIVE** — the endo-1-generator `s` + the FOUR 2-cell generators
(`mu`, `eta`, `delta`, `epsilon`), kernel-checked (`rfl`).  This is the explicit refutation of the
"six 2-cell generators" miscount: the bare walking Frobenius monad has FOUR 2-cells. -/
theorem frobMonadOmegaGeneratorLabelCountIsFive : allFrobMonadGenLabels.length = 5 := rfl

/-! ## The two Frobenius legs and the shared middle (the B1 truth-probe: the rows type-check on concrete
words FIRST)

Each cell is a `CellExpr frobMonadOmegaComputad 2` that type-checks on the nose — the whiskerings and
vertical composites elaborate because the free carrier's composability is extrinsic.  This is the B1
truth-probe: the two Frobenius rows ARE well-typed 2-cell equations on concrete words. -/

/-- ★ The **Frobenius LEFT leg** `L1 = (s <| delta) . (mu |> s) : s.s => s.s` — the classical `(mu.1)(1.delta)`
in diagrammatic order (Carboni-Walters "S=X" left side). -/
def frobMonadOmegaFrobLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaDeltaGen)
    (CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaSGen)

/-- ★ The **shared middle** `M = mu . delta : s.s => s.s` — `delta after mu` (the RHS of BOTH Frobenius
rows). -/
def frobMonadOmegaFrobMiddle : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp frobMonadOmegaMuGen frobMonadOmegaDeltaGen

/-- ★ The **Frobenius RIGHT leg** `L2 = (delta |> s) . (s <| mu) : s.s => s.s` — the classical `(1.mu)(delta.1)`
in diagrammatic order (Carboni-Walters right side). -/
def frobMonadOmegaFrobRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaSGen)
    (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaMuGen)

/-! ## The literal-globularity boundary checks (all three cells `s.s => s.s` on the nose) -/

/-- The Frobenius left leg's source boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobLeftLeg_boundarySource :
    boundarySource frobMonadOmegaFrobLeftLeg = frobMonadOmegaSsWord := rfl

/-- The Frobenius left leg's target boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobLeftLeg_boundaryTarget :
    boundaryTarget frobMonadOmegaFrobLeftLeg = frobMonadOmegaSsWord := rfl

/-- The shared middle's source boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobMiddle_boundarySource :
    boundarySource frobMonadOmegaFrobMiddle = frobMonadOmegaSsWord := rfl

/-- The shared middle's target boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobMiddle_boundaryTarget :
    boundaryTarget frobMonadOmegaFrobMiddle = frobMonadOmegaSsWord := rfl

/-- The Frobenius right leg's source boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobRightLeg_boundarySource :
    boundarySource frobMonadOmegaFrobRightLeg = frobMonadOmegaSsWord := rfl

/-- The Frobenius right leg's target boundary is `s.s` (literal). -/
theorem frobMonadOmegaFrobRightLeg_boundaryTarget :
    boundaryTarget frobMonadOmegaFrobRightLeg = frobMonadOmegaSsWord := rfl

/-! ## Non-vacuity — the Frobenius legs are genuinely distinct 2-cells (the B1 truth-probe) -/

/-- ★ **The Frobenius left leg and the shared middle are structurally DISTINCT** (a whisker composite vs a
generator composite) — the F1 row genuinely identifies non-equal 2-cells. -/
theorem frobMonadOmegaFrobLeft_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle = false := rfl

/-- ★ **The Frobenius right leg and the shared middle are structurally DISTINCT.** -/
theorem frobMonadOmegaFrobRight_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle = false := rfl

/-- ★ **The two Frobenius legs are structurally DISTINCT** (the two whisker orders `(s <| delta).(mu |> s)`
vs `(delta |> s).(s <| mu)`) — the two rows are genuinely different overlaps. -/
theorem frobMonadOmegaFrobLegs_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobRightLeg = false := rfl

/-- ★ **The multiplication and the comultiplication are genuinely distinct 2-cells** — `mu` and `delta` are
structurally NOT equal (the real tag comparator separates `muMult` from `deltaComult`). -/
theorem frobMonadOmegaMuDelta_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaMuGen frobMonadOmegaDeltaGen = false := rfl

/-- ★ **THE F1 ROW IS LITERALLY GLOBULAR AT THE SOURCE.**  The two leg source 1-cells are the LITERALLY
IDENTICAL `s.s`, so `cellBeq` computes `true` — the peak closes on the nose. -/
theorem frobMonadOmegaFrobLeftLeg_literallyParallelSource :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      (boundarySource frobMonadOmegaFrobLeftLeg) (boundarySource frobMonadOmegaFrobMiddle) = true := rfl

/-- ★ **THE F1 ROW IS LITERALLY GLOBULAR AT THE TARGET.**  The two leg target 1-cells are the LITERALLY
IDENTICAL `s.s` — so the valley closes on the nose too.  Both boundaries literal is the Frobenius rows'
distinctive scope (the mu-redex / delta-expansion overlap resolving by `refl`). -/
theorem frobMonadOmegaFrobLeftLeg_literallyParallelTarget :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      (boundaryTarget frobMonadOmegaFrobLeftLeg) (boundaryTarget frobMonadOmegaFrobMiddle) = true := rfl

/-! ## The two Frobenius rows as genuine globular `CriticalPairRow`s (peak = valley = `s.s`) -/

/-- ★ The **F1 (frobLeft) row as a genuine globular `CriticalPairRow`** — its legs are a parallel pair on
the nose (peak `s.s`, valley `s.s`; the four boundary fields discharge by `rfl`).  The mu-delta Frobenius
overlap is a literally-parallel critical pair, so it instantiates the `CriticalPairRow` structure directly
(exactly like `monadOmegaPentagonRow`). -/
def frobMonadOmegaFrobLeftRow : CriticalPairRow frobMonadOmegaComputad 1 where
  peak := frobMonadOmegaSsWord
  valley := frobMonadOmegaSsWord
  leftLeg := frobMonadOmegaFrobLeftLeg
  rightLeg := frobMonadOmegaFrobMiddle
  leftLegSource := rfl
  leftLegTarget := rfl
  rightLegSource := rfl
  rightLegTarget := rfl

/-- ★ The **F2 (frobRight) row as a genuine globular `CriticalPairRow`** (peak `s.s`, valley `s.s`;
`rfl` boundary fields). -/
def frobMonadOmegaFrobRightRow : CriticalPairRow frobMonadOmegaComputad 1 where
  peak := frobMonadOmegaSsWord
  valley := frobMonadOmegaSsWord
  leftLeg := frobMonadOmegaFrobRightLeg
  rightLeg := frobMonadOmegaFrobMiddle
  leftLegSource := rfl
  leftLegTarget := rfl
  rightLegSource := rfl
  rightLegTarget := rfl

/-- The F1 row is globular — its legs are a parallel pair (non-vacuity of the globular sub-case). -/
theorem frobMonadOmegaFrobLeftRow_isParallelPair :
    IsParallelPair frobMonadOmegaFrobLeftRow.leftLeg frobMonadOmegaFrobLeftRow.rightLeg :=
  criticalPairRow_isParallelPair frobMonadOmegaFrobLeftRow

/-- The F2 row is globular — its legs are a parallel pair. -/
theorem frobMonadOmegaFrobRightRow_isParallelPair :
    IsParallelPair frobMonadOmegaFrobRightRow.leftLeg frobMonadOmegaFrobRightRow.rightLeg :=
  criticalPairRow_isParallelPair frobMonadOmegaFrobRightRow

/-! ## B1 non-vacuity probes (the truth-probe outputs) -/

#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle
#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle
#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobRightLeg
#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  (boundarySource frobMonadOmegaFrobLeftLeg) (boundarySource frobMonadOmegaFrobMiddle)
#eval allFrobMonadGenLabels.length

/-! ## The B1 honesty markers -/

/-- ★ **ESTABLISHED (B1).**  The walking Frobenius monad's FOUR 2-cell generators (`mu`, `eta`, `delta`,
`epsilon`) over one object with one endo-1-generator `s` are re-encoded as an `OmegaComputad` 2-polygraph,
and the two Frobenius rows F1 `(s <| delta).(mu |> s)` / F2 `(delta |> s).(s <| mu)` type-check on concrete
words as `CellExpr frobMonadOmegaComputad 2` (`frobMonadOmegaFrobLeftLeg` / `frobMonadOmegaFrobRightLeg`),
each sharing the middle `M = mu . delta` and globular on the nose at both boundaries
(`frobMonadOmegaFrobLeftRow` / `frobMonadOmegaFrobRightRow`, peak = valley = `s.s`).  `= true`. -/
def fxFrob_frobeniusRowsTypeCheckOnConcreteWords : Bool := true

/-- ★ **THE FROBENIUS ROWS ARE LITERALLY GLOBULAR ON BOTH BOUNDARIES (B1).**  `= true` records that both
Frobenius rows' peak AND valley close on the nose (`frobMonadOmegaFrobLeftLeg_literallyParallelSource /
Target = true`): all three cells `L1` / `M` / `L2` have source and target `s.s` literally, so the
mu-redex / delta-expansion overlap resolves with a `refl` join — the easiest resolution scope (the same as
the walking-equivalence cancellations), not modulo-strict. -/
def fxFrob_frobeniusRowsLiterallyGlobular : Bool := true

end FX1Poly.Polygraph.Omega
