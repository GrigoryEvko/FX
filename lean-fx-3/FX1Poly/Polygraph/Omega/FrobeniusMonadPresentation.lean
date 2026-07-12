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

/-! # =========================================================================================
    # B2 — THE TWELVE CRITICAL-PAIR RESOLUTIONS (5 monad + 5 comonad + 2 Frobenius)
    # =========================================================================================

★ **The walking Frobenius monad = monad(mu, eta) + comonad(delta, epsilon) + Frobenius(F1, F2), single
object, FOUR 2-cell generators, TWELVE critical-pair rows = 5 + 5 + 2.**  The monad-internal five reuse the
walking monad's leg shapes verbatim (`MonadCoherentPresentation`); the comonad-internal five are the
OP-MIRROR shapes declared NATIVELY (op does not transport onto the delta-labeled generator — `op mu` is a
mu-labeled cell, not delta — so a native declaration, per the `WalkingDistLawPresentation` colour-generic
precedent, is required); the two Frobenius rows join by `refl` at BOTH peak and valley (the cleanest new
content — no strict-modulo work).

## The comonad's join scope is the MIRROR of the monad's (op-duality swaps source / target)

| Monad pair        | peak     | valley   |    | Comonad pair (op-mirror) | peak     | valley   |
|-------------------|----------|----------|----|--------------------------|----------|----------|
| unitUnit          | units    | refl     |    | counitCounit             | refl     | units    |
| leftUnitAssoc     | assoc    | refl     |    | leftCounitCoassoc        | refl     | assoc    |
| rightUnitAssoc    | units    | assoc    |    | rightCounitCoassoc       | assoc    | units    |
| pentagon          | refl     | refl     |    | copentagon               | refl     | refl     |
| rootUnitAssoc     | refl     | refl     |    | rootCounitCoassoc        | refl     | refl     |

The walking Frobenius monad is SELF-OP-DUAL up to the relabeling `mu <-> delta`, `eta <-> epsilon` (a
docstring free-rider observation, exactly the walking-equivalence self-op-dual note — NOT an op-transport
of the comonad rows, which is a type mismatch). -/

/-! ## The five monad-internal legs (over `s`, `eta`, `mu`) — the walking monad's five leg shapes -/

/-- **monad `unitUnit` left leg**: `eta |> s` (`id.s => s.s`). -/
def frobMonadOmegaMonadUnitUnitLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaEtaGen frobMonadOmegaSGen

/-- **monad `unitUnit` right leg**: `s <| eta` (`s.id => s.s`). -/
def frobMonadOmegaMonadUnitUnitRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaEtaGen

/-- **monad `leftUnitAssoc` left leg**: `mu |> s` (`(s.s).s => s.s`). -/
def frobMonadOmegaMonadLeftUnitAssocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaSGen

/-- **monad `leftUnitAssoc` right leg**: `s <| mu` (`s.(s.s) => s.s`). -/
def frobMonadOmegaMonadLeftUnitAssocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaMuGen

/-- **monad `rightUnitAssoc` left leg**: `eta |> s.s` (`id.(s.s) => s.(s.s)`). -/
def frobMonadOmegaMonadRightUnitAssocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaEtaGen frobMonadOmegaSsWord

/-- **monad `rightUnitAssoc` right leg**: `s.s <| eta` (`(s.s).id => (s.s).s`). -/
def frobMonadOmegaMonadRightUnitAssocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaEtaGen

/-- **monad `pentagon` left leg**: `(mu |> s.s) . (s <| mu)`. -/
def frobMonadOmegaMonadPentagonLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaSsWord)
    (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaMuGen)

/-- **monad `pentagon` right leg**: `(s.s <| mu) . (mu |> s)`. -/
def frobMonadOmegaMonadPentagonRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaMuGen)
    (CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaSGen)

/-- **monad `rootUnitAssoc` left leg**: `(mu |> id) . (s <| eta)`. -/
def frobMonadOmegaMonadRootUnitAssocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaIdOne)
    (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaEtaGen)

/-- **monad `rootUnitAssoc` right leg**: `(s.s <| eta) . (mu |> s)`. -/
def frobMonadOmegaMonadRootUnitAssocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaEtaGen)
    (CellExpr.whiskerRight frobMonadOmegaMuGen frobMonadOmegaSGen)

/-! ## The five comonad-internal legs (over `s`, `epsilon`, `delta`) — the OP-MIRROR shapes, native -/

/-- **comonad `counitCounit` left leg**: `epsilon |> s` (`s.s => id.s`). -/
def frobMonadOmegaCounitCounitLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaEpsGen frobMonadOmegaSGen

/-- **comonad `counitCounit` right leg**: `s <| epsilon` (`s.s => s.id`). -/
def frobMonadOmegaCounitCounitRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaEpsGen

/-- **comonad `leftCounitCoassoc` left leg**: `delta |> s` (`s.s => (s.s).s`). -/
def frobMonadOmegaLeftCounitCoassocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaSGen

/-- **comonad `leftCounitCoassoc` right leg**: `s <| delta` (`s.s => s.(s.s)`). -/
def frobMonadOmegaLeftCounitCoassocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaDeltaGen

/-- **comonad `rightCounitCoassoc` left leg**: `epsilon |> s.s` (`s.(s.s) => id.(s.s)`). -/
def frobMonadOmegaRightCounitCoassocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerRight frobMonadOmegaEpsGen frobMonadOmegaSsWord

/-- **comonad `rightCounitCoassoc` right leg**: `s.s <| epsilon` (`(s.s).s => (s.s).id`). -/
def frobMonadOmegaRightCounitCoassocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaEpsGen

/-- **comonad `copentagon` left leg**: `(delta |> s) . (s.s <| delta)` (the Godement front of `delta * delta`). -/
def frobMonadOmegaCopentagonLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaSGen)
    (CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaDeltaGen)

/-- **comonad `copentagon` right leg**: `(s <| delta) . (delta |> s.s)` (the Godement back of `delta * delta`). -/
def frobMonadOmegaCopentagonRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaDeltaGen)
    (CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaSsWord)

/-- **comonad `rootCounitCoassoc` left leg**: `(delta |> s) . (s.s <| epsilon)` (the Godement front of
`delta * epsilon`). -/
def frobMonadOmegaRootCounitCoassocLeftLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaSGen)
    (CellExpr.whiskerLeft frobMonadOmegaSsWord frobMonadOmegaEpsGen)

/-- **comonad `rootCounitCoassoc` right leg**: `(s <| epsilon) . (delta |> id)` (the Godement back of
`delta * epsilon`). -/
def frobMonadOmegaRootCounitCoassocRightLeg : CellExpr frobMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft frobMonadOmegaSGen frobMonadOmegaEpsGen)
    (CellExpr.whiskerRight frobMonadOmegaDeltaGen frobMonadOmegaIdOne)

/-! ## The twelve critical-pair rows and the base relation -/

/-- ★ The **twelve walking-Frobenius-monad critical-pair rows** — the five monad-internal pairs, the five
comonad-internal pairs, and the two Frobenius rows.  A `CellRelOver` firing on each overlap's two reduction
legs: the walking Frobenius monad's homotopy basis at Squier's convergent scope. -/
inductive FrobMonadCriticalRow :
    {d : Nat} → CellExpr frobMonadOmegaComputad d → CellExpr frobMonadOmegaComputad d → Prop where
  /-- monad `unitUnit`. -/
  | monadUnitUnit : FrobMonadCriticalRow frobMonadOmegaMonadUnitUnitLeftLeg
      frobMonadOmegaMonadUnitUnitRightLeg
  /-- monad `leftUnitAssoc`. -/
  | monadLeftUnitAssoc : FrobMonadCriticalRow frobMonadOmegaMonadLeftUnitAssocLeftLeg
      frobMonadOmegaMonadLeftUnitAssocRightLeg
  /-- monad `rightUnitAssoc`. -/
  | monadRightUnitAssoc : FrobMonadCriticalRow frobMonadOmegaMonadRightUnitAssocLeftLeg
      frobMonadOmegaMonadRightUnitAssocRightLeg
  /-- monad `pentagon`. -/
  | monadPentagon : FrobMonadCriticalRow frobMonadOmegaMonadPentagonLeftLeg
      frobMonadOmegaMonadPentagonRightLeg
  /-- monad `rootUnitAssoc`. -/
  | monadRootUnitAssoc : FrobMonadCriticalRow frobMonadOmegaMonadRootUnitAssocLeftLeg
      frobMonadOmegaMonadRootUnitAssocRightLeg
  /-- comonad `counitCounit`. -/
  | counitCounit : FrobMonadCriticalRow frobMonadOmegaCounitCounitLeftLeg
      frobMonadOmegaCounitCounitRightLeg
  /-- comonad `leftCounitCoassoc`. -/
  | leftCounitCoassoc : FrobMonadCriticalRow frobMonadOmegaLeftCounitCoassocLeftLeg
      frobMonadOmegaLeftCounitCoassocRightLeg
  /-- comonad `rightCounitCoassoc`. -/
  | rightCounitCoassoc : FrobMonadCriticalRow frobMonadOmegaRightCounitCoassocLeftLeg
      frobMonadOmegaRightCounitCoassocRightLeg
  /-- comonad `copentagon`. -/
  | copentagon : FrobMonadCriticalRow frobMonadOmegaCopentagonLeftLeg frobMonadOmegaCopentagonRightLeg
  /-- comonad `rootCounitCoassoc`. -/
  | rootCounitCoassoc : FrobMonadCriticalRow frobMonadOmegaRootCounitCoassocLeftLeg
      frobMonadOmegaRootCounitCoassocRightLeg
  /-- Frobenius F1 (frobLeft) — `(s <| delta).(mu |> s) ~ mu . delta`. -/
  | frobLeft : FrobMonadCriticalRow frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle
  /-- Frobenius F2 (frobRight) — `(delta |> s).(s <| mu) ~ mu . delta`. -/
  | frobRight : FrobMonadCriticalRow frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle

/-- The base relation the 3-cells resolve: the strict omega laws united with the twelve critical-pair
rows. -/
def frobMonadOmegaBaseRel : CellRelOver frobMonadOmegaComputad :=
  unionCellRel frobMonadOmegaComputad (StrictAxiomRel frobMonadOmegaComputad) FrobMonadCriticalRow

/-! ## The twelve generating 3-cells -/

/-- ★ **THE monad `unitUnit` GENERATING 3-CELL.** -/
def frobMonadOmegaMonadUnitUnitThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaMonadUnitUnitLeftLeg frobMonadOmegaMonadUnitUnitRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.monadUnitUnit)

/-- ★ **THE monad `leftUnitAssoc` GENERATING 3-CELL.** -/
def frobMonadOmegaMonadLeftUnitAssocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaMonadLeftUnitAssocLeftLeg frobMonadOmegaMonadLeftUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.monadLeftUnitAssoc)

/-- ★ **THE monad `rightUnitAssoc` GENERATING 3-CELL.** -/
def frobMonadOmegaMonadRightUnitAssocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaMonadRightUnitAssocLeftLeg frobMonadOmegaMonadRightUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.monadRightUnitAssoc)

/-- ★ **THE monad `pentagon` GENERATING 3-CELL.** -/
def frobMonadOmegaMonadPentagonThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaMonadPentagonLeftLeg frobMonadOmegaMonadPentagonRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.monadPentagon)

/-- ★ **THE monad `rootUnitAssoc` GENERATING 3-CELL.** -/
def frobMonadOmegaMonadRootUnitAssocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaMonadRootUnitAssocLeftLeg frobMonadOmegaMonadRootUnitAssocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.monadRootUnitAssoc)

/-- ★ **THE comonad `counitCounit` GENERATING 3-CELL.** -/
def frobMonadOmegaCounitCounitThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaCounitCounitLeftLeg frobMonadOmegaCounitCounitRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.counitCounit)

/-- ★ **THE comonad `leftCounitCoassoc` GENERATING 3-CELL.** -/
def frobMonadOmegaLeftCounitCoassocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaLeftCounitCoassocLeftLeg frobMonadOmegaLeftCounitCoassocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.leftCounitCoassoc)

/-- ★ **THE comonad `rightCounitCoassoc` GENERATING 3-CELL.** -/
def frobMonadOmegaRightCounitCoassocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaRightCounitCoassocLeftLeg frobMonadOmegaRightCounitCoassocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.rightCounitCoassoc)

/-- ★ **THE comonad `copentagon` GENERATING 3-CELL.** -/
def frobMonadOmegaCopentagonThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaCopentagonLeftLeg frobMonadOmegaCopentagonRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.copentagon)

/-- ★ **THE comonad `rootCounitCoassoc` GENERATING 3-CELL.** -/
def frobMonadOmegaRootCounitCoassocThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaRootCounitCoassocLeftLeg frobMonadOmegaRootCounitCoassocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.rootCounitCoassoc)

/-- ★★ **THE FROBENIUS F1 GENERATING 3-CELL** (`(s <| delta).(mu |> s) ~ mu . delta`) — the genuinely-new
mu-delta interaction content. -/
def frobMonadOmegaFrobLeftThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.frobLeft)

/-- ★★ **THE FROBENIUS F2 GENERATING 3-CELL** (`(delta |> s).(s <| mu) ~ mu . delta`). -/
def frobMonadOmegaFrobRightThreeCell :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle :=
  SaturatedConvOverWithId.ofRelation (Or.inr FrobMonadCriticalRow.frobRight)

/-! ## The twelve peak joins (the leg SOURCES join modulo strict) -/

/-- monad `unitUnit` peak: `id.s ~ s.id` (units). -/
def frobMonadOmegaMonadUnitUnitPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaMonadUnitUnitLeftLeg)
      (boundarySource frobMonadOmegaMonadUnitUnitRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft frobMonadOmegaSGen)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight frobMonadOmegaSGen))))

/-- monad `leftUnitAssoc` peak: `(s.s).s ~ s.(s.s)` (assoc). -/
def frobMonadOmegaMonadLeftUnitAssocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaMonadLeftUnitAssocLeftLeg)
      (boundarySource frobMonadOmegaMonadLeftUnitAssocRightLeg) :=
  SaturatedConvOverWithId.ofRelation
    (Or.inl (StrictAxiomRel.vcompAssoc frobMonadOmegaSGen frobMonadOmegaSGen frobMonadOmegaSGen))

/-- monad `rightUnitAssoc` peak: `id.(s.s) ~ (s.s).id` (units). -/
def frobMonadOmegaMonadRightUnitAssocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaMonadRightUnitAssocLeftLeg)
      (boundarySource frobMonadOmegaMonadRightUnitAssocRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft frobMonadOmegaSsWord)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight frobMonadOmegaSsWord))))

/-- monad `pentagon` peak: LITERALLY equal (`(s.s).(s.s)`) — `refl`. -/
def frobMonadOmegaMonadPentagonPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaMonadPentagonLeftLeg)
      (boundarySource frobMonadOmegaMonadPentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rootUnitAssoc` peak: LITERALLY equal (`(s.s).id`) — `refl`. -/
def frobMonadOmegaMonadRootUnitAssocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaMonadRootUnitAssocLeftLeg)
      (boundarySource frobMonadOmegaMonadRootUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `counitCounit` peak: LITERALLY equal (`s.s`) — `refl` (the op-mirror of monad `unitUnit`). -/
def frobMonadOmegaCounitCounitPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaCounitCounitLeftLeg)
      (boundarySource frobMonadOmegaCounitCounitRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `leftCounitCoassoc` peak: LITERALLY equal (`s.s`) — `refl`. -/
def frobMonadOmegaLeftCounitCoassocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaLeftCounitCoassocLeftLeg)
      (boundarySource frobMonadOmegaLeftCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `rightCounitCoassoc` peak: `s.(s.s) ~ (s.s).s` (assoc; the op-mirror of monad `rightUnitAssoc`). -/
def frobMonadOmegaRightCounitCoassocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaRightCounitCoassocLeftLeg)
      (boundarySource frobMonadOmegaRightCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.symm
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc frobMonadOmegaSGen frobMonadOmegaSGen frobMonadOmegaSGen)))

/-- comonad `copentagon` peak: LITERALLY equal (`s.s`) — `refl`. -/
def frobMonadOmegaCopentagonPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaCopentagonLeftLeg)
      (boundarySource frobMonadOmegaCopentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `rootCounitCoassoc` peak: LITERALLY equal (`s.s`) — `refl`. -/
def frobMonadOmegaRootCounitCoassocPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaRootCounitCoassocLeftLeg)
      (boundarySource frobMonadOmegaRootCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- Frobenius F1 peak: LITERALLY equal (`s.s`) — `refl`. -/
def frobMonadOmegaFrobLeftPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaFrobLeftLeg) (boundarySource frobMonadOmegaFrobMiddle) :=
  SaturatedConvOverWithId.refl _

/-- Frobenius F2 peak: LITERALLY equal (`s.s`) — `refl`. -/
def frobMonadOmegaFrobRightPeakJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundarySource frobMonadOmegaFrobRightLeg) (boundarySource frobMonadOmegaFrobMiddle) :=
  SaturatedConvOverWithId.refl _

/-! ## The twelve valley joins (the leg TARGETS join modulo strict) -/

/-- monad `unitUnit` valley: both `s.s` — `refl`. -/
def frobMonadOmegaMonadUnitUnitValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaMonadUnitUnitLeftLeg)
      (boundaryTarget frobMonadOmegaMonadUnitUnitRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `leftUnitAssoc` valley: both `s.s` — `refl`. -/
def frobMonadOmegaMonadLeftUnitAssocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaMonadLeftUnitAssocLeftLeg)
      (boundaryTarget frobMonadOmegaMonadLeftUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rightUnitAssoc` valley: `s.(s.s) ~ (s.s).s` (assoc). -/
def frobMonadOmegaMonadRightUnitAssocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaMonadRightUnitAssocLeftLeg)
      (boundaryTarget frobMonadOmegaMonadRightUnitAssocRightLeg) :=
  SaturatedConvOverWithId.symm
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc frobMonadOmegaSGen frobMonadOmegaSGen frobMonadOmegaSGen)))

/-- monad `pentagon` valley: both `s.s` — `refl`. -/
def frobMonadOmegaMonadPentagonValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaMonadPentagonLeftLeg)
      (boundaryTarget frobMonadOmegaMonadPentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- monad `rootUnitAssoc` valley: both `s.s` — `refl`. -/
def frobMonadOmegaMonadRootUnitAssocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaMonadRootUnitAssocLeftLeg)
      (boundaryTarget frobMonadOmegaMonadRootUnitAssocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `counitCounit` valley: `id.s ~ s.id` (units; the op-mirror of monad `unitUnit`'s peak). -/
def frobMonadOmegaCounitCounitValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaCounitCounitLeftLeg)
      (boundaryTarget frobMonadOmegaCounitCounitRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft frobMonadOmegaSGen)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight frobMonadOmegaSGen))))

/-- comonad `leftCounitCoassoc` valley: `(s.s).s ~ s.(s.s)` (assoc; the op-mirror of monad `leftUnitAssoc`'s
peak). -/
def frobMonadOmegaLeftCounitCoassocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaLeftCounitCoassocLeftLeg)
      (boundaryTarget frobMonadOmegaLeftCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.ofRelation
    (Or.inl (StrictAxiomRel.vcompAssoc frobMonadOmegaSGen frobMonadOmegaSGen frobMonadOmegaSGen))

/-- comonad `rightCounitCoassoc` valley: `id.(s.s) ~ (s.s).id` (units). -/
def frobMonadOmegaRightCounitCoassocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaRightCounitCoassocLeftLeg)
      (boundaryTarget frobMonadOmegaRightCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft frobMonadOmegaSsWord)))
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight frobMonadOmegaSsWord))))

/-- comonad `copentagon` valley: both `(s.s).(s.s)` — `refl`. -/
def frobMonadOmegaCopentagonValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaCopentagonLeftLeg)
      (boundaryTarget frobMonadOmegaCopentagonRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- comonad `rootCounitCoassoc` valley: both `(s.s).id` — `refl`. -/
def frobMonadOmegaRootCounitCoassocValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaRootCounitCoassocLeftLeg)
      (boundaryTarget frobMonadOmegaRootCounitCoassocRightLeg) :=
  SaturatedConvOverWithId.refl _

/-- Frobenius F1 valley: both `s.s` — `refl`. -/
def frobMonadOmegaFrobLeftValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaFrobLeftLeg) (boundaryTarget frobMonadOmegaFrobMiddle) :=
  SaturatedConvOverWithId.refl _

/-- Frobenius F2 valley: both `s.s` — `refl`. -/
def frobMonadOmegaFrobRightValleyJoin :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (boundaryTarget frobMonadOmegaFrobRightLeg) (boundaryTarget frobMonadOmegaFrobMiddle) :=
  SaturatedConvOverWithId.refl _

/-! ## The assembled per-pair resolution -/

/-- ★ A **coherent resolution** of one Frobenius-monad critical pair, joinable MODULO the strict congruence:
the two leg SOURCES are convertible (peak), the two legs are convertible (the generating 3-cell), and the
two leg TARGETS are convertible (valley).  Parameterised by the two legs so all twelve pairs share one datum
shape. -/
structure FrobMonadCriticalPairResolved {d : Nat}
    (leftLeg rightLeg : CellExpr frobMonadOmegaComputad (d + 1)) : Prop where
  /-- The two leg SOURCES are convertible (the peak join). -/
  peakJoined : SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
    (boundarySource leftLeg) (boundarySource rightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible : SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel leftLeg rightLeg
  /-- The two leg TARGETS are convertible (the valley join). -/
  valleyJoined : SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
    (boundaryTarget leftLeg) (boundaryTarget rightLeg)

/-- The monad `unitUnit` pair is coherently resolved (peak units, valley refl). -/
theorem frobMonadOmegaMonadUnitUnitResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaMonadUnitUnitLeftLeg
      frobMonadOmegaMonadUnitUnitRightLeg :=
  ⟨frobMonadOmegaMonadUnitUnitPeakJoin, frobMonadOmegaMonadUnitUnitThreeCell,
    frobMonadOmegaMonadUnitUnitValleyJoin⟩

/-- The monad `leftUnitAssoc` pair is coherently resolved (peak assoc, valley refl). -/
theorem frobMonadOmegaMonadLeftUnitAssocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaMonadLeftUnitAssocLeftLeg
      frobMonadOmegaMonadLeftUnitAssocRightLeg :=
  ⟨frobMonadOmegaMonadLeftUnitAssocPeakJoin, frobMonadOmegaMonadLeftUnitAssocThreeCell,
    frobMonadOmegaMonadLeftUnitAssocValleyJoin⟩

/-- The monad `rightUnitAssoc` pair is coherently resolved (peak units, valley assoc — the richest). -/
theorem frobMonadOmegaMonadRightUnitAssocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaMonadRightUnitAssocLeftLeg
      frobMonadOmegaMonadRightUnitAssocRightLeg :=
  ⟨frobMonadOmegaMonadRightUnitAssocPeakJoin, frobMonadOmegaMonadRightUnitAssocThreeCell,
    frobMonadOmegaMonadRightUnitAssocValleyJoin⟩

/-- The monad `pentagon` pair is coherently resolved (peak refl, valley refl — literally globular). -/
theorem frobMonadOmegaMonadPentagonResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaMonadPentagonLeftLeg
      frobMonadOmegaMonadPentagonRightLeg :=
  ⟨frobMonadOmegaMonadPentagonPeakJoin, frobMonadOmegaMonadPentagonThreeCell,
    frobMonadOmegaMonadPentagonValleyJoin⟩

/-- The monad `rootUnitAssoc` pair is coherently resolved (peak refl, valley refl). -/
theorem frobMonadOmegaMonadRootUnitAssocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaMonadRootUnitAssocLeftLeg
      frobMonadOmegaMonadRootUnitAssocRightLeg :=
  ⟨frobMonadOmegaMonadRootUnitAssocPeakJoin, frobMonadOmegaMonadRootUnitAssocThreeCell,
    frobMonadOmegaMonadRootUnitAssocValleyJoin⟩

/-- The comonad `counitCounit` pair is coherently resolved (peak refl, valley units — op-mirror of
`unitUnit`). -/
theorem frobMonadOmegaCounitCounitResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaCounitCounitLeftLeg
      frobMonadOmegaCounitCounitRightLeg :=
  ⟨frobMonadOmegaCounitCounitPeakJoin, frobMonadOmegaCounitCounitThreeCell,
    frobMonadOmegaCounitCounitValleyJoin⟩

/-- The comonad `leftCounitCoassoc` pair is coherently resolved (peak refl, valley assoc). -/
theorem frobMonadOmegaLeftCounitCoassocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaLeftCounitCoassocLeftLeg
      frobMonadOmegaLeftCounitCoassocRightLeg :=
  ⟨frobMonadOmegaLeftCounitCoassocPeakJoin, frobMonadOmegaLeftCounitCoassocThreeCell,
    frobMonadOmegaLeftCounitCoassocValleyJoin⟩

/-- The comonad `rightCounitCoassoc` pair is coherently resolved (peak assoc, valley units — the richest
comonad pair). -/
theorem frobMonadOmegaRightCounitCoassocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaRightCounitCoassocLeftLeg
      frobMonadOmegaRightCounitCoassocRightLeg :=
  ⟨frobMonadOmegaRightCounitCoassocPeakJoin, frobMonadOmegaRightCounitCoassocThreeCell,
    frobMonadOmegaRightCounitCoassocValleyJoin⟩

/-- The comonad `copentagon` pair is coherently resolved (peak refl, valley refl — literally globular). -/
theorem frobMonadOmegaCopentagonResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaCopentagonLeftLeg frobMonadOmegaCopentagonRightLeg :=
  ⟨frobMonadOmegaCopentagonPeakJoin, frobMonadOmegaCopentagonThreeCell,
    frobMonadOmegaCopentagonValleyJoin⟩

/-- The comonad `rootCounitCoassoc` pair is coherently resolved (peak refl, valley refl). -/
theorem frobMonadOmegaRootCounitCoassocResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaRootCounitCoassocLeftLeg
      frobMonadOmegaRootCounitCoassocRightLeg :=
  ⟨frobMonadOmegaRootCounitCoassocPeakJoin, frobMonadOmegaRootCounitCoassocThreeCell,
    frobMonadOmegaRootCounitCoassocValleyJoin⟩

/-- ★★ The Frobenius F1 pair is coherently resolved (peak refl, valley refl — literally globular on both
boundaries).  The genuinely-new mu-delta interaction. -/
theorem frobMonadOmegaFrobLeftResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle :=
  ⟨frobMonadOmegaFrobLeftPeakJoin, frobMonadOmegaFrobLeftThreeCell, frobMonadOmegaFrobLeftValleyJoin⟩

/-- ★★ The Frobenius F2 pair is coherently resolved (peak refl, valley refl — literally globular on both
boundaries). -/
theorem frobMonadOmegaFrobRightResolved :
    FrobMonadCriticalPairResolved frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle :=
  ⟨frobMonadOmegaFrobRightPeakJoin, frobMonadOmegaFrobRightThreeCell, frobMonadOmegaFrobRightValleyJoin⟩

/-! ## The coherent-presentation bundle (the honest-scope statement) -/

/-- ★ **The walking-Frobenius-monad coherent-presentation statement (honest scope).**  All TWELVE critical
pairs are coherently resolved modulo the strict congruence — a `Prop` conjunction of the twelve per-pair
resolutions (5 monad + 5 comonad + 2 Frobenius). -/
def FrobMonadWalkerCoherentPresentationStatement : Prop :=
  FrobMonadCriticalPairResolved frobMonadOmegaMonadUnitUnitLeftLeg
    frobMonadOmegaMonadUnitUnitRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaMonadLeftUnitAssocLeftLeg
    frobMonadOmegaMonadLeftUnitAssocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaMonadRightUnitAssocLeftLeg
    frobMonadOmegaMonadRightUnitAssocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaMonadPentagonLeftLeg
    frobMonadOmegaMonadPentagonRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaMonadRootUnitAssocLeftLeg
    frobMonadOmegaMonadRootUnitAssocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaCounitCounitLeftLeg
    frobMonadOmegaCounitCounitRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaLeftCounitCoassocLeftLeg
    frobMonadOmegaLeftCounitCoassocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaRightCounitCoassocLeftLeg
    frobMonadOmegaRightCounitCoassocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaCopentagonLeftLeg frobMonadOmegaCopentagonRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaRootCounitCoassocLeftLeg
    frobMonadOmegaRootCounitCoassocRightLeg ∧
  FrobMonadCriticalPairResolved frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle ∧
  FrobMonadCriticalPairResolved frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle

/-- ★★ **THE WALKING FROBENIUS MONAD COHERENT PRESENTATION (twelve critical pairs, joinable modulo strict).**
The walking Frobenius monad `<s | mu, eta, delta, epsilon | monad + comonad + two Frobenius rows>` re-encoded
as an `OmegaComputad` 2-polygraph has all TWELVE Squier critical pairs exhibited as generating 3-cells, each
joinable-modulo-strict at peak and valley — the five monad-internal transported, the five comonad-internal
op-mirror, and the two Frobenius rows joined by `refl` on both boundaries (the genuinely-new mu-delta
interaction). -/
theorem frobMonadWalkerCoherentPresentation : FrobMonadWalkerCoherentPresentationStatement :=
  ⟨frobMonadOmegaMonadUnitUnitResolved, frobMonadOmegaMonadLeftUnitAssocResolved,
    frobMonadOmegaMonadRightUnitAssocResolved, frobMonadOmegaMonadPentagonResolved,
    frobMonadOmegaMonadRootUnitAssocResolved, frobMonadOmegaCounitCounitResolved,
    frobMonadOmegaLeftCounitCoassocResolved, frobMonadOmegaRightCounitCoassocResolved,
    frobMonadOmegaCopentagonResolved, frobMonadOmegaRootCounitCoassocResolved,
    frobMonadOmegaFrobLeftResolved, frobMonadOmegaFrobRightResolved⟩

/-- ★ **The two-Frobenius-rows statement (the genuinely-new mu-delta interaction content).**  A `Prop`
conjunction of the two Frobenius coherent resolutions — the content that distinguishes the Frobenius monad
from the bare monad + comonad. -/
def FrobMonadTwoFrobeniusRowsResolvedStatement : Prop :=
  FrobMonadCriticalPairResolved frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle ∧
  FrobMonadCriticalPairResolved frobMonadOmegaFrobRightLeg frobMonadOmegaFrobMiddle

/-- ★★ **THE TWO FROBENIUS ROWS, COHERENTLY RESOLVED (literally globular on both boundaries).**  Both
mu-delta Frobenius overlaps exhibited as generating 3-cells, each joinable on the nose at peak AND valley —
the genuinely-new content of the walking Frobenius monad over the disjoint monad + comonad. -/
theorem frobMonadTwoFrobeniusRowsResolved : FrobMonadTwoFrobeniusRowsResolvedStatement :=
  ⟨frobMonadOmegaFrobLeftResolved, frobMonadOmegaFrobRightResolved⟩

/-! ## The least-congruence universal property (map-out) -/

/-- ★ **THE TWELVE 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP).**  For any relation
`targetRel` absorbing the Frobenius-monad base relation (a congruence containing the strict laws and the
twelve critical-pair rows), the two legs of EVERY critical row are `targetRel`-related — so the twelve
generating 3-cells are the datum whose fold through `SaturatedConvOverWithId.recInto` identifies each critical
pair in EVERY model.  Uniform in the row (one statement covering all twelve, keyed on
`FrobMonadCriticalRow`). -/
theorem frobMonadCriticalPairsIdentifiedInEveryModel {targetRel : CellRelOver frobMonadOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId frobMonadOmegaComputad frobMonadOmegaBaseRel targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr frobMonadOmegaComputad d}
    (row : FrobMonadCriticalRow leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation (Or.inr row))

/-! ## The twelve-row census -/

/-- The twelve critical-pair labels — five monad-internal, five comonad-internal, two Frobenius. -/
inductive FrobMonadCriticalPairLabel
  /-- monad `unitUnit`. -/
  | monadUnitUnit
  /-- monad `leftUnitAssoc`. -/
  | monadLeftUnitAssoc
  /-- monad `rightUnitAssoc`. -/
  | monadRightUnitAssoc
  /-- monad `pentagon`. -/
  | monadPentagon
  /-- monad `rootUnitAssoc`. -/
  | monadRootUnitAssoc
  /-- comonad `counitCounit`. -/
  | counitCounit
  /-- comonad `leftCounitCoassoc`. -/
  | leftCounitCoassoc
  /-- comonad `rightCounitCoassoc`. -/
  | rightCounitCoassoc
  /-- comonad `copentagon`. -/
  | copentagon
  /-- comonad `rootCounitCoassoc`. -/
  | rootCounitCoassoc
  /-- Frobenius F1 (frobLeft). -/
  | frobLeft
  /-- Frobenius F2 (frobRight). -/
  | frobRight

/-- The complete enumeration of the Frobenius-monad critical pairs — TWELVE, listed. -/
def allFrobMonadCriticalPairs : List FrobMonadCriticalPairLabel :=
  [.monadUnitUnit, .monadLeftUnitAssoc, .monadRightUnitAssoc, .monadPentagon, .monadRootUnitAssoc,
    .counitCounit, .leftCounitCoassoc, .rightCounitCoassoc, .copentagon, .rootCounitCoassoc,
    .frobLeft, .frobRight]

/-- ★ **The critical-pair count is exactly TWELVE** — kernel-checked (`rfl`): 5 monad + 5 comonad + 2
Frobenius. -/
theorem frobMonadCriticalPairCountIsTwelve : allFrobMonadCriticalPairs.length = 12 := rfl

/-- The two Frobenius-interaction labels — the genuinely-new mu-delta content. -/
def allFrobMonadFrobeniusPairs : List FrobMonadCriticalPairLabel := [.frobLeft, .frobRight]

/-- ★ **The Frobenius-interaction count is exactly TWO** — kernel-checked (`rfl`). -/
theorem frobMonadFrobeniusPairCountIsTwo : allFrobMonadFrobeniusPairs.length = 2 := rfl

/-! ## B2 non-vacuity — a sample of monad / comonad legs are genuinely distinct 2-cells -/

/-- The monad `unitUnit` legs are structurally DISTINCT (`eta |> s` vs `s <| eta`). -/
theorem frobMonadOmegaMonadUnitUnitLegs_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaMonadUnitUnitLeftLeg frobMonadOmegaMonadUnitUnitRightLeg = false := rfl

/-- The comonad `counitCounit` legs are structurally DISTINCT (`epsilon |> s` vs `s <| epsilon`). -/
theorem frobMonadOmegaCounitCounitLegs_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaCounitCounitLeftLeg frobMonadOmegaCounitCounitRightLeg = false := rfl

/-- The comonad `copentagon` legs are structurally DISTINCT (the two Godement whisker orders of `delta * delta`). -/
theorem frobMonadOmegaCopentagonLegs_distinct :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      frobMonadOmegaCopentagonLeftLeg frobMonadOmegaCopentagonRightLeg = false := rfl

/-- The monad `unitUnit` peak spellings are structurally distinct (`id.s` vs `s.id`) — parallel only MODULO
strict (the honest fragment boundary). -/
theorem frobMonadOmegaMonadUnitUnitLegs_notLiterallyParallel :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      (boundarySource frobMonadOmegaMonadUnitUnitLeftLeg)
      (boundarySource frobMonadOmegaMonadUnitUnitRightLeg) = false := rfl

/-- The comonad `counitCounit` VALLEY spellings are structurally distinct (`id.s` vs `s.id`) — the op-mirror
modulo-strict boundary (the comonad's valley is modulo-strict where the monad's peak is). -/
theorem frobMonadOmegaCounitCounitLegs_notLiterallyParallelTarget :
    cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
      (boundaryTarget frobMonadOmegaCounitCounitLeftLeg)
      (boundaryTarget frobMonadOmegaCounitCounitRightLeg) = false := rfl

/-! ## B2 non-vacuity probes -/

#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  frobMonadOmegaMonadUnitUnitLeftLeg frobMonadOmegaMonadUnitUnitRightLeg
#eval cellBeq frobMonadOmegaModeBeq frobMonadOmegaGenBeq
  frobMonadOmegaCounitCounitLeftLeg frobMonadOmegaCounitCounitRightLeg
#eval allFrobMonadCriticalPairs.length

/-! ## The B2 honesty marker -/

/-- ★ **ESTABLISHED (B2).**  The walking Frobenius monad's TWELVE Squier critical pairs (5 monad-internal
transported + 5 comonad-internal op-mirror + 2 Frobenius) are exhibited as generating 3-cells over
`frobMonadOmegaBaseRel`, each coherently resolved modulo strict at peak and valley
(`frobMonadWalkerCoherentPresentation`), with the twelve-row census
(`frobMonadCriticalPairCountIsTwelve`) and the least-congruence UP
(`frobMonadCriticalPairsIdentifiedInEveryModel`).  The two Frobenius rows join by `refl` on both boundaries
(`frobMonadTwoFrobeniusRowsResolved`) — the genuinely-new mu-delta interaction.  `= true`. -/
def fxFrob_twelveCriticalPairsShipped : Bool := true

/-! # =========================================================================================
    # B3 — THE SOUNDNESS INVARIANT (the four-count + the respects-congruence lemma)
    # =========================================================================================

★ **The generator four-count `(#mu, #eta, #delta, #epsilon)` — a machine-checked, congruence-respecting
soundness invariant.**  A structural constant-`Nat` fold (propext-clean like `cellSize`) that counts the
occurrences of each 2-cell generator, IGNORING identities (count zero) and whiskering 1-cells (not counted).
The exact analogue of the walking monad's `(#eta, #mu)` cofork column and the Homology abelianization; the
2GROUP-lane Peiffer-invariance pattern (an invariant map + a respects-congruence lemma via the
least-congruence UP `SaturatedConvOverWithId.recInto`).

## Why THIS fold respects the strict laws (the load-bearing design decision)

`vcompUnitLeft a` rewrites `(id (src a)) . a  ~  a`, so identities MUST contribute the zero count (else the
introduced `id (src a)` would change the total).  `whiskerLeftFunctorial w b c` rewrites
`w <| (b.c)  ~  (w <| b) . (w <| c)`, so the whiskering cell `w` MUST NOT be counted (else it would be
double-counted on the RHS).  With `count (id _) = 0` and whiskering cells uncounted, EVERY one of the eight
strict axioms preserves the count (units / functoriality / whisker-unit by `refl`; associativity by
`fourAdd`-associativity; interchange by `fourAdd`-commutativity) and EVERY one of the twelve critical rows
relates equal-count legs (each carries the same generator multiset on both legs).  So the map factors
through `SaturatedConvOverWithId.recInto` into the "equal four-count" congruence: convertible ⟹ equal count.

## Honestly WEAK, and sound only because there is NO special law

The four-count does not separate `mu.delta` from `delta.mu` (both `(1,0,1,0)`) — it is deliberately weak, the
r1-shippable floor.  It is sound only BECAUSE the bare walking Frobenius monad has NO special law
`mu . delta = id` (which would map `mu.delta -> 0`, breaking the count).  The special / commutative Frobenius
PROP (`TwoCategory/Frobenius`) DOES have `mu . delta = id`, so the four-count is NOT sound there — a genuine
distinction confirming the Omega walker is the PLAIN (non-special) one.  The full separating invariant
(genus + boundary matching, the completeness grade) is NAMED-OUT to the `TwoCategory/Frobenius` Cospan /
corelation engine in B4, with genus itself an open wall in every lane. -/

/-! ## The componentwise four-vector monoid -/

/-- Componentwise addition on the four-count vector `(#mu, #eta, #delta, #epsilon)`. -/
def fourAdd : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | (a1, a2, a3, a4), (b1, b2, b3, b4) => (a1 + b1, a2 + b2, a3 + b3, a4 + b4)

/-- `fourAdd` left identity — the zero vector is a left unit (from `Nat.zero_add`). -/
theorem fourAdd_zero_left (x : Nat × Nat × Nat × Nat) : fourAdd (0, 0, 0, 0) x = x := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  show (0 + x1, 0 + x2, 0 + x3, 0 + x4) = (x1, x2, x3, x4)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, Nat.zero_add]

/-- `fourAdd` right identity — the zero vector is a right unit (`Nat.add_zero`, definitional). -/
theorem fourAdd_zero_right (x : Nat × Nat × Nat × Nat) : fourAdd x (0, 0, 0, 0) = x := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  show (x1 + 0, x2 + 0, x3 + 0, x4 + 0) = (x1, x2, x3, x4)
  rw [Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero]

/-- `fourAdd` associativity (componentwise `Nat.add_assoc`). -/
theorem fourAdd_assoc (x y z : Nat × Nat × Nat × Nat) :
    fourAdd (fourAdd x y) z = fourAdd x (fourAdd y z) := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨y1, y2, y3, y4⟩ := y
  obtain ⟨z1, z2, z3, z4⟩ := z
  show (x1 + y1 + z1, x2 + y2 + z2, x3 + y3 + z3, x4 + y4 + z4)
    = (x1 + (y1 + z1), x2 + (y2 + z2), x3 + (y3 + z3), x4 + (y4 + z4))
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

/-- `fourAdd` commutativity (componentwise `Nat.add_comm`). -/
theorem fourAdd_comm (x y : Nat × Nat × Nat × Nat) : fourAdd x y = fourAdd y x := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨y1, y2, y3, y4⟩ := y
  show (x1 + y1, x2 + y2, x3 + y3, x4 + y4) = (y1 + x1, y2 + x2, y3 + x3, y4 + x4)
  rw [Nat.add_comm x1 y1, Nat.add_comm x2 y2, Nat.add_comm x3 y3, Nat.add_comm x4 y4]

/-! ## The generator four-count fold -/

/-- The **four-tag** of a generator label — `1` in the slot of the 2-cell generator it names, `0` elsewhere
(the endo-1-generator `s` contributes nothing).  Full five-arm split — propext-free. -/
def frobMonadLabelFourTag : FrobMonadGenLabel → Nat × Nat × Nat × Nat
  | .sEndo => (0, 0, 0, 0)
  | .muMult => (1, 0, 0, 0)
  | .etaUnit => (0, 1, 0, 0)
  | .deltaComult => (0, 0, 1, 0)
  | .epsCounit => (0, 0, 0, 1)

/-- ★ The **generator four-count** `(#mu, #eta, #delta, #epsilon)` of a cell — a total structural fold over
all six constructors into the constant `Nat × Nat × Nat × Nat` motive (propext-free, like `cellSize`).
Identities count ZERO (no recursion), whiskering 1-cells are NOT counted (only the whiskered cell recurses),
`vcomp` sums both factors, and a `gen` node contributes its label's four-tag.  These choices are exactly what
makes the count invariant under the strict laws. -/
def frobMonadOmegaGeneratorFourCount :
    {dim : Nat} → CellExpr frobMonadOmegaComputad dim → Nat × Nat × Nat × Nat
  | _, .ofMode _ => (0, 0, 0, 0)
  | _, .gen label _ _ => frobMonadLabelFourTag label
  | _, .id _ => (0, 0, 0, 0)
  | _, .vcomp left right =>
      fourAdd (frobMonadOmegaGeneratorFourCount left) (frobMonadOmegaGeneratorFourCount right)
  | _, .whiskerLeft _ cell => frobMonadOmegaGeneratorFourCount cell
  | _, .whiskerRight cell _ => frobMonadOmegaGeneratorFourCount cell

/-! ## The respects-congruence lemma (the four-count absorbs the base relation) -/

/-- ★★ **THE FOUR-COUNT RESPECTS THE CONGRUENCE.**  The "equal four-count" relation absorbs the
idCongr-extended saturated congruence over the Frobenius-monad base relation: every strict axiom preserves
the count (units / whisker-functoriality / whisker-unit by `refl`; associativity via `fourAdd_assoc`;
interchange via `fourAdd_comm`), every one of the twelve critical rows relates equal-count legs (each carries
the same generator multiset on both legs, closed by `rfl`), and the congruence closures propagate
componentwise.  This is the Peiffer-invariance datum — the map + the respects-congruence lemma the
least-congruence UP folds. -/
def frobMonadOmegaFourCountAbsorbs :
    IsSaturatedCongruenceWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
      (fun {_dim : Nat} cellAlpha cellBeta =>
        frobMonadOmegaGeneratorFourCount cellAlpha = frobMonadOmegaGeneratorFourCount cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta row
    cases row with
    | inl strict =>
        cases strict with
        | vcompAssoc a b c => exact fourAdd_assoc _ _ _
        | vcompUnitLeft a => exact fourAdd_zero_left _
        | vcompUnitRight a => exact fourAdd_zero_right _
        | whiskerLeftUnit w c => rfl
        | whiskerRightUnit c w => rfl
        | whiskerLeftFunctorial w b c => rfl
        | whiskerRightFunctorial a b w => rfl
        | interchange a b => exact fourAdd_comm _ _
        | whiskerAssocLeft _ _ _ => rfl
        | whiskerAssocRight _ _ _ => rfl
        | whiskerLeftRightCommute _ _ _ => rfl
    | inr frob =>
        cases frob with
        | monadUnitUnit => rfl
        | monadLeftUnitAssoc => rfl
        | monadRightUnitAssoc => rfl
        | monadPentagon => rfl
        | monadRootUnitAssoc => rfl
        | counitCounit => rfl
        | leftCounitCoassoc => rfl
        | rightCounitCoassoc => rfl
        | copentagon => rfl
        | rootCounitCoassoc => rfl
        | frobLeft => rfl
        | frobRight => rfl
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun z => fourAdd z (frobMonadOmegaGeneratorFourCount cellBeta)) hconv
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun z => fourAdd (frobMonadOmegaGeneratorFourCount cellAlpha) z) hconv
  whiskerLeftCongr := by intro _dim _w _cellBeta _cellBeta' hconv; exact hconv
  whiskerRightCongr := by intro _dim _cellAlpha _cellAlpha' _w hconv; exact hconv
  idCongr := by intro _dim _cellAlpha _cellBeta _hconv; rfl
  whiskerLeftWhiskerCongr := by intro _dim _wA _wA' _inner _hconv; rfl
  whiskerRightWhiskerCongr := by intro _dim _inner _wA _wA' _hconv; rfl
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-! ## Soundness — convertible cells share the four-count -/

/-- ★★ **SOUNDNESS: convertible ⟹ equal four-count.**  Any two cells convertible under the Frobenius-monad
base congruence have the identical generator four-count `(#mu, #eta, #delta, #epsilon)` — the fold of the
respects-congruence lemma through the least-congruence UP `SaturatedConvOverWithId.recInto`.  Machine-checked,
cheap, honestly weak. -/
theorem frobMonadOmegaFourCountSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr frobMonadOmegaComputad dim}
    (conv : SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel cellAlpha cellBeta) :
    frobMonadOmegaGeneratorFourCount cellAlpha = frobMonadOmegaGeneratorFourCount cellBeta :=
  SaturatedConvOverWithId.recInto frobMonadOmegaFourCountAbsorbs conv

/-! ## Exercised — two convertible cells share the invariant, a non-convertible candidate is separated -/

/-- ★ **EXERCISED (convertible ⟹ shared).**  The Frobenius F1 left leg `(s <| delta).(mu |> s)` and the
shared middle `mu . delta` are convertible (the F1 3-cell), so soundness DERIVES their equal four-count —
both `(1, 0, 1, 0)` (one `mu`, one `delta`), obtained from the convertibility, not assumed. -/
theorem frobMonadOmegaFrobLeftCountShared :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaFrobLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaFrobMiddle :=
  frobMonadOmegaFourCountSound frobMonadOmegaFrobLeftThreeCell

/-- ★ **EXERCISED (convertible ⟹ shared, F2).**  The F2 leg and the shared middle share the four-count. -/
theorem frobMonadOmegaFrobRightCountShared :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaFrobRightLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaFrobMiddle :=
  frobMonadOmegaFourCountSound frobMonadOmegaFrobRightThreeCell

/-- ★ The multiplication and the comultiplication have DIFFERENT four-counts (`(1,0,0,0)` vs `(0,0,1,0)`) —
the `#mu` slot separates them. -/
theorem frobMonadOmegaMuDeltaCountDiffers :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaMuGen
      ≠ frobMonadOmegaGeneratorFourCount frobMonadOmegaDeltaGen := by
  intro hcount
  exact Nat.noConfusion (congrArg (fun fourVector => fourVector.1) hcount)

/-- ★★ **EXERCISED (separation).**  `mu` and `delta` are NOT convertible under the Frobenius-monad
congruence — the four-count separates them (were they convertible, soundness would force equal counts, but
`(1,0,0,0) ≠ (0,0,1,0)`).  The soundness invariant is genuinely discriminating: it refutes a candidate
convertibility. -/
theorem frobMonadOmegaMuDeltaNotConvertible :
    ¬ SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
        frobMonadOmegaMuGen frobMonadOmegaDeltaGen :=
  fun conv => frobMonadOmegaMuDeltaCountDiffers (frobMonadOmegaFourCountSound conv)

/-! ## The B3 honesty marker -/

/-- ★ **ESTABLISHED (B3).**  The generator four-count `(#mu, #eta, #delta, #epsilon)`
(`frobMonadOmegaGeneratorFourCount`) is a machine-checked, congruence-respecting soundness invariant: the
respects-congruence lemma (`frobMonadOmegaFourCountAbsorbs`) folds through the least-congruence UP into
soundness (`frobMonadOmegaFourCountSound`, convertible ⟹ equal count), exercised BOTH ways — two convertible
cells share the invariant (`frobMonadOmegaFrobLeftCountShared`) and a non-convertible candidate is separated
(`frobMonadOmegaMuDeltaNotConvertible`).  Honestly weak (does not separate `mu.delta` from `delta.mu`) and
sound only because the bare walking Frobenius monad has no special law `mu.delta = id`.  `= true`. -/
def fxFrob_soundInvariantShipped : Bool := true

/-! # =========================================================================================
    # B4 — THE DECISION LEDGER (honest scope) + the ambijunction framing + the census feed
    # =========================================================================================

★ **The honest r1 scope: the soundness invariant is SHIPPED; completeness / decision is NAMED at the
`TwoCategory/Frobenius` TL-bridge, NOT shipped; no 2Cob / TL overclaim.**

## Soundness (SHIPPED, Omega lane)

Convertible 2-cells ⟹ equal four-count (`frobMonadOmegaFourCountSound`).  Weak but genuine,
congruence-respecting (`frobMonadOmegaFourCountAbsorbs`), machine-checked, exercised both ways.

## Completeness (NOT shipped — NAMED at the TL / Cospan bridge, walled at TWO named nodes)

The `TwoCategory/Frobenius/SpiderCompleteness` lane DECIDES a Frobenius word problem
(`spiderConv_iff_extraEq` + `instDecidableSpiderConv`) via a corelation partition invariant — BUT for the
EXTRASPECIAL-COMMUTATIVE theory (a symmetry `sigma` + commutativity / cocommutativity + special + bone).
The bare walking Frobenius MONAD here is NON-COMMUTATIVE (no `sigma`), so that decision does NOT transfer.
It is walled at two named nodes:

  1. **Non-commutativity** — the `S_n` / comb leg-straightening the TwoCategory lane proves avoidable is
     avoidable ONLY because of commutativity ("commutativity / cocommutativity make leg-permutations a
     LOCAL bounded absorption"); without `sigma` this is the still-open `BRAUER-BREACH` node.
  2. **Genus (2Cob)** — the plain (non-special) Frobenius PROP is `2Cob` = partition + genus-per-block, and
     genus is UNBUILT in every lane (the TwoCategory lane ledgers `fxFrob_has2CobGenus = false`).  The
     handle / genus operator is `epsilon . mu . delta . eta : id => id` (diagrammatic order); in the
     commutative case `hom(id, id)` is free on this handle (Abrams NF), but the Omega walker is
     non-commutative a priori, so completeness there is genuinely open.

The full separating invariant is (a) a union-find port-partition engine — exactly the
`TwoCategory/Frobenius/PartitionModel` (`extraSpiderDiagramOf`, Cospan(FinSet) / corelation) — NAMED, not
rebuilt (importing it into Omega is forbidden); plus (b) a per-block genus counter — a shared future wall,
not an r1 deliverable in ANY lane.

## The ambijunction framing (Street 2004, NAMED)

A Frobenius monad is exactly an AMBIDEXTROUS adjunction ("ambijunction"): `mu / eta` present `s.s -| s` while
`delta / epsilon` present `s -| s.s`, and the Frobenius law is the compatibility making the two adjunctions
share a unit / counit — Street, *Frobenius monads and pseudomonoids* (JMP 45, 2004).  The two Frobenius rows
F1 / F2 shipped here ARE that compatibility.  This is the framing, NAMED (the ambijunction's biadjoint
snake equations are the OMEGA-5 higher-coherence handoff, not an r1 deliverable).

## Self-op-duality (docstring free-rider, per the walking-equivalence precedent)

The walking Frobenius monad is SELF-OP-DUAL up to the relabeling `mu <-> delta`, `eta <-> epsilon`: `op`
sends the monad-internal rows to the comonad-internal rows and fixes the two Frobenius rows (up to the
relabeling), so the op-dual walker is a free-rider on the same presentation.  This is a docstring
observation only — NOT an `op`-transport of the comonad rows (which would be a type mismatch: `op mu` is a
mu-labeled cell, not the delta-labeled generator), exactly why the comonad half was declared natively in B2.

## Census feed (B4)

The single-object walking Frobenius MONAD is fed additively into `SquierFamilyCensus` (a
`SquierFamilyFrobeniusWalker` entry grounded in `frobMonadWalkerCoherentPresentation`), WITHOUT touching the
decided-9 count or the `fxOmega4_multiObjectWalkersOutsideDecidedNineR2` marker — that marker is correct for
the multi-object Frobenius PROP but the single-object Frobenius MONAD is a DISTINCT walker, recorded by a NEW
census marker. -/

/-- ★★ **ESTABLISHED (r1 summary).**  The walking Frobenius monad
`<s | mu, eta, delta, epsilon | monad + comonad + two Frobenius rows>` re-encoded as an `OmegaComputad`
2-polygraph: FOUR 2-cell generators, TWELVE critical-pair rows (5 monad transported + 5 comonad op-mirror
native + 2 Frobenius refl-joined), all coherently resolved modulo strict
(`frobMonadWalkerCoherentPresentation`), the least-congruence UP
(`frobMonadCriticalPairsIdentifiedInEveryModel`), and a machine-checked four-count soundness invariant
(`frobMonadOmegaFourCountSound`).  `= true`. -/
def fxFrob_walkingFrobeniusMonadPresentationShipped : Bool := true

/-- ★ **NAMED-OUT (not shipped) — genus + matching completeness.**  `= false` records that the full
separating (completeness-grade) invariant — the port-partition matching (`TwoCategory/Frobenius/PartitionModel`
Cospan / corelation engine) plus a per-block genus counter — is NAMED to the `TwoCategory/Frobenius` bridge,
NOT shipped in the Omega lane (importing the engine is forbidden; genus is unbuilt in every lane,
`fxFrob_has2CobGenus = false` in the TwoCategory ledger).  The Omega r1 ships the WEAK four-count only. -/
def fxFrob_genusMatchingCompletenessNamedNotShipped : Bool := false

/-- ★ **WALL — the bare walker's decision stays walled (honest).**  `= false` records that the full 2-cell
word-problem DECISION for the bare (non-commutative, non-special) walking Frobenius monad is NOT shipped:
the `TwoCategory/Frobenius/SpiderCompleteness` decision (`instDecidableSpiderConv`) is for the
EXTRASPECIAL-COMMUTATIVE theory and does NOT transfer, walled at two named nodes — non-commutativity (the
open `BRAUER-BREACH`) and 2Cob-genus (`fxFrob_has2CobGenus = false`).  No 2Cob / TL overclaim. -/
def fxFrob_completenessWalledAtNonCommutativityAndGenus : Bool := false

/-- ★ **THE AMBIJUNCTION FRAMING (Street 2004, NAMED).**  `= true` records that the walking Frobenius monad
is framed as an AMBIDEXTROUS adjunction: `mu / eta` present `s.s -| s`, `delta / epsilon` present `s -| s.s`,
and the two shipped Frobenius rows F1 / F2 (`frobMonadTwoFrobeniusRowsResolved`) ARE the compatibility making
the two adjunctions a Frobenius pair (Street, *Frobenius monads and pseudomonoids*).  The framing is NAMED;
the ambijunction's higher snake coherences are the OMEGA-5 handoff. -/
def fxFrob_ambijunctionFramingNamed : Bool := true

/-- ★ **WALL / OMEGA-5 HANDOFF (honest).**  `= false` records that the FULL homotopy basis for the walking
Frobenius monad — every parallel 2-path pair 3-cell-homotopic, by a structural length-fuel 2-path normalizer
one dimension up — is NOT reached this round, exactly as every walker deferred it
(`fxOmega4_walkingMonadFullHomotopyBasisReached`, `fxDistLaw_fullHomotopyBasisReached`).  The shipped content
is the twelve generating 3-cells + their peak / valley joins, not the closure of every 2-sphere. -/
def fxFrob_fullHomotopyBasisReached : Bool := false

end FX1Poly.Polygraph.Omega
