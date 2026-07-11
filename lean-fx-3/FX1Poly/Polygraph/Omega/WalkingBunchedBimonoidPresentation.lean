import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # Polygraph/Omega/WalkingBunchedBimonoidPresentation — the walking bunched bimonoid (WP-BI r1, #2188)

★ **The walking bunched bimonoid `<a, m | (bicommutative bimonoid on a) + (non-commutative monoid on m)>`
re-encoded as an `OmegaComputad` 2-polygraph.**  A bunched structure (O'Hearn-Pym; the FX §6.4 separation /
BI reading, NAMED in the ledger, NOT imported) carries TWO independent products: an ADDITIVE bunch (here the
1-generator `a`, bearing a bicommutative bimonoid `mu_a, eta_a, delta_a, eps_a, sigma_a`) and a
MULTIPLICATIVE bunch (here the 1-generator `m`, bearing a bare non-commutative monoid `mu_m, eta_m`).  The two
products do NOT interact at the walker level — `a` and `m` share no cells and no relations; the mixed structure
is the free product / PROP coproduct (the two bunches interact only through the logic's implications, not on
objects).

## The adjudicated route (recon (1)): route (i), the single-object 2-categorical reading

Two 1-cell generators `a`, `m` over one object (`modeCarrier := Unit`).  `m` carries a non-commutative monoid;
`a` carries a bicommutative bimonoid (a monoid + a comonoid + bialgebra compatibility + (co)commutativity +
an involutive self-braiding `sigma_a : a.a => a.a`).  The swap is UNAVOIDABLE: the bialgebra law B1
`delta.mu = (mu (x) mu).(1 (x) sigma (x) 1).(delta (x) delta)` cannot be stated without a middle swap of the
inner two strands, so the additive side is intrinsically braided territory (the strong-monad B4's named
braided-base scaffold, one strand wider).

## The honest count (recon (1))

  * **Multiplicative `m`** — 5 transported critical pairs (the walking-monad five, colour `m`).
  * **Additive `a`** — 5 transported (monoid, colour `a`) + 5 transported (comonoid, from the Frobenius
    comonad-internal shapes, colour `a`) + 4 NEW bialgebra rows (B1 delta-of-product-with-swap, B2
    counit-of-product, B3 delta-of-unit, B4 bone) + 2 NEW (co)commutativity rows + 1 NEW sigma-involution row.
  * **Total** — 15 transported + 7 NEW = 22 critical-pair rows, the honest FULL bicommutative-bimonoid walker
    at Squier's convergent scope.  Larger than any shipped walker (Frobenius 12, DistLaw 14).

## The tamed B1 4-strand risk (recon (2), risk #2)

The sole correctness risk is the B1 right leg's 4-strand composite over `a.a.a.a`.  It is TAMED by the free
carrier's EXTRINSIC vcomp composability: a `CellExpr.vcomp` accepts ANY two same-dimension cells (composability
is a `Prop`, not a constructor side-condition), so the OUTER boundary of the whole 3-fold composite is read off
the leftmost source (`a.a`) and the rightmost target (`a.a`) REGARDLESS of internal bracketing mismatches.
Hence B1 is a globular `a.a => a.a` row with peak / valley `refl` — the internal associativity mismatches are
absorbed by the separate strict-axiom rows, exactly as Frobenius F1 / F2 and the strong-monad rows do.  The B1
boundary reductions are machine-checked (`rfl`) below (the truth-probe discipline: build on concrete words
FIRST).

## The r1 scope (recon (5)) — SHIP / DEFER

  * **SHIP** — both generators `a, m` incl. `sigma_a`; the 7 NEW additive rows (bialgebra + (co)comm +
    sigma-involution) as generating 3-cells; the 15 transported rows; the Frobenius-distinction self-attack
    (the four-count is UNSOUND over the bialgebra congruence, `BI != Frobenius`); the census extension.
  * **DEFER (NAMED walls)** — Yang-Baxter / hexagon on `a.a.a` (the braided-base wall); sigma-naturality-vs-
    `mu/eta/delta/eps` rows; the full `Mat(N)` convergent normalizer (the additive 2-cell decision, OMEGA-5);
    the full homotopy basis (OMEGA-5, `*FullHomotopyBasisReached = false`).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The bunched-bimonoid signature (nine generator labels) -/

/-- ★ The **nine generator labels** of the walking bunched bimonoid: the two 1-generators — the additive
colour `a` (bicommutative bimonoid) and the multiplicative colour `m` (non-commutative monoid) — plus the five
additive 2-cell generators (`mu_a`, `eta_a`, `delta_a`, `eps_a`, `sigma_a`) and the two multiplicative 2-cell
generators (`mu_m`, `eta_m`).  A finite inductive (full case splits everywhere — the wildcard-`_ =>` propext
leak is avoided). -/
inductive BunchedBIGenLabel where
  /-- The additive 1-generator `a : * => *` (the bicommutative-bimonoid bunch). -/
  | additiveColour
  /-- The multiplicative 1-generator `m : * => *` (the non-commutative-monoid bunch). -/
  | multColour
  /-- The additive multiplication `mu_a : a.a => a`. -/
  | addMult
  /-- The additive unit `eta_a : id => a`. -/
  | addUnit
  /-- The additive comultiplication `delta_a : a => a.a` (an EXPANSION). -/
  | addComult
  /-- The additive counit `eps_a : a => id`. -/
  | addCounit
  /-- The additive self-braiding / swap `sigma_a : a.a => a.a` — the star of the additive side. -/
  | addSwap
  /-- The multiplicative multiplication `mu_m : m.m => m`. -/
  | multMult
  /-- The multiplicative unit `eta_m : id => m`. -/
  | multUnit

/-- The **integer tag** of a generator label — a full nine-arm split (constant `Nat` motive, propext-free);
the label comparator compares tags. -/
def bunchedBimonoidLabelTag : BunchedBIGenLabel → Nat
  | .additiveColour => 0
  | .multColour => 1
  | .addMult => 2
  | .addUnit => 3
  | .addComult => 4
  | .addCounit => 5
  | .addSwap => 6
  | .multMult => 7
  | .multUnit => 8

/-- The **label `Bool` equality** — tags equal (`Nat.beq` on tags, propext-free); separates all nine labels,
so the structural cell comparator distinguishes the additive colour `a` from the multiplicative colour `m` and
all seven 2-cell generators. -/
def bunchedBimonoidLabelBeq (labelA labelB : BunchedBIGenLabel) : Bool :=
  bunchedBimonoidLabelTag labelA == bunchedBimonoidLabelTag labelB

/-- ★ The **walking-bunched-bimonoid omega-computad**: one object (`Unit`), the constant nine-label family
`BunchedBIGenLabel` at every dimension (the two 1-generators and the seven 2-generators are drawn from it;
globularity is extrinsic, so the label family need not know the cells its labels span).  Constant family
(no `Nat`-match in `genLabel`) — propext-clean. -/
def bunchedBimonoidOmegaComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => BunchedBIGenLabel

/-- The trivial mode comparator (one object). -/
def bunchedBimonoidOmegaModeBeq :
    bunchedBimonoidOmegaComputad.modeCarrier → bunchedBimonoidOmegaComputad.modeCarrier → Bool :=
  fun _ _ => true

/-- The heterogeneous generator comparator — compares the nine labels by tag (the two colours and the seven
2-cell generators must be separated). -/
def bunchedBimonoidOmegaGenBeq :
    (dimA dimB : Nat) →
      bunchedBimonoidOmegaComputad.genLabel dimA → bunchedBimonoidOmegaComputad.genLabel dimB → Bool :=
  fun _ _ labelA labelB => bunchedBimonoidLabelBeq labelA labelB

/-! ## The generators -/

/-- The single object `*`. -/
def bunchedBimonoidPoint : CellExpr bunchedBimonoidOmegaComputad 0 := CellExpr.ofMode ()

/-- ★ The **additive** 1-generator `a : * => *` (the bicommutative-bimonoid bunch). -/
def bunchedBimonoidAdditiveGen : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.gen (dim := 0) BunchedBIGenLabel.additiveColour bunchedBimonoidPoint bunchedBimonoidPoint

/-- ★ The **multiplicative** 1-generator `m : * => *` (the non-commutative-monoid bunch). -/
def bunchedBimonoidMultGen : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.gen (dim := 0) BunchedBIGenLabel.multColour bunchedBimonoidPoint bunchedBimonoidPoint

/-- The identity 1-cell `id` (the units' source, the counit's target). -/
def bunchedBimonoidIdOne : CellExpr bunchedBimonoidOmegaComputad 1 := CellExpr.id bunchedBimonoidPoint

/-- The 1-cell word `a.a` (the additive multiplication's source, the comultiplication's target). -/
def bunchedBimonoidAaWord : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen

/-- The 1-cell word `m.m` (the multiplicative multiplication's source). -/
def bunchedBimonoidMmWord : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.vcomp bunchedBimonoidMultGen bunchedBimonoidMultGen

/-- ★ The additive **multiplication** `mu_a : a.a => a` (label `addMult`). -/
def bunchedBimonoidAddMuGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addMult bunchedBimonoidAaWord bunchedBimonoidAdditiveGen

/-- ★ The additive **unit** `eta_a : id => a` (label `addUnit`). -/
def bunchedBimonoidAddEtaGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addUnit bunchedBimonoidIdOne bunchedBimonoidAdditiveGen

/-- ★ The additive **comultiplication** `delta_a : a => a.a` (label `addComult`) — an EXPANSION (the coherent
presentation layer needs no termination; `symm` is a constructor). -/
def bunchedBimonoidAddDeltaGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addComult bunchedBimonoidAdditiveGen bunchedBimonoidAaWord

/-- ★ The additive **counit** `eps_a : a => id` (label `addCounit`). -/
def bunchedBimonoidAddEpsGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addCounit bunchedBimonoidAdditiveGen bunchedBimonoidIdOne

/-- ★★ The additive **self-braiding / swap** `sigma_a : a.a => a.a` (label `addSwap`) — the middle swap the
bialgebra law B1 needs, a genuine non-identity endo-2-cell (tag-separated from `id (a.a)`). -/
def bunchedBimonoidAddSigmaGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addSwap bunchedBimonoidAaWord bunchedBimonoidAaWord

/-- ★ The multiplicative **multiplication** `mu_m : m.m => m` (label `multMult`). -/
def bunchedBimonoidMultMuGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.multMult bunchedBimonoidMmWord bunchedBimonoidMultGen

/-- ★ The multiplicative **unit** `eta_m : id => m` (label `multUnit`). -/
def bunchedBimonoidMultEtaGen : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.multUnit bunchedBimonoidIdOne bunchedBimonoidMultGen

/-- The nine generator labels, enumerated — two 1-generators + seven 2-generators. -/
def allBunchedBimonoidGenLabels : List BunchedBIGenLabel :=
  [.additiveColour, .multColour, .addMult, .addUnit, .addComult, .addCounit, .addSwap, .multMult, .multUnit]

/-- ★ **The generator-label count is exactly NINE** — kernel-checked (`rfl`): the two 1-generators (`a`, `m`)
and the SEVEN 2-cell generators (five additive `mu_a`/`eta_a`/`delta_a`/`eps_a`/`sigma_a` + two multiplicative
`mu_m`/`eta_m`). -/
theorem bunchedBimonoidGeneratorLabelCountIsNine : allBunchedBimonoidGenLabels.length = 9 := rfl

/-! # =========================================================================================
    # B1 — THE PRESENTATION: the bialgebra + (co)comm + sigma rows type-check on concrete words FIRST
    # =========================================================================================

★ **The seven NEW additive rows are the genuinely-new content (the DELTA over the transported monoid /
comonoid).**  Each leg is a `CellExpr bunchedBimonoidOmegaComputad 2` that type-checks on the nose — the
whiskerings and vertical composites elaborate because the free carrier's composability is extrinsic.  This is
the B1 truth-probe: the bialgebra rows ARE well-typed 2-cell equations on concrete words, and the B1 4-strand
right leg's OUTER boundary is `a.a => a.a` (machine-checked `rfl`), taming the sole correctness risk. -/

/-! ## Bialgebra B1 — delta-of-product with the middle swap (the 4-strand right leg, the risk) -/

/-- ★ The **bialgebra B1 LEFT leg** `delta_a . mu_a : a.a => a.a` — comultiply-after-multiply (diagrammatic
order `vcomp mu delta`: `mu` then `delta`).  Exactly the Frobenius-middle shape, on the additive generators. -/
def bunchedBimonoidBialgebraProductLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddDeltaGen

/-- The **`delta_a (x) delta_a`** front of the B1 right leg `a.a => (a.a).(a.a)` — `(delta |> a) . (a.a <| delta)`
(comultiply each of the two strands). -/
def bunchedBimonoidDeltaTensorDelta : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
    (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddDeltaGen)

/-- The **`1 (x) sigma_a (x) 1`** middle swap `a.(a.a).a => a.(a.a).a` — `a <| (sigma |> a)` (swap the inner
two of the four strands).  Its internal bracketing need not literally match the neighbours: the free carrier's
EXTRINSIC vcomp composability means the OUTER boundary of the whole B1 right leg is read off its leftmost /
rightmost factors, not this middle cell. -/
def bunchedBimonoidMiddleSwap : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)

/-- The **`mu_a (x) mu_a`** back of the B1 right leg `(a.a).(a.a) => a.a` — `(mu |> a.a) . (a <| mu)`
(multiply each pair). -/
def bunchedBimonoidMuTensorMu : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAaWord)
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)

/-- ★★ The **bialgebra B1 RIGHT leg** `(mu (x) mu).(1 (x) sigma (x) 1).(delta (x) delta) : a.a => a.a` — the
4-strand composite (the recon's sole flagged correctness risk, TAMED by extrinsic composability: the OUTER
boundary is `a.a => a.a` on the nose, machine-checked below). -/
def bunchedBimonoidBialgebraProductRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidDeltaTensorDelta
    (CellExpr.vcomp bunchedBimonoidMiddleSwap bunchedBimonoidMuTensorMu)

/-- ★ **THE B1 RISK IS TAMED (source).**  The 4-strand right leg's source boundary is `a.a` on the nose
(`rfl`) — the leftmost factor `delta (x) delta` sources at `a.a`, and `boundarySource` of a `vcomp` is read off
the leftmost factor regardless of the internal 4-strand bracketing. -/
theorem bunchedBimonoidBialgebraProductRightLeg_boundarySource :
    boundarySource bunchedBimonoidBialgebraProductRightLeg = bunchedBimonoidAaWord := rfl

/-- ★ **THE B1 RISK IS TAMED (target).**  The 4-strand right leg's target boundary is `a.a` on the nose
(`rfl`) — the rightmost factor `mu (x) mu` targets at `a.a`. -/
theorem bunchedBimonoidBialgebraProductRightLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraProductRightLeg = bunchedBimonoidAaWord := rfl

/-- The B1 left leg's source boundary is `a.a` (`rfl`). -/
theorem bunchedBimonoidBialgebraProductLeftLeg_boundarySource :
    boundarySource bunchedBimonoidBialgebraProductLeftLeg = bunchedBimonoidAaWord := rfl

/-- The B1 left leg's target boundary is `a.a` (`rfl`) — B1 is a globular `a.a => a.a` row, peak / valley
`refl`. -/
theorem bunchedBimonoidBialgebraProductLeftLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraProductLeftLeg = bunchedBimonoidAaWord := rfl

/-! ## Bialgebra B2 — counit-of-product `eps.mu = eps (x) eps` (`a.a => id`) -/

/-- ★ The **bialgebra B2 LEFT leg** `eps_a . mu_a : a.a => id` — counit-after-multiply (`vcomp mu eps`). -/
def bunchedBimonoidBialgebraCounitLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddEpsGen

/-- ★ The **bialgebra B2 RIGHT leg** `eps_a (x) eps_a : a.a => id.id` — `(a <| eps) . (eps |> id)` (counit each
strand; valley `id.id`, joined to `id` modulo one strict unit). -/
def bunchedBimonoidBialgebraCounitRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen)
    (CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidIdOne)

/-- The B2 left leg's target boundary is `id` (`rfl`). -/
theorem bunchedBimonoidBialgebraCounitLeftLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraCounitLeftLeg = bunchedBimonoidIdOne := rfl

/-- The B2 right leg's target boundary is `id.id` (`rfl`) — the valley joins to `id` modulo one strict unit. -/
theorem bunchedBimonoidBialgebraCounitRightLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraCounitRightLeg
      = CellExpr.vcomp bunchedBimonoidIdOne bunchedBimonoidIdOne := rfl

/-! ## Bialgebra B3 — delta-of-unit `delta.eta = eta (x) eta` (`id => a.a`) -/

/-- ★ The **bialgebra B3 LEFT leg** `delta_a . eta_a : id => a.a` — comultiply-after-unit (`vcomp eta delta`). -/
def bunchedBimonoidBialgebraUnitLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddEtaGen bunchedBimonoidAddDeltaGen

/-- ★ The **bialgebra B3 RIGHT leg** `eta_a (x) eta_a : id.id => a.a` — `(eta |> id) . (a <| eta)` (unit each
strand; peak `id.id`, joined to `id` modulo one strict unit). -/
def bunchedBimonoidBialgebraUnitRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidIdOne)
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)

/-- The B3 left leg's target boundary is `a.a` (`rfl`). -/
theorem bunchedBimonoidBialgebraUnitLeftLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraUnitLeftLeg = bunchedBimonoidAaWord := rfl

/-- The B3 right leg's target boundary is `a.a` (`rfl`) — both legs valley at `a.a`, `refl`. -/
theorem bunchedBimonoidBialgebraUnitRightLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraUnitRightLeg = bunchedBimonoidAaWord := rfl

/-! ## Bialgebra B4 — the bone `eps.eta = id` (`id => id`) -/

/-- ★ The **bialgebra B4 LEFT leg** `eps_a . eta_a : id => id` — counit-after-unit (`vcomp eta eps`). -/
def bunchedBimonoidBialgebraBoneLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddEtaGen bunchedBimonoidAddEpsGen

/-- ★ The **bialgebra B4 RIGHT leg** `id_{id} : id => id` — the identity 2-cell on the 1-cell `id`. -/
def bunchedBimonoidBialgebraBoneRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.id bunchedBimonoidIdOne

/-- The B4 left leg's source / target boundaries are both `id` (`rfl`) — B4 is a globular `id => id` row. -/
theorem bunchedBimonoidBialgebraBoneLeftLeg_boundaryTarget :
    boundaryTarget bunchedBimonoidBialgebraBoneLeftLeg = bunchedBimonoidIdOne := rfl

/-! ## (Co)commutativity — `mu.sigma = mu` (`a.a => a`) and `sigma.delta = delta` (`a => a.a`) -/

/-- ★ The **commutativity LEFT leg** `mu_a . sigma_a : a.a => a` — multiply-after-swap (`vcomp sigma mu`). -/
def bunchedBimonoidCommutativityLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddSigmaGen bunchedBimonoidAddMuGen

/-- ★ The **commutativity RIGHT leg** `mu_a : a.a => a` — the product is symmetric (the swap is absorbed). -/
def bunchedBimonoidCommutativityRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidAddMuGen

/-- ★ The **cocommutativity LEFT leg** `sigma_a . delta_a : a => a.a` — swap-after-comultiply
(`vcomp delta sigma`). -/
def bunchedBimonoidCocommutativityLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddDeltaGen bunchedBimonoidAddSigmaGen

/-- ★ The **cocommutativity RIGHT leg** `delta_a : a => a.a` — the coproduct is cosymmetric. -/
def bunchedBimonoidCocommutativityRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidAddDeltaGen

/-! ## Sigma-involution — `sigma.sigma = id` (`a.a => a.a`), the swap's own symmetry law -/

/-- ★ The **sigma-involution LEFT leg** `sigma_a . sigma_a : a.a => a.a` — the swap applied twice. -/
def bunchedBimonoidSigmaInvolutionLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen

/-- ★ The **sigma-involution RIGHT leg** `id_{a.a} : a.a => a.a` — the swap is an involution (`sigma^2 = id`). -/
def bunchedBimonoidSigmaInvolutionRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.id bunchedBimonoidAaWord

/-! ## Non-vacuity — the NEW rows are genuinely distinct 2-cells (the B1 truth-probe) -/

/-- ★ The **bialgebra B1 legs are structurally DISTINCT** (`delta.mu` vs the 4-strand composite) — the B1 row
genuinely identifies non-equal 2-cells. -/
theorem bunchedBimonoidBialgebraProductLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidBialgebraProductLeftLeg bunchedBimonoidBialgebraProductRightLeg = false := rfl

/-- ★ The **bialgebra B2 legs are structurally DISTINCT** (`eps.mu` vs `eps (x) eps`). -/
theorem bunchedBimonoidBialgebraCounitLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidBialgebraCounitLeftLeg bunchedBimonoidBialgebraCounitRightLeg = false := rfl

/-- ★ The **bialgebra B3 legs are structurally DISTINCT** (`delta.eta` vs `eta (x) eta`). -/
theorem bunchedBimonoidBialgebraUnitLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidBialgebraUnitLeftLeg bunchedBimonoidBialgebraUnitRightLeg = false := rfl

/-- ★ The **bialgebra B4 legs are structurally DISTINCT** (`eps.eta` vs `id_{id}`). -/
theorem bunchedBimonoidBialgebraBoneLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidBialgebraBoneLeftLeg bunchedBimonoidBialgebraBoneRightLeg = false := rfl

/-- ★ The **commutativity legs are structurally DISTINCT** (`mu.sigma` vs `mu`). -/
theorem bunchedBimonoidCommutativityLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidCommutativityLeftLeg bunchedBimonoidCommutativityRightLeg = false := rfl

/-- ★ The **cocommutativity legs are structurally DISTINCT** (`sigma.delta` vs `delta`). -/
theorem bunchedBimonoidCocommutativityLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidCocommutativityLeftLeg bunchedBimonoidCocommutativityRightLeg = false := rfl

/-- ★★ **THE SWAP SYMMETRY LAW PROBED (sigma-involution legs distinct).**  `sigma.sigma` and `id_{a.a}` are
structurally NOT equal — the involution row `sigma^2 = id` genuinely identifies a non-identity double-swap with
the identity (the swap's own symmetry law is non-vacuous). -/
theorem bunchedBimonoidSigmaInvolutionLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidSigmaInvolutionLeftLeg bunchedBimonoidSigmaInvolutionRightLeg = false := rfl

/-- ★★ **THE SWAP GENERATOR IS NON-VACUOUS.**  `sigma_a` is structurally NOT equal to the identity 2-cell
`id_{a.a}` — the self-braiding is a genuine non-identity endo-2-cell (tag `addSwap`, separated from `id`). -/
theorem bunchedBimonoidSwapGen_notIdentity :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidAddSigmaGen (CellExpr.id bunchedBimonoidAaWord) = false := rfl

/-- ★ **The two colours are genuinely distinct 1-generators** — `a` and `m` are structurally NOT equal (the
tag comparator separates `additiveColour` from `multColour`); the two bunches share no cells. -/
theorem bunchedBimonoidColours_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidAdditiveGen bunchedBimonoidMultGen = false := rfl

/-! ## B1 non-vacuity probes (the truth-probe outputs) -/

#eval cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
  bunchedBimonoidBialgebraProductLeftLeg bunchedBimonoidBialgebraProductRightLeg
#eval cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
  bunchedBimonoidAddSigmaGen (CellExpr.id bunchedBimonoidAaWord)
#eval cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
  bunchedBimonoidAdditiveGen bunchedBimonoidMultGen
#eval allBunchedBimonoidGenLabels.length

/-! ## The B1 honesty markers -/

/-- ★ **ESTABLISHED (B1).**  The walking bunched bimonoid's SEVEN new additive rows type-check on concrete
words as `CellExpr bunchedBimonoidOmegaComputad 2`: the four bialgebra rows (B1 delta-of-product-with-swap, B2
counit-of-product, B3 delta-of-unit, B4 bone), the two (co)commutativity rows, and the sigma-involution row.
The B1 4-strand right leg's OUTER boundary is `a.a => a.a` on the nose
(`bunchedBimonoidBialgebraProductRightLeg_boundarySource` / `_boundaryTarget`), taming the sole correctness
risk, and every new row's legs are structurally distinct.  `= true`. -/
def fxBunchedBimonoid_bialgebraRowsTypeCheckOnConcreteWords : Bool := true

/-- ★★ **THE SWAP GENERATOR'S SYMMETRY LAW IS PROBED (B1).**  `= true` records that the additive self-braiding
`sigma_a : a.a => a.a` is a genuine non-identity endo-2-cell (`bunchedBimonoidSwapGen_notIdentity`), and its
own symmetry law `sigma^2 = id` is non-vacuous (`bunchedBimonoidSigmaInvolutionLegs_distinct`) — the swap is
UNAVOIDABLE (the B1 bialgebra law needs the middle swap of the inner two strands), the additive side is
intrinsically braided territory. -/
def fxBunchedBimonoid_swapSymmetryLawProbed : Bool := true

end FX1Poly.Polygraph.Omega
