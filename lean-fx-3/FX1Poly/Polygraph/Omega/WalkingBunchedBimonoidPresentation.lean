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

/-! # =========================================================================================
    # B2 — THE 22 CRITICAL-PAIR RESOLUTIONS (15 transported + 7 new), joinable modulo strict
    # =========================================================================================

★ **The walking bunched bimonoid = 5 monoid-`m` + 5 monoid-`a` + 5 comonoid-`a` + 4 bialgebra + 2 (co)comm +
1 sigma-involution = 22 critical-pair rows.**  The 15 transported rows reuse the walking-monad / Frobenius-
comonad leg shapes verbatim (colour `m` / colour `a`); the 7 new rows are the DELTA.  Every row joins modulo
strict at peak and valley: the transported rows by the standard monad / comonad joins, the bialgebra product /
(co)comm / sigma-involution rows by `refl` on both boundaries, and the counit-of-product / delta-of-unit rows
by one strict unit (their `eps (x) eps` / `eta (x) eta` composites land in `id.id`). -/

/-! ## The five monoid-`m` legs (over `m`, `eta_m`, `mu_m`) — the walking monad's five leg shapes -/

/-- monoid-`m` `unitUnit` left leg `eta_m |> m`. -/
def bunchedBimonoidMultMonadUnitUnitLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidMultEtaGen bunchedBimonoidMultGen

/-- monoid-`m` `unitUnit` right leg `m <| eta_m`. -/
def bunchedBimonoidMultMonadUnitUnitRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidMultGen bunchedBimonoidMultEtaGen

/-- monoid-`m` `leftUnitAssoc` left leg `mu_m |> m`. -/
def bunchedBimonoidMultMonadLeftUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidMultMuGen bunchedBimonoidMultGen

/-- monoid-`m` `leftUnitAssoc` right leg `m <| mu_m`. -/
def bunchedBimonoidMultMonadLeftUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidMultGen bunchedBimonoidMultMuGen

/-- monoid-`m` `rightUnitAssoc` left leg `eta_m |> m.m`. -/
def bunchedBimonoidMultMonadRightUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidMultEtaGen bunchedBimonoidMmWord

/-- monoid-`m` `rightUnitAssoc` right leg `m.m <| eta_m`. -/
def bunchedBimonoidMultMonadRightUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidMmWord bunchedBimonoidMultEtaGen

/-- monoid-`m` `pentagon` left leg `(mu_m |> m.m) . (m <| mu_m)`. -/
def bunchedBimonoidMultMonadPentagonLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidMultMuGen bunchedBimonoidMmWord)
    (CellExpr.whiskerLeft bunchedBimonoidMultGen bunchedBimonoidMultMuGen)

/-- monoid-`m` `pentagon` right leg `(m.m <| mu_m) . (mu_m |> m)`. -/
def bunchedBimonoidMultMonadPentagonRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidMmWord bunchedBimonoidMultMuGen)
    (CellExpr.whiskerRight bunchedBimonoidMultMuGen bunchedBimonoidMultGen)

/-- monoid-`m` `rootUnitAssoc` left leg `(mu_m |> id) . (m <| eta_m)`. -/
def bunchedBimonoidMultMonadRootUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidMultMuGen bunchedBimonoidIdOne)
    (CellExpr.whiskerLeft bunchedBimonoidMultGen bunchedBimonoidMultEtaGen)

/-- monoid-`m` `rootUnitAssoc` right leg `(m.m <| eta_m) . (mu_m |> m)`. -/
def bunchedBimonoidMultMonadRootUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidMmWord bunchedBimonoidMultEtaGen)
    (CellExpr.whiskerRight bunchedBimonoidMultMuGen bunchedBimonoidMultGen)

/-! ## The five monoid-`a` legs (over `a`, `eta_a`, `mu_a`) — the same five leg shapes, colour `a` -/

/-- monoid-`a` `unitUnit` left leg `eta_a |> a`. -/
def bunchedBimonoidAddMonadUnitUnitLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidAdditiveGen

/-- monoid-`a` `unitUnit` right leg `a <| eta_a`. -/
def bunchedBimonoidAddMonadUnitUnitRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen

/-- monoid-`a` `leftUnitAssoc` left leg `mu_a |> a`. -/
def bunchedBimonoidAddMonadLeftUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen

/-- monoid-`a` `leftUnitAssoc` right leg `a <| mu_a`. -/
def bunchedBimonoidAddMonadLeftUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen

/-- monoid-`a` `rightUnitAssoc` left leg `eta_a |> a.a`. -/
def bunchedBimonoidAddMonadRightUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidAaWord

/-- monoid-`a` `rightUnitAssoc` right leg `a.a <| eta_a`. -/
def bunchedBimonoidAddMonadRightUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEtaGen

/-- monoid-`a` `pentagon` left leg `(mu_a |> a.a) . (a <| mu_a)`. -/
def bunchedBimonoidAddMonadPentagonLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAaWord)
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)

/-- monoid-`a` `pentagon` right leg `(a.a <| mu_a) . (mu_a |> a)`. -/
def bunchedBimonoidAddMonadPentagonRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddMuGen)
    (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)

/-- monoid-`a` `rootUnitAssoc` left leg `(mu_a |> id) . (a <| eta_a)`. -/
def bunchedBimonoidAddMonadRootUnitAssocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidIdOne)
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)

/-- monoid-`a` `rootUnitAssoc` right leg `(a.a <| eta_a) . (mu_a |> a)`. -/
def bunchedBimonoidAddMonadRootUnitAssocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEtaGen)
    (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)

/-! ## The five comonoid-`a` legs (over `a`, `eps_a`, `delta_a`) — the Frobenius comonad's op-mirror shapes -/

/-- comonoid-`a` `counitCounit` left leg `eps_a |> a`. -/
def bunchedBimonoidComonoidCounitCounitLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAdditiveGen

/-- comonoid-`a` `counitCounit` right leg `a <| eps_a`. -/
def bunchedBimonoidComonoidCounitCounitRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen

/-- comonoid-`a` `leftCounitCoassoc` left leg `delta_a |> a`. -/
def bunchedBimonoidComonoidLeftCounitCoassocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen

/-- comonoid-`a` `leftCounitCoassoc` right leg `a <| delta_a`. -/
def bunchedBimonoidComonoidLeftCounitCoassocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddDeltaGen

/-- comonoid-`a` `rightCounitCoassoc` left leg `eps_a |> a.a`. -/
def bunchedBimonoidComonoidRightCounitCoassocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddEpsGen bunchedBimonoidAaWord

/-- comonoid-`a` `rightCounitCoassoc` right leg `a.a <| eps_a`. -/
def bunchedBimonoidComonoidRightCounitCoassocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEpsGen

/-- comonoid-`a` `copentagon` left leg `(delta_a |> a) . (a.a <| delta_a)`. -/
def bunchedBimonoidComonoidCopentagonLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
    (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddDeltaGen)

/-- comonoid-`a` `copentagon` right leg `(a <| delta_a) . (delta_a |> a.a)`. -/
def bunchedBimonoidComonoidCopentagonRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddDeltaGen)
    (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAaWord)

/-- comonoid-`a` `rootCounitCoassoc` left leg `(delta_a |> a) . (a.a <| eps_a)`. -/
def bunchedBimonoidComonoidRootCounitCoassocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen)
    (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEpsGen)

/-- comonoid-`a` `rootCounitCoassoc` right leg `(a <| eps_a) . (delta_a |> id)`. -/
def bunchedBimonoidComonoidRootCounitCoassocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen)
    (CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidIdOne)

/-! ## The 22 critical-pair rows and the base relation -/

/-- ★ The **twenty-two walking-bunched-bimonoid critical-pair rows** — 5 monoid-`m` + 5 monoid-`a` + 5
comonoid-`a` (transported) + 4 bialgebra + 2 (co)commutativity + 1 sigma-involution (new).  A `CellRelOver`
firing on each overlap's two reduction legs: the walking bunched bimonoid's homotopy basis at Squier's
convergent scope. -/
inductive BunchedBimonoidCriticalRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d → Prop where
  /-- monoid-`m` `unitUnit`. -/
  | multMonadUnitUnit : BunchedBimonoidCriticalRow bunchedBimonoidMultMonadUnitUnitLeftLeg
      bunchedBimonoidMultMonadUnitUnitRightLeg
  /-- monoid-`m` `leftUnitAssoc`. -/
  | multMonadLeftUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidMultMonadLeftUnitAssocLeftLeg
      bunchedBimonoidMultMonadLeftUnitAssocRightLeg
  /-- monoid-`m` `rightUnitAssoc`. -/
  | multMonadRightUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidMultMonadRightUnitAssocLeftLeg
      bunchedBimonoidMultMonadRightUnitAssocRightLeg
  /-- monoid-`m` `pentagon`. -/
  | multMonadPentagon : BunchedBimonoidCriticalRow bunchedBimonoidMultMonadPentagonLeftLeg
      bunchedBimonoidMultMonadPentagonRightLeg
  /-- monoid-`m` `rootUnitAssoc`. -/
  | multMonadRootUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidMultMonadRootUnitAssocLeftLeg
      bunchedBimonoidMultMonadRootUnitAssocRightLeg
  /-- monoid-`a` `unitUnit`. -/
  | addMonadUnitUnit : BunchedBimonoidCriticalRow bunchedBimonoidAddMonadUnitUnitLeftLeg
      bunchedBimonoidAddMonadUnitUnitRightLeg
  /-- monoid-`a` `leftUnitAssoc`. -/
  | addMonadLeftUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidAddMonadLeftUnitAssocLeftLeg
      bunchedBimonoidAddMonadLeftUnitAssocRightLeg
  /-- monoid-`a` `rightUnitAssoc`. -/
  | addMonadRightUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidAddMonadRightUnitAssocLeftLeg
      bunchedBimonoidAddMonadRightUnitAssocRightLeg
  /-- monoid-`a` `pentagon`. -/
  | addMonadPentagon : BunchedBimonoidCriticalRow bunchedBimonoidAddMonadPentagonLeftLeg
      bunchedBimonoidAddMonadPentagonRightLeg
  /-- monoid-`a` `rootUnitAssoc`. -/
  | addMonadRootUnitAssoc : BunchedBimonoidCriticalRow bunchedBimonoidAddMonadRootUnitAssocLeftLeg
      bunchedBimonoidAddMonadRootUnitAssocRightLeg
  /-- comonoid-`a` `counitCounit`. -/
  | comonoidCounitCounit : BunchedBimonoidCriticalRow bunchedBimonoidComonoidCounitCounitLeftLeg
      bunchedBimonoidComonoidCounitCounitRightLeg
  /-- comonoid-`a` `leftCounitCoassoc`. -/
  | comonoidLeftCounitCoassoc : BunchedBimonoidCriticalRow bunchedBimonoidComonoidLeftCounitCoassocLeftLeg
      bunchedBimonoidComonoidLeftCounitCoassocRightLeg
  /-- comonoid-`a` `rightCounitCoassoc`. -/
  | comonoidRightCounitCoassoc : BunchedBimonoidCriticalRow bunchedBimonoidComonoidRightCounitCoassocLeftLeg
      bunchedBimonoidComonoidRightCounitCoassocRightLeg
  /-- comonoid-`a` `copentagon`. -/
  | comonoidCopentagon : BunchedBimonoidCriticalRow bunchedBimonoidComonoidCopentagonLeftLeg
      bunchedBimonoidComonoidCopentagonRightLeg
  /-- comonoid-`a` `rootCounitCoassoc`. -/
  | comonoidRootCounitCoassoc : BunchedBimonoidCriticalRow bunchedBimonoidComonoidRootCounitCoassocLeftLeg
      bunchedBimonoidComonoidRootCounitCoassocRightLeg
  /-- bialgebra B1 (delta-of-product with the middle swap). -/
  | bialgebraProduct : BunchedBimonoidCriticalRow bunchedBimonoidBialgebraProductLeftLeg
      bunchedBimonoidBialgebraProductRightLeg
  /-- bialgebra B2 (counit-of-product). -/
  | bialgebraCounit : BunchedBimonoidCriticalRow bunchedBimonoidBialgebraCounitLeftLeg
      bunchedBimonoidBialgebraCounitRightLeg
  /-- bialgebra B3 (delta-of-unit). -/
  | bialgebraUnit : BunchedBimonoidCriticalRow bunchedBimonoidBialgebraUnitLeftLeg
      bunchedBimonoidBialgebraUnitRightLeg
  /-- bialgebra B4 (the bone `eps.eta = id`). -/
  | bialgebraBone : BunchedBimonoidCriticalRow bunchedBimonoidBialgebraBoneLeftLeg
      bunchedBimonoidBialgebraBoneRightLeg
  /-- commutativity `mu.sigma = mu`. -/
  | commutativity : BunchedBimonoidCriticalRow bunchedBimonoidCommutativityLeftLeg
      bunchedBimonoidCommutativityRightLeg
  /-- cocommutativity `sigma.delta = delta`. -/
  | cocommutativity : BunchedBimonoidCriticalRow bunchedBimonoidCocommutativityLeftLeg
      bunchedBimonoidCocommutativityRightLeg
  /-- sigma-involution `sigma.sigma = id`. -/
  | sigmaInvolution : BunchedBimonoidCriticalRow bunchedBimonoidSigmaInvolutionLeftLeg
      bunchedBimonoidSigmaInvolutionRightLeg

/-- The base relation the 3-cells resolve: the strict omega laws united with the 22 critical-pair rows. -/
def bunchedBimonoidOmegaBaseRel : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad (StrictAxiomRel bunchedBimonoidOmegaComputad)
    BunchedBimonoidCriticalRow

/-! ## The assembled per-pair resolution datum -/

/-- ★ A **coherent resolution** of one bunched-bimonoid critical pair, joinable MODULO the strict congruence:
the two leg SOURCES are convertible (peak), the two legs are convertible (the generating 3-cell), and the two
leg TARGETS are convertible (valley).  Parameterised by the two legs so all 22 pairs share one datum shape. -/
structure BunchedBimonoidCriticalPairResolved {d : Nat}
    (leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad (d + 1)) : Prop where
  /-- The two leg SOURCES are convertible (the peak join). -/
  peakJoined : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
    (boundarySource leftLeg) (boundarySource rightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
    leftLeg rightLeg
  /-- The two leg TARGETS are convertible (the valley join). -/
  valleyJoined : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
    (boundaryTarget leftLeg) (boundaryTarget rightLeg)

/-- Build a per-pair resolution from a single critical row plus its peak / valley joins — the generating 3-cell
is the row fired through `ofRelation`. -/
def bunchedBimonoidResolveRow {d : Nat}
    {leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad (d + 1)}
    (peakJoin : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
      (boundarySource leftLeg) (boundarySource rightLeg))
    (row : BunchedBimonoidCriticalRow leftLeg rightLeg)
    (valleyJoin : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
      (boundaryTarget leftLeg) (boundaryTarget rightLeg)) :
    BunchedBimonoidCriticalPairResolved leftLeg rightLeg :=
  ⟨peakJoin, SaturatedConvOverWithId.ofRelation (Or.inr row), valleyJoin⟩

/-! ## The 22 per-pair resolutions (peak + 3-cell + valley, assembled) -/

/-- monoid-`m` `unitUnit` resolved (peak units, valley refl). -/
theorem bunchedBimonoidMultMonadUnitUnitResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadUnitUnitLeftLeg
      bunchedBimonoidMultMonadUnitUnitRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidMultGen)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidMultGen)))))
    BunchedBimonoidCriticalRow.multMonadUnitUnit
    (SaturatedConvOverWithId.refl _)

/-- monoid-`m` `leftUnitAssoc` resolved (peak assoc, valley refl). -/
theorem bunchedBimonoidMultMonadLeftUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadLeftUnitAssocLeftLeg
      bunchedBimonoidMultMonadLeftUnitAssocRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidMultGen bunchedBimonoidMultGen bunchedBimonoidMultGen)))
    BunchedBimonoidCriticalRow.multMonadLeftUnitAssoc
    (SaturatedConvOverWithId.refl _)

/-- monoid-`m` `rightUnitAssoc` resolved (peak units, valley assoc). -/
theorem bunchedBimonoidMultMonadRightUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadRightUnitAssocLeftLeg
      bunchedBimonoidMultMonadRightUnitAssocRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidMmWord)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidMmWord)))))
    BunchedBimonoidCriticalRow.multMonadRightUnitAssoc
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidMultGen bunchedBimonoidMultGen
          bunchedBimonoidMultGen))))

/-- monoid-`m` `pentagon` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidMultMonadPentagonResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadPentagonLeftLeg
      bunchedBimonoidMultMonadPentagonRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.multMonadPentagon (SaturatedConvOverWithId.refl _)

/-- monoid-`m` `rootUnitAssoc` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidMultMonadRootUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadRootUnitAssocLeftLeg
      bunchedBimonoidMultMonadRootUnitAssocRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.multMonadRootUnitAssoc (SaturatedConvOverWithId.refl _)

/-- monoid-`a` `unitUnit` resolved (peak units, valley refl). -/
theorem bunchedBimonoidAddMonadUnitUnitResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadUnitUnitLeftLeg
      bunchedBimonoidAddMonadUnitUnitRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAdditiveGen)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen)))))
    BunchedBimonoidCriticalRow.addMonadUnitUnit
    (SaturatedConvOverWithId.refl _)

/-- monoid-`a` `leftUnitAssoc` resolved (peak assoc, valley refl). -/
theorem bunchedBimonoidAddMonadLeftUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadLeftUnitAssocLeftLeg
      bunchedBimonoidAddMonadLeftUnitAssocRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen
        bunchedBimonoidAdditiveGen)))
    BunchedBimonoidCriticalRow.addMonadLeftUnitAssoc
    (SaturatedConvOverWithId.refl _)

/-- monoid-`a` `rightUnitAssoc` resolved (peak units, valley assoc). -/
theorem bunchedBimonoidAddMonadRightUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadRightUnitAssocLeftLeg
      bunchedBimonoidAddMonadRightUnitAssocRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAaWord)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAaWord)))))
    BunchedBimonoidCriticalRow.addMonadRightUnitAssoc
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen
          bunchedBimonoidAdditiveGen))))

/-- monoid-`a` `pentagon` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidAddMonadPentagonResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadPentagonLeftLeg
      bunchedBimonoidAddMonadPentagonRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.addMonadPentagon (SaturatedConvOverWithId.refl _)

/-- monoid-`a` `rootUnitAssoc` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidAddMonadRootUnitAssocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadRootUnitAssocLeftLeg
      bunchedBimonoidAddMonadRootUnitAssocRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.addMonadRootUnitAssoc (SaturatedConvOverWithId.refl _)

/-- comonoid-`a` `counitCounit` resolved (peak refl, valley units). -/
theorem bunchedBimonoidComonoidCounitCounitResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidCounitCounitLeftLeg
      bunchedBimonoidComonoidCounitCounitRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.comonoidCounitCounit
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAdditiveGen)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen)))))

/-- comonoid-`a` `leftCounitCoassoc` resolved (peak refl, valley assoc). -/
theorem bunchedBimonoidComonoidLeftCounitCoassocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidLeftCounitCoassocLeftLeg
      bunchedBimonoidComonoidLeftCounitCoassocRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.comonoidLeftCounitCoassoc
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen
        bunchedBimonoidAdditiveGen)))

/-- comonoid-`a` `rightCounitCoassoc` resolved (peak assoc, valley units). -/
theorem bunchedBimonoidComonoidRightCounitCoassocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidRightCounitCoassocLeftLeg
      bunchedBimonoidComonoidRightCounitCoassocRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen
          bunchedBimonoidAdditiveGen))))
    BunchedBimonoidCriticalRow.comonoidRightCounitCoassoc
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAaWord)))
      (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAaWord)))))

/-- comonoid-`a` `copentagon` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidComonoidCopentagonResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidCopentagonLeftLeg
      bunchedBimonoidComonoidCopentagonRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.comonoidCopentagon (SaturatedConvOverWithId.refl _)

/-- comonoid-`a` `rootCounitCoassoc` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidComonoidRootCounitCoassocResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidRootCounitCoassocLeftLeg
      bunchedBimonoidComonoidRootCounitCoassocRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.comonoidRootCounitCoassoc (SaturatedConvOverWithId.refl _)

/-- ★★ bialgebra B1 (delta-of-product with the middle swap) resolved (peak refl, valley refl — the tamed
4-strand row is globular `a.a => a.a`). -/
theorem bunchedBimonoidBialgebraProductResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraProductLeftLeg
      bunchedBimonoidBialgebraProductRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.bialgebraProduct (SaturatedConvOverWithId.refl _)

/-- ★ bialgebra B2 (counit-of-product) resolved (peak refl, valley one strict unit: `id ~ id.id`). -/
theorem bunchedBimonoidBialgebraCounitResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraCounitLeftLeg
      bunchedBimonoidBialgebraCounitRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.bialgebraCounit
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidIdOne))))

/-- ★ bialgebra B3 (delta-of-unit) resolved (peak one strict unit: `id ~ id.id`, valley refl). -/
theorem bunchedBimonoidBialgebraUnitResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraUnitLeftLeg
      bunchedBimonoidBialgebraUnitRightLeg :=
  bunchedBimonoidResolveRow
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidIdOne))))
    BunchedBimonoidCriticalRow.bialgebraUnit (SaturatedConvOverWithId.refl _)

/-- ★ bialgebra B4 (the bone `eps.eta = id`) resolved (peak refl, valley refl). -/
theorem bunchedBimonoidBialgebraBoneResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraBoneLeftLeg
      bunchedBimonoidBialgebraBoneRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.bialgebraBone (SaturatedConvOverWithId.refl _)

/-- ★ commutativity `mu.sigma = mu` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidCommutativityResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidCommutativityLeftLeg
      bunchedBimonoidCommutativityRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.commutativity (SaturatedConvOverWithId.refl _)

/-- ★ cocommutativity `sigma.delta = delta` resolved (peak refl, valley refl). -/
theorem bunchedBimonoidCocommutativityResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidCocommutativityLeftLeg
      bunchedBimonoidCocommutativityRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.cocommutativity (SaturatedConvOverWithId.refl _)

/-- ★★ sigma-involution `sigma.sigma = id` resolved (peak refl, valley refl) — the swap's own symmetry law. -/
theorem bunchedBimonoidSigmaInvolutionResolved :
    BunchedBimonoidCriticalPairResolved bunchedBimonoidSigmaInvolutionLeftLeg
      bunchedBimonoidSigmaInvolutionRightLeg :=
  bunchedBimonoidResolveRow (SaturatedConvOverWithId.refl _)
    BunchedBimonoidCriticalRow.sigmaInvolution (SaturatedConvOverWithId.refl _)

/-! ## The coherent-presentation bundle (the honest-scope statement) -/

/-- ★ **The walking-bunched-bimonoid coherent-presentation statement (honest scope).**  All 22 critical pairs
are coherently resolved modulo the strict congruence — a `Prop` conjunction of the 22 per-pair resolutions
(5 monoid-`m` + 5 monoid-`a` + 5 comonoid-`a` + 4 bialgebra + 2 (co)comm + 1 sigma-involution). -/
def BunchedBimonoidWalkerCoherentPresentationStatement : Prop :=
  BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadUnitUnitLeftLeg
    bunchedBimonoidMultMonadUnitUnitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadLeftUnitAssocLeftLeg
    bunchedBimonoidMultMonadLeftUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadRightUnitAssocLeftLeg
    bunchedBimonoidMultMonadRightUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadPentagonLeftLeg
    bunchedBimonoidMultMonadPentagonRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidMultMonadRootUnitAssocLeftLeg
    bunchedBimonoidMultMonadRootUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadUnitUnitLeftLeg
    bunchedBimonoidAddMonadUnitUnitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadLeftUnitAssocLeftLeg
    bunchedBimonoidAddMonadLeftUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadRightUnitAssocLeftLeg
    bunchedBimonoidAddMonadRightUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadPentagonLeftLeg
    bunchedBimonoidAddMonadPentagonRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidAddMonadRootUnitAssocLeftLeg
    bunchedBimonoidAddMonadRootUnitAssocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidCounitCounitLeftLeg
    bunchedBimonoidComonoidCounitCounitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidLeftCounitCoassocLeftLeg
    bunchedBimonoidComonoidLeftCounitCoassocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidRightCounitCoassocLeftLeg
    bunchedBimonoidComonoidRightCounitCoassocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidCopentagonLeftLeg
    bunchedBimonoidComonoidCopentagonRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidComonoidRootCounitCoassocLeftLeg
    bunchedBimonoidComonoidRootCounitCoassocRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraProductLeftLeg
    bunchedBimonoidBialgebraProductRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraCounitLeftLeg
    bunchedBimonoidBialgebraCounitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraUnitLeftLeg
    bunchedBimonoidBialgebraUnitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraBoneLeftLeg
    bunchedBimonoidBialgebraBoneRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidCommutativityLeftLeg
    bunchedBimonoidCommutativityRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidCocommutativityLeftLeg
    bunchedBimonoidCocommutativityRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidSigmaInvolutionLeftLeg
    bunchedBimonoidSigmaInvolutionRightLeg

/-- ★★ **THE WALKING BUNCHED BIMONOID COHERENT PRESENTATION (22 critical pairs, joinable modulo strict).**
The walking bunched bimonoid `<a, m | bicommutative bimonoid on a + non-commutative monoid on m>` re-encoded as
an `OmegaComputad` 2-polygraph has all 22 Squier critical pairs exhibited as generating 3-cells, each
joinable-modulo-strict at peak and valley — 15 transported (5 monoid-`m` + 5 monoid-`a` + 5 comonoid-`a`) and
7 new (4 bialgebra + 2 (co)commutativity + 1 sigma-involution, the genuinely-new additive content). -/
theorem bunchedBimonoidWalkerCoherentPresentation :
    BunchedBimonoidWalkerCoherentPresentationStatement :=
  ⟨bunchedBimonoidMultMonadUnitUnitResolved, bunchedBimonoidMultMonadLeftUnitAssocResolved,
    bunchedBimonoidMultMonadRightUnitAssocResolved, bunchedBimonoidMultMonadPentagonResolved,
    bunchedBimonoidMultMonadRootUnitAssocResolved, bunchedBimonoidAddMonadUnitUnitResolved,
    bunchedBimonoidAddMonadLeftUnitAssocResolved, bunchedBimonoidAddMonadRightUnitAssocResolved,
    bunchedBimonoidAddMonadPentagonResolved, bunchedBimonoidAddMonadRootUnitAssocResolved,
    bunchedBimonoidComonoidCounitCounitResolved, bunchedBimonoidComonoidLeftCounitCoassocResolved,
    bunchedBimonoidComonoidRightCounitCoassocResolved, bunchedBimonoidComonoidCopentagonResolved,
    bunchedBimonoidComonoidRootCounitCoassocResolved, bunchedBimonoidBialgebraProductResolved,
    bunchedBimonoidBialgebraCounitResolved, bunchedBimonoidBialgebraUnitResolved,
    bunchedBimonoidBialgebraBoneResolved, bunchedBimonoidCommutativityResolved,
    bunchedBimonoidCocommutativityResolved, bunchedBimonoidSigmaInvolutionResolved⟩

/-- ★ **The seven-new-additive-rows statement (the genuinely-new content over disjoint monoid + comonoid).**
A `Prop` conjunction of the four bialgebra + two (co)commutativity + one sigma-involution resolutions — the
content that distinguishes the bunched bimonoid from a bare monoid + comonoid + monoid. -/
def BunchedBimonoidSevenNewRowsResolvedStatement : Prop :=
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraProductLeftLeg
    bunchedBimonoidBialgebraProductRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraCounitLeftLeg
    bunchedBimonoidBialgebraCounitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraUnitLeftLeg
    bunchedBimonoidBialgebraUnitRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidBialgebraBoneLeftLeg
    bunchedBimonoidBialgebraBoneRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidCommutativityLeftLeg
    bunchedBimonoidCommutativityRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidCocommutativityLeftLeg
    bunchedBimonoidCocommutativityRightLeg ∧
  BunchedBimonoidCriticalPairResolved bunchedBimonoidSigmaInvolutionLeftLeg
    bunchedBimonoidSigmaInvolutionRightLeg

/-- ★★ **THE SEVEN NEW ADDITIVE ROWS, COHERENTLY RESOLVED MODULO STRICT.**  The four bialgebra rows (incl. the
tamed B1 4-strand delta-of-product with the middle swap), the two (co)commutativity rows, and the
sigma-involution row exhibited as generating 3-cells, each joinable-modulo-strict — the genuinely-new content
of the bicommutative bimonoid over the disjoint monoid + comonoid. -/
theorem bunchedBimonoidSevenNewRowsResolved : BunchedBimonoidSevenNewRowsResolvedStatement :=
  ⟨bunchedBimonoidBialgebraProductResolved, bunchedBimonoidBialgebraCounitResolved,
    bunchedBimonoidBialgebraUnitResolved, bunchedBimonoidBialgebraBoneResolved,
    bunchedBimonoidCommutativityResolved, bunchedBimonoidCocommutativityResolved,
    bunchedBimonoidSigmaInvolutionResolved⟩

/-! ## The least-congruence universal property (map-out) -/

/-- ★ **THE 22 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP).**  For any relation `targetRel`
absorbing the bunched-bimonoid base relation (a congruence containing the strict laws and the 22 critical-pair
rows), the two legs of EVERY critical row are `targetRel`-related — so the 22 generating 3-cells are the datum
whose fold through `SaturatedConvOverWithId.recInto` identifies each critical pair in EVERY model.  Uniform in
the row (one statement covering all 22, keyed on `BunchedBimonoidCriticalRow`). -/
theorem bunchedBimonoidCriticalPairsIdentifiedInEveryModel
    {targetRel : CellRelOver bunchedBimonoidOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad d}
    (row : BunchedBimonoidCriticalRow leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation (Or.inr row))

/-! ## The 22-row census -/

/-- The twenty-two critical-pair labels — 5 monoid-`m` + 5 monoid-`a` + 5 comonoid-`a` + 4 bialgebra +
2 (co)comm + 1 sigma-involution. -/
inductive BunchedBimonoidCriticalPairLabel
  /-- monoid-`m` `unitUnit`. -/
  | multMonadUnitUnit
  /-- monoid-`m` `leftUnitAssoc`. -/
  | multMonadLeftUnitAssoc
  /-- monoid-`m` `rightUnitAssoc`. -/
  | multMonadRightUnitAssoc
  /-- monoid-`m` `pentagon`. -/
  | multMonadPentagon
  /-- monoid-`m` `rootUnitAssoc`. -/
  | multMonadRootUnitAssoc
  /-- monoid-`a` `unitUnit`. -/
  | addMonadUnitUnit
  /-- monoid-`a` `leftUnitAssoc`. -/
  | addMonadLeftUnitAssoc
  /-- monoid-`a` `rightUnitAssoc`. -/
  | addMonadRightUnitAssoc
  /-- monoid-`a` `pentagon`. -/
  | addMonadPentagon
  /-- monoid-`a` `rootUnitAssoc`. -/
  | addMonadRootUnitAssoc
  /-- comonoid-`a` `counitCounit`. -/
  | comonoidCounitCounit
  /-- comonoid-`a` `leftCounitCoassoc`. -/
  | comonoidLeftCounitCoassoc
  /-- comonoid-`a` `rightCounitCoassoc`. -/
  | comonoidRightCounitCoassoc
  /-- comonoid-`a` `copentagon`. -/
  | comonoidCopentagon
  /-- comonoid-`a` `rootCounitCoassoc`. -/
  | comonoidRootCounitCoassoc
  /-- bialgebra B1 (delta-of-product with swap). -/
  | bialgebraProduct
  /-- bialgebra B2 (counit-of-product). -/
  | bialgebraCounit
  /-- bialgebra B3 (delta-of-unit). -/
  | bialgebraUnit
  /-- bialgebra B4 (the bone). -/
  | bialgebraBone
  /-- commutativity. -/
  | commutativity
  /-- cocommutativity. -/
  | cocommutativity
  /-- sigma-involution. -/
  | sigmaInvolution

/-- The complete enumeration of the bunched-bimonoid critical pairs — TWENTY-TWO, listed. -/
def allBunchedBimonoidCriticalPairs : List BunchedBimonoidCriticalPairLabel :=
  [.multMonadUnitUnit, .multMonadLeftUnitAssoc, .multMonadRightUnitAssoc, .multMonadPentagon,
    .multMonadRootUnitAssoc, .addMonadUnitUnit, .addMonadLeftUnitAssoc, .addMonadRightUnitAssoc,
    .addMonadPentagon, .addMonadRootUnitAssoc, .comonoidCounitCounit, .comonoidLeftCounitCoassoc,
    .comonoidRightCounitCoassoc, .comonoidCopentagon, .comonoidRootCounitCoassoc, .bialgebraProduct,
    .bialgebraCounit, .bialgebraUnit, .bialgebraBone, .commutativity, .cocommutativity, .sigmaInvolution]

/-- ★ **The critical-pair count is exactly TWENTY-TWO** — kernel-checked (`rfl`): 15 transported + 7 new. -/
theorem bunchedBimonoidCriticalPairCountIsTwentyTwo : allBunchedBimonoidCriticalPairs.length = 22 := rfl

/-- The seven NEW additive critical pairs — the DELTA over the transported monoid / comonoid. -/
def allBunchedBimonoidNewRows : List BunchedBimonoidCriticalPairLabel :=
  [.bialgebraProduct, .bialgebraCounit, .bialgebraUnit, .bialgebraBone,
    .commutativity, .cocommutativity, .sigmaInvolution]

/-- ★ **The new-additive-row count is exactly SEVEN** — kernel-checked (`rfl`): 4 bialgebra + 2 (co)comm +
1 sigma-involution. -/
theorem bunchedBimonoidNewRowCountIsSeven : allBunchedBimonoidNewRows.length = 7 := rfl

/-! ## B2 non-vacuity — a sample of transported legs are genuinely distinct 2-cells -/

/-- The monoid-`m` `unitUnit` legs are structurally DISTINCT (`eta_m |> m` vs `m <| eta_m`). -/
theorem bunchedBimonoidMultMonadUnitUnitLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidMultMonadUnitUnitLeftLeg bunchedBimonoidMultMonadUnitUnitRightLeg = false := rfl

/-- The comonoid-`a` `copentagon` legs are structurally DISTINCT (the two Godement whisker orders of
`delta * delta`). -/
theorem bunchedBimonoidComonoidCopentagonLegs_distinct :
    cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
      bunchedBimonoidComonoidCopentagonLeftLeg bunchedBimonoidComonoidCopentagonRightLeg = false := rfl

/-! ## B2 non-vacuity probes -/

#eval allBunchedBimonoidCriticalPairs.length
#eval allBunchedBimonoidNewRows.length
#eval cellBeq bunchedBimonoidOmegaModeBeq bunchedBimonoidOmegaGenBeq
  bunchedBimonoidMultMonadUnitUnitLeftLeg bunchedBimonoidMultMonadUnitUnitRightLeg

/-- ★ **ESTABLISHED (B2).**  The walking bunched bimonoid's 22 Squier critical pairs (15 transported: 5
monoid-`m` + 5 monoid-`a` + 5 comonoid-`a`; 7 new: 4 bialgebra + 2 (co)comm + 1 sigma-involution) are
exhibited as generating 3-cells over `bunchedBimonoidOmegaBaseRel`, each coherently resolved modulo strict at
peak and valley (`bunchedBimonoidWalkerCoherentPresentation`), with the 22-row census
(`bunchedBimonoidCriticalPairCountIsTwentyTwo`) and the least-congruence UP
(`bunchedBimonoidCriticalPairsIdentifiedInEveryModel`).  The seven new rows are the genuinely-new content over
the disjoint monoid + comonoid (`bunchedBimonoidSevenNewRowsResolved`).  `= true`. -/
def fxBunchedBimonoid_twentyTwoCriticalPairsShipped : Bool := true

/-- ★ **THE BIALGEBRA MIDDLE-SWAP ROW IS THE STAR (B2).**  `= true` records that the bialgebra B1 row (the
delta-of-product with the middle swap `1 (x) sigma (x) 1`) is the genuinely-new braided content: it CANNOT be
stated without the self-braiding `sigma_a`, and its 4-strand right leg is TAMED to a globular `a.a => a.a` row
(peak / valley `refl`) by the free carrier's extrinsic vcomp composability — the recon's sole flagged
correctness risk, discharged. -/
def fxBunchedBimonoid_bialgebraMiddleSwapRowIsTheStar : Bool := true

/-! # =========================================================================================
    # B3 — THE DECISION LEDGER (honest scope) — the three fragments at their honest status
    # =========================================================================================

★ **The bunched bimonoid decomposes into two non-interacting bunches, so its decision splits into three
fragments (recon (3)): the multiplicative `m`, the additive `a`, and their mixed free product.**  The
multiplicative side is DECIDED (single-colour, transported); the additive side is NAMED at `Mat(N)` but its
convergent normalizer is r2; the mixed side is the CLEAN case (the Amalgam disjoint-signature transfer applies
precisely because `a` and `m` share NO interacting symbol — the exact inverse of the DistLaw / strong-monad
wall, which was blocked BECAUSE the swap is a shared/interacting cell).  These are honest NAMED ledger markers
(the house style of the Frobenius / strong-monad decision ledgers), not fabricated flips. -/

/-- ★ **DECIDED — the multiplicative `m` 2-cell decision is monotone-maps / augmented simplex Delta.**  `= true`
records that the multiplicative bunch is a bare non-commutative monoid on the single colour `m`, whose 2-cell
word problem is the walking-monad decision — monotone maps / the augmented simplex category Delta (the
`List Nat` / `monadPath_normalForm` model shipped upstream in `MonadCoherentPresentation` / `MonotoneMap`).
Single-colour, so the two-colour DistLaw wall does NOT apply; transported verbatim, DECIDABLE. -/
def fxBunchedBimonoid_multiplicativeDecisionIsMonotoneMapsDelta : Bool := true

/-- ★ **NAMED — the additive `a` fragment corresponds to `Mat(N)`, the matrix PROP (#2033 feed).**  `= true`
records the correspondence (Lafont / Pirashvili / Fox): bicommutative bimonoids are exactly `Mat(N)`, the PROP
of natural-number matrices under matrix-multiplication composition (equivalently `Span(FinSet)` up to iso).
The additive 2-cell decision is therefore matrix equality — decidable IN PRINCIPLE.  This NAMES the target of
the #2033 matrix-PROP correspondence; the full diagram-to-matrix "spider" normalizer is the r2 deliverable
(`fxBunchedBimonoid_additiveConvergentNormalizerReached = false`). -/
def fxBunchedBimonoid_additiveDecisionIsMatNat : Bool := true

/-- ★ **WALL (honest, r2 / OMEGA-5) — the additive convergent `Mat(N)` normalizer is NOT shipped.**  `= false`
records that the full convergent bialgebra normalizer (diagram -> matrix "spider" normal form, the additive
2-cell decision procedure) is LARGE and DEFERRED to r2 / OMEGA-5.  r1 ships the presentation + the 22 resolved
critical pairs + the `Mat(N)` correspondence NAMED, not the normalizer. -/
def fxBunchedBimonoid_additiveConvergentNormalizerReached : Bool := false

/-- ★ **CLEAN — the mixed `a/m` decision is the alternating-block free product `Mat(N) (union) Delta`.**
`= true` records that the mixed fragment is the free product / PROP coproduct of the two bunches, whose normal
form is ALTERNATING BLOCKS (each `a`-block a matrix, each `m`-block a monotone map).  It is DECIDABLE RELATIVE
to the two per-bunch decisions via the Amalgam lane's disjoint-signature combination (Pigozzi 1974;
Baader-Tinelli 1998) — which transfers here PRECISELY because there is NO interacting symbol between `a` and
`m` (the exact inverse of the DistLaw / strong-monad wall, which was blocked because the swap is a
shared/interacting cell).  So the mixed COMBINATION is the easy part; the only hard component is the additive
`Mat(N)` normalizer itself. -/
def fxBunchedBimonoid_mixedDecisionIsAlternatingBlockAmalgam : Bool := true

/-- ★ **DECIDED (trivial) — the 1-cell theory is the free monoid on `{a, m}`, literal-equality decidable.**
`= true` records that at the 1-cell level both bunches are single-colour endo-1-generators with NO relations,
so the mixed 1-cell theory is the free monoid on the two colours `{a, m}`: two 1-cell words are convertible iff
literally equal (a decidable structural equality, the tag comparator `bunchedBimonoidLabelBeq` separates the
colours).  No cross-braiding at the 1-cell level. -/
def fxBunchedBimonoid_oneCellDecisionIsFreeMonoidLiteralEquality : Bool := true

/-- ★ **WALL (honest, r2) — Yang-Baxter / the hexagon on `a.a.a` is NOT shipped.**  `= false` records that at
one generator the braiding hexagon degenerates to the Yang-Baxter / braid relation
`sigma_{12} . sigma_{23} . sigma_{12} ~ sigma_{23} . sigma_{12} . sigma_{23}` on `a.a.a` — the non-trivial S_3
Coxeter relation, a genuine modulo-`interchange` 3-strand overlap.  It is the strong-monad B4's named
braided-base wall, one strand of the additive side wider, and is DEFERRED to r2 (`sigma^2 = id` is trivial and
IS shipped; Yang-Baxter is the genuine 3-strand cost). -/
def fxBunchedBimonoid_yangBaxterHexagonReached : Bool := false

/-- ★ **WALL (honest, r2) — the sigma-naturality-vs-`mu/eta/delta/eps` rows are NOT shipped.**  `= false`
records that the Beck-shaped swap-naturality critical pairs (the self-braiding commuting past each of the four
(co)monoid operations) are DEFERRED to r2 — they may be partly subsumed by the shipped (co)commutativity and
bialgebra rows, but the full naturality tail is not exhibited in r1. -/
def fxBunchedBimonoid_sigmaNaturalityRowsShipped : Bool := false

/-- ★ **WALL (honest, OMEGA-5, uniform with the family) — the full homotopy basis is NOT reached.**  `= false`
records that r1 ships the 22 generating 3-cells (Squier's convergent-scope critical pairs) but NOT the full
homotopy basis (the higher coherences closing the polygraphic resolution).  Uniform with every shipped walker
(`fxFrob_fullHomotopyBasisReached`, etc.) — the OMEGA-5 handoff. -/
def fxBunchedBimonoid_fullHomotopyBasisReached : Bool := false

/-! # =========================================================================================
    # B4 — THE FROBENIUS-DISTINCTION SELF-ATTACK + the grade-algebra / matrix-PROP tie-ins
    # =========================================================================================

★ **The bialgebra law B1 is NOT the Frobenius law, on the SAME four (co)monoid generators — machine-checked
via the Frobenius four-count (recon (4)).**  The Frobenius four-count `(#mu_a, #eta_a, #delta_a, #eps_a)` is a
SOUND invariant over the walking *Frobenius* monad (its F1 / F2 legs both count `(1,0,1,0)`), but it is
UNSOUND over the walking bunched *bimonoid*: the bialgebra B1 relates `delta_a . mu_a` (count `(1,0,1,0)`) to
the 4-strand `(mu (x) mu).(1 (x) sigma (x) 1).(delta (x) delta)` (count `(2,0,2,0)`) — DIFFERENT counts on
CONVERTIBLE legs.  So `BI != Frobenius`: the two theories are genuinely distinct (bare Frobenius = `2Cob` =
partition + genus, non-matrix; bare bicommutative bimonoid = `Mat(N)`), and the guard against silently
duplicating the Frobenius walker is a machine-checked refutation, not a docstring claim. -/

/-- Componentwise addition on the four-count vector `(#mu_a, #eta_a, #delta_a, #eps_a)` — a distinctively-named
local adder (NOT the Frobenius `fourAdd`, which is not imported). -/
def bunchedBimonoidFourAdd :
    Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | (a1, a2, a3, a4), (b1, b2, b3, b4) => (a1 + b1, a2 + b2, a3 + b3, a4 + b4)

/-- The **four-tag** of a bunched generator label — `1` in the slot of the additive (co)monoid generator it
names, `0` elsewhere.  The two 1-generators, the swap `sigma_a`, and BOTH multiplicative generators contribute
`(0,0,0,0)` — exactly the Frobenius four-count's blind spots, which is what makes it unsound over the bialgebra.
Full nine-arm split (constant-`Nat` motive, propext-free). -/
def bunchedBimonoidLabelFourTag : BunchedBIGenLabel → Nat × Nat × Nat × Nat
  | .additiveColour => (0, 0, 0, 0)
  | .multColour => (0, 0, 0, 0)
  | .addMult => (1, 0, 0, 0)
  | .addUnit => (0, 1, 0, 0)
  | .addComult => (0, 0, 1, 0)
  | .addCounit => (0, 0, 0, 1)
  | .addSwap => (0, 0, 0, 0)
  | .multMult => (0, 0, 0, 0)
  | .multUnit => (0, 0, 0, 0)

/-- The **generator four-count** `(#mu_a, #eta_a, #delta_a, #eps_a)` of a cell — the Frobenius-analogous total
structural fold (propext-free, like `cellSize`): identities / modes count zero, whiskering 1-cells are not
counted, `vcomp` sums both factors, a `gen` node contributes its label's four-tag. -/
def bunchedBimonoidGeneratorFourCount :
    {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Nat × Nat × Nat × Nat
  | _, .ofMode _ => (0, 0, 0, 0)
  | _, .gen label _ _ => bunchedBimonoidLabelFourTag label
  | _, .id _ => (0, 0, 0, 0)
  | _, .vcomp left right =>
      bunchedBimonoidFourAdd (bunchedBimonoidGeneratorFourCount left)
        (bunchedBimonoidGeneratorFourCount right)
  | _, .whiskerLeft _ cell => bunchedBimonoidGeneratorFourCount cell
  | _, .whiskerRight cell _ => bunchedBimonoidGeneratorFourCount cell

/-- ★ The **B1 LEFT leg `delta_a . mu_a` has four-count `(1,0,1,0)`** — one `mu_a`, one `delta_a` (`rfl`). -/
theorem bunchedBimonoidBialgebraProductLeftLeg_fourCount :
    bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductLeftLeg = (1, 0, 1, 0) := rfl

/-- ★ The **B1 RIGHT leg `(mu (x) mu).(1 (x) sigma (x) 1).(delta (x) delta)` has four-count `(2,0,2,0)`** — TWO
`mu_a`, TWO `delta_a` (the swap `sigma_a` counts zero) (`rfl`).  The doubled (mu, delta) count is the exact
signature of the bialgebra law that the Frobenius four-count cannot see. -/
theorem bunchedBimonoidBialgebraProductRightLeg_fourCount :
    bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductRightLeg = (2, 0, 2, 0) := rfl

/-- ★★ **THE FROBENIUS FOUR-COUNT IS UNSOUND OVER THE BIALGEBRA (the `BI != Frobenius` refutation).**  The B1
legs have DIFFERENT four-counts `(1,0,1,0) != (2,0,2,0)` — a `rfl`-reduced refutation.  Reusing the Frobenius
four-count as this walker's soundness invariant would therefore be a lie: it relates unequal-count cells (the
B1 legs are convertible, see below), so it does NOT respect the bunched-bimonoid congruence. -/
theorem bunchedFourCountUnsoundForBialgebra :
    bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductLeftLeg
      ≠ bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductRightLeg := by
  intro hcount
  exact Nat.noConfusion (Nat.succ.inj (congrArg (fun fourVector => fourVector.1) hcount))

/-- ★★ **`BI != Frobenius` — THE MACHINE-CHECKED SEPARATION.**  There EXIST two 2-cells that are CONVERTIBLE
under the bunched-bimonoid congruence (the bialgebra B1 3-cell) yet have UNEQUAL Frobenius four-count.  Hence
the four-count is not a congruence-respecting invariant here — unlike the walking Frobenius monad, where F1 /
F2 preserve it (both `(1,0,1,0)`).  This is the guard against silently duplicating the Frobenius walker:
the bunched bimonoid is a genuinely distinct theory (`Mat(N)`, not `2Cob`). -/
theorem bunchedBimonoidFrobeniusFourCountBreaksOnBialgebra :
    ∃ (leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad 2),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel leftLeg rightLeg ∧
      bunchedBimonoidGeneratorFourCount leftLeg ≠ bunchedBimonoidGeneratorFourCount rightLeg :=
  ⟨bunchedBimonoidBialgebraProductLeftLeg, bunchedBimonoidBialgebraProductRightLeg,
    bunchedBimonoidBialgebraProductResolved.legsConvertible, bunchedFourCountUnsoundForBialgebra⟩

/-! ## B4 non-vacuity probes -/

#eval bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductLeftLeg
#eval bunchedBimonoidGeneratorFourCount bunchedBimonoidBialgebraProductRightLeg

/-! ## The B4 honesty markers -/

/-- ★★ **ESTABLISHED (B4) — the Frobenius four-count is UNSOUND here, shipped ONLY as a refuted invariant.**
`= true` records that the Frobenius four-count `(#mu_a, #eta_a, #delta_a, #eps_a)` is NOT reused as this
walker's soundness invariant (`bunchedFourCountUnsoundForBialgebra`, `bunchedBimonoidFrobeniusFourCountBreaks
OnBialgebra`): the bialgebra B1 relates convertible legs of counts `(1,0,1,0)` and `(2,0,2,0)`, so the count
breaks the congruence.  This is the machine-checked guard against silently duplicating the Frobenius walker. -/
def fxBunchedBimonoid_frobeniusFourCountUnsoundHere : Bool := true

/-- ★★ **`BI != FROBENIUS` (B4).**  `= true` records the theory separation: the bare bicommutative bimonoid is
`Mat(N)` (partition/matrix, no genus), whereas the bare Frobenius monad is `2Cob` (partition + per-block
genus) — two distinct PROPs.  Their defining laws differ on the same four (co)monoid generators (the bialgebra
B1 `delta.mu = (mu (x) mu)(1 (x) sigma (x) 1)(delta (x) delta)` vs the Frobenius F1 / F2
`(s <| delta)(mu |> s) = mu.delta`), machine-separated by the four-count mismatch.  Not a Frobenius duplicate. -/
def fxBunchedBimonoid_biNotEqualFrobenius : Bool := true

/-- ★ **GRADE-ALGEBRA TIE-IN NAMED (B4, docstring-only) — the FX §6.4 bunched/BI reading.**  `= true` records
the tie-in: a bunched structure (O'Hearn-Pym) carries TWO non-interacting products — an additive bunch and a
multiplicative bunch — exactly the FX §6.4 separation-logic-as-usage-grade reading, where the separating
conjunction `*` IS the `+` of the usage grade algebra (the permission PCM `Frac`) and the multiplicative
context is the ordinary product.  The additive `a` = the separating/BI bunch, the multiplicative `m` = the
Cartesian bunch.  NAMED in the ledger, NOT imported: the `bunch` / `BI` markers live in
`FX1Poly/Tier0/Mode/Linear.lean` (the §6.4 linear/BI exponential + separation-PCM markers) and importing them
into the Omega lane is forbidden — this is the docstring cross-reference only. -/
def fxBunchedBimonoid_gradeAlgebraTieInNamed : Bool := true

/-- ★ **MATRIX-PROP CORRESPONDENCE NAMED FOR THE #2033 FEED (B4, docstring-only).**  `= true` records that the
additive fragment feeds the #2033 matrix-PROP table: bicommutative bimonoids are `Mat(N)`
(`fxBunchedBimonoid_additiveDecisionIsMatNat`), the same `Mat(N)` spine the TABLE / #2033 lane targets.  This
NAMES the additive-side census/table feed — the correspondence is the r2 normalizer's target
(`fxBunchedBimonoid_additiveConvergentNormalizerReached = false`), recorded additively without importing or
touching the table lane. -/
def fxBunchedBimonoid_matrixPropCorrespondenceNamedForTable : Bool := true

end FX1Poly.Polygraph.Omega
