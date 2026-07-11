import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidOverQuotientAdjudication

/-! # Polygraph/Omega/WalkingBunchedBimonoidSpiderNormalForm — the matrix PROP opens (WP-PROP r1, #2032/#2033)

★ **The additive fragment IS the PROP `Mat(N)`, and this file opens the diagram-to-matrix "spider" direction.**
The upstream layers shipped the SOUND functor `CellExpr -> Mat(N)` (`bunchedBimonoidEvalCell`,
`bunchedBimonoidMatrixSoundOverSound`): convertible-over-`BunchedBimonoidSoundRow` implies equal matrix.  The
converse — the diagram-to-matrix "spider" normal form (equal matrix implies convertible) — is the r2+
completeness wall (`fxBunchedBimonoid_matrixCompletenessIsSpiderNormalFormWall = false`,
`fxBunchedBimonoid_spiderCompletenessTargetsSoundSubTheory = false`, NAMED, NOT edited here).  This file ships
the r1 opens toward it: the PROP carrier VIEW (no new inductive), the spider SECTION on the instance family (the
staged delta-fan / mu-fold building blocks + per-instance round-trips `evalCell (spider M) = M`), and two
hand-exhibited completeness instances (each diagram converted to the canonical spider word through the SOUND
congruence).

## The carrier adjudication (B1) — THE VIEW WINS, zero new inductives

Free-PROP `Mat(N)(p, q)` at one colour is exactly the shipped dim-2 words `CellExpr bunchedBimonoidOmegaComputad
2` whose source / target 1-cell words have widths `p` / `q`.  Every PROP datum already exists as a shipped
semantic layer:

  * hom-set `p => q` = a dim-2 word with `bunchedBimonoidWordWidth (boundarySource .) = p`,
    `bunchedBimonoidWordWidth (boundaryTarget .) = q` (widths EXTRINSIC, computed by `bunchedBimonoidEvalCell` at
    dim 1);
  * composition `g . f` = `CellExpr.vcomp f g` (domain preserved, `boundarySource (vcomp f g) = boundarySource
    f`);
  * monoidal tensor = the godement / whisker composite (identity-block direct sum under `evalCell`);
  * the objects `a^n` = `bunchedBimonoidAPow n` (width `n`), the PROP objects being the naturals;
  * the functor into `Mat(N)` = `bunchedBimonoidEvalCell`.

So r1 adds NO new type — only the arity word `bunchedBimonoidAPow` and the hom / composition VIEW theorems.  A
quotiented hom-set (literal `q x p` matrices) is the completeness / spider-NF direction, walled at r2+.

## The spider section (B2) — the staged Lafont form, instance-scoped

For a `q x p` matrix `M` with total `K`, the staged spider reads "delta-stage ; perm-stage ; mu-stage":
`deltaStage : a^p => a^K` fans each input into its column-sum of copies (the building block
`bunchedBimonoidDeltaFan`), `permStage : a^K => a^K` routes grouped-by-input to grouped-by-output (a `sigma`
composite; for the flagship it is the shipped `bunchedBimonoidMiddleSwap`, identity for the scalar / diagonal
instances), `muStage : a^K => a^q` folds each output's wires (`bunchedBimonoidMuFold`).  Then `M = Mg . P . C` by
construction.  For CLOSED `M`, `evalCell` is fully computational (`List.range.map`, no `List.getD`), so the
round-trip `evalCell (spider M) = M` is `rfl` per instance — the r1 deliverable.  The GENERAL round-trip
(for all `M`) and the three general stage-evaluation lemmas need the finite-sum Fubini kit (the shipped
`fxBunchedBimonoid_matrixStrictLawExtensionReached = false` wall) and are NAMED r2, not attempted.

## The completeness instances (B3) — hand-exhibited convertibilities to the canonical spider

Each instance exhibits a diagram converted to its canonical spider word THROUGH `BunchedBimonoidSoundRow` (the
faithful sub-theory, NOT the over-quotienting `bunchedBimonoidOmegaBaseRel`): the bialgebra-B1 legs converge to
`bunchedBimonoidSpiderAllOnesTwo` (= the shipped B1 right leg = spider `[[1,1],[1,1]]`), and the cocommutativity
legs converge to `bunchedBimonoidSpiderCopyOne` (= `delta` = spider `[[1],[1]]`).  These are HAND-EXHIBITED
convertibilities, NOT a general "equal-matrix implies convertible" decision — that (the #2033 star) is r2+ and is
NOT claimed here.

Raw Lean 4 + Init; STRUCTURAL only (delta-fan / mu-fold recurse structurally on the copy count); ASCII-only.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE PROP SUBSTRATE: the carrier VIEW (hom + composition), truth-probed on concrete words
    # =========================================================================================

★ **The truth-probe FIRST: the hom / composition views type-check on concrete words.**  Before any spider, the
carrier view is confirmed: each dim-2 generator IS a PROP hom `p => q` (its boundary widths), and vertical
composition IS PROP composition (the outer boundary is read off the first-applied / last-applied factor).  No new
inductive — only the arity word and the view theorems. -/

/-! ## The PROP objects — the arity words `a^n` (width `n`) -/

/-- ★ The **arity word** `a^n : * => *` — the PROP object at arity `n`, the `n`-fold vertical composite of the
additive colour `a` (right-nested onto the empty word `id`).  Structural recursion on `n`; propext-clean (full
`0 / n+1` split, no wildcard). -/
def bunchedBimonoidAPow : Nat → CellExpr bunchedBimonoidOmegaComputad 1
  | 0 => bunchedBimonoidIdOne
  | n + 1 => CellExpr.vcomp bunchedBimonoidAdditiveGen (bunchedBimonoidAPow n)

/-- The object `a^0` is the empty word (width 0). -/
theorem bunchedBimonoidAPowZero_width :
    bunchedBimonoidWordWidth (bunchedBimonoidAPow 0) = 0 := rfl

/-- The object `a^1` has width 1. -/
theorem bunchedBimonoidAPowOne_width :
    bunchedBimonoidWordWidth (bunchedBimonoidAPow 1) = 1 := rfl

/-- The object `a^2` has width 2. -/
theorem bunchedBimonoidAPowTwo_width :
    bunchedBimonoidWordWidth (bunchedBimonoidAPow 2) = 2 := rfl

/-- The object `a^3` has width 3. -/
theorem bunchedBimonoidAPowThree_width :
    bunchedBimonoidWordWidth (bunchedBimonoidAPow 3) = 3 := rfl

/-- ★ The **width bridge** to the shipped `a.a` word — `a^2` (right-nested) and `bunchedBimonoidAaWord`
(flat `vcomp a a`) are NOT definitionally equal but denote the SAME PROP object (both width 2). -/
theorem bunchedBimonoidAPowTwoWidthMatchesAaWord :
    bunchedBimonoidWordWidth (bunchedBimonoidAPow 2) = bunchedBimonoidWordWidth bunchedBimonoidAaWord := rfl

/-! ## The PROP hom-set view — each dim-2 generator is a hom `p => q` (its boundary widths) -/

/-- ★ `mu_a` is a PROP hom `2 => 1` (source width 2). -/
theorem bunchedBimonoidAddMuGen_isHomSourceWidth :
    bunchedBimonoidWordWidth (boundarySource bunchedBimonoidAddMuGen) = 2 := rfl

/-- ★ `mu_a` is a PROP hom `2 => 1` (target width 1). -/
theorem bunchedBimonoidAddMuGen_isHomTargetWidth :
    bunchedBimonoidWordWidth (boundaryTarget bunchedBimonoidAddMuGen) = 1 := rfl

/-- ★ `delta_a` is a PROP hom `1 => 2` (source width 1). -/
theorem bunchedBimonoidAddDeltaGen_isHomSourceWidth :
    bunchedBimonoidWordWidth (boundarySource bunchedBimonoidAddDeltaGen) = 1 := rfl

/-- ★ `delta_a` is a PROP hom `1 => 2` (target width 2). -/
theorem bunchedBimonoidAddDeltaGen_isHomTargetWidth :
    bunchedBimonoidWordWidth (boundaryTarget bunchedBimonoidAddDeltaGen) = 2 := rfl

/-- ★ `sigma_a` is a PROP endo-hom `2 => 2` (source width 2). -/
theorem bunchedBimonoidAddSigmaGen_isHomSourceWidth :
    bunchedBimonoidWordWidth (boundarySource bunchedBimonoidAddSigmaGen) = 2 := rfl

/-- ★ `sigma_a` is a PROP endo-hom `2 => 2` (target width 2). -/
theorem bunchedBimonoidAddSigmaGen_isHomTargetWidth :
    bunchedBimonoidWordWidth (boundaryTarget bunchedBimonoidAddSigmaGen) = 2 := rfl

/-- ★ `eta_a` is a PROP hom `0 => 1` (source width 0). -/
theorem bunchedBimonoidAddEtaGen_isHomSourceWidth :
    bunchedBimonoidWordWidth (boundarySource bunchedBimonoidAddEtaGen) = 0 := rfl

/-- ★ `eps_a` is a PROP hom `1 => 0` (target width 0). -/
theorem bunchedBimonoidAddEpsGen_isHomTargetWidth :
    bunchedBimonoidWordWidth (boundaryTarget bunchedBimonoidAddEpsGen) = 0 := rfl

/-! ## The PROP composition view — `vcomp` is composition, the outer boundary composes -/

/-- ★ **COMPOSITION PRESERVES THE DOMAIN.**  The composite `vcomp mu_a delta_a` (= `delta_a . mu_a`, "mu then
delta") has domain `= boundarySource mu_a` — vertical composition reads its source off the first-applied factor,
exactly PROP composition's domain law.  Machine-checked `rfl` on the shipped B1 left leg. -/
theorem bunchedBimonoidPropCompositionPreservesDomain :
    boundarySource bunchedBimonoidBialgebraProductLeftLeg = boundarySource bunchedBimonoidAddMuGen := rfl

/-- ★ **COMPOSITION PRESERVES THE CODOMAIN.**  The composite `vcomp mu_a delta_a` has codomain `= boundaryTarget
delta_a` — the last-applied factor's target, PROP composition's codomain law. -/
theorem bunchedBimonoidPropCompositionPreservesCodomain :
    boundaryTarget bunchedBimonoidBialgebraProductLeftLeg = boundaryTarget bunchedBimonoidAddDeltaGen := rfl

/-- ★ The composite `delta_a . mu_a` is a PROP endo-hom `2 => 2` (domain width 2). -/
theorem bunchedBimonoidPropCompositeSourceWidth :
    bunchedBimonoidWordWidth (boundarySource bunchedBimonoidBialgebraProductLeftLeg) = 2 := rfl

/-- ★ The composite `delta_a . mu_a` is a PROP endo-hom `2 => 2` (codomain width 2). -/
theorem bunchedBimonoidPropCompositeTargetWidth :
    bunchedBimonoidWordWidth (boundaryTarget bunchedBimonoidBialgebraProductLeftLeg) = 2 := rfl

/-! ## The B1 honesty marker -/

/-- ★ **ESTABLISHED (B1) — the PROP hom / composition views type-check on concrete words.**  `= true` records
the carrier adjudication (the VIEW wins, zero new inductive): the arity words `bunchedBimonoidAPow n` are the PROP
objects (width `n`, `bunchedBimonoidAPow{Zero,One,Two,Three}_width`); each dim-2 generator is a hom `p => q` read
off its boundary widths (`mu : 2=>1`, `delta : 1=>2`, `sigma : 2=>2`, `eta : 0=>1`, `eps : 1=>0`); and `vcomp` is
PROP composition, preserving domain / codomain (`bunchedBimonoidPropCompositionPreserves{Domain,Codomain}`).  The
functor into `Mat(N)` is the shipped `bunchedBimonoidEvalCell`; NO new type is introduced. -/
def fxBunchedBimonoid_propHomAndCompositionViewsTypeCheck : Bool := true

/-! # =========================================================================================
    # B2 — THE SPIDER CONSTRUCTOR + THE ROUND-TRIP: staged delta-fan / mu-fold + per-instance rfl
    # =========================================================================================

★ **The staged Lafont spider, instance-scoped, with `evalCell (spider M) = M` per instance by `rfl`.**  The two
general building blocks are the delta-fan (`a => a^k`, fan one input into `k` copies) and the mu-fold
(`a^k => a`, merge `k` wires into one output); the perm-stage routing is the shipped `sigma` composite
(`bunchedBimonoidMiddleSwap` for the flagship, identity for the scalar / diagonal instances).  The round-trip is
`rfl` because `bunchedBimonoidEvalCell` is fully computational on closed inputs. -/

/-! ## The two staged building blocks — delta-fan and mu-fold (STRUCTURAL on the copy count) -/

/-- ★ The **delta-fan** `bunchedBimonoidDeltaFan k : a => a^k` — fan one input strand into `k` copies.  `0`
deletes (`eps_a`), `1` keeps (`id a`), `k+2` comultiplies then recursively fans the left copy.  Structural
recursion on the copy count (full `0 / 1 / k+2` split, no wildcard — propext-clean).  The delta-stage building
block: `evalCell (deltaFan k)` is the `k x 1` all-ones copy column. -/
def bunchedBimonoidDeltaFan : Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0 => bunchedBimonoidAddEpsGen
  | 1 => CellExpr.id bunchedBimonoidAdditiveGen
  | k + 2 => CellExpr.vcomp bunchedBimonoidAddDeltaGen
      (CellExpr.whiskerRight (bunchedBimonoidDeltaFan (k + 1)) bunchedBimonoidAdditiveGen)

/-- ★ The **mu-fold** `bunchedBimonoidMuFold k : a^k => a` — merge `k` input strands into one output.  `0`
creates (`eta_a`), `1` keeps (`id a`), `k+2` recursively folds the left `k+1` then multiplies.  Structural on the
merge count.  The mu-stage building block: `evalCell (muFold k)` is the `1 x k` all-ones fold row. -/
def bunchedBimonoidMuFold : Nat → CellExpr bunchedBimonoidOmegaComputad 2
  | 0 => bunchedBimonoidAddEtaGen
  | 1 => CellExpr.id bunchedBimonoidAdditiveGen
  | k + 2 => CellExpr.vcomp
      (CellExpr.whiskerRight (bunchedBimonoidMuFold (k + 1)) bunchedBimonoidAdditiveGen)
      bunchedBimonoidAddMuGen

/-- ★ The **scalar spider** `bunchedBimonoidSpiderScalar n : a => a` — fan one input into `n` wires then merge
them into one output, evaluating to the `1 x 1` matrix `[[n]]`.  The `1x1` spider family: delta-stage then
mu-stage, no routing. -/
def bunchedBimonoidSpiderScalar (n : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (bunchedBimonoidDeltaFan n) (bunchedBimonoidMuFold n)

/-! ## The flagship instances — the spider words pinned to shipped forms -/

/-- ★★ The **all-ones `2 x 2` spider** `bunchedBimonoidSpiderAllOnesTwo` — DEFINITIONALLY the shipped bialgebra
B1 right leg `(mu (x) mu).(1 (x) sigma (x) 1).(delta (x) delta)`, the staged spider of `[[1,1],[1,1]]` (colsum =
rowsum = 2, `K = 4`, the perm-stage routing being the shipped `bunchedBimonoidMiddleSwap`).  Pinning it to the
exact word makes the flagship completeness instance's `refl` leg close. -/
def bunchedBimonoidSpiderAllOnesTwo : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidBialgebraProductRightLeg

/-- ★ The **copy spider** `bunchedBimonoidSpiderCopyOne` — DEFINITIONALLY `delta_a`, the staged spider of
`[[1],[1]]` (one input copied to two outputs; delta-stage only). -/
def bunchedBimonoidSpiderCopyOne : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidAddDeltaGen

/-- ★ A **`2 x 3` sample spider** `bunchedBimonoidSpiderTwoByThreeSample` — `(muFold 2) (x) a`, the staged spider
of `[[1,1,0],[0,0,1]]` (each column feeds exactly one output, so the delta- / perm-stages are identity and only
the mu-stage fires: inputs 0,1 merge to output 0, input 2 passes to output 1). -/
def bunchedBimonoidSpiderTwoByThreeSample : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight (bunchedBimonoidMuFold 2) bunchedBimonoidAdditiveGen

/-! ## The building-block shape lemmas (the delta-fan / mu-fold matrices, `rfl`) -/

/-- The delta-fan of `0` DELETES — `evalCell (deltaFan 0) = eps = 0 x 1`. -/
theorem bunchedBimonoidDeltaFanZero_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 0) = { rows := 0, cols := 1, entries := [] } := rfl

/-- The delta-fan of `2` COPIES to two wires — `evalCell (deltaFan 2) = [[1],[1]]`. -/
theorem bunchedBimonoidDeltaFanTwo_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 2) = { rows := 2, cols := 1, entries := [[1], [1]] } := rfl

/-- The delta-fan of `3` COPIES to three wires — `evalCell (deltaFan 3) = [[1],[1],[1]]`. -/
theorem bunchedBimonoidDeltaFanThree_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 3)
      = { rows := 3, cols := 1, entries := [[1], [1], [1]] } := rfl

/-- The mu-fold of `0` CREATES — `evalCell (muFold 0) = eta = 1 x 0`. -/
theorem bunchedBimonoidMuFoldZero_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidMuFold 0) = { rows := 1, cols := 0, entries := [[]] } := rfl

/-- The mu-fold of `2` MERGES two wires — `evalCell (muFold 2) = [[1,1]]`. -/
theorem bunchedBimonoidMuFoldTwo_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidMuFold 2) = { rows := 1, cols := 2, entries := [[1, 1]] } := rfl

/-- The mu-fold of `3` MERGES three wires — `evalCell (muFold 3) = [[1,1,1]]`. -/
theorem bunchedBimonoidMuFoldThree_matrix :
    bunchedBimonoidEvalCell (bunchedBimonoidMuFold 3)
      = { rows := 1, cols := 3, entries := [[1, 1, 1]] } := rfl

/-! ## THE ROUND-TRIP — `evalCell (spider M) = M` per instance (the four self-attacks + [[3]], `rfl`) -/

/-- ★★ **ROUND-TRIP (the zero matrix `[[0]]`).**  The scalar spider of `0` — fan into zero wires (delete) then
merge zero wires (create) — evaluates to the `1 x 1` zero matrix.  `rfl`. -/
theorem bunchedBimonoidSpiderScalarZeroRoundTrip :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 0) = { rows := 1, cols := 1, entries := [[0]] } := rfl

/-- ★ **ROUND-TRIP (the identity scalar `[[1]]`).**  The scalar spider of `1` is the identity `1 x 1` matrix. -/
theorem bunchedBimonoidSpiderScalarOneRoundTrip :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 1) = { rows := 1, cols := 1, entries := [[1]] } := rfl

/-- ★★ **ROUND-TRIP (the multiplicity `[[2]]`).**  The scalar spider of `2` evaluates to `[[2]]` — the loop-free
multiplicity bubble (fan to two wires, merge two wires; `1*1 + 1*1 = 2`). -/
theorem bunchedBimonoidSpiderScalarTwoRoundTrip :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 2) = { rows := 1, cols := 1, entries := [[2]] } := rfl

/-- ★★ **ROUND-TRIP (the multiplicity `[[3]]`, fan depth 2).**  The scalar spider of `3` evaluates to `[[3]]`. -/
theorem bunchedBimonoidSpiderScalarThreeRoundTrip :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 3) = { rows := 1, cols := 1, entries := [[3]] } := rfl

/-- ★★ **ROUND-TRIP (the empty `0 x 0` matrix).**  The empty spider — the identity 2-cell on the empty word
`id` — evaluates to the `0 x 0` matrix (the B4 bone's identity, NOT the eta-then-eps bone). -/
theorem bunchedBimonoidSpiderEmptyRoundTrip :
    bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidIdOne) = { rows := 0, cols := 0, entries := [] } := rfl

/-- ★★ **ROUND-TRIP (the flagship `[[1,1],[1,1]]`).**  The all-ones `2 x 2` spider (= the shipped B1 right leg)
evaluates to `[[1,1],[1,1]]` — the staged `(delta (x) delta) ; middle-swap ; (mu (x) mu)` reproduces the matrix
on the nose. -/
theorem bunchedBimonoidSpiderAllOnesTwoRoundTrip :
    bunchedBimonoidEvalCell bunchedBimonoidSpiderAllOnesTwo
      = { rows := 2, cols := 2, entries := [[1, 1], [1, 1]] } := rfl

/-- ★★ **ROUND-TRIP (the `2 x 3` sample `[[1,1,0],[0,0,1]]`).**  The mu-stage-only sample spider evaluates to its
matrix — the general `2 x 3` shape reproduced on the nose (each column feeding one output). -/
theorem bunchedBimonoidSpiderTwoByThreeRoundTrip :
    bunchedBimonoidEvalCell bunchedBimonoidSpiderTwoByThreeSample
      = { rows := 2, cols := 3, entries := [[1, 1, 0], [0, 0, 1]] } := rfl

/-! ## The direct self-attack forms (the recon's self-attack table, `rfl`) -/

/-- ★ **SELF-ATTACK (`[[0]]` direct form).**  The cap-cup zero scalar `eps_a ; eta_a : a => a` (delete then
create) evaluates to `[[0]]` — the same matrix as `spiderScalar 0`, in the two-generator direct form. -/
theorem bunchedBimonoidZeroScalarSelfAttack :
    bunchedBimonoidEvalCell (CellExpr.vcomp bunchedBimonoidAddEpsGen bunchedBimonoidAddEtaGen)
      = { rows := 1, cols := 1, entries := [[0]] } := rfl

/-- ★ **SELF-ATTACK (`[[2]]` direct form).**  The multiplicity bubble `delta_a ; mu_a : a => a` (copy then merge)
evaluates to `[[2]]` — the same matrix as `spiderScalar 2`, in the two-generator direct form. -/
theorem bunchedBimonoidMultiplicityTwoSelfAttack :
    bunchedBimonoidEvalCell (CellExpr.vcomp bunchedBimonoidAddDeltaGen bunchedBimonoidAddMuGen)
      = { rows := 1, cols := 1, entries := [[2]] } := rfl

/-! ## B2 truth-probe outputs -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 0)
#eval bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 3)
#eval bunchedBimonoidEvalCell bunchedBimonoidSpiderAllOnesTwo
#eval bunchedBimonoidEvalCell bunchedBimonoidSpiderTwoByThreeSample

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the staged spider + per-instance round-trip are shipped.**  `= true` records the two
general building blocks (`bunchedBimonoidDeltaFan` = delta-stage, `bunchedBimonoidMuFold` = mu-stage) and the
instance-family spiders (`bunchedBimonoidSpiderScalar n`, `...AllOnesTwo`, `...CopyOne`, `...TwoByThreeSample`),
each with its round-trip `evalCell (spider M) = M` machine-checked `rfl`: the zero matrix `[[0]]`, the identity
`[[1]]`, the multiplicities `[[2]]` / `[[3]]`, the empty `0 x 0`, the flagship `[[1,1],[1,1]]`, and the `2 x 3`
sample `[[1,1,0],[0,0,1]]`.  The perm-stage routing is instance-scoped (`bunchedBimonoidMiddleSwap` for the
flagship, identity elsewhere). -/
def fxBunchedBimonoid_spiderPerInstanceRoundTripShipped : Bool := true

/-- ★ **WALL (honest, r2) — the GENERAL round-trip `forall M, evalCell (spider M) = M` is NOT shipped.**
`= false` records that the universally-quantified round-trip needs the finite-sum Fubini / matMul-associativity
kit (the same wall as `fxBunchedBimonoid_matrixStrictLawExtensionReached`) to close the delta-stage / mu-stage
composition for arbitrary `M`.  r1 ships per-instance `rfl` only; the `forall`-theorem is NAMED r2, not stated. -/
def fxBunchedBimonoid_spiderGeneralRoundTripReached : Bool := false

/-- ★ **WALL (honest, r2) — the three GENERAL stage-evaluation lemmas are NOT shipped.**  `= false` records that
the general `evalCell deltaStage = C` (copy matrix), `evalCell permStage = P` (permutation), `evalCell muStage =
Mg` (fold matrix) — from which `M = Mg . P . C` by construction — need the same Fubini kit and are DEFERRED to
r2.  Only the per-instance building-block shape lemmas (`bunchedBimonoidDeltaFan{Two,Three}_matrix`, etc.) are
shipped. -/
def fxBunchedBimonoid_spiderGeneralStageLemmasReached : Bool := false

/-- ★ **WALL (honest, r2) — the GENERAL perm-stage routing for an arbitrary matrix is NOT shipped.**  `= false`
records that the row-major-to-column-sum routing (the perm-stage of a general `spiderOf : List (List Nat) ->
word`) requires a transpose helper (the encoding risk); r1 keeps the perm-stage INSTANCE-scoped (the flagship's
`bunchedBimonoidMiddleSwap`; identity for the scalar / diagonal instances) and NAMES the general routing r2. -/
def fxBunchedBimonoid_spiderGeneralRoutingReached : Bool := false

end FX1Poly.Polygraph.Omega
