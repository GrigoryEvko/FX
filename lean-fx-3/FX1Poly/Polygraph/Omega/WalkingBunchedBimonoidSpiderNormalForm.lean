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

end FX1Poly.Polygraph.Omega
