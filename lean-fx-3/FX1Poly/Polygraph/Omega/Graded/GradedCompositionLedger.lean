import FX1Poly.Polygraph.Omega.Graded.GradedCell
import FX1Poly.Polygraph.Omega.Graded.GradedAppAnchor
import FX1Poly.Polygraph.Omega.Graded.EnrichedCheckSeed
import FX1Poly.Polygraph.Omega.Graded.CollisionCatalog
import FX1Poly.Polygraph.Omega.Graded.GradedCellComposition

/-! # Polygraph/Omega/Graded/GradedCompositionLedger — the OMEGA-5 r1 ledger + the OMEGA-6 handoff (B5)

The honest r1 ledger: what the graded rung SHIPPED (each machine-checked zero-axiom), the hypothesis-free
r1 re-assessment, every surviving jam named with its EXACT goal and NAMED blocking node, and the OMEGA-6
handoff spec.  This file edits NOTHING outside `Omega/Graded/`; all markers are hypothesis-free `Bool`
defs, so every declaration is axiom-free.

OMEGA-5 r1 is a RECOGNITION round, not a construction round: the grade algebra
(`OrderedGradeSemiring` / `GradeVectorOver` / `add` / `scale` + all semimodule laws) and the App rule
(`HasGradeOver.app`, grade `add p (scale r q)`) were already shipped, zero-axiom, generic over any
semiring, Polygraph-free.  r1 PAIRS them and NAMES the identity.

## What OMEGA-5 r1 SHIPPED (each machine-checked zero-axiom)

  * **B1 — THE GRADED CARRIER** (`GradedCell.lean`).  `GradedCell computad dim R := CellExpr computad
    dim × GradeVectorOver R` (extrinsic product — the grade is a decoration, never an index, per
    POLY-TAB / OMEGA-1).  The composition arithmetic: `gradeCompose r p q := add p (scale r q)`
    (sequential, the App rule `p + r·q`) and `gradeComposePar p q := add p q` (parallel / context split);
    `gradedVcomp` / `gradedWhiskerLeft` / `gradedWhiskerRight` on `GradedCell`.  Non-vacuity COMPUTES at
    the usage semiring `{0,1,ω}` — the identity composite `[0]+1·[1]=[1]`, the DECISIVE `r=ω` case
    `[0,1]+ω·[1,0]=[ω,1]`, the context-split saturation `[1]+[1]=[ω]`, and a concrete dim-3 graded vcomp
    yielding both a cell and the grade `[ω]`.

  * **B2 — THE APP ANCHOR** (`GradedAppAnchor.lean`) — THE HEADLINE.  `appGrade_eq_gradeCompose`: the
    KERNEL App rule concludes at EXACTLY `gradeCompose binderGrade functionGrades argumentGrades`, on the
    real judgment `HasGradeOver`, by the App constructor (defeq).  `appGrade_invert_gradeCompose`: the
    inverse — any application derivation exhibits its grade as that composite.  The two worked demos
    reuse the shipped typed terms through a `gradeCompose`-shaped ascription (no rebuild): the applied
    identity in any dimension, and THE DECISIVE `r=ω` redex `(λx.(g x)x) z` at `gradeCompose ω [0,1] [1,0]
    = [ω,1]`.  The §6.2 typing rule IS enriched composition — the grade ARITHMETIC (`add ∘ scale`) is
    dimension/k-uniform.

  * **B3 — THE ENRICHED-FUNCTOR SEED** (`EnrichedCheckSeed.lean`), grade side.  `enrichedCheckOnGrades`
    (the shipped `isPointwiseBelowBool` read as the functor's per-dimension evaluation),
    `enrichedCheckOnGrades_correct` (soundness+completeness — a faithful DECISION), `checkUsageFactor`
    (the usage instance).  The functoriality-on-grades legs are FREE from the shipped semimodule laws:
    `gradeCompose_mono` / `gradeComposePar_mono` (the composites preserve the admissibility ORDER) and
    `gradeCompose_scaleHom` (the scalar action is a homomorphism over the sequential composite).

  * **B4 — THE §6.8 CATALOG AS DATA** (`CollisionCatalog.lean`).  `CollisionRow` + the nine collision
    rows + `sixEightCatalog`, every row `isFreeLocus := false` (the non-free markers), `E044` (CT×Async)
    the contradictory sharpest, `I004` the 3-way.  `sixEightCatalog_allNonFree` proves every §6.8
    collision is a non-free locus of the 21-dimension amalgam — as a checked datum.

## The r1 re-assessment (hypothesis-free)

r1 recognized the App rule as enriched composition and seeded the functor on the usage factor, but the
CELL-side functor, the amalgam modular-transfer, the 21-dim product semiring, the collision non-free
LINK proof, and the cell-level (boundary-respecting) App=composite are the honestly-walled remainder.
`fxOmega5_r1RecognitionRoundComplete = true` (the r1 SCOPE is done); the deeper theorems are `false`.

## The surviving jams (each: EXACT goal + NAMED blocking node)

  * **JAM — the enriched functor's CELL side.**  Goal: extend `check` from grade vectors to
    `CellExpr computad n → AmalgamatedProduct(dimensionWalkers)` with `check (a *_k b) = check a ⊗_k
    check b`.  NAMED node: the walker-product codomain `⊗_k` = the amalgamated-product / dispatch arrow
    (AMALG-2, Amalgam lane's `Dispatch.lean`: `fxAmalg_hasDispatchTheorem = false`, the arrow
    uninhabited).  Genuinely open — no published modular-decidability-transfer theorem for non-disjoint
    signatures.  `fxOmega5_enrichedFunctorCellSideReached = false`.

  * **JAM — the 21-dimension PRODUCT semiring.**  Goal: one `OrderedGradeSemiring` that is the product
    of the 21 heterogeneous dimension carriers (so the full grade vector is checked by one instance).
    NAMED node: a dependent-tuple grade / n-ary product `OrderedGradeSemiring` over heterogeneous
    `Carrier`s; r1 does the single usage dimension.  `fxOmega5_productSemiring21Reached = false`.

  * **JAM — the collision NON-FREE LINK proof.**  Goal: prove `collisionPair d1 d2 → ¬ disjointSignatures
    d1 d2 → modular decidability transfer fails` (turning the B4 `isFreeLocus := false` DATA into a
    THEOREM).  NAMED node: the disjointness predicate wired to dimension pairs + the amalgam dispatch
    hypothesis `computadGeneratorsDisjoint` (Amalgam `Dispatch.lean`; Baader-Tinelli 1998 shared-symbol
    undecidability).  `fxOmega5_collisionNonFreeLinkReached = false`.

  * **JAM — the amalgam modular TRANSFER.**  Goal: the Nelson-Oppen / Pigozzi decidability transfer
    across the 21 theories at the free (disjoint) loci.  NAMED node: same disjoint-signature restriction
    — Pigozzi / Baader-Tinelli cover only disjoint signatures, and §6.8 says the FX dimensions are not
    disjoint.  `fxOmega5_amalgamModularTransferReached = false`.

  * **JAM — App = graded 2-composite WITH boundaries (cell level).**  Goal: identify the App rule with a
    genuine boundary-respecting graded `vcomp` at the CELL level (not only the grade arithmetic).  NAMED
    node: graded vcomp as a boundary-respecting composite aligned with `boundarySource`/`boundaryTarget`
    (needs the cell-side functor).  r1 did the arithmetic + the demo.
    `fxOmega5_appCellLevelCompositionReached = false`.

## The OMEGA-6 handoff spec — what the next round consumes from r1

  * from B1: `GradedCell` + `gradeCompose` / `gradeComposePar` + `gradedVcomp` / `gradedWhiskerLeft` /
    `gradedWhiskerRight` — the graded carrier the cell-side functor decorates, with its k-uniform
    arithmetic;
  * from B2: `appGrade_eq_gradeCompose` + `appGrade_invert_gradeCompose` — the App = sequential-composite
    identity, both directions, on the real `HasGradeOver` judgment (the anchor the cell-level theorem
    lifts);
  * from B3: `enrichedCheckOnGrades` + `enrichedCheckOnGrades_correct` + `gradeCompose_mono` /
    `gradeComposePar_mono` / `gradeCompose_scaleHom` — the grade-side functor + its free compatibility
    laws, ready to be ONE FACTOR of the walker product once AMALG-2 lands;
  * from B4: `sixEightCatalog` + `sixEightCatalog_allNonFree` — the non-free loci as data, ready to be
    wired to the disjointness predicate for the LINK proof.

Raw Lean 4 + Init; a docstring record plus `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega.Graded

/-! ## The r1 shipped-piece markers (each cites machine-checked code) -/

/-- ★ **B1 — the graded carrier + composition arithmetic SHIPPED.**  `= true`: `GradedCell` (extrinsic
product), `gradeCompose` / `gradeComposePar`, `gradedVcomp` / `gradedWhiskerLeft` / `gradedWhiskerRight`,
with usage `{0,1,ω}` non-vacuity computing (incl. the decisive `r=ω`). -/
def fxOmega5_gradedCarrierShippedR1 : Bool := true

/-- ★ **B2 — the App anchor SHIPPED.**  `= true`: `appGrade_eq_gradeCompose` /
`appGrade_invert_gradeCompose` identify the kernel App rule's grade with `gradeCompose r p q` on the real
`HasGradeOver` judgment (both directions, defeq), the decisive `r=ω` redex reused through the anchor. -/
def fxOmega5_appAnchorShippedR1 : Bool := true

/-- ★ **B3 — the enriched-functor seed (grade side) SHIPPED.**  `= true`: `enrichedCheckOnGrades` +
`enrichedCheckOnGrades_correct` + the free functoriality legs (`gradeCompose_mono` /
`gradeComposePar_mono` / `gradeCompose_scaleHom`), the usage factor end-to-end. -/
def fxOmega5_enrichedFunctorGradeSideSeededR1 : Bool := true

/-- ★ **B4 — the §6.8 catalog as data SHIPPED.**  `= true`: `sixEightCatalog` (9 `CollisionRow` non-free
loci, all `isFreeLocus = false`), `sixEightCatalog_allNonFree`, the contradictory `E044` and 3-way
`I004`. -/
def fxOmega5_collisionCatalogAsDataShippedR1 : Bool := true

/-! ## The r1 completion marker (the SCOPE is done) -/

/-- ★ **The OMEGA-5 r1 recognition round is COMPLETE.**  `= true`: B1–B4 shipped, machine-checked
zero-axiom.  This gates the r1 SCOPE (recognition + decoration), NOT the deeper theorems — those are the
jam markers below (all `false`). -/
def fxOmega5_r1RecognitionRoundComplete : Bool := true

/-! ## The surviving-jam markers (each `= false` — NOT reached; the exact goal + NAMED node above) -/

/-- ★ **The enriched functor's CELL side is NOT reached.**  `= false` — the walker-product codomain
`⊗_k` needs the amalgamated-product / dispatch arrow (AMALG-2, `fxAmalg_hasDispatchTheorem = false`,
arrow uninhabited); no published modular-transfer theorem for non-disjoint signatures. -/
def fxOmega5_enrichedFunctorCellSideReached : Bool := false

/-- ★ **The 21-dimension PRODUCT semiring is NOT reached.**  `= false` — needs an n-ary /
dependent-tuple product `OrderedGradeSemiring` over heterogeneous carriers; r1 does the single usage
dimension. -/
def fxOmega5_productSemiring21Reached : Bool := false

/-- ★ **The collision NON-FREE LINK proof is NOT reached.**  `= false` — `collisionPair d1 d2 → ¬
disjoint → transfer fails` needs the disjointness predicate wired to dimension pairs + the amalgam
dispatch hypothesis `computadGeneratorsDisjoint` (Amalgam lane).  B4 records the loci as DATA; the LINK
is a THEOREM for a later round. -/
def fxOmega5_collisionNonFreeLinkReached : Bool := false

/-- ★ **The amalgam modular TRANSFER is NOT reached.**  `= false` — Nelson-Oppen / Pigozzi cover only
disjoint signatures, and §6.8 says the FX dimensions are not disjoint (Baader-Tinelli 1998). -/
def fxOmega5_amalgamModularTransferReached : Bool := false

/-- ★ **App = graded 2-composite WITH boundaries (cell level) is NOT reached.**  `= false` — r1
identified the grade ARITHMETIC (`add ∘ scale`); a boundary-respecting graded `vcomp` identified with
App at the CELL level needs the cell-side functor. -/
def fxOmega5_appCellLevelCompositionReached : Bool := false

/-! ## The OMEGA-6 handoff marker -/

/-- ★ **The OMEGA-6 handoff is RECORDED.**  `= true`: OMEGA-6 consumes, from r1, the graded carrier
(B1), the App anchor both directions (B2), the grade-side functor + its free compatibility laws (B3),
and the non-free loci as data (B4).  See the file docstring for the full spec. -/
def fxOmega5_omegaSixHandoffRecordedR1 : Bool := true

/-! ## OMEGA-5 r2 — the cell-side graded composition (the 110-percent grind)

r2 grinds one rung past r1's recognition (`GradedCellComposition.lean`): the lockstep composite's GRADE
leg is now a proven ALGEBRA, the grade projection is a machine-checked enriched FUNCTOR, and the checker
REFUSES genuinely.  Each marker below is a hypothesis-free `Bool`.  The honest boundary: r2 owns the
GRADE leg only; the CELL leg's associativity is NOT proven here (free `CellExpr.vcomp`) — it is cited to
OMEGA-7's `linearizeFull_pasteAlong_assoc` (Tier-0, un-importable under the layer rule).  The r1 jams
(cell-side functor, product semiring, collision transfer, cell-level App composite) stay open — their
`false` markers above are UNCHANGED.

## What OMEGA-5 r2 SHIPPED (each machine-checked zero-axiom, `GradedCellComposition.lean`)

  * **B1 — the grade-leg composition algebra.**  `gradeCompose_assoc` (the scalar-REINDEXED associativity
    `gradeCompose (a·b) (gradeCompose a p q) t = gradeCompose a p (gradeCompose b q t)`, both sides
    `p + a·q + (a·b)·t`, anchored to the kernel semiring's `mul_assoc` via `scale_scale`) and
    `gradeCompose_leftUnit`.  The naive same-outer-scalar form is REFUTED
    (`gradeCompose_assoc_naive_isFalse`, at `a=ω, b=1`) — the reindex is load-bearing.
  * **B2 — the enriched-functor grade slice.**  `gradeOf` + the projection / sequential / whisker functor
    laws (composition → `gradeCompose` / `gradeComposePar`) + `gradedVcomp_gradeOf_assoc`
    (functor-over-associativity: the grade legs IDENTIFIED, the cell legs DISTINCT).
  * **B3 — the refusal slice.**  `gradedComposeGuarded` (blocks the composite on over-budget grades) +
    `gradedComposeAtCollisionRow` (the §6.8 `E044` CT × Async row exercised as a genuine composition
    refusal at the non-free locus).
  * **B4 — non-vacuity on real cells + real kernel grades.**  `demoGradedCellOmegaOne` (a real dim-2 cell
    decorated with the ω-scaling-redex App grade `[ω,1]`), the composite computing cell + grade, and the
    refusal firing on real cells (over-budget `none` / within-budget `some` / `E044` blocking a
    within-budget composite). -/

/-- ★ **B1 — the grade-leg composition algebra SHIPPED (r2).**  `= true`: `gradeCompose_assoc` (the
scalar-reindexed associativity, anchored to the kernel semiring's `mul_assoc` via `scale_scale`) +
`gradeCompose_leftUnit`, with the naive same-scalar form refuted (`gradeCompose_assoc_naive_isFalse`).
The carrier + composite are REUSED (`GradedCell` / `gradedVcomp`), not re-founded. -/
def fxOmega5_gradedAssociativityShippedR2 : Bool := true

/-- ★ **B2 — the enriched-functor grade slice SHIPPED (r2).**  `= true`: `gradeOf` (the functor's
object-map) + the projection / sequential / whisker functor laws (composition → `gradeCompose` /
`gradeComposePar`) + `gradedVcomp_gradeOf_assoc`.  This IDENTIFIES the grade legs of the two triple
composites while their CELL legs stay DISTINCT (free `vcomp`) — an identification of grades and a
DISPARITY of cells, stated openly; the cell leg is cited to OMEGA-7. -/
def fxOmega5_enrichedFunctorGradeSliceShippedR2 : Bool := true

/-- ★ **B3/B4 — the refusal slice SHIPPED (r2).**  `= true`: `gradedComposeGuarded` blocks the annotated
composite on over-budget grades (refuses/admits, witnessed on real cells), and
`gradedComposeAtCollisionRow` exercises the §6.8 `E044` (CT × Async) row as a genuine composition refusal
at the non-free locus.  The refusal reads the catalog DATA (the checker content); the underlying
amalgam-collision theorem stays the jam (`fxOmega5_collisionNonFreeLinkReached = false`), and the refusal
is single-dimension (`fxUsageSemiring`) — the product-semiring collision stays
`fxOmega5_productSemiring21Reached = false`. -/
def fxOmega5_collisionRefusalSliceShippedR2 : Bool := true

/-- ★ **The r2 CELL-leg associativity stays CITED, not re-proven.**  `= true` records the HONEST scope
boundary: r2 proves the GRADE-leg associativity ONLY; the annotated-cell composite is NOT associative
(free `CellExpr.vcomp`), so the cell leg is cited to OMEGA-7's `linearizeFull_pasteAlong_assoc` (Tier-0,
un-importable under the layer rule), never re-derived here.  Accordingly
`fxOmega5_appCellLevelCompositionReached` (above) stays `false`. -/
def fxOmega5_r2CellLegAssociativityCitedToOmegaSeven : Bool := true

end FX1Poly.Polygraph.Omega.Graded
