import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPositionGenericMoves

/-! # Polygraph/Omega/WalkingBunchedBimonoidCollisionCanonForm — the Coxeter-free collision canon form: the
`(m,n)` wide collision retracts to the staged bialgebra NF `deltaStage ; wideSwap ; muStage`, the width-`(2,2)`
collision-to-staged-NF convertibility DELIVERED zero-Coxeter (peel-to-generator unit strips + the shipped
width-2 bialgebra brick + one `vcompAssoc`), and the honest verdict that the integer bubble-sort is NOT a valid
sort-to-CONV bridge (it does not preserve the permutation matrix) (WP-PROP r10, #2033)

★ **THE r10 HEADLINE — the collision at the flagship width converts to its staged normal form WITHOUT any
Coxeter word-problem, and the tempting integer-sort bridge is machine-refuted.**  The r8 `RiffleAssembly`
shipped the staged bialgebra NF `bialgebraNF m n := spiderStaged (deltaStage m n) (wideSwap m n) (muStage n m)`
and matched its MATRIX to the wide collision at four generic widths; the r9 `PositionGenericMoves` delivered the
recursion's gate (a) (the generic-position naturality slide).  This file names the retraction target as the
`collisionCanonForm` (definitionally the shipped `bialgebraNF`), truth-probes its matrix against the collision at
`(2,1),(1,2),(2,2),(3,2)` (all `rfl`), and DELIVERS the genuinely-new syntactic content: the `(2,2)` wide
collision `muFold 2 ; deltaFan 2` is CONVERTIBLE over the star scope to the staged bialgebra NF
`bialgebraNormalFormTwoTwo = (delta (x) delta) ; (1 (x) sigma (x) 1) ; (mu (x) mu)` by a chain that uses ONLY the
strict unit / associativity laws and the shipped width-2 `bialgebraProduct` brick — NO Yang-Baxter, NO
`CoxeterWordUnique`, NO bubble-sort.

## Why this is Coxeter-free (the strand arithmetic, worked out)

At width `(2,2)` the peels bottom out immediately: `muFold 2 = (muFold 1 |> a) ; mu_a` with `muFold 1 = id a`, so
the leading factor `whiskerRight (id a) a` strips to `id (a.a)` via `whiskerRightUnit` and vanishes into `mu_a`
by `vcompUnitLeft`; dually `deltaFan 2` strips to `delta_a`.  So `wideCollision 2 2 ~ mu_a ; delta_a`, the shipped
brick `bunchedBimonoidWidthTwoCollisionConv` fires once to reach `bialgebraProductRightLeg`, and a single
`vcompAssoc` re-brackets it to the staged NF `bialgebraNormalFormTwoTwo`.  There is no generated middle `sigma`
to thread past any residual block (the residual `muFold 1` / `deltaFan 1` are identities), so the perm middle is
the bare `middleSwap` on the nose — no permutation word-problem arises.  This is the honest Coxeter-free anchor of
the `(m,n)` recursion: the general `m+2,n+2` arm (where the brick's `sigma` MUST thread past non-trivial
residual blocks via the r9 slides, and the emitted word reconciles with `wideSwap`'s riffle bracketing only up to
Coxeter) stays the named residual.

## The integer-sort bridge is a dead end (the decisive negative control)

The r8 B3 shipped a FUEL-STRUCTURAL bubble sort on the position list as plain `Nat`s.  This file machine-refutes
it as a sort-to-CONV bridge: `permWord [1,0] 3` (the word `s_2 s_1`) and `permWord [0,1] 3` (its integer-sorted
image `s_1 s_2`) evaluate to DIFFERENT permutation matrices — adjacent generators do not commute, so sorting the
positions as integers does NOT preserve the permutation.  A per-swap sort-to-CONV dispatch over this carrier
cannot exist; a real bridge needs a Coxeter-aware normal form (braids on adjacent inversions), which the integer
sort is not.  So r10 takes the Coxeter-free canon route, NOT the sort-bridge route.

## The star does NOT flip

No hypothesis-free inhabitant of `bunchedBimonoidStarStatementAdditiveWellTyped` is produced.  The `(2,2)`
collision-to-NF advances exactly one instance (the flagship, fold-fan) of the star's `vcomp` case and touches
neither the general `spiderOf` retraction nor the equal-matrices middle determinism.  Every upstream star /
recursion marker stays byte-intact `= false`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The collision / staged-NF matrix `rfl` pins evaluate a `matMul` product up to width 3, exceeding the default
heartbeat budget; the raise is a compute allowance only, the proof terms stay `Eq.refl` / congruence-constructor
plumbing, axiom-free (uniform with the r6/r7/r8/r9 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # L1 — THE COLLISION CANON FORM (the retraction target) + its matrix soundness
    # =========================================================================================
-/

/-- ★★ **THE COLLISION CANON FORM `collisionCanonForm m n : a^m => a^n`** — the retraction target of the wide
collision, DEFINITIONALLY the shipped staged bialgebra normal form
`bialgebraNF m n = spiderStaged (deltaStage m n) (wideSwap m n) (muStage n m)`: fan each of the `m` inputs into
`n` copies, route grouped-by-input to grouped-by-output through the general riffle word `wideSwap` (r8), then fold
each output block of `m` into one.  Naming it `collisionCanonForm` records its ROLE — the Coxeter-free canonical
form the `(m,n)` collision `muFold m ; deltaFan n` retracts to — and its matrix matches the collision on the nose
at every probed width (below). -/
def bunchedBimonoidCollisionCanonForm (m n : Nat) : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidBialgebraNF m n

/-! ## L1 truth-probe outputs (the canon matrix equals the collision matrix) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 2 1)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 1)
#eval bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 3 2)
#eval bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 2)

/-- ★ **THE CANON MATCHES THE COLLISION AT `(2,1)` (the degenerate right end).**  `evalCell (collisionCanonForm
2 1) = evalCell (wideCollision 2 1)` (both the `1 x 2` fold row `[[1,1]]`), `rfl` — the `n = 1` collapse where
`deltaFan 1 = id`, the canon's route / mu-stage trivialise, and the collision is the bare fold. -/
theorem bunchedBimonoidCollisionCanonMatchesCollisionTwoOne :
    bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 2 1)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 1) := rfl

/-- ★ **THE CANON MATCHES THE COLLISION AT `(1,2)` (the degenerate left end).**  `evalCell (collisionCanonForm
1 2) = evalCell (wideCollision 1 2)` (both the `2 x 1` copy column `[[1],[1]]`), `rfl` — the `m = 1` collapse. -/
theorem bunchedBimonoidCollisionCanonMatchesCollisionOneTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 1 2)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 1 2) := rfl

/-- ★★ **THE CANON MATCHES THE COLLISION AT `(2,2)` (the flagship base).**  `evalCell (collisionCanonForm 2 2) =
evalCell (wideCollision 2 2)` (both the all-ones `[[1,1],[1,1]]`), `rfl` — the semantic target of the `(2,2)`
convertibility delivered below. -/
theorem bunchedBimonoidCollisionCanonMatchesCollisionTwoTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 2 2)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 2 2) := rfl

/-- ★★ **THE CANON MATCHES THE COLLISION AT `(3,2)` (a genuine wider-than-flagship grid).**  `evalCell
(collisionCanonForm 3 2) = evalCell (wideCollision 3 2)` (both the `2 x 3` all-ones), `rfl` — here the canon's
route is the load-bearing `wideSwap 3 2` (a `6 x 6` perfect shuffle), and the matrix still matches on the nose. -/
theorem bunchedBimonoidCollisionCanonMatchesCollisionThreeTwo :
    bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 3 2)
      = bunchedBimonoidEvalCell (bunchedBimonoidWideCollision 3 2) := rfl

/-- ★ **THE `(2,2)` CANON AND THE CLEAN STAGED NF SHARE THEIR MATRIX.**  `evalCell (collisionCanonForm 2 2) =
evalCell bialgebraNormalFormTwoTwo` (both `[[1,1],[1,1]]`), `rfl`.  The general canon's route at `(2,2)` is
`wideSwap 2 2` (the riffle bracketing) while the CONV below reaches the `middleSwap`-routed staged NF
`bialgebraNormalFormTwoTwo`; the two cells share their map on the nose, so both are legitimate `(2,2)` normal
forms — they differ as CELLS only by the perm-middle word (`wideSwap 2 2` vs `middleSwap`), reconciled only up to
Coxeter (the named residual). -/
theorem bunchedBimonoidCollisionCanonTwoTwoMatchesStagedNF :
    bunchedBimonoidEvalCell (bunchedBimonoidCollisionCanonForm 2 2)
      = bunchedBimonoidEvalCell bunchedBimonoidBialgebraNormalFormTwoTwo := rfl

/-! # =========================================================================================
    # L2 — THE PEEL-TO-GENERATOR UNIT STRIPS (width-2, Coxeter-free CONV atoms)
    # =========================================================================================
-/

/-- ★★ **THE MU-FOLD-TWO STRIP `muFold 2 ~ mu_a`.**  `muFold 2 = (muFold 1 |> a) ; mu_a` with
`muFold 1 = id a`, so the leading factor `whiskerRight (id a) a` strips to `id (a.a)` by the strict
`whiskerRightUnit` row and vanishes into `mu_a` by the strict `vcompUnitLeft` row (the boundary source of `mu_a`
is `a.a` on the nose).  A convertibility over the star scope, fired through the strict sub-theory (`Or.inl`) —
NO Coxeter. -/
theorem bunchedBimonoidMuFoldTwoStripToGen :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidMuFold 2) bunchedBimonoidAddMuGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))))
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAddMuGen)))

/-- ★★ **THE DELTA-FAN-TWO STRIP `deltaFan 2 ~ delta_a`.**  The dual: `deltaFan 2 = delta_a ; (deltaFan 1 |> a)`
with `deltaFan 1 = id a`, so the trailing factor `whiskerRight (id a) a` strips to `id (a.a)` by
`whiskerRightUnit` and vanishes into `delta_a` by `vcompUnitRight` (the boundary target of `delta_a` is `a.a`).
NO Coxeter. -/
theorem bunchedBimonoidDeltaFanTwoStripToGen :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidDeltaFan 2) bunchedBimonoidAddDeltaGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddDeltaGen
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))))
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAddDeltaGen)))

/-! # =========================================================================================
    # L3 — THE FLAGSHIP (2,2) COLLISION-TO-STAGED-NF CONVERTIBILITY (Coxeter-free)
    # =========================================================================================
-/

/-- ★★ **THE `(2,2)` COLLISION STRIPS TO THE WIDTH-2 BRICK `wideCollision 2 2 ~ mu_a ; delta_a`.**  Rewrite the
left factor `muFold 2 ~ mu_a` (`vcompCongrLeft`) and the right factor `deltaFan 2 ~ delta_a` (`vcompCongrRight`)
of `wideCollision 2 2 = muFold 2 ; deltaFan 2`, landing on the bare width-2 collision `mu_a ; delta_a` the shipped
bialgebra brick fires on.  NO Coxeter. -/
theorem bunchedBimonoidWideCollisionTwoTwoStripToBrick :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidWideCollision 2 2)
      (CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddDeltaGen) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft (bunchedBimonoidDeltaFan 2)
      bunchedBimonoidMuFoldTwoStripToGen)
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddMuGen
      bunchedBimonoidDeltaFanTwoStripToGen)

/-- ★★★ **THE FLAGSHIP (2,2) COLLISION-TO-STAGED-NF CONVERTIBILITY — Coxeter-free.**  The wide collision
`wideCollision 2 2 = muFold 2 ; deltaFan 2` is CONVERTIBLE over the star scope to the staged bialgebra normal
form `bialgebraNormalFormTwoTwo = (delta (x) delta) ; (1 (x) sigma (x) 1) ; (mu (x) mu)`, by the chain: strip to
the width-2 brick (`...StripToBrick`, strict unit laws only), fire the shipped width-2 `bialgebraProduct` brick
(`bunchedBimonoidWidthTwoCollisionConv`) to reach `bialgebraProductRightLeg`, and re-bracket by a single
`vcompAssoc` to the `spiderStaged` shape.  The complete chain uses ONLY the strict `whiskerRightUnit` /
`vcompUnitLeft` / `vcompUnitRight` / `vcompAssoc` rows and the one `bialgebraProduct` sound row — NO Yang-Baxter,
NO `CoxeterWordUnique`, NO bubble-sort.  This is the honest Coxeter-free anchor of the `(m,n)` collision
recursion. -/
theorem bunchedBimonoidWideCollisionTwoTwoConvToStagedNF :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidWideCollision 2 2) bunchedBimonoidBialgebraNormalFormTwoTwo :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.trans bunchedBimonoidWideCollisionTwoTwoStripToBrick
      bunchedBimonoidWidthTwoCollisionConv)
    (SaturatedConvOverWithId.symm
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidDeltaTensorDelta bunchedBimonoidMiddleSwap
          bunchedBimonoidMuTensorMu))))

/-! # =========================================================================================
    # L4 — THE INTEGER-SORT BRIDGE IS A DEAD END (the decisive negative control)
    # =========================================================================================
-/

/-! ## L4 truth-probe outputs (the integer sort disagrees with the permutation) -/

#eval bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0] 3)
#eval bunchedBimonoidEvalCell (bunchedBimonoidPermWord
  (bunchedBimonoidBubbleSortFuel (bunchedBimonoidInversionFuelBound 2) [1, 0]) 3)

/-- The word `permWord [1,0] 3` (`s_2 s_1`) evaluates to `[[0,0,1],[1,0,0],[0,1,0]]`, `rfl`. -/
theorem bunchedBimonoidPermWordOneZeroMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0] 3)
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [1, 0, 0], [0, 1, 0]] } := rfl

/-- The integer-sorted word `permWord (bubbleSortFuel _ [1,0]) 3 = permWord [0,1] 3` (`s_1 s_2`) evaluates to the
DIFFERENT matrix `[[0,1,0],[0,0,1],[1,0,0]]`, `rfl`. -/
theorem bunchedBimonoidPermWordSortedOneZeroMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord
        (bunchedBimonoidBubbleSortFuel (bunchedBimonoidInversionFuelBound 2) [1, 0]) 3)
      = { rows := 3, cols := 3, entries := [[0, 1, 0], [0, 0, 1], [1, 0, 0]] } := rfl

/-- ★★★ **THE INTEGER BUBBLE-SORT DOES NOT PRESERVE THE PERMUTATION MATRIX (route-6 is a dead end).**  The word
`permWord [1,0] 3` (`s_2 s_1`) and its integer-sorted image `permWord (bubbleSortFuel _ [1,0]) 3 = permWord
[0,1] 3` (`s_1 s_2`) evaluate to DIFFERENT `3 x 3` permutation matrices (they differ in the `(1,0)` entry: `1`
vs `0`).  Adjacent Coxeter generators do not commute, so sorting the position list as plain integers does NOT
preserve the permutation — a per-swap "sorted-determinism-to-CONV" dispatch over this carrier is impossible.  The
decisive negative control that justifies the Coxeter-free canon route over the integer-sort bridge. -/
theorem bunchedBimonoidBubbleSortNotMatrixPreserving :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0] 3)
      ≠ bunchedBimonoidEvalCell (bunchedBimonoidPermWord
          (bunchedBimonoidBubbleSortFuel (bunchedBimonoidInversionFuelBound 2) [1, 0]) 3) :=
  fun heq => Nat.noConfusion
    (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 0) heq)

/-! # =========================================================================================
    # L5 — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (L1) — the collision canon form is named and matrix-correct.**  `= true` records
`bunchedBimonoidCollisionCanonForm` (the retraction target, definitionally the shipped staged `bialgebraNF`) and
`bunchedBimonoidCollisionCanonMatchesCollision{TwoOne,OneTwo,TwoTwo,ThreeTwo}` — the canon and the wide collision
share their `Mat(N)` map on the nose at the four probed widths, including the wider-than-flagship `(3,2)` where
the canon's route is the load-bearing `wideSwap 3 2`. -/
def fxBunchedBimonoid_collisionCanonFormMatrixCorrect : Bool := true

/-- ★★★ **ESTABLISHED (L3) — the flagship `(2,2)` collision converts to its staged NF, Coxeter-free.**  `= true`
records `bunchedBimonoidWideCollisionTwoTwoConvToStagedNF`: `wideCollision 2 2 ~ bialgebraNormalFormTwoTwo` over
the star scope, via the two peel-to-generator unit strips (`bunchedBimonoid{MuFoldTwo,DeltaFanTwo}StripToGen`),
the shipped width-2 `bialgebraProduct` brick (`bunchedBimonoidWidthTwoCollisionConv`), and a single `vcompAssoc`.
The chain uses ONLY strict unit / associativity rows + the one bialgebra sound row — NO Yang-Baxter, NO
`CoxeterWordUnique`, NO bubble-sort.  The Coxeter-free anchor of the `(m,n)` collision recursion. -/
def fxBunchedBimonoid_collisionTwoTwoConvToStagedNFCoxeterFree : Bool := true

/-- ★★★ **ESTABLISHED (L4) — the integer bubble-sort is NOT a valid sort-to-CONV bridge.**  `= true` records
`bunchedBimonoidBubbleSortNotMatrixPreserving`: the word `permWord [1,0] 3` and its integer-sorted image
`permWord [0,1] 3` evaluate to DIFFERENT permutation matrices (adjacent generators do not commute), so the r8 B3
fuel-structural integer sort does NOT preserve the permutation — a per-swap sorted-determinism-to-CONV dispatch
over this carrier is impossible.  The decisive negative control justifying the Coxeter-free canon route. -/
def fxBunchedBimonoid_integerSortNotMatrixPreserving : Bool := true

/-- ★ **THE GENERAL `(m+2,n+2)` COLLISION ARM STAYS GATED — no flip (exact residual named).**  `= false` records
that beyond the Coxeter-free `(2,2)` anchor (L3) the general recursion step is NOT shipped: the `m+2,n+2` peel
generates a middle `sigma` that MUST be threaded past the non-trivial residual `muFold m` / `deltaFan n` blocks
via the r9 `bunchedBimonoid{Mu,Delta}NaturalitySlideAtPosition` slides, and the emitted permutation word
reconciles with the canon's route `wideSwap` (the riffle bracketing) only up to Coxeter — the bracket-match
`collisionRoute (m,n) ~ wideSwap (m,n)` is exactly the walled `CoxeterWordUnique` content
(`fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid`, r8, byte-intact).  The `(2,2)` anchor sidesteps this
because its residual blocks are identities (no `sigma` to thread, the perm middle is the bare `middleSwap`); the
general arm is the honest r11 residual. -/
def fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r10: no literal hypothesis-free inhabitant
is produced.  The `(2,2)` collision-to-NF advances exactly one instance (the flagship fold-fan) of the star's
`vcomp` case and touches neither the general `spiderOf` retraction nor the equal-matrices middle determinism.
The star-owning marker `fxBunchedBimonoid_correctedWellTypedStarStillOpen` (StarAssembly, r7) and every upstream
star marker keep their name and `= false` value byte-intact (cross-file, not edited) — NO fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonForm : Bool := false

/-- ★★★ **ESTABLISHED (L5) — the WP-PROP r10 collision-canon-form ledger (the honest scoreboard).**  `= true`
records the complete r10 round: L1 the collision canon form named + matrix-correct at four widths
(`fxBunchedBimonoid_collisionCanonFormMatrixCorrect`); L3 the flagship `(2,2)` collision-to-staged-NF
convertibility DELIVERED Coxeter-free
(`fxBunchedBimonoid_collisionTwoTwoConvToStagedNFCoxeterFree` — unit strips + the shipped brick + one
`vcompAssoc`, no Coxeter); L4 the integer bubble-sort machine-refuted as a sort-to-CONV bridge
(`fxBunchedBimonoid_integerSortNotMatrixPreserving`).  The general `(m+2,n+2)` arm stays gated on the
bracket-match Coxeter content (`fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch = false`); the star
does NOT flip (`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonForm = false`).  Every upstream wall
keeps its name and value byte-intact (cross-file, not edited); zero-axiom (per-decl `#assert_no_axioms` +
independent `#print axioms` in the twin); STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_collisionCanonFormRoundTenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
