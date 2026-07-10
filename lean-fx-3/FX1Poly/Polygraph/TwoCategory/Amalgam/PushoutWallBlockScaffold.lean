import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallBlockScaffold — the wall-BLOCK read-off + the machine-checked
REFUTATION of dom-to-cod wall-block conservation (WP-AMALG-2 r8, B1)

The r7 ledger (`PushoutFactorizationInductionLedger.lean`, `PushoutVcompInterchangeSplice.lean`) narrowed the
residual to a top-level `pushoutFactorize` whose reconstruction bridge is "keyed to B1's wall skeleton"
(`wallLetterCount_dom_eq_cod`), and whose vcomp-case alignment was to ZIP the two recursive layouts because their
wall-block LISTS agree.  r8 TRUTH-PROBES that alignment premise FIRST — and it is FALSE.

## The finding: the wall-block LIST is NOT a dom-to-cod invariant (only the COUNT is)

`PushoutWallCountInvariance.lean` (r6) proved the wall COUNT is conserved dom-to-cod for every pushout 2-cell
(`wallLetterCount_dom_eq_cod`).  The recon's vcomp zip needed the strictly stronger `wallBlocks_dom_eq_cod`: the
ordered LIST of `s`-blocks (the shipped `pushoutWallBlocks` from `blockDecompose`) is dom/cod-identical.  That
STRONGER statement is refuted by a concrete cell:

  `unitSplitsWallCell := whiskerLeft s (whiskerRight s eta)  :  s·s  ==>  s·t·s`

The unit generator `eta : t^0 ==> t` (a WIRE-CREATING generator, `t^0` empty domain), whiskered by `s` on both
sides, CREATES a fresh `t` BETWEEN the two `s`-walls.  So the domain word `s·s` has ONE wall-block `[[s, s]]`
(the two `s`'s are adjacent — one maximal run), while the codomain word `s·t·s` has TWO wall-blocks `[[s], [s]]`
(the fresh `t` splits the run).  The COUNT is preserved (both `2`); the GROUPING is not.

## Why this matters — the recon's vcomp zip is blocked, and residual (iii) is now concrete

The recon's factorization alignment (zip `pairsU` and `pairsL` because they share a rigid wall scaffold) DEPENDS
on the wall-block list being a dom/cod invariant.  It is not: the `s`-blocks SPLIT and MERGE as wire-creating
generators fire, so there is NO dom/cod-invariant wall skeleton finer than the total count, and the total count is
too coarse to key the per-gap zip (it cannot tell `[[s, s]]` from `[[s], [s]]`).  This is exactly the master
demand's residual (iii) — "the unit/counit WIRE-CREATING generators break the convex-block projection"
(`DispatchSaturated.lean`) — now a MACHINE-CHECKED counterexample rather than prose.

The factorization GOAL itself is NOT refuted (see `PushoutLayoutFactorization.lean`: this very cell factors as a
single `eta`-gap between two `s`-walls).  What is refuted is the recon's wall-block-keyed ALIGNMENT STRATEGY for
the general vcomp case.  #2043 does NOT close; nothing flips.

## What ships (each zero-axiom, STRUCTURAL / `rfl`, ASCII-only)

  * **`pushoutPathWord`** — read the boundary WORD off a pushout 1-cell path (feeds the shipped `blockDecompose`).
  * **`unitSplitsWallCell`** + **`unitSplitsWallDom` / `unitSplitsWallCod`** — the wall-splitting witness and its
    boundaries.
  * **`unitSplitsWall_dom_wallBlocks` / `unitSplitsWall_cod_wallBlocks`** — the domain reads as `[[s, s]]`, the
    codomain as `[[s], [s]]` (each `rfl`, through the shipped `pushoutWallBlocks`).
  * **`unitSplitsWall_wallBlockCount_domCod_differ`** — the two wall-block lists have DIFFERENT length (1 vs 2):
    the refutation of `wallBlocks_dom_eq_cod`.
  * **`unitSplitsWall_wallCount_preserved`** — yet the wall COUNT is conserved (via `wallLetterCount_dom_eq_cod`):
    the refutation is precise — count yes, blocks no.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The boundary WORD of a pushout 1-cell path -/

/-- The **boundary word** of a pushout 1-cell path — each `cons` letter's generator index, read off the path so the
shipped `blockDecompose` / `pushoutWallBlocks` (which operate on WORDS) apply to a cell's boundary.  Structural on
the path; the empty path is the empty word. -/
def pushoutPathWord : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode →
    List (Fin involutionMonadPushout.modalityGenerators.length)
  | _, _, .nil _ => []
  | _, _, .cons letter rest => letter.val :: pushoutPathWord rest

/-! ## The wall-splitting witness cell and its boundaries -/

/-- The **domain 1-cell** `s·s` of the wall-splitting witness — two adjacent `s`-walls (ONE maximal run). -/
def unitSplitsWallDom : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  composePath monadPushSPath
    (composePath (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
      monadPushSPath)

/-- The **codomain 1-cell** `s·t·s` of the wall-splitting witness — the fresh `t` (created by `eta`) SPLITS the run
into two `s`-walls. -/
def unitSplitsWallCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  composePath monadPushSPath (composePath monadPushTPath monadPushSPath)

/-- ★★★ **THE WALL-SPLITTING WITNESS.**  `whiskerLeft s (whiskerRight s eta) : s·s ==> s·t·s` — the unit generator
`eta : t^0 ==> t` whiskered by an `s` on each side.  Because `eta`'s domain is empty (`t^0`), the cell CREATES a
`t` between the two `s`-walls: the domain `s·s` and the codomain `s·t·s` have the SAME `s`-count but DIFFERENT
`s`-block structure.  This is the concrete cell that refutes dom-to-cod wall-block conservation. -/
def unitSplitsWallCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature unitSplitsWallDom unitSplitsWallCod :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushSPath
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature) monadPushSPath pushoutEta)

/-! ## The refutation: the wall-block LIST is not conserved dom-to-cod -/

/-- ★★ The domain `s·s` has ONE wall-block `[[s, s]]` — the two `s`'s form a single maximal run (`rfl`, through the
shipped `pushoutWallBlocks` / `blockDecompose`). -/
theorem unitSplitsWall_dom_wallBlocks :
    pushoutWallBlocks (pushoutPathWord unitSplitsWallDom) = [[sLetter, sLetter]] := rfl

/-- ★★ The codomain `s·t·s` has TWO wall-blocks `[[s], [s]]` — the fresh `t` (created by `eta`) splits the run
(`rfl`).  Contrast `unitSplitsWall_dom_wallBlocks`: SAME cell's two boundaries, DIFFERENT wall-block lists. -/
theorem unitSplitsWall_cod_wallBlocks :
    pushoutWallBlocks (pushoutPathWord unitSplitsWallCod) = [[sLetter], [sLetter]] := rfl

/-- ★★★ **THE REFUTATION of `wallBlocks_dom_eq_cod`.**  The domain and codomain wall-block lists of
`unitSplitsWallCell` have DIFFERENT length (`1` vs `2`), so they are NOT equal: the recon's premise "the ordered
list of `s`-blocks of dom equals that of cod" is FALSE.  Proved structurally through the two `rfl` block
computations (no `decide`, no propext): after rewriting, the goal is `1 ≠ 2`, discharged by `Nat.noConfusion` on
the injected successor equality. -/
theorem unitSplitsWall_wallBlockCount_domCod_differ :
    (pushoutWallBlocks (pushoutPathWord unitSplitsWallDom)).length
      ≠ (pushoutWallBlocks (pushoutPathWord unitSplitsWallCod)).length := by
  rw [unitSplitsWall_dom_wallBlocks, unitSplitsWall_cod_wallBlocks]
  intro hlen
  exact Nat.noConfusion (Nat.succ.inj hlen)

/-- ★★ **The refutation is PRECISE — the wall COUNT is still conserved.**  Despite the block lists differing, the
total `s`-count is dom/cod-equal (`2 = 2`), via the shipped r6 invariant `wallLetterCount_dom_eq_cod` applied to
`unitSplitsWallCell`.  So the correct reading is: the wall COUNT is a dom-to-cod invariant, the wall-block GROUPING
is not — the wire-creating `eta` splits an `s`-block without changing the `s`-count. -/
theorem unitSplitsWall_wallCount_preserved :
    pushoutPathWallCount unitSplitsWallDom = pushoutPathWallCount unitSplitsWallCod :=
  wallLetterCount_dom_eq_cod unitSplitsWallCell

/-! ## Observability — the split, computed -/

-- The domain `s·s` wall-blocks: expect `[[0, 0]]` (one block of two s's).
#eval (pushoutWallBlocks (pushoutPathWord unitSplitsWallDom)).map (fun block => block.map Fin.val)
-- The codomain `s·t·s` wall-blocks: expect `[[0], [0]]` (two blocks of one s each).
#eval (pushoutWallBlocks (pushoutPathWord unitSplitsWallCod)).map (fun block => block.map Fin.val)
-- The wall COUNTS: expect `(2, 2)` (conserved).
#eval (pushoutPathWallCount unitSplitsWallDom, pushoutPathWallCount unitSplitsWallCod)

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the wall-block LIST is NOT a dom-to-cod invariant (WP-AMALG-2 r8, B1).**  `= true`: the
concrete cell `unitSplitsWallCell` (`whiskerLeft s (whiskerRight s eta) : s·s ==> s·t·s`) has domain wall-blocks
`[[s, s]]` (one block) and codomain wall-blocks `[[s], [s]]` (two blocks), through the SHIPPED `pushoutWallBlocks` /
`blockDecompose` (`unitSplitsWall_dom_wallBlocks` / `unitSplitsWall_cod_wallBlocks`, `rfl`); their lengths differ
(`unitSplitsWall_wallBlockCount_domCod_differ`), while the total wall COUNT is conserved
(`unitSplitsWall_wallCount_preserved`, via r6's `wallLetterCount_dom_eq_cod`).  This REFUTES the recon's
`wallBlocks_dom_eq_cod` — the premise its vcomp-case zip relied on — and makes the master demand's residual (iii)
(`DispatchSaturated.lean`: "the unit/counit WIRE-CREATING generators break the convex-block projection") a
machine-checked fact: the wire-creating `eta` (`t^0 ==> t`) splits an `s`-block.  The factorization GOAL is not
refuted (see `PushoutLayoutFactorization.lean`); the recon's wall-block-keyed ALIGNMENT strategy is.  #2043 does
NOT close.  `= true`. -/
def fxAmalg_wallBlockListNotDomCodInvariant : Bool := true

end FX1Poly.Polygraph.Amalgam
