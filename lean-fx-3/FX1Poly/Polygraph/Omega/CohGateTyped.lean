import FX1Poly.Polygraph.Omega.PsContextTyped
import FX1Poly.Polygraph.Omega.CohSeed

/-! # Polygraph/Omega/CohGateTyped — the CaTT coherence FULLNESS gate, typed over the ps-telescope
    (OMEGA-6 r2, B2)

★ **Where the typed telescope becomes LOAD-BEARING — the CaTT `coh` fullness side-condition, decided over the
r2 ps-telescope.**  r1's `CohRow` (`CohSeed.lean`) carries a checked ps-context and a parallel boundary as
INDEPENDENT fields; its docstring names the two things it does NOT enforce, both deferred: the CaTT **fullness**
side-condition ("every variable of the ps-context occurs in the boundary") and the typed link that the
boundary lives OVER the ps-context.  With B1's typed telescope in hand, r2 decides fullness structurally.

## Fullness, decidably, on the telescope side (pure Polygraph, no CellExpr realization)

A CaTT `coh` over a ps-context `Γ` fills a parallel pair `(source, target)` of a common base type; the
FULLNESS rule demands every variable of `Γ` be used by the source, the target, or the base type.  Fullness
inspects exactly the VARIABLE SUPPORT (the set of de Bruijn levels) of the three, which is fully reachable
without touching CellExpr realization (that is OMEGA-7):

  * `varsOfTeleType` — the levels a boundary type mentions;
  * `levelsUpTo` / `natElem` — the ps-context's level set and decidable membership;
  * ★ `cohFullnessCheck` — every level of `Γ` is covered by `srcSupp ∪ tgtSupp ∪ vars(base)`, and the supports
    are well-scoped (`< length Γ`).  A `Bool` decision, propext-clean (full enumeration + `Nat.blt`/`Nat.beq`).

## The typed coh row and the forgetful MAP (honesty guard)

`CohRowTyped` is an r1 `CohRow` ENRICHED with the typed boundary data (`base`, `srcSupp`, `tgtSupp`) and the
fullness proof over the row's OWN ps-context.  `cohRowTypedForget` is a genuine forgetful MAP back to the r1
row (a projection sharing the underlying row) — NOT a variable-disjoint conjunction of "typed gate AND r1
gate".  This is the conjunction-vs-identification discipline: the typed and untyped gates are identified
THROUGH the shared `underlying` row, never paired as independent facts.

## Non-vacuity — the rejection witness (typing is LOAD-BEARING)

  * POSITIVE (`arrowDiskCohRowTyped`): over the 1-disk ps-context `(x)(y)(f)` a coherence whose boundary uses
    `f` and whose base type `x ->_* y` uses `x, y` — fullness HOLDS (`= true`).
  * ★ NEGATIVE (`interchangeMissingMiddleCoh`): over the horizontal-composite ps-context
    `(x)(y)(z)(f,g,a)(h,k,b)` — whose SHARED MIDDLE object `y` sits at level 1 — a boundary whose source
    support is the left half `{x,f,g,a} = {0,2,3,4}` and target support is the right half `{z,h,k,b} =
    {5,6,7,8}`, so the middle `y` is used by NEITHER.  The r1 skeleton ADMITS this (the ps-context CHECKS,
    `overRowChecks`, and a parallel `CellExpr` pair exists — `interchangeCohRow`); the TYPED gate REJECTS it
    (`cohFullnessCheck ... = false`, by `rfl`).  A coherence r1 admits by independent fields but typing rejects
    once the boundary is typed over `Γ` — the concrete demonstration that fullness/typing is load-bearing.

Raw Lean 4 + Init, STRUCTURAL only, ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## Variable support and the level set -/

/-- The **variable support** of a boundary type — the de Bruijn levels it mentions.  `star` mentions nothing;
a hom `s ->_base t` mentions `s`, `t`, and recursively the levels of `base`. -/
def varsOfTeleType : TeleType → List Nat
  | .star => []
  | .arrow base sourceLevel targetLevel => sourceLevel :: targetLevel :: varsOfTeleType base

/-- The **levels of a telescope**, `[length-1, …, 1, 0]` (descending; order is irrelevant to the coverage
`.all`).  A plain structural count-down — computes by `rfl`, no `List.range` dependency. -/
def levelsUpTo : Nat → List Nat
  | 0 => []
  | count + 1 => count :: levelsUpTo count

/-- Decidable **membership** of a level in a support list — cons-recursive `Nat.beq`, propext-clean (avoids
the `List.find?` / `List.elem`-instance route). -/
def natElem : Nat → List Nat → Bool
  | _, [] => false
  | target, head :: rest => Nat.beq target head || natElem target rest

/-- ★ **The CaTT fullness gate, decided over the ps-telescope.**  `cohFullnessCheck Γ base srcSupp tgtSupp`
holds iff every de Bruijn level of `Γ` is covered by the source support, the target support, or the base
type's variables (the CaTT fullness rule), AND both supports are well-scoped (`< length Γ`).  A `Bool`
decision — full enumeration + `Nat.blt`/`Nat.beq`, propext-clean. -/
def cohFullnessCheck (telescope : PsTelescope) (base : TeleType) (srcSupp tgtSupp : List Nat) : Bool :=
  (levelsUpTo telescope.length).all
      (fun level => natElem level srcSupp || natElem level tgtSupp || natElem level (varsOfTeleType base))
    && srcSupp.all (fun level => Nat.blt level telescope.length)
    && tgtSupp.all (fun level => Nat.blt level telescope.length)

/-! ## The typed coherence row and the forgetful map -/

/-- ★ A **typed coherence row** — an r1 `CohRow` ENRICHED with the typed boundary data (`base`, `srcSupp`,
`tgtSupp`) and a proof that the boundary is FULL over the row's OWN ps-context.  The `underlying` field makes
the typed / untyped relationship an identification through a shared row (via `cohRowTypedForget`), not a
variable-disjoint conjunction. -/
structure CohRowTyped (computad : OmegaComputad) (dim : Nat) where
  /-- The boundary base type `B` (the common type of the parallel `source` / `target`). -/
  base : TeleType
  /-- The de Bruijn levels the source boundary uses. -/
  srcSupp : List Nat
  /-- The de Bruijn levels the target boundary uses. -/
  tgtSupp : List Nat
  /-- The r1 coherence row this enriches (carries the CellExpr boundary, parallelism, and ps-check). -/
  underlying : CohRow computad dim
  /-- The boundary is FULL over the underlying row's ps-context (the CaTT fullness side-condition, decided). -/
  fullnessOverPs :
    cohFullnessCheck (telescopeOf (elaboratePsContext underlying.psContext)) base srcSupp tgtSupp = true

/-- ★ **The forgetful MAP** `CohRowTyped → CohRow` — a genuine projection sharing the underlying row.  The
typed gate is the r1 gate PLUS fullness, identified through this map (never a disjoint pairing). -/
def cohRowTypedForget {computad : OmegaComputad} {dim : Nat} (row : CohRowTyped computad dim) :
    CohRow computad dim := row.underlying

/-! ## Non-vacuity 1 — the positive witness (fullness HOLDS over the 1-disk) -/

/-- The **1-disk ps-context** `(x)(y)(f)` — `pss`, `pse`, then `psd` back to the object `y`.  CHECKS as a
completed ps-context (focus returns to dimension 0). -/
def arrowDiskPsContext : PsContextRow := .drop (.extend .start)

/-- The 1-disk CHECKS at the typed level. -/
theorem arrowDiskPsContext_psTyped : psTypedCheck arrowDiskPsContext = true := rfl

/-- The **1-disk coherence row** (r1) — the checked 1-disk ps-context filled by the parallel 1-cell pair
`(oneCellGen, oneCellId)` (both `objectCell → objectCell`, parallel by `rfl`), mirroring `twoGlobeCohRow`. -/
def arrowDiskCohRow : CohRow demoComputad 1 where
  psContext := arrowDiskPsContext
  psContextChecks := rfl
  cohLabel := ()
  source := oneCellGen
  target := oneCellId
  boundaryParallel := ⟨rfl, rfl⟩

/-- ★ The **1-disk typed coherence row** — the coherence's source boundary uses `f` (level 2), its base type
`x ->_* y` (`arrow star 0 1`) uses `x, y` (levels 0, 1): fullness covers the whole ps-context `{0,1,2}`. -/
def arrowDiskCohRowTyped : CohRowTyped demoComputad 1 where
  base := TeleType.arrow TeleType.star 0 1
  srcSupp := [2]
  tgtSupp := [2]
  underlying := arrowDiskCohRow
  fullnessOverPs := rfl

/-- ★ Fullness HOLDS for the positive witness (non-vacuity of `cohFullnessCheck = true`). -/
theorem arrowDiskCohRowTyped_fullnessHolds :
    cohFullnessCheck (telescopeOf (elaboratePsContext arrowDiskCohRowTyped.underlying.psContext))
      arrowDiskCohRowTyped.base arrowDiskCohRowTyped.srcSupp arrowDiskCohRowTyped.tgtSupp = true :=
  arrowDiskCohRowTyped.fullnessOverPs

/-- ★ The forgetful map returns the underlying r1 row (the identification, by `rfl`). -/
theorem arrowDiskCohRowTyped_forgetIsUnderlying :
    cohRowTypedForget arrowDiskCohRowTyped = arrowDiskCohRow := rfl

/-! ## Non-vacuity 2 — the rejection witness (typing is LOAD-BEARING) -/

/-- A **rejected typed boundary** — a boundary whose ps-context the r1 skeleton ADMITS (`overRowChecks`) but
whose typing over that ps-context a `CohRowTyped` could not carry.  The `_fullnessFails` theorem witnesses the
rejection. -/
structure RejectedTypedBoundary where
  /-- The ps-context the coherence is built over. -/
  overRow : PsContextRow
  /-- The r1 skeleton ADMITS the ps-context (the r1 gate passes). -/
  overRowChecks : psContextCheck overRow = true
  /-- The boundary base type. -/
  base : TeleType
  /-- The source boundary support. -/
  srcSupp : List Nat
  /-- The target boundary support. -/
  tgtSupp : List Nat

/-- ★ **The interchange coherence with the SHARED MIDDLE object omitted.**  Over the horizontal-composite
ps-context `(x)(y)(z)(f,g,a)(h,k,b)` — whose shared middle object `y` sits at level 1 — the source support is
the left half `{x,f,g,a} = {0,2,3,4}` and the target support is the right half `{z,h,k,b} = {5,6,7,8}`, so `y`
is used by NEITHER (base `star` mentions nothing).  The r1 skeleton admits this (the ps-context checks). -/
def interchangeMissingMiddleCoh : RejectedTypedBoundary where
  overRow := horizontalCompositePsContext
  overRowChecks := horizontalCompositePsContext_checks
  base := TeleType.star
  srcSupp := [0, 2, 3, 4]
  tgtSupp := [5, 6, 7, 8]

/-- ★ **The r1 skeleton ADMITS the interchange-missing-middle coherence** — its ps-context CHECKS (the r1 gate
passes; a parallel `CellExpr` pair exists, `interchangeCohRow`). -/
theorem interchangeMissingMiddleCoh_r1Admits :
    psContextCheck interchangeMissingMiddleCoh.overRow = true :=
  interchangeMissingMiddleCoh.overRowChecks

/-- ★ **The TYPED gate REJECTS it** — `cohFullnessCheck` over the horizontal-composite telescope returns
`false` (by `rfl`), because the shared middle object `y` at level 1 is covered by NEITHER support nor the
base type.  A coherence r1 admits by independent fields but typing rejects once the boundary is typed over the
ps-context: the concrete demonstration that fullness/typing is LOAD-BEARING. -/
theorem interchangeMissingMiddleCoh_fullnessFails :
    cohFullnessCheck (telescopeOf (elaboratePsContext interchangeMissingMiddleCoh.overRow))
      interchangeMissingMiddleCoh.base interchangeMissingMiddleCoh.srcSupp
      interchangeMissingMiddleCoh.tgtSupp = false := rfl

end FX1Poly.Polygraph.Omega
