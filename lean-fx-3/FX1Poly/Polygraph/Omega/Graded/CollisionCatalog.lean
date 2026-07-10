/-! # Polygraph/Omega/Graded/CollisionCatalog — the §6.8 soundness-collision catalog, as DATA
(OMEGA-5 r1, B4)

The wall of the graded round: the 21 dimensions are NOT orthogonal.  fx_design.md §6.8 catalogs the
known soundness COLLISIONS — pairs (and one triple) of dimensions that are not signature-disjoint.  In
the amalgamated-product reading (the 21-dim checker = one enriched ω-functor into the amalgamated
product of the dimension theories), each collision is a locus where the amalgam is NOT a free product,
so the Nelson-Oppen / Pigozzi / Baader-Tinelli modular decidability transfer (which requires disjoint
signatures) FAILS.  **The §6.8 catalog IS the non-free locus of the 21-dimension amalgam.**

This file records that catalog as machine-readable DATA — nine rows, each flagged `isFreeLocus := false`
(the non-free markers), so the honest fact "these dimension pairs do not amalgamate freely" is a checked
datum, not prose.  The strongest is `E044` (CT × Async): contradictory — NO refinement permits it.

## The nine collisions (fx_design.md §6.8)

| code | dimensions                       | gap  | note                                   |
|------|----------------------------------|------|----------------------------------------|
| I002 | classified × Fail                | 102  | error payload carries classified data  |
| L002 | borrow × Async                   | 104  | borrow live across `await`             |
| E044 | CT × Async                       | 105  | CONTRADICTORY — no refinement permits   |
| I003 | CT × Fail on secret              | 106  | secret-dependent `fail` leaks branch    |
| M012 | monotonic × concurrent           | 108  | needs `atomic(T)` / lock_free           |
| P002 | ghost × runtime conditional      | 109  | erased value in runtime scrutinee       |
| I004 | classified × async × session     | 112  | 3-WAY collision                         |
| N002 | decimal × overflow(wrap)         | 113  | wrap meaningless for exact decimal      |
| L003 | borrow × unscoped spawn          | 114  | use `task_group`                        |

## What is DATA here vs DEFERRED

DATA (this file): the catalog + the per-row `isFreeLocus := false` non-free markers + the arity of the
3-way collision + the contradictory-locus marker.  DEFERRED (r1 ledger): the LINK theorem
`collisionPair d1 d2 → ¬ disjointSignatures d1 d2 → modular transfer fails` — a stated correspondence
whose PROOF needs the disjointness predicate wired to dimension pairs and the amalgam's dispatch
hypothesis (`computadGeneratorsDisjoint`, Amalgam lane).  Nothing is proven about the amalgam itself
this round.

## Zero-axiom verification

`CollisionRow` is a plain record; `sixEightCatalog` is a list literal; the non-vacuity witnesses are
structural `List.length` / field projections closed by `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph.Omega.Graded

/-- A dimension identifier — a §6.1 dimension named by its surface keyword (`"classified"`, `"CT"`, …). -/
abbrev DimId : Type := String

/-- One row of the §6.8 soundness-collision catalog: the colliding dimensions, the compiler error code,
the tracked design-gap id, and whether the locus is a FREE (signature-disjoint, amalgamates freely)
product locus.  Every §6.8 collision has `isFreeLocus := false` — that is the point. -/
structure CollisionRow where
  /-- The colliding dimensions (two, or three for the one 3-way collision). -/
  dims : List DimId
  /-- The compiler error code fx_design.md §6.8 assigns the collision. -/
  errorCode : String
  /-- The `gaps.json` id tracking the collision. -/
  gapId : Nat
  /-- Whether the amalgam is FREE at this locus.  `false` for every §6.8 collision (the non-free
  marker): the dimensions share signature, so the modular decidability transfer does not apply. -/
  isFreeLocus : Bool

/-! ## The nine collision rows -/

/-- I002 — classified × Fail: the error payload carries classified data (gap 102). -/
def collisionClassifiedFail : CollisionRow :=
  { dims := ["classified", "Fail"], errorCode := "I002", gapId := 102, isFreeLocus := false }

/-- L002 — borrow × Async: a borrow lives across an `await` (gap 104). -/
def collisionBorrowAsync : CollisionRow :=
  { dims := ["borrow", "Async"], errorCode := "L002", gapId := 104, isFreeLocus := false }

/-- E044 — CT × Async: CONTRADICTORY, no refinement permits it — the sharpest collision (gap 105). -/
def collisionCtAsync : CollisionRow :=
  { dims := ["CT", "Async"], errorCode := "E044", gapId := 105, isFreeLocus := false }

/-- I003 — CT × Fail on secret: a secret-dependent `fail` leaks the branch (gap 106). -/
def collisionCtFailSecret : CollisionRow :=
  { dims := ["CT", "Fail"], errorCode := "I003", gapId := 106, isFreeLocus := false }

/-- M012 — monotonic × concurrent: needs `atomic(T)` / lock_free (gap 108). -/
def collisionMonotonicConcurrent : CollisionRow :=
  { dims := ["monotonic", "concurrent"], errorCode := "M012", gapId := 108, isFreeLocus := false }

/-- P002 — ghost × runtime conditional: an erased value in a runtime scrutinee (gap 109). -/
def collisionGhostRuntime : CollisionRow :=
  { dims := ["ghost", "runtime"], errorCode := "P002", gapId := 109, isFreeLocus := false }

/-- I004 — classified × async × session: the 3-WAY collision (gap 112). -/
def collisionClassifiedAsyncSession : CollisionRow :=
  { dims := ["classified", "Async", "session"], errorCode := "I004", gapId := 112,
    isFreeLocus := false }

/-- N002 — decimal × overflow(wrap): wrap is meaningless for exact decimal (gap 113). -/
def collisionDecimalOverflowWrap : CollisionRow :=
  { dims := ["decimal", "overflow"], errorCode := "N002", gapId := 113, isFreeLocus := false }

/-- L003 — borrow × unscoped spawn: use `task_group` (gap 114). -/
def collisionBorrowUnscopedSpawn : CollisionRow :=
  { dims := ["borrow", "spawn"], errorCode := "L003", gapId := 114, isFreeLocus := false }

/-- **The §6.8 soundness-collision catalog** — the nine non-free loci of the 21-dimension amalgam. -/
def sixEightCatalog : List CollisionRow :=
  [ collisionClassifiedFail, collisionBorrowAsync, collisionCtAsync, collisionCtFailSecret,
    collisionMonotonicConcurrent, collisionGhostRuntime, collisionClassifiedAsyncSession,
    collisionDecimalOverflowWrap, collisionBorrowUnscopedSpawn ]

/-- Whether EVERY row of a catalog is a non-free locus. -/
def allCollisionsNonFree (catalog : List CollisionRow) : Bool :=
  catalog.all (fun row => not row.isFreeLocus)

/-! ## Non-vacuity -/

/-- The catalog has exactly the nine §6.8 collisions. -/
theorem sixEightCatalog_length : sixEightCatalog.length = 9 :=
  rfl

/-- **Every §6.8 collision is a NON-FREE locus** — the honest marker, as a checked datum: the amalgam
does not amalgamate freely at any of the nine. -/
theorem sixEightCatalog_allNonFree : allCollisionsNonFree sixEightCatalog = true :=
  rfl

/-- The sharpest collision `E044` (CT × Async) is contradictory — recorded as a non-free locus. -/
theorem collisionCtAsync_isContradictoryNonFree :
    collisionCtAsync.errorCode = "E044" ∧ collisionCtAsync.isFreeLocus = false :=
  ⟨rfl, rfl⟩

/-- The 3-WAY collision `I004` genuinely names three dimensions. -/
theorem collisionClassifiedAsyncSession_isThreeWay :
    collisionClassifiedAsyncSession.dims.length = 3 :=
  rfl

end FX1Poly.Polygraph.Omega.Graded
