import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcSamePartitionFresh
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapCore

/-! # MODE-COMMUTE r22 — the COMPOUND fresh-block transposition at SYMBOLIC cell widths

The r20 cell-ascent WALL-WIDTH observation: the Godement swap of a whole cell against a whole
cell must transpose two disjoint fresh id ranges whose widths are the cells' TOTAL fresh
allocations — SYMBOLIC aggregate widths `widthA`/`widthB`, not the per-generator `{1, 3}` the
cup/cap simulation packages hardcode.  The recon showed the arithmetic carrier is ALREADY
width-generic (`arcFreshBlockTransposition baseFresh widthFirst widthSecond` has arbitrary
`widthFirst`/`widthSecond`) and the component-preservation crux (`isSameComponent_renameLinks`)
is ALREADY shipped sigma-generically.  So this file is a LIFT-to-symbolic-widths + thin
re-export, not a from-scratch build.

## What this file ships (each piece zero-axiom, each general over `baseFresh widthA widthB`)

  ★ `blockRotate_eq_arcFreshBlockTransposition` — the two byte-identical carriers (the r17
    standalone `blockRotate` and the live `arcFreshBlockTransposition`) are DEFINITIONALLY the
    same function.  `rfl`.
  ★ `compoundFreshBlockTransposition` — the swap of the two adjacent symbolic-width fresh
    blocks `[baseFresh, baseFresh+widthA)` and `[baseFresh+widthA, baseFresh+widthA+widthB)`,
    DEFINITIONAL over the width-generic carrier (a SINGLE rotation, NOT a composite: a block
    transposition of two adjacent blocks IS the rotation of the window by one block's width).
  ★ The four UF-automorphism obligations, thin re-exports of the width-generic shipped lemmas:
    `_fixesZero` (`σ 0 = 0` under `0 < baseFresh`), `_fixesBelow` (fixes the pre-swap state and
    boundary), `_fixesAbove` (fixes the future-allocation tail), `_leftInverse` (the swapped-width
    transposition undoes it) and `_injective`.
  ★ The two renaming-commutation cruxes at the compound sigma: `unionFindRootOf_compoundTransposition`
    (the union-find root commutes) and `isSameComponent_compoundTransposition` (the same-component
    partition is preserved) — the component-preservation leg the next-rung `componentsCorr` consumes.
  ★ `renameLinks_compoundTransposition_ofBelow` — the CONSUMER-SHAPED bridge: the compound
    transposition FIXES a link list all of whose entries are below `baseFresh` (the whole pre-swap
    state).  This is the hook the r23 `disjointWhiskerSupport` list-equality induction plugs into,
    exactly as `capCapSwap_componentsCorr` used `renameLinks_ofFixedEntries` at width 1/1.
  ★ Two firing probes: `compoundFreshBlockTransposition_shapes_probe` (the (2,3)/(3,2)/(1,4)
    shapes over base 10, `rfl`, reproducing the recon rotation table — establishes the permutation
    genuinely moves each block and fixes the complement) and `isSameComponent_compoundTransposition_probe`
    (the crux fires UNIVERSALLY over every query pair on the concrete two-block link state
    `[(0,1),(1,2),(3,4)]` at the (2,3) shape, via the general theorem — not a `decide` sample).

## What is honest-DEFERRED (r23+)

The full seed simulation `atomPastCell` / `disjointWhiskerSupport` / `blockSwapCore` — the
whisker-support LIST equality `reduct.links = renameLinks σ redex.links` over a whole
unbounded `runArcCell`-generated cell (the generalization of `capCapSwap_componentsCorr`'s
fixed 4-join `renameTower` to an arbitrary cell) — is the genuine open work.  This file supplies
that consumer its `σ`, the four obligations, and the two renaming-commutation cruxes; it does NOT
construct the list equality.  The parent honesty pin `fxMode_hasArcGodementSamePartitionFreshProof`
stays `false` (the refuted literal `:472`/`:545` is NEVER proven — the live target is the
FOREST-gated `ArcGodementSamePartitionFreshForest` only).

Raw Lean 4 + Init; every proof is a thin re-export of a width-generic shipped lemma or a `rfl`
computation.  Per-declaration `#assert_no_axioms` + independent `#print axioms` in the audit twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Carrier reconciliation — the two byte-identical fresh-block carriers agree -/

/-- ★ **The two carriers are the same function.**  The r17 standalone `blockRotate`
(`FreeTwoCell.BlockRotation`) and the live `arcFreshBlockTransposition`
(`WalkingAdjunction.ArcFreshBlockTransposition`) have byte-identical definitions, so they are
definitionally equal as functions `Nat → Nat → Nat → Nat → Nat`.  `rfl`. -/
theorem blockRotate_eq_arcFreshBlockTransposition :
    blockRotate = arcFreshBlockTransposition := rfl

/-! ## The compound sigma at symbolic cell widths -/

/-- ★ **The compound fresh-block transposition at SYMBOLIC widths.**  Swaps the two adjacent
fresh blocks whose widths are the cells' aggregate fresh allocations `widthA`/`widthB`: the
first block `[baseFresh, baseFresh+widthA)` moves up by `widthB`, the second block
`[baseFresh+widthA, baseFresh+widthA+widthB)` moves down by `widthA`; identity below `baseFresh`
and at or above the two blocks.  DEFINITIONAL over the width-generic carrier — a single window
rotation, not a composite. -/
def compoundFreshBlockTransposition (baseFresh widthA widthB : Nat) : Nat → Nat :=
  arcFreshBlockTransposition baseFresh widthA widthB

/-! ## The four UF-automorphism obligations (thin re-exports of the width-generic lemmas) -/

/-- The compound transposition FIXES `0` whenever the fresh base is positive — the scaffold's
`sigmaFixesZero` premise, now at symbolic widths. -/
theorem compoundFreshBlockTransposition_fixesZero (baseFresh widthA widthB : Nat)
    (isPositive : 0 < baseFresh) :
    compoundFreshBlockTransposition baseFresh widthA widthB 0 = 0 :=
  arcFreshBlockTransposition_fixesZero baseFresh widthA widthB isPositive

/-- The compound transposition FIXES every identifier strictly below the fresh base — the whole
pre-swap state and the boundary range.  The scaffold's `fixesBoundary` premise at symbolic widths. -/
theorem compoundFreshBlockTransposition_fixesBelow (baseFresh widthA widthB identifier : Nat)
    (isBelow : identifier < baseFresh) :
    compoundFreshBlockTransposition baseFresh widthA widthB identifier = identifier :=
  arcFreshBlockTransposition_ofBelow baseFresh widthA widthB identifier isBelow

/-- The compound transposition FIXES every identifier at or above both blocks — the
future-allocation tail.  The scaffold's `fixesAbove` premise at symbolic widths (the alignment
`redexCore.nextFresh = baseFresh + widthA + widthB` is the r23 seam). -/
theorem compoundFreshBlockTransposition_fixesAbove (baseFresh widthA widthB identifier : Nat)
    (isAtOrAbove : baseFresh + widthA + widthB ≤ identifier) :
    compoundFreshBlockTransposition baseFresh widthA widthB identifier = identifier :=
  arcFreshBlockTransposition_ofAtOrAbove baseFresh widthA widthB identifier isAtOrAbove

/-- ★ **Left inverse at symbolic widths** — the compound transposition with the two block widths
SWAPPED undoes it (the involution/inverse identity).  Thin re-export of the width-generic left
inverse. -/
theorem compoundFreshBlockTransposition_leftInverse (baseFresh widthA widthB identifier : Nat) :
    compoundFreshBlockTransposition baseFresh widthB widthA
        (compoundFreshBlockTransposition baseFresh widthA widthB identifier)
      = identifier :=
  arcFreshBlockTransposition_leftInverse baseFresh widthA widthB identifier

/-- ★ **Injectivity at symbolic widths** — the scaffold's `inj` premise, read off the left
inverse.  Thin re-export of the width-generic injectivity. -/
theorem compoundFreshBlockTransposition_injective (baseFresh widthA widthB firstId secondId : Nat)
    (imagesEqual : compoundFreshBlockTransposition baseFresh widthA widthB firstId
      = compoundFreshBlockTransposition baseFresh widthA widthB secondId) :
    firstId = secondId :=
  arcFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual

/-! ## The renaming-commutation cruxes at the compound sigma -/

/-- ★ **The union-find root commutes with the compound transposition.**  Instance of the shipped
sigma-generic `unionFindRootOf_rename` at the compound sigma (injective by
`compoundFreshBlockTransposition_injective`).  The root-following crux the next-rung count
correspondences consume. -/
theorem unionFindRootOf_compoundTransposition (baseFresh widthA widthB : Nat)
    (links : List (Nat × Nat)) (node : Nat) :
    unionFindRootOf (renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB) links)
        (compoundFreshBlockTransposition baseFresh widthA widthB node)
      = compoundFreshBlockTransposition baseFresh widthA widthB (unionFindRootOf links node) :=
  unionFindRootOf_rename (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    links node

/-- ★ **THE COMPONENT-PRESERVATION CRUX at the compound sigma.**  The same-component partition of
the renamed links at the renamed probes equals that of the original links at the original probes —
querying through the compound transposition sees the same partition.  Instance of the shipped
sigma-generic `isSameComponent_renameLinks` at the compound sigma.  This is the keystone
`componentsCorr` leg's engine, now at symbolic widths. -/
theorem isSameComponent_compoundTransposition (baseFresh widthA widthB : Nat)
    (links : List (Nat × Nat)) (queryLeft queryRight : Nat) :
    isSameComponent (renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB) links)
        (compoundFreshBlockTransposition baseFresh widthA widthB queryLeft)
        (compoundFreshBlockTransposition baseFresh widthA widthB queryRight)
      = isSameComponent links queryLeft queryRight :=
  isSameComponent_renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    links queryLeft queryRight

/-! ## The consumer-shaped bridge — the compound transposition fixes the pre-swap links -/

/-- ★ **CONSUMER BRIDGE (the statement the next rung needs).**  The compound transposition leaves
UNCHANGED any link list all of whose entries are below `baseFresh` (the whole pre-swap state — its
ids are all old, strictly below the fresh base).  This is the exact hook the r23
`disjointWhiskerSupport` list-equality plugs into, mirroring `capCapSwap_componentsCorr`'s use of
`renameLinks_ofFixedEntries` at width 1/1, now at symbolic widths.  Thin over the shipped
`renameLinks_ofFixedEntries` discharged by `_fixesBelow` on each entry. -/
theorem renameLinks_compoundTransposition_ofBelow (baseFresh widthA widthB : Nat)
    (links : List (Nat × Nat))
    (linkEntriesFresh : ∀ edge ∈ links, edge.1 < baseFresh ∧ edge.2 < baseFresh) :
    renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB) links = links :=
  renameLinks_ofFixedEntries (compoundFreshBlockTransposition baseFresh widthA widthB) links
    (fun edge edgeMember =>
      And.intro
        (compoundFreshBlockTransposition_fixesBelow baseFresh widthA widthB edge.1
          (linkEntriesFresh edge edgeMember).1)
        (compoundFreshBlockTransposition_fixesBelow baseFresh widthA widthB edge.2
          (linkEntriesFresh edge edgeMember).2))

/-! ## Firing probes -/

/-- ★ **Rotation-shape fire (the recon table, `rfl`).**  Over base `10`, the compound
transposition on the (2,3), (3,2) and (1,4) shapes moves each block's boundary as the recon
`#eval` table records — establishing the permutation genuinely MOVES the window (a refl-checked
non-triviality witness, not the identity).  (2,3): block A `[10,12)` up to `[13,15)`, block B
`[12,15)` down to `[10,13)` — so `10 ↦ 13`, `12 ↦ 10`.  (3,2): `10 ↦ 12`, `13 ↦ 10`.  (1,4):
`10 ↦ 14`, `11 ↦ 10`. -/
theorem compoundFreshBlockTransposition_shapes_probe :
    compoundFreshBlockTransposition 10 2 3 10 = 13
    ∧ compoundFreshBlockTransposition 10 2 3 12 = 10
    ∧ compoundFreshBlockTransposition 10 3 2 10 = 12
    ∧ compoundFreshBlockTransposition 10 3 2 13 = 10
    ∧ compoundFreshBlockTransposition 10 1 4 10 = 14
    ∧ compoundFreshBlockTransposition 10 1 4 11 = 10 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The crux fires UNIVERSALLY on a concrete two-block state.**  At the (2,3) shape over base
`10`, the compound transposition is a partition automorphism of the below-base probe link list
`[(0,1),(1,2),(3,4)]` — for EVERY query pair (a universal instantiation of the general crux, NOT
a `decide` sample over finitely many pairs).  Since the links are all below base, the renaming
fixes them, and the theorem states the same-component relation transports along the sigma
untouched. -/
theorem isSameComponent_compoundTransposition_probe (queryLeft queryRight : Nat) :
    isSameComponent (renameLinks (compoundFreshBlockTransposition 10 2 3) [(0, 1), (1, 2), (3, 4)])
        (compoundFreshBlockTransposition 10 2 3 queryLeft)
        (compoundFreshBlockTransposition 10 2 3 queryRight)
      = isSameComponent [(0, 1), (1, 2), (3, 4)] queryLeft queryRight :=
  isSameComponent_compoundTransposition 10 2 3 [(0, 1), (1, 2), (3, 4)] queryLeft queryRight

/-! ## Honesty markers -/

/-- **Honesty marker — the compound fresh-block transposition is SHIPPED at symbolic widths.**
`compoundFreshBlockTransposition` (definitional over the width-generic carrier, reconciled with
the r17 `blockRotate` via `blockRotate_eq_arcFreshBlockTransposition`) with its full
UF-automorphism interface: the four fixing/inverse/injectivity obligations, the two
renaming-commutation cruxes (`unionFindRootOf_compoundTransposition`,
`isSameComponent_compoundTransposition`), and the consumer-shaped below-base fixing bridge
(`renameLinks_compoundTransposition_ofBelow`).  All zero-axiom (thin re-exports of shipped
width-generic lemmas + `rfl`).  `= true`. -/
def fxMode_hasCompoundFreshBlockTransposition : Bool := true

/-- **Honesty pin — the r23 cell-swap keystone stays OPEN.**  This file supplies the compound
sigma, its four obligations and the two renaming cruxes, but NOT the whisker-support list equality
`reduct.links = renameLinks σ redex.links` over a whole cell (the r23 `disjointWhiskerSupport` /
`blockSwapCore`).  The refuted-literal honesty pin `fxMode_hasArcGodementSamePartitionFreshProof`
(the `:545` guard of the MACHINE-REFUTED `ArcGodementSamePartitionFresh` `:472`) is therefore NEVER
flipped — the live target is the FOREST-gated `ArcGodementSamePartitionFreshForest` only.  `rfl`. -/
theorem arcCompoundBlockTransposition_blockSwapCore_stays_open :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
