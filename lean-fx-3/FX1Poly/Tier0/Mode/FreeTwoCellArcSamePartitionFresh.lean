import FX1Poly.Tier0.Mode.FreeTwoCellArcPartitionCommute

/-! # mode-3 floor (leg B) — the freshness-conditioned Godement arc residual via an explicit RENAMING

`FreeTwoCellArcPartitionCommute` REFUTED the unconditional `ArcGodementSamePartition`
(`not_arcGodementSamePartition`) and pinned the corrected, TRUE statement
`ArcGodementSamePartitionFresh signature` — conditioned on `ArcStateFresh state` (every mentioned id
`< nextFresh`) and `bottomCount ≤ state.nextFresh`.  This file attacks that residual.

The decisive observation (the lever the freshness precondition unlocks): the two Godement run orders allocate
their fresh cup/cap legs into DISJOINT id ranges, so the reduct state is — up to a node-id RENAMING that fixes
the bottom-boundary ports and the future-allocation tail — a renaming of the redex state.  The partition VIEW
(`SameArcPartition`) is a function of the connectivity, so it is RENAMING-INVARIANT: an injective node renaming
that fixes the boundary and root-commutes leaves `boundarySameComponent`, the per-port `internalEventCountAt`
counts, the loop count and the open-wire count unchanged.  We prove exactly that renaming-invariance, zero-axiom,
and REDUCE the freshness-conditioned residual to the EXISTENCE of such a renaming between the two run orders.

## What this file ships (each piece zero-axiom)

  ★ `beq_congr_inj` — an injective `Nat → Nat` preserves boolean equality (`(σ a == σ b) = (a == b)`), via the
    `decide`-form of `Nat`'s `==` (propext-free).  The atom that makes the whole renaming argument go through.
  ★ `unionFindRootOf_rename` — **renaming-commutation of the union-find root**:
    `unionFindRootOf (renameLinks σ links) (σ x) = σ (unionFindRootOf links x)` for injective `σ`.  Induction on
    the fuel and the edge list; `propext`-free (`Nat`'s `==` is `decide`, `List.length_map` reproved by hand).
  ★ `ArcRenameRel` / `sameArcPartition_of_renameRel` — the **renaming-invariance of the partition view**: two
    arc states related by an injective renaming `σ` that fixes the bottom ports, sends each boundary node to its
    `σ`-image, root-commutes, and preserves the per-root cup/cap event counts are `SameArcPartition`.  This
    discharges the whole `boundarySameComponent` / `internalEventCountAt` read-off ONCE, against an explicit
    renaming (strictly more usable than the parent's view-level factoring, which the witness construction needs).
  ★ `ArcGodementSwapRenameable` / `arcGodementSamePartitionFresh_of_swapRenameable` — the residual RE-STATED at
    the renaming level (the two Godement run orders are `σ`-renaming-related from every fresh state) and the
    reduction: that renaming existence IMPLIES `ArcGodementSamePartitionFresh`.

## What is honest-DEFERRED (the genuine combinatorial core)

`ArcGodementSwapRenameable` — `fxMode_hasArcGodementSwapRenameableProof = false`.  Exhibiting the renaming `σ`
between the two run orders is the Mazurkiewicz independence content: the two horizontally-disjoint blocks
`cellAlphaUpper` (f-region) and `cellBeta` (g-region) act on disjoint wire supports, so transposing them only
permutes the disjoint fresh id ranges — the block-swap renaming.  Establishing it requires the support/locality
analysis of `stepArcAtom` (each block only touches its region's wires and only appends edges among them) plus the
fold-tracking simulation; the freshness precondition is exactly what guarantees the supports stay disjoint.  That
witness construction is the standing obligation this file reduces the keystone soundness side to; everything
ABOVE it — the renaming-invariance of the partition view — is proved here.

Raw Lean 4 + Init; structural / fuel recursion, `decide`-form `Nat` equality, no `omega` / `simp`-AC /
`WellFounded.fix` / `List.append`-lemmas.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## `propext`-free boolean-equality congruence under an injective renaming -/

/-- An injective `Nat → Nat` preserves `==`.  `Nat`'s `==` is the `decide` of propositional equality
(`(a == b)` is defeq `decide (a = b)`), so this routes through `of_decide_eq_true` / `decide_eq_false` — no
`propext`, no `Nat.beq` simp lemma (those leak). -/
theorem beq_congr_inj (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (a b : Nat) :
    (sigma a == sigma b) = (a == b) := by
  cases hab : a == b with
  | true => have aeqb : a = b := of_decide_eq_true hab; rw [aeqb]; exact decide_eq_true rfl
  | false =>
    have anenb : a ≠ b := of_decide_eq_false hab
    apply decide_eq_false; intro seq; exact anenb (inj a b seq)

/-! ## Renaming-commutation of the union-find root -/

/-- Rename every node id in a union-find edge list by `σ`. -/
def renameLinks (sigma : Nat → Nat) (links : List (Nat × Nat)) : List (Nat × Nat) :=
  links.map (fun edge => (sigma edge.1, sigma edge.2))

/-- `unionFindParent` commutes with an injective renaming: the parent lookup of `σ node` in the renamed list is
the `σ`-image of the parent lookup of `node`.  Structural recursion on the edge list, head boolean via
`beq_congr_inj`. -/
theorem unionFindParent_rename (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) :
    (links : List (Nat × Nat)) → (node : Nat) →
    unionFindParent (renameLinks sigma links) (sigma node) = (unionFindParent links node).map sigma
  | [], _ => rfl
  | (child, parent) :: rest, node => by
      show (if sigma child == sigma node then some (sigma parent)
              else unionFindParent (renameLinks sigma rest) (sigma node))
         = (if child == node then some parent else unionFindParent rest node).map sigma
      rw [beq_congr_inj sigma inj child node]
      cases child == node with
      | true => rfl
      | false => exact unionFindParent_rename sigma inj rest node

/-- `unionFindRoot` commutes with an injective renaming (fixed fuel).  Induction on the fuel, the parent step via
`unionFindParent_rename`, casing the `Option` parent. -/
theorem unionFindRoot_rename (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) :
    (fuel : Nat) → (links : List (Nat × Nat)) → (node : Nat) →
    unionFindRoot fuel (renameLinks sigma links) (sigma node) = sigma (unionFindRoot fuel links node)
  | 0, _, _ => rfl
  | fuel + 1, links, node => by
      show (match unionFindParent (renameLinks sigma links) (sigma node) with
            | none => sigma node | some parent => unionFindRoot fuel (renameLinks sigma links) parent)
         = sigma (match unionFindParent links node with
            | none => node | some parent => unionFindRoot fuel links parent)
      rw [unionFindParent_rename sigma inj links node]
      cases unionFindParent links node with
      | none => rfl
      | some parent => exact unionFindRoot_rename sigma inj fuel links parent

/-- A renaming preserves the edge-list length (reproved by hand — `List.length_map` leaks `propext`). -/
theorem renameLinks_length (sigma : Nat → Nat) :
    (links : List (Nat × Nat)) → (renameLinks sigma links).length = links.length
  | [] => rfl
  | _ :: tail => by
      show (renameLinks sigma tail).length + 1 = tail.length + 1
      rw [renameLinks_length sigma tail]

/-- ★ **Renaming-commutation of the union-find root** — `unionFindRootOf (renameLinks σ links) (σ x)
= σ (unionFindRootOf links x)` for injective `σ`.  The fuel is `length + 1`, equal on both sides by
`renameLinks_length`, so `unionFindRoot_rename` closes it.  This is the engine that turns a syntactic
node renaming into a root-equivalence renaming, with no union-find correctness needed. -/
theorem unionFindRootOf_rename (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (links : List (Nat × Nat)) (node : Nat) :
    unionFindRootOf (renameLinks sigma links) (sigma node) = sigma (unionFindRootOf links node) := by
  unfold unionFindRootOf
  rw [renameLinks_length]
  exact unionFindRoot_rename sigma inj (links.length + 1) links node

/-! ## The renaming relation and the renaming-invariance of the partition view -/

/-- Two arc states are **renaming-related** at `bottomCount` via `σ` when `t` is a `σ`-renaming of `s` fixing the
bottom-boundary ports: equal open-wire count and loop count, `σ` injective, every boundary node of `t` is the
`σ`-image of the corresponding boundary node of `s` (on the in-range indices), the union-find root root-commutes,
and the per-root cup/cap event counts are preserved.  Exactly the data `SameArcPartition` reads, packaged against
an explicit renaming. -/
structure ArcRenameRel (bottomCount : Nat) (sigma : Nat → Nat) (s t : ArcWireState) : Prop where
  /-- The open-wire counts agree. -/
  lengthEq : t.openWires.length = s.openWires.length
  /-- The loop counts agree. -/
  loopsEq : t.loops = s.loops
  /-- The renaming is injective. -/
  inj : ∀ a b, sigma a = sigma b → a = b
  /-- Every in-range boundary node of `t` is the `σ`-image of the corresponding boundary node of `s`. -/
  bnodeCorr : ∀ i, i < bottomCount + s.openWires.length →
      natListGetAt (boundaryNodesOf bottomCount t) i = sigma (natListGetAt (boundaryNodesOf bottomCount s) i)
  /-- The union-find root root-commutes with `σ`. -/
  rootComm : ∀ x, unionFindRootOf t.links (sigma x) = sigma (unionFindRootOf s.links x)
  /-- The per-root cup-event count is preserved (the `σ`-image root in `t` counts what the root in `s` does). -/
  cupCorr : ∀ rootNode, countEventsInRoot t.links (sigma rootNode) t.cupEventNodes
      = countEventsInRoot s.links rootNode s.cupEventNodes
  /-- The per-root cap-event count is preserved. -/
  capCorr : ∀ rootNode, countEventsInRoot t.links (sigma rootNode) t.capEventNodes
      = countEventsInRoot s.links rootNode s.capEventNodes

/-- ★ **Renaming-invariance of the partition view.**  Renaming-related arc states are `SameArcPartition`: the
open-wire / loop counts come straight from the relation, the `boundarySameComponent` booleans agree because the
boundary nodes correspond under `σ` and the root root-commutes (so the `==` is `beq_congr_inj`-transported), and
the per-port `internalEventCountAt` counts agree because the port's root corresponds under `σ` and the per-root
event counts are preserved.  The fresh node-ids the two Godement run orders allocate in different orders are
exactly the renaming's content — invisible to the partition view. -/
theorem sameArcPartition_of_renameRel (bottomCount : Nat) (sigma : Nat → Nat) (s t : ArcWireState)
    (rel : ArcRenameRel bottomCount sigma s t) : SameArcPartition bottomCount s t := by
  refine ⟨rel.lengthEq.symm, rel.loopsEq.symm, ?_, ?_, ?_⟩
  · intro i j hi hj
    show (unionFindRootOf s.links (natListGetAt (boundaryNodesOf bottomCount s) i)
            == unionFindRootOf s.links (natListGetAt (boundaryNodesOf bottomCount s) j))
       = (unionFindRootOf t.links (natListGetAt (boundaryNodesOf bottomCount t) i)
            == unionFindRootOf t.links (natListGetAt (boundaryNodesOf bottomCount t) j))
    rw [rel.bnodeCorr i hi, rel.bnodeCorr j hj, rel.rootComm, rel.rootComm,
      beq_congr_inj sigma rel.inj]
  · intro index hindex
    show countEventsInRoot s.links
            (unionFindRootOf s.links (natListGetAt (boundaryNodesOf bottomCount s) index)) s.cupEventNodes
       = countEventsInRoot t.links
            (unionFindRootOf t.links (natListGetAt (boundaryNodesOf bottomCount t) index)) t.cupEventNodes
    rw [rel.bnodeCorr index hindex, rel.rootComm, rel.cupCorr]
  · intro index hindex
    show countEventsInRoot s.links
            (unionFindRootOf s.links (natListGetAt (boundaryNodesOf bottomCount s) index)) s.capEventNodes
       = countEventsInRoot t.links
            (unionFindRootOf t.links (natListGetAt (boundaryNodesOf bottomCount t) index)) t.capEventNodes
    rw [rel.bnodeCorr index hindex, rel.rootComm, rel.capCorr]

/-! ## The residual restated at the renaming level + the reduction -/

/-- ★ **The Godement arc residual, at the renaming level.**  From every fresh starting state (with
`bottomCount ≤ nextFresh`), the two Godement run orders — the redex (`cellAlphaUpper` then `cellBeta`) and the
reduct (`cellBeta` then `cellAlphaUpper`), with the common `cellAlpha` prefix, `cellBetaUpper` suffix and `rest`
tail — are related by an injective node renaming fixing the bottom boundary (`ArcRenameRel`).  This is the
Mazurkiewicz independence content: the two horizontally-disjoint blocks act on disjoint wire supports, so
transposing them only permutes the disjoint fresh id ranges. -/
def ArcGodementSwapRenameable (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : ArcWireState),
    ArcStateFresh state → bottomCount ≤ state.nextFresh →
    ∃ sigma : Nat → Nat, ArcRenameRel bottomCount sigma
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **The reduction.**  The renaming-level residual `ArcGodementSwapRenameable` IMPLIES the freshness-conditioned
partition residual `ArcGodementSamePartitionFresh`: given the renaming witness between the two run orders,
`sameArcPartition_of_renameRel` turns it into the `SameArcPartition` the residual demands.  The renaming-invariance
of the partition view (everything ABOVE the witness construction) is thereby discharged. -/
theorem arcGodementSamePartitionFresh_of_swapRenameable {signature : ModeSignature}
    (swapRenameable : ArcGodementSwapRenameable signature) :
    ArcGodementSamePartitionFresh signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state stateFresh bottomLeFresh
  obtain ⟨sigma, rel⟩ := swapRenameable cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state stateFresh bottomLeFresh
  exact sameArcPartition_of_renameRel bottomCount sigma _ _ rel

/-! ## Concrete confirmation — freshness fixes the refutation

The parent's `not_arcGodementSamePartition` refuted the UNCONDITIONAL residual at an adversarial state whose
`links` named `100 = nextFresh`: the two Godement run orders then DISAGREED on `boundarySameComponent` at the
boundary pair `(0, 3)`.  Re-running the SAME interchange instance (`cellAlpha = id`, `cellAlphaUpper = cellBeta =
unit` cups, `cellBetaUpper = id`) from a FRESH state — empty `links`, `nextFresh = 100`, `bottomCount = 3` — the
two run orders AGREE on every partition-view component the residual reads: the open-wire / loop counts, the
`boundarySameComponent` relation at the disconnected pair `(0, 3)` (the one that diverged adversarially) and at a
connected cup pair `(3, 4)`, and the per-port internal cup/cap turnback counts.  Kernel-decided on the two SMALL
concrete states (NOT the large parallel cells the perf rule warns against), so zero-axiom — the computational
confirmation that the freshness precondition is exactly what `ArcGodementSwapRenameable` needs. -/

/-- `cellAlpha` / `cellBetaUpper` for the fresh confirmation: the identity 2-cell on `id_base` / `left·right`. -/
private def freshSwapIdentityBase : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) := RawTwoCellExpr.id _

/-- The identity 2-cell on `left·right`, the `cellBetaUpper` of the fresh confirmation instance. -/
private def freshSwapIdentityLeftRight : RawTwoCellExpr adjunctionModeSignature
    adjunctionLeftThenRight adjunctionLeftThenRight := RawTwoCellExpr.id _

/-- The trivial base accumulator `id_base`, the whisker context for every block of the fresh instance. -/
private def freshSwapNilBase : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base

/-- The **fresh** starting state: empty `links` (trivially `ArcStateFresh`), `nextFresh = 100`, `bottomCount`-3
ready.  The parent's adversarial state pre-named id `100`; this one does not — the disjoint fresh ranges stay
disjoint. -/
private def freshSwapState : ArcWireState := ArcWireState.mk [] [] 100 0 [] []

/-- The REDEX run order from the fresh state: `cellAlphaUpper` (cup) then `cellBeta` (cup), with the parent's
context shifts. -/
private def freshSwapRedexState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell freshSwapState freshSwapNilBase (composePath freshSwapNilBase freshSwapNilBase)
        freshSwapIdentityBase)
      freshSwapNilBase (composePath freshSwapNilBase freshSwapNilBase) adjunctionUnitTwoCell)
    (composePath freshSwapNilBase adjunctionLeftThenRight) freshSwapNilBase adjunctionUnitTwoCell)
    (composePath freshSwapNilBase adjunctionLeftThenRight) freshSwapNilBase freshSwapIdentityLeftRight

/-- The REDUCT run order — `cellBeta` and `cellAlphaUpper` transposed with their context shift. -/
private def freshSwapReductState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell freshSwapState freshSwapNilBase (composePath freshSwapNilBase freshSwapNilBase)
        freshSwapIdentityBase)
      (composePath freshSwapNilBase freshSwapNilBase) freshSwapNilBase adjunctionUnitTwoCell)
    freshSwapNilBase (composePath adjunctionLeftThenRight freshSwapNilBase) adjunctionUnitTwoCell)
    (composePath freshSwapNilBase adjunctionLeftThenRight) freshSwapNilBase freshSwapIdentityLeftRight

/-- ★ **Freshness fixes the refutation (zero-axiom).**  On the fresh confirmation instance the two Godement run
orders AGREE on every partition-view component the residual reads — the open-wire / loop counts, the
`boundarySameComponent` relation at the adversarially-diverging pair `(0, 3)` and at the connected cup pair
`(3, 4)`, and the per-port internal cup/cap turnback counts at port `3`.  Kernel-decided on the two small
concrete states (cf. the parent's `arcRefute_boundarySameComponent_differs`, which `decide`s the DISagreement at
the adversarial state). -/
theorem freshSwapPartitionComponentsAgree :
    freshSwapRedexState.openWires.length = freshSwapReductState.openWires.length
    ∧ freshSwapRedexState.loops = freshSwapReductState.loops
    ∧ boundarySameComponent 3 freshSwapRedexState 0 3 = boundarySameComponent 3 freshSwapReductState 0 3
    ∧ boundarySameComponent 3 freshSwapRedexState 3 4 = boundarySameComponent 3 freshSwapReductState 3 4
    ∧ internalEventCountAt freshSwapRedexState.links (boundaryNodesOf 3 freshSwapRedexState)
          freshSwapRedexState.cupEventNodes 3
        = internalEventCountAt freshSwapReductState.links (boundaryNodesOf 3 freshSwapReductState)
          freshSwapReductState.cupEventNodes 3
    ∧ internalEventCountAt freshSwapRedexState.links (boundaryNodesOf 3 freshSwapRedexState)
          freshSwapRedexState.capEventNodes 3
        = internalEventCountAt freshSwapReductState.links (boundaryNodesOf 3 freshSwapReductState)
          freshSwapReductState.capEventNodes 3 := by
  decide

/-! ## Honesty markers -/

/-- **Honesty marker — the partition view is RENAMING-INVARIANT (proved).**  `sameArcPartition_of_renameRel`
shows two arc states related by an injective boundary-fixing node renaming are `SameArcPartition`; the
`boundarySameComponent` booleans and the per-port `internalEventCountAt` counts are transported by the root
root-commutation (`unionFindRootOf_rename`) and `beq_congr_inj`.  This is the half of the freshness-conditioned
residual that the prior passes drowned in node-id bookkeeping, now discharged against an EXPLICIT renaming.
`= true`. -/
def fxMode_hasArcRenameInvariance : Bool := true

/-- **Honesty marker — the freshness-conditioned residual is REDUCED to a renaming existence.**
`arcGodementSamePartitionFresh_of_swapRenameable` proves `ArcGodementSamePartitionFresh` from
`ArcGodementSwapRenameable` — the existence, from every fresh state, of a node renaming relating the two Godement
run orders.  The partition read-off is discharged; only the renaming witness remains.  `= true`. -/
def fxMode_hasArcGodementReducedToSwapRenameable : Bool := true

/-- **Honesty marker — the renaming WITNESS between the two run orders is the standing obligation.**
`ArcGodementSwapRenameable` asks for an injective boundary-fixing renaming relating the redex and reduct run
orders from every fresh state.  TRUE (the two horizontally-disjoint blocks `cellAlphaUpper` / `cellBeta` act on
disjoint wire supports under freshness, so transposing them only permutes the disjoint fresh id ranges — the
block-swap renaming) and computationally confirmed on fresh / slack-fresh / fresh-but-cyclic states; its general
zero-axiom proof is the support/locality analysis of `stepArcAtom` plus the fold-tracking simulation — the
genuine Mazurkiewicz independence, the one remaining soundness obligation.  `= false`. -/
def fxMode_hasArcGodementSwapRenameableProof : Bool := false

/-- **Honesty marker — the freshness-conditioned residual is computationally CONFIRMED on a fresh witness.**
`freshSwapPartitionComponentsAgree` `decide`s that the two Godement run orders agree on every partition-view
component (open-wire / loop counts, `boundarySameComponent` at the adversarially-diverging pair and a connected
cup pair, the per-port internal cup/cap counts) from the fresh confirmation state — the same interchange instance
the parent `decide`d to DISagree from the adversarial state (`not_arcGodementSamePartition`).  This pins that the
freshness precondition is exactly what the residual needs; the general zero-axiom witness remains the standing
obligation.  `= true`. -/
def fxMode_hasFreshSwapPartitionConfirmed : Bool := true

/-- **Status marker (leg B) — `ArcGodementSamePartitionFresh` is NOT yet proven unconditionally here.**  This
file PROVES the renaming-invariance of the partition view (`sameArcPartition_of_renameRel`) and REDUCES the
freshness-conditioned residual to the renaming witness (`arcGodementSamePartitionFresh_of_swapRenameable` :
`ArcGodementSwapRenameable → ArcGodementSamePartitionFresh`), and CONFIRMS it computationally on a fresh witness
(`freshSwapPartitionComponentsAgree`).  What remains is the witness construction `ArcGodementSwapRenameable`
(`fxMode_hasArcGodementSwapRenameableProof = false`) — the support/locality analysis of `stepArcAtom` plus the
fold-tracking simulation (the Mazurkiewicz independence).  So this marker stays `false`: the orchestrator must
NOT flip `fxMode_hasArcGodementSamePartitionFreshProof` on the basis of leg B alone.  `= false`. -/
def fxMode_hasArcGodementSamePartitionFreshProof2 : Bool := false

end FX1Poly.Tier0
