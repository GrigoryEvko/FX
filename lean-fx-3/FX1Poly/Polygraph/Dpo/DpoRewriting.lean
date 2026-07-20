import FX1Poly.Polygraph.Net.OpenPetriCospan

/-! # Double-pushout hypergraph rewriting — the single-step rewrite decision

A **hypergraph** is a node count `0 .. nodeCount-1` together with a list of
labelled hyperedges (a `Nat` label plus an ordered `List Nat` endpoint tuple).  A
**double-pushout (DPO) rule** is a span `L ← K → R` of hypergraphs (a left pattern,
an interface, a right replacement) with two node maps `kToL`, `kToR` recording where
each interface node lands in `L` and in `R`.  A **match** is a node map `L → host`.

The single-step DPO rewrite of `host` along the rule at the match is computed in two
categorical pushout steps, realised concretely:

* **pushout complement** (the context `D`) — delete from `host` the match-images of
  the `L \ K` edges (`dpoDeleteContext`).  It exists exactly when the *dangling*
  condition holds (deleting nodes leaves no surviving edge with a deleted endpoint)
  and the match is *mono* / injective (`pushoutComplementExists`).
* **pushout** (glue `R` onto `D` along `K`) — offset `R`'s ids strictly above the
  host, fold the shipped fuel-bounded **union-find** `unionFindJoin` down the zipped
  interface images `match ∘ kToL` / `offset ∘ kToR` to identify the interface, then
  rewrite every id to its `unionFindRootOf` glued root and append `R`'s relabelled
  edges (`dpoGluePushout`).

Reuse (no re-derivation): the union-find pushout engine `unionFindJoin` /
`unionFindRootOf` (`WalkingAdjunction.MatchingDecision`) and the sorted-`List Nat`
multiset kit + the `ocp` id-list / relabel utilities from `OpenPetriCospan` (which
themselves reuse `CommWordProblem`'s `cswSort` / `cswListNatBeq` / `cswListNatBeqEq`).

What lands: the carrier + ops (T1), pushout-complement + pushout via union-find (T2),
the single-step decision `decideRewritesTo` with the `DpoRewriteStep` relation, its
soundness `dpoRewriteStepSound` and the `none`-refutation half, plus concrete
structural soundness (deleted `L\K` edges absent, `R` edges present, interface
identified) (T3).

Walls (concrete `false` markers with obstructions below): multi-step reachability
`H1 ~>* H2` is undecidable (DPO hypergraph rewriting is Turing-complete)
(`dpgHasGeneralReachability`); critical-pair / local-confluence completeness needs an
undecidable termination hypothesis (`dpgHasConfluence`); pushout-complement
uniqueness fails for non-mono matches (`dpgHasPushoutComplementUniqueness`).

Zero-axiom: no `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`, `decide`; no wildcard match
arms over a split scrutinee in shipped code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Dpo

open FX1Poly.Polygraph (unionFindJoin unionFindRootOf isSameComponent)
open FX1Poly.Polygraph.Net
  (ocpBoth ocpBothElim ocpMapId ocpMemBool ocpDedup ocpIndexOf ocpListLe)
open FX1Poly.ComputerAlgebra (cswLe cswSort cswListNatBeq cswListNatBeqEq cswNatBeqEq cswNatBeqRefl cswListNatBeqRefl)

/-! ## The carrier — labelled hyperedges and hypergraphs -/

/-- A labelled hyperedge: a `Nat` label and an ordered `List Nat` endpoint tuple. -/
structure Hyperedge where
  label : Nat
  endpoints : List Nat

/-- A hypergraph: node ids `0 .. nodeCount-1` plus a list of labelled hyperedges. -/
structure Hypergraph where
  nodeCount : Nat
  edges : List Hyperedge

/-- A DPO rule — a span `L ← K → R` with the two interface node maps
(`kToL i` is where interface node `i` lands in `L`, `kToR i` in `R`). -/
structure DpoRule where
  left : Hypergraph
  interface : Hypergraph
  right : Hypergraph
  kToL : List Nat
  kToR : List Nat

/-- A match: an injective node map from `L`'s nodes into the host graph. -/
structure Match where
  nodeMap : List Nat

/-! ## Cons-only list primitives (no `List.append`, no `List.getD`) -/

/-- Cons-only append of `Nat` id lists. -/
def dpgAppendNat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: dpgAppendNat xs ys

/-- Cons-only append of hyperedge lists. -/
def dpgAppendEdge : List Hyperedge → List Hyperedge → List Hyperedge
  | [], ys => ys
  | x :: xs, ys => x :: dpgAppendEdge xs ys

/-- Indexed lookup into a `Nat` list (default `0` past the end); structural, no `getD`. -/
def dpgNth : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: rest, Nat.succ index => dpgNth rest index

/-- The ascending list `[start, start+1, …]` of the given length (cons-only). -/
def dpgRangeFrom : Nat → Nat → List Nat
  | 0, _ => []
  | Nat.succ count, start => start :: dpgRangeFrom count (Nat.succ start)

/-- The node-index list `[0, 1, …, count-1]`. -/
def dpgRange (count : Nat) : List Nat := dpgRangeFrom count 0

/-- Strict `<` on `Nat` via `cswLe` (no order lemma leak). -/
def dpgLt (smaller larger : Nat) : Bool := cswLe (Nat.succ smaller) larger

/-- No two entries of a `Nat` list are equal (injectivity check). -/
def dpgInjective : List Nat → Bool
  | [] => true
  | head :: rest => cond (ocpMemBool head rest) false (dpgInjective rest)

/-! ## Edge relabelling, equality, order, and canonical sort -/

/-- Relabel one hyperedge's endpoints by `renamer`, keeping its label. -/
def dpgEdgeRelabel (renamer : Nat → Nat) (edge : Hyperedge) : Hyperedge :=
  { label := edge.label, endpoints := ocpMapId renamer edge.endpoints }

/-- Relabel every hyperedge in a list. -/
def dpgEdgesRelabel (renamer : Nat → Nat) : List Hyperedge → List Hyperedge
  | [] => []
  | head :: rest => dpgEdgeRelabel renamer head :: dpgEdgesRelabel renamer rest

/-- Structural equality of hyperedges: label equal and endpoint tuples equal. -/
def dpgEdgeBeq (leftEdge rightEdge : Hyperedge) : Bool :=
  ocpBoth (Nat.beq leftEdge.label rightEdge.label)
    (cswListNatBeq leftEdge.endpoints rightEdge.endpoints)

/-- Structural equality of hyperedge lists (cons-only). -/
def dpgEdgeListBeq : List Hyperedge → List Hyperedge → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      ocpBoth (dpgEdgeBeq leftHead rightHead) (dpgEdgeListBeq leftRest rightRest)

/-- `≤` on hyperedges: compare labels, breaking ties lexicographically on endpoints. -/
def dpgEdgeLe (leftEdge rightEdge : Hyperedge) : Bool :=
  cond (Nat.beq leftEdge.label rightEdge.label)
    (ocpListLe leftEdge.endpoints rightEdge.endpoints)
    (cswLe leftEdge.label rightEdge.label)

/-- Ordered insert of a hyperedge into a `dpgEdgeLe`-sorted list. -/
def dpgEdgeInsert (edge : Hyperedge) : List Hyperedge → List Hyperedge
  | [] => [edge]
  | head :: rest =>
      cond (dpgEdgeLe edge head) (edge :: head :: rest) (head :: dpgEdgeInsert edge rest)

/-- Insertion sort of a hyperedge list (a deterministic canonical order). -/
def dpgEdgeSort : List Hyperedge → List Hyperedge
  | [] => []
  | head :: rest => dpgEdgeInsert head (dpgEdgeSort rest)

/-- Hyperedge membership as a `Bool`. -/
def dpgEdgeMemBool (target : Hyperedge) : List Hyperedge → Bool
  | [] => false
  | head :: rest => cond (dpgEdgeBeq target head) true (dpgEdgeMemBool target rest)

/-- Drop from the second list every edge that is `dpgEdgeBeq`-equal to one in the first. -/
def dpgEdgeRemoveThose (toRemove : List Hyperedge) : List Hyperedge → List Hyperedge
  | [] => []
  | head :: rest =>
      cond (dpgEdgeMemBool head toRemove)
        (dpgEdgeRemoveThose toRemove rest)
        (head :: dpgEdgeRemoveThose toRemove rest)

/-! ## Canonical form + the graph decision -/

/-- Every endpoint id appearing across a hyperedge list, in edge order. -/
def dpgAllEndpoints : List Hyperedge → List Nat
  | [] => []
  | head :: rest => dpgAppendNat head.endpoints (dpgAllEndpoints rest)

/-- Canonicalise a hypergraph: relabel every node to its dense first-appearance index
(over the endpoint-appearance order), then sort the edges. -/
def dpgCanonicalize (graph : Hypergraph) : Hypergraph :=
  let order := ocpDedup (dpgAllEndpoints graph.edges)
  let dense := fun (nodeId : Nat) => ocpIndexOf order nodeId
  { nodeCount := order.length,
    edges := dpgEdgeSort (dpgEdgesRelabel dense graph.edges) }

/-- Structural equality of hypergraphs (node count then edge list). -/
def dpgHypergraphBeq (leftGraph rightGraph : Hypergraph) : Bool :=
  ocpBoth (Nat.beq leftGraph.nodeCount rightGraph.nodeCount)
    (dpgEdgeListBeq leftGraph.edges rightGraph.edges)

/-- Decide graph equality up to canonical form. -/
def canonicalHypergraphBeq (leftGraph rightGraph : Hypergraph) : Bool :=
  dpgHypergraphBeq (dpgCanonicalize leftGraph) (dpgCanonicalize rightGraph)

/-! ## Well-formedness predicates (T1) -/

/-- Every endpoint of a `List Nat` is a valid node id (`< nodeCount`). -/
def dpgEndpointsValid (nodeCount : Nat) : List Nat → Bool
  | [] => true
  | head :: rest => ocpBoth (dpgLt head nodeCount) (dpgEndpointsValid nodeCount rest)

/-- Every hyperedge references only valid node ids. -/
def dpgEdgesValid (nodeCount : Nat) : List Hyperedge → Bool
  | [] => true
  | head :: rest =>
      ocpBoth (dpgEndpointsValid nodeCount head.endpoints) (dpgEdgesValid nodeCount rest)

/-- A hypergraph is well-formed when every edge references valid nodes. -/
def dpgHypergraphWellFormed (graph : Hypergraph) : Bool :=
  dpgEdgesValid graph.nodeCount graph.edges

/-- A DPO rule is well-formed: both interface maps injective and all three graphs
well-formed. -/
def dpgRuleWellFormed (rule : DpoRule) : Bool :=
  ocpBoth (dpgInjective rule.kToL)
    (ocpBoth (dpgInjective rule.kToR)
      (ocpBoth (dpgHypergraphWellFormed rule.left)
        (ocpBoth (dpgHypergraphWellFormed rule.interface)
          (dpgHypergraphWellFormed rule.right))))

/-- A match is well-formed when its node map is injective (a mono match). -/
def dpgMatchWellFormed (mtch : Match) : Bool := dpgInjective mtch.nodeMap

/-! ## Pushout complement — the context `D` and its existence (T2) -/

/-- The `L`-edges that lie in the interface image (`kToL`-relabelled `K`-edges). -/
def dpgInterfaceImageEdges (rule : DpoRule) : List Hyperedge :=
  dpgEdgesRelabel (fun (kNode : Nat) => dpgNth rule.kToL kNode) rule.interface.edges

/-- The `L \ K` edges: `L`-edges that are NOT interface images. -/
def dpgDeletedLeftEdges (rule : DpoRule) : List Hyperedge :=
  dpgEdgeRemoveThose (dpgInterfaceImageEdges rule) rule.left.edges

/-- The host edges deleted by the rewrite (match-images of the `L \ K` edges). -/
def dpgDeletedHostEdges (rule : DpoRule) (mtch : Match) : List Hyperedge :=
  dpgEdgesRelabel (fun (lNode : Nat) => dpgNth mtch.nodeMap lNode) (dpgDeletedLeftEdges rule)

/-- The context `D`: the host with the deleted `L \ K` match-image edges removed. -/
def dpoDeleteContext (host : Hypergraph) (rule : DpoRule) (mtch : Match) : Hypergraph :=
  { nodeCount := host.nodeCount,
    edges := dpgEdgeRemoveThose (dpgDeletedHostEdges rule mtch) host.edges }

/-- Keep the ids not present in `mapValues` (cons-only sift). -/
def dpgSiftNotIn (mapValues : List Nat) : List Nat → List Nat
  | [] => []
  | head :: rest =>
      cond (ocpMemBool head mapValues) (dpgSiftNotIn mapValues rest) (head :: dpgSiftNotIn mapValues rest)

/-- The `L`-nodes not covered by the interface map `kToL` (the nodes the rule deletes). -/
def dpgDeletedLeftNodes (rule : DpoRule) : List Nat :=
  dpgSiftNotIn rule.kToL (dpgRange rule.left.nodeCount)

/-- The host nodes deleted by the rewrite (match-images of the deleted `L`-nodes). -/
def dpgDeletedHostNodes (rule : DpoRule) (mtch : Match) : List Nat :=
  ocpMapId (fun (lNode : Nat) => dpgNth mtch.nodeMap lNode) (dpgDeletedLeftNodes rule)

/-- No endpoint of a `List Nat` is among the deleted node ids. -/
def dpgAllNotMem : List Nat → List Nat → Bool
  | [], _ => true
  | head :: rest, deleted => cond (ocpMemBool head deleted) false (dpgAllNotMem rest deleted)

/-- Every surviving edge avoids every deleted node id (the dangling condition body). -/
def dpgEdgesAvoidNodes (deleted : List Nat) : List Hyperedge → Bool
  | [] => true
  | head :: rest =>
      ocpBoth (dpgAllNotMem head.endpoints deleted) (dpgEdgesAvoidNodes deleted rest)

/-- **Pushout-complement existence**: the dangling condition (no surviving edge in the
context references a deleted host node) together with the mono / injectivity condition
(the match is injective, so deletion is unambiguous). -/
def pushoutComplementExists (host : Hypergraph) (rule : DpoRule) (mtch : Match) : Bool :=
  ocpBoth
    (dpgEdgesAvoidNodes (dpgDeletedHostNodes rule mtch)
      (dpoDeleteContext host rule mtch).edges)
    (dpgInjective mtch.nodeMap)

/-! ## Pushout — glue `R` onto `D` along `K` via the shipped union-find (T2) -/

/-- Fold `unionFindJoin` down the interface, identifying each interface node's host
image (`match ∘ kToL`) with its offset right image (`offset + kToR`). -/
def dpgBuildGlue (offset : Nat) (rule : DpoRule) (mtch : Match) :
    List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], links => links
  | kNode :: rest, links =>
      dpgBuildGlue offset rule mtch rest
        (unionFindJoin links
          (dpgNth mtch.nodeMap (dpgNth rule.kToL kNode))
          (offset + dpgNth rule.kToR kNode))

/-- The glue links for a rewrite: fold over all interface nodes with the host node
count as the fresh offset. -/
def dpgGlueLinks (host : Hypergraph) (rule : DpoRule) (mtch : Match) : List (Nat × Nat) :=
  dpgBuildGlue host.nodeCount rule mtch (dpgRange rule.interface.nodeCount) []

/-- **Glue pushout**: append `R`'s offset-relabelled edges to the context `D`, then
rewrite every id to its `unionFindRootOf` glued root. -/
def dpoGluePushout (host : Hypergraph) (rule : DpoRule) (mtch : Match) : Hypergraph :=
  let offset := host.nodeCount
  let context := dpoDeleteContext host rule mtch
  let glueLinks := dpgGlueLinks host rule mtch
  let toRoot := fun (nodeId : Nat) => unionFindRootOf glueLinks nodeId
  let shiftedRightEdges := dpgEdgesRelabel (fun (rNode : Nat) => offset + rNode) rule.right.edges
  { nodeCount := offset + rule.right.nodeCount,
    edges := dpgEdgesRelabel toRoot (dpgAppendEdge context.edges shiftedRightEdges) }

/-! ## The single-step rewrite decision + relation (T3) -/

/-- Single-step DPO rewrite: `none` when the pushout complement does not exist,
otherwise the glued pushout graph. -/
def dpoRewriteAt (host : Hypergraph) (rule : DpoRule) (mtch : Match) : Option Hypergraph :=
  match pushoutComplementExists host rule mtch with
  | false => none
  | true => some (dpoGluePushout host rule mtch)

/-- Decide that `host` rewrites to `result` at the rule + match: the computed rewrite
must be canonically equal to `result` (and `none` decides `false`). -/
def decideRewritesTo (host result : Hypergraph) (rule : DpoRule) (mtch : Match) : Bool :=
  match dpoRewriteAt host rule mtch with
  | some producedGraph => canonicalHypergraphBeq producedGraph result
  | none => false

/-- The DPO single-step relation: `host` rewrites to `result` at `rule` + `mtch`
exactly when `dpoRewriteAt` produces `result`. -/
inductive DpoRewriteStep : Hypergraph → DpoRule → Match → Hypergraph → Prop where
  | ofRewrite {host : Hypergraph} {rule : DpoRule} {mtch : Match} {result : Hypergraph} :
      dpoRewriteAt host rule mtch = some result → DpoRewriteStep host rule mtch result

/-! ## Reflexivity lemmas for the canonical decision -/

/-- `dpgEdgeBeq` is reflexive. -/
theorem dpgEdgeBeqRefl : (edge : Hyperedge) → dpgEdgeBeq edge edge = true
  | ⟨edgeLabel, edgeEndpoints⟩ => by
      show ocpBoth (Nat.beq edgeLabel edgeLabel) (cswListNatBeq edgeEndpoints edgeEndpoints) = true
      rw [cswNatBeqRefl edgeLabel, cswListNatBeqRefl edgeEndpoints]
      rfl

/-- `dpgEdgeListBeq` is reflexive. -/
theorem dpgEdgeListBeqRefl : (edges : List Hyperedge) → dpgEdgeListBeq edges edges = true
  | [] => rfl
  | head :: rest => by
      show ocpBoth (dpgEdgeBeq head head) (dpgEdgeListBeq rest rest) = true
      rw [dpgEdgeBeqRefl head, dpgEdgeListBeqRefl rest]
      rfl

/-- `dpgHypergraphBeq` is reflexive. -/
theorem dpgHypergraphBeqRefl : (graph : Hypergraph) → dpgHypergraphBeq graph graph = true
  | ⟨graphNodeCount, graphEdges⟩ => by
      show ocpBoth (Nat.beq graphNodeCount graphNodeCount) (dpgEdgeListBeq graphEdges graphEdges) = true
      rw [cswNatBeqRefl graphNodeCount, dpgEdgeListBeqRefl graphEdges]
      rfl

/-- `canonicalHypergraphBeq` is reflexive: a graph is canonically equal to itself. -/
theorem canonicalHypergraphBeqRefl (graph : Hypergraph) :
    canonicalHypergraphBeq graph graph = true :=
  dpgHypergraphBeqRefl (dpgCanonicalize graph)

/-! ## Soundness of the edge / graph decisions -/

/-- `dpgEdgeBeq` sound: beq-true edges are equal. -/
theorem dpgEdgeBeqEq : (leftEdge rightEdge : Hyperedge) →
    dpgEdgeBeq leftEdge rightEdge = true → leftEdge = rightEdge
  | ⟨leftLabel, leftEndpoints⟩, ⟨rightLabel, rightEndpoints⟩, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [cswNatBeqEq leftLabel rightLabel hSplit.left,
        cswListNatBeqEq leftEndpoints rightEndpoints hSplit.right]

/-- `dpgEdgeListBeq` sound: beq-true edge lists are equal. -/
theorem dpgEdgeListBeqEq : (leftEdges rightEdges : List Hyperedge) →
    dpgEdgeListBeq leftEdges rightEdges = true → leftEdges = rightEdges
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [dpgEdgeBeqEq leftHead rightHead hSplit.left,
        dpgEdgeListBeqEq leftRest rightRest hSplit.right]

/-- `dpgHypergraphBeq` sound: beq-true hypergraphs are equal. -/
theorem dpgHypergraphBeqEq : (leftGraph rightGraph : Hypergraph) →
    dpgHypergraphBeq leftGraph rightGraph = true → leftGraph = rightGraph
  | ⟨leftNodeCount, leftEdges⟩, ⟨rightNodeCount, rightEdges⟩, hBeq => by
      have hSplit := ocpBothElim _ _ hBeq
      rw [cswNatBeqEq leftNodeCount rightNodeCount hSplit.left,
        dpgEdgeListBeqEq leftEdges rightEdges hSplit.right]

/-- **Canonical decision soundness**: `canonicalHypergraphBeq` returning `true` means
the two hypergraphs have equal canonical forms. -/
theorem canonicalHypergraphBeqSound (leftGraph rightGraph : Hypergraph) :
    canonicalHypergraphBeq leftGraph rightGraph = true →
    dpgCanonicalize leftGraph = dpgCanonicalize rightGraph := by
  intro hBeq
  exact dpgHypergraphBeqEq (dpgCanonicalize leftGraph) (dpgCanonicalize rightGraph) hBeq

/-! ## The rewrite-step soundness + refutation (T3) -/

/-- **Rewrite-step soundness**: a genuine DPO step decides `true`. -/
theorem dpoRewriteStepSound : (host : Hypergraph) → (rule : DpoRule) → (mtch : Match) →
    (result : Hypergraph) → DpoRewriteStep host rule mtch result →
    decideRewritesTo host result rule mtch = true
  | host, rule, mtch, result, DpoRewriteStep.ofRewrite hEq => by
      show (match dpoRewriteAt host rule mtch with
        | some producedGraph => canonicalHypergraphBeq producedGraph result
        | none => false) = true
      rw [hEq]
      exact canonicalHypergraphBeqRefl result

/-- **Refutation half**: when the pushout complement does not exist, no rewrite is
decided. -/
theorem dpoRewriteNoneRefutes (host : Hypergraph) (rule : DpoRule) (mtch : Match)
    (result : Hypergraph) (hNone : dpoRewriteAt host rule mtch = none) :
    decideRewritesTo host result rule mtch = false := by
  show (match dpoRewriteAt host rule mtch with
    | some producedGraph => canonicalHypergraphBeq producedGraph result
    | none => false) = false
  rw [hNone]

/-! ## Concrete example — a path graph with the middle edge relabelled -/

/-- Host: the path `0 →(0) 1 →(0) 2` (two label-`0` edges). -/
def dpgHostPath : Hypergraph :=
  { nodeCount := 3,
    edges := [{ label := 0, endpoints := [0, 1] }, { label := 0, endpoints := [1, 2] }] }

/-- Rule replacing a label-`0` edge between the two interface nodes by a label-`5`
edge: `L = ({0,1}, {0 →(0) 1})`, `K = ({0,1}, ∅)`, `R = ({0,1}, {0 →(5) 1})`, with
both interface maps the identity `[0, 1]`. -/
def dpgRelabelRule : DpoRule :=
  { left := { nodeCount := 2, edges := [{ label := 0, endpoints := [0, 1] }] },
    interface := { nodeCount := 2, edges := [] },
    right := { nodeCount := 2, edges := [{ label := 5, endpoints := [0, 1] }] },
    kToL := [0, 1],
    kToR := [0, 1] }

/-- The match embedding `L`'s two nodes onto host nodes `0`, `1`. -/
def dpgMatchAtZeroOne : Match := { nodeMap := [0, 1] }

/-- A node-deleting rule: `L = ({0,1}, {0 →(0) 1})`, interface `K = ({0}, ∅)`
covering only `L`-node `0`, so `L`-node `1` is deleted; `R = ({0}, ∅)`.  Applying it
removes the matched edge and deletes the second matched node. -/
def dpgDeleteNodeRule : DpoRule :=
  { left := { nodeCount := 2, edges := [{ label := 0, endpoints := [0, 1] }] },
    interface := { nodeCount := 1, edges := [] },
    right := { nodeCount := 1, edges := [] },
    kToL := [0],
    kToR := [0] }

/-- The computed rewrite result at the good match. -/
def dpgResultAtZeroOne : Hypergraph := dpoGluePushout dpgHostPath dpgRelabelRule dpgMatchAtZeroOne

/-! ## Fires (T5) — ground `rfl`/`Eq` evaluations the build must accept -/

/-- FIRE: the pushout complement exists at the good match. -/
theorem dpgFireComplementExistsGood :
    pushoutComplementExists dpgHostPath dpgRelabelRule dpgMatchAtZeroOne = true := rfl

/-- FIRE (T3, `L\K` removed): the context `D` at the good match has dropped the matched
`0 →(0) 1` edge, keeping only the surviving `1 →(0) 2` edge. -/
theorem dpgFireContextDropsMatchedEdge :
    (dpoDeleteContext dpgHostPath dpgRelabelRule dpgMatchAtZeroOne).edges
      = [{ label := 0, endpoints := [1, 2] }] := rfl

/-- FIRE (T3, interface identified): the glue links identify each interface node's host
image with its offset right image — interface node `0`'s two images share a root. -/
theorem dpgFireInterfaceNodeZeroGlued :
    isSameComponent (dpgGlueLinks dpgHostPath dpgRelabelRule dpgMatchAtZeroOne) 0 3 = true := rfl

/-- FIRE (T3, interface identified): interface node `1`'s two images share a root. -/
theorem dpgFireInterfaceNodeOneGlued :
    isSameComponent (dpgGlueLinks dpgHostPath dpgRelabelRule dpgMatchAtZeroOne) 1 4 = true := rfl

/-- FIRE (T5, produce expected graph): the good rewrite yields a graph canonically equal
to itself — the decision fires `true`. -/
theorem dpgFireRewriteDecidesTrue :
    decideRewritesTo dpgHostPath dpgResultAtZeroOne dpgRelabelRule dpgMatchAtZeroOne = true := rfl

/-- FIRE (T5, canonically-equal hand-written result): a graph with different raw node
ids `7, 8, 9` but the same structure (a label-`0` edge then a label-`5` edge sharing a
node) is canonically equal to the computed rewrite result — the decision fires `true`. -/
theorem dpgFireRewriteMatchesHandwritten :
    decideRewritesTo dpgHostPath
      { nodeCount := 3,
        edges := [{ label := 0, endpoints := [7, 8] }, { label := 5, endpoints := [9, 7] }] }
      dpgRelabelRule dpgMatchAtZeroOne = true := rfl

/-- FIRE (T5, control — wrong result decides false): the label-`5` edge does not become
label-`9`. -/
theorem dpgFireWrongResultDecidesFalse :
    decideRewritesTo dpgHostPath
      { nodeCount := 3,
        edges := [{ label := 0, endpoints := [7, 8] }, { label := 9, endpoints := [9, 7] }] }
      dpgRelabelRule dpgMatchAtZeroOne = false := rfl

/-- FIRE (T5, dangling fires): applying the node-deleting rule at the match deletes host
node `1`, but node `1` still carries the surviving `1 →(0) 2` edge — the pushout
complement does NOT exist and the rewrite is `none`. -/
theorem dpgFireDanglingComplementNone :
    dpoRewriteAt dpgHostPath dpgDeleteNodeRule dpgMatchAtZeroOne = none := rfl

/-- FIRE (T5, dangling condition is what fails): the complement-existence check is `false`
for the node-deleting rule at this match. -/
theorem dpgFireDanglingComplementFalse :
    pushoutComplementExists dpgHostPath dpgDeleteNodeRule dpgMatchAtZeroOne = false := rfl

/-- FIRE (T5, dangling refutes the decision): with no complement, every claimed result
decides `false`. -/
theorem dpgFireDanglingDecidesFalse :
    decideRewritesTo dpgHostPath dpgResultAtZeroOne dpgDeleteNodeRule dpgMatchAtZeroOne = false := rfl

/-- FIRE (T3 relation): the good rewrite is a genuine `DpoRewriteStep`. -/
theorem dpgFireRewriteStep :
    DpoRewriteStep dpgHostPath dpgRelabelRule dpgMatchAtZeroOne dpgResultAtZeroOne :=
  DpoRewriteStep.ofRewrite rfl

/-! ## Capability markers and the walls (T4) -/

/-- Landed: the carrier + pushout-complement + union-find pushout + the single-step
rewrite decision with soundness. -/
def dpgHasSingleStepDecision : Bool := true

/-- Landed: for a **mono** (injective) match the pushout complement's existence is
decided by the dangling + injectivity check (`pushoutComplementExists`). -/
def dpgHasMonoMatchComplementExists : Bool := true

/-- **WALL** — multi-step DPO reachability `H1 ~>* H2` (does some finite sequence of
rewrites carry `H1` to `H2`?) is **undecidable**.  DPO hypergraph rewriting is
Turing-complete: a semi-Thue / semigroup rewriting system embeds as unary hyperedge
rules, so reachability decides the word problem for finitely-presented semigroups,
which is undecidable (Post/Markov).  The in-repo honest citation is the shipped
semigroup word-problem substrate (`CommWordProblem` / the trace word problem) whose
non-commutative form is exactly the undecidable core.  Burned attacks: (1) a
bounded-depth `List.any` over rewrite sequences up to length `k` is a one-sided
under-approximation — it can confirm reachability but never certify
NON-reachability (no `k` bounds the search, the id space is unbounded); (2) a
normal-form / termination oracle that would bound the search is exactly a solution to
the (undecidable) uniform halting problem for the rewrite system, so it cannot be a
zero-axiom `Bool`.  The decidable core that stays `true` is the single-step decision
at a given match (`dpgHasSingleStepDecision`). -/
def dpgHasGeneralReachability : Bool := false

/-- **WALL** — critical-pair / local-confluence completeness (a Newman-style decision
that a hypergraph rewrite system is confluent).  Even *local* confluence → global
confluence requires a Noetherianity (termination) hypothesis, and termination of DPO
rewriting is undecidable (it subsumes the uniform halting problem, attack (2) above).
Beyond termination, confluence itself demands joinability of *all* critical pairs, of
which there can be unboundedly many (overlaps range over an unbounded node space), so
it is not a finite zero-axiom check.  Burned attacks: (1) enumerate critical pairs up
to a size bound and check joinability — misses larger overlaps, so a `true` verdict is
unsound (one-sided); (2) assume termination and invoke Newman's lemma — the
termination premise is itself the undecidable input, so it cannot be discharged by a
`Bool`.  -/
def dpgHasConfluence : Bool := false

/-- **WALL** — pushout-complement **uniqueness** for arbitrary (possibly non-mono)
matches.  The classical Ehrig result: the pushout complement of `K → L → G` is unique
(up to iso) **only when the match `L → G` is monic**.  For a non-injective match two
distinct host nodes can be the image of two `L`-nodes, and there is a genuine choice of
which host structure to keep in the context `D` — several non-isomorphic complements
satisfy the pushout square.  The abstract statement of what uniqueness *would* look like
is `FX1Poly.Axis.Context.IsPushout.uniqueUpToIso` (any two pushout objects of one span
are canonically isomorphic), but that lives over an abstract `RawCategory`, not the
concrete `Hypergraph` carrier, and presupposes the mono hypothesis via the pushout
square's monic leg.  Burned attacks: (1) `canonicalHypergraphBeq` the two candidate
complements of a non-mono match — they are genuinely non-isomorphic, so no canonical
`beq` can identify them (a `true` would be unsound); (2) restrict the decision to
mono matches to recover uniqueness — that is exactly `dpgHasMonoMatchComplementExists`
= `true`, i.e. abandoning the non-mono case, not deciding it. -/
def dpgHasPushoutComplementUniqueness : Bool := false

end FX1Poly.Polygraph.Dpo
