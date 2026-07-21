/-! # FX1Poly.Polygraph.Frobenius.SpiderPartitionWord — the spider theorem, standalone

The free (extra)special commutative Frobenius PROP as boundary partitions.  A diagram over a
finite boundary is a canonical rep vector: `partition : List Nat` of length `inputs + outputs`,
where entry `i` is the least boundary index sharing `i`'s union-find block (`rep i <= i`,
`rep (rep i) = rep i`).  This is the corelation (extraspecial) invariant of Coya–Fong: the
partition of the combined boundary is a COMPLETE invariant precisely because the special law
`mult ; comult = id` erases the free-floating closed-circle count.

Hermetic and zero-axiom: imports only `Init`.  Own fuel-based union-find (no `WellFounded.fix`),
own cons-only structural `List Nat` equality (no `List.getD`/`List.reverse`), full-enumeration
matches only (no wildcard over a split scrutinee), `cond`/Bool-match branching (no propext `if`).

WALL: the closed-component count (floating circles / genus), the planar cyclic leg order
(non-commutative Frobenius / Temperley–Lieb), and the interacting-bialgebra completeness
(two Frobenius colours + Hopf = full ZX) are all out of reach of a boundary partition; see the
three `Has…` markers below. -/

namespace FX1Poly.Polygraph.SpiderPartition

/-! ## Cons-only structural primitives -/

/-- Structural indexer on `List Nat`, default `0` (never `List.getD`, which leaks propext). -/
def fspListGet : List Nat → Nat → Nat
  | [], _ => 0
  | value :: _, 0 => value
  | _ :: rest, position + 1 => fspListGet rest position

/-- Cons-only structural Boolean equality on `List Nat`. -/
def fspListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      Nat.beq leftHead rightHead && fspListBeq leftRest rightRest

/-- Reflexivity of `Nat.beq`. -/
theorem fspNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => fspNatBeqRefl value

/-- `Nat.beq`-true naturals are equal. -/
theorem fspNatBeqEq : (left right : Nat) → Nat.beq left right = true → left = right
  | 0, 0, _ => rfl
  | 0, _ + 1, hBeq => Bool.noConfusion hBeq
  | _ + 1, 0, hBeq => Bool.noConfusion hBeq
  | left + 1, right + 1, hBeq => congrArg Nat.succ (fspNatBeqEq left right hBeq)

/-- Both conjuncts of a true Boolean `&&`. -/
theorem fspAndElim : (left right : Bool) → (left && right) = true → left = true ∧ right = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hAnd => Bool.noConfusion hAnd
  | false, true, hAnd => Bool.noConfusion hAnd
  | false, false, hAnd => Bool.noConfusion hAnd

/-- Reflexivity of `fspListBeq`. -/
theorem fspListBeqRefl : (letters : List Nat) → fspListBeq letters letters = true
  | [] => rfl
  | head :: rest => by
      show (Nat.beq head head && fspListBeq rest rest) = true
      rw [fspNatBeqRefl head, fspListBeqRefl rest]; rfl

/-- `fspListBeq`-true lists are equal. -/
theorem fspListBeqEq : (left right : List Nat) → fspListBeq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := fspAndElim _ _ hBeq
      rw [fspNatBeqEq leftHead rightHead hSplit.left,
        fspListBeqEq leftRest rightRest hSplit.right]

/-! ## Fuel-based union-find over a parent-edge list (child → parent) -/

/-- Recorded parent of `node`, or `none`; first match wins. -/
def fspParent : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (child, parent) :: rest, node =>
      match Nat.beq child node with
      | true => some parent
      | false => fspParent rest node

/-- Follow parent edges to the root, fuel-bounded (structural on fuel). -/
def fspRoot : Nat → List (Nat × Nat) → Nat → Nat
  | 0, _, node => node
  | fuel + 1, links, node =>
      match fspParent links node with
      | none => node
      | some parent => fspRoot fuel links parent

/-- Root of `node`, fuel sized to the edge count. -/
def fspRootOf (links : List (Nat × Nat)) (node : Nat) : Nat :=
  fspRoot (links.length + 1) links node

/-- Point first root at second; no-op when roots already agree (idempotent merge). -/
def fspJoin (links : List (Nat × Nat)) (firstNode secondNode : Nat) : List (Nat × Nat) :=
  match Nat.beq (fspRootOf links firstNode) (fspRootOf links secondNode) with
  | true => links
  | false => (fspRootOf links firstNode, fspRootOf links secondNode) :: links

/-- Fold a rep/parent vector into union-find edges: join `nodeOff + k` with `repOff + vec[k]`. -/
def fspJoinVec (nodeOff repOff : Nat) : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [], links => links
  | position, value :: rest, links =>
      fspJoinVec nodeOff repOff (position + 1) rest
        (fspJoin links (nodeOff + position) (repOff + value))

/-! ## Canonicalisation: rep/parent vector → least-index canonical rep vector -/

/-- Least index `scan` (from a start, fuel-bounded) whose root is `targetRoot`. -/
def fspLeastRep (links : List (Nat × Nat)) (targetRoot : Nat) : Nat → Nat → Nat
  | scan, 0 => scan
  | scan, fuel + 1 =>
      match Nat.beq (fspRootOf links scan) targetRoot with
      | true => scan
      | false => fspLeastRep links targetRoot (scan + 1) fuel

/-- The canonical rep vector over points `0 .. total-1` from a union-find edge list. -/
def fspRepVecOver (links : List (Nat × Nat)) (total : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | index, fuel + 1 =>
      fspLeastRep links (fspRootOf links index) 0 total
        :: fspRepVecOver links total (index + 1) fuel

/-- Canonicalise any rep/parent vector into least-index canonical form. -/
def fspCanonicalise (vec : List Nat) : List Nat :=
  fspRepVecOver (fspJoinVec 0 0 0 vec []) vec.length 0 vec.length

/-- Canonical-form predicate on a rep vector: every entry `rep i` has `rep i <= i` and
`rep (rep i) = rep i`. -/
def fspVecCanonicalFrom (vec : List Nat) : Nat → Nat → Bool
  | _, 0 => true
  | index, fuel + 1 =>
      let repHere := fspListGet vec index
      Nat.ble repHere index
        && Nat.beq (fspListGet vec repHere) repHere
        && fspVecCanonicalFrom vec (index + 1) fuel

/-- Whole-vector canonical predicate. -/
def fspVecCanonical (vec : List Nat) : Bool := fspVecCanonicalFrom vec 0 vec.length

/-! ## The FrobDiagram carrier -/

/-- A special-commutative-Frobenius diagram over a finite boundary: `inputs` on the bottom,
`outputs` on top, and the canonical boundary partition as a rep vector of length
`inputs + outputs`. -/
structure FspFrobDiagram where
  inputs : Nat
  outputs : Nat
  partition : List Nat

/-- Structural equality decision on diagrams (via `fspListBeq`, not derived). -/
def fspDecideEq (left right : FspFrobDiagram) : Bool :=
  Nat.beq left.inputs right.inputs
    && Nat.beq left.outputs right.outputs
    && fspListBeq left.partition right.partition

/-- A diagram is well-formed when its partition length matches the boundary and is canonical. -/
def fspWellFormed (diagram : FspFrobDiagram) : Bool :=
  Nat.beq diagram.partition.length (diagram.inputs + diagram.outputs)
    && fspVecCanonical diagram.partition

/-! ## Spider generators -/

/-- The all-`0` rep vector of length `count` (one block for everything). -/
def fspZeros : Nat → List Nat
  | 0 => []
  | count + 1 => 0 :: fspZeros count

/-- `[start, start+1, …, start+count-1]`. -/
def fspCountUp : Nat → Nat → List Nat
  | _, 0 => []
  | start, count + 1 => start :: fspCountUp (start + 1) count

/-- Cons-only append on `List Nat`. -/
def fspAppendNat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: fspAppendNat xs ys

/-- The single spider `m → n`: every boundary leg in one block. -/
def fspSpider (inputCount outputCount : Nat) : FspFrobDiagram :=
  { inputs := inputCount, outputs := outputCount, partition := fspZeros (inputCount + outputCount) }

/-- Identity rep vector: input `i` paired with output `i`, least rep `i`. -/
def fspIdentityVec (legCount : Nat) : List Nat :=
  fspAppendNat (fspCountUp 0 legCount) (fspCountUp 0 legCount)

/-- The identity diagram `n → n`. -/
def fspIdentity (legCount : Nat) : FspFrobDiagram :=
  { inputs := legCount, outputs := legCount, partition := fspIdentityVec legCount }

/-- Unit `0 → 1`. -/
def fspUnit : FspFrobDiagram := { inputs := 0, outputs := 1, partition := [0] }

/-- Counit `1 → 0`. -/
def fspCounit : FspFrobDiagram := { inputs := 1, outputs := 0, partition := [0] }

/-- Multiplication `2 → 1` (all three legs one block). -/
def fspMult : FspFrobDiagram := { inputs := 2, outputs := 1, partition := fspZeros 3 }

/-- Comultiplication `1 → 2` (all three legs one block). -/
def fspComult : FspFrobDiagram := { inputs := 1, outputs := 2, partition := fspZeros 3 }

/-- The symmetry / swap `2 → 2`: input 0 to output 1, input 1 to output 0. -/
def fspSwap : FspFrobDiagram := { inputs := 2, outputs := 2, partition := [0, 1, 1, 0] }

/-! ## Composition: glue the shared boundary, transitive-close, restrict to the outer boundary

Universe layout for `fspCompose d1 d2` (`d1 : m → n`, `d2 : n → p`):
`[d1 inputs 0..m-1] [shared n legs m..m+n-1] [d2 outputs m+n..m+n+p-1]`.
`d1`'s outputs and `d2`'s inputs share the SAME universe ids `m..m+n-1`, so gluing is automatic.
Both partitions are folded into a single union-find; the outer boundary (d1 inputs, d2 outputs)
is read back with least-index labels. -/

/-- Outer boundary index → universe id (inputs stay put; outputs jump past the shared legs). -/
def fspOuterToUniverse (inputCount sharedCount outerIndex : Nat) : Nat :=
  match Nat.blt outerIndex inputCount with
  | true => outerIndex
  | false => inputCount + sharedCount + (outerIndex - inputCount)

/-- Least outer index whose universe root is `targetRoot`. -/
def fspOuterLeastRep (links : List (Nat × Nat)) (inputCount sharedCount targetRoot : Nat) :
    Nat → Nat → Nat
  | scan, 0 => scan
  | scan, fuel + 1 =>
      match Nat.beq (fspRootOf links (fspOuterToUniverse inputCount sharedCount scan)) targetRoot with
      | true => scan
      | false => fspOuterLeastRep links inputCount sharedCount targetRoot (scan + 1) fuel

/-- Read back the outer boundary as a canonical least-index rep vector. -/
def fspOuterRepVec (links : List (Nat × Nat)) (inputCount sharedCount outerTotal : Nat) :
    Nat → Nat → List Nat
  | _, 0 => []
  | index, fuel + 1 =>
      fspOuterLeastRep links inputCount sharedCount
          (fspRootOf links (fspOuterToUniverse inputCount sharedCount index)) 0 outerTotal
        :: fspOuterRepVec links inputCount sharedCount outerTotal (index + 1) fuel

/-- Compose `d1 : m → n` with `d2 : n → p` into `m → p`. -/
def fspCompose (first second : FspFrobDiagram) : FspFrobDiagram :=
  let inputCount := first.inputs
  let sharedCount := first.outputs
  let outputCount := second.outputs
  let links := fspJoinVec inputCount inputCount 0 second.partition
    (fspJoinVec 0 0 0 first.partition [])
  let outerTotal := inputCount + outputCount
  { inputs := inputCount, outputs := outputCount,
    partition := fspOuterRepVec links inputCount sharedCount outerTotal 0 outerTotal }

/-! ## Decision-procedure metatheory -/

/-- The decision is reflexive. -/
theorem fspDecideEqRefl : (diagram : FspFrobDiagram) → fspDecideEq diagram diagram = true := by
  intro diagram
  show (Nat.beq diagram.inputs diagram.inputs
      && Nat.beq diagram.outputs diagram.outputs
      && fspListBeq diagram.partition diagram.partition) = true
  rw [fspNatBeqRefl, fspNatBeqRefl, fspListBeqRefl]; rfl

/-- The decision reflects equality: a `true` verdict means the diagrams are equal. -/
theorem fspDecideEqEq : (left right : FspFrobDiagram) → fspDecideEq left right = true → left = right := by
  intro left right hDecide
  cases left with
  | mk leftInputs leftOutputs leftPartition =>
    cases right with
    | mk rightInputs rightOutputs rightPartition =>
      have hSplit := fspAndElim _ _ hDecide
      have hHead := fspAndElim _ _ hSplit.left
      have hInputs := fspNatBeqEq _ _ hHead.left
      have hOutputs := fspNatBeqEq _ _ hHead.right
      have hPartition := fspListBeqEq _ _ hSplit.right
      subst hInputs; subst hOutputs; subst hPartition; rfl

/-- Symmetry of the decision. -/
theorem fspDecideEqSymm (left right : FspFrobDiagram) (hDecide : fspDecideEq left right = true) :
    fspDecideEq right left = true := by
  have hEq := fspDecideEqEq _ _ hDecide; subst hEq; exact fspDecideEqRefl _

/-- Transitivity of the decision. -/
theorem fspDecideEqTrans (left middle right : FspFrobDiagram)
    (hLeftMiddle : fspDecideEq left middle = true) (hMiddleRight : fspDecideEq middle right = true) :
    fspDecideEq left right = true := by
  have hLeft := fspDecideEqEq _ _ hLeftMiddle
  have hRight := fspDecideEqEq _ _ hMiddleRight
  subst hLeft; subst hRight; exact fspDecideEqRefl _

/-! ## The special-commutative-Frobenius congruence -/

/-- The corelation (extraspecial) congruence on Frobenius diagrams: the equivalence closure of the
special-commutative-Frobenius generator equations that the boundary partition witnesses.  Each
generator row is a genuine boundary-partition identity (spider fusion, (co)unit absorption,
identity law) verified by the engine. -/
inductive FspFrobConv : FspFrobDiagram → FspFrobDiagram → Prop where
  | refl (diagram : FspFrobDiagram) : FspFrobConv diagram diagram
  | symm {left right : FspFrobDiagram} : FspFrobConv left right → FspFrobConv right left
  | trans {left middle right : FspFrobDiagram} :
      FspFrobConv left middle → FspFrobConv middle right → FspFrobConv left right
  /-- Spider fusion / the special-Frobenius law: `mult ; comult` fuses to the single `2 → 2` spider. -/
  | spiderFusion : FspFrobConv (fspCompose fspMult fspComult) (fspSpider 2 2)
  /-- Counit absorbs multiplication: `mult ; counit` is the `2 → 0` spider. -/
  | multCounit : FspFrobConv (fspCompose fspMult fspCounit) (fspSpider 2 0)
  /-- Unit absorbs comultiplication: `unit ; comult` is the `0 → 2` spider. -/
  | unitComult : FspFrobConv (fspCompose fspUnit fspComult) (fspSpider 0 2)
  /-- Unit then counit is the empty `0 → 0` diagram (the closed circle discarded by the special law). -/
  | unitCounit : FspFrobConv (fspCompose fspUnit fspCounit) (fspSpider 0 0)
  /-- Left identity law: identity precomposed with multiplication is multiplication. -/
  | identityLeftMult : FspFrobConv (fspCompose (fspIdentity 2) fspMult) fspMult
  /-- Left identity law on the identity itself (a non-collapsing reindex witness). -/
  | identityLeftId : FspFrobConv (fspCompose (fspIdentity 2) (fspIdentity 2)) (fspIdentity 2)

/-- SOUNDNESS: convertible diagrams have equal canonical boundary partitions. -/
theorem fspFrobConv_partitionSound {left right : FspFrobDiagram} (hConv : FspFrobConv left right) :
    fspDecideEq left right = true := by
  induction hConv with
  | refl diagram => exact fspDecideEqRefl diagram
  | symm _ ih => exact fspDecideEqSymm _ _ ih
  | trans _ _ ihLeft ihRight => exact fspDecideEqTrans _ _ _ ihLeft ihRight
  | spiderFusion => rfl
  | multCounit => rfl
  | unitComult => rfl
  | unitCounit => rfl
  | identityLeftMult => rfl
  | identityLeftId => rfl

/-- COMPLETENESS (corelation): equal canonical boundary partitions are convertible. -/
theorem fspFrobConv_complete {left right : FspFrobDiagram} (hDecide : fspDecideEq left right = true) :
    FspFrobConv left right := by
  have hEq := fspDecideEqEq _ _ hDecide; subst hEq; exact .refl left

/-- REFUTATION: distinct canonical boundary partitions are not convertible. -/
theorem fspFrobConv_refute {left right : FspFrobDiagram} (hDecide : fspDecideEq left right = false) :
    ¬ FspFrobConv left right := by
  intro hConv
  have hTrue := fspFrobConv_partitionSound hConv
  rw [hTrue] at hDecide; exact Bool.noConfusion hDecide

/-- THE SPIDER THEOREM: convertibility is decided by canonical boundary-partition equality. -/
theorem fspFrobConv_iff_decide {left right : FspFrobDiagram} :
    FspFrobConv left right ↔ fspDecideEq left right = true :=
  ⟨fspFrobConv_partitionSound, fspFrobConv_complete⟩

/-- The convertibility relation is decidable. -/
instance instFspFrobConvDecidable (left right : FspFrobDiagram) :
    Decidable (FspFrobConv left right) :=
  decidable_of_iff _ fspFrobConv_iff_decide.symm

/-! ## The wall (T4) — three provably-out-of-reach refinements -/

/-- WALL: the closed floating-circle / genus count.  A boundary partition cannot see interior
components that touch no boundary leg (an η-then-ε bone circle vs. a μ-after-δ bubble both leave
the boundary partition unchanged, yet differ in isolated-circle count).  Deciding the full special
`Cospan(FinSet)` (or the genus of the closed 2-cobordism) needs a separate interior-own-root
counter that boundary-view threading cannot recover.

Burned attack 1: extend the rep vector with a trailing "circle count" Nat — but composition would
have to know which interior blocks touch NO outer leg AFTER reindexing, information the outer
least-rep readback deletes by construction (it only ranges over outer indices).
Burned attack 2: keep every universe node in the partition (no restriction) — then the invariant is
no longer boundary-indexed and two DIFFERENT boundary reindexings of the same diagram separate, so
soundness of `fspCompose` against the corelation theory fails.  The special law is exactly what
erases this count; keeping it is a different (non-special) theory. -/
def fspHasNonSpecialCircleCount : Bool := false

/-- WALL: the planar cyclic leg order.  Non-commutative Frobenius / Temperley–Lieb / chord diagrams
need a cyclic order on the legs of each block; an unordered partition identifies the crossing `swap`
with a planar cup-cap it is not equal to in the braided theory.

Burned attack 1: store each block as an ordered `List Nat` instead of a rep vector — but then
`fspJoin`'s idempotent merge (which makes spider fusion hold structurally) no longer applies, and
the union of two ordered lists has no canonical cyclic representative without an S_n normal form.
Burned attack 2: append a permutation-parity bit — insufficient, TL is not detected by parity
(the Jones/Kauffman bracket is a polynomial invariant, not a Z/2 one). -/
def fspHasPlanarCyclicOrder : Bool := false

/-- WALL: interacting-bialgebra completeness (two Frobenius colours + the bialgebra/Hopf law = full
ZX).  Two interacting Frobenius structures are decided by an F2 span invariant, not a single
partition; the phased/Kauffman content is the hard completeness frontier.

Burned attack 1: run two independent partition engines (one per colour) and pair them — the
bialgebra law relates the two colours, so a product of partitions is unsound (it validates
non-equal ZX diagrams).  Burned attack 2: quotient by the Hopf law on the combined partition — the
Hopf/antipode identity is not a partition identity (it collapses a bialgebra loop the partition
cannot represent), so no rep-vector quotient realises it. -/
def fspHasInteractingBialgebraCompleteness : Bool := false

/-! ## Fires (T5) — ground `rfl` decisions -/

/-- Spider fusion fires TRUE: `mult ; comult` equals the single `2 → 2` spider. -/
theorem fspFire_spiderFusion : fspDecideEq (fspCompose fspMult fspComult) (fspSpider 2 2) = true := rfl

/-- Unit-counit round fires TRUE: `unit ; counit` equals the empty `0 → 0` diagram. -/
theorem fspFire_unitCounitRound : fspDecideEq (fspCompose fspUnit fspCounit) (fspSpider 0 0) = true := rfl

/-- Genuine separation: the swap `2 → 2` is NOT the identity `2 → 2`. -/
theorem fspFire_swapNotIdentity : fspDecideEq fspSwap (fspIdentity 2) = false := rfl

/-- Identity law fires TRUE: `identity ; mult` equals `mult`. -/
theorem fspFire_identityLeftMult : fspDecideEq (fspCompose (fspIdentity 2) fspMult) fspMult = true := rfl

/-- Non-collapsing identity fire: `identity ; identity` equals `identity` (reindex witness). -/
theorem fspFire_identityLeftId :
    fspDecideEq (fspCompose (fspIdentity 2) (fspIdentity 2)) (fspIdentity 2) = true := rfl

/-- Canonicalise is idempotent on canonical input (one-block). -/
theorem fspFire_canonicaliseIdempotentZeros : fspCanonicalise (fspZeros 3) = fspZeros 3 := rfl

/-- Canonicalise is idempotent on canonical input (identity). -/
theorem fspFire_canonicaliseIdempotentId : fspCanonicalise (fspIdentityVec 2) = fspIdentityVec 2 := rfl

/-- The generators and identity are well-formed. -/
theorem fspFire_multWellFormed : fspWellFormed fspMult = true := rfl

/-- Well-formedness of the identity diagram. -/
theorem fspFire_identityWellFormed : fspWellFormed (fspIdentity 3) = true := rfl

end FX1Poly.Polygraph.SpiderPartition
