/-! # Polygraph/LinearLogic/MultiplicativeProofNet — unit-free MLL proof-structures + the Danos–Regnier DECISION

Multiplicative linear logic without units (`⊗`, `⅋`, dual atoms), read as PROOF STRUCTURES over
occurrence-indexed links, with the **Danos–Regnier correctness criterion** as a total decidable `Bool`
function: a proof structure is a proof *net* iff EVERY switching of its par-links yields a correction graph
that is **acyclic AND connected**.

## What this file ships (each piece self-contained, Init only, zero-axiom)

  * **T1 — syntax.**  `MllFormula` (atom index + polarity | tensor | par) with computing `DecidableEq` and the
    involutive de-Morgan `dual`; `MllLink` (axiom | cut | tensor | par) over occurrence ids; `MllProofStructure`
    = an occurrence count + a link list; a decidable `isWellFormed` range check.
  * **T2 — the switching graph + the DR decision.**  A switching = one boolean per par-link; the correction
    graph = the fixed axiom/cut/tensor edges plus, per par-link, the ONE chosen premise→conclusion edge.
    `mnlDecideProofNetCorrect` enumerates all `2^(#par)` switchings and, for each, tests ACYCLIC (a union-find
    fold that flags a merge of two already-same-component endpoints) AND CONNECTED (all occurrences share one
    component).  Total `Bool`; well-definedness witnessed by `mnlAllSwitchings_ne_nil`.
  * **T3 — soundness (base) + the wall.**  `MllSequentProof` (axiom / ⊗ / ⅋ / cut rules) and the desugaring
    `mnlDesugar` into a proof structure.  Soundness for the AXIOM rule is a general theorem
    (`mnlAxiomRuleDesugarsToCorrectNet`, all atom indices).  The full inductive soundness step and the converse
    SEQUENTIALIZATION are walled with named `false` markers naming the precise obstructions.
  * **T4 — ground fires.**  The single axiom net and a par of an axiom are DR-correct; a tensor of dual atoms is
    cyclic (not correct); two disjoint axioms are disconnected (not correct).

## The reused idea — the fuel-bounded union-find

The graph engine is the fuel-bounded `Nat`-id union-find of the shipped Joyal–Street matching decision
(`Polygraph/TwoCategory/WalkingAdjunction/MatchingDecision.lean`: `unionFindRootOf` / `isSameComponent` /
`unionFindJoin`, and the `stepCap` cycle-detector pattern — a join that finds its two endpoints already
connected closes a loop).  That module sits behind the entire (unbuilt) 2-category tower, so this file inlines
the ~26-line kernel under the `mnl` prefix rather than importing it; the implementation is the same
structural / `Nat`-fuel recursion (no `WellFounded.fix` / `omega` / `simp`-AC).

Raw Lean 4 + Init only.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.LinearLogic

/-! ## T1 — unit-free MLL syntax -/

/-- A **unit-free MLL formula**: a polarised atom (`index` names the propositional variable, `isPositive`
distinguishes `p` from its dual `p^⊥`), a multiplicative conjunction `tensor` (`⊗`), or a multiplicative
disjunction `par` (`⅋`).  A flat `Nat`/recursive datum, so equality decides and computes. -/
inductive MllFormula where
  | atom (index : Nat) (isPositive : Bool)
  | tensor (left right : MllFormula)
  | par (left right : MllFormula)
deriving DecidableEq

/-- De-Morgan **duality**: flip an atom's polarity and swap `tensor ↔ par` recursively.  A plain structural
function — no axioms. -/
def MllFormula.dual : MllFormula → MllFormula
  | MllFormula.atom index isPositive => MllFormula.atom index (not isPositive)
  | MllFormula.tensor left right => MllFormula.par left.dual right.dual
  | MllFormula.par left right => MllFormula.tensor left.dual right.dual

/-- Duality is an **involution**: `dual (dual A) = A`.  Structural induction; the atom base flips the polarity
back by `cases` on the boolean. -/
theorem MllFormula.dual_dual (formula : MllFormula) : formula.dual.dual = formula := by
  induction formula with
  | atom index isPositive => cases isPositive <;> rfl
  | tensor left right ihLeft ihRight =>
      show MllFormula.tensor left.dual.dual right.dual.dual = MllFormula.tensor left right
      rw [ihLeft, ihRight]
  | par left right ihLeft ihRight =>
      show MllFormula.par left.dual.dual right.dual.dual = MllFormula.par left right
      rw [ihLeft, ihRight]

/-- A **link** of a proof structure, over occurrence indices (`Nat` ids): an AXIOM link connects a dual pair of
atom occurrences, a CUT link connects a dual pair of formula occurrences, a TENSOR / PAR link has two premise
occurrences and one conclusion occurrence.  The par-link is the ONLY switch point. -/
inductive MllLink where
  | axiomLink (posOcc negOcc : Nat)
  | cutLink (leftOcc rightOcc : Nat)
  | tensorLink (premiseA premiseB conclusion : Nat)
  | parLink (premiseA premiseB conclusion : Nat)
deriving DecidableEq

/-- A **proof structure**: the number of formula occurrences (ids `0 … occCount-1`) and the list of links. -/
structure MllProofStructure where
  occCount : Nat
  links : List MllLink
deriving DecidableEq

/-- Whether every occurrence id a link mentions is below the occurrence count. -/
def MllLink.isInRange (occCount : Nat) : MllLink → Bool
  | MllLink.axiomLink posOcc negOcc => posOcc < occCount && negOcc < occCount
  | MllLink.cutLink leftOcc rightOcc => leftOcc < occCount && rightOcc < occCount
  | MllLink.tensorLink premiseA premiseB conclusion =>
      premiseA < occCount && premiseB < occCount && conclusion < occCount
  | MllLink.parLink premiseA premiseB conclusion =>
      premiseA < occCount && premiseB < occCount && conclusion < occCount

/-- Range **well-formedness**: every link references only declared occurrences. -/
def MllProofStructure.isWellFormed (proofStructure : MllProofStructure) : Bool :=
  proofStructure.links.all (MllLink.isInRange proofStructure.occCount)

/-! ## The fuel-bounded union-find (inlined from the shipped `MatchingDecision` kernel) -/

/-- The recorded parent of a node (a child→parent edge), `none` at a root. -/
def mnlParentOf : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (child, parent) :: rest, node =>
      if child == node then some parent else mnlParentOf rest node

/-- Follow parent edges to the root, fuel-bounded (the chain is no longer than the edge count). -/
def mnlRootFuel : Nat → List (Nat × Nat) → Nat → Nat
  | 0, _, node => node
  | fuel + 1, links, node =>
      match mnlParentOf links node with
      | none => node
      | some parent => mnlRootFuel fuel links parent

/-- The root of a node, with fuel sized to the edge list. -/
def mnlRootOf (links : List (Nat × Nat)) (node : Nat) : Nat :=
  mnlRootFuel (links.length + 1) links node

/-- Whether two nodes are already in the same component. -/
def mnlIsSameComponent (links : List (Nat × Nat)) (firstNode secondNode : Nat) : Bool :=
  mnlRootOf links firstNode == mnlRootOf links secondNode

/-- Union two nodes — point the first root at the second (a no-op when already joined). -/
def mnlJoin (links : List (Nat × Nat)) (firstNode secondNode : Nat) : List (Nat × Nat) :=
  let firstRoot := mnlRootOf links firstNode
  let secondRoot := mnlRootOf links secondNode
  if firstRoot == secondRoot then links else (firstRoot, secondRoot) :: links

/-! ## T2 — the switching graph -/

/-- The **fixed edges** of a proof structure — the axiom / cut / tensor edges present in every switching.  An
axiom or cut connects its pair; a tensor connects each premise to its conclusion; a par contributes NO fixed
edge (its edge is switch-selected). -/
def mnlFixedEdges : List MllLink → List (Nat × Nat)
  | [] => []
  | MllLink.axiomLink posOcc negOcc :: rest => (posOcc, negOcc) :: mnlFixedEdges rest
  | MllLink.cutLink leftOcc rightOcc :: rest => (leftOcc, rightOcc) :: mnlFixedEdges rest
  | MllLink.tensorLink premiseA premiseB conclusion :: rest =>
      (premiseA, conclusion) :: (premiseB, conclusion) :: mnlFixedEdges rest
  | MllLink.parLink _premiseA _premiseB _conclusion :: rest => mnlFixedEdges rest

/-- The **switch-selected edges** for a choice vector: walking the link list, each par-link consumes the head
boolean and wires its `premiseA` (choice `true`) OR `premiseB` (choice `false`) to its conclusion; a choice
vector shorter than the par-link count defaults exhausted par-links to `premiseA`.  Non-par links pass the choice
vector through unchanged. -/
def mnlSwitchingEdges : List MllLink → List Bool → List (Nat × Nat)
  | [], _ => []
  | MllLink.parLink premiseA premiseB conclusion :: rest, choice :: choicesRest =>
      (if choice then (premiseA, conclusion) else (premiseB, conclusion))
        :: mnlSwitchingEdges rest choicesRest
  | MllLink.parLink premiseA _premiseB conclusion :: rest, [] =>
      (premiseA, conclusion) :: mnlSwitchingEdges rest []
  | MllLink.axiomLink _posOcc _negOcc :: rest, choices => mnlSwitchingEdges rest choices
  | MllLink.cutLink _leftOcc _rightOcc :: rest, choices => mnlSwitchingEdges rest choices
  | MllLink.tensorLink _premiseA _premiseB _conclusion :: rest, choices => mnlSwitchingEdges rest choices

/-- The number of par-links (the number of switch points). -/
def mnlCountParLinks : List MllLink → Nat
  | [] => 0
  | MllLink.parLink _premiseA _premiseB _conclusion :: rest => mnlCountParLinks rest + 1
  | MllLink.axiomLink _posOcc _negOcc :: rest => mnlCountParLinks rest
  | MllLink.cutLink _leftOcc _rightOcc :: rest => mnlCountParLinks rest
  | MllLink.tensorLink _premiseA _premiseB _conclusion :: rest => mnlCountParLinks rest

/-- Every choice vector of a given length — the `2^count` switchings, structural on the count. -/
def mnlAllSwitchings : Nat → List (List Bool)
  | 0 => [[]]
  | count + 1 =>
      (mnlAllSwitchings count).foldr
        (fun shorter results => (false :: shorter) :: (true :: shorter) :: results) []

/-- **Well-definedness of the enumeration**: `mnlAllSwitchings count` is never empty, so the DR decision
quantifies over a nonempty family of switchings. -/
theorem mnlAllSwitchings_ne_nil (count : Nat) : mnlAllSwitchings count ≠ [] := by
  induction count with
  | zero => exact List.cons_ne_nil _ _
  | succ smaller ih =>
      unfold mnlAllSwitchings
      cases headTail : mnlAllSwitchings smaller with
      | nil => exact absurd headTail ih
      | cons head tail => exact List.cons_ne_nil _ _

/-! ## The Danos–Regnier tests -/

/-- The union-find state threaded through the acyclicity fold: the connectivity links so far, and whether a
cycle has been detected. -/
structure MllDrState where
  links : List (Nat × Nat)
  hasCycle : Bool

/-- Process one correction-graph edge: if its two endpoints are ALREADY connected, adding it closes a cycle —
flag `hasCycle`; otherwise union the endpoints (the `stepCap` cycle-detector pattern). -/
def mnlAcyclicStep (state : MllDrState) (edge : Nat × Nat) : MllDrState :=
  if mnlIsSameComponent state.links edge.1 edge.2 then
    { links := state.links, hasCycle := true }
  else
    { links := mnlJoin state.links edge.1 edge.2, hasCycle := state.hasCycle }

/-- Fold the acyclicity step over all edges, from the empty union-find. -/
def mnlRunAcyclic (edges : List (Nat × Nat)) : MllDrState :=
  edges.foldl mnlAcyclicStep { links := [], hasCycle := false }

/-- Whether every occurrence `0 … occCount-1` shares occurrence `0`'s component. -/
def mnlIsFullyConnected (occCount : Nat) (links : List (Nat × Nat)) : Bool :=
  (List.range occCount).all (fun node => mnlIsSameComponent links node 0)

/-- Whether ONE switching's correction graph is Danos–Regnier correct: acyclic AND connected. -/
def mnlSwitchingIsCorrect (proofStructure : MllProofStructure) (choices : List Bool) : Bool :=
  let edges := mnlFixedEdges proofStructure.links ++ mnlSwitchingEdges proofStructure.links choices
  let final := mnlRunAcyclic edges
  not final.hasCycle && mnlIsFullyConnected proofStructure.occCount final.links

/-- ★ **The Danos–Regnier correctness DECISION**: a proof structure is a proof NET iff EVERY switching of its
par-links yields an acyclic, connected correction graph.  A total `Bool` function — decides by `rfl` on concrete
small nets. -/
def mnlDecideProofNetCorrect (proofStructure : MllProofStructure) : Bool :=
  (mnlAllSwitchings (mnlCountParLinks proofStructure.links)).all
    (mnlSwitchingIsCorrect proofStructure)

/-! ## T3 — sequent proofs, the desugaring, and soundness (base) -/

/-- A cut-free-plus-cut **MLL sequent derivation**, indexed by its conclusion sequent (a list of formulas).  The
axiom rule proves `⊢ p, p^⊥`; `⅋` merges the two leading formulas; `⊗` joins two derivations at a tensor; `cut`
eliminates a dual pair across two derivations. -/
inductive MllSequentProof : List MllFormula → Type where
  | axiomRule (atomIndex : Nat) :
      MllSequentProof [MllFormula.atom atomIndex true, MllFormula.atom atomIndex false]
  | parRule {sequent : List MllFormula} {leftFormula rightFormula : MllFormula} :
      MllSequentProof (leftFormula :: rightFormula :: sequent) →
      MllSequentProof (MllFormula.par leftFormula rightFormula :: sequent)
  | tensorRule {leftSequent rightSequent : List MllFormula} {leftFormula rightFormula : MllFormula} :
      MllSequentProof (leftFormula :: leftSequent) →
      MllSequentProof (rightFormula :: rightSequent) →
      MllSequentProof (MllFormula.tensor leftFormula rightFormula :: (leftSequent ++ rightSequent))
  | cutRule {leftSequent rightSequent : List MllFormula} {cutFormula : MllFormula} :
      MllSequentProof (cutFormula :: leftSequent) →
      MllSequentProof (cutFormula.dual :: rightSequent) →
      MllSequentProof (leftSequent ++ rightSequent)

/-- Shift every occurrence id a link mentions by an offset (for disjoint-union of two sub-structures). -/
def MllLink.shiftBy (offset : Nat) : MllLink → MllLink
  | MllLink.axiomLink posOcc negOcc => MllLink.axiomLink (posOcc + offset) (negOcc + offset)
  | MllLink.cutLink leftOcc rightOcc => MllLink.cutLink (leftOcc + offset) (rightOcc + offset)
  | MllLink.tensorLink premiseA premiseB conclusion =>
      MllLink.tensorLink (premiseA + offset) (premiseB + offset) (conclusion + offset)
  | MllLink.parLink premiseA premiseB conclusion =>
      MllLink.parLink (premiseA + offset) (premiseB + offset) (conclusion + offset)

/-- Shift a list of occurrence ids by an offset. -/
def mnlShiftNatList (offset : Nat) (items : List Nat) : List Nat :=
  items.map (fun item => item + offset)

/-- The **desugaring** of a sequent derivation into a proof structure, returning also the occurrence ids of the
conclusion formulas in sequent order.  Occurrences of the right derivation are shifted past the left's count so
the two share no ids.  (The unreachable list-shape arms keep the function total; they never fire because a par /
tensor / cut derivation always exposes the required leading conclusion occurrence(s).) -/
def mnlDesugarAux : {sequent : List MllFormula} → MllSequentProof sequent → MllProofStructure × List Nat
  | _, MllSequentProof.axiomRule _atomIndex =>
      ({ occCount := 2, links := [MllLink.axiomLink 0 1] }, [0, 1])
  | _, MllSequentProof.parRule subProof =>
      let sub := mnlDesugarAux subProof
      match sub.2 with
      | premiseAOcc :: premiseBOcc :: restConclusions =>
          let conclusionOcc := sub.1.occCount
          ({ occCount := sub.1.occCount + 1,
             links := MllLink.parLink premiseAOcc premiseBOcc conclusionOcc :: sub.1.links },
           conclusionOcc :: restConclusions)
      | [] => (sub.1, [])
      | onlyOne :: [] => (sub.1, [onlyOne])
  | _, MllSequentProof.tensorRule leftProof rightProof =>
      let subLeft := mnlDesugarAux leftProof
      let subRight := mnlDesugarAux rightProof
      let offset := subLeft.1.occCount
      let conclusionOcc := subLeft.1.occCount + subRight.1.occCount
      match subLeft.2, subRight.2 with
      | leftHeadOcc :: restLeft, rightHeadOcc :: restRight =>
          ({ occCount := conclusionOcc + 1,
             links := MllLink.tensorLink leftHeadOcc (rightHeadOcc + offset) conclusionOcc
                        :: (subLeft.1.links ++ subRight.1.links.map (MllLink.shiftBy offset)) },
           conclusionOcc :: (restLeft ++ mnlShiftNatList offset restRight))
      | [], _rightConclusions => (subLeft.1, [])
      | _leftHead :: _leftRest, [] => (subLeft.1, [])
  | _, MllSequentProof.cutRule leftProof rightProof =>
      let subLeft := mnlDesugarAux leftProof
      let subRight := mnlDesugarAux rightProof
      let offset := subLeft.1.occCount
      match subLeft.2, subRight.2 with
      | leftHeadOcc :: restLeft, rightHeadOcc :: restRight =>
          ({ occCount := subLeft.1.occCount + subRight.1.occCount,
             links := MllLink.cutLink leftHeadOcc (rightHeadOcc + offset)
                        :: (subLeft.1.links ++ subRight.1.links.map (MllLink.shiftBy offset)) },
           restLeft ++ mnlShiftNatList offset restRight)
      | [], _rightConclusions => (subLeft.1, [])
      | _leftHead :: _leftRest, [] => (subLeft.1, [])

/-- The proof structure a sequent derivation desugars to. -/
def mnlDesugar {sequent : List MllFormula} (proof : MllSequentProof sequent) : MllProofStructure :=
  (mnlDesugarAux proof).1

/-- ★ **Soundness of the desugaring — the AXIOM base case, general over the atom index.**  For every atom index,
the desugaring of the axiom rule is the single-axiom net `⊢ p, p^⊥`, and that net is Danos–Regnier correct: its
one correction graph (no par-links) is the single edge `0—1`, which is acyclic and connects both occurrences.
The atom index never touches the graph, so `rfl` closes it uniformly. -/
theorem mnlAxiomRuleDesugarsToCorrectNet (atomIndex : Nat) :
    mnlDecideProofNetCorrect (mnlDesugar (MllSequentProof.axiomRule atomIndex)) = true := rfl

/-! ## T3 — the wall: full soundness (inductive step) and sequentialization

The base case above is a genuine general theorem.  The remaining directions are walled. -/

/-- **Wall marker — the inductive soundness step is NOT proven here.**  Full soundness ("the desugaring of ANY
sequent derivation is Danos–Regnier correct") needs, per rule, a graph lemma relating the switchings of a
COMBINED structure to those of its parts: a ⊗-link joins two disjoint correct correction graphs at a fresh node
(stays acyclic + connects them across all switchings); a ⅋-link adds a switch-selected edge that connects
without cycling in every switching; cut is the tensor argument without a fresh conclusion.  Each is an induction
over the correction graph under the `2^n` switchings — a union-find INVARIANT preservation whose zero-axiom proof
requires reasoning about the fuel-bounded root chains under the offset-disjoint index renaming (`shiftBy`), well
beyond what the `rfl`-decidable base case gives.  Two attacks were burned: (1) a direct `decide`/`rfl` on the
combined `mnlDecideProofNetCorrect` fails — the sub-proofs are abstract, so nothing computes; (2) a structural
induction on `MllSequentProof` stalls at the ⊗/cut cases, where relating `mnlRunAcyclic (fixedEdges ++
switchingEdges)` of the concatenated-and-shifted link list to the two sub-folds needs a disjoint-support
union-find commutation lemma (the same separation-style obligation the shipped matching route left as its
Godement residual).  `= false`. -/
def mnlHasFullSoundnessProof : Bool := false

/-- **Wall marker — SEQUENTIALIZATION is the deep wall.**  The converse of Danos–Regnier — "every DR-correct
proof structure is the desugaring of some sequent derivation" — is the sequentialization theorem
(Danos–Regnier 1989; Girard's splitting-tensor / empire argument).  It is NOT a `decide`-shaped fact: it asserts
the EXISTENCE of a derivation, built by finding a splitting tensor (or a terminal par) and recursing, i.e. a
`WellFounded` / structural-on-proof-structure construction over an existential.  The `2^n` switching enumeration
decides correctness but yields no witness derivation.  Two attacks were burned: (1) enumerate candidate final
rules and recurse on the shrunk structure — but the splitting-tensor SEARCH (which tensor splits the net into two
DR-correct halves) is itself an existential over correction-graph connectivity that the fuel enumeration does not
discharge, and the recursion is on structure size, needing `WellFounded.fix` (forbidden); (2) invert
`mnlDesugarAux` structurally — but its ⊗/cut arms concatenate-and-shift link lists non-injectively at the level
of a bare `MllProofStructure`, so no structural inverse recovers the split.  Ship the DECISION and the base
soundness; wall the reconstruction.  `= false`. -/
def mnlHasSequentialization : Bool := false

/-! ## T4 — ground fires -/

/-- The single-axiom net `⊢ p, p^⊥` — occurrences `0` (`p`) and `1` (`p^⊥`), one axiom link. -/
def mnlSingleAxiomNet : MllProofStructure :=
  { occCount := 2, links := [MllLink.axiomLink 0 1] }

/-- A par over one axiom: `⊢ p ⅋ p^⊥` — axiom `0—1`, then a par-link merging them into conclusion `2`. -/
def mnlParNet : MllProofStructure :=
  { occCount := 3, links := [MllLink.axiomLink 0 1, MllLink.parLink 0 1 2] }

/-- A tensor of dual atoms: `⊢ p ⊗ p^⊥` — axiom `0—1`, then a tensor-link to conclusion `2`.  NOT a proof net. -/
def mnlCyclicTensorNet : MllProofStructure :=
  { occCount := 3, links := [MllLink.axiomLink 0 1, MllLink.tensorLink 0 1 2] }

/-- Two disjoint axioms — `⊢ p, p^⊥` beside `⊢ q, q^⊥` with nothing joining them.  NOT connected. -/
def mnlDisconnectedNet : MllProofStructure :=
  { occCount := 4, links := [MllLink.axiomLink 0 1, MllLink.axiomLink 2 3] }

/-- ★ **Fire 1** — the single axiom net IS Danos–Regnier correct. -/
theorem mnlSingleAxiomNet_isCorrect : mnlDecideProofNetCorrect mnlSingleAxiomNet = true := rfl

/-- ★ **Fire 2** — a par of an axiom IS Danos–Regnier correct (both switchings acyclic + connected). -/
theorem mnlParNet_isCorrect : mnlDecideProofNetCorrect mnlParNet = true := rfl

/-- ★ **Fire 3** — a tensor of dual atoms is NOT Danos–Regnier correct: its unique correction graph closes a
cycle `0—1—2—0`. -/
theorem mnlCyclicTensorNet_isNotCorrect : mnlDecideProofNetCorrect mnlCyclicTensorNet = false := rfl

/-- **Fire 4** — two disjoint axioms are NOT Danos–Regnier correct: acyclic but disconnected. -/
theorem mnlDisconnectedNet_isNotCorrect : mnlDecideProofNetCorrect mnlDisconnectedNet = false := rfl

/-- **Fire 5 (soundness link)** — the desugaring of `⅋`-over-axiom (`⊢ p ⅋ p^⊥`) is DR-correct, connecting the
sequent layer (T3) to the decision (T2) on a concrete par net. -/
theorem mnlParProofDesugarsToCorrectNet :
    mnlDecideProofNetCorrect (mnlDesugar (MllSequentProof.parRule (MllSequentProof.axiomRule 0))) = true := rfl

end FX1Poly.Polygraph.LinearLogic
