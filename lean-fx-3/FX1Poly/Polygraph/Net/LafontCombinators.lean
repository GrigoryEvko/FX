import FX1Poly.Polygraph.LinearLogic.MultiplicativeProofNet

/-! # Lafont interaction combinators: the three-symbol system + six rules + local confluence

This file instantiates the Lafont **interaction combinators** — the concrete three-symbol universal
interaction-net system (`gammaCon` the constructor, `deltaDup` the duplicator, `epsilonEra` the eraser)
with the six specific interaction rules — and harvests the ORTHOGONALITY DIVIDEND directly: because every
agent has exactly ONE principal port, two disjoint active pairs never share an agent, so firing them in
either order reaches the SAME net (the one-step diamond), proved here as a literal `rfl` on a concrete
two-redex net.

## Model

  * A **wire** is a shared `Nat` port identity; two ports on the same wire carry the same id.  Auxiliary
    connectivity beyond direct sharing is recorded in a `wiring : List (Nat x Nat)` union-find, reusing the
    shipped fuel-bounded kit (`mnlRootOf` / `mnlIsSameComponent`) from `MultiplicativeProofNet` — no new
    union-find is derived.
  * An **agent** carries a stable `agentId`, its `kind`, and its `ports` (a `List Nat`; the HEAD is the
    single principal port, the tail is the auxiliary ports).  `epsilonEra` has arity 0 → `ports = [p]`;
    `gammaCon` / `deltaDup` have arity 2 → `ports = [p, a1, a2]`.
  * An **active pair** is two distinct agents whose principal ports are the same union-find component
    (`icbIsActivePair`, a structural `Bool`).

## What this file ships (each zero-axiom)

  * **`AgentKind` / `icbAgent` / `icbNet` / `icbIsActivePair`** (T1) — the carrier.
  * **`icbInteract`** (T2) — the six rules as ONE total dispatch on the ordered kind pair (all nine
    ordered cases enumerated): annihilate γγ / δδ / εε, commute γδ / δγ (four fresh agents, the 2×2 grid),
    erase εγ / εδ / γε / δε (delete + spawn two erasers on the auxiliaries).
  * **`icbReduceAt` / `icbReduceStep` / `icbIsNormalForm`** (T3) — one-step reduction and normal-form
    recognition; `icbDisjointRedexDiamond` is the local-confluence-by-orthogonality payoff, a `rfl`.
  * **`icbHasGlobalTermination := false` / `icbHasFullConfluence := false`** (T4) — the honest walls:
    interaction combinators are Turing-universal (Lafont), so global normalization is UNDECIDABLE.

## Zero-axiom verification

Structural `List`/`Nat` recursion, `Nat.decEq`-driven `if` and full-enumeration matches (no wildcard over a
split scrutinee), hand-rolled append (`icbCat`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`, `funext`, or `WellFounded.fix`.  Per-declaration gated in the audit twin.
-/

namespace FX1Poly.Polygraph

/-! ## T1 — the carrier: three symbols, agents, nets, active pairs -/

/-- The three Lafont interaction-combinator symbols. -/
inductive AgentKind where
  /-- The constructor combinator (binary principal-plus-two-auxiliary). -/
  | gammaCon
  /-- The duplicator combinator (binary). -/
  | deltaDup
  /-- The eraser combinator (nullary auxiliary; principal only). -/
  | epsilonEra

/-- Full-enumeration Boolean equality on kinds (all nine ordered cases explicit — propext-free). -/
def icbKindBeq : AgentKind → AgentKind → Bool
  | .gammaCon, .gammaCon => true
  | .gammaCon, .deltaDup => false
  | .gammaCon, .epsilonEra => false
  | .deltaDup, .gammaCon => false
  | .deltaDup, .deltaDup => true
  | .deltaDup, .epsilonEra => false
  | .epsilonEra, .gammaCon => false
  | .epsilonEra, .deltaDup => false
  | .epsilonEra, .epsilonEra => true

/-- An interaction-combinator **agent**: a stable identity, a symbol kind, and its ports — the HEAD of
`ports` is the single principal port, the tail lists the auxiliary ports. -/
structure icbAgent where
  /-- Stable identity of this agent. -/
  agentId : Nat
  /-- The agent's symbol. -/
  kind : AgentKind
  /-- Port wires: head = principal, tail = auxiliaries. -/
  ports : List Nat

/-- An interaction **net**: the agents plus a union-find `wiring` recording which port wires are joined. -/
structure icbNet where
  /-- The agents of the net. -/
  agents : List icbAgent
  /-- The union-find of joined port wires (reused fuel kit from `MultiplicativeProofNet`). -/
  wiring : List (Nat × Nat)

/-- The single principal port of an agent (the head of `ports`; `0` for a portless agent — never arises
for well-formed γ/δ/ε, all of which have a principal port). -/
def icbPrincipalPort (ag : icbAgent) : Nat :=
  match ag.ports with
  | [] => 0
  | principal :: _ => principal

/-- The first auxiliary port (second port), or `0` when absent. -/
def icbAux1 (ag : icbAgent) : Nat :=
  match ag.ports with
  | [] => 0
  | _ :: [] => 0
  | _ :: firstAux :: _ => firstAux

/-- The second auxiliary port (third port), or `0` when absent. -/
def icbAux2 (ag : icbAgent) : Nat :=
  match ag.ports with
  | [] => 0
  | _ :: [] => 0
  | _ :: _ :: [] => 0
  | _ :: _ :: secondAux :: _ => secondAux

/-- Find an agent by id (structural, `Nat.decEq`-driven). -/
def icbFindAgent : List icbAgent → Nat → Option icbAgent
  | [], _ => none
  | ag :: rest, wantedId => if ag.agentId = wantedId then some ag else icbFindAgent rest wantedId

/-- **Active pair (T1).**  Two DISTINCT agents whose principal ports lie in the same wiring component form
an active pair — the redex.  A structural `Bool`, reusing the shipped `mnlIsSameComponent`. -/
def icbIsActivePair (net : icbNet) (leftId rightId : Nat) : Bool :=
  match icbFindAgent net.agents leftId, icbFindAgent net.agents rightId with
  | some leftAg, some rightAg =>
      (if leftId = rightId then false else true) &&
        LinearLogic.mnlIsSameComponent net.wiring
          (icbPrincipalPort leftAg) (icbPrincipalPort rightAg)
  | some _, none => false
  | none, some _ => false
  | none, none => false

/-! ## T2 — the six interaction rules as one total dispatch -/

/-- Build a `gammaCon` agent with principal `p` and auxiliaries `a1`, `a2`. -/
def icbMkGamma (id p a1 a2 : Nat) : icbAgent := { agentId := id, kind := .gammaCon, ports := [p, a1, a2] }
/-- Build a `deltaDup` agent with principal `p` and auxiliaries `a1`, `a2`. -/
def icbMkDelta (id p a1 a2 : Nat) : icbAgent := { agentId := id, kind := .deltaDup, ports := [p, a1, a2] }
/-- Build an `epsilonEra` agent with principal `p`. -/
def icbMkEps (id p : Nat) : icbAgent := { agentId := id, kind := .epsilonEra, ports := [p] }

/-- **The six rules (T2).**  Given the two agents of an active pair (left = principal side, right = the
partner that is deleted) and a `fresh` id/wire base, returns the replacement agents installed where the
LEFT agent was, together with any extra wiring entries.  All nine ordered kind pairs are enumerated:

  * γγ / δδ — **annihilate**: no agents remain, the two pairs of auxiliaries cross-wire straight through.
  * εε — **annihilate**: both erasers vanish, no wiring.
  * γδ / δγ — **commute**: four fresh agents (two copies of each symbol) in the 2×2 grid; the four internal
    grid wires `fresh+4 … fresh+7` are shared directly, so no extra `wiring` entries are needed.
  * εγ / εδ / γε / δε — **erase**: the binary agent is deleted and the eraser is duplicated onto its two
    auxiliaries (two fresh `epsilonEra` agents). -/
def icbInteract (leftAg rightAg : icbAgent) (fresh : Nat) : List icbAgent × List (Nat × Nat) :=
  match leftAg.kind, rightAg.kind with
  | .gammaCon, .gammaCon =>
      ([], [(icbAux1 leftAg, icbAux1 rightAg), (icbAux2 leftAg, icbAux2 rightAg)])
  | .deltaDup, .deltaDup =>
      ([], [(icbAux1 leftAg, icbAux1 rightAg), (icbAux2 leftAg, icbAux2 rightAg)])
  | .epsilonEra, .epsilonEra =>
      ([], [])
  | .gammaCon, .deltaDup =>
      ([ icbMkDelta fresh       (icbAux1 leftAg)  (fresh + 4) (fresh + 5)
       , icbMkDelta (fresh + 1) (icbAux2 leftAg)  (fresh + 6) (fresh + 7)
       , icbMkGamma (fresh + 2) (icbAux1 rightAg) (fresh + 4) (fresh + 6)
       , icbMkGamma (fresh + 3) (icbAux2 rightAg) (fresh + 5) (fresh + 7) ], [])
  | .deltaDup, .gammaCon =>
      ([ icbMkGamma fresh       (icbAux1 leftAg)  (fresh + 4) (fresh + 5)
       , icbMkGamma (fresh + 1) (icbAux2 leftAg)  (fresh + 6) (fresh + 7)
       , icbMkDelta (fresh + 2) (icbAux1 rightAg) (fresh + 4) (fresh + 6)
       , icbMkDelta (fresh + 3) (icbAux2 rightAg) (fresh + 5) (fresh + 7) ], [])
  | .epsilonEra, .gammaCon =>
      ([ icbMkEps fresh (icbAux1 rightAg), icbMkEps (fresh + 1) (icbAux2 rightAg) ], [])
  | .epsilonEra, .deltaDup =>
      ([ icbMkEps fresh (icbAux1 rightAg), icbMkEps (fresh + 1) (icbAux2 rightAg) ], [])
  | .gammaCon, .epsilonEra =>
      ([ icbMkEps fresh (icbAux1 leftAg), icbMkEps (fresh + 1) (icbAux2 leftAg) ], [])
  | .deltaDup, .epsilonEra =>
      ([ icbMkEps fresh (icbAux1 leftAg), icbMkEps (fresh + 1) (icbAux2 leftAg) ], [])

/-! ## T3 — one-step reduction, normal forms, and the local-confluence diamond -/

/-- Own append on agent lists (avoids `List.append`, whose lemmas leak `propext` here). -/
def icbCat : List icbAgent → List icbAgent → List icbAgent
  | [], ys => ys
  | x :: xs, ys => x :: icbCat xs ys

/-- Own append on wiring lists. -/
def icbCatWire : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | x :: xs, ys => x :: icbCatWire xs ys

/-- Position-preserving expansion: the LEFT agent expands to `repl`, the RIGHT (partner) agent to nothing,
every other agent is kept.  Because expansion happens in place, disjoint firings commute literally. -/
def icbExpand (leftId rightId : Nat) (repl : List icbAgent) : List icbAgent → List icbAgent
  | [] => []
  | ag :: rest =>
      if ag.agentId = leftId then icbCat repl (icbExpand leftId rightId repl rest)
      else if ag.agentId = rightId then icbExpand leftId rightId repl rest
      else ag :: icbExpand leftId rightId repl rest

/-- Drop wiring entries whose either endpoint is one of the two consumed principal ports. -/
def icbWiringDrop (portL portR : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (u, v) :: rest =>
      if u = portL then icbWiringDrop portL portR rest
      else if u = portR then icbWiringDrop portL portR rest
      else if v = portL then icbWiringDrop portL portR rest
      else if v = portR then icbWiringDrop portL portR rest
      else (u, v) :: icbWiringDrop portL portR rest

/-- Max of two `Nat`s (own, no order lemmas needed — only computed). -/
def icbMaxNat (a b : Nat) : Nat := if a < b then b else a

/-- Max agent id in a net (fold). -/
def icbMaxId : List icbAgent → Nat
  | [] => 0
  | ag :: rest => icbMaxNat ag.agentId (icbMaxId rest)

/-- Max port id used anywhere in a port list. -/
def icbMaxInList : List Nat → Nat
  | [] => 0
  | p :: rest => icbMaxNat p (icbMaxInList rest)

/-- Max port id across all agents. -/
def icbMaxPort : List icbAgent → Nat
  | [] => 0
  | ag :: rest => icbMaxNat (icbMaxInList ag.ports) (icbMaxPort rest)

/-- A fresh id/wire base strictly above every agent id and port in the net. -/
def icbFreshBase (net : icbNet) : Nat :=
  Nat.succ (icbMaxNat (icbMaxId net.agents) (icbMaxPort net.agents))

/-- **Reduce a specific active pair (T3).**  Look up both agents, fire the rule via `icbInteract`, install
the replacement in place of the left agent, delete the right, and drop the spent principal wire; when
either agent is missing this is a no-op. -/
def icbReduceAt (net : icbNet) (leftId rightId : Nat) : icbNet :=
  match icbFindAgent net.agents leftId, icbFindAgent net.agents rightId with
  | some leftAg, some rightAg =>
      let outcome := icbInteract leftAg rightAg (icbFreshBase net)
      { agents := icbExpand leftId rightId outcome.fst net.agents
      , wiring := icbCatWire outcome.snd
          (icbWiringDrop (icbPrincipalPort leftAg) (icbPrincipalPort rightAg) net.wiring) }
  | some _, none => net
  | none, some _ => net
  | none, none => net

/-- Find the first active ordered pair `(leftId, rightId)` with `leftId` earlier than `rightId` in the
agent list (structural double scan). -/
def icbScanFrom (net : icbNet) (leftId : Nat) : List icbAgent → Option (Nat × Nat)
  | [] => none
  | ag :: rest =>
      if icbIsActivePair net leftId ag.agentId then some (leftId, ag.agentId)
      else icbScanFrom net leftId rest

/-- Scan every earlier agent against all later agents for the first active pair. -/
def icbFirstActivePairAux (net : icbNet) : List icbAgent → Option (Nat × Nat)
  | [] => none
  | ag :: rest =>
      match icbScanFrom net ag.agentId rest with
      | some pair => some pair
      | none => icbFirstActivePairAux net rest

/-- The first active pair of the net, if any. -/
def icbFirstActivePair (net : icbNet) : Option (Nat × Nat) :=
  icbFirstActivePairAux net net.agents

/-- **One-step reduction (T3).**  Fire the first active pair; `none` at a normal form. -/
def icbReduceStep (net : icbNet) : Option icbNet :=
  match icbFirstActivePair net with
  | none => none
  | some (leftId, rightId) => some (icbReduceAt net leftId rightId)

/-- **Normal-form recognition (T3).**  A net is normal when it has no active pair. -/
def icbIsNormalForm (net : icbNet) : Bool :=
  match icbFirstActivePair net with
  | none => true
  | some _ => false

/-! ## T3 — concrete local-confluence diamond (orthogonality dividend) -/

/-- Two ε on wire `10` (an active εε pair, ids 0/1). -/
def icbDiamondEpsA : icbAgent := icbMkEps 0 10
/-- Its partner on the same wire. -/
def icbDiamondEpsB : icbAgent := icbMkEps 1 10
/-- Two ε on wire `20` (a second, disjoint active εε pair, ids 2/3). -/
def icbDiamondEpsC : icbAgent := icbMkEps 2 20
/-- Its partner on the same wire. -/
def icbDiamondEpsD : icbAgent := icbMkEps 3 20
/-- A net with TWO disjoint active εε pairs (no shared wire). -/
def icbDiamondNet : icbNet :=
  { agents := [icbDiamondEpsA, icbDiamondEpsB, icbDiamondEpsC, icbDiamondEpsD], wiring := [] }

/-- ★ **Local confluence by orthogonality (T3 headline).**  Reducing the two DISJOINT active pairs `(0,1)`
and `(2,3)` in either order reaches the SAME net — the one-step diamond, pinned by `rfl`.  This is the
no-critical-pairs dividend of the single-principal-port discipline, instantiated on the six-rule system. -/
theorem icbDisjointRedexDiamond :
    icbReduceAt (icbReduceAt icbDiamondNet 0 1) 2 3
      = icbReduceAt (icbReduceAt icbDiamondNet 2 3) 0 1 := rfl

/-! ## T4 — the honest walls: Turing-universality ⇒ undecidable global normalization -/

/-- **Wall marker (T4).**  Whether an ARBITRARY interaction-combinator net reaches a normal form is
UNDECIDABLE: the γ/δ/ε system is Turing-universal (Lafont 1997 — it faithfully encodes the SK-combinators
and hence the untyped λ-calculus), so a total zero-axiom decider for "this net normalises" would decide the
halting problem.  Two attacks burned:

  1. **Bounded-fuel reduction is one-sided.**  `icbReduceStep` iterated with any fuel `k` witnesses
     TERMINATION when a normal form is hit within `k` steps, but exhausting the fuel proves nothing — it
     cannot certify NON-termination, so it is not a decider.
  2. **No structural size-decrease measure exists.**  The obvious agent-count measure FAILS because the
     `commute` rules (γδ / δγ) STRICTLY GROW the agent count (two agents become four), so reduction is not
     size-decreasing; no `WellFounded` order on nets is available zero-axiom (the same wall as the NET-4
     Dickson impossibility). -/
def icbHasGlobalTermination : Bool := false

/-- **Wall marker (T4).**  The LOCAL diamond (`icbDisjointRedexDiamond`) lands for disjoint redexes.  FULL
confluence over UNBOUNDED nets — that every pair of maximal reduction sequences meets — is NOT proven here:
it rides the same universality obstruction (a global normal form need not exist) plus the general-graph
fresh-wire allocation residual walled at `lfnHasGeneralGraphDiamond := false`. -/
def icbHasFullConfluence : Bool := false

/-! ## T5 — concrete fires -/

/-- A γ agent (id 0) on principal wire `5`, auxiliaries `1`, `2`. -/
def icbFireGammaA : icbAgent := icbMkGamma 0 5 1 2
/-- A second γ agent (id 1) on the same principal wire `5`, auxiliaries `3`, `4`. -/
def icbFireGammaB : icbAgent := icbMkGamma 1 5 3 4
/-- A net with a single γγ active pair. -/
def icbGammaGammaNet : icbNet := { agents := [icbFireGammaA, icbFireGammaB], wiring := [] }

/-- ★ **Fire 1: γγ annihilation cancels both agents.** -/
theorem icbFireGammaAnnihilates : (icbReduceAt icbGammaGammaNet 0 1).agents = [] := rfl

/-- ★ **Fire 1b: the annihilation cross-wires the auxiliaries straight through** (`1—3`, `2—4`). -/
theorem icbFireGammaWiring : (icbReduceAt icbGammaGammaNet 0 1).wiring = [(1, 3), (2, 4)] := rfl

/-- A δ agent (id 1) on principal wire `5`, auxiliaries `3`, `4`. -/
def icbFireDeltaB : icbAgent := icbMkDelta 1 5 3 4
/-- A net with a single γδ active pair. -/
def icbGammaDeltaNet : icbNet := { agents := [icbFireGammaA, icbFireDeltaB], wiring := [] }

/-- ★ **Fire 2: γδ commutation produces four fresh agents (the 2×2 grid).** -/
theorem icbFireCommuteProducesFour :
    (icbReduceAt icbGammaDeltaNet 0 1).agents
      = [ icbMkDelta 6 1 10 11, icbMkDelta 7 2 12 13
        , icbMkGamma 8 3 10 12, icbMkGamma 9 4 11 13 ] := rfl

/-- An ε agent (id 0) on principal wire `5`. -/
def icbFireEpsA : icbAgent := icbMkEps 0 5
/-- A γ agent (id 1) on principal wire `5`, auxiliaries `3`, `4`. -/
def icbFireGammaForErase : icbAgent := icbMkGamma 1 5 3 4
/-- A net with a single εγ active pair. -/
def icbEpsGammaNet : icbNet := { agents := [icbFireEpsA, icbFireGammaForErase], wiring := [] }

/-- ★ **Fire 3: εγ erasing deletes the constructor and spawns two erasers on its auxiliaries.** -/
theorem icbFireEraseSpawnsTwo :
    (icbReduceAt icbEpsGammaNet 0 1).agents = [ icbMkEps 6 3, icbMkEps 7 4 ] := rfl

/-- ★ **Fire 4: a net with no active pair decides `isNormalForm = true`.**  The two ε sit on DIFFERENT
wires, so they do not interact. -/
def icbNormalNet : icbNet := { agents := [icbMkEps 0 5, icbMkEps 1 9], wiring := [] }

/-- ★ Fire 4. -/
theorem icbNormalIsNormal : icbIsNormalForm icbNormalNet = true := rfl

/-- ★ **Fire 5: a net WITH an active pair decides `isNormalForm = false`.** -/
theorem icbGammaGammaNotNormal : icbIsNormalForm icbGammaGammaNet = false := rfl

/-- ★ Fire 5b: the γγ pair genuinely IS an active pair. -/
theorem icbGammaGammaActive : icbIsActivePair icbGammaGammaNet 0 1 = true := rfl

/-- ★ Fire 6 (control): two ε on different wires are NOT an active pair. -/
theorem icbNormalNotActive : icbIsActivePair icbNormalNet 0 1 = false := rfl

/-- ★ Fire 7: `icbReduceStep` fires the first active pair of the γγ net (down to the empty agent set). -/
theorem icbReduceStepFires :
    icbReduceStep icbGammaGammaNet = some { agents := [], wiring := [(1, 3), (2, 4)] } := rfl

end FX1Poly.Polygraph
