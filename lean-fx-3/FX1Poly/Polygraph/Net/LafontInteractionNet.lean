/-! # Lafont interaction nets: strong confluence for free from the principal-port discipline

This file builds Lafont-style INTERACTION NETS as a bounded, list-based rewrite system and harvests the
ORTHOGONALITY DIVIDEND: because every agent has exactly ONE principal port, no agent can belong to two
active pairs, so any two distinct active pairs are DISJOINT — the "no critical pairs" property — and
disjoint firings COMMUTE.  That commutation IS the one-step diamond (strong confluence for free), proved
here as a literal list-splice equality with no graph isomorphism and no `WellFounded.fix`.

## What this file ships (each zero-axiom)

  * **`lfnAgent` / `lfnInteractionRule` / `lfnRuleTable`** — an agent is an identity + a symbol + the id
    its single PRINCIPAL port connects to + the ids of its auxiliary ports; a net is a `List lfnAgent`; a
    rule is keyed by an ordered symbol pair and carries a replacement fragment.
  * **`lfnFireResolved` / `lfnFireRedex` / `lfnNetStep`** — the reduction: fire a rule at an active pair
    by replacing the pair's two agents (the principal one becomes the rule RHS, the other becomes empty),
    position-preserving (a `flatMap`-style expansion, so it commutes literally).
  * **`lfnIsActivePair` / `lfnActivePairPartnerUnique` / `lfnActivePairsShareImpliesEqual`** — the
    ORTHOGONALITY: the single principal port forces the active-pair partner to be UNIQUE, so distinct
    active pairs share no agent.
  * **`lfnNetExpandCommute` / `lfnDisjointRedexCommute`** — ★ the STRONG-CONFLUENCE payoff: two disjoint
    resolved firings commute (fire order does not matter), reaching a common apex — the one-step diamond.
  * **`lfnHasGeneralGraphDiamond := false`** — the honest wall: the fully-general GRAPH-net diamond (nets
    equal up to renaming of internal wire nodes; fresh-wire allocation) is NOT proven here; it rides the
    graph-isomorphism / union-find fresh-allocation independence residual that is walled elsewhere.

## Zero-axiom verification

Structural List/Nat recursion, `Nat.decEq`-driven `if` (no `==`/`Nat.beq` extraction), hand-rolled append
(`lfnCat`) with its own associativity so nothing routes through `List.append_assoc` (which leaks `propext`
in this Init-only setting).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`, `funext`, or `WellFounded.fix`.  Per-declaration gated in the audit twin.
-/

namespace FX1Poly.Polygraph

/-! ## Bool / decidable-`if` micro-kit (self-contained, no `==`) -/

/-- From `a && b = true`, the left conjunct is `true`. -/
theorem lfnBandTrueLeft {leftBit rightBit : Bool} (h : (leftBit && rightBit) = true) :
    leftBit = true := by
  cases leftBit with
  | false => exact Bool.noConfusion h
  | true => rfl

/-- From `a && b = true`, the right conjunct is `true`. -/
theorem lfnBandTrueRight {leftBit rightBit : Bool} (h : (leftBit && rightBit) = true) :
    rightBit = true := by
  cases leftBit with
  | false => exact Bool.noConfusion h
  | true => exact h

/-- A decidable proposition that gates a `true`/`false` and reports `true` really holds. -/
theorem lfnIfEqTrue {Predicate : Prop} [inst : Decidable Predicate]
    (h : (if Predicate then true else false) = true) : Predicate := by
  cases inst with
  | isTrue holds => exact holds
  | isFalse fails => rw [if_neg fails] at h; exact Bool.noConfusion h

/-! ## Interaction-net representation (T1) -/

/-- An interaction-net **agent**: a stable identity `agentId`, a `symbol` (the agent kind), the id its
single PRINCIPAL port connects to (`principalTarget`), and the ids its auxiliary ports connect to.  The
single principal port is the crux of Lafont orthogonality — an agent participates in at most one active
pair. -/
structure lfnAgent where
  /-- Stable identity of this agent. -/
  agentId : Nat
  /-- The agent's symbol / kind. -/
  symbol : Nat
  /-- The id of the agent connected via this agent's single principal port. -/
  principalTarget : Nat
  /-- The ids connected via the auxiliary ports. -/
  auxPorts : List Nat

/-- An **interaction rule**, keyed by the ORDERED symbol pair that meets principal-to-principal; `rhs` is
the replacement net fragment installed where the active pair was. -/
structure lfnInteractionRule where
  /-- Symbol of the left (principal) agent this rule fires on. -/
  leftSymbol : Nat
  /-- Symbol of the right (principal) agent this rule fires on. -/
  rightSymbol : Nat
  /-- The replacement net fragment. -/
  rhs : List lfnAgent

/-- A finite **rule table** carried as data. -/
abbrev lfnRuleTable := List lfnInteractionRule

/-! ## Hand-rolled append + expansion (position-preserving reduction) -/

/-- Own append on nets (avoids `List.append`, whose lemmas leak `propext` here). -/
def lfnCat : List lfnAgent → List lfnAgent → List lfnAgent
  | [], ys => ys
  | x :: xs, ys => x :: lfnCat xs ys

/-- Right identity of `lfnCat`. -/
theorem lfnCatNil (xs : List lfnAgent) : lfnCat xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => show x :: lfnCat xs [] = x :: xs; rw [ih]

/-- Associativity of `lfnCat`. -/
theorem lfnCatAssoc (xs ys zs : List lfnAgent) :
    lfnCat (lfnCat xs ys) zs = lfnCat xs (lfnCat ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => show x :: lfnCat (lfnCat xs ys) zs = x :: lfnCat xs (lfnCat ys zs); rw [ih]

/-- The per-agent firing action of a redex `(leftId, rightId)` with replacement: the principal (left)
agent expands to the replacement, the partner (right) agent expands to nothing, everything else is kept.
Because expansion happens IN PLACE (position-preserving), disjoint firings commute literally. -/
def lfnAgentAction (leftId rightId : Nat) (replacement : List lfnAgent) (ag : lfnAgent) :
    List lfnAgent :=
  if ag.agentId = leftId then replacement
  else if ag.agentId = rightId then [] else [ag]

/-- Characterization of `lfnAgentAction` at the left (principal) agent. -/
theorem lfnAgentActionAtLeft (leftId rightId : Nat) (replacement : List lfnAgent) {ag : lfnAgent}
    (h : ag.agentId = leftId) : lfnAgentAction leftId rightId replacement ag = replacement := by
  unfold lfnAgentAction; rw [if_pos h]

/-- Characterization of `lfnAgentAction` at the right (partner) agent. -/
theorem lfnAgentActionAtRight (leftId rightId : Nat) (replacement : List lfnAgent) {ag : lfnAgent}
    (h1 : ag.agentId ≠ leftId) (h2 : ag.agentId = rightId) :
    lfnAgentAction leftId rightId replacement ag = [] := by
  unfold lfnAgentAction; rw [if_neg h1, if_pos h2]

/-- Characterization of `lfnAgentAction` away from both endpoints (agent untouched). -/
theorem lfnAgentActionAtOther (leftId rightId : Nat) (replacement : List lfnAgent) {ag : lfnAgent}
    (h1 : ag.agentId ≠ leftId) (h2 : ag.agentId ≠ rightId) :
    lfnAgentAction leftId rightId replacement ag = [ag] := by
  unfold lfnAgentAction; rw [if_neg h1, if_neg h2]

/-- Expand a per-agent action over a whole net (position-preserving `flatMap`). -/
def lfnNetExpand (act : lfnAgent → List lfnAgent) : List lfnAgent → List lfnAgent
  | [] => []
  | ag :: rest => lfnCat (act ag) (lfnNetExpand act rest)

/-- Expanding a singleton yields exactly the action's output. -/
theorem lfnNetExpandSingleton (act : lfnAgent → List lfnAgent) (ag : lfnAgent) :
    lfnNetExpand act [ag] = act ag := by
  show lfnCat (act ag) (lfnNetExpand act []) = act ag
  show lfnCat (act ag) [] = act ag
  exact lfnCatNil (act ag)

/-- `lfnNetExpand` distributes over `lfnCat` (the fusion law). -/
theorem lfnNetExpandCat (act : lfnAgent → List lfnAgent) :
    ∀ (xs ys : List lfnAgent),
      lfnNetExpand act (lfnCat xs ys) = lfnCat (lfnNetExpand act xs) (lfnNetExpand act ys)
  | [], _ => rfl
  | ag :: xs, ys => by
    show lfnCat (act ag) (lfnNetExpand act (lfnCat xs ys))
       = lfnCat (lfnCat (act ag) (lfnNetExpand act xs)) (lfnNetExpand act ys)
    rw [lfnNetExpandCat act xs ys, lfnCatAssoc]

/-! ## Rule lookup + reduction step (T1) -/

/-- Look up the agent with a given id (first match). -/
def lfnFindAgent : List lfnAgent → Nat → Option lfnAgent
  | [], _ => none
  | ag :: rest, target => if ag.agentId = target then some ag else lfnFindAgent rest target

/-- Look up the rule for an ordered symbol pair. -/
def lfnLookupRule : lfnRuleTable → Nat → Nat → Option lfnInteractionRule
  | [], _, _ => none
  | rule :: rest, leftSym, rightSym =>
      if rule.leftSymbol = leftSym ∧ rule.rightSymbol = rightSym then some rule
      else lfnLookupRule rest leftSym rightSym

/-- Fire a redex whose replacement is already RESOLVED: replace the pair `(leftId, rightId)` by
`replacement` (at the principal agent's position) and empty (at the partner's position). -/
def lfnFireResolved (leftId rightId : Nat) (replacement net : List lfnAgent) : List lfnAgent :=
  lfnNetExpand (lfnAgentAction leftId rightId replacement) net

/-- Fire a redex at an active pair: look the two agents up, look their rule up, and expand. -/
def lfnFireRedex (table : lfnRuleTable) (net : List lfnAgent) (leftId rightId : Nat) :
    List lfnAgent :=
  match lfnFindAgent net leftId with
  | none => net
  | some agLeft =>
    match lfnFindAgent net rightId with
    | none => net
    | some agRight =>
      match lfnLookupRule table agLeft.symbol agRight.symbol with
      | none => net
      | some rule => lfnFireResolved leftId rightId rule.rhs net

/-! ## Active pairs and the orthogonality dividend (T2) -/

/-- Does the agent named `queryId` exist and have its principal port pointing at `targetId`? -/
def lfnAgentPointsTo : List lfnAgent → Nat → Nat → Bool
  | [], _, _ => false
  | ag :: rest, queryId, targetId =>
      if ag.agentId = queryId then (if ag.principalTarget = targetId then true else false)
      else lfnAgentPointsTo rest queryId targetId

/-- An **active pair**: `leftId` and `rightId` are distinct agents wired principal-to-principal (each
principal port points at the other). -/
def lfnIsActivePair (net : List lfnAgent) (leftId rightId : Nat) : Bool :=
  lfnAgentPointsTo net leftId rightId
    && lfnAgentPointsTo net rightId leftId
    && (if leftId = rightId then false else true)

/-- The **reduction relation**: `net` steps to `next` when some active pair fires. -/
def lfnNetStep (table : lfnRuleTable) (net next : List lfnAgent) : Prop :=
  ∃ leftId rightId,
    lfnIsActivePair net leftId rightId = true ∧ lfnFireRedex table net leftId rightId = next

/-- ★ **Single principal port ⇒ unique partner.**  An agent's principal port determines its partner, so
`lfnAgentPointsTo net queryId _` is a FUNCTION of the agent: it cannot point at two different targets. -/
theorem lfnAgentPointsToFunctional :
    ∀ (net : List lfnAgent) (queryId firstTarget secondTarget : Nat),
      lfnAgentPointsTo net queryId firstTarget = true →
      lfnAgentPointsTo net queryId secondTarget = true →
      firstTarget = secondTarget
  | [], _, _, _, hx, _ => Bool.noConfusion hx
  | ag :: rest, queryId, firstTarget, secondTarget, hx, hy => by
    change (if ag.agentId = queryId then (if ag.principalTarget = firstTarget then true else false)
              else lfnAgentPointsTo rest queryId firstTarget) = true at hx
    change (if ag.agentId = queryId then (if ag.principalTarget = secondTarget then true else false)
              else lfnAgentPointsTo rest queryId secondTarget) = true at hy
    cases hdec : Nat.decEq ag.agentId queryId with
    | isTrue hEq =>
      rw [if_pos hEq] at hx hy
      exact (lfnIfEqTrue hx).symm.trans (lfnIfEqTrue hy)
    | isFalse hNe =>
      rw [if_neg hNe] at hx hy
      exact lfnAgentPointsToFunctional rest queryId firstTarget secondTarget hx hy

/-- Extract the left-to-right principal link of an active pair. -/
theorem lfnIsActivePairPointsLR (net : List lfnAgent) (leftId rightId : Nat)
    (h : lfnIsActivePair net leftId rightId = true) : lfnAgentPointsTo net leftId rightId = true :=
  lfnBandTrueLeft (lfnBandTrueLeft h)

/-- Extract the right-to-left principal link of an active pair. -/
theorem lfnIsActivePairPointsRL (net : List lfnAgent) (leftId rightId : Nat)
    (h : lfnIsActivePair net leftId rightId = true) : lfnAgentPointsTo net rightId leftId = true :=
  lfnBandTrueRight (lfnBandTrueLeft h)

/-- ★ **The orthogonality core: the active-pair partner is UNIQUE.**  If `aId` is in an active pair with
`bId` and also with `cId`, then `bId = cId`.  The single-principal-port law: no agent is the principal of
two active pairs. -/
theorem lfnActivePairPartnerUnique (net : List lfnAgent) (aId bId cId : Nat)
    (h1 : lfnIsActivePair net aId bId = true) (h2 : lfnIsActivePair net aId cId = true) :
    bId = cId :=
  lfnAgentPointsToFunctional net aId bId cId
    (lfnIsActivePairPointsLR net aId bId h1) (lfnIsActivePairPointsLR net aId cId h2)

/-- ★ **Distinct active pairs are DISJOINT (no critical pairs).**  If two active pairs share an agent
then they are the SAME pair (equal, possibly with the two orientations swapped).  Contrapositive: any two
truly-distinct active pairs share no agent — the interaction-net orthogonality property. -/
theorem lfnActivePairsShareImpliesEqual (net : List lfnAgent) (aId bId cId dId : Nat)
    (h1 : lfnIsActivePair net aId bId = true) (h2 : lfnIsActivePair net cId dId = true)
    (hshare : aId = cId ∨ aId = dId ∨ bId = cId ∨ bId = dId) :
    (aId = cId ∧ bId = dId) ∨ (aId = dId ∧ bId = cId) := by
  rcases hshare with hac | had | hbc | hbd
  · rw [← hac] at h2
    exact Or.inl ⟨hac, lfnActivePairPartnerUnique net aId bId dId h1 h2⟩
  · rw [← had] at h2
    have hbc : bId = cId :=
      lfnAgentPointsToFunctional net aId bId cId
        (lfnIsActivePairPointsLR net aId bId h1) (lfnIsActivePairPointsRL net cId aId h2)
    exact Or.inr ⟨had, hbc⟩
  · rw [← hbc] at h2
    have had : aId = dId :=
      lfnAgentPointsToFunctional net bId aId dId
        (lfnIsActivePairPointsRL net aId bId h1) (lfnIsActivePairPointsLR net bId dId h2)
    exact Or.inr ⟨had, hbc⟩
  · rw [← hbd] at h2
    have hac : aId = cId :=
      lfnAgentPointsToFunctional net bId aId cId
        (lfnIsActivePairPointsRL net aId bId h1) (lfnIsActivePairPointsRL net cId bId h2)
    exact Or.inl ⟨hac, hbd⟩

/-! ## Strong confluence for free: disjoint-redex commutation (T3) -/

/-- The replacement ids of a redex avoid the two consumed ids of the OTHER redex (the freshness /
disjoint-support condition that makes the two firings genuinely independent). -/
def lfnNetAvoids (leftId rightId : Nat) : List lfnAgent → Prop
  | [] => True
  | ag :: rest => ag.agentId ≠ leftId ∧ ag.agentId ≠ rightId ∧ lfnNetAvoids leftId rightId rest

/-- A firing is the identity on a fragment whose ids avoid its two consumed ids. -/
theorem lfnNetExpandIdOfAvoids (leftId rightId : Nat) (replacement : List lfnAgent) :
    ∀ (xs : List lfnAgent), lfnNetAvoids leftId rightId xs →
      lfnNetExpand (lfnAgentAction leftId rightId replacement) xs = xs
  | [], _ => rfl
  | ag :: rest, h => by
    obtain ⟨hL, hR, hrest⟩ := h
    show lfnCat (lfnAgentAction leftId rightId replacement ag)
          (lfnNetExpand (lfnAgentAction leftId rightId replacement) rest) = ag :: rest
    rw [lfnAgentActionAtOther leftId rightId replacement hL hR,
        lfnNetExpandIdOfAvoids leftId rightId replacement rest hrest]
    rfl

/-- The per-agent commutation: firing redex `(cId,dId)` after redex `(aId,bId)` on a single agent equals
firing them in the other order, given the four ids are disjoint and each replacement is fresh w.r.t. the
other redex.  This is where the single-principal-port disjointness cashes out. -/
theorem lfnAgentActionCommute (aId bId cId dId : Nat) (replA replC : List lfnAgent)
    (hac : aId ≠ cId) (had : aId ≠ dId) (hbc : bId ≠ cId) (hbd : bId ≠ dId)
    (hA : lfnNetAvoids cId dId replA) (hC : lfnNetAvoids aId bId replC) (ag : lfnAgent) :
    lfnNetExpand (lfnAgentAction cId dId replC) (lfnAgentAction aId bId replA ag)
      = lfnNetExpand (lfnAgentAction aId bId replA) (lfnAgentAction cId dId replC ag) := by
  cases hda : Nat.decEq ag.agentId aId with
  | isTrue hEa =>
    have hnc : ag.agentId ≠ cId := fun h => hac (hEa ▸ h)
    have hnd : ag.agentId ≠ dId := fun h => had (hEa ▸ h)
    rw [lfnAgentActionAtLeft aId bId replA hEa,
        lfnAgentActionAtOther cId dId replC hnc hnd,
        lfnNetExpandSingleton (lfnAgentAction aId bId replA) ag,
        lfnAgentActionAtLeft aId bId replA hEa,
        lfnNetExpandIdOfAvoids cId dId replC replA hA]
  | isFalse hEa =>
    cases hdb : Nat.decEq ag.agentId bId with
    | isTrue hEb =>
      have hnc : ag.agentId ≠ cId := fun h => hbc (hEb ▸ h)
      have hnd : ag.agentId ≠ dId := fun h => hbd (hEb ▸ h)
      rw [lfnAgentActionAtRight aId bId replA hEa hEb,
          lfnAgentActionAtOther cId dId replC hnc hnd,
          lfnNetExpandSingleton (lfnAgentAction aId bId replA) ag,
          lfnAgentActionAtRight aId bId replA hEa hEb]
      rfl
    | isFalse hEb =>
      cases hdc : Nat.decEq ag.agentId cId with
      | isTrue hEc =>
        rw [lfnAgentActionAtOther aId bId replA hEa hEb,
            lfnAgentActionAtLeft cId dId replC hEc,
            lfnNetExpandSingleton (lfnAgentAction cId dId replC) ag,
            lfnAgentActionAtLeft cId dId replC hEc,
            lfnNetExpandIdOfAvoids aId bId replA replC hC]
      | isFalse hEc =>
        cases hdd : Nat.decEq ag.agentId dId with
        | isTrue hEd =>
          rw [lfnAgentActionAtOther aId bId replA hEa hEb,
              lfnAgentActionAtRight cId dId replC hEc hEd,
              lfnNetExpandSingleton (lfnAgentAction cId dId replC) ag,
              lfnAgentActionAtRight cId dId replC hEc hEd]
          rfl
        | isFalse hEd =>
          rw [lfnAgentActionAtOther aId bId replA hEa hEb,
              lfnAgentActionAtOther cId dId replC hEc hEd,
              lfnNetExpandSingleton (lfnAgentAction cId dId replC) ag,
              lfnNetExpandSingleton (lfnAgentAction aId bId replA) ag,
              lfnAgentActionAtOther aId bId replA hEa hEb,
              lfnAgentActionAtOther cId dId replC hEc hEd]

/-- ★ **Disjoint firings commute on a whole net** (the netExpand-level engine).  By induction on the net,
using the fusion law and the per-agent commutation. -/
theorem lfnNetExpandCommute (aId bId cId dId : Nat) (replA replC : List lfnAgent)
    (hac : aId ≠ cId) (had : aId ≠ dId) (hbc : bId ≠ cId) (hbd : bId ≠ dId)
    (hA : lfnNetAvoids cId dId replA) (hC : lfnNetAvoids aId bId replC) :
    ∀ (net : List lfnAgent),
      lfnNetExpand (lfnAgentAction cId dId replC)
          (lfnNetExpand (lfnAgentAction aId bId replA) net)
        = lfnNetExpand (lfnAgentAction aId bId replA)
          (lfnNetExpand (lfnAgentAction cId dId replC) net)
  | [] => rfl
  | ag :: rest => by
    show lfnNetExpand (lfnAgentAction cId dId replC)
          (lfnCat (lfnAgentAction aId bId replA ag)
            (lfnNetExpand (lfnAgentAction aId bId replA) rest))
       = lfnNetExpand (lfnAgentAction aId bId replA)
          (lfnCat (lfnAgentAction cId dId replC ag)
            (lfnNetExpand (lfnAgentAction cId dId replC) rest))
    rw [lfnNetExpandCat, lfnNetExpandCat,
        lfnNetExpandCommute aId bId cId dId replA replC hac had hbc hbd hA hC rest,
        lfnAgentActionCommute aId bId cId dId replA replC hac had hbc hbd hA hC ag]

/-- ★ **Strong confluence for free (the one-step diamond).**  Two DISJOINT resolved firings out of a
common net reach a COMMON APEX regardless of order — `fireResolved r₂ ∘ fireResolved r₁ =
fireResolved r₁ ∘ fireResolved r₂`.  This is the orthogonality dividend: no critical pairs (each agent has
one principal port) ⇒ the local peak of two distinct redexes is filled by firing the OTHER redex, which
is undisturbed.  Proved as a literal, position-preserving list equality — no graph isomorphism, no
`WellFounded.fix`. -/
theorem lfnDisjointRedexCommute (aId bId cId dId : Nat) (replA replC net : List lfnAgent)
    (hac : aId ≠ cId) (had : aId ≠ dId) (hbc : bId ≠ cId) (hbd : bId ≠ dId)
    (hA : lfnNetAvoids cId dId replA) (hC : lfnNetAvoids aId bId replC) :
    lfnFireResolved cId dId replC (lfnFireResolved aId bId replA net)
      = lfnFireResolved aId bId replA (lfnFireResolved cId dId replC net) :=
  lfnNetExpandCommute aId bId cId dId replA replC hac had hbc hbd hA hC net

/-! ## Honest wall: the fully-general graph-net diamond -/

/-- **Wall marker.**  The disjoint-redex commutation above lands the diamond for the BOUNDED, list-based
net where redexes are named by stable `agentId` and disjointness is a structural fact.  The fully-general
GRAPH-net one-step diamond — nets equal only up to renaming of internal wire nodes, so the apex is
well-defined only up to graph ISOMORPHISM, and firing must FRESHLY allocate the replacement's internal
wires — is NOT proven here.  It rides exactly the state-parametric union-find fresh-allocation independence
residual that is walled at `fxBrauer_hasWiringDescDisjointWindowFreshProof := false`
(`WiringDescGodement`) and `arcWholeCellCommute_blockCommute_stays_false`
(`ArcWholeCellDisjointSupportCommute`): general fresh-node allocation / graph iso is not available
zero-axiom.  The list-net scoping sidesteps it by making replacement ids explicit data with a freshness
hypothesis (`lfnNetAvoids`). -/
def lfnHasGeneralGraphDiamond : Bool := false

/-! ## Concrete fires (T4) -/

/-- A left (principal) agent of symbol `1` pointing at agent `2`. -/
def lfnDemoAgentA : lfnAgent := { agentId := 1, symbol := 1, principalTarget := 2, auxPorts := [] }
/-- A right (principal) agent of symbol `2` pointing back at agent `1`. -/
def lfnDemoAgentB : lfnAgent := { agentId := 2, symbol := 2, principalTarget := 1, auxPorts := [] }
/-- The rule RHS agent produced by the `(1,2)` interaction. -/
def lfnDemoResult : lfnAgent := { agentId := 9, symbol := 3, principalTarget := 9, auxPorts := [] }
/-- The `(1,2) → [result]` rule. -/
def lfnDemoRule : lfnInteractionRule := { leftSymbol := 1, rightSymbol := 2, rhs := [lfnDemoResult] }
/-- A one-rule table. -/
def lfnDemoTable : lfnRuleTable := [lfnDemoRule]
/-- The active-pair net `[A, B]`. -/
def lfnDemoNet : List lfnAgent := [lfnDemoAgentA, lfnDemoAgentB]

/-- ★ **Fire 1: a concrete 2-symbol interaction fires** — the `(1,2)` active pair produces the rule RHS. -/
theorem lfnFireExample : lfnFireRedex lfnDemoTable lfnDemoNet 1 2 = [lfnDemoResult] := rfl

/-- The annihilation rule `(1,2) → []`. -/
def lfnDemoAnnih : lfnInteractionRule := { leftSymbol := 1, rightSymbol := 2, rhs := [] }
/-- An annihilation table. -/
def lfnDemoTable2 : lfnRuleTable := [lfnDemoAnnih]
/-- First active pair, principal `3` ↔ `4`. -/
def lfnPairOneA : lfnAgent := { agentId := 3, symbol := 1, principalTarget := 4, auxPorts := [] }
/-- First active pair, partner. -/
def lfnPairOneB : lfnAgent := { agentId := 4, symbol := 2, principalTarget := 3, auxPorts := [] }
/-- A spectator agent in no active pair. -/
def lfnSpectator : lfnAgent := { agentId := 5, symbol := 8, principalTarget := 8, auxPorts := [] }
/-- Second active pair, principal `6` ↔ `7`. -/
def lfnPairTwoA : lfnAgent := { agentId := 6, symbol := 1, principalTarget := 7, auxPorts := [] }
/-- Second active pair, partner. -/
def lfnPairTwoB : lfnAgent := { agentId := 7, symbol := 2, principalTarget := 6, auxPorts := [] }
/-- A net with TWO disjoint active pairs and a spectator between them. -/
def lfnTwoRedexNet : List lfnAgent :=
  [lfnPairOneA, lfnPairOneB, lfnSpectator, lfnPairTwoA, lfnPairTwoB]

/-- ★ **Fire 2: two disjoint redexes COMMUTE** — firing `(3,4)` then `(6,7)` equals firing `(6,7)` then
`(3,4)`, pinned by `rfl` on a concrete net (the spectator survives both orders). -/
theorem lfnCommuteExample :
    lfnFireRedex lfnDemoTable2 (lfnFireRedex lfnDemoTable2 lfnTwoRedexNet 3 4) 6 7
      = lfnFireRedex lfnDemoTable2 (lfnFireRedex lfnDemoTable2 lfnTwoRedexNet 6 7) 3 4 := rfl

/-- ★ **Fire 3 (control): two agents NOT wired principal-to-principal is NOT an active pair.**  Here agent
`1` points at `9`, not at `2`. -/
def lfnControlAgentA : lfnAgent := { agentId := 1, symbol := 1, principalTarget := 9, auxPorts := [] }
/-- Its would-be partner, correctly pointing back. -/
def lfnControlAgentB : lfnAgent := { agentId := 2, symbol := 2, principalTarget := 1, auxPorts := [] }
/-- The non-active control net. -/
def lfnControlNet : List lfnAgent := [lfnControlAgentA, lfnControlAgentB]

/-- ★ The control: `(1,2)` is not an active pair (principal ports don't mutually point). -/
theorem lfnControlNotActive : lfnIsActivePair lfnControlNet 1 2 = false := rfl

/-- A positive check that the two-redex net's first pair genuinely IS an active pair. -/
theorem lfnActiveExample : lfnIsActivePair lfnTwoRedexNet 3 4 = true := rfl

end FX1Poly.Polygraph
