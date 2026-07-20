import FX1Poly.ComputerAlgebra.Semigroup.CommWordProblem
import FX1Poly.ComputerAlgebra.Order.AlmostFull

/-! # FX1Poly/Polygraph/Net/PrimeEventStructure — prime event structures (NET-14)

A **prime event structure** is a set of events carrying a causal partial order and a
symmetric irreflexive conflict relation (with conflict inherited along causation).  A
**configuration** is a *conflict-free, down-closed* set of events — a consistent state of
the process the structure describes.  The finite decidable core of NET-14 is here:

## What is DECIDED (zero-axiom)

* **T1 — the carrier.**  `EventStructure` (events + `causalPairs` + `conflictPairs`), the
  symmetric conflict lookup `evsInConflict`, the structural fuel-bounded transitive-closure
  reachability `evsCausesLe` (fuel = event count, no `WellFounded.fix`), and the
  well-formedness Boolean `evsWellFormed` (symmetric + irreflexive + conflict-inheritance).

* **T2 — configuration validity.**  `evsIsConflictFree` (structural pairwise fold),
  `evsIsDownClosed` (every stored causal predecessor of a member is a member), and their
  `evsBoth`-conjunction `evsIsConfiguration`.  Decided `true` on a genuine configuration,
  `false` on a conflicting set and on a non-down-closed set.

* **T3 — covering + equality + soundness.**  `evsConfigEq` compares configurations up to
  reordering via the reused `cswSort` normal form (`evsConfigEqSound` from
  `cswListNatBeqEq`).  `evsEnabled` / `evsExtendsBy` / `evsCovers` describe single-event
  extension.  The keystone `evsExtendPreservesConfig` proves — structurally, zero-axiom —
  that extending a configuration by an *enabled* event yields a configuration; `evsCovers`
  soundness (`evsCoversSound`) is the fold-level corollary producing the witnessing event.

## What is WALLED

* **The Winskel unfolding.**  Safe Petri nets correspond to prime event structures via the
  *unfolding*, an infinite construction with no finite normal form for an unbounded net.
  The compositional/coverability side is the same Karp–Miller / Dickson WQO wall already
  certified in this repo.  `evsHasPetriUnfolding = false`, tied definitionally to
  `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false`.

* **Infinite-domain completeness.**  Configurations of an *infinite* event structure form a
  prime algebraic coherent domain; recovering a PES from such a domain needs directed
  suprema / an omega-colimit — a limit object outside the finite-Boolean fragment.
  `evsHasInfiniteDomainCompleteness = false`.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`.  All `Nat`/list order facts are the
hand-rolled structural `csw` kit or local structural recursions; no leak-prone library
order/append lemma is used. -/

namespace FX1Poly.Polygraph.Net

open FX1Poly.ComputerAlgebra (cswSort cswListNatBeq cswListNatBeqEq)

/-! ## Boolean micro-kit (structural, propext-clean) — `cond`-based conjunction and negation -/

/-- `cond`-based Boolean conjunction (avoids the `&&` match-compiler path). -/
def evsBoth (leftFlag rightFlag : Bool) : Bool := cond leftFlag rightFlag false

/-- `cond` on a `true` scrutinee. -/
theorem evsCondTrue {carrier : Type} (whenTrue whenFalse : carrier) :
    cond true whenTrue whenFalse = whenTrue := rfl

/-- `cond` on a `false` scrutinee. -/
theorem evsCondFalse {carrier : Type} (whenTrue whenFalse : carrier) :
    cond false whenTrue whenFalse = whenFalse := rfl

/-- Introduce a `true` conjunction from its two `true` halves. -/
theorem evsBothIntro (leftFlag rightFlag : Bool)
    (hLeft : leftFlag = true) (hRight : rightFlag = true) : evsBoth leftFlag rightFlag = true := by
  rw [hLeft, hRight]; rfl

/-- Eliminate a `true` conjunction into its two `true` halves. -/
theorem evsBothElim : (leftFlag rightFlag : Bool) → evsBoth leftFlag rightFlag = true →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, hBoth => Bool.noConfusion hBoth
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Boolean negation as a `cond` (no `!` / `Bool.not` match). -/
def evsNegate (flag : Bool) : Bool := cond flag false true

/-! ## Cons-only list utilities over `Nat` id lists -/

/-- Length of a `List Nat` (cons-only). -/
def evsLength : List Nat → Nat
  | [] => 0
  | _ :: rest => Nat.succ (evsLength rest)

/-- Append of two `List Nat` (cons-only, no `List.append`). -/
def evsAppend : List Nat → List Nat → List Nat
  | [], suffix => suffix
  | head :: rest, suffix => head :: evsAppend rest suffix

/-- Membership as a `Bool` (cons-only, no `List.elem`). -/
def evsMemBool (target : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => cond (Nat.beq target head) true (evsMemBool target rest)

/-- If a head matches, the id is a member. -/
theorem evsMemConsSelf (target head : Nat) (rest : List Nat)
    (hBeq : Nat.beq target head = true) : evsMemBool target (head :: rest) = true := by
  show cond (Nat.beq target head) true (evsMemBool target rest) = true
  rw [hBeq]; rfl

/-- Membership is monotone under prepending a new head. -/
theorem evsMemConsMono (target head : Nat) (rest : List Nat)
    (hMem : evsMemBool target rest = true) : evsMemBool target (head :: rest) = true := by
  show cond (Nat.beq target head) true (evsMemBool target rest) = true
  rw [hMem]
  cases Nat.beq target head <;> rfl

/-! ## The carrier — events, causal pairs, conflict pairs -/

/-- A prime event structure: a list of event ids, a list of causal pairs
`(predecessor, successor)` (read as `predecessor ≤ successor`), and a list of conflict pairs
(intended symmetric).  Configurations are plain `List Nat` event sets over `events`. -/
structure EventStructure where
  events : List Nat
  causalPairs : List (Nat × Nat)
  conflictPairs : List (Nat × Nat)

/-! ## Conflict — the symmetric lookup -/

/-- Boolean membership of an ordered pair in a pair list (cons-only). -/
def evsPairMemBool (first second : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (leftEntry, rightEntry) :: rest =>
      cond (evsBoth (Nat.beq leftEntry first) (Nat.beq rightEntry second)) true
        (evsPairMemBool first second rest)

/-- Two events are in conflict when the stored pair occurs in *either* order (the query is
symmetric regardless of how the pair list was written). -/
def evsInConflict (eventStructure : EventStructure) (first second : Nat) : Bool :=
  cond (evsPairMemBool first second eventStructure.conflictPairs) true
    (evsPairMemBool second first eventStructure.conflictPairs)

/-! ## Causal reachability — structural fuel transitive closure (fuel = event count) -/

/-- The direct successors of `node` along the causal edges (cons-only). -/
def evsSuccsOf (node : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (predecessor, successor) :: rest =>
      cond (Nat.beq predecessor node) (successor :: evsSuccsOf node rest) (evsSuccsOf node rest)

/-- Collect the direct successors of every node in a frontier (cons-only). -/
def evsExpandAll (edges : List (Nat × Nat)) : List Nat → List Nat
  | [] => []
  | node :: rest => evsAppend (evsSuccsOf node edges) (evsExpandAll edges rest)

/-- Fuel-bounded reachable-set saturation: each round appends the successors of the current
frontier.  Structural recursion on `fuel` (no `WellFounded.fix`). -/
def evsReachSet (edges : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, frontier => frontier
  | Nat.succ fuel, frontier =>
      evsReachSet edges fuel (evsAppend frontier (evsExpandAll edges frontier))

/-- `evsCausesLe source goal` decides `source ≤ goal` in the causal order: `goal` is reached
from `{source}` within `evsLength events` saturation rounds (reflexive because `source` is in
the initial frontier). -/
def evsCausesLe (eventStructure : EventStructure) (source goal : Nat) : Bool :=
  evsMemBool goal
    (evsReachSet eventStructure.causalPairs (evsLength eventStructure.events) (source :: []))

/-! ## Well-formedness — symmetric + irreflexive + conflict inheritance -/

/-- Every stored conflict pair is queryable in the swapped order. -/
def evsSymmetricFold (eventStructure : EventStructure) : List (Nat × Nat) → Bool
  | [] => true
  | (first, second) :: rest =>
      evsBoth (evsInConflict eventStructure second first) (evsSymmetricFold eventStructure rest)

/-- No event conflicts with itself. -/
def evsIrreflexiveFold (eventStructure : EventStructure) : List Nat → Bool
  | [] => true
  | event :: rest =>
      evsBoth (evsNegate (evsInConflict eventStructure event event))
        (evsIrreflexiveFold eventStructure rest)

/-- For a fixed conflicting pair `(first, second)`, inheritance along every causal edge out
of `second`: whenever `second ≤ successor` we require `first` in conflict with `successor`. -/
def evsInheritOverEdges (eventStructure : EventStructure) (first second : Nat) :
    List (Nat × Nat) → Bool
  | [] => true
  | (predecessor, successor) :: rest =>
      evsBoth (cond (Nat.beq predecessor second) (evsInConflict eventStructure first successor) true)
        (evsInheritOverEdges eventStructure first second rest)

/-- Conflict inheritance over all stored conflict pairs. -/
def evsInheritFold (eventStructure : EventStructure) : List (Nat × Nat) → Bool
  | [] => true
  | (first, second) :: rest =>
      evsBoth (evsInheritOverEdges eventStructure first second eventStructure.causalPairs)
        (evsInheritFold eventStructure rest)

/-- The structure is well-formed: conflict symmetric, irreflexive, and inherited along
causation. -/
def evsWellFormed (eventStructure : EventStructure) : Bool :=
  evsBoth (evsSymmetricFold eventStructure eventStructure.conflictPairs)
    (evsBoth (evsIrreflexiveFold eventStructure eventStructure.events)
      (evsInheritFold eventStructure eventStructure.conflictPairs))

/-! ## Configuration validity — conflict-free + down-closed -/

/-- One event is conflict-free with an entire event list. -/
def evsNoConflictWith (eventStructure : EventStructure) (event : Nat) : List Nat → Bool
  | [] => true
  | head :: rest =>
      evsBoth (evsNegate (evsInConflict eventStructure event head))
        (evsNoConflictWith eventStructure event rest)

/-- A configuration is conflict-free: every unordered pair of its members is non-conflicting. -/
def evsIsConflictFree (eventStructure : EventStructure) : List Nat → Bool
  | [] => true
  | head :: rest =>
      evsBoth (evsNoConflictWith eventStructure head rest) (evsIsConflictFree eventStructure rest)

/-- For each causal edge `(predecessor, successor)`: if `successor` is in `config` then
`predecessor` must be too (else vacuously satisfied). -/
def evsDownClosedFold (config : List Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (predecessor, successor) :: rest =>
      evsBoth (cond (evsMemBool successor config) (evsMemBool predecessor config) true)
        (evsDownClosedFold config rest)

/-- A configuration is down-closed under the stored causal order. -/
def evsIsDownClosed (eventStructure : EventStructure) (config : List Nat) : Bool :=
  evsDownClosedFold config eventStructure.causalPairs

/-- A configuration: conflict-free and down-closed (`evsBoth`-conjunction, not `&&`). -/
def evsIsConfiguration (eventStructure : EventStructure) (config : List Nat) : Bool :=
  evsBoth (evsIsConflictFree eventStructure config) (evsIsDownClosed eventStructure config)

/-! ## Enabling, covering, and configuration equality -/

/-- For each causal edge into `newEvent`, its predecessor must already be in `config`. -/
def evsPredsInFold (newEvent : Nat) (config : List Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (predecessor, successor) :: rest =>
      evsBoth (cond (Nat.beq successor newEvent) (evsMemBool predecessor config) true)
        (evsPredsInFold newEvent config rest)

/-- Every direct causal predecessor of `newEvent` is present in `config`. -/
def evsPredecessorsIn (eventStructure : EventStructure) (config : List Nat) (newEvent : Nat) : Bool :=
  evsPredsInFold newEvent config eventStructure.causalPairs

/-- `newEvent` is enabled at `config`: its predecessors are all in `config`, it is
conflict-free with `config`, and it is not already a member. -/
def evsEnabled (eventStructure : EventStructure) (config : List Nat) (newEvent : Nat) : Bool :=
  evsBoth (evsPredecessorsIn eventStructure config newEvent)
    (evsBoth (evsNoConflictWith eventStructure newEvent config)
      (evsNegate (evsMemBool newEvent config)))

/-- Equality of configurations up to reordering, via the reused `cswSort` normal form. -/
def evsConfigEq (left right : List Nat) : Bool := cswListNatBeq (cswSort left) (cswSort right)

/-- `later` covers `earlier` by `newEvent`: the event is enabled and `later` equals
`newEvent :: earlier` up to reordering. -/
def evsExtendsBy (eventStructure : EventStructure) (earlier later : List Nat) (newEvent : Nat) :
    Bool :=
  evsBoth (evsEnabled eventStructure earlier newEvent)
    (evsConfigEq later (newEvent :: earlier))

/-- Fold: some event of the list witnesses a cover of `earlier` by `later`. -/
def evsCoversFold (eventStructure : EventStructure) (earlier later : List Nat) :
    List Nat → Bool
  | [] => false
  | event :: rest =>
      cond (evsExtendsBy eventStructure earlier later event) true
        (evsCoversFold eventStructure earlier later rest)

/-- The covering relation: `later` covers `earlier` when some event of the structure
witnesses a single-event extension. -/
def evsCovers (eventStructure : EventStructure) (earlier later : List Nat) : Bool :=
  evsCoversFold eventStructure earlier later eventStructure.events

/-! ## Soundness — validity preserved under single-event extension -/

/-- The down-closure fold survives prepending an enabled `newEvent`.  Every stored causal
edge stays satisfied: successors already in `config` keep their (unchanged) predecessors,
and edges into `newEvent` have their predecessor supplied by `evsPredsInFold`. -/
theorem evsDownClosedFoldExtend (newEvent : Nat) (config : List Nat) :
    (edges : List (Nat × Nat)) →
    evsDownClosedFold config edges = true →
    evsPredsInFold newEvent config edges = true →
    evsDownClosedFold (newEvent :: config) edges = true
  | [], _, _ => rfl
  | (predecessor, successor) :: rest, hDown, hPreds => by
      have hDownSplit := evsBothElim _ _ hDown
      have hPredsSplit := evsBothElim _ _ hPreds
      apply evsBothIntro
      · cases hSucc : Nat.beq successor newEvent with
        | true =>
            have hPredMem : evsMemBool predecessor config = true := by
              have hHead := hPredsSplit.left
              rw [hSucc, evsCondTrue] at hHead
              exact hHead
            have hPredMemExt : evsMemBool predecessor (newEvent :: config) = true :=
              evsMemConsMono predecessor newEvent config hPredMem
            have hSuccMemExt : evsMemBool successor (newEvent :: config) = true := by
              show cond (Nat.beq successor newEvent) true (evsMemBool successor config) = true
              rw [hSucc, evsCondTrue]
            show cond (evsMemBool successor (newEvent :: config))
                (evsMemBool predecessor (newEvent :: config)) true = true
            rw [hSuccMemExt, evsCondTrue, hPredMemExt]
        | false =>
            have hSuccEq : evsMemBool successor (newEvent :: config) = evsMemBool successor config := by
              show cond (Nat.beq successor newEvent) true (evsMemBool successor config)
                  = evsMemBool successor config
              rw [hSucc, evsCondFalse]
            cases hSuccInConfig : evsMemBool successor config with
            | true =>
                have hPredMem : evsMemBool predecessor config = true := by
                  have hHead := hDownSplit.left
                  rw [hSuccInConfig, evsCondTrue] at hHead
                  exact hHead
                have hPredMemExt : evsMemBool predecessor (newEvent :: config) = true :=
                  evsMemConsMono predecessor newEvent config hPredMem
                show cond (evsMemBool successor (newEvent :: config))
                    (evsMemBool predecessor (newEvent :: config)) true = true
                rw [hSuccEq, hSuccInConfig, evsCondTrue, hPredMemExt]
            | false =>
                show cond (evsMemBool successor (newEvent :: config))
                    (evsMemBool predecessor (newEvent :: config)) true = true
                rw [hSuccEq, hSuccInConfig, evsCondFalse]
      · exact evsDownClosedFoldExtend newEvent config rest hDownSplit.right hPredsSplit.right

/-- **Keystone.**  Extending a configuration by an enabled event yields a configuration.
Conflict-freeness is preserved because the new event is conflict-free with the (already
conflict-free) configuration; down-closure is preserved by `evsDownClosedFoldExtend`. -/
theorem evsExtendPreservesConfig (eventStructure : EventStructure) (config : List Nat)
    (newEvent : Nat)
    (hConfig : evsIsConfiguration eventStructure config = true)
    (hEnabled : evsEnabled eventStructure config newEvent = true) :
    evsIsConfiguration eventStructure (newEvent :: config) = true := by
  have hConfigSplit := evsBothElim _ _ hConfig
  have hEnabledSplit := evsBothElim _ _ hEnabled
  have hNoConflictSplit := evsBothElim _ _ hEnabledSplit.right
  apply evsBothIntro
  · show evsBoth (evsNoConflictWith eventStructure newEvent config)
        (evsIsConflictFree eventStructure config) = true
    exact evsBothIntro _ _ hNoConflictSplit.left hConfigSplit.left
  · show evsDownClosedFold (newEvent :: config) eventStructure.causalPairs = true
    exact evsDownClosedFoldExtend newEvent config eventStructure.causalPairs
      hConfigSplit.right hEnabledSplit.left

/-- Extension via `evsExtendsBy`: the witnessing event, being enabled, preserves validity of
`newEvent :: earlier`. -/
theorem evsExtendsBySound (eventStructure : EventStructure) (earlier later : List Nat)
    (newEvent : Nat)
    (hExtends : evsExtendsBy eventStructure earlier later newEvent = true)
    (hConfig : evsIsConfiguration eventStructure earlier = true) :
    evsIsConfiguration eventStructure (newEvent :: earlier) = true :=
  evsExtendPreservesConfig eventStructure earlier newEvent hConfig
    (evsBothElim _ _ hExtends).left

/-- `evsConfigEq` is sound: equal-by-normal-form configurations have equal `cswSort` forms. -/
theorem evsConfigEqSound (left right : List Nat) :
    evsConfigEq left right = true → cswSort left = cswSort right :=
  cswListNatBeqEq (cswSort left) (cswSort right)

/-- Covering soundness: if `later` covers `earlier` and `earlier` is a configuration, some
event witnesses the extension and `newEvent :: earlier` is again a configuration. -/
theorem evsCoversSound (eventStructure : EventStructure) (earlier later : List Nat)
    (hConfig : evsIsConfiguration eventStructure earlier = true) :
    (events : List Nat) →
    evsCoversFold eventStructure earlier later events = true →
    ∃ witness, evsExtendsBy eventStructure earlier later witness = true
      ∧ evsIsConfiguration eventStructure (witness :: earlier) = true
  | [], hCovers => Bool.noConfusion hCovers
  | event :: rest, hCovers => by
      cases hEvent : evsExtendsBy eventStructure earlier later event with
      | true =>
          exact ⟨event, hEvent, evsExtendsBySound eventStructure earlier later event hEvent hConfig⟩
      | false =>
          have hRest : evsCoversFold eventStructure earlier later rest = true := by
            have hFull : cond (evsExtendsBy eventStructure earlier later event) true
                (evsCoversFold eventStructure earlier later rest) = true := hCovers
            rw [hEvent, evsCondFalse] at hFull
            exact hFull
          exact evsCoversSound eventStructure earlier later hConfig rest hRest

/-! ## The walls -/

/-- **WALL — the Winskel Petri-net → prime-event-structure unfolding.**

The unfolding of a safe Petri net is a (generally *infinite*) occurrence net whose events
are the finite firing histories; for an unbounded net there is no finite normal form, and
the compositional coverability that would decide reachability of markings is Karp–Miller =
the same almost-full / Dickson WQO wall already certified zero-axiom in this repo.

Burned attacks:
  * (1) *Bounded fuel truncation of the unfolding.*  Cutting the unfolding at `k` firing
    levels decides configurations only up to depth `k`; a genuine unfolding needs the
    supremum over all `k`, whose finiteness reduces to Karp–Miller tree termination, which
    is exactly `FX1Poly.ComputerAlgebra.fxNet4_dicksonWall = false` (the both-`later`
    AF-product case needs `WellFounded.fix`).
  * (2) *Direct coverability decider on the net.*  Reusing the NET-9 coverability route
    hits `ocpHasCompositionalCoverability = false` / `cvbHasKarpMillerTree = false`, all
    definitionally equal to the same Dickson wall — no finite Boolean certificate exists. -/
def evsHasPetriUnfolding : Bool := false

/-- The Winskel-unfolding wall is definitionally the certified NET-4 Dickson impossibility. -/
theorem evsUnfoldingWallEqualsDickson :
    evsHasPetriUnfolding = FX1Poly.ComputerAlgebra.fxNet4_dicksonWall := rfl

/-- **WALL — prime-algebraic-domain completeness for infinite event structures.**

Configurations of an event structure ordered by inclusion form a prime algebraic coherent
domain, and *every* such domain arises from a PES (Nielsen–Plotkin–Winskel).  The
representation theorem quantifies over directed sets of configurations and their suprema.

Burned attacks:
  * (1) *Finite configuration lattice.*  Enumerating configurations of a *finite* structure
    is decidable, but the completeness statement is about *infinite* structures where the
    complete-prime elements are recovered only as directed suprema — an omega-colimit object
    that the finite-Boolean fragment cannot name; the limit needs `WellFounded.fix` over the
    inclusion order.
  * (2) *Coinductive configuration stream.*  Modelling infinite configurations as a codata
    stream of finite approximants pushes the completeness obligation into a bisimulation up
    to directed joins, whose well-definedness again rests on a non-structural well-founded
    recursion forbidden here. -/
def evsHasInfiniteDomainCompleteness : Bool := false

/-! ## Capability markers (the DECIDED half) -/

/-- The finite configuration-validity decision is shipped. -/
def evsHasConfigurationDecision : Bool := true

/-- Configuration equality up to reordering is shipped. -/
def evsHasConfigEquality : Bool := true

/-- The single-event covering decision is shipped. -/
def evsHasCoveringDecision : Bool := true

/-- The extend-preserves-validity keystone is shipped. -/
def evsHasExtendPreservation : Bool := true

/-! ## The running example and ground fires

`evsExample`: events `{0, 1, 2}`, one causal edge `0 ≤ 2`, and symmetric conflict
`0 # 1`, `1 # 2`.  This is well-formed: `0 # 1` with `0 ≤ 2` would force `1 # 2` by
inheritance — and `1 # 2` is present. -/

/-- The running prime event structure. -/
def evsExample : EventStructure where
  events := 0 :: 1 :: 2 :: []
  causalPairs := (0, 2) :: []
  conflictPairs := (0, 1) :: (1, 0) :: (1, 2) :: (2, 1) :: []

/-- The set `{2, 0}` is a valid configuration (conflict-free and down-closed: `0 ≤ 2` and
both endpoints present). -/
theorem evsFireConfigValid : evsIsConfiguration evsExample (2 :: 0 :: []) = true := rfl

/-- The set `{0, 1}` is not a configuration: `0 # 1`. -/
theorem evsFireConflictInvalid : evsIsConfiguration evsExample (0 :: 1 :: []) = false := rfl

/-- The set `{2}` is not a configuration: it omits the causal predecessor `0` of `2`. -/
theorem evsFireDownClosedFails : evsIsConfiguration evsExample (2 :: []) = false := rfl

/-- Event `2` is enabled at the configuration `{0}` (its predecessor `0` is present and it is
conflict-free with `{0}`). -/
theorem evsFireEnabled : evsEnabled evsExample (0 :: []) 2 = true := rfl

/-- Extending the configuration `{0}` by the enabled event `2` stays a configuration — the
keystone, instantiated on the running example. -/
theorem evsFireExtendStaysConfig :
    evsIsConfiguration evsExample (2 :: 0 :: []) = true :=
  evsExtendPreservesConfig evsExample (0 :: []) 2 rfl rfl

/-- `{2, 0}` and `{0, 2}` are equal configurations (equal up to reordering). -/
theorem evsFireConfigEqReorder : evsConfigEq (2 :: 0 :: []) (0 :: 2 :: []) = true := rfl

/-- `{0, 1}` and `{0, 2}` are distinct configurations. -/
theorem evsFireConfigNeq : evsConfigEq (0 :: 1 :: []) (0 :: 2 :: []) = false := rfl

/-- Causal reachability decides `0 ≤ 2` (via the edge `0 → 2`). -/
theorem evsFireCausesLeTrue : evsCausesLe evsExample 0 2 = true := rfl

/-- Causal reachability decides `¬ (2 ≤ 0)` (no edge out of `2`). -/
theorem evsFireCausesLeFalse : evsCausesLe evsExample 2 0 = false := rfl

/-- The running example is well-formed (symmetric, irreflexive, conflict-inherited). -/
theorem evsFireWellFormed : evsWellFormed evsExample = true := rfl

end FX1Poly.Polygraph.Net
