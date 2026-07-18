import FX1Poly.ComputerAlgebra.Order.AlmostFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/Decision/HornSatDecision — HORN-SAT decided via the least-model fixpoint

Propositional HORN-SAT (Dowling–Gallier / van Emden–Kowalski least-model semantics), decided
constructively and certificate-first.  A clause is `HornSatClause` — a `body : List Nat` of
atoms plus an optional `head : Option Nat`; `head = none` is the GOAL clause (the body implies
falsity).  A system is `List HornSatClause`.

Truth sets are strictly-ascending `List Nat` with `Bool` membership `hornSatMember` (a
`Nat.beq` scan) and sorted insertion `hornSatInsert` (a membership guard over the three-way
comparison placer `hornSatPlace`, driven by the structural comparator `hornSatCompareNat`).
The immediate-consequence operator `hornSatStep` folds one pass over the clauses, inserting
each fired head; `hornSatSaturate` iterates it under structural fuel, detecting stabilization
with the hand-rolled list comparator `hornSatTrueSetBeq`.

## Fuel adequacy (proven, not assumed)

Each pass either returns the input list LITERALLY (`hornSatStepGrowsOrFixes`) or strictly
grows its length; the set is duplicate-free (`hornSatIsDistinct` is preserved from the empty
start) and every element it ever receives is drawn from the system's head list
(`hornSatStepStaysWithin` + `hornSatHeadsListCovers`).  The pigeonhole lemma
`hornSatDistinctWithinLength` (via `hornSatRemoveFirst`) caps the set's length by the head
list's length, so fuel `length (hornSatHeadsList system) + 1` reaches a genuine fixpoint:
`hornSatSaturateReachesFixpoint`, specialized to `hornSatLeastModelIsFixpoint`.  All length
arithmetic runs through the local existential order `hornSatNatLe` (`∃ delta, large = small
+ delta`) — no `Nat.le`/`Nat.sub` library surface.

## The decision and its certificates

`hornSatDecide` saturates from the empty set and scans for a fired goal clause
(`hornSatFindViolatedGoal`):

  * SAT branch (`HornSatVerdict.isSatisfiable leastModelSet`):
    - `hornSatLeastModelIsClosed` — at the fixpoint every fired positive clause has its head
      in the set (closure, from the fixpoint equation + `hornSatStepDeliversHead`);
    - `hornSatDecideSatisfiableGivesModel` — the executable checker `hornSatCheckModel`
      accepts the returned set;
    - `hornSatDecideSatisfiableInducedEnv` — checker-eval agreement: the induced environment
      `fun atom => hornSatMember leastModelSet atom` satisfies every clause under the
      functional evaluator `hornSatEnvSatisfiesAll` (`hornSatCheckModelInduced`).
  * MINIMALITY — `hornSatLeastModelIsMinimal`: for ANY `environment : Nat → Bool` whose
    `hornSatEnvSatisfiesAll` check passes, every member of the saturated set is
    environment-true (fuel induction over the saturation with the per-pass lemma
    `hornSatStepKeepsEnvBound`).
  * UNSAT branch (`HornSatVerdict.isUnsatisfiable goalIndex saturatedSet`):
    `hornSatDecideUnsatisfiableSound` — minimality forces any satisfying environment to make
    the fired goal body all-true, yet the goal clause requires falsity — `False`.

The least model is also canonical: `hornSatLeastModelIsDistinct` and
`hornSatLeastModelIsAscending` (strict ascent through `hornSatPlace`).

## Zero-axiom

Structural recursion/induction only (on `Nat`, `List`, `Option`, `Ordering`, `Bool`, and the
membership derivations `HornSatClauseIn`); `cond`-based branching everywhere so every case
split is a `Bool`/constructor `cases` plus `rw`.  Nat facts used: `Nat.add_comm`,
`Nat.add_assoc`, `Nat.zero_add`, `Nat.eq_of_beq_eq_true` (all propext-clean); everything else
is hand-rolled (`hornSatNatSuccAdd`, `hornSatNatBeqSelf`, the comparator kit).  No `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/HornSatDecision.lean`.  Marker:
`fxDissatIsland_hasHornSatDecision := true`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Clause shape -/

/-- A Horn clause: conjunction of `body` atoms implying `head`; `head = none` means the body
implies falsity (a goal clause). -/
structure HornSatClause where
  body : List Nat
  head : Option Nat

/-- Structural list membership for clauses (hand-rolled `List.Mem` clone, kept local so the
decomposition stays axiom-free). -/
inductive HornSatClauseIn : HornSatClause → List HornSatClause → Prop where
  | here (clause : HornSatClause) (rest : List HornSatClause) :
      HornSatClauseIn clause (clause :: rest)
  | there (clause other : HornSatClause) (rest : List HornSatClause) :
      HornSatClauseIn clause rest → HornSatClauseIn clause (other :: rest)

/-! ## Nat comparison kit (structural, propext-clean) -/

/-- `Nat.beq` is reflexive (hand-rolled). -/
theorem hornSatNatBeqSelf : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ inner => hornSatNatBeqSelf inner

/-- Structural three-way comparison on `Nat`. -/
def hornSatCompareNat : Nat → Nat → Ordering
  | 0, 0 => Ordering.eq
  | 0, Nat.succ _ => Ordering.lt
  | Nat.succ _, 0 => Ordering.gt
  | Nat.succ innerLeft, Nat.succ innerRight => hornSatCompareNat innerLeft innerRight

/-- The comparator is reflexively `eq`. -/
theorem hornSatCompareSelfIsEq : (value : Nat) → hornSatCompareNat value value = Ordering.eq
  | 0 => rfl
  | Nat.succ inner => hornSatCompareSelfIsEq inner

/-- `eq` verdicts are honest: the compared numbers are equal. -/
theorem hornSatCompareEqImpliesEq : (left right : Nat) →
    hornSatCompareNat left right = Ordering.eq → left = right
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hcompare => Ordering.noConfusion hcompare
  | Nat.succ _, 0, hcompare => Ordering.noConfusion hcompare
  | Nat.succ innerLeft, Nat.succ innerRight, hcompare =>
      congrArg Nat.succ (hornSatCompareEqImpliesEq innerLeft innerRight hcompare)

/-- Flipping a `gt` verdict yields `lt`. -/
theorem hornSatCompareGtImpliesLtFlip : (left right : Nat) →
    hornSatCompareNat left right = Ordering.gt → hornSatCompareNat right left = Ordering.lt
  | 0, 0, hcompare => Ordering.noConfusion hcompare
  | 0, Nat.succ _, hcompare => Ordering.noConfusion hcompare
  | Nat.succ _, 0, _ => rfl
  | Nat.succ innerLeft, Nat.succ innerRight, hcompare =>
      hornSatCompareGtImpliesLtFlip innerLeft innerRight hcompare

/-! ## Additive arithmetic kit (existential order, no `Nat.le` surface) -/

/-- `succ` distributes out of the left addend (hand-rolled `Nat.succ_add`). -/
theorem hornSatNatSuccAdd : (first second : Nat) →
    Nat.succ first + second = Nat.succ (first + second)
  | _, 0 => rfl
  | first, Nat.succ innerSecond => congrArg Nat.succ (hornSatNatSuccAdd first innerSecond)

/-- Successor injectivity via `Nat.pred` (no auto-generated `injEq`). -/
theorem hornSatNatSuccInj (first second : Nat)
    (hsucc : Nat.succ first = Nat.succ second) : first = second :=
  congrArg Nat.pred hsucc

/-- No number equals the successor of itself plus anything. -/
theorem hornSatNatNeverSuccPlus : (value extra : Nat) →
    value = Nat.succ (value + extra) → False
  | 0, _extra, himpossible => Nat.noConfusion himpossible
  | Nat.succ inner, extra, himpossible =>
      hornSatNatNeverSuccPlus inner extra
        (Eq.trans
          (hornSatNatSuccInj inner (Nat.succ inner + extra) himpossible)
          (hornSatNatSuccAdd inner extra))

/-- Existential additive order on `Nat`: `small ≤ large` as a concrete delta witness. -/
def hornSatNatLe (small large : Nat) : Prop := ∃ delta, large = small + delta

/-- Zero is below everything. -/
theorem hornSatNatLeZero (value : Nat) : hornSatNatLe 0 value :=
  ⟨value, (Nat.zero_add value).symm⟩

/-- The order is `succ`-monotone. -/
theorem hornSatNatLeSucc (small large : Nat) (hle : hornSatNatLe small large) :
    hornSatNatLe (Nat.succ small) (Nat.succ large) :=
  match hle with
  | ⟨delta, hEquation⟩ =>
      ⟨delta, Eq.trans (congrArg Nat.succ hEquation) (hornSatNatSuccAdd small delta).symm⟩

/-- The order is transitive (deltas add). -/
theorem hornSatNatLeTrans (small middle large : Nat)
    (hSmallMiddle : hornSatNatLe small middle) (hMiddleLarge : hornSatNatLe middle large) :
    hornSatNatLe small large :=
  match hSmallMiddle, hMiddleLarge with
  | ⟨firstDelta, hFirst⟩, ⟨secondDelta, hSecond⟩ =>
      ⟨firstDelta + secondDelta,
        Eq.trans hSecond
          (Eq.trans (congrArg (fun value => value + secondDelta) hFirst)
            (Nat.add_assoc small firstDelta secondDelta))⟩

/-- The order is compatible with a common left addend. -/
theorem hornSatNatLeAddLeft (base small large : Nat) (hle : hornSatNatLe small large) :
    hornSatNatLe (base + small) (base + large) :=
  match hle with
  | ⟨delta, hEquation⟩ =>
      ⟨delta, Eq.trans (congrArg (fun value => base + value) hEquation)
        (Nat.add_assoc base small delta).symm⟩

/-- `succ value ≤ value` is absurd. -/
theorem hornSatNatLeSuccSelfFalse (value : Nat)
    (hle : hornSatNatLe (Nat.succ value) value) : False :=
  match hle with
  | ⟨delta, hEquation⟩ =>
      hornSatNatNeverSuccPlus value delta
        (Eq.trans hEquation (hornSatNatSuccAdd value delta))

/-! ## Boolean split helpers -/

/-- A true conjunction splits into two true conjuncts. -/
theorem hornSatAndSplit : (left right : Bool) →
    (left && right) = true → left = true ∧ right = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hcontr => Bool.noConfusion hcontr
  | false, true, hcontr => Bool.noConfusion hcontr
  | false, false, hcontr => Bool.noConfusion hcontr

/-- A false disjunction splits into two false disjuncts. -/
theorem hornSatOrFalseSplit : (left right : Bool) →
    (left || right) = false → left = false ∧ right = false
  | false, false, _ => ⟨rfl, rfl⟩
  | false, true, hcontr => Bool.noConfusion hcontr
  | true, false, hcontr => Bool.noConfusion hcontr
  | true, true, hcontr => Bool.noConfusion hcontr

/-! ## Truth-set membership -/

/-- `Bool` membership scan over a truth set (`Nat.beq` per element). -/
def hornSatMember (trueSet : List Nat) (atom : Nat) : Bool :=
  match trueSet with
  | [] => false
  | head :: tail => Nat.beq atom head || hornSatMember tail atom

/-- The head of a cons is a member. -/
theorem hornSatMemberHead (headAtom : Nat) (tail : List Nat) :
    hornSatMember (headAtom :: tail) headAtom = true := by
  show (Nat.beq headAtom headAtom || hornSatMember tail headAtom) = true
  rw [hornSatNatBeqSelf]
  rfl

/-- Membership in the tail lifts over a cons. -/
theorem hornSatMemberTail (headAtom atom : Nat) (tail : List Nat)
    (hmember : hornSatMember tail atom = true) :
    hornSatMember (headAtom :: tail) atom = true := by
  show (Nat.beq atom headAtom || hornSatMember tail atom) = true
  exact afOrIntroRight _ _ hmember

/-- A member of a cons is the head or a member of the tail. -/
theorem hornSatMemberInversion (headAtom atom : Nat) (tail : List Nat)
    (hmember : hornSatMember (headAtom :: tail) atom = true) :
    atom = headAtom ∨ hornSatMember tail atom = true := by
  have hUnfolded : (Nat.beq atom headAtom || hornSatMember tail atom) = true := hmember
  rcases afOrElim _ _ hUnfolded with hbeq | htail
  · exact Or.inl (Nat.eq_of_beq_eq_true hbeq)
  · exact Or.inr htail

/-- Non-membership introduction over a cons. -/
theorem hornSatMemberConsFalseIntro (headAtom atom : Nat) (tail : List Nat)
    (hbeq : Nat.beq atom headAtom = false) (htail : hornSatMember tail atom = false) :
    hornSatMember (headAtom :: tail) atom = false := by
  show (Nat.beq atom headAtom || hornSatMember tail atom) = false
  rw [hbeq, htail]
  rfl

/-! ## Sorted placement and guarded insertion -/

/-- One placement step, keyed by a comparison verdict (kept first-order so proofs can
rewrite the verdict and reduce definitionally). -/
def hornSatPlaceStep (comparison : Ordering) (atom headAtom : Nat)
    (tail placedTail : List Nat) : List Nat :=
  match comparison with
  | Ordering.lt => atom :: headAtom :: tail
  | Ordering.eq => headAtom :: tail
  | Ordering.gt => headAtom :: placedTail

/-- Three-way-comparison sorted placement. -/
def hornSatPlace (atom : Nat) : List Nat → List Nat
  | [] => [atom]
  | headAtom :: tail =>
      hornSatPlaceStep (hornSatCompareNat atom headAtom) atom headAtom tail
        (hornSatPlace atom tail)

/-- Placement unfold, `lt` verdict. -/
theorem hornSatPlaceConsOfLt (atom headAtom : Nat) (tail : List Nat)
    (hcompare : hornSatCompareNat atom headAtom = Ordering.lt) :
    hornSatPlace atom (headAtom :: tail) = atom :: headAtom :: tail := by
  show hornSatPlaceStep (hornSatCompareNat atom headAtom) atom headAtom tail
    (hornSatPlace atom tail) = atom :: headAtom :: tail
  rw [hcompare]
  rfl

/-- Placement unfold, `eq` verdict. -/
theorem hornSatPlaceConsOfEq (atom headAtom : Nat) (tail : List Nat)
    (hcompare : hornSatCompareNat atom headAtom = Ordering.eq) :
    hornSatPlace atom (headAtom :: tail) = headAtom :: tail := by
  show hornSatPlaceStep (hornSatCompareNat atom headAtom) atom headAtom tail
    (hornSatPlace atom tail) = headAtom :: tail
  rw [hcompare]
  rfl

/-- Placement unfold, `gt` verdict. -/
theorem hornSatPlaceConsOfGt (atom headAtom : Nat) (tail : List Nat)
    (hcompare : hornSatCompareNat atom headAtom = Ordering.gt) :
    hornSatPlace atom (headAtom :: tail) = headAtom :: hornSatPlace atom tail := by
  show hornSatPlaceStep (hornSatCompareNat atom headAtom) atom headAtom tail
    (hornSatPlace atom tail) = headAtom :: hornSatPlace atom tail
  rw [hcompare]
  rfl

/-- Membership-guarded sorted insertion: a present atom leaves the set untouched
LITERALLY; a fresh atom is placed by three-way comparison. -/
def hornSatInsert (atom : Nat) (trueSet : List Nat) : List Nat :=
  cond (hornSatMember trueSet atom) trueSet (hornSatPlace atom trueSet)

/-- Insertion of a present atom is the identity. -/
theorem hornSatInsertOfMember (atom : Nat) (trueSet : List Nat)
    (hmember : hornSatMember trueSet atom = true) :
    hornSatInsert atom trueSet = trueSet := by
  show cond (hornSatMember trueSet atom) trueSet (hornSatPlace atom trueSet) = trueSet
  rw [hmember]
  rfl

/-- Insertion of a fresh atom is sorted placement. -/
theorem hornSatInsertOfFresh (atom : Nat) (trueSet : List Nat)
    (hfresh : hornSatMember trueSet atom = false) :
    hornSatInsert atom trueSet = hornSatPlace atom trueSet := by
  show cond (hornSatMember trueSet atom) trueSet (hornSatPlace atom trueSet)
    = hornSatPlace atom trueSet
  rw [hfresh]
  rfl

/-- A fresh atom placed against a cons never compares `eq` to the head. -/
theorem hornSatFreshCompareNeverEq (atom headAtom : Nat) (tail : List Nat)
    (hfresh : hornSatMember (headAtom :: tail) atom = false)
    (hcompare : hornSatCompareNat atom headAtom = Ordering.eq) : False := by
  have hsplitFresh := hornSatOrFalseSplit _ _ hfresh
  have hcontr := hsplitFresh.1
  rw [hornSatCompareEqImpliesEq atom headAtom hcompare, hornSatNatBeqSelf] at hcontr
  exact Bool.noConfusion hcontr

/-- The placed atom is a member of the placement. -/
theorem hornSatPlaceMakesMember : (atom : Nat) → (trueSet : List Nat) →
    hornSatMember (hornSatPlace atom trueSet) atom = true
  | atom, [] => by
      show (Nat.beq atom atom || false) = true
      rw [hornSatNatBeqSelf]
      rfl
  | atom, headAtom :: tail => by
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          exact hornSatMemberHead atom (headAtom :: tail)
      | eq =>
          rw [hornSatPlaceConsOfEq atom headAtom tail hcompare,
            hornSatCompareEqImpliesEq atom headAtom hcompare]
          exact hornSatMemberHead headAtom tail
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          exact hornSatMemberTail headAtom atom (hornSatPlace atom tail)
            (hornSatPlaceMakesMember atom tail)

/-- Placement preserves prior members. -/
theorem hornSatPlacePreservesMembers : (atom otherAtom : Nat) → (trueSet : List Nat) →
    hornSatMember trueSet otherAtom = true →
    hornSatMember (hornSatPlace atom trueSet) otherAtom = true
  | _, _, [], hmember => Bool.noConfusion hmember
  | atom, otherAtom, headAtom :: tail, hmember => by
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          exact hornSatMemberTail atom otherAtom (headAtom :: tail) hmember
      | eq =>
          rw [hornSatPlaceConsOfEq atom headAtom tail hcompare]
          exact hmember
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          rcases hornSatMemberInversion headAtom otherAtom tail hmember with hEqHead | hInTail
          · rw [hEqHead]
            exact hornSatMemberHead headAtom (hornSatPlace atom tail)
          · exact hornSatMemberTail headAtom otherAtom (hornSatPlace atom tail)
              (hornSatPlacePreservesMembers atom otherAtom tail hInTail)

/-- A member of a placement is the placed atom or a prior member. -/
theorem hornSatPlaceMemberInversion : (atom otherAtom : Nat) → (trueSet : List Nat) →
    hornSatMember (hornSatPlace atom trueSet) otherAtom = true →
    otherAtom = atom ∨ hornSatMember trueSet otherAtom = true
  | atom, otherAtom, [], hmember => by
      have hUnfolded : (Nat.beq otherAtom atom || false) = true := hmember
      rcases afOrElim _ _ hUnfolded with hbeq | hcontr
      · exact Or.inl (Nat.eq_of_beq_eq_true hbeq)
      · exact Bool.noConfusion hcontr
  | atom, otherAtom, headAtom :: tail, hmember => by
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare] at hmember
          rcases hornSatMemberInversion atom otherAtom (headAtom :: tail) hmember
            with hEqAtom | hInRest
          · exact Or.inl hEqAtom
          · exact Or.inr hInRest
      | eq =>
          rw [hornSatPlaceConsOfEq atom headAtom tail hcompare] at hmember
          exact Or.inr hmember
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare] at hmember
          rcases hornSatMemberInversion headAtom otherAtom (hornSatPlace atom tail) hmember
            with hEqHead | hInPlaced
          · refine Or.inr ?_
            rw [hEqHead]
            exact hornSatMemberHead headAtom tail
          · rcases hornSatPlaceMemberInversion atom otherAtom tail hInPlaced
              with hEqAtom | hInTail
            · exact Or.inl hEqAtom
            · exact Or.inr (hornSatMemberTail headAtom otherAtom tail hInTail)

/-- Placing a fresh atom grows the length by exactly one. -/
theorem hornSatPlaceLengthOfFresh : (atom : Nat) → (trueSet : List Nat) →
    hornSatMember trueSet atom = false →
    (hornSatPlace atom trueSet).length = Nat.succ trueSet.length
  | _, [], _ => rfl
  | atom, headAtom :: tail, hfresh => by
      have hsplitFresh := hornSatOrFalseSplit _ _ hfresh
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          rfl
      | eq => exact False.elim (hornSatFreshCompareNeverEq atom headAtom tail hfresh hcompare)
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          show Nat.succ (hornSatPlace atom tail).length = Nat.succ (Nat.succ tail.length)
          exact congrArg Nat.succ (hornSatPlaceLengthOfFresh atom tail hsplitFresh.2)

/-- The inserted atom is a member of the insertion. -/
theorem hornSatInsertMakesMember (atom : Nat) (trueSet : List Nat) :
    hornSatMember (hornSatInsert atom trueSet) atom = true := by
  cases hmem : hornSatMember trueSet atom with
  | true =>
      rw [hornSatInsertOfMember atom trueSet hmem]
      exact hmem
  | false =>
      rw [hornSatInsertOfFresh atom trueSet hmem]
      exact hornSatPlaceMakesMember atom trueSet

/-- Insertion preserves prior members. -/
theorem hornSatInsertPreservesMembers (atom otherAtom : Nat) (trueSet : List Nat)
    (hmember : hornSatMember trueSet otherAtom = true) :
    hornSatMember (hornSatInsert atom trueSet) otherAtom = true := by
  cases hmem : hornSatMember trueSet atom with
  | true =>
      rw [hornSatInsertOfMember atom trueSet hmem]
      exact hmember
  | false =>
      rw [hornSatInsertOfFresh atom trueSet hmem]
      exact hornSatPlacePreservesMembers atom otherAtom trueSet hmember

/-- A member of an insertion is the inserted atom or a prior member. -/
theorem hornSatInsertMemberInversion (atom otherAtom : Nat) (trueSet : List Nat)
    (hmember : hornSatMember (hornSatInsert atom trueSet) otherAtom = true) :
    otherAtom = atom ∨ hornSatMember trueSet otherAtom = true := by
  cases hmem : hornSatMember trueSet atom with
  | true =>
      rw [hornSatInsertOfMember atom trueSet hmem] at hmember
      exact Or.inr hmember
  | false =>
      rw [hornSatInsertOfFresh atom trueSet hmem] at hmember
      exact hornSatPlaceMemberInversion atom otherAtom trueSet hmember

/-- Insertion either fixes the set literally or grows its length by exactly one. -/
theorem hornSatInsertGrowsOrFixes (atom : Nat) (trueSet : List Nat) :
    hornSatInsert atom trueSet = trueSet ∨
      (hornSatInsert atom trueSet).length = Nat.succ trueSet.length := by
  cases hmem : hornSatMember trueSet atom with
  | true => exact Or.inl (hornSatInsertOfMember atom trueSet hmem)
  | false =>
      refine Or.inr ?_
      rw [hornSatInsertOfFresh atom trueSet hmem]
      exact hornSatPlaceLengthOfFresh atom trueSet hmem

/-! ## Duplicate freedom -/

/-- `Bool` duplicate-freedom: no atom repeats. -/
def hornSatIsDistinct : List Nat → Bool
  | [] => true
  | headAtom :: tail => !hornSatMember tail headAtom && hornSatIsDistinct tail

/-- Duplicate-freedom of a cons splits into head-freshness and tail-freedom. -/
theorem hornSatDistinctConsSplit (headAtom : Nat) (tail : List Nat)
    (hdistinct : hornSatIsDistinct (headAtom :: tail) = true) :
    hornSatMember tail headAtom = false ∧ hornSatIsDistinct tail = true := by
  have hUnfolded : (!hornSatMember tail headAtom && hornSatIsDistinct tail) = true := hdistinct
  cases hmem : hornSatMember tail headAtom with
  | false =>
      rw [hmem] at hUnfolded
      exact ⟨rfl, hUnfolded⟩
  | true =>
      rw [hmem] at hUnfolded
      exact Bool.noConfusion hUnfolded

/-- Duplicate-freedom introduction over a cons. -/
theorem hornSatDistinctConsIntro (headAtom : Nat) (tail : List Nat)
    (hfresh : hornSatMember tail headAtom = false)
    (hdistinct : hornSatIsDistinct tail = true) :
    hornSatIsDistinct (headAtom :: tail) = true := by
  show (!hornSatMember tail headAtom && hornSatIsDistinct tail) = true
  rw [hfresh, hdistinct]
  rfl

/-- Placing a fresh atom preserves duplicate-freedom. -/
theorem hornSatPlaceKeepsDistinct : (trueSet : List Nat) → (atom : Nat) →
    hornSatIsDistinct trueSet = true → hornSatMember trueSet atom = false →
    hornSatIsDistinct (hornSatPlace atom trueSet) = true
  | [], atom, _, _ => by
      show (!hornSatMember ([] : List Nat) atom && hornSatIsDistinct []) = true
      rfl
  | headAtom :: tail, atom, hdistinct, hfresh => by
      have hsplitDistinct := hornSatDistinctConsSplit headAtom tail hdistinct
      have hsplitFresh := hornSatOrFalseSplit _ _ hfresh
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          exact hornSatDistinctConsIntro atom (headAtom :: tail)
            (hornSatMemberConsFalseIntro headAtom atom tail hsplitFresh.1 hsplitFresh.2)
            hdistinct
      | eq =>
          exact False.elim (hornSatFreshCompareNeverEq atom headAtom tail hfresh hcompare)
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          apply hornSatDistinctConsIntro
          · cases hprobe : hornSatMember (hornSatPlace atom tail) headAtom with
            | false => rfl
            | true =>
                rcases hornSatPlaceMemberInversion atom headAtom tail hprobe
                  with hEqAtom | hInTail
                · rw [hEqAtom] at hcompare
                  rw [hornSatCompareSelfIsEq] at hcompare
                  exact Ordering.noConfusion hcompare
                · exact Bool.noConfusion (Eq.trans hsplitDistinct.1.symm hInTail)
          · exact hornSatPlaceKeepsDistinct tail atom hsplitDistinct.2 hsplitFresh.2

/-- Insertion preserves duplicate-freedom. -/
theorem hornSatInsertKeepsDistinct (atom : Nat) (trueSet : List Nat)
    (hdistinct : hornSatIsDistinct trueSet = true) :
    hornSatIsDistinct (hornSatInsert atom trueSet) = true := by
  cases hmem : hornSatMember trueSet atom with
  | true =>
      rw [hornSatInsertOfMember atom trueSet hmem]
      exact hdistinct
  | false =>
      rw [hornSatInsertOfFresh atom trueSet hmem]
      exact hornSatPlaceKeepsDistinct trueSet atom hdistinct hmem

/-! ## Strict ascent -/

/-- Is a comparison verdict `lt`? -/
def hornSatOrderingIsLt (comparison : Ordering) : Bool :=
  match comparison with
  | Ordering.lt => true
  | Ordering.eq => false
  | Ordering.gt => false

/-- Is `lower` strictly below `upper`? -/
def hornSatNatIsBelow (lower upper : Nat) : Bool :=
  hornSatOrderingIsLt (hornSatCompareNat lower upper)

/-- An `lt` verdict certifies strict below-ness. -/
theorem hornSatIsBelowOfLt (lower upper : Nat)
    (hcompare : hornSatCompareNat lower upper = Ordering.lt) :
    hornSatNatIsBelow lower upper = true := by
  show hornSatOrderingIsLt (hornSatCompareNat lower upper) = true
  rw [hcompare]
  rfl

/-- Strict ascent above an exclusive lower bound. -/
def hornSatIsAscendingFrom (lowerBound : Nat) : List Nat → Bool
  | [] => true
  | headAtom :: tail => hornSatNatIsBelow lowerBound headAtom && hornSatIsAscendingFrom headAtom tail

/-- Strict ascent of a truth set. -/
def hornSatIsAscending : List Nat → Bool
  | [] => true
  | headAtom :: tail => hornSatIsAscendingFrom headAtom tail

/-- Placing a fresh atom that clears the bound preserves bounded strict ascent. -/
theorem hornSatPlaceKeepsAscendingFrom : (trueSet : List Nat) → (lowerBound atom : Nat) →
    hornSatIsAscendingFrom lowerBound trueSet = true →
    hornSatNatIsBelow lowerBound atom = true →
    hornSatMember trueSet atom = false →
    hornSatIsAscendingFrom lowerBound (hornSatPlace atom trueSet) = true
  | [], lowerBound, atom, _, hbelow, _ => by
      show (hornSatNatIsBelow lowerBound atom && true) = true
      rw [hbelow]
      rfl
  | headAtom :: tail, lowerBound, atom, hascending, hbelow, hfresh => by
      have hAscUnfolded : (hornSatNatIsBelow lowerBound headAtom
          && hornSatIsAscendingFrom headAtom tail) = true := hascending
      have hsplitAsc := hornSatAndSplit _ _ hAscUnfolded
      have hsplitFresh := hornSatOrFalseSplit _ _ hfresh
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          show (hornSatNatIsBelow lowerBound atom
            && (hornSatNatIsBelow atom headAtom && hornSatIsAscendingFrom headAtom tail)) = true
          rw [hbelow, hornSatIsBelowOfLt atom headAtom hcompare, hsplitAsc.2]
          rfl
      | eq =>
          exact False.elim (hornSatFreshCompareNeverEq atom headAtom tail hfresh hcompare)
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          show (hornSatNatIsBelow lowerBound headAtom
            && hornSatIsAscendingFrom headAtom (hornSatPlace atom tail)) = true
          rw [hsplitAsc.1]
          show hornSatIsAscendingFrom headAtom (hornSatPlace atom tail) = true
          exact hornSatPlaceKeepsAscendingFrom tail headAtom atom hsplitAsc.2
            (hornSatIsBelowOfLt headAtom atom (hornSatCompareGtImpliesLtFlip atom headAtom hcompare))
            hsplitFresh.2

/-- Placing a fresh atom preserves strict ascent. -/
theorem hornSatPlaceKeepsAscending : (trueSet : List Nat) → (atom : Nat) →
    hornSatIsAscending trueSet = true → hornSatMember trueSet atom = false →
    hornSatIsAscending (hornSatPlace atom trueSet) = true
  | [], _, _, _ => rfl
  | headAtom :: tail, atom, hascending, hfresh => by
      have hAscFrom : hornSatIsAscendingFrom headAtom tail = true := hascending
      have hsplitFresh := hornSatOrFalseSplit _ _ hfresh
      cases hcompare : hornSatCompareNat atom headAtom with
      | lt =>
          rw [hornSatPlaceConsOfLt atom headAtom tail hcompare]
          show (hornSatNatIsBelow atom headAtom && hornSatIsAscendingFrom headAtom tail) = true
          rw [hornSatIsBelowOfLt atom headAtom hcompare, hAscFrom]
          rfl
      | eq =>
          exact False.elim (hornSatFreshCompareNeverEq atom headAtom tail hfresh hcompare)
      | gt =>
          rw [hornSatPlaceConsOfGt atom headAtom tail hcompare]
          show hornSatIsAscendingFrom headAtom (hornSatPlace atom tail) = true
          exact hornSatPlaceKeepsAscendingFrom tail headAtom atom hAscFrom
            (hornSatIsBelowOfLt headAtom atom (hornSatCompareGtImpliesLtFlip atom headAtom hcompare))
            hsplitFresh.2

/-- Insertion preserves strict ascent. -/
theorem hornSatInsertKeepsAscending (atom : Nat) (trueSet : List Nat)
    (hascending : hornSatIsAscending trueSet = true) :
    hornSatIsAscending (hornSatInsert atom trueSet) = true := by
  cases hmem : hornSatMember trueSet atom with
  | true =>
      rw [hornSatInsertOfMember atom trueSet hmem]
      exact hascending
  | false =>
      rw [hornSatInsertOfFresh atom trueSet hmem]
      exact hornSatPlaceKeepsAscending trueSet atom hascending hmem

/-! ## Pigeonhole: a distinct set inside a pool is no longer than the pool -/

/-- Remove the first `Nat.beq` occurrence of a target from a pool. -/
def hornSatRemoveFirst (targetAtom : Nat) : List Nat → List Nat
  | [] => []
  | poolHead :: poolTail =>
      cond (Nat.beq targetAtom poolHead) poolTail
        (poolHead :: hornSatRemoveFirst targetAtom poolTail)

/-- Removing a present target shortens the pool by exactly one. -/
theorem hornSatRemoveFirstShortens : (poolList : List Nat) → (targetAtom : Nat) →
    hornSatMember poolList targetAtom = true →
    poolList.length = Nat.succ (hornSatRemoveFirst targetAtom poolList).length
  | [], _, hmember => Bool.noConfusion hmember
  | poolHead :: poolTail, targetAtom, hmember => by
      cases hprobe : Nat.beq targetAtom poolHead with
      | true =>
          have hremove : hornSatRemoveFirst targetAtom (poolHead :: poolTail) = poolTail := by
            show cond (Nat.beq targetAtom poolHead) poolTail
              (poolHead :: hornSatRemoveFirst targetAtom poolTail) = poolTail
            rw [hprobe]
            rfl
          rw [hremove]
          rfl
      | false =>
          have hMemberUnfolded : (Nat.beq targetAtom poolHead
              || hornSatMember poolTail targetAtom) = true := hmember
          rw [hprobe] at hMemberUnfolded
          have hremove : hornSatRemoveFirst targetAtom (poolHead :: poolTail)
              = poolHead :: hornSatRemoveFirst targetAtom poolTail := by
            show cond (Nat.beq targetAtom poolHead) poolTail
              (poolHead :: hornSatRemoveFirst targetAtom poolTail)
              = poolHead :: hornSatRemoveFirst targetAtom poolTail
            rw [hprobe]
            rfl
          rw [hremove]
          show Nat.succ poolTail.length
            = Nat.succ (Nat.succ (hornSatRemoveFirst targetAtom poolTail).length)
          exact congrArg Nat.succ
            (hornSatRemoveFirstShortens poolTail targetAtom hMemberUnfolded)

/-- Removal keeps every member that differs from the target. -/
theorem hornSatRemoveFirstKeepsOthers : (poolList : List Nat) → (targetAtom otherAtom : Nat) →
    Nat.beq otherAtom targetAtom = false →
    hornSatMember poolList otherAtom = true →
    hornSatMember (hornSatRemoveFirst targetAtom poolList) otherAtom = true
  | [], _, _, _, hmember => Bool.noConfusion hmember
  | poolHead :: poolTail, targetAtom, otherAtom, hdiff, hmember => by
      cases hprobe : Nat.beq targetAtom poolHead with
      | true =>
          have hremove : hornSatRemoveFirst targetAtom (poolHead :: poolTail) = poolTail := by
            show cond (Nat.beq targetAtom poolHead) poolTail
              (poolHead :: hornSatRemoveFirst targetAtom poolTail) = poolTail
            rw [hprobe]
            rfl
          rw [hremove]
          rcases hornSatMemberInversion poolHead otherAtom poolTail hmember
            with hEqHead | hInTail
          · have hSame : otherAtom = targetAtom :=
              Eq.trans hEqHead (Nat.eq_of_beq_eq_true hprobe).symm
            rw [hSame, hornSatNatBeqSelf] at hdiff
            exact Bool.noConfusion hdiff
          · exact hInTail
      | false =>
          have hremove : hornSatRemoveFirst targetAtom (poolHead :: poolTail)
              = poolHead :: hornSatRemoveFirst targetAtom poolTail := by
            show cond (Nat.beq targetAtom poolHead) poolTail
              (poolHead :: hornSatRemoveFirst targetAtom poolTail)
              = poolHead :: hornSatRemoveFirst targetAtom poolTail
            rw [hprobe]
            rfl
          rw [hremove]
          rcases hornSatMemberInversion poolHead otherAtom poolTail hmember
            with hEqHead | hInTail
          · rw [hEqHead]
            exact hornSatMemberHead poolHead (hornSatRemoveFirst targetAtom poolTail)
          · exact hornSatMemberTail poolHead otherAtom
              (hornSatRemoveFirst targetAtom poolTail)
              (hornSatRemoveFirstKeepsOthers poolTail targetAtom otherAtom hdiff hInTail)

/-- **Pigeonhole.**  A duplicate-free truth set whose members all lie in a pool is no longer
than the pool. -/
theorem hornSatDistinctWithinLength : (trueSet : List Nat) → (poolList : List Nat) →
    hornSatIsDistinct trueSet = true →
    ((atom : Nat) → hornSatMember trueSet atom = true → hornSatMember poolList atom = true) →
    hornSatNatLe trueSet.length poolList.length
  | [], poolList, _, _ => hornSatNatLeZero poolList.length
  | firstAtom :: restAtoms, poolList, hdistinct, hwithin => by
      have hsplitDistinct := hornSatDistinctConsSplit firstAtom restAtoms hdistinct
      have hFirstInPool : hornSatMember poolList firstAtom = true :=
        hwithin firstAtom (hornSatMemberHead firstAtom restAtoms)
      have hRestWithin : (atom : Nat) → hornSatMember restAtoms atom = true →
          hornSatMember (hornSatRemoveFirst firstAtom poolList) atom = true := by
        intro atom hInRest
        have hDiff : Nat.beq atom firstAtom = false := by
          cases hprobe : Nat.beq atom firstAtom with
          | false => rfl
          | true =>
              have hEqFirst : atom = firstAtom := Nat.eq_of_beq_eq_true hprobe
              rw [hEqFirst] at hInRest
              exact Bool.noConfusion (Eq.trans hsplitDistinct.1.symm hInRest)
        exact hornSatRemoveFirstKeepsOthers poolList firstAtom atom hDiff
          (hwithin atom (hornSatMemberTail firstAtom atom restAtoms hInRest))
      have hRestLe : hornSatNatLe restAtoms.length
          (hornSatRemoveFirst firstAtom poolList).length :=
        hornSatDistinctWithinLength restAtoms (hornSatRemoveFirst firstAtom poolList)
          hsplitDistinct.2 hRestWithin
      have hPoolLen : poolList.length
          = Nat.succ (hornSatRemoveFirst firstAtom poolList).length :=
        hornSatRemoveFirstShortens poolList firstAtom hFirstInPool
      rw [hPoolLen]
      exact hornSatNatLeSucc restAtoms.length
        (hornSatRemoveFirst firstAtom poolList).length hRestLe

/-! ## Bodies, single-clause application, one pass -/

/-- Does the truth set contain every body atom? -/
def hornSatBodyHolds (trueSet : List Nat) : List Nat → Bool
  | [] => true
  | atom :: restBody => hornSatMember trueSet atom && hornSatBodyHolds trueSet restBody

/-- Body satisfaction is monotone under member-preserving set growth. -/
theorem hornSatBodyHoldsMonotone : (body : List Nat) → (smallSet largeSet : List Nat) →
    ((atom : Nat) → hornSatMember smallSet atom = true → hornSatMember largeSet atom = true) →
    hornSatBodyHolds smallSet body = true → hornSatBodyHolds largeSet body = true
  | [], _, _, _, _ => rfl
  | atom :: restBody, smallSet, largeSet, hwiden, hholds => by
      have hUnfolded : (hornSatMember smallSet atom
          && hornSatBodyHolds smallSet restBody) = true := hholds
      have hsplit := hornSatAndSplit _ _ hUnfolded
      show (hornSatMember largeSet atom && hornSatBodyHolds largeSet restBody) = true
      rw [hwiden atom hsplit.1,
        hornSatBodyHoldsMonotone restBody smallSet largeSet hwiden hsplit.2]
      rfl

/-- One clause application step, keyed by the head option and the fired flag. -/
def hornSatApplyClauseStep (headOption : Option Nat) (bodyFires : Bool)
    (trueSet : List Nat) : List Nat :=
  match headOption with
  | none => trueSet
  | some headAtom => cond bodyFires (hornSatInsert headAtom trueSet) trueSet

/-- Apply one clause to a truth set: insert the head when the body holds. -/
def hornSatApplyClause (clause : HornSatClause) (trueSet : List Nat) : List Nat :=
  hornSatApplyClauseStep clause.head (hornSatBodyHolds trueSet clause.body) trueSet

/-- Clause application preserves members. -/
theorem hornSatApplyPreservesMembers : (clause : HornSatClause) → (trueSet : List Nat) →
    (atom : Nat) → hornSatMember trueSet atom = true →
    hornSatMember (hornSatApplyClause clause trueSet) atom = true
  | ⟨_clauseBody, none⟩, _, _, hmember => hmember
  | ⟨clauseBody, some headAtom⟩, trueSet, atom, hmember => by
      have hRetyped : hornSatMember (cond (hornSatBodyHolds trueSet clauseBody)
          (hornSatInsert headAtom trueSet) trueSet) atom = true →
          hornSatMember (hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet) atom = true :=
        fun hclosed => hclosed
      apply hRetyped
      cases hbody : hornSatBodyHolds trueSet clauseBody with
      | false => exact hmember
      | true => exact hornSatInsertPreservesMembers headAtom atom trueSet hmember

/-- Clause application either fixes the set literally or grows its length by one. -/
theorem hornSatApplyGrowsOrFixes : (clause : HornSatClause) → (trueSet : List Nat) →
    hornSatApplyClause clause trueSet = trueSet ∨
      (hornSatApplyClause clause trueSet).length = Nat.succ trueSet.length
  | ⟨_clauseBody, none⟩, _trueSet => Or.inl rfl
  | ⟨clauseBody, some headAtom⟩, trueSet => by
      cases hbody : hornSatBodyHolds trueSet clauseBody with
      | false =>
          refine Or.inl ?_
          show cond (hornSatBodyHolds trueSet clauseBody)
            (hornSatInsert headAtom trueSet) trueSet = trueSet
          rw [hbody]
          rfl
      | true =>
          have hApplyIsInsert : hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet
              = hornSatInsert headAtom trueSet := by
            show cond (hornSatBodyHolds trueSet clauseBody)
              (hornSatInsert headAtom trueSet) trueSet = hornSatInsert headAtom trueSet
            rw [hbody]
            rfl
          rw [hApplyIsInsert]
          exact hornSatInsertGrowsOrFixes headAtom trueSet

/-- Clause application preserves duplicate-freedom. -/
theorem hornSatApplyKeepsDistinct : (clause : HornSatClause) → (trueSet : List Nat) →
    hornSatIsDistinct trueSet = true →
    hornSatIsDistinct (hornSatApplyClause clause trueSet) = true
  | ⟨_clauseBody, none⟩, _, hdistinct => hdistinct
  | ⟨clauseBody, some headAtom⟩, trueSet, hdistinct => by
      have hRetyped : hornSatIsDistinct (cond (hornSatBodyHolds trueSet clauseBody)
          (hornSatInsert headAtom trueSet) trueSet) = true →
          hornSatIsDistinct (hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet) = true :=
        fun hclosed => hclosed
      apply hRetyped
      cases hbody : hornSatBodyHolds trueSet clauseBody with
      | false => exact hdistinct
      | true => exact hornSatInsertKeepsDistinct headAtom trueSet hdistinct

/-- Clause application preserves strict ascent. -/
theorem hornSatApplyKeepsAscending : (clause : HornSatClause) → (trueSet : List Nat) →
    hornSatIsAscending trueSet = true →
    hornSatIsAscending (hornSatApplyClause clause trueSet) = true
  | ⟨_clauseBody, none⟩, _, hascending => hascending
  | ⟨clauseBody, some headAtom⟩, trueSet, hascending => by
      have hRetyped : hornSatIsAscending (cond (hornSatBodyHolds trueSet clauseBody)
          (hornSatInsert headAtom trueSet) trueSet) = true →
          hornSatIsAscending (hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet) = true :=
        fun hclosed => hclosed
      apply hRetyped
      cases hbody : hornSatBodyHolds trueSet clauseBody with
      | false => exact hascending
      | true => exact hornSatInsertKeepsAscending headAtom trueSet hascending

/-- One saturation pass: fold every clause over the truth set. -/
def hornSatStep (system : List HornSatClause) (trueSet : List Nat) : List Nat :=
  match system with
  | [] => trueSet
  | clause :: restSystem => hornSatStep restSystem (hornSatApplyClause clause trueSet)

/-- A pass preserves members. -/
theorem hornSatStepPreservesMembers : (system : List HornSatClause) → (trueSet : List Nat) →
    (atom : Nat) → hornSatMember trueSet atom = true →
    hornSatMember (hornSatStep system trueSet) atom = true
  | [], _, _, hmember => hmember
  | clause :: restSystem, trueSet, atom, hmember =>
      hornSatStepPreservesMembers restSystem (hornSatApplyClause clause trueSet) atom
        (hornSatApplyPreservesMembers clause trueSet atom hmember)

/-- A pass either returns the input set LITERALLY or strictly grows its length. -/
theorem hornSatStepGrowsOrFixes : (system : List HornSatClause) → (trueSet : List Nat) →
    hornSatStep system trueSet = trueSet ∨
      ∃ growthDelta, (hornSatStep system trueSet).length
        = trueSet.length + Nat.succ growthDelta
  | [], _ => Or.inl rfl
  | clause :: restSystem, trueSet => by
      cases hornSatApplyGrowsOrFixes clause trueSet with
      | inl hApplyFix =>
          have hStepUnfolded : hornSatStep (clause :: restSystem) trueSet
              = hornSatStep restSystem trueSet := by
            show hornSatStep restSystem (hornSatApplyClause clause trueSet)
              = hornSatStep restSystem trueSet
            rw [hApplyFix]
          rw [hStepUnfolded]
          exact hornSatStepGrowsOrFixes restSystem trueSet
      | inr hApplyGrow =>
          refine Or.inr ?_
          cases hornSatStepGrowsOrFixes restSystem (hornSatApplyClause clause trueSet) with
          | inl hRestFix =>
              refine ⟨0, ?_⟩
              show (hornSatStep restSystem (hornSatApplyClause clause trueSet)).length
                = trueSet.length + Nat.succ 0
              rw [hRestFix, hApplyGrow]
          | inr hRestGrow =>
              rcases hRestGrow with ⟨restDelta, hRestLen⟩
              refine ⟨Nat.succ restDelta, ?_⟩
              show (hornSatStep restSystem (hornSatApplyClause clause trueSet)).length
                = trueSet.length + Nat.succ (Nat.succ restDelta)
              rw [hRestLen, hApplyGrow, hornSatNatSuccAdd]
              rfl

/-- A pass preserves duplicate-freedom. -/
theorem hornSatStepKeepsDistinct : (system : List HornSatClause) → (trueSet : List Nat) →
    hornSatIsDistinct trueSet = true → hornSatIsDistinct (hornSatStep system trueSet) = true
  | [], _, hdistinct => hdistinct
  | clause :: restSystem, trueSet, hdistinct =>
      hornSatStepKeepsDistinct restSystem (hornSatApplyClause clause trueSet)
        (hornSatApplyKeepsDistinct clause trueSet hdistinct)

/-- A pass preserves strict ascent. -/
theorem hornSatStepKeepsAscending : (system : List HornSatClause) → (trueSet : List Nat) →
    hornSatIsAscending trueSet = true → hornSatIsAscending (hornSatStep system trueSet) = true
  | [], _, hascending => hascending
  | clause :: restSystem, trueSet, hascending =>
      hornSatStepKeepsAscending restSystem (hornSatApplyClause clause trueSet)
        (hornSatApplyKeepsAscending clause trueSet hascending)

/-! ## The head pool -/

/-- One head-collection step, keyed by the head option. -/
def hornSatHeadsListStep (headOption : Option Nat) (restHeads : List Nat) : List Nat :=
  match headOption with
  | some headAtom => headAtom :: restHeads
  | none => restHeads

/-- All heads of a system (with multiplicity; the pigeonhole tolerates duplicates). -/
def hornSatHeadsList : List HornSatClause → List Nat
  | [] => []
  | clause :: restSystem => hornSatHeadsListStep clause.head (hornSatHeadsList restSystem)

/-- Every positive clause's head is in the head pool. -/
theorem hornSatHeadsListCovers : (system : List HornSatClause) →
    (clauseBody : List Nat) → (headAtom : Nat) →
    HornSatClauseIn ⟨clauseBody, some headAtom⟩ system →
    hornSatMember (hornSatHeadsList system) headAtom = true
  | [], _, _, hInSystem => nomatch hInSystem
  | clause :: restSystem, clauseBody, headAtom, hInSystem => by
      cases hInSystem with
      | here _ =>
          exact hornSatMemberHead headAtom (hornSatHeadsList restSystem)
      | there _ _ hInRest =>
          cases hHeadProbe : clause.head with
          | some listedHead =>
              have hUnfolded : hornSatHeadsList (clause :: restSystem)
                  = listedHead :: hornSatHeadsList restSystem := by
                show hornSatHeadsListStep clause.head (hornSatHeadsList restSystem)
                  = listedHead :: hornSatHeadsList restSystem
                rw [hHeadProbe]
                rfl
              rw [hUnfolded]
              exact hornSatMemberTail listedHead headAtom (hornSatHeadsList restSystem)
                (hornSatHeadsListCovers restSystem clauseBody headAtom hInRest)
          | none =>
              have hUnfolded : hornSatHeadsList (clause :: restSystem)
                  = hornSatHeadsList restSystem := by
                show hornSatHeadsListStep clause.head (hornSatHeadsList restSystem)
                  = hornSatHeadsList restSystem
                rw [hHeadProbe]
                rfl
              rw [hUnfolded]
              exact hornSatHeadsListCovers restSystem clauseBody headAtom hInRest

/-- A pass keeps the truth set inside any pool that covers the sub-system's heads. -/
theorem hornSatStepStaysWithin : (subSystem : List HornSatClause) →
    (trueSet poolList : List Nat) →
    ((clauseBody : List Nat) → (headAtom : Nat) →
      HornSatClauseIn ⟨clauseBody, some headAtom⟩ subSystem →
      hornSatMember poolList headAtom = true) →
    ((atom : Nat) → hornSatMember trueSet atom = true → hornSatMember poolList atom = true) →
    (atom : Nat) → hornSatMember (hornSatStep subSystem trueSet) atom = true →
    hornSatMember poolList atom = true
  | [], _trueSet, _poolList, _hheads, hwithin, atom, hmember => hwithin atom hmember
  | ⟨clauseBody, clauseHead⟩ :: restSystem, trueSet, poolList, hheads, hwithin, atom,
      hmember => by
      have hApplyWithin : (probeAtom : Nat) →
          hornSatMember (hornSatApplyClause ⟨clauseBody, clauseHead⟩ trueSet) probeAtom = true →
          hornSatMember poolList probeAtom = true := by
        intro probeAtom hprobe
        cases clauseHead with
        | none => exact hwithin probeAtom hprobe
        | some headAtom =>
            have hProbeRetyped : hornSatMember (cond (hornSatBodyHolds trueSet clauseBody)
                (hornSatInsert headAtom trueSet) trueSet) probeAtom = true := hprobe
            cases hbody : hornSatBodyHolds trueSet clauseBody with
            | false =>
                rw [hbody] at hProbeRetyped
                exact hwithin probeAtom hProbeRetyped
            | true =>
                rw [hbody] at hProbeRetyped
                rcases hornSatInsertMemberInversion headAtom probeAtom trueSet hProbeRetyped
                  with hEqHead | hInPrior
                · rw [hEqHead]
                  exact hheads clauseBody headAtom (HornSatClauseIn.here _ _)
                · exact hwithin probeAtom hInPrior
      exact hornSatStepStaysWithin restSystem
        (hornSatApplyClause ⟨clauseBody, clauseHead⟩ trueSet) poolList
        (fun goalBody goalHead hInRest =>
          hheads goalBody goalHead (HornSatClauseIn.there _ _ _ hInRest))
        hApplyWithin atom hmember

/-- A pass delivers the head of any fired positive clause of the system. -/
theorem hornSatStepDeliversHead : (system : List HornSatClause) → (trueSet : List Nat) →
    (clauseBody : List Nat) → (headAtom : Nat) →
    HornSatClauseIn ⟨clauseBody, some headAtom⟩ system →
    hornSatBodyHolds trueSet clauseBody = true →
    hornSatMember (hornSatStep system trueSet) headAtom = true
  | [], _, _, _, hInSystem, _ => nomatch hInSystem
  | clause :: restSystem, trueSet, clauseBody, headAtom, hInSystem, hbody => by
      cases hInSystem with
      | here _ =>
          have hApplyIsInsert : hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet
              = hornSatInsert headAtom trueSet := by
            show cond (hornSatBodyHolds trueSet clauseBody)
              (hornSatInsert headAtom trueSet) trueSet = hornSatInsert headAtom trueSet
            rw [hbody]
            rfl
          show hornSatMember (hornSatStep restSystem
            (hornSatApplyClause ⟨clauseBody, some headAtom⟩ trueSet)) headAtom = true
          rw [hApplyIsInsert]
          exact hornSatStepPreservesMembers restSystem (hornSatInsert headAtom trueSet)
            headAtom (hornSatInsertMakesMember headAtom trueSet)
      | there _ _ hInRest =>
          exact hornSatStepDeliversHead restSystem
            (hornSatApplyClause clause trueSet) clauseBody headAtom hInRest
            (hornSatBodyHoldsMonotone clauseBody trueSet
              (hornSatApplyClause clause trueSet)
              (fun atom hmember => hornSatApplyPreservesMembers clause trueSet atom hmember)
              hbody)

/-! ## Truth-set comparison (stabilization detector) -/

/-- Hand-rolled `Bool` equality of truth sets. -/
def hornSatTrueSetBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _rightHead :: _rightTail => false
  | _leftHead :: _leftTail, [] => false
  | leftHead :: leftTail, rightHead :: rightTail =>
      Nat.beq leftHead rightHead && hornSatTrueSetBeq leftTail rightTail

/-- The comparator is reflexive. -/
theorem hornSatTrueSetBeqSelf : (trueSet : List Nat) →
    hornSatTrueSetBeq trueSet trueSet = true
  | [] => rfl
  | headAtom :: tail => by
      show (Nat.beq headAtom headAtom && hornSatTrueSetBeq tail tail) = true
      rw [hornSatNatBeqSelf, hornSatTrueSetBeqSelf tail]
      rfl

/-- A true comparison certifies list equality. -/
theorem hornSatTrueSetBeqImpliesEq : (leftSet rightSet : List Nat) →
    hornSatTrueSetBeq leftSet rightSet = true → leftSet = rightSet
  | [], [], _ => rfl
  | [], _rightHead :: _rightTail, hbeq => Bool.noConfusion hbeq
  | _leftHead :: _leftTail, [], hbeq => Bool.noConfusion hbeq
  | leftHead :: leftTail, rightHead :: rightTail, hbeq => by
      have hsplit := hornSatAndSplit _ _ hbeq
      rw [Nat.eq_of_beq_eq_true hsplit.1,
        hornSatTrueSetBeqImpliesEq leftTail rightTail hsplit.2]

/-! ## Saturation under structural fuel -/

/-- Iterate `hornSatStep` until a pass changes nothing, bounded by structural fuel. -/
def hornSatSaturate (fuel : Nat) (system : List HornSatClause)
    (trueSet : List Nat) : List Nat :=
  match fuel with
  | 0 => trueSet
  | Nat.succ remainingFuel =>
      cond (hornSatTrueSetBeq (hornSatStep system trueSet) trueSet)
        trueSet
        (hornSatSaturate remainingFuel system (hornSatStep system trueSet))

/-- Saturation unfold: a stable pass returns the set. -/
theorem hornSatSaturateSuccOfStable (remainingFuel : Nat) (system : List HornSatClause)
    (trueSet : List Nat)
    (hstable : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet = true) :
    hornSatSaturate (Nat.succ remainingFuel) system trueSet = trueSet := by
  show cond (hornSatTrueSetBeq (hornSatStep system trueSet) trueSet) trueSet
    (hornSatSaturate remainingFuel system (hornSatStep system trueSet)) = trueSet
  rw [hstable]
  rfl

/-- Saturation unfold: a changing pass recurses on the stepped set. -/
theorem hornSatSaturateSuccOfChanged (remainingFuel : Nat) (system : List HornSatClause)
    (trueSet : List Nat)
    (hchanged : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet = false) :
    hornSatSaturate (Nat.succ remainingFuel) system trueSet
      = hornSatSaturate remainingFuel system (hornSatStep system trueSet) := by
  show cond (hornSatTrueSetBeq (hornSatStep system trueSet) trueSet) trueSet
    (hornSatSaturate remainingFuel system (hornSatStep system trueSet))
    = hornSatSaturate remainingFuel system (hornSatStep system trueSet)
  rw [hchanged]
  rfl

/-- Saturation preserves duplicate-freedom. -/
theorem hornSatSaturateKeepsDistinct : (fuel : Nat) → (system : List HornSatClause) →
    (trueSet : List Nat) → hornSatIsDistinct trueSet = true →
    hornSatIsDistinct (hornSatSaturate fuel system trueSet) = true
  | 0, _, _, hdistinct => hdistinct
  | Nat.succ remainingFuel, system, trueSet, hdistinct => by
      cases hchanged : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet with
      | true =>
          rw [hornSatSaturateSuccOfStable remainingFuel system trueSet hchanged]
          exact hdistinct
      | false =>
          rw [hornSatSaturateSuccOfChanged remainingFuel system trueSet hchanged]
          exact hornSatSaturateKeepsDistinct remainingFuel system
            (hornSatStep system trueSet) (hornSatStepKeepsDistinct system trueSet hdistinct)

/-- Saturation preserves strict ascent. -/
theorem hornSatSaturateKeepsAscending : (fuel : Nat) → (system : List HornSatClause) →
    (trueSet : List Nat) → hornSatIsAscending trueSet = true →
    hornSatIsAscending (hornSatSaturate fuel system trueSet) = true
  | 0, _, _, hascending => hascending
  | Nat.succ remainingFuel, system, trueSet, hascending => by
      cases hchanged : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet with
      | true =>
          rw [hornSatSaturateSuccOfStable remainingFuel system trueSet hchanged]
          exact hascending
      | false =>
          rw [hornSatSaturateSuccOfChanged remainingFuel system trueSet hchanged]
          exact hornSatSaturateKeepsAscending remainingFuel system
            (hornSatStep system trueSet) (hornSatStepKeepsAscending system trueSet hascending)

/-- **Fuel adequacy.**  Under the pigeonhole bound — the truth set is duplicate-free, lies
inside the head pool, and `succ (pool length) ≤ set length + fuel` — saturation reaches a
genuine fixpoint of `hornSatStep`. -/
theorem hornSatSaturateReachesFixpoint : (fuel : Nat) → (system : List HornSatClause) →
    (trueSet : List Nat) →
    hornSatIsDistinct trueSet = true →
    ((atom : Nat) → hornSatMember trueSet atom = true →
      hornSatMember (hornSatHeadsList system) atom = true) →
    hornSatNatLe (Nat.succ (hornSatHeadsList system).length) (trueSet.length + fuel) →
    hornSatStep system (hornSatSaturate fuel system trueSet)
      = hornSatSaturate fuel system trueSet
  | 0, system, trueSet, hdistinct, hwithin, hbound => by
      have hBoundNoFuel : hornSatNatLe (Nat.succ (hornSatHeadsList system).length)
          trueSet.length := hbound
      have hcap : hornSatNatLe trueSet.length (hornSatHeadsList system).length :=
        hornSatDistinctWithinLength trueSet (hornSatHeadsList system) hdistinct hwithin
      exact False.elim (hornSatNatLeSuccSelfFalse (hornSatHeadsList system).length
        (hornSatNatLeTrans (Nat.succ (hornSatHeadsList system).length) trueSet.length
          (hornSatHeadsList system).length hBoundNoFuel hcap))
  | Nat.succ remainingFuel, system, trueSet, hdistinct, hwithin, hbound => by
      cases hchanged : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet with
      | true =>
          rw [hornSatSaturateSuccOfStable remainingFuel system trueSet hchanged]
          exact hornSatTrueSetBeqImpliesEq (hornSatStep system trueSet) trueSet hchanged
      | false =>
          rw [hornSatSaturateSuccOfChanged remainingFuel system trueSet hchanged]
          have hDistinctNext : hornSatIsDistinct (hornSatStep system trueSet) = true :=
            hornSatStepKeepsDistinct system trueSet hdistinct
          have hWithinNext : (atom : Nat) →
              hornSatMember (hornSatStep system trueSet) atom = true →
              hornSatMember (hornSatHeadsList system) atom = true :=
            hornSatStepStaysWithin system trueSet (hornSatHeadsList system)
              (hornSatHeadsListCovers system) hwithin
          cases hornSatStepGrowsOrFixes system trueSet with
          | inl hStepFix =>
              have hStable : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet = true := by
                rw [hStepFix]
                exact hornSatTrueSetBeqSelf trueSet
              rw [hStable] at hchanged
              exact Bool.noConfusion hchanged
          | inr hStepGrow =>
              rcases hStepGrow with ⟨growthDelta, hGrowLen⟩
              have hBoundNext : hornSatNatLe (Nat.succ (hornSatHeadsList system).length)
                  ((hornSatStep system trueSet).length + remainingFuel) := by
                rw [hGrowLen, Nat.add_assoc, hornSatNatSuccAdd]
                exact hornSatNatLeTrans (Nat.succ (hornSatHeadsList system).length)
                  (trueSet.length + Nat.succ remainingFuel)
                  (trueSet.length + Nat.succ (growthDelta + remainingFuel))
                  hbound
                  (hornSatNatLeAddLeft trueSet.length (Nat.succ remainingFuel)
                    (Nat.succ (growthDelta + remainingFuel))
                    (hornSatNatLeSucc remainingFuel (growthDelta + remainingFuel)
                      ⟨growthDelta, Nat.add_comm growthDelta remainingFuel⟩))
              exact hornSatSaturateReachesFixpoint remainingFuel system
                (hornSatStep system trueSet) hDistinctNext hWithinNext hBoundNext

/-! ## The least model -/

/-- The least model: saturate from the empty set with proven-adequate fuel. -/
def hornSatLeastModel (system : List HornSatClause) : List Nat :=
  hornSatSaturate (Nat.succ (hornSatHeadsList system).length) system []

/-- The least model is a genuine fixpoint of the one-pass operator. -/
theorem hornSatLeastModelIsFixpoint (system : List HornSatClause) :
    hornSatStep system (hornSatLeastModel system) = hornSatLeastModel system :=
  hornSatSaturateReachesFixpoint (Nat.succ (hornSatHeadsList system).length) system []
    rfl
    (fun _atom hcontr => Bool.noConfusion hcontr)
    ⟨0, Nat.zero_add (Nat.succ (hornSatHeadsList system).length)⟩

/-- The least model is duplicate-free. -/
theorem hornSatLeastModelIsDistinct (system : List HornSatClause) :
    hornSatIsDistinct (hornSatLeastModel system) = true :=
  hornSatSaturateKeepsDistinct (Nat.succ (hornSatHeadsList system).length) system [] rfl

/-- The least model is strictly ascending. -/
theorem hornSatLeastModelIsAscending (system : List HornSatClause) :
    hornSatIsAscending (hornSatLeastModel system) = true :=
  hornSatSaturateKeepsAscending (Nat.succ (hornSatHeadsList system).length) system [] rfl

/-- **Closure.**  At the least model, every fired positive clause has its head in the set. -/
theorem hornSatLeastModelIsClosed (system : List HornSatClause)
    (clauseBody : List Nat) (headAtom : Nat)
    (hInSystem : HornSatClauseIn ⟨clauseBody, some headAtom⟩ system)
    (hbody : hornSatBodyHolds (hornSatLeastModel system) clauseBody = true) :
    hornSatMember (hornSatLeastModel system) headAtom = true := by
  have hDelivered : hornSatMember (hornSatStep system (hornSatLeastModel system))
      headAtom = true :=
    hornSatStepDeliversHead system (hornSatLeastModel system) clauseBody headAtom
      hInSystem hbody
  rw [hornSatLeastModelIsFixpoint system] at hDelivered
  exact hDelivered

/-! ## Functional (environment) semantics -/

/-- Does an environment make every body atom true? -/
def hornSatEnvBodyHolds (environment : Nat → Bool) : List Nat → Bool
  | [] => true
  | atom :: restBody => environment atom && hornSatEnvBodyHolds environment restBody

/-- Does an environment make a head true (`none` is falsity)? -/
def hornSatEnvHeadHolds (environment : Nat → Bool) (headOption : Option Nat) : Bool :=
  match headOption with
  | some headAtom => environment headAtom
  | none => false

/-- Does an environment satisfy one clause (fired body forces the head)? -/
def hornSatEnvClauseHolds (environment : Nat → Bool) (clause : HornSatClause) : Bool :=
  cond (hornSatEnvBodyHolds environment clause.body)
    (hornSatEnvHeadHolds environment clause.head) true

/-- Does an environment satisfy every clause of a system? -/
def hornSatEnvSatisfiesAll (environment : Nat → Bool) : List HornSatClause → Bool
  | [] => true
  | clause :: restSystem =>
      hornSatEnvClauseHolds environment clause
        && hornSatEnvSatisfiesAll environment restSystem

/-- A satisfying environment satisfies every listed clause. -/
theorem hornSatEnvSatisfiesAllExtract : (system : List HornSatClause) →
    (environment : Nat → Bool) →
    hornSatEnvSatisfiesAll environment system = true →
    (clause : HornSatClause) → HornSatClauseIn clause system →
    hornSatEnvClauseHolds environment clause = true
  | [], _, _, _, hInSystem => nomatch hInSystem
  | listedClause :: restSystem, environment, hall, clause, hInSystem => by
      have hAllUnfolded : (hornSatEnvClauseHolds environment listedClause
          && hornSatEnvSatisfiesAll environment restSystem) = true := hall
      have hsplit := hornSatAndSplit _ _ hAllUnfolded
      cases hInSystem with
      | here _ => exact hsplit.1
      | there _ _ hInRest =>
          exact hornSatEnvSatisfiesAllExtract restSystem environment hsplit.2 clause hInRest

/-- Lift set-level body satisfaction through a member-dominating environment. -/
theorem hornSatBodyHoldsLift : (body : List Nat) → (trueSet : List Nat) →
    (environment : Nat → Bool) →
    ((atom : Nat) → hornSatMember trueSet atom = true → environment atom = true) →
    hornSatBodyHolds trueSet body = true → hornSatEnvBodyHolds environment body = true
  | [], _, _, _, _ => rfl
  | atom :: restBody, trueSet, environment, hbound, hholds => by
      have hUnfolded : (hornSatMember trueSet atom
          && hornSatBodyHolds trueSet restBody) = true := hholds
      have hsplit := hornSatAndSplit _ _ hUnfolded
      show (environment atom && hornSatEnvBodyHolds environment restBody) = true
      rw [hbound atom hsplit.1,
        hornSatBodyHoldsLift restBody trueSet environment hbound hsplit.2]
      rfl

/-- A satisfied positive clause with a fired body forces its head in the environment. -/
theorem hornSatEnvClauseHeadTrue (environment : Nat → Bool) (clauseBody : List Nat)
    (headAtom : Nat)
    (hEnvBody : hornSatEnvBodyHolds environment clauseBody = true)
    (hEnvClause : hornSatEnvClauseHolds environment ⟨clauseBody, some headAtom⟩ = true) :
    environment headAtom = true := by
  have hUnfolded : cond (hornSatEnvBodyHolds environment clauseBody)
      (environment headAtom) true = true := hEnvClause
  rw [hEnvBody] at hUnfolded
  exact hUnfolded

/-- A satisfied goal clause with a fired body is absurd. -/
theorem hornSatEnvClauseGoalRefutes (environment : Nat → Bool) (clauseBody : List Nat)
    (hEnvBody : hornSatEnvBodyHolds environment clauseBody = true)
    (hEnvClause : hornSatEnvClauseHolds environment ⟨clauseBody, none⟩ = true) : False := by
  have hUnfolded : cond (hornSatEnvBodyHolds environment clauseBody) false true = true :=
    hEnvClause
  rw [hEnvBody] at hUnfolded
  exact Bool.noConfusion hUnfolded

/-! ## Minimality of the least model -/

/-- Clause application keeps the truth set below any satisfying environment. -/
theorem hornSatApplyKeepsEnvBound : (clauseBody : List Nat) → (clauseHead : Option Nat) →
    (trueSet : List Nat) → (environment : Nat → Bool) →
    hornSatEnvClauseHolds environment ⟨clauseBody, clauseHead⟩ = true →
    ((atom : Nat) → hornSatMember trueSet atom = true → environment atom = true) →
    (atom : Nat) →
    hornSatMember (hornSatApplyClause ⟨clauseBody, clauseHead⟩ trueSet) atom = true →
    environment atom = true
  | _clauseBody, none, _, _, _, hbound, atom, hmember => hbound atom hmember
  | clauseBody, some headAtom, trueSet, environment, hEnvClause, hbound, atom, hmember => by
      have hMemberRetyped : hornSatMember (cond (hornSatBodyHolds trueSet clauseBody)
          (hornSatInsert headAtom trueSet) trueSet) atom = true := hmember
      cases hbody : hornSatBodyHolds trueSet clauseBody with
      | false =>
          rw [hbody] at hMemberRetyped
          exact hbound atom hMemberRetyped
      | true =>
          rw [hbody] at hMemberRetyped
          rcases hornSatInsertMemberInversion headAtom atom trueSet hMemberRetyped
            with hEqHead | hInPrior
          · rw [hEqHead]
            exact hornSatEnvClauseHeadTrue environment clauseBody headAtom
              (hornSatBodyHoldsLift clauseBody trueSet environment hbound hbody) hEnvClause
          · exact hbound atom hInPrior

/-- A pass keeps the truth set below any satisfying environment. -/
theorem hornSatStepKeepsEnvBound : (system : List HornSatClause) → (trueSet : List Nat) →
    (environment : Nat → Bool) →
    hornSatEnvSatisfiesAll environment system = true →
    ((atom : Nat) → hornSatMember trueSet atom = true → environment atom = true) →
    (atom : Nat) → hornSatMember (hornSatStep system trueSet) atom = true →
    environment atom = true
  | [], _, _, _, hbound, atom, hmember => hbound atom hmember
  | ⟨clauseBody, clauseHead⟩ :: restSystem, trueSet, environment, hall, hbound, atom,
      hmember => by
      have hAllUnfolded : (hornSatEnvClauseHolds environment ⟨clauseBody, clauseHead⟩
          && hornSatEnvSatisfiesAll environment restSystem) = true := hall
      have hsplit := hornSatAndSplit _ _ hAllUnfolded
      exact hornSatStepKeepsEnvBound restSystem
        (hornSatApplyClause ⟨clauseBody, clauseHead⟩ trueSet) environment hsplit.2
        (hornSatApplyKeepsEnvBound clauseBody clauseHead trueSet environment
          hsplit.1 hbound)
        atom hmember

/-- Saturation keeps the truth set below any satisfying environment. -/
theorem hornSatSaturateKeepsEnvBound : (fuel : Nat) → (system : List HornSatClause) →
    (trueSet : List Nat) → (environment : Nat → Bool) →
    hornSatEnvSatisfiesAll environment system = true →
    ((atom : Nat) → hornSatMember trueSet atom = true → environment atom = true) →
    (atom : Nat) → hornSatMember (hornSatSaturate fuel system trueSet) atom = true →
    environment atom = true
  | 0, _, _, _, _, hbound, atom, hmember => hbound atom hmember
  | Nat.succ remainingFuel, system, trueSet, environment, hall, hbound, atom, hmember => by
      cases hchanged : hornSatTrueSetBeq (hornSatStep system trueSet) trueSet with
      | true =>
          rw [hornSatSaturateSuccOfStable remainingFuel system trueSet hchanged] at hmember
          exact hbound atom hmember
      | false =>
          rw [hornSatSaturateSuccOfChanged remainingFuel system trueSet hchanged] at hmember
          exact hornSatSaturateKeepsEnvBound remainingFuel system
            (hornSatStep system trueSet) environment hall
            (hornSatStepKeepsEnvBound system trueSet environment hall hbound) atom hmember

/-- **Minimality.**  Every member of the least model is true in EVERY satisfying
environment. -/
theorem hornSatLeastModelIsMinimal (system : List HornSatClause)
    (environment : Nat → Bool)
    (hall : hornSatEnvSatisfiesAll environment system = true)
    (atom : Nat) (hmember : hornSatMember (hornSatLeastModel system) atom = true) :
    environment atom = true :=
  hornSatSaturateKeepsEnvBound (Nat.succ (hornSatHeadsList system).length) system []
    environment hall (fun _probeAtom hcontr => Bool.noConfusion hcontr) atom hmember

/-! ## The executable model checker and its agreement with environment evaluation -/

/-- Does the truth set make a head true (`none` is falsity)? -/
def hornSatSetHeadHolds (trueSet : List Nat) (headOption : Option Nat) : Bool :=
  match headOption with
  | some headAtom => hornSatMember trueSet headAtom
  | none => false

/-- Does the truth set satisfy one clause? -/
def hornSatClauseHoldsIn (trueSet : List Nat) (clause : HornSatClause) : Bool :=
  cond (hornSatBodyHolds trueSet clause.body)
    (hornSatSetHeadHolds trueSet clause.head) true

/-- Executable model checker: does the truth set satisfy every clause? -/
def hornSatCheckModel (trueSet : List Nat) : List HornSatClause → Bool
  | [] => true
  | clause :: restSystem =>
      hornSatClauseHoldsIn trueSet clause && hornSatCheckModel trueSet restSystem

/-- Body evaluation under the induced environment agrees with the set-level check. -/
theorem hornSatEnvBodyHoldsInduced : (trueSet body : List Nat) →
    hornSatEnvBodyHolds (fun probeAtom => hornSatMember trueSet probeAtom) body
      = hornSatBodyHolds trueSet body
  | _trueSet, [] => rfl
  | trueSet, atom :: restBody =>
      congrArg (fun restFlag => hornSatMember trueSet atom && restFlag)
        (hornSatEnvBodyHoldsInduced trueSet restBody)

/-- Head evaluation under the induced environment agrees with the set-level check. -/
theorem hornSatEnvHeadHoldsInduced : (trueSet : List Nat) → (headOption : Option Nat) →
    hornSatEnvHeadHolds (fun probeAtom => hornSatMember trueSet probeAtom) headOption
      = hornSatSetHeadHolds trueSet headOption
  | _trueSet, some _headAtom => rfl
  | _trueSet, none => rfl

/-- Clause evaluation under the induced environment agrees with the checker. -/
theorem hornSatClauseHoldsInduced (trueSet : List Nat) (clause : HornSatClause) :
    hornSatEnvClauseHolds (fun probeAtom => hornSatMember trueSet probeAtom) clause
      = hornSatClauseHoldsIn trueSet clause := by
  show cond (hornSatEnvBodyHolds (fun probeAtom => hornSatMember trueSet probeAtom)
      clause.body)
    (hornSatEnvHeadHolds (fun probeAtom => hornSatMember trueSet probeAtom) clause.head) true
    = cond (hornSatBodyHolds trueSet clause.body)
      (hornSatSetHeadHolds trueSet clause.head) true
  rw [hornSatEnvBodyHoldsInduced trueSet clause.body,
    hornSatEnvHeadHoldsInduced trueSet clause.head]

/-- **Checker–evaluator agreement.**  Environment evaluation under the induced environment
IS the executable checker. -/
theorem hornSatCheckModelInduced : (trueSet : List Nat) → (system : List HornSatClause) →
    hornSatEnvSatisfiesAll (fun probeAtom => hornSatMember trueSet probeAtom) system
      = hornSatCheckModel trueSet system
  | _trueSet, [] => rfl
  | trueSet, clause :: restSystem => by
      show (hornSatEnvClauseHolds (fun probeAtom => hornSatMember trueSet probeAtom) clause
          && hornSatEnvSatisfiesAll (fun probeAtom => hornSatMember trueSet probeAtom)
            restSystem)
        = (hornSatClauseHoldsIn trueSet clause && hornSatCheckModel trueSet restSystem)
      rw [hornSatClauseHoldsInduced trueSet clause,
        hornSatCheckModelInduced trueSet restSystem]

/-- The checker passes when every listed clause passes. -/
theorem hornSatCheckModelOfAll : (system : List HornSatClause) → (trueSet : List Nat) →
    ((clause : HornSatClause) → HornSatClauseIn clause system →
      hornSatClauseHoldsIn trueSet clause = true) →
    hornSatCheckModel trueSet system = true
  | [], _, _ => rfl
  | clause :: restSystem, trueSet, hall => by
      show (hornSatClauseHoldsIn trueSet clause && hornSatCheckModel trueSet restSystem) = true
      rw [hall clause (HornSatClauseIn.here _ _),
        hornSatCheckModelOfAll restSystem trueSet
          (fun probeClause hInRest => hall probeClause (HornSatClauseIn.there _ _ _ hInRest))]
      rfl

/-! ## The decision procedure -/

/-- One scan step: positive clauses are skipped; a goal clause fires when its body holds. -/
def hornSatScanStep (headOption : Option Nat) (bodyFires : Bool) (currentIndex : Nat)
    (restScan : Option Nat) : Option Nat :=
  match headOption with
  | some _headAtom => restScan
  | none => cond bodyFires (some currentIndex) restScan

/-- Scan for the first goal clause whose body holds in the fixed set. -/
def hornSatFindViolatedGoal (fixedSet : List Nat) :
    List HornSatClause → Nat → Option Nat
  | [], _currentIndex => none
  | clause :: restSystem, currentIndex =>
      hornSatScanStep clause.head (hornSatBodyHolds fixedSet clause.body) currentIndex
        (hornSatFindViolatedGoal fixedSet restSystem (currentIndex + 1))

/-- A clean scan means no goal clause fires. -/
theorem hornSatFindNoneMeansGoalsIdle : (system : List HornSatClause) →
    (fixedSet : List Nat) → (currentIndex : Nat) →
    hornSatFindViolatedGoal fixedSet system currentIndex = none →
    (goalBody : List Nat) → HornSatClauseIn ⟨goalBody, none⟩ system →
    hornSatBodyHolds fixedSet goalBody = false
  | [], _, _, _, _, hInSystem => nomatch hInSystem
  | clause :: restSystem, fixedSet, currentIndex, hscan, goalBody, hInSystem => by
      cases hInSystem with
      | here _ =>
          have hCondScan : cond (hornSatBodyHolds fixedSet goalBody) (some currentIndex)
              (hornSatFindViolatedGoal fixedSet restSystem (currentIndex + 1)) = none := hscan
          cases hbody : hornSatBodyHolds fixedSet goalBody with
          | false => rfl
          | true =>
              rw [hbody] at hCondScan
              have hSomeIsNone : some currentIndex = (none : Option Nat) := hCondScan
              exact nomatch hSomeIsNone
      | there _ _ hInRest =>
          have hScanUnfolded : hornSatScanStep clause.head
              (hornSatBodyHolds fixedSet clause.body) currentIndex
              (hornSatFindViolatedGoal fixedSet restSystem (currentIndex + 1)) = none := hscan
          cases hHeadProbe : clause.head with
          | some _listedHead =>
              rw [hHeadProbe] at hScanUnfolded
              exact hornSatFindNoneMeansGoalsIdle restSystem fixedSet (currentIndex + 1)
                hScanUnfolded goalBody hInRest
          | none =>
              rw [hHeadProbe] at hScanUnfolded
              cases hbody : hornSatBodyHolds fixedSet clause.body with
              | true =>
                  rw [hbody] at hScanUnfolded
                  have hSomeIsNone : some currentIndex = (none : Option Nat) := hScanUnfolded
                  exact nomatch hSomeIsNone
              | false =>
                  rw [hbody] at hScanUnfolded
                  exact hornSatFindNoneMeansGoalsIdle restSystem fixedSet (currentIndex + 1)
                    hScanUnfolded goalBody hInRest

/-- A hit scan pins a listed goal clause whose body holds. -/
theorem hornSatFindSomeMeansGoalFired : (system : List HornSatClause) →
    (fixedSet : List Nat) → (currentIndex foundIndex : Nat) →
    hornSatFindViolatedGoal fixedSet system currentIndex = some foundIndex →
    ∃ goalBody, HornSatClauseIn ⟨goalBody, none⟩ system ∧
      hornSatBodyHolds fixedSet goalBody = true
  | [], fixedSet, currentIndex, foundIndex, hscan =>
      nomatch (show (none : Option Nat) = some foundIndex from hscan)
  | ⟨clauseBody, clauseHead⟩ :: restSystem, fixedSet, currentIndex, foundIndex, hscan => by
      cases clauseHead with
      | some _listedHead =>
          have hRestScan : hornSatFindViolatedGoal fixedSet restSystem (currentIndex + 1)
              = some foundIndex := hscan
          rcases hornSatFindSomeMeansGoalFired restSystem fixedSet (currentIndex + 1)
            foundIndex hRestScan with ⟨goalBody, hInRest, hfired⟩
          exact ⟨goalBody, HornSatClauseIn.there _ _ _ hInRest, hfired⟩
      | none =>
          have hCondScan : cond (hornSatBodyHolds fixedSet clauseBody) (some currentIndex)
              (hornSatFindViolatedGoal fixedSet restSystem (currentIndex + 1))
              = some foundIndex := hscan
          cases hbody : hornSatBodyHolds fixedSet clauseBody with
          | true =>
              exact ⟨clauseBody, HornSatClauseIn.here _ _, hbody⟩
          | false =>
              rw [hbody] at hCondScan
              rcases hornSatFindSomeMeansGoalFired restSystem fixedSet (currentIndex + 1)
                foundIndex hCondScan with ⟨goalBody, hInRest, hfired⟩
              exact ⟨goalBody, HornSatClauseIn.there _ _ _ hInRest, hfired⟩

/-- The decision verdict: the least model, or a fired goal clause index plus the
saturated set. -/
inductive HornSatVerdict where
  | isSatisfiable (leastModelSet : List Nat)
  | isUnsatisfiable (goalIndex : Nat) (saturatedSet : List Nat)

/-- Package a scan result as a verdict. -/
def hornSatVerdictOfScan (leastModelSet : List Nat) (scanResult : Option Nat) :
    HornSatVerdict :=
  match scanResult with
  | some goalIndex => HornSatVerdict.isUnsatisfiable goalIndex leastModelSet
  | none => HornSatVerdict.isSatisfiable leastModelSet

/-- **The decider.**  Saturate from the empty set; report a fired goal clause if any,
otherwise the least model. -/
def hornSatDecide (system : List HornSatClause) : HornSatVerdict :=
  hornSatVerdictOfScan (hornSatLeastModel system)
    (hornSatFindViolatedGoal (hornSatLeastModel system) system 0)

/-- Is the verdict satisfiable? -/
def hornSatVerdictIsSatisfiable : HornSatVerdict → Bool
  | HornSatVerdict.isSatisfiable _leastModelSet => true
  | HornSatVerdict.isUnsatisfiable _goalIndex _saturatedSet => false

/-- The verdict's carried truth set (least model, or the saturated set). -/
def hornSatVerdictWitnessSet : HornSatVerdict → List Nat
  | HornSatVerdict.isSatisfiable leastModelSet => leastModelSet
  | HornSatVerdict.isUnsatisfiable _goalIndex saturatedSet => saturatedSet

/-- The verdict's fired goal clause index, if unsatisfiable. -/
def hornSatVerdictGoalIndex : HornSatVerdict → Option Nat
  | HornSatVerdict.isSatisfiable _leastModelSet => none
  | HornSatVerdict.isUnsatisfiable goalIndex _saturatedSet => some goalIndex

/-- A satisfiable verdict carries exactly the least model. -/
theorem hornSatDecideSatisfiableGivesLeastModel (system : List HornSatClause)
    (modelSet : List Nat)
    (hdecide : hornSatDecide system = HornSatVerdict.isSatisfiable modelSet) :
    modelSet = hornSatLeastModel system := by
  cases hscan : hornSatFindViolatedGoal (hornSatLeastModel system) system 0 with
  | some foundIndex =>
      have hDecideUnfolded : hornSatVerdictOfScan (hornSatLeastModel system)
          (hornSatFindViolatedGoal (hornSatLeastModel system) system 0)
          = HornSatVerdict.isSatisfiable modelSet := hdecide
      rw [hscan] at hDecideUnfolded
      exact HornSatVerdict.noConfusion hDecideUnfolded
  | none =>
      have hDecideUnfolded : hornSatVerdictOfScan (hornSatLeastModel system)
          (hornSatFindViolatedGoal (hornSatLeastModel system) system 0)
          = HornSatVerdict.isSatisfiable modelSet := hdecide
      rw [hscan] at hDecideUnfolded
      exact (HornSatVerdict.isSatisfiable.inj hDecideUnfolded).symm

/-- **SAT soundness.**  A satisfiable verdict's model passes the executable checker. -/
theorem hornSatDecideSatisfiableGivesModel (system : List HornSatClause)
    (modelSet : List Nat)
    (hdecide : hornSatDecide system = HornSatVerdict.isSatisfiable modelSet) :
    hornSatCheckModel modelSet system = true := by
  cases hscan : hornSatFindViolatedGoal (hornSatLeastModel system) system 0 with
  | some foundIndex =>
      have hDecideUnfolded : hornSatVerdictOfScan (hornSatLeastModel system)
          (hornSatFindViolatedGoal (hornSatLeastModel system) system 0)
          = HornSatVerdict.isSatisfiable modelSet := hdecide
      rw [hscan] at hDecideUnfolded
      exact HornSatVerdict.noConfusion hDecideUnfolded
  | none =>
      rw [hornSatDecideSatisfiableGivesLeastModel system modelSet hdecide]
      apply hornSatCheckModelOfAll
      intro clause hInSystem
      cases clause with
      | mk clauseBody clauseHead =>
          cases clauseHead with
          | some headAtom =>
              cases hbody : hornSatBodyHolds (hornSatLeastModel system) clauseBody with
              | false =>
                  show cond (hornSatBodyHolds (hornSatLeastModel system) clauseBody)
                    (hornSatSetHeadHolds (hornSatLeastModel system) (some headAtom)) true
                    = true
                  rw [hbody]
                  rfl
              | true =>
                  show cond (hornSatBodyHolds (hornSatLeastModel system) clauseBody)
                    (hornSatSetHeadHolds (hornSatLeastModel system) (some headAtom)) true
                    = true
                  rw [hbody]
                  show hornSatMember (hornSatLeastModel system) headAtom = true
                  exact hornSatLeastModelIsClosed system clauseBody headAtom hInSystem hbody
          | none =>
              have hIdle : hornSatBodyHolds (hornSatLeastModel system) clauseBody = false :=
                hornSatFindNoneMeansGoalsIdle system (hornSatLeastModel system) 0 hscan
                  clauseBody hInSystem
              show cond (hornSatBodyHolds (hornSatLeastModel system) clauseBody)
                (hornSatSetHeadHolds (hornSatLeastModel system) none) true = true
              rw [hIdle]
              rfl

/-- **Checker–evaluator corollary.**  On the SAT branch the induced environment satisfies
every clause under functional evaluation. -/
theorem hornSatDecideSatisfiableInducedEnv (system : List HornSatClause)
    (modelSet : List Nat)
    (hdecide : hornSatDecide system = HornSatVerdict.isSatisfiable modelSet) :
    hornSatEnvSatisfiesAll (fun probeAtom => hornSatMember modelSet probeAtom) system
      = true := by
  rw [hornSatCheckModelInduced modelSet system]
  exact hornSatDecideSatisfiableGivesModel system modelSet hdecide

/-- **UNSAT soundness.**  An unsatisfiable verdict refutes EVERY environment: minimality
pushes the least model below any satisfying environment, which then fires the reported
goal clause — absurd. -/
theorem hornSatDecideUnsatisfiableSound (system : List HornSatClause)
    (goalIndex : Nat) (saturatedSet : List Nat) (environment : Nat → Bool)
    (hdecide : hornSatDecide system = HornSatVerdict.isUnsatisfiable goalIndex saturatedSet)
    (hall : hornSatEnvSatisfiesAll environment system = true) : False := by
  cases hscan : hornSatFindViolatedGoal (hornSatLeastModel system) system 0 with
  | none =>
      have hDecideUnfolded : hornSatVerdictOfScan (hornSatLeastModel system)
          (hornSatFindViolatedGoal (hornSatLeastModel system) system 0)
          = HornSatVerdict.isUnsatisfiable goalIndex saturatedSet := hdecide
      rw [hscan] at hDecideUnfolded
      exact HornSatVerdict.noConfusion hDecideUnfolded
  | some foundIndex =>
      rcases hornSatFindSomeMeansGoalFired system (hornSatLeastModel system) 0 foundIndex
        hscan with ⟨goalBody, hInSystem, hfired⟩
      exact hornSatEnvClauseGoalRefutes environment goalBody
        (hornSatBodyHoldsLift goalBody (hornSatLeastModel system) environment
          (hornSatLeastModelIsMinimal system environment hall) hfired)
        (hornSatEnvSatisfiesAllExtract system environment hall ⟨goalBody, none⟩ hInSystem)

/-! ## Marker -/

/-- HORN-SAT is DECIDED on this island: least-model fixpoint with proven fuel adequacy,
closure, checker/evaluator agreement, minimality, and unsat soundness — all zero-axiom. -/
def fxDissatIsland_hasHornSatDecision : Bool := true

/-! ## Genuineness smokes (SAT, UNSAT, and FALSE checker cases) -/

-- Chain system: fact 1; 1 → 2; 2 → 3.  Least model [1, 2, 3]; satisfiable.
#eval hornSatLeastModel
  ([⟨[], some 1⟩, ⟨[1], some 2⟩, ⟨[2], some 3⟩] : List HornSatClause)
#eval hornSatVerdictIsSatisfiable (hornSatDecide
  ([⟨[], some 1⟩, ⟨[1], some 2⟩, ⟨[2], some 3⟩] : List HornSatClause))
#eval hornSatVerdictWitnessSet (hornSatDecide
  ([⟨[], some 1⟩, ⟨[1], some 2⟩, ⟨[2], some 3⟩] : List HornSatClause))
#eval hornSatCheckModel
  (hornSatVerdictWitnessSet (hornSatDecide
    ([⟨[], some 1⟩, ⟨[1], some 2⟩, ⟨[2], some 3⟩] : List HornSatClause)))
  ([⟨[], some 1⟩, ⟨[1], some 2⟩, ⟨[2], some 3⟩] : List HornSatClause)

-- Reversed chain (multi-pass saturation): 2 → 3; 1 → 2; fact 1.  Least model [1, 2, 3].
#eval hornSatLeastModel
  ([⟨[2], some 3⟩, ⟨[1], some 2⟩, ⟨[], some 1⟩] : List HornSatClause)

-- Unsatisfiable pair: fact 1; goal clause 1 → falsity.  Fired goal at index 1.
#eval hornSatVerdictIsSatisfiable (hornSatDecide
  ([⟨[], some 1⟩, ⟨[1], none⟩] : List HornSatClause))
#eval hornSatVerdictGoalIndex (hornSatDecide
  ([⟨[], some 1⟩, ⟨[1], none⟩] : List HornSatClause))
#eval hornSatVerdictWitnessSet (hornSatDecide
  ([⟨[], some 1⟩, ⟨[1], none⟩] : List HornSatClause))

-- Empty least model with an idle goal clause: 5 → 6; goal 6 → falsity.  Satisfiable, [].
#eval hornSatVerdictIsSatisfiable (hornSatDecide
  ([⟨[5], some 6⟩, ⟨[6], none⟩] : List HornSatClause))
#eval hornSatVerdictWitnessSet (hornSatDecide
  ([⟨[5], some 6⟩, ⟨[6], none⟩] : List HornSatClause))

-- The empty clause alone: goal with empty body fires immediately at index 0.
#eval hornSatVerdictIsSatisfiable (hornSatDecide ([⟨[], none⟩] : List HornSatClause))
#eval hornSatVerdictGoalIndex (hornSatDecide ([⟨[], none⟩] : List HornSatClause))

-- Self-loop clause 7 → 7 never fires from the empty start: satisfiable with [].
#eval hornSatVerdictIsSatisfiable (hornSatDecide ([⟨[7], some 7⟩] : List HornSatClause))
#eval hornSatVerdictWitnessSet (hornSatDecide ([⟨[7], some 7⟩] : List HornSatClause))

-- Unsorted facts + a join: least model comes out strictly ascending.
#eval hornSatLeastModel
  ([⟨[], some 3⟩, ⟨[], some 1⟩, ⟨[1, 3], some 2⟩] : List HornSatClause)
#eval hornSatIsAscending (hornSatLeastModel
  ([⟨[], some 3⟩, ⟨[], some 1⟩, ⟨[1, 3], some 2⟩] : List HornSatClause))

-- FALSE checker cases: a non-model is rejected.
#eval hornSatCheckModel [2] ([⟨[], some 1⟩] : List HornSatClause)
#eval hornSatCheckModel [] ([⟨[], some 1⟩] : List HornSatClause)
#eval hornSatBodyHolds [1, 3] [1, 2]
#eval hornSatTrueSetBeq [1, 2] [1, 3]
#eval hornSatTrueSetBeq [1, 2] [1, 2]

end FX1Poly.ComputerAlgebra
