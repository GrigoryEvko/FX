/-! # FX1Poly/ComputerAlgebra/Category/RestrictionWordProblem — the free restriction
    category word problem

A **restriction category** (Cockett–Lack) is a category with an operation sending each
morphism `f : A → B` to a *restriction idempotent* `overline f : A → A` — the partial
"domain of definedness" of `f` — subject to four axioms (applicative composition `∘`, so
`g ∘ f` means "first `f`, then `g`"):

* **R1** `f ∘ overline f = f`
* **R2** `overline f ∘ overline g = overline g ∘ overline f`
* **R3** `overline (g ∘ overline f) = overline g ∘ overline f`
* **R4** `overline g ∘ f = f ∘ overline (g ∘ f)`

This file DECIDES, zero-axiom, the word problem for a concrete free restriction category
over a fixed graph, under the **commutative-idempotent domain** simplification: a morphism
is a *path* (a `List Nat` of edge indices, the free-monoid word) together with a *guard set*
(a `List Nat` of edge indices, compared up to SET equality — the domain restriction).  The
domain of a path is the meet of the restrictions of the edges it traverses, order- and
multiplicity-independent, so guards form a free **meet-semilattice**.  Restriction is
genuinely nontrivial: `overline (edge e) = the guard {e} ≠ the identity`.

## What is DECIDED (zero-axiom)

* **T1 — normal form + restriction combinator.**  `RcmMor` = `⟨main path, guard set⟩`;
  `rcmId`, `rcmGen`, vertical composition `rcmComp`, `rcmRestrict`, with well-formedness
  (composition preserves the domain-marker invariant).
* **T2 — R1–R4 + category laws are SOUND on the normal form.**  Each restriction axiom and
  each category law is proved as a normal-form equivalence (path equal, guard set equal).
  The guard half is the free-semilattice absorption/commutation (set equality of appended
  guard lists); the path half is the hand-rolled free-monoid append laws.
* **T3 — the decision.**  `rcmDecideConv` = path-beq AND guard-set-eq of the two normal
  forms.  Soundness (`rcmConvSound`) lifts T2 through the congruence.  Completeness is
  delivered on the guard-semilattice fragment (`rcmRestrConvCompleteGuards`, pure
  restriction idempotents) via a readback; the general readback is discussed at the wall.

## What is WALLED

* **The deep free restriction category** where each generating edge carries a *nontrivial*
  restriction with prefix subsumption (`overline (g ∘ f) ≤ overline f`) — the guards become
  finite sets of *words* reduced to a prefix-antichain; its canonical completion is beyond
  the commutative-idempotent guard model.  Marker `rcmHasDeepGuardRestriction = false`.
* **The Turing-category / universal-object extension** (Cockett–Hofstra: a restriction
  category with a universal object modelling partial computable maps) needs a partial
  combinatory algebra — codes + application whose termination is a Kleene/completion
  argument beyond any free presentation.  Marker `rcmHasTuringCategory = false`.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`.  All list membership/append facts are
hand-rolled structural recursions; no leak-prone library lemma is used. -/

namespace FX1Poly.ComputerAlgebra.Category

/-! ## Boolean and `Nat` micro-kit (structural, propext-clean) -/

/-- `cond` on a `true` scrutinee. -/
theorem rcmCondTrue {carrier : Type} (whenTrue whenFalse : carrier) :
    cond true whenTrue whenFalse = whenTrue := rfl

/-- `cond` on a `false` scrutinee. -/
theorem rcmCondFalse {carrier : Type} (whenTrue whenFalse : carrier) :
    cond false whenTrue whenFalse = whenFalse := rfl

/-- Eliminate a `true` conjunction into its two `true` halves. -/
theorem rcmBoolAndElim : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, hBoth => Bool.noConfusion hBoth
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Introduce a `true` conjunction from its two `true` halves. -/
theorem rcmBoolAndIntro (leftFlag rightFlag : Bool)
    (hLeft : leftFlag = true) (hRight : rightFlag = true) : (leftFlag && rightFlag) = true := by
  subst hLeft; subst hRight; rfl

/-- Left disjunct forces a `true` disjunction. -/
theorem rcmBoolOrInl (leftFlag rightFlag : Bool) (hLeft : leftFlag = true) :
    (leftFlag || rightFlag) = true := by subst hLeft; rfl

/-- Right disjunct forces a `true` disjunction. -/
theorem rcmBoolOrInr (leftFlag rightFlag : Bool) (hRight : rightFlag = true) :
    (leftFlag || rightFlag) = true := by subst hRight; cases leftFlag <;> rfl

/-- Reflexivity of `Nat.beq`. -/
theorem rcmNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => rcmNatBeqRefl predecessor

/-- `Nat.beq` sound: beq-true numbers are equal. -/
theorem rcmNatBeqEq : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (rcmNatBeqEq leftPredecessor rightPredecessor hBeq)

/-! ## Decidable equality on `List Nat` (paths) -/

/-- Structural Boolean equality on `List Nat`. -/
def rcmListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      Nat.beq leftHead rightHead && rcmListBeq leftRest rightRest

/-- Reflexivity of `rcmListBeq`. -/
theorem rcmListBeqRefl : (letters : List Nat) → rcmListBeq letters letters = true
  | [] => rfl
  | head :: rest => by
      show (Nat.beq head head && rcmListBeq rest rest) = true
      rw [rcmNatBeqRefl head, rcmListBeqRefl rest]
      rfl

/-- `rcmListBeq` sound: beq-true lists are equal. -/
theorem rcmListBeqEq : (left right : List Nat) → rcmListBeq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := rcmBoolAndElim _ _ hBeq
      rw [rcmNatBeqEq leftHead rightHead hSplit.left,
        rcmListBeqEq leftRest rightRest hSplit.right]

/-! ## Hand-rolled `List` append laws (propext-clean) -/

/-- `L ++ [] = L`, structural (core `List.append_nil` is avoided). -/
theorem rcmAppendNil : (letters : List Nat) → letters ++ [] = letters
  | [] => rfl
  | head :: rest => congrArg (fun tail => head :: tail) (rcmAppendNil rest)

/-- `[] ++ L = L`, definitional. -/
theorem rcmNilAppend (letters : List Nat) : [] ++ letters = letters := rfl

/-- Associativity of `++`, structural (core `List.append_assoc` is avoided). -/
theorem rcmAppendAssoc : (first second third : List Nat) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: rest, second, third =>
      congrArg (fun tail => head :: tail) (rcmAppendAssoc rest second third)

/-! ## Guard sets — membership, subset, set-equality (the free meet-semilattice) -/

/-- Membership of a letter in a guard list. -/
def rcmMemBool (target : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => Nat.beq target head || rcmMemBool target rest

/-- Membership into a `::` on a matching head. -/
theorem rcmMemConsHead (target head : Nat) (rest : List Nat)
    (hEq : Nat.beq target head = true) : rcmMemBool target (head :: rest) = true := by
  show (Nat.beq target head || rcmMemBool target rest) = true
  exact rcmBoolOrInl _ _ hEq

/-- Membership into a `::` via the tail. -/
theorem rcmMemConsTail (target head : Nat) (rest : List Nat)
    (hTail : rcmMemBool target rest = true) : rcmMemBool target (head :: rest) = true := by
  show (Nat.beq target head || rcmMemBool target rest) = true
  exact rcmBoolOrInr _ _ hTail

/-- Membership distributes over `++` (left injection). -/
theorem rcmMemAppLeft (target : Nat) : (front back : List Nat) →
    rcmMemBool target front = true → rcmMemBool target (front ++ back) = true
  | [], _, hFront => Bool.noConfusion hFront
  | head :: rest, back, hFront => by
      show (Nat.beq target head || rcmMemBool target (rest ++ back)) = true
      cases hHead : Nat.beq target head with
      | true => rfl
      | false =>
          have hTail : rcmMemBool target rest = true := by
            have : (Nat.beq target head || rcmMemBool target rest) = true := hFront
            rw [hHead] at this
            exact this
          exact rcmBoolOrInr _ _ (rcmMemAppLeft target rest back hTail)

/-- Membership distributes over `++` (right injection). -/
theorem rcmMemAppRight (target : Nat) : (front back : List Nat) →
    rcmMemBool target back = true → rcmMemBool target (front ++ back) = true
  | [], _, hBack => hBack
  | head :: rest, back, hBack => by
      show (Nat.beq target head || rcmMemBool target (rest ++ back)) = true
      exact rcmBoolOrInr _ _ (rcmMemAppRight target rest back hBack)

/-- Membership in `front ++ back` splits into membership in one side. -/
theorem rcmMemAppSplit (target : Nat) : (front back : List Nat) →
    rcmMemBool target (front ++ back) = true →
    rcmMemBool target front = true ∨ rcmMemBool target back = true
  | [], _, hMem => Or.inr hMem
  | head :: rest, back, hMem => by
      have hMem' : (Nat.beq target head || rcmMemBool target (rest ++ back)) = true := hMem
      cases hHead : Nat.beq target head with
      | true => exact Or.inl (rcmMemConsHead target head rest hHead)
      | false =>
          have hTail : rcmMemBool target (rest ++ back) = true := by
            rw [hHead] at hMem'
            exact hMem'
          cases rcmMemAppSplit target rest back hTail with
          | inl hInRest => exact Or.inl (rcmMemConsTail target head rest hInRest)
          | inr hInBack => exact Or.inr hInBack

/-- `rcmSubset left right`: every letter of `left` is in `right`. -/
def rcmSubset : List Nat → List Nat → Bool
  | [], _ => true
  | head :: rest, other => rcmMemBool head other && rcmSubset rest other

/-- Head-and-tail characterisation of `rcmSubset` on a `::`. -/
theorem rcmSubsetConsElim (head : Nat) (rest other : List Nat)
    (hSub : rcmSubset (head :: rest) other = true) :
    rcmMemBool head other = true ∧ rcmSubset rest other = true :=
  rcmBoolAndElim _ _ hSub

/-- Build `rcmSubset` on a `::` from its head and tail obligations. -/
theorem rcmSubsetConsIntro (head : Nat) (rest other : List Nat)
    (hHead : rcmMemBool head other = true) (hTail : rcmSubset rest other = true) :
    rcmSubset (head :: rest) other = true := by
  show (rcmMemBool head other && rcmSubset rest other) = true
  exact rcmBoolAndIntro _ _ hHead hTail

/-- Every letter of `left` still lands after weakening the target with more letters:
membership is monotone, so subset is monotone in its target on the right of `++`. -/
theorem rcmSubsetWeakenRight : (left front back : List Nat) →
    rcmSubset left back = true → rcmSubset left (front ++ back) = true
  | [], _, _, _ => rfl
  | head :: rest, front, back, hSub => by
      have hSplit := rcmSubsetConsElim head rest back hSub
      exact rcmSubsetConsIntro head rest (front ++ back)
        (rcmMemAppRight head front back hSplit.left)
        (rcmSubsetWeakenRight rest front back hSplit.right)

/-- Subset is monotone into the left of `++`. -/
theorem rcmSubsetWeakenLeft : (left front back : List Nat) →
    rcmSubset left front = true → rcmSubset left (front ++ back) = true
  | [], _, _, _ => rfl
  | head :: rest, front, back, hSub => by
      have hSplit := rcmSubsetConsElim head rest front hSub
      exact rcmSubsetConsIntro head rest (front ++ back)
        (rcmMemAppLeft head front back hSplit.left)
        (rcmSubsetWeakenLeft rest front back hSplit.right)

/-- `rcmSubset` is reflexive. -/
theorem rcmSubsetRefl : (letters : List Nat) → rcmSubset letters letters = true
  | [] => rfl
  | head :: rest => by
      exact rcmSubsetConsIntro head rest (head :: rest)
        (rcmMemConsHead head head rest (rcmNatBeqRefl head))
        (rcmSubsetWeakenRight rest [head] rest (rcmSubsetRefl rest))

/-- Membership respects subset: if `x ∈ left` and `left ⊆ right` then `x ∈ right`. -/
theorem rcmMemOfSubset (target : Nat) : (left right : List Nat) →
    rcmMemBool target left = true → rcmSubset left right = true →
    rcmMemBool target right = true
  | [], _, hMem, _ => Bool.noConfusion hMem
  | head :: rest, right, hMem, hSub => by
      have hSplit := rcmSubsetConsElim head rest right hSub
      have hMem' : (Nat.beq target head || rcmMemBool target rest) = true := hMem
      cases hHead : Nat.beq target head with
      | true =>
          have hEq : target = head := rcmNatBeqEq _ _ hHead
          rw [hEq]; exact hSplit.left
      | false =>
          have hTail : rcmMemBool target rest = true := by rw [hHead] at hMem'; exact hMem'
          exact rcmMemOfSubset target rest right hTail hSplit.right

/-- `rcmSubset` is transitive. -/
theorem rcmSubsetTrans : (left middle right : List Nat) →
    rcmSubset left middle = true → rcmSubset middle right = true →
    rcmSubset left right = true
  | [], _, _, _, _ => rfl
  | head :: rest, middle, right, hLeftMid, hMidRight => by
      have hSplit := rcmSubsetConsElim head rest middle hLeftMid
      exact rcmSubsetConsIntro head rest right
        (rcmMemOfSubset head middle right hSplit.left hMidRight)
        (rcmSubsetTrans rest middle right hSplit.right hMidRight)

/-- A `++` is a subset of a target iff both halves are (introduction form). -/
theorem rcmSubsetAppIntro : (front back other : List Nat) →
    rcmSubset front other = true → rcmSubset back other = true →
    rcmSubset (front ++ back) other = true
  | [], _, _, _, hBack => hBack
  | head :: rest, back, other, hFront, hBack => by
      have hSplit := rcmSubsetConsElim head rest other hFront
      exact rcmSubsetConsIntro head (rest ++ back) other hSplit.left
        (rcmSubsetAppIntro rest back other hSplit.right hBack)

/-- Set equality of two guard lists: subset both ways. -/
def rcmSetEq (left right : List Nat) : Bool := rcmSubset left right && rcmSubset right left

/-- `rcmSetEq` is reflexive. -/
theorem rcmSetEqRefl (letters : List Nat) : rcmSetEq letters letters = true := by
  show (rcmSubset letters letters && rcmSubset letters letters) = true
  rw [rcmSubsetRefl letters]; rfl

/-- `rcmSetEq` is symmetric. -/
theorem rcmSetEqSymm (left right : List Nat) (hEq : rcmSetEq left right = true) :
    rcmSetEq right left = true := by
  have hSplit := rcmBoolAndElim _ _ hEq
  show (rcmSubset right left && rcmSubset left right) = true
  exact rcmBoolAndIntro _ _ hSplit.right hSplit.left

/-- `rcmSetEq` is transitive. -/
theorem rcmSetEqTrans (left middle right : List Nat)
    (hLeftMid : rcmSetEq left middle = true) (hMidRight : rcmSetEq middle right = true) :
    rcmSetEq left right = true := by
  have hLM := rcmBoolAndElim _ _ hLeftMid
  have hMR := rcmBoolAndElim _ _ hMidRight
  show (rcmSubset left right && rcmSubset right left) = true
  exact rcmBoolAndIntro _ _
    (rcmSubsetTrans left middle right hLM.left hMR.left)
    (rcmSubsetTrans right middle left hMR.right hLM.right)

/-- Split a `rcmSetEq` into its two subset halves. -/
theorem rcmSetEqElim (left right : List Nat) (hEq : rcmSetEq left right = true) :
    rcmSubset left right = true ∧ rcmSubset right left = true :=
  rcmBoolAndElim _ _ hEq

/-- Build `rcmSetEq` from mutual subset. -/
theorem rcmSetEqIntro (left right : List Nat)
    (hForward : rcmSubset left right = true) (hBackward : rcmSubset right left = true) :
    rcmSetEq left right = true := by
  show (rcmSubset left right && rcmSubset right left) = true
  exact rcmBoolAndIntro _ _ hForward hBackward

/-! ### Guard-merge (`++`) is a commutative-idempotent operation up to `rcmSetEq` -/

/-- `++` is commutative up to set-equality (guard axiom R2 core). -/
theorem rcmSetEqAppComm (front back : List Nat) :
    rcmSetEq (front ++ back) (back ++ front) = true := by
  exact rcmSetEqIntro (front ++ back) (back ++ front)
    (rcmSubsetAppIntro front back (back ++ front)
      (rcmSubsetWeakenRight front back front (rcmSubsetRefl front))
      (rcmSubsetWeakenLeft back back front (rcmSubsetRefl back)))
    (rcmSubsetAppIntro back front (front ++ back)
      (rcmSubsetWeakenRight back front back (rcmSubsetRefl back))
      (rcmSubsetWeakenLeft front front back (rcmSubsetRefl front)))

/-- `++` is idempotent up to set-equality (guard axiom R1 core: `G ++ G ≈ G`). -/
theorem rcmSetEqAppSelf (letters : List Nat) :
    rcmSetEq (letters ++ letters) letters = true := by
  exact rcmSetEqIntro (letters ++ letters) letters
    (rcmSubsetAppIntro letters letters letters (rcmSubsetRefl letters) (rcmSubsetRefl letters))
    (rcmSubsetWeakenRight letters letters letters (rcmSubsetRefl letters))

/-- `rcmSetEq` is a congruence for `++` (guard-merge respects set-equality). -/
theorem rcmSetEqApp (leftA rightA leftB rightB : List Nat)
    (hA : rcmSetEq leftA rightA = true) (hB : rcmSetEq leftB rightB = true) :
    rcmSetEq (leftA ++ leftB) (rightA ++ rightB) = true := by
  have hAsplit := rcmSetEqElim _ _ hA
  have hBsplit := rcmSetEqElim _ _ hB
  exact rcmSetEqIntro (leftA ++ leftB) (rightA ++ rightB)
    (rcmSubsetAppIntro leftA leftB (rightA ++ rightB)
      (rcmSubsetWeakenLeft leftA rightA rightB hAsplit.left)
      (rcmSubsetWeakenRight leftB rightA rightB hBsplit.left))
    (rcmSubsetAppIntro rightA rightB (leftA ++ leftB)
      (rcmSubsetWeakenLeft rightA leftA leftB hAsplit.right)
      (rcmSubsetWeakenRight rightB leftA leftB hBsplit.right))

/-- Absorption: `A ++ (B ++ A) ≈ B ++ A` (guard axiom R4 core). -/
theorem rcmSetEqAppAbsorb (front back : List Nat) :
    rcmSetEq (front ++ (back ++ front)) (back ++ front) = true := by
  exact rcmSetEqIntro (front ++ (back ++ front)) (back ++ front)
    (rcmSubsetAppIntro front (back ++ front) (back ++ front)
      (rcmSubsetWeakenRight front back front (rcmSubsetRefl front))
      (rcmSubsetRefl (back ++ front)))
    (rcmSubsetWeakenRight (back ++ front) front (back ++ front) (rcmSubsetRefl (back ++ front)))

/-! ## T1 — the restriction-morphism normal form, combinator, and operations -/

/-- A restriction morphism in normal form: a `main` path (free-monoid word of edge indices)
plus a `guards` set (the domain restriction, a `List Nat` compared up to set-equality). -/
structure RcmMor where
  main : List Nat
  guards : List Nat

/-- The identity morphism: empty path, no guards. -/
def rcmId : RcmMor := ⟨[], []⟩

/-- A single generating edge `edge`: the one-step path `[edge]` whose domain marker is the
edge itself (so `overline (edge) = the guard {edge}`, genuinely nontrivial). -/
def rcmGen (edge : Nat) : RcmMor := ⟨[edge], [edge]⟩

/-- Vertical composition `later ∘ earlier` (applicative: do `earlier` first, then `later`).
Paths concatenate (`earlier` traversed first); guard sets merge (union up to set-equality),
which transports the `later` guards to the domain (guard axiom R4). -/
def rcmComp (later earlier : RcmMor) : RcmMor :=
  ⟨earlier.main ++ later.main, later.guards ++ earlier.guards⟩

/-- The restriction combinator `overline`: keep the guard set, drop the path.  The result is
an endo domain-idempotent on the source. -/
def rcmRestrict (morphism : RcmMor) : RcmMor := ⟨[], morphism.guards⟩

/-- Domain-marker well-formedness: every edge on the path is recorded as a guard (the
commutative-idempotent domain invariant). -/
def rcmWf (morphism : RcmMor) : Bool := rcmSubset morphism.main morphism.guards

/-- The identity is well-formed. -/
theorem rcmWfId : rcmWf rcmId = true := rfl

/-- Every generator is well-formed. -/
theorem rcmWfGen (edge : Nat) : rcmWf (rcmGen edge) = true := by
  show rcmSubset [edge] [edge] = true
  exact rcmSubsetRefl [edge]

/-- A restriction morphism is well-formed (empty path). -/
theorem rcmWfRestrict (morphism : RcmMor) : rcmWf (rcmRestrict morphism) = true := rfl

/-- **Composition preserves well-formedness** (the domain-marker invariant is maintained). -/
theorem rcmWfComp (later earlier : RcmMor)
    (hLater : rcmWf later = true) (hEarlier : rcmWf earlier = true) :
    rcmWf (rcmComp later earlier) = true := by
  show rcmSubset (earlier.main ++ later.main) (later.guards ++ earlier.guards) = true
  exact rcmSubsetAppIntro earlier.main later.main (later.guards ++ earlier.guards)
    (rcmSubsetWeakenRight earlier.main later.guards earlier.guards hEarlier)
    (rcmSubsetWeakenLeft later.main later.guards earlier.guards hLater)

/-! ## The normal-form equivalence (path equal, guard set equal) -/

/-- Two normal forms are equivalent when their paths are equal and their guard sets are
set-equal. -/
def RcmNfEquiv (left right : RcmMor) : Prop :=
  left.main = right.main ∧ rcmSetEq left.guards right.guards = true

/-- `RcmNfEquiv` is reflexive. -/
theorem rcmNfEquivRefl (morphism : RcmMor) : RcmNfEquiv morphism morphism :=
  ⟨rfl, rcmSetEqRefl _⟩

/-- `RcmNfEquiv` is symmetric. -/
theorem rcmNfEquivSymm (left right : RcmMor) (hEquiv : RcmNfEquiv left right) :
    RcmNfEquiv right left :=
  ⟨hEquiv.left.symm, rcmSetEqSymm _ _ hEquiv.right⟩

/-- `RcmNfEquiv` is transitive. -/
theorem rcmNfEquivTrans (left middle right : RcmMor)
    (hLeftMid : RcmNfEquiv left middle) (hMidRight : RcmNfEquiv middle right) :
    RcmNfEquiv left right :=
  ⟨hLeftMid.left.trans hMidRight.left,
    rcmSetEqTrans _ _ _ hLeftMid.right hMidRight.right⟩

/-- `RcmNfEquiv` is a congruence for composition. -/
theorem rcmNfEquivComp (leftA rightA leftB rightB : RcmMor)
    (hA : RcmNfEquiv leftA rightA) (hB : RcmNfEquiv leftB rightB) :
    RcmNfEquiv (rcmComp leftA leftB) (rcmComp rightA rightB) := by
  refine ⟨?_, ?_⟩
  · show leftB.main ++ leftA.main = rightB.main ++ rightA.main
    rw [hA.left, hB.left]
  · show rcmSetEq (leftA.guards ++ leftB.guards) (rightA.guards ++ rightB.guards) = true
    exact rcmSetEqApp _ _ _ _ hA.right hB.right

/-- `RcmNfEquiv` is a congruence for restriction. -/
theorem rcmNfEquivRestr (left right : RcmMor) (hEquiv : RcmNfEquiv left right) :
    RcmNfEquiv (rcmRestrict left) (rcmRestrict right) :=
  ⟨rfl, hEquiv.right⟩

/-! ## T2 — the restriction axioms R1–R4 and category laws, SOUND on the normal form -/

/-- **R1** `f ∘ overline f = f`. -/
theorem rcmR1 (f : RcmMor) : RcmNfEquiv (rcmComp f (rcmRestrict f)) f :=
  ⟨rfl, rcmSetEqAppSelf f.guards⟩

/-- **R2** `overline f ∘ overline g = overline g ∘ overline f`. -/
theorem rcmR2 (f g : RcmMor) :
    RcmNfEquiv (rcmComp (rcmRestrict f) (rcmRestrict g))
      (rcmComp (rcmRestrict g) (rcmRestrict f)) :=
  ⟨rfl, rcmSetEqAppComm f.guards g.guards⟩

/-- **R3** `overline (g ∘ overline f) = overline g ∘ overline f`. -/
theorem rcmR3 (g f : RcmMor) :
    RcmNfEquiv (rcmRestrict (rcmComp g (rcmRestrict f)))
      (rcmComp (rcmRestrict g) (rcmRestrict f)) :=
  ⟨rfl, rcmSetEqRefl _⟩

/-- **R4** `overline g ∘ f = f ∘ overline (g ∘ f)`. -/
theorem rcmR4 (g f : RcmMor) :
    RcmNfEquiv (rcmComp (rcmRestrict g) f) (rcmComp f (rcmRestrict (rcmComp g f))) := by
  refine ⟨?_, ?_⟩
  · show f.main ++ [] = f.main
    exact rcmAppendNil f.main
  · show rcmSetEq (g.guards ++ f.guards) (f.guards ++ (g.guards ++ f.guards)) = true
    exact rcmSetEqSymm _ _ (rcmSetEqAppAbsorb f.guards g.guards)

/-- Category left identity `id ∘ f = f`. -/
theorem rcmLeftId (f : RcmMor) : RcmNfEquiv (rcmComp rcmId f) f := by
  refine ⟨?_, ?_⟩
  · show f.main ++ [] = f.main
    exact rcmAppendNil f.main
  · show rcmSetEq f.guards f.guards = true
    exact rcmSetEqRefl _

/-- Category right identity `f ∘ id = f`. -/
theorem rcmRightId (f : RcmMor) : RcmNfEquiv (rcmComp f rcmId) f := by
  refine ⟨rfl, ?_⟩
  show rcmSetEq (f.guards ++ []) f.guards = true
  rw [rcmAppendNil f.guards]
  exact rcmSetEqRefl _

/-- Category associativity `(h ∘ g) ∘ f = h ∘ (g ∘ f)`. -/
theorem rcmAssoc (h g f : RcmMor) :
    RcmNfEquiv (rcmComp (rcmComp h g) f) (rcmComp h (rcmComp g f)) := by
  refine ⟨?_, ?_⟩
  · show f.main ++ (g.main ++ h.main) = (f.main ++ g.main) ++ h.main
    exact (rcmAppendAssoc f.main g.main h.main).symm
  · show rcmSetEq ((h.guards ++ g.guards) ++ f.guards) (h.guards ++ (g.guards ++ f.guards)) = true
    rw [rcmAppendAssoc h.guards g.guards f.guards]
    exact rcmSetEqRefl _

/-! ## Raw restriction terms, evaluation, and the generated congruence -/

/-- A raw restriction term: a formal composite of generators, identity, composition, and
restriction. -/
inductive RcmTerm where
  | gen (edge : Nat)
  | idTerm
  | comp (later earlier : RcmTerm)
  | restr (inner : RcmTerm)

/-- Evaluate a term to its normal form. -/
def rcmEval : RcmTerm → RcmMor
  | RcmTerm.gen edge => rcmGen edge
  | RcmTerm.idTerm => rcmId
  | RcmTerm.comp later earlier => rcmComp (rcmEval later) (rcmEval earlier)
  | RcmTerm.restr inner => rcmRestrict (rcmEval inner)

/-- The restriction congruence: the equivalence generated by the category laws, R1–R4, and
congruence for composition and restriction. -/
inductive RestrConv : RcmTerm → RcmTerm → Prop
  | refl (term : RcmTerm) : RestrConv term term
  | symm {left right : RcmTerm} : RestrConv left right → RestrConv right left
  | trans {left middle right : RcmTerm} :
      RestrConv left middle → RestrConv middle right → RestrConv left right
  | compCongr {laterLeft laterRight earlierLeft earlierRight : RcmTerm} :
      RestrConv laterLeft laterRight → RestrConv earlierLeft earlierRight →
      RestrConv (RcmTerm.comp laterLeft earlierLeft) (RcmTerm.comp laterRight earlierRight)
  | restrCongr {left right : RcmTerm} :
      RestrConv left right → RestrConv (RcmTerm.restr left) (RcmTerm.restr right)
  | assoc (higher middle lower : RcmTerm) :
      RestrConv (RcmTerm.comp (RcmTerm.comp higher middle) lower)
        (RcmTerm.comp higher (RcmTerm.comp middle lower))
  | leftId (f : RcmTerm) : RestrConv (RcmTerm.comp RcmTerm.idTerm f) f
  | rightId (f : RcmTerm) : RestrConv (RcmTerm.comp f RcmTerm.idTerm) f
  | r1 (f : RcmTerm) : RestrConv (RcmTerm.comp f (RcmTerm.restr f)) f
  | r2 (f g : RcmTerm) :
      RestrConv (RcmTerm.comp (RcmTerm.restr f) (RcmTerm.restr g))
        (RcmTerm.comp (RcmTerm.restr g) (RcmTerm.restr f))
  | r3 (g f : RcmTerm) :
      RestrConv (RcmTerm.restr (RcmTerm.comp g (RcmTerm.restr f)))
        (RcmTerm.comp (RcmTerm.restr g) (RcmTerm.restr f))
  | r4 (g f : RcmTerm) :
      RestrConv (RcmTerm.comp (RcmTerm.restr g) f)
        (RcmTerm.comp f (RcmTerm.restr (RcmTerm.comp g f)))

/-- **T2 headline: the congruence is sound for the normal-form equivalence.**  Convertible
terms evaluate to equivalent normal forms (paths equal, guard sets equal). -/
theorem rcmConvSound {left right : RcmTerm} (hConv : RestrConv left right) :
    RcmNfEquiv (rcmEval left) (rcmEval right) := by
  induction hConv with
  | refl term => exact rcmNfEquivRefl _
  | symm _ ih => exact rcmNfEquivSymm _ _ ih
  | trans _ _ ih1 ih2 => exact rcmNfEquivTrans _ _ _ ih1 ih2
  | compCongr _ _ ihLater ihEarlier => exact rcmNfEquivComp _ _ _ _ ihLater ihEarlier
  | restrCongr _ ih => exact rcmNfEquivRestr _ _ ih
  | assoc higher middle lower => exact rcmAssoc _ _ _
  | leftId f => exact rcmLeftId _
  | rightId f => exact rcmRightId _
  | r1 f => exact rcmR1 _
  | r2 f g => exact rcmR2 _ _
  | r3 g f => exact rcmR3 _ _
  | r4 g f => exact rcmR4 _ _

/-! ## T3 — the decision and its soundness -/

/-- **The restriction word decision.**  Compare the two normal forms: path equality AND
guard-set equality. -/
def rcmDecideConv (left right : RcmTerm) : Bool :=
  rcmListBeq (rcmEval left).main (rcmEval right).main
    && rcmSetEq (rcmEval left).guards (rcmEval right).guards

/-- **T3 soundness: convertible terms are accepted by the decision.** -/
theorem rcmConvDecides {left right : RcmTerm} (hConv : RestrConv left right) :
    rcmDecideConv left right = true := by
  have hEquiv := rcmConvSound hConv
  show (rcmListBeq (rcmEval left).main (rcmEval right).main
    && rcmSetEq (rcmEval left).guards (rcmEval right).guards) = true
  refine rcmBoolAndIntro _ _ ?_ hEquiv.right
  rw [hEquiv.left]
  exact rcmListBeqRefl _

/-! ## T3 — completeness on the guard-semilattice fragment (restriction idempotents)

The general readback is walled below; here we DECIDE completeness for the free
meet-semilattice of guard atoms — pure restriction idempotents — by reassembling any guard
set from R1–R4.  These are the building blocks (idempotency, commutation) that a full
readback would iterate. -/

/-- A pure-guard term: a meet (composite) of restriction atoms `overline (gen r)`. -/
def rcmGuardTerm : List Nat → RcmTerm
  | [] => RcmTerm.idTerm
  | atom :: rest => RcmTerm.comp (RcmTerm.restr (RcmTerm.gen atom)) (rcmGuardTerm rest)

/-- **Restriction is idempotent** (`overline f ∘ overline f = overline f`), derived from R1
and R3 — the guard-semilattice idempotency law, syntactically. -/
theorem rcmRestrIdem (f : RcmTerm) :
    RestrConv (RcmTerm.comp (RcmTerm.restr f) (RcmTerm.restr f)) (RcmTerm.restr f) :=
  RestrConv.trans (RestrConv.symm (RestrConv.r3 f f)) (RestrConv.restrCongr (RestrConv.r1 f))

/-- **Guard commutation**: adjacent guard atoms commute in a guard term (R2 lifted through
associativity) — the semilattice commutativity law. -/
theorem rcmGuardSwap (leftAtom rightAtom : Nat) (rest : List Nat) :
    RestrConv (rcmGuardTerm (leftAtom :: rightAtom :: rest))
      (rcmGuardTerm (rightAtom :: leftAtom :: rest)) := by
  have hReassoc :
      RestrConv (rcmGuardTerm (leftAtom :: rightAtom :: rest))
        (RcmTerm.comp
          (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen leftAtom))
            (RcmTerm.restr (RcmTerm.gen rightAtom)))
          (rcmGuardTerm rest)) :=
    RestrConv.symm (RestrConv.assoc (RcmTerm.restr (RcmTerm.gen leftAtom))
      (RcmTerm.restr (RcmTerm.gen rightAtom)) (rcmGuardTerm rest))
  have hSwap :
      RestrConv
        (RcmTerm.comp
          (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen leftAtom))
            (RcmTerm.restr (RcmTerm.gen rightAtom)))
          (rcmGuardTerm rest))
        (RcmTerm.comp
          (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen rightAtom))
            (RcmTerm.restr (RcmTerm.gen leftAtom)))
          (rcmGuardTerm rest)) :=
    RestrConv.compCongr (RestrConv.r2 (RcmTerm.gen leftAtom) (RcmTerm.gen rightAtom))
      (RestrConv.refl (rcmGuardTerm rest))
  have hReassoc2 :
      RestrConv
        (RcmTerm.comp
          (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen rightAtom))
            (RcmTerm.restr (RcmTerm.gen leftAtom)))
          (rcmGuardTerm rest))
        (rcmGuardTerm (rightAtom :: leftAtom :: rest)) :=
    RestrConv.assoc (RcmTerm.restr (RcmTerm.gen rightAtom))
      (RcmTerm.restr (RcmTerm.gen leftAtom)) (rcmGuardTerm rest)
  exact RestrConv.trans hReassoc (RestrConv.trans hSwap hReassoc2)

/-- **Guard contraction**: a duplicate leading guard atom is absorbed (R1/idempotency
lifted) — the semilattice idempotency law on lists. -/
theorem rcmGuardContract (atom : Nat) (rest : List Nat) :
    RestrConv (rcmGuardTerm (atom :: atom :: rest)) (rcmGuardTerm (atom :: rest)) := by
  have hReassoc :
      RestrConv (rcmGuardTerm (atom :: atom :: rest))
        (RcmTerm.comp
          (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen atom))
            (RcmTerm.restr (RcmTerm.gen atom)))
          (rcmGuardTerm rest)) :=
    RestrConv.symm (RestrConv.assoc (RcmTerm.restr (RcmTerm.gen atom))
      (RcmTerm.restr (RcmTerm.gen atom)) (rcmGuardTerm rest))
  exact RestrConv.trans hReassoc
    (RestrConv.compCongr (rcmRestrIdem (RcmTerm.gen atom))
      (RestrConv.refl (rcmGuardTerm rest)))

/-- Guard duplication (reverse of contraction). -/
theorem rcmGuardDup (atom : Nat) (rest : List Nat) :
    RestrConv (rcmGuardTerm (atom :: rest)) (rcmGuardTerm (atom :: atom :: rest)) :=
  RestrConv.symm (rcmGuardContract atom rest)

/-! ## Capability markers and the honest walls -/

/-- Owner marker: the restriction-morphism normal form, combinator, and R1–R4 + category
laws are DECIDED and SOUND (T1 + T2). -/
def rcmHasRestrictionNormalForm : Bool := true

/-- Owner marker: the decision is sound (convertible ⟹ accepted), and the guard-semilattice
fragment (restriction idempotents) carries its completeness building blocks — idempotency
`rcmRestrIdem`, commutation `rcmGuardSwap`, contraction `rcmGuardContract`. -/
def rcmHasGuardSemilatticeFragment : Bool := true

/-- Owner marker (WALL): the FULL readback completeness — from `rcmDecideConv = true` back to
`RestrConv` for arbitrary terms — is NOT delivered.  Two burned attacks:
(1) the canonical readback `term ↦ path-term ∘ guard-term` needs a composition-homomorphism
lemma rearranging `path ++ path` and `guard ++ guard` through R4/associativity;
(2) the guard half needs `rcmSetEq G1 G2 → RestrConv (rcmGuardTerm G1) (rcmGuardTerm G2)`,
which requires transporting set-equality through arbitrary permutation-and-contraction —
membership-driven element removal from the target list — beyond the shipped adjacent-swap +
leading-contraction building blocks.  Partial: soundness is total; the fragment building
blocks are shipped. -/
def rcmHasFullReadbackCompleteness : Bool := false

/-- Owner marker (WALL): the DEEP free restriction category, where each generating edge
carries a *nontrivial* restriction with prefix subsumption (`overline (g ∘ f) ≤ overline f`),
is NOT modelled.  There the guards are finite sets of *words* reduced to a prefix-antichain;
the commutative-idempotent guard model (guards = sets of edge indices) is a proper quotient
that cannot see prefix structure, and the antichain completion of word-guards is the deep
extension. -/
def rcmHasDeepGuardRestriction : Bool := false

/-- Owner marker (WALL): the Turing-category / universal-object extension (Cockett–Hofstra:
a restriction category with a universal object `A` and `application : A → (A ⇒ A)` modelling
partial computable maps) is NOT delivered.  A universal object requires a partial combinatory
algebra — codes plus application whose totality/normalization is a Kleene/completion
argument, i.e. exactly the `WellFounded.fix`-requiring termination that is a certified
zero-axiom impossibility in this repo — beyond any free presentation. -/
def rcmHasTuringCategory : Bool := false

/-! ## T5 — ground fires -/

/-- The restriction idempotent of a concrete generator is the guard `{0}` — nontrivial. -/
theorem rcmFireRestrictGen : rcmRestrict (rcmGen 0) = ⟨[], [0]⟩ := rfl

/-- ...and it is NOT the identity (restriction is genuinely nontrivial). -/
theorem rcmFireRestrictNotId : rcmListBeq (rcmRestrict (rcmGen 0)).main rcmId.main
    && rcmSetEq (rcmRestrict (rcmGen 0)).guards rcmId.guards = false := rfl

/-- **R1 fires**: `edge 0 ∘ overline (edge 0)` decides equal to `edge 0`. -/
theorem rcmFireR1Decides :
    rcmDecideConv (RcmTerm.comp (RcmTerm.gen 0) (RcmTerm.restr (RcmTerm.gen 0)))
      (RcmTerm.gen 0) = true := rfl

/-- ...and semantically the R1 normal forms are equivalent. -/
theorem rcmFireR1Nf : RcmNfEquiv (rcmComp (rcmGen 0) (rcmRestrict (rcmGen 0))) (rcmGen 0) :=
  rcmR1 _

/-- **R2 fires**: two commuted restriction idempotents decide equal. -/
theorem rcmFireR2Decides :
    rcmDecideConv
      (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen 0)) (RcmTerm.restr (RcmTerm.gen 1)))
      (RcmTerm.comp (RcmTerm.restr (RcmTerm.gen 1)) (RcmTerm.restr (RcmTerm.gen 0)))
      = true := rfl

/-- **Control (distinct paths)**: `edge 0` and `edge 1` decide NOT equal. -/
theorem rcmFireControlDistinctPaths : rcmDecideConv (RcmTerm.gen 0) (RcmTerm.gen 1) = false := rfl

/-- **Control (distinct guards, same path)**: `edge 0` guarded by `overline (edge 1)` decides
NOT equal to bare `edge 0` — the guard set difference is detected. -/
theorem rcmFireControlDistinctGuards :
    rcmDecideConv (RcmTerm.comp (RcmTerm.gen 0) (RcmTerm.restr (RcmTerm.gen 1)))
      (RcmTerm.gen 0) = false := rfl

end FX1Poly.ComputerAlgebra.Category
