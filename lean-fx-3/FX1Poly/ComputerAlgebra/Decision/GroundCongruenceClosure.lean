/-! # FX1Poly/ComputerAlgebra/Decision/GroundCongruenceClosure — the DISSAT-UF equality engine
    (ground congruence closure decided with zero search)

Ground equational logic over curried binary application terms is decided by **congruence
closure**: `GccDeriv equations sourceTerm targetTerm` (the reflexive-symmetric-transitive-
congruent closure of a finite equation list) holds **iff** the two terms have byte-equal
normal forms under a saturated equivalence table.  The design follows the completion-style
reading of congruence closure (Kapur RTA 1997; Bachmair–Tiwari–Vigneron JAR 2003;
Nieuwenhuis–Oliveras flat-term form), internalized as computation:

  * **Universe** — the beq-deduped list of every subterm of every equation side plus the
    two query terms (`gccBuildQueryUniverse`), proven subterm-closed.
  * **Saturation** — a pair table seeded with the equations plus reflexive pairs on the
    universe, closed one pass at a time (`gccSaturateStep`) under symmetry (swapped pairs),
    transitivity (endpoint joins) and congruence ON THE UNIVERSE (apply-node pairs whose
    children are already related).  Fuel `|U times U| + 1` suffices: insertion is
    beq-deduped, so the table is duplicate-free and bounded by the full pair square
    (`gccNoDupBoundedByLength`, a constructive pigeonhole via list erasure); each
    non-fixpoint pass strictly grows the table (`gccPairInsertAllStable`), hence the
    returned state is a genuine fixpoint (`gccSaturateReachesFixpoint`) and closure is
    extracted from "the pass added nothing" (`gccStepStableAllPresent`).
  * **Representatives** — `gccRepresentative` scans the universe in a FIXED order for the
    first table-related member (fallback: the term itself).  Related members get equal
    representatives (`gccRepresentativeRespects`, via pointwise scan agreement), and the
    representative is idempotent (`gccRepresentativeIdempotent`) — no table orientation
    needed.
  * **Signature table** — `gccBuildSignature` maps the key `(rep child1, rep child2)` of
    every apply-node in the universe to the node's representative.  Keying by
    representatives (never by normal forms) breaks the classic circularity, and makes the
    congruence case of completeness definitional: normalization of an apply node depends
    only on the normalized children.
  * **Total normalization** — `gccNormalize` recurses structurally, replacing symbols by
    representatives and apply nodes by their signature-table entry when the key hits,
    else rebuilding.  Totality on ALL terms is the standard dodge (Nelson–Oppen's total
    model extension, BTV's valley proofs) of the out-of-universe-transitivity problem: the
    `byTrans` case of completeness is `Eq.trans` of normal forms, with no universe side
    condition.

## The decision

`gccDecide equations sourceTerm targetTerm` = beq of the two normal forms under the
query-specific saturated table.  DECIDED, fully:

  * soundness    `gccDecideImpliesDeriv`  (beq-true normal forms chain back through the
    table, every entry of which carries a `GccDeriv` witness),
  * completeness `gccDerivImpliesDecide`  (induction on the derivation; the keystone
    `gccNormalizeAgreesOnUniverse` — every universe member normalizes to its
    representative — closes the equation case, and signature functionality
    `gccSigLookupFunctional` closes the keystone's apply case),
  * the packaged biconditional `gccDeriv_iff_decide`,
  * the `Decidable` instance `gccDerivDecidable` (built from the biconditional by Bool
    case split — no `propext`, no `decide`),
  * marker `fxDissatUf_hasGroundCongruenceDecision := true`.

## Zero-axiom discipline

Init only.  Structural recursion throughout (fuel for saturation, adequacy proven; no
`WellFounded.fix`).  No `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `omega`, no `decide` on `Prop` goals, no wildcard match arms
over inductive scrutinees.  Nat arithmetic restricted to the safe kit
(`Nat.add_comm/add_assoc/zero_add/add_zero/succ_add` plus hand-rolled cancellation);
Bool dispatch in definitions uses `cond`, never `if`.  All list helpers are bespoke,
monomorphic, cons-only.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/GroundCongruenceClosure.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Nat and Bool kit (hand-rolled, propext-free) -/

/-- Reflexivity of `Nat.beq`. -/
theorem gccNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => gccNatBeqRefl predecessor

/-- `Nat.beq` sound: beq-true numbers are equal. -/
theorem gccNatBeqEq : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (gccNatBeqEq leftPredecessor rightPredecessor hBeq)

/-- Additive cancellation against the base: `base + extra = base → extra = 0`. -/
theorem gccNatAddSelfImpliesZero : (baseValue extraValue : Nat) →
    baseValue + extraValue = baseValue → extraValue = 0
  | 0, extraValue, hSum => (Nat.zero_add extraValue).symm.trans hSum
  | Nat.succ basePredecessor, extraValue, hSum => by
      have hSuccEq : Nat.succ (basePredecessor + extraValue) = Nat.succ basePredecessor :=
        (Nat.succ_add basePredecessor extraValue).symm.trans hSum
      injection hSuccEq with hInner
      exact gccNatAddSelfImpliesZero basePredecessor extraValue hInner

/-- A vanishing sum has vanishing parts. -/
theorem gccNatAddSplitZero : (leftValue rightValue : Nat) → leftValue + rightValue = 0 →
    leftValue = 0 ∧ rightValue = 0
  | leftValue, 0, hSum => ⟨(Nat.add_zero leftValue).symm.trans hSum, rfl⟩
  | _, Nat.succ _, hSum => Nat.noConfusion hSum

/-- Conjunction elimination for Bool `&&`. -/
theorem gccBoolAndElim : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hAnd => Bool.noConfusion hAnd
  | false, true, hAnd => Bool.noConfusion hAnd
  | false, false, hAnd => Bool.noConfusion hAnd

/-! ## Terms: curried binary application over Nat-named symbols -/

/-- Ground terms: a symbol, or a curried application of one term to another. -/
inductive GccTerm : Type where
  | symbol (name : Nat) : GccTerm
  | apply (function : GccTerm) (argument : GccTerm) : GccTerm

/-- Structural Boolean equality on terms. -/
def gccTermBeq : GccTerm → GccTerm → Bool
  | GccTerm.symbol leftName, GccTerm.symbol rightName => Nat.beq leftName rightName
  | GccTerm.symbol _, GccTerm.apply _ _ => false
  | GccTerm.apply _ _, GccTerm.symbol _ => false
  | GccTerm.apply leftFunction leftArgument, GccTerm.apply rightFunction rightArgument =>
      gccTermBeq leftFunction rightFunction && gccTermBeq leftArgument rightArgument

/-- Reflexivity of `gccTermBeq`. -/
theorem gccTermBeqRefl : (term : GccTerm) → gccTermBeq term term = true
  | GccTerm.symbol name => gccNatBeqRefl name
  | GccTerm.apply function argument => by
      show (gccTermBeq function function && gccTermBeq argument argument) = true
      rw [gccTermBeqRefl function, gccTermBeqRefl argument]
      rfl

/-- `gccTermBeq` sound: beq-true terms are equal. -/
theorem gccTermBeqEq : (leftTerm rightTerm : GccTerm) → gccTermBeq leftTerm rightTerm = true →
    leftTerm = rightTerm
  | GccTerm.symbol leftName, GccTerm.symbol rightName, hBeq =>
      congrArg GccTerm.symbol (gccNatBeqEq leftName rightName hBeq)
  | GccTerm.symbol _, GccTerm.apply _ _, hBeq => Bool.noConfusion hBeq
  | GccTerm.apply _ _, GccTerm.symbol _, hBeq => Bool.noConfusion hBeq
  | GccTerm.apply leftFunction leftArgument, GccTerm.apply rightFunction rightArgument, hBeq =>
      have hSplit := gccBoolAndElim (gccTermBeq leftFunction rightFunction)
        (gccTermBeq leftArgument rightArgument) hBeq
      congr (congrArg GccTerm.apply (gccTermBeqEq leftFunction rightFunction hSplit.left))
        (gccTermBeqEq leftArgument rightArgument hSplit.right)

/-! ## Term pairs -/

/-- Componentwise Boolean equality on term pairs. -/
def gccPairBeq (leftPair rightPair : GccTerm × GccTerm) : Bool :=
  gccTermBeq leftPair.fst rightPair.fst && gccTermBeq leftPair.snd rightPair.snd

/-- Reflexivity of `gccPairBeq`. -/
theorem gccPairBeqRefl (pair : GccTerm × GccTerm) : gccPairBeq pair pair = true := by
  show (gccTermBeq pair.fst pair.fst && gccTermBeq pair.snd pair.snd) = true
  rw [gccTermBeqRefl pair.fst, gccTermBeqRefl pair.snd]
  rfl

/-- `gccPairBeq` sound: beq-true pairs are equal. -/
theorem gccPairBeqEq : (leftPair rightPair : GccTerm × GccTerm) →
    gccPairBeq leftPair rightPair = true → leftPair = rightPair
  | (leftFirst, leftSecond), (rightFirst, rightSecond), hBeq =>
      have hSplit := gccBoolAndElim (gccTermBeq leftFirst rightFirst)
        (gccTermBeq leftSecond rightSecond) hBeq
      congr (congrArg Prod.mk (gccTermBeqEq leftFirst rightFirst hSplit.left))
        (gccTermBeqEq leftSecond rightSecond hSplit.right)

/-! ## Bespoke list kit (monomorphic, cons-only) -/

/-- Indexed access into an equation list. -/
def gccListGetPair : List (GccTerm × GccTerm) → Nat → Option (GccTerm × GccTerm)
  | [], 0 => none
  | [], Nat.succ _ => none
  | headPair :: _, 0 => some headPair
  | _ :: rest, Nat.succ previousIndex => gccListGetPair rest previousIndex

/-- Boolean membership in a term list. -/
def gccTermListHasMember : List GccTerm → GccTerm → Bool
  | [], _ => false
  | headTerm :: rest, candidate =>
      cond (gccTermBeq candidate headTerm) true (gccTermListHasMember rest candidate)

/-- Boolean membership in a pair list. -/
def gccPairListHasMember : List (GccTerm × GccTerm) → (GccTerm × GccTerm) → Bool
  | [], _ => false
  | headPair :: rest, candidatePair =>
      cond (gccPairBeq candidatePair headPair) true (gccPairListHasMember rest candidatePair)

/-- Deduplicating insertion into a term list. -/
def gccTermListInsert (accumulated : List GccTerm) (newTerm : GccTerm) : List GccTerm :=
  cond (gccTermListHasMember accumulated newTerm) accumulated (newTerm :: accumulated)

/-- Deduplicating insertion into a pair list. -/
def gccPairListInsert (table : List (GccTerm × GccTerm)) (candidatePair : GccTerm × GccTerm) :
    List (GccTerm × GccTerm) :=
  cond (gccPairListHasMember table candidatePair) table (candidatePair :: table)

/-- Deduplicating insertion of a whole candidate list (left fold). -/
def gccPairListInsertAll : List (GccTerm × GccTerm) → List (GccTerm × GccTerm) →
    List (GccTerm × GccTerm)
  | table, [] => table
  | table, candidatePair :: rest =>
      gccPairListInsertAll (gccPairListInsert table candidatePair) rest

/-- Cons-only append of pair lists. -/
def gccPairListAppend : List (GccTerm × GccTerm) → List (GccTerm × GccTerm) →
    List (GccTerm × GccTerm)
  | [], rightList => rightList
  | headPair :: rest, rightList => headPair :: gccPairListAppend rest rightList

/-- Does the pair list carry no beq-duplicates? -/
def gccPairListHasNoDup : List (GccTerm × GccTerm) → Bool
  | [] => true
  | headPair :: rest =>
      cond (gccPairListHasMember rest headPair) false (gccPairListHasNoDup rest)

/-- Remove the first beq-match of a target pair. -/
def gccPairListErase : List (GccTerm × GccTerm) → (GccTerm × GccTerm) →
    List (GccTerm × GccTerm)
  | [], _ => []
  | headPair :: rest, targetPair =>
      cond (gccPairBeq targetPair headPair) rest (headPair :: gccPairListErase rest targetPair)

/-! ### Membership lemmas -/

/-- Head membership from a beq hit. -/
theorem gccTermMemberHeadOfBeq (headTerm : GccTerm) (rest : List GccTerm)
    (candidate : GccTerm) (hBeq : gccTermBeq candidate headTerm = true) :
    gccTermListHasMember (headTerm :: rest) candidate = true := by
  simp only [gccTermListHasMember]
  rw [hBeq]
  rfl

/-- Tail membership lifts over a cons. -/
theorem gccTermMemberTail (headTerm : GccTerm) (rest : List GccTerm) (candidate : GccTerm)
    (hMember : gccTermListHasMember rest candidate = true) :
    gccTermListHasMember (headTerm :: rest) candidate = true := by
  simp only [gccTermListHasMember]
  cases hBeq : gccTermBeq candidate headTerm with
  | true => rfl
  | false => exact hMember

/-- Head membership from a beq hit (pair version). -/
theorem gccPairMemberHeadOfBeq (headPair : GccTerm × GccTerm) (rest : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm) (hBeq : gccPairBeq candidatePair headPair = true) :
    gccPairListHasMember (headPair :: rest) candidatePair = true := by
  simp only [gccPairListHasMember]
  rw [hBeq]
  rfl

/-- Tail membership lifts over a cons (pair version). -/
theorem gccPairMemberTail (headPair : GccTerm × GccTerm) (rest : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm)
    (hMember : gccPairListHasMember rest candidatePair = true) :
    gccPairListHasMember (headPair :: rest) candidatePair = true := by
  simp only [gccPairListHasMember]
  cases hBeq : gccPairBeq candidatePair headPair with
  | true => rfl
  | false => exact hMember

/-- Cons membership splits into a head beq hit or tail membership. -/
theorem gccPairMemberConsSplit (headPair : GccTerm × GccTerm) (rest : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm)
    (hMember : gccPairListHasMember (headPair :: rest) candidatePair = true) :
    gccPairBeq candidatePair headPair = true ∨ gccPairListHasMember rest candidatePair = true := by
  simp only [gccPairListHasMember] at hMember
  cases hBeq : gccPairBeq candidatePair headPair with
  | true => exact Or.inl rfl
  | false =>
      rw [hBeq] at hMember
      exact Or.inr hMember

/-- Insertion contains the inserted pair. -/
theorem gccPairInsertContainsSelf (table : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm) :
    gccPairListHasMember (gccPairListInsert table candidatePair) candidatePair = true := by
  cases hPresent : gccPairListHasMember table candidatePair with
  | true =>
      have hUnfold : gccPairListInsert table candidatePair = table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]; exact hPresent
  | false =>
      have hUnfold : gccPairListInsert table candidatePair = candidatePair :: table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]
      exact gccPairMemberHeadOfBeq candidatePair table candidatePair
        (gccPairBeqRefl candidatePair)

/-- Insertion keeps old members. -/
theorem gccPairInsertKeepsMember (table : List (GccTerm × GccTerm))
    (candidatePair oldPair : GccTerm × GccTerm)
    (hMember : gccPairListHasMember table oldPair = true) :
    gccPairListHasMember (gccPairListInsert table candidatePair) oldPair = true := by
  cases hPresent : gccPairListHasMember table candidatePair with
  | true =>
      have hUnfold : gccPairListInsert table candidatePair = table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]; exact hMember
  | false =>
      have hUnfold : gccPairListInsert table candidatePair = candidatePair :: table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]
      exact gccPairMemberTail candidatePair table oldPair hMember

/-- Bulk insertion keeps old members. -/
theorem gccPairInsertAllKeepsMember : (candidates table : List (GccTerm × GccTerm)) →
    (oldPair : GccTerm × GccTerm) → gccPairListHasMember table oldPair = true →
    gccPairListHasMember (gccPairListInsertAll table candidates) oldPair = true
  | [], _, _, hMember => hMember
  | candidatePair :: rest, table, oldPair, hMember =>
      gccPairInsertAllKeepsMember rest (gccPairListInsert table candidatePair) oldPair
        (gccPairInsertKeepsMember table candidatePair oldPair hMember)

/-- Bulk insertion contains every candidate. -/
theorem gccPairInsertAllAddsAll : (candidates table : List (GccTerm × GccTerm)) →
    (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember candidates candidatePair = true →
    gccPairListHasMember (gccPairListInsertAll table candidates) candidatePair = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headCandidate :: rest, table, candidatePair, hMember => by
      cases hBeq : gccPairBeq candidatePair headCandidate with
      | true =>
          have hEq : candidatePair = headCandidate := gccPairBeqEq candidatePair headCandidate hBeq
          refine gccPairInsertAllKeepsMember rest (gccPairListInsert table headCandidate)
            candidatePair ?_
          rw [hEq]
          exact gccPairInsertContainsSelf table headCandidate
      | false =>
          simp only [gccPairListHasMember] at hMember
          rw [hBeq] at hMember
          exact gccPairInsertAllAddsAll rest (gccPairListInsert table headCandidate)
            candidatePair hMember

/-- Bulk-insertion membership inverts to an old member or a candidate. -/
theorem gccPairInsertAllInversion : (candidates table : List (GccTerm × GccTerm)) →
    (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember (gccPairListInsertAll table candidates) candidatePair = true →
    gccPairListHasMember table candidatePair = true ∨
      gccPairListHasMember candidates candidatePair = true
  | [], _, _, hMember => Or.inl hMember
  | headCandidate :: rest, table, candidatePair, hMember => by
      have hSplit := gccPairInsertAllInversion rest (gccPairListInsert table headCandidate)
        candidatePair hMember
      cases hSplit with
      | inr hInRest =>
          exact Or.inr (gccPairMemberTail headCandidate rest candidatePair hInRest)
      | inl hInInsert =>
          cases hPresent : gccPairListHasMember table headCandidate with
          | true =>
              have hUnfold : gccPairListInsert table headCandidate = table := by
                simp only [gccPairListInsert]; rw [hPresent]; rfl
              rw [hUnfold] at hInInsert
              exact Or.inl hInInsert
          | false =>
              have hUnfold : gccPairListInsert table headCandidate = headCandidate :: table := by
                simp only [gccPairListInsert]; rw [hPresent]; rfl
              rw [hUnfold] at hInInsert
              cases gccPairMemberConsSplit headCandidate table candidatePair hInInsert with
              | inl hBeq =>
                  exact Or.inr (gccPairMemberHeadOfBeq headCandidate rest candidatePair hBeq)
              | inr hInTable => exact Or.inl hInTable

/-! ### Length growth and stability of bulk insertion -/

/-- Bulk insertion only grows the table. -/
theorem gccPairInsertAllGrows : (candidates table : List (GccTerm × GccTerm)) →
    ∃ growth, (gccPairListInsertAll table candidates).length = table.length + growth
  | [], table => ⟨0, (Nat.add_zero table.length).symm⟩
  | headCandidate :: rest, table => by
      cases hPresent : gccPairListHasMember table headCandidate with
      | true =>
          obtain ⟨growth, hGrowth⟩ := gccPairInsertAllGrows rest table
          refine ⟨growth, ?_⟩
          have hUnfold : gccPairListInsert table headCandidate = table := by
            simp only [gccPairListInsert]; rw [hPresent]; rfl
          show (gccPairListInsertAll (gccPairListInsert table headCandidate) rest).length =
            table.length + growth
          rw [hUnfold]
          exact hGrowth
      | false =>
          obtain ⟨growth, hGrowth⟩ := gccPairInsertAllGrows rest (headCandidate :: table)
          refine ⟨1 + growth, ?_⟩
          have hUnfold : gccPairListInsert table headCandidate = headCandidate :: table := by
            simp only [gccPairListInsert]; rw [hPresent]; rfl
          show (gccPairListInsertAll (gccPairListInsert table headCandidate) rest).length =
            table.length + (1 + growth)
          rw [hUnfold, hGrowth]
          show (table.length + 1) + growth = table.length + (1 + growth)
          exact Nat.add_assoc table.length 1 growth

/-- A length-stable bulk insertion changed nothing and had every candidate present. -/
theorem gccPairInsertAllStable : (candidates table : List (GccTerm × GccTerm)) →
    (gccPairListInsertAll table candidates).length = table.length →
    gccPairListInsertAll table candidates = table ∧
      (∀ candidatePair, gccPairListHasMember candidates candidatePair = true →
        gccPairListHasMember table candidatePair = true)
  | [], _, _ => ⟨rfl, fun _ hMember => Bool.noConfusion hMember⟩
  | headCandidate :: rest, table, hLength => by
      cases hPresent : gccPairListHasMember table headCandidate with
      | true =>
          have hUnfold : gccPairListInsert table headCandidate = table := by
            simp only [gccPairListInsert]; rw [hPresent]; rfl
          have hStep : gccPairListInsertAll table (headCandidate :: rest) =
              gccPairListInsertAll table rest := by
            show gccPairListInsertAll (gccPairListInsert table headCandidate) rest =
              gccPairListInsertAll table rest
            rw [hUnfold]
          rw [hStep] at hLength
          obtain ⟨hStable, hAllPresent⟩ := gccPairInsertAllStable rest table hLength
          refine ⟨hStep.trans hStable, ?_⟩
          intro candidatePair hMember
          cases gccPairMemberConsSplit headCandidate rest candidatePair hMember with
          | inl hBeq =>
              have hEq : candidatePair = headCandidate :=
                gccPairBeqEq candidatePair headCandidate hBeq
              rw [hEq]
              exact hPresent
          | inr hInRest => exact hAllPresent candidatePair hInRest
      | false =>
          have hUnfold : gccPairListInsert table headCandidate = headCandidate :: table := by
            simp only [gccPairListInsert]; rw [hPresent]; rfl
          have hStep : gccPairListInsertAll table (headCandidate :: rest) =
              gccPairListInsertAll (headCandidate :: table) rest := by
            show gccPairListInsertAll (gccPairListInsert table headCandidate) rest =
              gccPairListInsertAll (headCandidate :: table) rest
            rw [hUnfold]
          rw [hStep] at hLength
          obtain ⟨growth, hGrowth⟩ := gccPairInsertAllGrows rest (headCandidate :: table)
          rw [hGrowth] at hLength
          have hAssoc : (table.length + 1) + growth = table.length + (1 + growth) :=
            Nat.add_assoc table.length 1 growth
          have hZero : 1 + growth = 0 :=
            gccNatAddSelfImpliesZero table.length (1 + growth) (hAssoc.symm.trans hLength)
          rw [Nat.add_comm] at hZero
          exact Nat.noConfusion hZero

/-! ### NoDup preservation -/

/-- Insertion preserves duplicate-freedom. -/
theorem gccPairInsertKeepsNoDup (table : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm) (hNoDup : gccPairListHasNoDup table = true) :
    gccPairListHasNoDup (gccPairListInsert table candidatePair) = true := by
  cases hPresent : gccPairListHasMember table candidatePair with
  | true =>
      have hUnfold : gccPairListInsert table candidatePair = table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]; exact hNoDup
  | false =>
      have hUnfold : gccPairListInsert table candidatePair = candidatePair :: table := by
        simp only [gccPairListInsert]; rw [hPresent]; rfl
      rw [hUnfold]
      simp only [gccPairListHasNoDup]
      rw [hPresent]
      exact hNoDup

/-- Bulk insertion preserves duplicate-freedom. -/
theorem gccPairInsertAllKeepsNoDup : (candidates table : List (GccTerm × GccTerm)) →
    gccPairListHasNoDup table = true →
    gccPairListHasNoDup (gccPairListInsertAll table candidates) = true
  | [], _, hNoDup => hNoDup
  | headCandidate :: rest, table, hNoDup =>
      gccPairInsertAllKeepsNoDup rest (gccPairListInsert table headCandidate)
        (gccPairInsertKeepsNoDup table headCandidate hNoDup)

/-! ### Erasure and the constructive pigeonhole -/

/-- Erasing a present pair shortens the list by exactly one. -/
theorem gccPairEraseShortens : (list : List (GccTerm × GccTerm)) →
    (targetPair : GccTerm × GccTerm) → gccPairListHasMember list targetPair = true →
    list.length = (gccPairListErase list targetPair).length + 1
  | [], _, hMember => Bool.noConfusion hMember
  | headPair :: rest, targetPair, hMember => by
      cases hBeq : gccPairBeq targetPair headPair with
      | true =>
          have hUnfold : gccPairListErase (headPair :: rest) targetPair = rest := by
            simp only [gccPairListErase]; rw [hBeq]; rfl
          rw [hUnfold]
          rfl
      | false =>
          have hUnfold : gccPairListErase (headPair :: rest) targetPair =
              headPair :: gccPairListErase rest targetPair := by
            simp only [gccPairListErase]; rw [hBeq]; rfl
          have hTailMember : gccPairListHasMember rest targetPair = true := by
            simp only [gccPairListHasMember] at hMember
            have hSelfBeq : gccPairBeq targetPair targetPair = true := gccPairBeqRefl targetPair
            cases hHeadBeq : gccPairBeq targetPair headPair with
            | true => exact Bool.noConfusion (hBeq.symm.trans hHeadBeq)
            | false =>
                rw [hHeadBeq] at hMember
                exact hMember
          rw [hUnfold]
          show rest.length + 1 = ((gccPairListErase rest targetPair).length + 1) + 1
          rw [gccPairEraseShortens rest targetPair hTailMember]

/-- Erasing one pair keeps every beq-distinct member. -/
theorem gccPairEraseKeepsOthers : (list : List (GccTerm × GccTerm)) →
    (targetPair otherPair : GccTerm × GccTerm) →
    gccPairListHasMember list otherPair = true → gccPairBeq otherPair targetPair = false →
    gccPairListHasMember (gccPairListErase list targetPair) otherPair = true
  | [], _, _, hMember, _ => Bool.noConfusion hMember
  | headPair :: rest, targetPair, otherPair, hMember, hDistinct => by
      cases hBeq : gccPairBeq targetPair headPair with
      | true =>
          have hUnfold : gccPairListErase (headPair :: rest) targetPair = rest := by
            simp only [gccPairListErase]; rw [hBeq]; rfl
          rw [hUnfold]
          cases gccPairMemberConsSplit headPair rest otherPair hMember with
          | inr hInRest => exact hInRest
          | inl hOtherHead =>
              have hOtherEq : otherPair = headPair := gccPairBeqEq otherPair headPair hOtherHead
              have hTargetEq : targetPair = headPair := gccPairBeqEq targetPair headPair hBeq
              rw [hOtherEq, hTargetEq, gccPairBeqRefl headPair] at hDistinct
              exact Bool.noConfusion hDistinct
      | false =>
          have hUnfold : gccPairListErase (headPair :: rest) targetPair =
              headPair :: gccPairListErase rest targetPair := by
            simp only [gccPairListErase]; rw [hBeq]; rfl
          rw [hUnfold]
          cases gccPairMemberConsSplit headPair rest otherPair hMember with
          | inl hOtherHead =>
              exact gccPairMemberHeadOfBeq headPair (gccPairListErase rest targetPair)
                otherPair hOtherHead
          | inr hInRest =>
              exact gccPairMemberTail headPair (gccPairListErase rest targetPair) otherPair
                (gccPairEraseKeepsOthers rest targetPair otherPair hInRest hDistinct)

/-- Constructive pigeonhole: a duplicate-free list of members of a superset is no longer
than the superset. -/
theorem gccNoDupBoundedByLength : (subsetList supersetList : List (GccTerm × GccTerm)) →
    gccPairListHasNoDup subsetList = true →
    (∀ candidatePair, gccPairListHasMember subsetList candidatePair = true →
      gccPairListHasMember supersetList candidatePair = true) →
    ∃ slack, subsetList.length + slack = supersetList.length
  | [], supersetList, _, _ => ⟨supersetList.length, Nat.zero_add supersetList.length⟩
  | headPair :: rest, supersetList, hNoDup, hSubset => by
      have hHeadFresh : gccPairListHasMember rest headPair = false := by
        cases hMem : gccPairListHasMember rest headPair with
        | false => rfl
        | true =>
            simp only [gccPairListHasNoDup] at hNoDup
            rw [hMem] at hNoDup
            exact Bool.noConfusion hNoDup
      have hRestNoDup : gccPairListHasNoDup rest = true := by
        simp only [gccPairListHasNoDup] at hNoDup
        rw [hHeadFresh] at hNoDup
        exact hNoDup
      have hHeadInSuperset : gccPairListHasMember supersetList headPair = true :=
        hSubset headPair (gccPairMemberHeadOfBeq headPair rest headPair (gccPairBeqRefl headPair))
      have hRestSubset : ∀ candidatePair, gccPairListHasMember rest candidatePair = true →
          gccPairListHasMember (gccPairListErase supersetList headPair) candidatePair = true := by
        intro candidatePair hMember
        have hInSuperset := hSubset candidatePair
          (gccPairMemberTail headPair rest candidatePair hMember)
        have hDistinct : gccPairBeq candidatePair headPair = false := by
          cases hBeq : gccPairBeq candidatePair headPair with
          | false => rfl
          | true =>
              have hEq := gccPairBeqEq candidatePair headPair hBeq
              rw [hEq] at hMember
              rw [hHeadFresh] at hMember
              exact Bool.noConfusion hMember
        exact gccPairEraseKeepsOthers supersetList headPair candidatePair hInSuperset hDistinct
      obtain ⟨slack, hSlack⟩ := gccNoDupBoundedByLength rest
        (gccPairListErase supersetList headPair) hRestNoDup hRestSubset
      refine ⟨slack, ?_⟩
      have hEraseLength := gccPairEraseShortens supersetList headPair hHeadInSuperset
      show (rest.length + 1) + slack = supersetList.length
      rw [Nat.add_assoc, Nat.add_comm 1 slack, ← Nat.add_assoc, hSlack, ← hEraseLength]

/-! ### Append membership -/

/-- Left summand membership lifts into an append. -/
theorem gccPairAppendMemberLeft : (leftList rightList : List (GccTerm × GccTerm)) →
    (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember leftList candidatePair = true →
    gccPairListHasMember (gccPairListAppend leftList rightList) candidatePair = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headPair :: rest, rightList, candidatePair, hMember => by
      cases gccPairMemberConsSplit headPair rest candidatePair hMember with
      | inl hBeq =>
          exact gccPairMemberHeadOfBeq headPair (gccPairListAppend rest rightList)
            candidatePair hBeq
      | inr hInRest =>
          exact gccPairMemberTail headPair (gccPairListAppend rest rightList) candidatePair
            (gccPairAppendMemberLeft rest rightList candidatePair hInRest)

/-- Right summand membership lifts into an append. -/
theorem gccPairAppendMemberRight : (leftList rightList : List (GccTerm × GccTerm)) →
    (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember rightList candidatePair = true →
    gccPairListHasMember (gccPairListAppend leftList rightList) candidatePair = true
  | [], _, _, hMember => hMember
  | headPair :: rest, rightList, candidatePair, hMember =>
      gccPairMemberTail headPair (gccPairListAppend rest rightList) candidatePair
        (gccPairAppendMemberRight rest rightList candidatePair hMember)

/-- Append membership splits into the summands. -/
theorem gccPairAppendInversion : (leftList rightList : List (GccTerm × GccTerm)) →
    (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember (gccPairListAppend leftList rightList) candidatePair = true →
    gccPairListHasMember leftList candidatePair = true ∨
      gccPairListHasMember rightList candidatePair = true
  | [], _, _, hMember => Or.inr hMember
  | headPair :: rest, rightList, candidatePair, hMember => by
      cases gccPairMemberConsSplit headPair (gccPairListAppend rest rightList) candidatePair
          hMember with
      | inl hBeq => exact Or.inl (gccPairMemberHeadOfBeq headPair rest candidatePair hBeq)
      | inr hDeeper =>
          cases gccPairAppendInversion rest rightList candidatePair hDeeper with
          | inl hInLeft =>
              exact Or.inl (gccPairMemberTail headPair rest candidatePair hInLeft)
          | inr hInRight => exact Or.inr hInRight

/-! ### Equation-list index and membership -/

/-- Indexed access implies beq-membership. -/
theorem gccListGetImpliesMember : (equations : List (GccTerm × GccTerm)) → (index : Nat) →
    (pair : GccTerm × GccTerm) → gccListGetPair equations index = some pair →
    gccPairListHasMember equations pair = true
  | [], 0, _, hGet => nomatch hGet
  | [], Nat.succ _, _, hGet => nomatch hGet
  | headPair :: rest, 0, pair, hGet => by
      injection hGet with hEq
      refine gccPairMemberHeadOfBeq headPair rest pair ?_
      rw [← hEq]
      exact gccPairBeqRefl headPair
  | headPair :: rest, Nat.succ previousIndex, pair, hGet =>
      gccPairMemberTail headPair rest pair
        (gccListGetImpliesMember rest previousIndex pair hGet)

/-- Beq-membership yields an index. -/
theorem gccMemberImpliesGet : (equations : List (GccTerm × GccTerm)) →
    (pair : GccTerm × GccTerm) → gccPairListHasMember equations pair = true →
    ∃ index, gccListGetPair equations index = some pair
  | [], _, hMember => Bool.noConfusion hMember
  | headPair :: rest, pair, hMember => by
      cases gccPairMemberConsSplit headPair rest pair hMember with
      | inl hBeq =>
          refine ⟨0, ?_⟩
          rw [gccPairBeqEq pair headPair hBeq]
          rfl
      | inr hInRest =>
          obtain ⟨index, hGet⟩ := gccMemberImpliesGet rest pair hInRest
          exact ⟨Nat.succ index, hGet⟩

/-! ## The subterm universe -/

/-- Collect a term and all its subterms into a deduplicated accumulator. -/
def gccCollectSubterms (accumulated : List GccTerm) : GccTerm → List GccTerm
  | GccTerm.symbol name => gccTermListInsert accumulated (GccTerm.symbol name)
  | GccTerm.apply function argument =>
      gccTermListInsert (gccCollectSubterms (gccCollectSubterms accumulated function) argument)
        (GccTerm.apply function argument)

/-- Is every apply-member's pair of children also a member? -/
def gccUniverseIsSubtermClosed (universeList : List GccTerm) : Prop :=
  ∀ function argument,
    gccTermListHasMember universeList (GccTerm.apply function argument) = true →
    gccTermListHasMember universeList function = true ∧
      gccTermListHasMember universeList argument = true

/-- Term insertion contains the inserted term. -/
theorem gccTermInsertContainsSelf (accumulated : List GccTerm) (newTerm : GccTerm) :
    gccTermListHasMember (gccTermListInsert accumulated newTerm) newTerm = true := by
  cases hPresent : gccTermListHasMember accumulated newTerm with
  | true =>
      have hUnfold : gccTermListInsert accumulated newTerm = accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold]; exact hPresent
  | false =>
      have hUnfold : gccTermListInsert accumulated newTerm = newTerm :: accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold]
      exact gccTermMemberHeadOfBeq newTerm accumulated newTerm (gccTermBeqRefl newTerm)

/-- Term insertion keeps old members. -/
theorem gccTermInsertKeepsMember (accumulated : List GccTerm) (newTerm oldTerm : GccTerm)
    (hMember : gccTermListHasMember accumulated oldTerm = true) :
    gccTermListHasMember (gccTermListInsert accumulated newTerm) oldTerm = true := by
  cases hPresent : gccTermListHasMember accumulated newTerm with
  | true =>
      have hUnfold : gccTermListInsert accumulated newTerm = accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold]; exact hMember
  | false =>
      have hUnfold : gccTermListInsert accumulated newTerm = newTerm :: accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold]
      exact gccTermMemberTail newTerm accumulated oldTerm hMember

/-- Term-insertion membership inverts to an old member or the new term. -/
theorem gccTermInsertInversion (accumulated : List GccTerm) (newTerm candidate : GccTerm)
    (hMember : gccTermListHasMember (gccTermListInsert accumulated newTerm) candidate = true) :
    gccTermListHasMember accumulated candidate = true ∨ candidate = newTerm := by
  cases hPresent : gccTermListHasMember accumulated newTerm with
  | true =>
      have hUnfold : gccTermListInsert accumulated newTerm = accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold] at hMember
      exact Or.inl hMember
  | false =>
      have hUnfold : gccTermListInsert accumulated newTerm = newTerm :: accumulated := by
        simp only [gccTermListInsert]; rw [hPresent]; rfl
      rw [hUnfold] at hMember
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq candidate newTerm with
      | true => exact Or.inr (gccTermBeqEq candidate newTerm hBeq)
      | false =>
          rw [hBeq] at hMember
          exact Or.inl hMember

/-- Collection contains the collected term. -/
theorem gccCollectSubtermsContainsSelf : (term : GccTerm) → (accumulated : List GccTerm) →
    gccTermListHasMember (gccCollectSubterms accumulated term) term = true
  | GccTerm.symbol name, accumulated =>
      gccTermInsertContainsSelf accumulated (GccTerm.symbol name)
  | GccTerm.apply function argument, accumulated =>
      gccTermInsertContainsSelf
        (gccCollectSubterms (gccCollectSubterms accumulated function) argument)
        (GccTerm.apply function argument)

/-- Collection keeps old members. -/
theorem gccCollectSubtermsKeepsMember : (term : GccTerm) → (accumulated : List GccTerm) →
    (oldTerm : GccTerm) → gccTermListHasMember accumulated oldTerm = true →
    gccTermListHasMember (gccCollectSubterms accumulated term) oldTerm = true
  | GccTerm.symbol name, accumulated, oldTerm, hMember =>
      gccTermInsertKeepsMember accumulated (GccTerm.symbol name) oldTerm hMember
  | GccTerm.apply function argument, accumulated, oldTerm, hMember =>
      gccTermInsertKeepsMember
        (gccCollectSubterms (gccCollectSubterms accumulated function) argument)
        (GccTerm.apply function argument) oldTerm
        (gccCollectSubtermsKeepsMember argument (gccCollectSubterms accumulated function)
          oldTerm (gccCollectSubtermsKeepsMember function accumulated oldTerm hMember))

/-- Inserting a symbol preserves subterm-closedness. -/
theorem gccTermInsertSymbolKeepsClosed (accumulated : List GccTerm) (name : Nat)
    (hClosed : gccUniverseIsSubtermClosed accumulated) :
    gccUniverseIsSubtermClosed (gccTermListInsert accumulated (GccTerm.symbol name)) := by
  intro function argument hMember
  cases gccTermInsertInversion accumulated (GccTerm.symbol name)
      (GccTerm.apply function argument) hMember with
  | inr hEq => exact GccTerm.noConfusion hEq
  | inl hInOld =>
      obtain ⟨hFunction, hArgument⟩ := hClosed function argument hInOld
      exact ⟨gccTermInsertKeepsMember accumulated (GccTerm.symbol name) function hFunction,
        gccTermInsertKeepsMember accumulated (GccTerm.symbol name) argument hArgument⟩

/-- Inserting an apply node whose children are already present preserves closedness. -/
theorem gccTermInsertApplyKeepsClosed (accumulated : List GccTerm)
    (function argument : GccTerm) (hClosed : gccUniverseIsSubtermClosed accumulated)
    (hFunctionIn : gccTermListHasMember accumulated function = true)
    (hArgumentIn : gccTermListHasMember accumulated argument = true) :
    gccUniverseIsSubtermClosed
      (gccTermListInsert accumulated (GccTerm.apply function argument)) := by
  intro innerFunction innerArgument hMember
  cases gccTermInsertInversion accumulated (GccTerm.apply function argument)
      (GccTerm.apply innerFunction innerArgument) hMember with
  | inr hEq =>
      injection hEq with hFunctionEq hArgumentEq
      rw [hFunctionEq, hArgumentEq]
      exact ⟨gccTermInsertKeepsMember accumulated (GccTerm.apply function argument) function
          hFunctionIn,
        gccTermInsertKeepsMember accumulated (GccTerm.apply function argument) argument
          hArgumentIn⟩
  | inl hInOld =>
      obtain ⟨hFunction, hArgument⟩ := hClosed innerFunction innerArgument hInOld
      exact ⟨gccTermInsertKeepsMember accumulated (GccTerm.apply function argument)
          innerFunction hFunction,
        gccTermInsertKeepsMember accumulated (GccTerm.apply function argument)
          innerArgument hArgument⟩

/-- Collection preserves subterm-closedness. -/
theorem gccCollectSubtermsKeepsClosed : (term : GccTerm) → (accumulated : List GccTerm) →
    gccUniverseIsSubtermClosed accumulated →
    gccUniverseIsSubtermClosed (gccCollectSubterms accumulated term)
  | GccTerm.symbol name, accumulated, hClosed =>
      gccTermInsertSymbolKeepsClosed accumulated name hClosed
  | GccTerm.apply function argument, accumulated, hClosed => by
      have hClosedFunction := gccCollectSubtermsKeepsClosed function accumulated hClosed
      have hClosedArgument :=
        gccCollectSubtermsKeepsClosed argument (gccCollectSubterms accumulated function)
          hClosedFunction
      refine gccTermInsertApplyKeepsClosed
        (gccCollectSubterms (gccCollectSubterms accumulated function) argument)
        function argument hClosedArgument ?_ ?_
      · exact gccCollectSubtermsKeepsMember argument (gccCollectSubterms accumulated function)
          function (gccCollectSubtermsContainsSelf function accumulated)
      · exact gccCollectSubtermsContainsSelf argument (gccCollectSubterms accumulated function)

/-- Collect every subterm of every equation side. -/
def gccCollectEquationSubterms : List (GccTerm × GccTerm) → List GccTerm → List GccTerm
  | [], accumulated => accumulated
  | equationPair :: rest, accumulated =>
      gccCollectEquationSubterms rest
        (gccCollectSubterms (gccCollectSubterms accumulated equationPair.fst) equationPair.snd)

/-- Equation collection keeps old members. -/
theorem gccCollectEquationKeepsMember : (equations : List (GccTerm × GccTerm)) →
    (accumulated : List GccTerm) → (oldTerm : GccTerm) →
    gccTermListHasMember accumulated oldTerm = true →
    gccTermListHasMember (gccCollectEquationSubterms equations accumulated) oldTerm = true
  | [], _, _, hMember => hMember
  | equationPair :: rest, accumulated, oldTerm, hMember =>
      gccCollectEquationKeepsMember rest _ oldTerm
        (gccCollectSubtermsKeepsMember equationPair.snd
          (gccCollectSubterms accumulated equationPair.fst) oldTerm
          (gccCollectSubtermsKeepsMember equationPair.fst accumulated oldTerm hMember))

/-- Equation collection preserves subterm-closedness. -/
theorem gccCollectEquationKeepsClosed : (equations : List (GccTerm × GccTerm)) →
    (accumulated : List GccTerm) → gccUniverseIsSubtermClosed accumulated →
    gccUniverseIsSubtermClosed (gccCollectEquationSubterms equations accumulated)
  | [], _, hClosed => hClosed
  | equationPair :: rest, accumulated, hClosed =>
      gccCollectEquationKeepsClosed rest _
        (gccCollectSubtermsKeepsClosed equationPair.snd
          (gccCollectSubterms accumulated equationPair.fst)
          (gccCollectSubtermsKeepsClosed equationPair.fst accumulated hClosed))

/-- Both sides of every listed equation land in the collected universe. -/
theorem gccCollectEquationHasSides : (equations : List (GccTerm × GccTerm)) →
    (accumulated : List GccTerm) → (pair : GccTerm × GccTerm) →
    gccPairListHasMember equations pair = true →
    gccTermListHasMember (gccCollectEquationSubterms equations accumulated) pair.fst = true ∧
      gccTermListHasMember (gccCollectEquationSubterms equations accumulated) pair.snd = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | equationPair :: rest, accumulated, pair, hMember => by
      cases gccPairMemberConsSplit equationPair rest pair hMember with
      | inl hBeq =>
          have hEq : pair = equationPair := gccPairBeqEq pair equationPair hBeq
          rw [hEq]
          constructor
          · exact gccCollectEquationKeepsMember rest _ equationPair.fst
              (gccCollectSubtermsKeepsMember equationPair.snd
                (gccCollectSubterms accumulated equationPair.fst) equationPair.fst
                (gccCollectSubtermsContainsSelf equationPair.fst accumulated))
          · exact gccCollectEquationKeepsMember rest _ equationPair.snd
              (gccCollectSubtermsContainsSelf equationPair.snd
                (gccCollectSubterms accumulated equationPair.fst))
      | inr hInRest =>
          exact gccCollectEquationHasSides rest _ pair hInRest

/-- The query universe: all equation subterms plus all subterms of both query terms. -/
def gccBuildQueryUniverse (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm) : List GccTerm :=
  gccCollectSubterms
    (gccCollectSubterms (gccCollectEquationSubterms equations []) sourceTerm) targetTerm

/-- The empty list is vacuously subterm-closed. -/
theorem gccNilIsSubtermClosed : gccUniverseIsSubtermClosed [] := by
  intro function argument hMember
  exact Bool.noConfusion hMember

/-- The query universe is subterm-closed. -/
theorem gccBuildQueryUniverseIsClosed (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm) :
    gccUniverseIsSubtermClosed (gccBuildQueryUniverse equations sourceTerm targetTerm) :=
  gccCollectSubtermsKeepsClosed targetTerm _
    (gccCollectSubtermsKeepsClosed sourceTerm _
      (gccCollectEquationKeepsClosed equations [] gccNilIsSubtermClosed))

/-- Both sides of every indexed equation are members of the query universe. -/
theorem gccBuildQueryUniverseHasSides (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm) :
    ∀ index leftTerm rightTerm,
      gccListGetPair equations index = some (leftTerm, rightTerm) →
      gccTermListHasMember (gccBuildQueryUniverse equations sourceTerm targetTerm)
          leftTerm = true ∧
        gccTermListHasMember (gccBuildQueryUniverse equations sourceTerm targetTerm)
          rightTerm = true := by
  intro index leftTerm rightTerm hGet
  have hMember := gccListGetImpliesMember equations index (leftTerm, rightTerm) hGet
  obtain ⟨hLeft, hRight⟩ := gccCollectEquationHasSides equations [] (leftTerm, rightTerm) hMember
  constructor
  · exact gccCollectSubtermsKeepsMember targetTerm _ leftTerm
      (gccCollectSubtermsKeepsMember sourceTerm _ leftTerm hLeft)
  · exact gccCollectSubtermsKeepsMember targetTerm _ rightTerm
      (gccCollectSubtermsKeepsMember sourceTerm _ rightTerm hRight)

/-! ## The ground equational judgment -/

/-- Ground equational derivability from a finite equation list: axioms by index, plus
reflexivity, symmetry, transitivity, and congruence of application. -/
inductive GccDeriv (equations : List (GccTerm × GccTerm)) : GccTerm → GccTerm → Prop where
  | byEquation (equationIndex : Nat) (leftTerm rightTerm : GccTerm)
      (lookupWitness : gccListGetPair equations equationIndex = some (leftTerm, rightTerm)) :
      GccDeriv equations leftTerm rightTerm
  | byRefl (term : GccTerm) : GccDeriv equations term term
  | bySymm (leftTerm rightTerm : GccTerm)
      (forwardDeriv : GccDeriv equations leftTerm rightTerm) :
      GccDeriv equations rightTerm leftTerm
  | byTrans (leftTerm middleTerm rightTerm : GccTerm)
      (leftDeriv : GccDeriv equations leftTerm middleTerm)
      (rightDeriv : GccDeriv equations middleTerm rightTerm) :
      GccDeriv equations leftTerm rightTerm
  | byCongruence (leftFunction rightFunction leftArgument rightArgument : GccTerm)
      (functionDeriv : GccDeriv equations leftFunction rightFunction)
      (argumentDeriv : GccDeriv equations leftArgument rightArgument) :
      GccDeriv equations (GccTerm.apply leftFunction leftArgument)
        (GccTerm.apply rightFunction rightArgument)

/-! ## Saturation candidates -/

/-- Swapped copies of every table pair (symmetry candidates). -/
def gccSwapPairs : List (GccTerm × GccTerm) → List (GccTerm × GccTerm)
  | [] => []
  | headPair :: rest => (headPair.snd, headPair.fst) :: gccSwapPairs rest

/-- Reflexive pairs over the universe. -/
def gccMakeReflPairs : List GccTerm → List (GccTerm × GccTerm)
  | [] => []
  | headTerm :: rest => (headTerm, headTerm) :: gccMakeReflPairs rest

/-- Transitivity joins of one fixed left pair against a scanned table. -/
def gccJoinThroughLeft (leftPair : GccTerm × GccTerm) : List (GccTerm × GccTerm) →
    List (GccTerm × GccTerm)
  | [] => []
  | rightPair :: rest =>
      cond (gccTermBeq leftPair.snd rightPair.fst)
        ((leftPair.fst, rightPair.snd) :: gccJoinThroughLeft leftPair rest)
        (gccJoinThroughLeft leftPair rest)

/-- All transitivity candidates: every join of a scanned pair with the full table. -/
def gccCollectTransCandidates (fullTable : List (GccTerm × GccTerm)) :
    List (GccTerm × GccTerm) → List (GccTerm × GccTerm)
  | [] => []
  | leftPair :: rest =>
      gccPairListAppend (gccJoinThroughLeft leftPair fullTable)
        (gccCollectTransCandidates fullTable rest)

/-- Congruence candidates for one fixed left apply node against an inner universe scan. -/
def gccCongRightScan (table : List (GccTerm × GccTerm))
    (leftFunction leftArgument : GccTerm) : List GccTerm → List (GccTerm × GccTerm)
  | [] => []
  | GccTerm.symbol _name :: rest => gccCongRightScan table leftFunction leftArgument rest
  | GccTerm.apply rightFunction rightArgument :: rest =>
      cond (gccPairListHasMember table (leftFunction, rightFunction))
        (cond (gccPairListHasMember table (leftArgument, rightArgument))
          ((GccTerm.apply leftFunction leftArgument,
              GccTerm.apply rightFunction rightArgument) ::
            gccCongRightScan table leftFunction leftArgument rest)
          (gccCongRightScan table leftFunction leftArgument rest))
        (gccCongRightScan table leftFunction leftArgument rest)

/-- All congruence candidates: universe apply nodes whose children are table-related. -/
def gccCollectCongCandidates (table : List (GccTerm × GccTerm))
    (innerUniverse : List GccTerm) : List GccTerm → List (GccTerm × GccTerm)
  | [] => []
  | GccTerm.symbol _name :: rest => gccCollectCongCandidates table innerUniverse rest
  | GccTerm.apply leftFunction leftArgument :: rest =>
      gccPairListAppend (gccCongRightScan table leftFunction leftArgument innerUniverse)
        (gccCollectCongCandidates table innerUniverse rest)

/-! ### Candidate intro lemmas -/

/-- Symmetry candidates contain every swapped table pair. -/
theorem gccSwapPairsContains : (table : List (GccTerm × GccTerm)) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember table (leftTerm, rightTerm) = true →
    gccPairListHasMember (gccSwapPairs table) (rightTerm, leftTerm) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headPair :: rest, leftTerm, rightTerm, hMember => by
      cases gccPairMemberConsSplit headPair rest (leftTerm, rightTerm) hMember with
      | inl hBeq =>
          have hEq : (leftTerm, rightTerm) = headPair :=
            gccPairBeqEq (leftTerm, rightTerm) headPair hBeq
          have hFst : headPair.fst = leftTerm := (congrArg Prod.fst hEq).symm
          have hSnd : headPair.snd = rightTerm := (congrArg Prod.snd hEq).symm
          refine gccPairMemberHeadOfBeq (headPair.snd, headPair.fst) (gccSwapPairs rest)
            (rightTerm, leftTerm) ?_
          rw [hFst, hSnd]
          exact gccPairBeqRefl (rightTerm, leftTerm)
      | inr hInRest =>
          exact gccPairMemberTail (headPair.snd, headPair.fst) (gccSwapPairs rest)
            (rightTerm, leftTerm) (gccSwapPairsContains rest leftTerm rightTerm hInRest)

/-- Symmetry-candidate membership inverts to a swapped table pair. -/
theorem gccSwapPairsInversion : (table : List (GccTerm × GccTerm)) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccSwapPairs table) (leftTerm, rightTerm) = true →
    gccPairListHasMember table (rightTerm, leftTerm) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headPair :: rest, leftTerm, rightTerm, hMember => by
      cases gccPairMemberConsSplit (headPair.snd, headPair.fst) (gccSwapPairs rest)
          (leftTerm, rightTerm) hMember with
      | inl hBeq =>
          have hEq : (leftTerm, rightTerm) = (headPair.snd, headPair.fst) :=
            gccPairBeqEq (leftTerm, rightTerm) (headPair.snd, headPair.fst) hBeq
          have hFst : leftTerm = headPair.snd := congrArg Prod.fst hEq
          have hSnd : rightTerm = headPair.fst := congrArg Prod.snd hEq
          refine gccPairMemberHeadOfBeq headPair rest (rightTerm, leftTerm) ?_
          rw [hFst, hSnd]
          exact gccPairBeqRefl (headPair.fst, headPair.snd)
      | inr hInRest =>
          exact gccPairMemberTail headPair rest (rightTerm, leftTerm)
            (gccSwapPairsInversion rest leftTerm rightTerm hInRest)

/-- Reflexive pairs contain the diagonal of every universe member. -/
theorem gccMakeReflPairsContains : (universeList : List GccTerm) → (memberTerm : GccTerm) →
    gccTermListHasMember universeList memberTerm = true →
    gccPairListHasMember (gccMakeReflPairs universeList) (memberTerm, memberTerm) = true
  | [], _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, memberTerm, hMember => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq memberTerm headTerm with
      | true =>
          have hEq : memberTerm = headTerm := gccTermBeqEq memberTerm headTerm hBeq
          refine gccPairMemberHeadOfBeq (headTerm, headTerm) (gccMakeReflPairs rest)
            (memberTerm, memberTerm) ?_
          rw [hEq]
          exact gccPairBeqRefl (headTerm, headTerm)
      | false =>
          rw [hBeq] at hMember
          exact gccPairMemberTail (headTerm, headTerm) (gccMakeReflPairs rest)
            (memberTerm, memberTerm) (gccMakeReflPairsContains rest memberTerm hMember)

/-- Reflexive-pair membership inverts to a diagonal over a universe member. -/
theorem gccMakeReflPairsInversion : (universeList : List GccTerm) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccMakeReflPairs universeList) (leftTerm, rightTerm) = true →
    ∃ baseTerm, leftTerm = baseTerm ∧ rightTerm = baseTerm ∧
      gccTermListHasMember universeList baseTerm = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, leftTerm, rightTerm, hMember => by
      cases gccPairMemberConsSplit (headTerm, headTerm) (gccMakeReflPairs rest)
          (leftTerm, rightTerm) hMember with
      | inl hBeq =>
          have hEq : (leftTerm, rightTerm) = (headTerm, headTerm) :=
            gccPairBeqEq (leftTerm, rightTerm) (headTerm, headTerm) hBeq
          exact ⟨headTerm, congrArg Prod.fst hEq, congrArg Prod.snd hEq,
            gccTermMemberHeadOfBeq headTerm rest headTerm (gccTermBeqRefl headTerm)⟩
      | inr hInRest =>
          obtain ⟨baseTerm, hLeft, hRight, hIn⟩ :=
            gccMakeReflPairsInversion rest leftTerm rightTerm hInRest
          exact ⟨baseTerm, hLeft, hRight, gccTermMemberTail headTerm rest baseTerm hIn⟩

/-- Joins contain every completion of the fixed left pair. -/
theorem gccJoinThroughLeftContains (leftPair : GccTerm × GccTerm) :
    (scanList : List (GccTerm × GccTerm)) → (middleTerm rightTerm : GccTerm) →
    gccPairListHasMember scanList (middleTerm, rightTerm) = true →
    leftPair.snd = middleTerm →
    gccPairListHasMember (gccJoinThroughLeft leftPair scanList)
      (leftPair.fst, rightTerm) = true
  | [], _, _, hMember, _ => Bool.noConfusion hMember
  | rightPair :: rest, middleTerm, rightTerm, hMember, hLink => by
      cases gccPairMemberConsSplit rightPair rest (middleTerm, rightTerm) hMember with
      | inl hBeq =>
          have hEq : (middleTerm, rightTerm) = rightPair :=
            gccPairBeqEq (middleTerm, rightTerm) rightPair hBeq
          have hFst : rightPair.fst = middleTerm := (congrArg Prod.fst hEq).symm
          have hSnd : rightPair.snd = rightTerm := (congrArg Prod.snd hEq).symm
          have hCondTrue : gccTermBeq leftPair.snd rightPair.fst = true := by
            rw [hFst, hLink]
            exact gccTermBeqRefl middleTerm
          have hUnfold : gccJoinThroughLeft leftPair (rightPair :: rest) =
              (leftPair.fst, rightPair.snd) :: gccJoinThroughLeft leftPair rest := by
            simp only [gccJoinThroughLeft]; rw [hCondTrue]; rfl
          rw [hUnfold]
          refine gccPairMemberHeadOfBeq (leftPair.fst, rightPair.snd)
            (gccJoinThroughLeft leftPair rest) (leftPair.fst, rightTerm) ?_
          rw [hSnd]
          exact gccPairBeqRefl (leftPair.fst, rightTerm)
      | inr hInRest =>
          have hDeeper := gccJoinThroughLeftContains leftPair rest middleTerm rightTerm
            hInRest hLink
          cases hCond : gccTermBeq leftPair.snd rightPair.fst with
          | true =>
              have hUnfold : gccJoinThroughLeft leftPair (rightPair :: rest) =
                  (leftPair.fst, rightPair.snd) :: gccJoinThroughLeft leftPair rest := by
                simp only [gccJoinThroughLeft]; rw [hCond]; rfl
              rw [hUnfold]
              exact gccPairMemberTail (leftPair.fst, rightPair.snd)
                (gccJoinThroughLeft leftPair rest) (leftPair.fst, rightTerm) hDeeper
          | false =>
              have hUnfold : gccJoinThroughLeft leftPair (rightPair :: rest) =
                  gccJoinThroughLeft leftPair rest := by
                simp only [gccJoinThroughLeft]; rw [hCond]; rfl
              rw [hUnfold]
              exact hDeeper

/-- Join membership inverts to a matching scanned pair. -/
theorem gccJoinThroughLeftInversion (leftPair : GccTerm × GccTerm) :
    (scanList : List (GccTerm × GccTerm)) → (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccJoinThroughLeft leftPair scanList) (leftTerm, rightTerm) = true →
    leftTerm = leftPair.fst ∧
      gccPairListHasMember scanList (leftPair.snd, rightTerm) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | rightPair :: rest, leftTerm, rightTerm, hMember => by
      cases hCond : gccTermBeq leftPair.snd rightPair.fst with
      | false =>
          have hUnfold : gccJoinThroughLeft leftPair (rightPair :: rest) =
              gccJoinThroughLeft leftPair rest := by
            simp only [gccJoinThroughLeft]; rw [hCond]; rfl
          rw [hUnfold] at hMember
          obtain ⟨hLeft, hScan⟩ :=
            gccJoinThroughLeftInversion leftPair rest leftTerm rightTerm hMember
          exact ⟨hLeft, gccPairMemberTail rightPair rest (leftPair.snd, rightTerm) hScan⟩
      | true =>
          have hUnfold : gccJoinThroughLeft leftPair (rightPair :: rest) =
              (leftPair.fst, rightPair.snd) :: gccJoinThroughLeft leftPair rest := by
            simp only [gccJoinThroughLeft]; rw [hCond]; rfl
          rw [hUnfold] at hMember
          cases gccPairMemberConsSplit (leftPair.fst, rightPair.snd)
              (gccJoinThroughLeft leftPair rest) (leftTerm, rightTerm) hMember with
          | inl hBeq =>
              have hEq : (leftTerm, rightTerm) = (leftPair.fst, rightPair.snd) :=
                gccPairBeqEq (leftTerm, rightTerm) (leftPair.fst, rightPair.snd) hBeq
              have hLeftEq : leftTerm = leftPair.fst := congrArg Prod.fst hEq
              have hRightEq : rightTerm = rightPair.snd := congrArg Prod.snd hEq
              have hLinkEq : leftPair.snd = rightPair.fst :=
                gccTermBeqEq leftPair.snd rightPair.fst hCond
              refine ⟨hLeftEq, ?_⟩
              refine gccPairMemberHeadOfBeq rightPair rest (leftPair.snd, rightTerm) ?_
              rw [hLinkEq, hRightEq]
              exact gccPairBeqRefl (rightPair.fst, rightPair.snd)
          | inr hInRest =>
              obtain ⟨hLeft, hScan⟩ :=
                gccJoinThroughLeftInversion leftPair rest leftTerm rightTerm hInRest
              exact ⟨hLeft, gccPairMemberTail rightPair rest (leftPair.snd, rightTerm) hScan⟩

/-- Transitivity candidates contain every endpoint join over the table. -/
theorem gccCollectTransContains (fullTable : List (GccTerm × GccTerm)) :
    (scanList : List (GccTerm × GccTerm)) → (leftTerm middleTerm rightTerm : GccTerm) →
    gccPairListHasMember scanList (leftTerm, middleTerm) = true →
    gccPairListHasMember fullTable (middleTerm, rightTerm) = true →
    gccPairListHasMember (gccCollectTransCandidates fullTable scanList)
      (leftTerm, rightTerm) = true
  | [], _, _, _, hMember, _ => Bool.noConfusion hMember
  | leftPair :: rest, leftTerm, middleTerm, rightTerm, hMember, hFull => by
      cases gccPairMemberConsSplit leftPair rest (leftTerm, middleTerm) hMember with
      | inl hBeq =>
          have hEq : (leftTerm, middleTerm) = leftPair :=
            gccPairBeqEq (leftTerm, middleTerm) leftPair hBeq
          have hFst : leftPair.fst = leftTerm := (congrArg Prod.fst hEq).symm
          have hSnd : leftPair.snd = middleTerm := (congrArg Prod.snd hEq).symm
          refine gccPairAppendMemberLeft (gccJoinThroughLeft leftPair fullTable)
            (gccCollectTransCandidates fullTable rest) (leftTerm, rightTerm) ?_
          rw [← hFst]
          exact gccJoinThroughLeftContains leftPair fullTable middleTerm rightTerm hFull hSnd
      | inr hInRest =>
          exact gccPairAppendMemberRight (gccJoinThroughLeft leftPair fullTable)
            (gccCollectTransCandidates fullTable rest) (leftTerm, rightTerm)
            (gccCollectTransContains fullTable rest leftTerm middleTerm rightTerm
              hInRest hFull)

/-- Transitivity-candidate membership inverts to a scanned pair plus a table pair. -/
theorem gccCollectTransInversion (fullTable : List (GccTerm × GccTerm)) :
    (scanList : List (GccTerm × GccTerm)) → (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccCollectTransCandidates fullTable scanList)
      (leftTerm, rightTerm) = true →
    ∃ middleTerm, gccPairListHasMember scanList (leftTerm, middleTerm) = true ∧
      gccPairListHasMember fullTable (middleTerm, rightTerm) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | leftPair :: rest, leftTerm, rightTerm, hMember => by
      cases gccPairAppendInversion (gccJoinThroughLeft leftPair fullTable)
          (gccCollectTransCandidates fullTable rest) (leftTerm, rightTerm) hMember with
      | inl hInJoin =>
          obtain ⟨hLeftEq, hScan⟩ :=
            gccJoinThroughLeftInversion leftPair fullTable leftTerm rightTerm hInJoin
          refine ⟨leftPair.snd, ?_, hScan⟩
          refine gccPairMemberHeadOfBeq leftPair rest (leftTerm, leftPair.snd) ?_
          rw [hLeftEq]
          exact gccPairBeqRefl (leftPair.fst, leftPair.snd)
      | inr hInRest =>
          obtain ⟨middleTerm, hScan, hFull⟩ :=
            gccCollectTransInversion fullTable rest leftTerm rightTerm hInRest
          exact ⟨middleTerm, gccPairMemberTail leftPair rest (leftTerm, middleTerm) hScan,
            hFull⟩

/-- The inner congruence scan contains every related right apply node. -/
theorem gccCongRightScanContains (table : List (GccTerm × GccTerm))
    (leftFunction leftArgument : GccTerm) : (innerScan : List GccTerm) →
    (rightFunction rightArgument : GccTerm) →
    gccTermListHasMember innerScan (GccTerm.apply rightFunction rightArgument) = true →
    gccPairListHasMember table (leftFunction, rightFunction) = true →
    gccPairListHasMember table (leftArgument, rightArgument) = true →
    gccPairListHasMember (gccCongRightScan table leftFunction leftArgument innerScan)
      (GccTerm.apply leftFunction leftArgument,
        GccTerm.apply rightFunction rightArgument) = true
  | [], _, _, hMember, _, _ => Bool.noConfusion hMember
  | headTerm :: rest, rightFunction, rightArgument, hMember, hFunctionPair, hArgumentPair => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq (GccTerm.apply rightFunction rightArgument) headTerm with
      | true =>
          have hEq : GccTerm.apply rightFunction rightArgument = headTerm :=
            gccTermBeqEq (GccTerm.apply rightFunction rightArgument) headTerm hBeq
          cases hEq
          have hUnfold : gccCongRightScan table leftFunction leftArgument
              (GccTerm.apply rightFunction rightArgument :: rest) =
              (GccTerm.apply leftFunction leftArgument,
                GccTerm.apply rightFunction rightArgument) ::
                gccCongRightScan table leftFunction leftArgument rest := by
            simp only [gccCongRightScan]
            rw [hFunctionPair, hArgumentPair]; rfl
          rw [hUnfold]
          exact gccPairMemberHeadOfBeq _ _ _
            (gccPairBeqRefl (GccTerm.apply leftFunction leftArgument,
              GccTerm.apply rightFunction rightArgument))
      | false =>
          rw [hBeq] at hMember
          have hDeeper := gccCongRightScanContains table leftFunction leftArgument rest
            rightFunction rightArgument hMember hFunctionPair hArgumentPair
          cases headTerm with
          | symbol name => exact hDeeper
          | apply headFunction headArgument =>
              cases hCondFunction : gccPairListHasMember table (leftFunction, headFunction) with
              | false =>
                  have hUnfold : gccCongRightScan table leftFunction leftArgument
                      (GccTerm.apply headFunction headArgument :: rest) =
                      gccCongRightScan table leftFunction leftArgument rest := by
                    simp only [gccCongRightScan]; rw [hCondFunction]; rfl
                  rw [hUnfold]
                  exact hDeeper
              | true =>
                  cases hCondArgument :
                      gccPairListHasMember table (leftArgument, headArgument) with
                  | false =>
                      have hUnfold : gccCongRightScan table leftFunction leftArgument
                          (GccTerm.apply headFunction headArgument :: rest) =
                          gccCongRightScan table leftFunction leftArgument rest := by
                        simp only [gccCongRightScan]; rw [hCondFunction, hCondArgument]; rfl
                      rw [hUnfold]
                      exact hDeeper
                  | true =>
                      have hUnfold : gccCongRightScan table leftFunction leftArgument
                          (GccTerm.apply headFunction headArgument :: rest) =
                          (GccTerm.apply leftFunction leftArgument,
                            GccTerm.apply headFunction headArgument) ::
                            gccCongRightScan table leftFunction leftArgument rest := by
                        simp only [gccCongRightScan]; rw [hCondFunction, hCondArgument]; rfl
                      rw [hUnfold]
                      exact gccPairMemberTail _ _ _ hDeeper

/-- Inner-congruence-scan membership inverts to a scanned apply node with related children. -/
theorem gccCongRightScanInversion (table : List (GccTerm × GccTerm))
    (leftFunction leftArgument : GccTerm) : (innerScan : List GccTerm) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccCongRightScan table leftFunction leftArgument innerScan)
      (leftTerm, rightTerm) = true →
    ∃ rightFunction rightArgument,
      leftTerm = GccTerm.apply leftFunction leftArgument ∧
      rightTerm = GccTerm.apply rightFunction rightArgument ∧
      gccTermListHasMember innerScan (GccTerm.apply rightFunction rightArgument) = true ∧
      gccPairListHasMember table (leftFunction, rightFunction) = true ∧
      gccPairListHasMember table (leftArgument, rightArgument) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, leftTerm, rightTerm, hMember => by
      cases headTerm with
      | symbol name =>
          obtain ⟨rightFunction, rightArgument, hLeftEq, hRightEq, hIn, hFunctionPair,
            hArgumentPair⟩ := gccCongRightScanInversion table leftFunction leftArgument rest
              leftTerm rightTerm hMember
          exact ⟨rightFunction, rightArgument, hLeftEq, hRightEq,
            gccTermMemberTail (GccTerm.symbol name) rest _ hIn, hFunctionPair, hArgumentPair⟩
      | apply headFunction headArgument =>
          cases hCondFunction : gccPairListHasMember table (leftFunction, headFunction) with
          | false =>
              have hUnfold : gccCongRightScan table leftFunction leftArgument
                  (GccTerm.apply headFunction headArgument :: rest) =
                  gccCongRightScan table leftFunction leftArgument rest := by
                simp only [gccCongRightScan]; rw [hCondFunction]; rfl
              rw [hUnfold] at hMember
              obtain ⟨rightFunction, rightArgument, hLeftEq, hRightEq, hIn, hFunctionPair,
                hArgumentPair⟩ := gccCongRightScanInversion table leftFunction leftArgument
                  rest leftTerm rightTerm hMember
              exact ⟨rightFunction, rightArgument, hLeftEq, hRightEq,
                gccTermMemberTail (GccTerm.apply headFunction headArgument) rest _ hIn,
                hFunctionPair, hArgumentPair⟩
          | true =>
              cases hCondArgument :
                  gccPairListHasMember table (leftArgument, headArgument) with
              | false =>
                  have hUnfold : gccCongRightScan table leftFunction leftArgument
                      (GccTerm.apply headFunction headArgument :: rest) =
                      gccCongRightScan table leftFunction leftArgument rest := by
                    simp only [gccCongRightScan]; rw [hCondFunction, hCondArgument]; rfl
                  rw [hUnfold] at hMember
                  obtain ⟨rightFunction, rightArgument, hLeftEq, hRightEq, hIn, hFunctionPair,
                    hArgumentPair⟩ := gccCongRightScanInversion table leftFunction
                      leftArgument rest leftTerm rightTerm hMember
                  exact ⟨rightFunction, rightArgument, hLeftEq, hRightEq,
                    gccTermMemberTail (GccTerm.apply headFunction headArgument) rest _ hIn,
                    hFunctionPair, hArgumentPair⟩
              | true =>
                  have hUnfold : gccCongRightScan table leftFunction leftArgument
                      (GccTerm.apply headFunction headArgument :: rest) =
                      (GccTerm.apply leftFunction leftArgument,
                        GccTerm.apply headFunction headArgument) ::
                        gccCongRightScan table leftFunction leftArgument rest := by
                    simp only [gccCongRightScan]; rw [hCondFunction, hCondArgument]; rfl
                  rw [hUnfold] at hMember
                  cases gccPairMemberConsSplit
                      (GccTerm.apply leftFunction leftArgument,
                        GccTerm.apply headFunction headArgument)
                      (gccCongRightScan table leftFunction leftArgument rest)
                      (leftTerm, rightTerm) hMember with
                  | inl hBeq =>
                      have hEq : (leftTerm, rightTerm) =
                          (GccTerm.apply leftFunction leftArgument,
                            GccTerm.apply headFunction headArgument) :=
                        gccPairBeqEq _ _ hBeq
                      refine ⟨headFunction, headArgument, congrArg Prod.fst hEq,
                        congrArg Prod.snd hEq, ?_, hCondFunction, hCondArgument⟩
                      exact gccTermMemberHeadOfBeq _ _ _
                        (gccTermBeqRefl (GccTerm.apply headFunction headArgument))
                  | inr hInRest =>
                      obtain ⟨rightFunction, rightArgument, hLeftEq, hRightEq, hIn,
                        hFunctionPair, hArgumentPair⟩ := gccCongRightScanInversion table
                          leftFunction leftArgument rest leftTerm rightTerm hInRest
                      exact ⟨rightFunction, rightArgument, hLeftEq, hRightEq,
                        gccTermMemberTail (GccTerm.apply headFunction headArgument) rest _
                          hIn, hFunctionPair, hArgumentPair⟩

/-- Congruence candidates contain every pair of universe apply nodes with related children. -/
theorem gccCollectCongContains (table : List (GccTerm × GccTerm))
    (innerUniverse : List GccTerm) : (outerScan : List GccTerm) →
    (leftFunction leftArgument rightFunction rightArgument : GccTerm) →
    gccTermListHasMember outerScan (GccTerm.apply leftFunction leftArgument) = true →
    gccTermListHasMember innerUniverse (GccTerm.apply rightFunction rightArgument) = true →
    gccPairListHasMember table (leftFunction, rightFunction) = true →
    gccPairListHasMember table (leftArgument, rightArgument) = true →
    gccPairListHasMember (gccCollectCongCandidates table innerUniverse outerScan)
      (GccTerm.apply leftFunction leftArgument,
        GccTerm.apply rightFunction rightArgument) = true
  | [], _, _, _, _, hMember, _, _, _ => Bool.noConfusion hMember
  | headTerm :: rest, leftFunction, leftArgument, rightFunction, rightArgument, hMember,
      hInner, hFunctionPair, hArgumentPair => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq (GccTerm.apply leftFunction leftArgument) headTerm with
      | true =>
          have hEq : GccTerm.apply leftFunction leftArgument = headTerm :=
            gccTermBeqEq (GccTerm.apply leftFunction leftArgument) headTerm hBeq
          cases hEq
          exact gccPairAppendMemberLeft
            (gccCongRightScan table leftFunction leftArgument innerUniverse)
            (gccCollectCongCandidates table innerUniverse rest) _
            (gccCongRightScanContains table leftFunction leftArgument innerUniverse
              rightFunction rightArgument hInner hFunctionPair hArgumentPair)
      | false =>
          rw [hBeq] at hMember
          have hDeeper := gccCollectCongContains table innerUniverse rest leftFunction
            leftArgument rightFunction rightArgument hMember hInner hFunctionPair
            hArgumentPair
          cases headTerm with
          | symbol name => exact hDeeper
          | apply headFunction headArgument =>
              exact gccPairAppendMemberRight
                (gccCongRightScan table headFunction headArgument innerUniverse)
                (gccCollectCongCandidates table innerUniverse rest) _ hDeeper

/-- Congruence-candidate membership inverts to universe apply nodes with related children. -/
theorem gccCollectCongInversion (table : List (GccTerm × GccTerm))
    (innerUniverse : List GccTerm) : (outerScan : List GccTerm) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccCollectCongCandidates table innerUniverse outerScan)
      (leftTerm, rightTerm) = true →
    ∃ leftFunction leftArgument rightFunction rightArgument,
      leftTerm = GccTerm.apply leftFunction leftArgument ∧
      rightTerm = GccTerm.apply rightFunction rightArgument ∧
      gccTermListHasMember outerScan (GccTerm.apply leftFunction leftArgument) = true ∧
      gccTermListHasMember innerUniverse (GccTerm.apply rightFunction rightArgument) = true ∧
      gccPairListHasMember table (leftFunction, rightFunction) = true ∧
      gccPairListHasMember table (leftArgument, rightArgument) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, leftTerm, rightTerm, hMember => by
      cases headTerm with
      | symbol name =>
          obtain ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq, hRightEq,
            hOuter, hInner, hFunctionPair, hArgumentPair⟩ :=
            gccCollectCongInversion table innerUniverse rest leftTerm rightTerm hMember
          exact ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq, hRightEq,
            gccTermMemberTail (GccTerm.symbol name) rest _ hOuter, hInner, hFunctionPair,
            hArgumentPair⟩
      | apply headFunction headArgument =>
          cases gccPairAppendInversion
              (gccCongRightScan table headFunction headArgument innerUniverse)
              (gccCollectCongCandidates table innerUniverse rest)
              (leftTerm, rightTerm) hMember with
          | inl hInScan =>
              obtain ⟨rightFunction, rightArgument, hLeftEq, hRightEq, hInner, hFunctionPair,
                hArgumentPair⟩ := gccCongRightScanInversion table headFunction headArgument
                  innerUniverse leftTerm rightTerm hInScan
              refine ⟨headFunction, headArgument, rightFunction, rightArgument, hLeftEq,
                hRightEq, ?_, hInner, hFunctionPair, hArgumentPair⟩
              exact gccTermMemberHeadOfBeq _ _ _
                (gccTermBeqRefl (GccTerm.apply headFunction headArgument))
          | inr hInRest =>
              obtain ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq,
                hRightEq, hOuter, hInner, hFunctionPair, hArgumentPair⟩ :=
                gccCollectCongInversion table innerUniverse rest leftTerm rightTerm hInRest
              exact ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq,
                hRightEq,
                gccTermMemberTail (GccTerm.apply headFunction headArgument) rest _ hOuter,
                hInner, hFunctionPair, hArgumentPair⟩

/-! ## The full pair square (for the pigeonhole bound) -/

/-- All pairs with one fixed left term. -/
def gccPairsWithLeft (leftTerm : GccTerm) : List GccTerm → List (GccTerm × GccTerm)
  | [] => []
  | rightTerm :: rest => (leftTerm, rightTerm) :: gccPairsWithLeft leftTerm rest

/-- The full pair square of a scan list against a fixed full list. -/
def gccAllPairsScan (fullList : List GccTerm) : List GccTerm → List (GccTerm × GccTerm)
  | [] => []
  | leftTerm :: rest =>
      gccPairListAppend (gccPairsWithLeft leftTerm fullList) (gccAllPairsScan fullList rest)

/-- The full pair square of a universe. -/
def gccAllUniversePairs (universeList : List GccTerm) : List (GccTerm × GccTerm) :=
  gccAllPairsScan universeList universeList

/-- Fixed-left pairs contain every right member. -/
theorem gccPairsWithLeftContains (leftTerm : GccTerm) : (fullList : List GccTerm) →
    (rightTerm : GccTerm) → gccTermListHasMember fullList rightTerm = true →
    gccPairListHasMember (gccPairsWithLeft leftTerm fullList) (leftTerm, rightTerm) = true
  | [], _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, rightTerm, hMember => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq rightTerm headTerm with
      | true =>
          have hEq : rightTerm = headTerm := gccTermBeqEq rightTerm headTerm hBeq
          refine gccPairMemberHeadOfBeq (leftTerm, headTerm) (gccPairsWithLeft leftTerm rest)
            (leftTerm, rightTerm) ?_
          rw [hEq]
          exact gccPairBeqRefl (leftTerm, headTerm)
      | false =>
          rw [hBeq] at hMember
          exact gccPairMemberTail (leftTerm, headTerm) (gccPairsWithLeft leftTerm rest)
            (leftTerm, rightTerm) (gccPairsWithLeftContains leftTerm rest rightTerm hMember)

/-- Fixed-left-pair membership inverts to the left term plus a right member. -/
theorem gccPairsWithLeftInversion (leftTerm : GccTerm) : (fullList : List GccTerm) →
    (candidateLeft candidateRight : GccTerm) →
    gccPairListHasMember (gccPairsWithLeft leftTerm fullList)
      (candidateLeft, candidateRight) = true →
    candidateLeft = leftTerm ∧ gccTermListHasMember fullList candidateRight = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, candidateLeft, candidateRight, hMember => by
      cases gccPairMemberConsSplit (leftTerm, headTerm) (gccPairsWithLeft leftTerm rest)
          (candidateLeft, candidateRight) hMember with
      | inl hBeq =>
          have hEq : (candidateLeft, candidateRight) = (leftTerm, headTerm) :=
            gccPairBeqEq (candidateLeft, candidateRight) (leftTerm, headTerm) hBeq
          refine ⟨congrArg Prod.fst hEq, ?_⟩
          have hRightEq : candidateRight = headTerm := congrArg Prod.snd hEq
          rw [hRightEq]
          exact gccTermMemberHeadOfBeq headTerm rest headTerm (gccTermBeqRefl headTerm)
      | inr hInRest =>
          obtain ⟨hLeftEq, hRightIn⟩ :=
            gccPairsWithLeftInversion leftTerm rest candidateLeft candidateRight hInRest
          exact ⟨hLeftEq, gccTermMemberTail headTerm rest candidateRight hRightIn⟩

/-- The pair square contains every pair of members. -/
theorem gccAllPairsScanContains (fullList : List GccTerm) : (scanList : List GccTerm) →
    (leftTerm rightTerm : GccTerm) → gccTermListHasMember scanList leftTerm = true →
    gccTermListHasMember fullList rightTerm = true →
    gccPairListHasMember (gccAllPairsScan fullList scanList) (leftTerm, rightTerm) = true
  | [], _, _, hMember, _ => Bool.noConfusion hMember
  | headTerm :: rest, leftTerm, rightTerm, hMember, hRight => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq leftTerm headTerm with
      | true =>
          have hEq : leftTerm = headTerm := gccTermBeqEq leftTerm headTerm hBeq
          refine gccPairAppendMemberLeft (gccPairsWithLeft headTerm fullList)
            (gccAllPairsScan fullList rest) (leftTerm, rightTerm) ?_
          rw [hEq]
          exact gccPairsWithLeftContains headTerm fullList rightTerm hRight
      | false =>
          rw [hBeq] at hMember
          exact gccPairAppendMemberRight (gccPairsWithLeft headTerm fullList)
            (gccAllPairsScan fullList rest) (leftTerm, rightTerm)
            (gccAllPairsScanContains fullList rest leftTerm rightTerm hMember hRight)

/-- Pair-square membership inverts to memberships of the components. -/
theorem gccAllPairsScanInversion (fullList : List GccTerm) : (scanList : List GccTerm) →
    (leftTerm rightTerm : GccTerm) →
    gccPairListHasMember (gccAllPairsScan fullList scanList) (leftTerm, rightTerm) = true →
    gccTermListHasMember scanList leftTerm = true ∧
      gccTermListHasMember fullList rightTerm = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, leftTerm, rightTerm, hMember => by
      cases gccPairAppendInversion (gccPairsWithLeft headTerm fullList)
          (gccAllPairsScan fullList rest) (leftTerm, rightTerm) hMember with
      | inl hInLeft =>
          obtain ⟨hLeftEq, hRightIn⟩ :=
            gccPairsWithLeftInversion headTerm fullList leftTerm rightTerm hInLeft
          refine ⟨?_, hRightIn⟩
          refine gccTermMemberHeadOfBeq headTerm rest leftTerm ?_
          rw [hLeftEq]
          exact gccTermBeqRefl headTerm
      | inr hInRest =>
          obtain ⟨hLeftIn, hRightIn⟩ :=
            gccAllPairsScanInversion fullList rest leftTerm rightTerm hInRest
          exact ⟨gccTermMemberTail headTerm rest leftTerm hLeftIn, hRightIn⟩

/-! ## The saturation step and the fueled loop -/

/-- One saturation pass: insert all symmetry, transitivity, and congruence candidates. -/
def gccSaturateStep (universeList : List GccTerm) (table : List (GccTerm × GccTerm)) :
    List (GccTerm × GccTerm) :=
  gccPairListInsertAll
    (gccPairListInsertAll
      (gccPairListInsertAll table (gccSwapPairs table))
      (gccCollectTransCandidates table table))
    (gccCollectCongCandidates table universeList universeList)

/-- The seed table: the equations themselves plus reflexive pairs on the universe. -/
def gccSeedTable (equations : List (GccTerm × GccTerm)) (universeList : List GccTerm) :
    List (GccTerm × GccTerm) :=
  gccPairListInsertAll (gccPairListInsertAll [] equations) (gccMakeReflPairs universeList)

/-- Fueled saturation: iterate the pass until a length fixpoint or fuel exhaustion. -/
def gccSaturate (universeList : List GccTerm) : Nat → List (GccTerm × GccTerm) →
    List (GccTerm × GccTerm)
  | 0, table => table
  | Nat.succ remainingFuel, table =>
      cond (Nat.beq (gccSaturateStep universeList table).length table.length)
        table
        (gccSaturate universeList remainingFuel (gccSaturateStep universeList table))

/-- Fuel that provably reaches the fixpoint: the pair square plus one. -/
def gccSaturationBound (universeList : List GccTerm) : Nat :=
  (gccAllUniversePairs universeList).length + 1

/-- The saturated table of an equation list over a universe. -/
def gccSaturatedTable (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) : List (GccTerm × GccTerm) :=
  gccSaturate universeList (gccSaturationBound universeList)
    (gccSeedTable equations universeList)

/-! ### Step preservation lemmas -/

/-- The pass keeps every table member. -/
theorem gccStepKeepsMember (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (candidatePair : GccTerm × GccTerm)
    (hMember : gccPairListHasMember table candidatePair = true) :
    gccPairListHasMember (gccSaturateStep universeList table) candidatePair = true :=
  gccPairInsertAllKeepsMember (gccCollectCongCandidates table universeList universeList) _
    candidatePair
    (gccPairInsertAllKeepsMember (gccCollectTransCandidates table table) _ candidatePair
      (gccPairInsertAllKeepsMember (gccSwapPairs table) table candidatePair hMember))

/-- The pass preserves derivability of every entry. -/
theorem gccStepKeepsSound (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hSound : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm) :
    ∀ leftTerm rightTerm,
      gccPairListHasMember (gccSaturateStep universeList table) (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm := by
  intro leftTerm rightTerm hMember
  cases gccPairInsertAllInversion (gccCollectCongCandidates table universeList universeList)
      _ (leftTerm, rightTerm) hMember with
  | inr hInCong =>
      obtain ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq, hRightEq,
        _hOuter, _hInner, hFunctionPair, hArgumentPair⟩ :=
        gccCollectCongInversion table universeList universeList leftTerm rightTerm hInCong
      rw [hLeftEq, hRightEq]
      exact GccDeriv.byCongruence leftFunction rightFunction leftArgument rightArgument
        (hSound leftFunction rightFunction hFunctionPair)
        (hSound leftArgument rightArgument hArgumentPair)
  | inl hInTrans =>
      cases gccPairInsertAllInversion (gccCollectTransCandidates table table) _
          (leftTerm, rightTerm) hInTrans with
      | inr hInTransCands =>
          obtain ⟨middleTerm, hLeftPair, hRightPair⟩ :=
            gccCollectTransInversion table table leftTerm rightTerm hInTransCands
          exact GccDeriv.byTrans leftTerm middleTerm rightTerm
            (hSound leftTerm middleTerm hLeftPair) (hSound middleTerm rightTerm hRightPair)
      | inl hInSwap =>
          cases gccPairInsertAllInversion (gccSwapPairs table) table (leftTerm, rightTerm)
              hInSwap with
          | inr hInSwapCands =>
              exact GccDeriv.bySymm rightTerm leftTerm
                (hSound rightTerm leftTerm
                  (gccSwapPairsInversion table leftTerm rightTerm hInSwapCands))
          | inl hInTable => exact hSound leftTerm rightTerm hInTable

/-- The pass keeps every entry inside the pair square. -/
theorem gccStepKeepsInside (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hInside : ∀ candidatePair, gccPairListHasMember table candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true) :
    ∀ candidatePair,
      gccPairListHasMember (gccSaturateStep universeList table) candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true := by
  intro candidatePair hMember
  cases gccPairInsertAllInversion (gccCollectCongCandidates table universeList universeList)
      _ candidatePair hMember with
  | inr hInCong =>
      obtain ⟨leftFunction, leftArgument, rightFunction, rightArgument, hLeftEq, hRightEq,
        hOuter, hInner, _hFunctionPair, _hArgumentPair⟩ :=
        gccCollectCongInversion table universeList universeList candidatePair.fst
          candidatePair.snd hInCong
      have hContains := gccAllPairsScanContains universeList universeList candidatePair.fst
        candidatePair.snd (hLeftEq ▸ hOuter) (hRightEq ▸ hInner)
      exact hContains
  | inl hInTrans =>
      cases gccPairInsertAllInversion (gccCollectTransCandidates table table) _
          candidatePair hInTrans with
      | inr hInTransCands =>
          obtain ⟨middleTerm, hLeftPair, hRightPair⟩ :=
            gccCollectTransInversion table table candidatePair.fst candidatePair.snd
              hInTransCands
          have hLeftIn := (gccAllPairsScanInversion universeList universeList
            candidatePair.fst middleTerm (hInside (candidatePair.fst, middleTerm)
              hLeftPair)).left
          have hRightIn := (gccAllPairsScanInversion universeList universeList middleTerm
            candidatePair.snd (hInside (middleTerm, candidatePair.snd) hRightPair)).right
          exact gccAllPairsScanContains universeList universeList candidatePair.fst
            candidatePair.snd hLeftIn hRightIn
      | inl hInSwap =>
          cases gccPairInsertAllInversion (gccSwapPairs table) table candidatePair
              hInSwap with
          | inr hInSwapCands =>
              have hSwapped := gccSwapPairsInversion table candidatePair.fst
                candidatePair.snd hInSwapCands
              obtain ⟨hSndIn, hFstIn⟩ := gccAllPairsScanInversion universeList universeList
                candidatePair.snd candidatePair.fst
                (hInside (candidatePair.snd, candidatePair.fst) hSwapped)
              exact gccAllPairsScanContains universeList universeList candidatePair.fst
                candidatePair.snd hFstIn hSndIn
          | inl hInTable => exact hInside candidatePair hInTable

/-- The pass preserves duplicate-freedom. -/
theorem gccStepKeepsNoDup (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hNoDup : gccPairListHasNoDup table = true) :
    gccPairListHasNoDup (gccSaturateStep universeList table) = true :=
  gccPairInsertAllKeepsNoDup (gccCollectCongCandidates table universeList universeList) _
    (gccPairInsertAllKeepsNoDup (gccCollectTransCandidates table table) _
      (gccPairInsertAllKeepsNoDup (gccSwapPairs table) table hNoDup))

/-- The pass only grows the table. -/
theorem gccStepLengthGrows (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm)) :
    ∃ growth, (gccSaturateStep universeList table).length = table.length + growth := by
  obtain ⟨swapGrowth, hSwapLen⟩ := gccPairInsertAllGrows (gccSwapPairs table) table
  obtain ⟨transGrowth, hTransLen⟩ := gccPairInsertAllGrows
    (gccCollectTransCandidates table table) (gccPairListInsertAll table (gccSwapPairs table))
  obtain ⟨congGrowth, hCongLen⟩ := gccPairInsertAllGrows
    (gccCollectCongCandidates table universeList universeList)
    (gccPairListInsertAll (gccPairListInsertAll table (gccSwapPairs table))
      (gccCollectTransCandidates table table))
  refine ⟨(swapGrowth + transGrowth) + congGrowth, ?_⟩
  show (gccPairListInsertAll
    (gccPairListInsertAll (gccPairListInsertAll table (gccSwapPairs table))
      (gccCollectTransCandidates table table))
    (gccCollectCongCandidates table universeList universeList)).length =
    table.length + ((swapGrowth + transGrowth) + congGrowth)
  rw [hCongLen, hTransLen, hSwapLen, Nat.add_assoc table.length swapGrowth transGrowth,
    Nat.add_assoc table.length (swapGrowth + transGrowth) congGrowth]

/-- A length-stable pass had every candidate family already present. -/
theorem gccStepStableAllPresent (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm))
    (hStable : (gccSaturateStep universeList table).length = table.length) :
    (∀ candidatePair, gccPairListHasMember (gccSwapPairs table) candidatePair = true →
      gccPairListHasMember table candidatePair = true) ∧
    (∀ candidatePair,
      gccPairListHasMember (gccCollectTransCandidates table table) candidatePair = true →
      gccPairListHasMember table candidatePair = true) ∧
    (∀ candidatePair,
      gccPairListHasMember (gccCollectCongCandidates table universeList universeList)
        candidatePair = true →
      gccPairListHasMember table candidatePair = true) := by
  obtain ⟨swapGrowth, hSwapLen⟩ := gccPairInsertAllGrows (gccSwapPairs table) table
  obtain ⟨transGrowth, hTransLen⟩ := gccPairInsertAllGrows
    (gccCollectTransCandidates table table) (gccPairListInsertAll table (gccSwapPairs table))
  obtain ⟨congGrowth, hCongLen⟩ := gccPairInsertAllGrows
    (gccCollectCongCandidates table universeList universeList)
    (gccPairListInsertAll (gccPairListInsertAll table (gccSwapPairs table))
      (gccCollectTransCandidates table table))
  have hChain : table.length + (swapGrowth + (transGrowth + congGrowth)) = table.length := by
    have hExpand : (gccSaturateStep universeList table).length =
        ((table.length + swapGrowth) + transGrowth) + congGrowth := by
      show (gccPairListInsertAll
        (gccPairListInsertAll (gccPairListInsertAll table (gccSwapPairs table))
          (gccCollectTransCandidates table table))
        (gccCollectCongCandidates table universeList universeList)).length =
        ((table.length + swapGrowth) + transGrowth) + congGrowth
      rw [hCongLen, hTransLen, hSwapLen]
    have hFlat := hExpand.symm.trans hStable
    rw [Nat.add_assoc table.length swapGrowth transGrowth,
      Nat.add_assoc table.length (swapGrowth + transGrowth) congGrowth,
      Nat.add_assoc swapGrowth transGrowth congGrowth] at hFlat
    exact hFlat
  have hAllZero := gccNatAddSelfImpliesZero table.length
    (swapGrowth + (transGrowth + congGrowth)) hChain
  obtain ⟨hSwapZero, hRestZero⟩ :=
    gccNatAddSplitZero swapGrowth (transGrowth + congGrowth) hAllZero
  obtain ⟨hTransZero, hCongZero⟩ := gccNatAddSplitZero transGrowth congGrowth hRestZero
  rw [hSwapZero, Nat.add_zero] at hSwapLen
  obtain ⟨hSwapStable, hSwapPresent⟩ :=
    gccPairInsertAllStable (gccSwapPairs table) table hSwapLen
  rw [hTransZero, Nat.add_zero, hSwapStable] at hTransLen
  obtain ⟨hTransStable, hTransPresent⟩ :=
    gccPairInsertAllStable (gccCollectTransCandidates table table) table hTransLen
  rw [hCongZero, Nat.add_zero, hSwapStable, hTransStable] at hCongLen
  obtain ⟨_hCongStable, hCongPresent⟩ := gccPairInsertAllStable
    (gccCollectCongCandidates table universeList universeList) table hCongLen
  exact ⟨hSwapPresent, hTransPresent, hCongPresent⟩

/-! ### Saturation preservation and adequacy -/

/-- Saturation keeps every table member. -/
theorem gccSaturateKeepsMember (universeList : List GccTerm) : (fuel : Nat) →
    (table : List (GccTerm × GccTerm)) → (candidatePair : GccTerm × GccTerm) →
    gccPairListHasMember table candidatePair = true →
    gccPairListHasMember (gccSaturate universeList fuel table) candidatePair = true
  | 0, _, _, hMember => hMember
  | Nat.succ remainingFuel, table, candidatePair, hMember => by
      simp only [gccSaturate]
      cases hTest : Nat.beq (gccSaturateStep universeList table).length table.length with
      | true => exact hMember
      | false =>
          exact gccSaturateKeepsMember universeList remainingFuel
            (gccSaturateStep universeList table) candidatePair
            (gccStepKeepsMember universeList table candidatePair hMember)

/-- Saturation preserves derivability of every entry. -/
theorem gccSaturateKeepsSound (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) : (fuel : Nat) → (table : List (GccTerm × GccTerm)) →
    (∀ leftTerm rightTerm, gccPairListHasMember table (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm) →
    ∀ leftTerm rightTerm,
      gccPairListHasMember (gccSaturate universeList fuel table) (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm
  | 0, _, hSound, leftTerm, rightTerm, hMember => hSound leftTerm rightTerm hMember
  | Nat.succ remainingFuel, table, hSound, leftTerm, rightTerm, hMember => by
      simp only [gccSaturate] at hMember
      cases hTest : Nat.beq (gccSaturateStep universeList table).length table.length with
      | true =>
          rw [hTest] at hMember
          exact hSound leftTerm rightTerm hMember
      | false =>
          rw [hTest] at hMember
          exact gccSaturateKeepsSound equations universeList remainingFuel
            (gccSaturateStep universeList table)
            (gccStepKeepsSound equations universeList table hSound) leftTerm rightTerm hMember

/-- Saturation keeps every entry inside the pair square. -/
theorem gccSaturateKeepsInside (universeList : List GccTerm) : (fuel : Nat) →
    (table : List (GccTerm × GccTerm)) →
    (∀ candidatePair, gccPairListHasMember table candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true) →
    ∀ candidatePair,
      gccPairListHasMember (gccSaturate universeList fuel table) candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true
  | 0, _, hInside, candidatePair, hMember => hInside candidatePair hMember
  | Nat.succ remainingFuel, table, hInside, candidatePair, hMember => by
      simp only [gccSaturate] at hMember
      cases hTest : Nat.beq (gccSaturateStep universeList table).length table.length with
      | true =>
          rw [hTest] at hMember
          exact hInside candidatePair hMember
      | false =>
          rw [hTest] at hMember
          exact gccSaturateKeepsInside universeList remainingFuel
            (gccSaturateStep universeList table)
            (gccStepKeepsInside universeList table hInside) candidatePair hMember

/-- **Adequacy**: with enough fuel budget, saturation lands on a genuine length fixpoint. -/
theorem gccSaturateReachesFixpoint (universeList : List GccTerm) : (fuel : Nat) →
    (table : List (GccTerm × GccTerm)) → gccPairListHasNoDup table = true →
    (∀ candidatePair, gccPairListHasMember table candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true) →
    (∃ slack, table.length + fuel =
      (gccAllUniversePairs universeList).length + 1 + slack) →
    (gccSaturateStep universeList (gccSaturate universeList fuel table)).length =
      (gccSaturate universeList fuel table).length
  | 0, table, hNoDup, hInside, ⟨slack, hBudget⟩ => by
      obtain ⟨slackBound, hPigeon⟩ :=
        gccNoDupBoundedByLength table (gccAllUniversePairs universeList) hNoDup hInside
      rw [Nat.add_zero] at hBudget
      rw [hBudget] at hPigeon
      rw [Nat.add_assoc ((gccAllUniversePairs universeList).length + 1) slack slackBound,
        Nat.add_assoc (gccAllUniversePairs universeList).length 1 (slack + slackBound)]
        at hPigeon
      have hZero := gccNatAddSelfImpliesZero (gccAllUniversePairs universeList).length
        (1 + (slack + slackBound)) hPigeon
      rw [Nat.add_comm] at hZero
      exact Nat.noConfusion hZero
  | Nat.succ remainingFuel, table, hNoDup, hInside, ⟨slack, hBudget⟩ => by
      simp only [gccSaturate]
      cases hTest : Nat.beq (gccSaturateStep universeList table).length table.length with
      | true => exact gccNatBeqEq _ _ hTest
      | false =>
          refine gccSaturateReachesFixpoint universeList remainingFuel
            (gccSaturateStep universeList table)
            (gccStepKeepsNoDup universeList table hNoDup)
            (gccStepKeepsInside universeList table hInside) ?_
          obtain ⟨growth, hGrowth⟩ := gccStepLengthGrows universeList table
          cases growth with
          | zero =>
              rw [Nat.add_zero] at hGrowth
              rw [hGrowth, gccNatBeqRefl table.length] at hTest
              exact Bool.noConfusion hTest
          | succ growthPredecessor =>
              refine ⟨slack + growthPredecessor, ?_⟩
              rw [hGrowth, Nat.add_assoc table.length (Nat.succ growthPredecessor)
                  remainingFuel,
                Nat.succ_add growthPredecessor remainingFuel,
                Nat.add_comm growthPredecessor remainingFuel,
                ← Nat.succ_add remainingFuel growthPredecessor,
                ← Nat.add_assoc table.length (Nat.succ remainingFuel) growthPredecessor,
                hBudget,
                Nat.add_assoc ((gccAllUniversePairs universeList).length + 1) slack
                  growthPredecessor]

/-! ### Seed table facts -/

/-- The seed table is duplicate-free. -/
theorem gccSeedTableHasNoDup (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) :
    gccPairListHasNoDup (gccSeedTable equations universeList) = true :=
  gccPairInsertAllKeepsNoDup (gccMakeReflPairs universeList) _
    (gccPairInsertAllKeepsNoDup equations [] rfl)

/-- The seed table carries every indexed equation. -/
theorem gccSeedTableHasEquations (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (index : Nat) (leftTerm rightTerm : GccTerm)
    (hGet : gccListGetPair equations index = some (leftTerm, rightTerm)) :
    gccPairListHasMember (gccSeedTable equations universeList) (leftTerm, rightTerm) = true :=
  gccPairInsertAllKeepsMember (gccMakeReflPairs universeList) _ (leftTerm, rightTerm)
    (gccPairInsertAllAddsAll equations [] (leftTerm, rightTerm)
      (gccListGetImpliesMember equations index (leftTerm, rightTerm) hGet))

/-- The seed table carries the diagonal of every universe member. -/
theorem gccSeedTableHasRefl (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (memberTerm : GccTerm)
    (hIn : gccTermListHasMember universeList memberTerm = true) :
    gccPairListHasMember (gccSeedTable equations universeList)
      (memberTerm, memberTerm) = true :=
  gccPairInsertAllAddsAll (gccMakeReflPairs universeList) _ (memberTerm, memberTerm)
    (gccMakeReflPairsContains universeList memberTerm hIn)

/-- Every seed entry is derivable. -/
theorem gccSeedTableIsSound (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) :
    ∀ leftTerm rightTerm,
      gccPairListHasMember (gccSeedTable equations universeList) (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm := by
  intro leftTerm rightTerm hMember
  cases gccPairInsertAllInversion (gccMakeReflPairs universeList)
      (gccPairListInsertAll [] equations) (leftTerm, rightTerm) hMember with
  | inl hInEquationPart =>
      cases gccPairInsertAllInversion equations [] (leftTerm, rightTerm) hInEquationPart with
      | inl hInNil => exact Bool.noConfusion hInNil
      | inr hInEquations =>
          obtain ⟨index, hGet⟩ :=
            gccMemberImpliesGet equations (leftTerm, rightTerm) hInEquations
          exact GccDeriv.byEquation index leftTerm rightTerm hGet
  | inr hInRefl =>
      obtain ⟨baseTerm, hLeftEq, hRightEq, _hIn⟩ :=
        gccMakeReflPairsInversion universeList leftTerm rightTerm hInRefl
      rw [hLeftEq, hRightEq]
      exact GccDeriv.byRefl baseTerm

/-- Every seed entry lies inside the pair square (given equation sides in the universe). -/
theorem gccSeedTableInside (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm)
    (hSides : ∀ index leftTerm rightTerm,
      gccListGetPair equations index = some (leftTerm, rightTerm) →
      gccTermListHasMember universeList leftTerm = true ∧
        gccTermListHasMember universeList rightTerm = true) :
    ∀ candidatePair,
      gccPairListHasMember (gccSeedTable equations universeList) candidatePair = true →
      gccPairListHasMember (gccAllUniversePairs universeList) candidatePair = true := by
  intro candidatePair hMember
  cases gccPairInsertAllInversion (gccMakeReflPairs universeList)
      (gccPairListInsertAll [] equations) candidatePair hMember with
  | inl hInEquationPart =>
      cases gccPairInsertAllInversion equations [] candidatePair hInEquationPart with
      | inl hInNil => exact Bool.noConfusion hInNil
      | inr hInEquations =>
          obtain ⟨index, hGet⟩ := gccMemberImpliesGet equations candidatePair hInEquations
          obtain ⟨hLeftIn, hRightIn⟩ :=
            hSides index candidatePair.fst candidatePair.snd hGet
          exact gccAllPairsScanContains universeList universeList candidatePair.fst
            candidatePair.snd hLeftIn hRightIn
  | inr hInRefl =>
      obtain ⟨baseTerm, hLeftEq, hRightEq, hIn⟩ :=
        gccMakeReflPairsInversion universeList candidatePair.fst candidatePair.snd hInRefl
      have hContains := gccAllPairsScanContains universeList universeList candidatePair.fst
        candidatePair.snd (hLeftEq.symm ▸ hIn) (hRightEq.symm ▸ hIn)
      exact hContains

/-! ## The saturated-table invariant bundle -/

/-- Everything the decision theorems need from a saturated table. -/
structure GccTableInvariants (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm)) : Prop where
  isSymmClosed : ∀ leftTerm rightTerm,
    gccPairListHasMember table (leftTerm, rightTerm) = true →
    gccPairListHasMember table (rightTerm, leftTerm) = true
  isTransClosed : ∀ leftTerm middleTerm rightTerm,
    gccPairListHasMember table (leftTerm, middleTerm) = true →
    gccPairListHasMember table (middleTerm, rightTerm) = true →
    gccPairListHasMember table (leftTerm, rightTerm) = true
  isCongClosed : ∀ leftFunction leftArgument rightFunction rightArgument,
    gccTermListHasMember universeList (GccTerm.apply leftFunction leftArgument) = true →
    gccTermListHasMember universeList (GccTerm.apply rightFunction rightArgument) = true →
    gccPairListHasMember table (leftFunction, rightFunction) = true →
    gccPairListHasMember table (leftArgument, rightArgument) = true →
    gccPairListHasMember table (GccTerm.apply leftFunction leftArgument,
      GccTerm.apply rightFunction rightArgument) = true
  isReflPopulated : ∀ memberTerm,
    gccTermListHasMember universeList memberTerm = true →
    gccPairListHasMember table (memberTerm, memberTerm) = true
  isEquationPopulated : ∀ equationIndex leftTerm rightTerm,
    gccListGetPair equations equationIndex = some (leftTerm, rightTerm) →
    gccPairListHasMember table (leftTerm, rightTerm) = true
  isInsideUniverse : ∀ leftTerm rightTerm,
    gccPairListHasMember table (leftTerm, rightTerm) = true →
    gccTermListHasMember universeList leftTerm = true ∧
      gccTermListHasMember universeList rightTerm = true
  isSoundlyDerivable : ∀ leftTerm rightTerm,
    gccPairListHasMember table (leftTerm, rightTerm) = true →
    GccDeriv equations leftTerm rightTerm

/-- The saturated table satisfies the full invariant bundle. -/
theorem gccSaturatedTableIsInvariant (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm)
    (hSides : ∀ index leftTerm rightTerm,
      gccListGetPair equations index = some (leftTerm, rightTerm) →
      gccTermListHasMember universeList leftTerm = true ∧
        gccTermListHasMember universeList rightTerm = true) :
    GccTableInvariants equations universeList (gccSaturatedTable equations universeList) := by
  have hSeedNoDup := gccSeedTableHasNoDup equations universeList
  have hSeedInside := gccSeedTableInside equations universeList hSides
  have hBudget : (gccSeedTable equations universeList).length +
      gccSaturationBound universeList =
      (gccAllUniversePairs universeList).length + 1 +
        (gccSeedTable equations universeList).length := by
    show (gccSeedTable equations universeList).length +
      ((gccAllUniversePairs universeList).length + 1) =
      (gccAllUniversePairs universeList).length + 1 +
        (gccSeedTable equations universeList).length
    exact Nat.add_comm (gccSeedTable equations universeList).length
      ((gccAllUniversePairs universeList).length + 1)
  have hFixpoint := gccSaturateReachesFixpoint universeList
    (gccSaturationBound universeList) (gccSeedTable equations universeList)
    hSeedNoDup hSeedInside ⟨(gccSeedTable equations universeList).length, hBudget⟩
  obtain ⟨hSwapPresent, hTransPresent, hCongPresent⟩ :=
    gccStepStableAllPresent universeList (gccSaturatedTable equations universeList) hFixpoint
  refine
    { isSymmClosed := ?_
      isTransClosed := ?_
      isCongClosed := ?_
      isReflPopulated := ?_
      isEquationPopulated := ?_
      isInsideUniverse := ?_
      isSoundlyDerivable := ?_ }
  · intro leftTerm rightTerm hMember
    exact hSwapPresent (rightTerm, leftTerm)
      (gccSwapPairsContains (gccSaturatedTable equations universeList) leftTerm rightTerm
        hMember)
  · intro leftTerm middleTerm rightTerm hLeftPair hRightPair
    exact hTransPresent (leftTerm, rightTerm)
      (gccCollectTransContains (gccSaturatedTable equations universeList)
        (gccSaturatedTable equations universeList) leftTerm middleTerm rightTerm
        hLeftPair hRightPair)
  · intro leftFunction leftArgument rightFunction rightArgument hLeftIn hRightIn
      hFunctionPair hArgumentPair
    exact hCongPresent
      (GccTerm.apply leftFunction leftArgument, GccTerm.apply rightFunction rightArgument)
      (gccCollectCongContains (gccSaturatedTable equations universeList) universeList
        universeList leftFunction leftArgument rightFunction rightArgument hLeftIn hRightIn
        hFunctionPair hArgumentPair)
  · intro memberTerm hIn
    exact gccSaturateKeepsMember universeList (gccSaturationBound universeList)
      (gccSeedTable equations universeList) (memberTerm, memberTerm)
      (gccSeedTableHasRefl equations universeList memberTerm hIn)
  · intro equationIndex leftTerm rightTerm hGet
    exact gccSaturateKeepsMember universeList (gccSaturationBound universeList)
      (gccSeedTable equations universeList) (leftTerm, rightTerm)
      (gccSeedTableHasEquations equations universeList equationIndex leftTerm rightTerm hGet)
  · intro leftTerm rightTerm hMember
    exact gccAllPairsScanInversion universeList universeList leftTerm rightTerm
      (gccSaturateKeepsInside universeList (gccSaturationBound universeList)
        (gccSeedTable equations universeList) hSeedInside (leftTerm, rightTerm) hMember)
  · intro leftTerm rightTerm hMember
    exact gccSaturateKeepsSound equations universeList (gccSaturationBound universeList)
      (gccSeedTable equations universeList) (gccSeedTableIsSound equations universeList)
      leftTerm rightTerm hMember

/-! ## Representatives -/

/-- The first universe member related to the query term under the table. -/
def gccFirstRelated (table : List (GccTerm × GccTerm)) : List GccTerm → GccTerm →
    Option GccTerm
  | [], _ => none
  | candidate :: rest, queryTerm =>
      cond (gccPairListHasMember table (queryTerm, candidate)) (some candidate)
        (gccFirstRelated table rest queryTerm)

/-- The representative: first related universe member, else the term itself. -/
def gccRepresentative (table : List (GccTerm × GccTerm)) (universeList : List GccTerm)
    (queryTerm : GccTerm) : GccTerm :=
  match gccFirstRelated table universeList queryTerm with
  | some canonical => canonical
  | none => queryTerm

/-- A found representative is table-related and a scan member. -/
theorem gccFirstRelatedFinds (table : List (GccTerm × GccTerm)) :
    (scanList : List GccTerm) → (queryTerm foundCanonical : GccTerm) →
    gccFirstRelated table scanList queryTerm = some foundCanonical →
    gccPairListHasMember table (queryTerm, foundCanonical) = true ∧
      gccTermListHasMember scanList foundCanonical = true
  | [], _, _, hFound => nomatch hFound
  | candidate :: rest, queryTerm, foundCanonical, hFound => by
      cases hPresent : gccPairListHasMember table (queryTerm, candidate) with
      | true =>
          have hUnfold : gccFirstRelated table (candidate :: rest) queryTerm =
              some candidate := by
            simp only [gccFirstRelated]; rw [hPresent]; rfl
          rw [hUnfold] at hFound
          injection hFound with hCanonicalEq
          constructor
          · rw [← hCanonicalEq]; exact hPresent
          · rw [← hCanonicalEq]
            exact gccTermMemberHeadOfBeq candidate rest candidate (gccTermBeqRefl candidate)
      | false =>
          have hUnfold : gccFirstRelated table (candidate :: rest) queryTerm =
              gccFirstRelated table rest queryTerm := by
            simp only [gccFirstRelated]; rw [hPresent]; rfl
          rw [hUnfold] at hFound
          obtain ⟨hPair, hIn⟩ := gccFirstRelatedFinds table rest queryTerm foundCanonical hFound
          exact ⟨hPair, gccTermMemberTail candidate rest foundCanonical hIn⟩

/-- A missed scan has no related member at all. -/
theorem gccFirstRelatedMisses (table : List (GccTerm × GccTerm)) :
    (scanList : List GccTerm) → (queryTerm : GccTerm) →
    gccFirstRelated table scanList queryTerm = none → (candidate : GccTerm) →
    gccTermListHasMember scanList candidate = true →
    gccPairListHasMember table (queryTerm, candidate) = false
  | [], _, _, _, hIn => Bool.noConfusion hIn
  | headCandidate :: rest, queryTerm, hNone, candidate, hIn => by
      cases hPresent : gccPairListHasMember table (queryTerm, headCandidate) with
      | true =>
          have hUnfold : gccFirstRelated table (headCandidate :: rest) queryTerm =
              some headCandidate := by
            simp only [gccFirstRelated]; rw [hPresent]; rfl
          rw [hUnfold] at hNone
          exact nomatch hNone
      | false =>
          have hUnfold : gccFirstRelated table (headCandidate :: rest) queryTerm =
              gccFirstRelated table rest queryTerm := by
            simp only [gccFirstRelated]; rw [hPresent]; rfl
          rw [hUnfold] at hNone
          simp only [gccTermListHasMember] at hIn
          cases hBeq : gccTermBeq candidate headCandidate with
          | true =>
              have hEq : candidate = headCandidate := gccTermBeqEq candidate headCandidate hBeq
              rw [hEq]
              exact hPresent
          | false =>
              rw [hBeq] at hIn
              exact gccFirstRelatedMisses table rest queryTerm hNone candidate hIn

/-- Every universe member is related to its representative (given reflexive population). -/
theorem gccRepresentativeIsRelated (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm))
    (hRefl : ∀ memberTerm, gccTermListHasMember universeList memberTerm = true →
      gccPairListHasMember table (memberTerm, memberTerm) = true)
    (queryTerm : GccTerm) (hIn : gccTermListHasMember universeList queryTerm = true) :
    gccPairListHasMember table (queryTerm, gccRepresentative table universeList queryTerm) =
      true := by
  cases hFirst : gccFirstRelated table universeList queryTerm with
  | some foundCanonical =>
      have hUnfold : gccRepresentative table universeList queryTerm = foundCanonical := by
        simp only [gccRepresentative]; rw [hFirst]
      rw [hUnfold]
      exact (gccFirstRelatedFinds table universeList queryTerm foundCanonical hFirst).left
  | none =>
      have hMiss := gccFirstRelatedMisses table universeList queryTerm hFirst queryTerm hIn
      rw [hRefl queryTerm hIn] at hMiss
      exact Bool.noConfusion hMiss

/-- The representative of a universe member stays in the universe. -/
theorem gccRepresentativeStaysInUniverse (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm)) (queryTerm : GccTerm)
    (hIn : gccTermListHasMember universeList queryTerm = true) :
    gccTermListHasMember universeList (gccRepresentative table universeList queryTerm) =
      true := by
  cases hFirst : gccFirstRelated table universeList queryTerm with
  | some foundCanonical =>
      have hUnfold : gccRepresentative table universeList queryTerm = foundCanonical := by
        simp only [gccRepresentative]; rw [hFirst]
      rw [hUnfold]
      exact (gccFirstRelatedFinds table universeList queryTerm foundCanonical hFirst).right
  | none =>
      have hUnfold : gccRepresentative table universeList queryTerm = queryTerm := by
        simp only [gccRepresentative]; rw [hFirst]
      rw [hUnfold]
      exact hIn

/-- Pointwise-agreeing queries scan to the same first related member. -/
theorem gccFirstRelatedAgrees (table : List (GccTerm × GccTerm))
    (leftQuery rightQuery : GccTerm)
    (hPointwise : ∀ candidate, gccPairListHasMember table (leftQuery, candidate) =
      gccPairListHasMember table (rightQuery, candidate)) :
    (scanList : List GccTerm) →
    gccFirstRelated table scanList leftQuery = gccFirstRelated table scanList rightQuery
  | [] => rfl
  | candidate :: rest => by
      have hUnfoldLeft : gccFirstRelated table (candidate :: rest) leftQuery =
          cond (gccPairListHasMember table (leftQuery, candidate)) (some candidate)
            (gccFirstRelated table rest leftQuery) := rfl
      have hUnfoldRight : gccFirstRelated table (candidate :: rest) rightQuery =
          cond (gccPairListHasMember table (rightQuery, candidate)) (some candidate)
            (gccFirstRelated table rest rightQuery) := rfl
      rw [hUnfoldLeft, hUnfoldRight, hPointwise candidate]
      cases hPresent : gccPairListHasMember table (rightQuery, candidate) with
      | true => rfl
      | false => exact gccFirstRelatedAgrees table leftQuery rightQuery hPointwise rest

/-- Table-related terms share their representative. -/
theorem gccRepresentativeRespects (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm))
    (hSymm : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      gccPairListHasMember table (rightTerm, leftTerm) = true)
    (hTrans : ∀ leftTerm middleTerm rightTerm,
      gccPairListHasMember table (leftTerm, middleTerm) = true →
      gccPairListHasMember table (middleTerm, rightTerm) = true →
      gccPairListHasMember table (leftTerm, rightTerm) = true)
    (hInside : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      gccTermListHasMember universeList leftTerm = true ∧
        gccTermListHasMember universeList rightTerm = true)
    (leftQuery rightQuery : GccTerm)
    (hPair : gccPairListHasMember table (leftQuery, rightQuery) = true) :
    gccRepresentative table universeList leftQuery =
      gccRepresentative table universeList rightQuery := by
  have hPointwise : ∀ candidate, gccPairListHasMember table (leftQuery, candidate) =
      gccPairListHasMember table (rightQuery, candidate) := by
    intro candidate
    cases hLeft : gccPairListHasMember table (leftQuery, candidate) with
    | true =>
        have hSwapped := hSymm leftQuery rightQuery hPair
        have hRight := hTrans rightQuery leftQuery candidate hSwapped hLeft
        exact hRight.symm
    | false =>
        cases hRight : gccPairListHasMember table (rightQuery, candidate) with
        | false => rfl
        | true =>
            have hDerived := hTrans leftQuery rightQuery candidate hPair hRight
            rw [hDerived] at hLeft
            exact Bool.noConfusion hLeft
  have hAgree := gccFirstRelatedAgrees table leftQuery rightQuery hPointwise universeList
  cases hFirst : gccFirstRelated table universeList leftQuery with
  | some foundCanonical =>
      have hRightFirst : gccFirstRelated table universeList rightQuery =
          some foundCanonical := hAgree.symm.trans hFirst
      have hLeftUnfold : gccRepresentative table universeList leftQuery = foundCanonical := by
        simp only [gccRepresentative]; rw [hFirst]
      have hRightUnfold : gccRepresentative table universeList rightQuery =
          foundCanonical := by
        simp only [gccRepresentative]; rw [hRightFirst]
      exact hLeftUnfold.trans hRightUnfold.symm
  | none =>
      have hRightIn := (hInside leftQuery rightQuery hPair).right
      have hMiss := gccFirstRelatedMisses table universeList leftQuery hFirst rightQuery
        hRightIn
      rw [hPair] at hMiss
      exact Bool.noConfusion hMiss

/-- The representative is idempotent on universe members. -/
theorem gccRepresentativeIdempotent (universeList : List GccTerm)
    (table : List (GccTerm × GccTerm))
    (hSymm : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      gccPairListHasMember table (rightTerm, leftTerm) = true)
    (hTrans : ∀ leftTerm middleTerm rightTerm,
      gccPairListHasMember table (leftTerm, middleTerm) = true →
      gccPairListHasMember table (middleTerm, rightTerm) = true →
      gccPairListHasMember table (leftTerm, rightTerm) = true)
    (hInside : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      gccTermListHasMember universeList leftTerm = true ∧
        gccTermListHasMember universeList rightTerm = true)
    (hRefl : ∀ memberTerm, gccTermListHasMember universeList memberTerm = true →
      gccPairListHasMember table (memberTerm, memberTerm) = true)
    (queryTerm : GccTerm) (hIn : gccTermListHasMember universeList queryTerm = true) :
    gccRepresentative table universeList (gccRepresentative table universeList queryTerm) =
      gccRepresentative table universeList queryTerm :=
  (gccRepresentativeRespects universeList table hSymm hTrans hInside queryTerm
    (gccRepresentative table universeList queryTerm)
    (gccRepresentativeIsRelated universeList table hRefl queryTerm hIn)).symm

/-- Every term is derivably equal to its representative (given a sound table). -/
theorem gccRepresentativeSound (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hSound : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm) (queryTerm : GccTerm) :
    GccDeriv equations queryTerm (gccRepresentative table universeList queryTerm) := by
  cases hFirst : gccFirstRelated table universeList queryTerm with
  | some foundCanonical =>
      have hUnfold : gccRepresentative table universeList queryTerm = foundCanonical := by
        simp only [gccRepresentative]; rw [hFirst]
      rw [hUnfold]
      exact hSound queryTerm foundCanonical
        (gccFirstRelatedFinds table universeList queryTerm foundCanonical hFirst).left
  | none =>
      have hUnfold : gccRepresentative table universeList queryTerm = queryTerm := by
        simp only [gccRepresentative]; rw [hFirst]
      rw [hUnfold]
      exact GccDeriv.byRefl queryTerm

/-! ## The signature table -/

/-- Scan a signature list for the first entry whose key beq-matches. -/
def gccSigLookup : List ((GccTerm × GccTerm) × GccTerm) → (GccTerm × GccTerm) →
    Option GccTerm
  | [], _ => none
  | signatureEntry :: rest, searchKey =>
      cond (gccPairBeq searchKey signatureEntry.fst) (some signatureEntry.snd)
        (gccSigLookup rest searchKey)

/-- Build the signature table: every universe apply node keyed by child representatives. -/
def gccBuildSignature (table : List (GccTerm × GccTerm)) (universeList : List GccTerm) :
    List GccTerm → List ((GccTerm × GccTerm) × GccTerm)
  | [] => []
  | GccTerm.symbol _name :: rest => gccBuildSignature table universeList rest
  | GccTerm.apply function argument :: rest =>
      ((gccRepresentative table universeList function,
          gccRepresentative table universeList argument),
        gccRepresentative table universeList (GccTerm.apply function argument)) ::
        gccBuildSignature table universeList rest

/-- A signature hit inverts to a scanned apply node with the matching key. -/
theorem gccSigLookupInversion (table : List (GccTerm × GccTerm))
    (universeList : List GccTerm) : (scanList : List GccTerm) →
    (searchKey : GccTerm × GccTerm) → (foundValue : GccTerm) →
    gccSigLookup (gccBuildSignature table universeList scanList) searchKey =
      some foundValue →
    ∃ matchedFunction matchedArgument,
      gccPairBeq searchKey (gccRepresentative table universeList matchedFunction,
        gccRepresentative table universeList matchedArgument) = true ∧
      foundValue = gccRepresentative table universeList
        (GccTerm.apply matchedFunction matchedArgument) ∧
      gccTermListHasMember scanList (GccTerm.apply matchedFunction matchedArgument) = true
  | [], _, _, hLookup => nomatch hLookup
  | GccTerm.symbol name :: rest, searchKey, foundValue, hLookup => by
      obtain ⟨matchedFunction, matchedArgument, hKey, hValue, hIn⟩ :=
        gccSigLookupInversion table universeList rest searchKey foundValue hLookup
      exact ⟨matchedFunction, matchedArgument, hKey, hValue,
        gccTermMemberTail (GccTerm.symbol name) rest _ hIn⟩
  | GccTerm.apply headFunction headArgument :: rest, searchKey, foundValue, hLookup => by
      have hUnfold : gccSigLookup
          (gccBuildSignature table universeList
            (GccTerm.apply headFunction headArgument :: rest)) searchKey =
          cond (gccPairBeq searchKey (gccRepresentative table universeList headFunction,
              gccRepresentative table universeList headArgument))
            (some (gccRepresentative table universeList
              (GccTerm.apply headFunction headArgument)))
            (gccSigLookup (gccBuildSignature table universeList rest) searchKey) := rfl
      rw [hUnfold] at hLookup
      cases hKeyBeq : gccPairBeq searchKey
          (gccRepresentative table universeList headFunction,
            gccRepresentative table universeList headArgument) with
      | true =>
          rw [hKeyBeq] at hLookup
          injection hLookup with hValueEq
          exact ⟨headFunction, headArgument, hKeyBeq, hValueEq.symm,
            gccTermMemberHeadOfBeq _ _ _
              (gccTermBeqRefl (GccTerm.apply headFunction headArgument))⟩
      | false =>
          rw [hKeyBeq] at hLookup
          obtain ⟨matchedFunction, matchedArgument, hKey, hValue, hIn⟩ :=
            gccSigLookupInversion table universeList rest searchKey foundValue hLookup
          exact ⟨matchedFunction, matchedArgument, hKey, hValue,
            gccTermMemberTail (GccTerm.apply headFunction headArgument) rest _ hIn⟩

/-- The signature lookup hits for every scanned apply node. -/
theorem gccSigLookupFinds (table : List (GccTerm × GccTerm))
    (universeList : List GccTerm) : (scanList : List GccTerm) →
    (childFunction childArgument : GccTerm) →
    gccTermListHasMember scanList (GccTerm.apply childFunction childArgument) = true →
    ∃ foundValue, gccSigLookup (gccBuildSignature table universeList scanList)
      (gccRepresentative table universeList childFunction,
        gccRepresentative table universeList childArgument) = some foundValue
  | [], _, _, hMember => Bool.noConfusion hMember
  | headTerm :: rest, childFunction, childArgument, hMember => by
      simp only [gccTermListHasMember] at hMember
      cases hBeq : gccTermBeq (GccTerm.apply childFunction childArgument) headTerm with
      | true =>
          have hEq : GccTerm.apply childFunction childArgument = headTerm :=
            gccTermBeqEq (GccTerm.apply childFunction childArgument) headTerm hBeq
          cases hEq
          refine ⟨gccRepresentative table universeList
            (GccTerm.apply childFunction childArgument), ?_⟩
          have hUnfold : gccSigLookup
              (gccBuildSignature table universeList
                (GccTerm.apply childFunction childArgument :: rest))
              (gccRepresentative table universeList childFunction,
                gccRepresentative table universeList childArgument) =
              cond (gccPairBeq (gccRepresentative table universeList childFunction,
                  gccRepresentative table universeList childArgument)
                  (gccRepresentative table universeList childFunction,
                    gccRepresentative table universeList childArgument))
                (some (gccRepresentative table universeList
                  (GccTerm.apply childFunction childArgument)))
                (gccSigLookup (gccBuildSignature table universeList rest)
                  (gccRepresentative table universeList childFunction,
                    gccRepresentative table universeList childArgument)) := rfl
          rw [hUnfold, gccPairBeqRefl]
          rfl
      | false =>
          rw [hBeq] at hMember
          cases headTerm with
          | symbol name =>
              exact gccSigLookupFinds table universeList rest childFunction childArgument
                hMember
          | apply headFunction headArgument =>
              obtain ⟨foundValue, hFound⟩ :=
                gccSigLookupFinds table universeList rest childFunction childArgument hMember
              have hUnfold : gccSigLookup
                  (gccBuildSignature table universeList
                    (GccTerm.apply headFunction headArgument :: rest))
                  (gccRepresentative table universeList childFunction,
                    gccRepresentative table universeList childArgument) =
                  cond (gccPairBeq (gccRepresentative table universeList childFunction,
                      gccRepresentative table universeList childArgument)
                      (gccRepresentative table universeList headFunction,
                        gccRepresentative table universeList headArgument))
                    (some (gccRepresentative table universeList
                      (GccTerm.apply headFunction headArgument)))
                    (gccSigLookup (gccBuildSignature table universeList rest)
                      (gccRepresentative table universeList childFunction,
                        gccRepresentative table universeList childArgument)) := rfl
              cases hHeadKey : gccPairBeq
                  (gccRepresentative table universeList childFunction,
                    gccRepresentative table universeList childArgument)
                  (gccRepresentative table universeList headFunction,
                    gccRepresentative table universeList headArgument) with
              | true =>
                  refine ⟨gccRepresentative table universeList
                    (GccTerm.apply headFunction headArgument), ?_⟩
                  rw [hUnfold, hHeadKey]
                  rfl
              | false =>
                  refine ⟨foundValue, ?_⟩
                  rw [hUnfold, hHeadKey]
                  exact hFound

/-- **Signature functionality**: any hit at a universe apply node's key returns that node's
representative. -/
theorem gccSigLookupFunctional (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hInvariants : GccTableInvariants equations universeList table)
    (hClosed : gccUniverseIsSubtermClosed universeList)
    (childFunction childArgument foundValue : GccTerm)
    (hApplyIn : gccTermListHasMember universeList
      (GccTerm.apply childFunction childArgument) = true)
    (hLookup : gccSigLookup (gccBuildSignature table universeList universeList)
      (gccRepresentative table universeList childFunction,
        gccRepresentative table universeList childArgument) = some foundValue) :
    foundValue = gccRepresentative table universeList
      (GccTerm.apply childFunction childArgument) := by
  obtain ⟨hChildFunctionIn, hChildArgumentIn⟩ := hClosed childFunction childArgument hApplyIn
  obtain ⟨matchedFunction, matchedArgument, hKeyBeq, hValueEq, hMatchedIn⟩ :=
    gccSigLookupInversion table universeList universeList _ foundValue hLookup
  obtain ⟨hMatchedFunctionIn, hMatchedArgumentIn⟩ :=
    hClosed matchedFunction matchedArgument hMatchedIn
  have hKeyEq := gccPairBeqEq _ _ hKeyBeq
  have hFunctionRepEq : gccRepresentative table universeList childFunction =
      gccRepresentative table universeList matchedFunction := congrArg Prod.fst hKeyEq
  have hArgumentRepEq : gccRepresentative table universeList childArgument =
      gccRepresentative table universeList matchedArgument := congrArg Prod.snd hKeyEq
  have hChildFunctionRel := gccRepresentativeIsRelated universeList table
    hInvariants.isReflPopulated childFunction hChildFunctionIn
  have hMatchedFunctionRel := gccRepresentativeIsRelated universeList table
    hInvariants.isReflPopulated matchedFunction hMatchedFunctionIn
  have hChildArgumentRel := gccRepresentativeIsRelated universeList table
    hInvariants.isReflPopulated childArgument hChildArgumentIn
  have hMatchedArgumentRel := gccRepresentativeIsRelated universeList table
    hInvariants.isReflPopulated matchedArgument hMatchedArgumentIn
  rw [hFunctionRepEq] at hChildFunctionRel
  rw [hArgumentRepEq] at hChildArgumentRel
  have hFunctionPair : gccPairListHasMember table (childFunction, matchedFunction) = true :=
    hInvariants.isTransClosed childFunction
      (gccRepresentative table universeList matchedFunction) matchedFunction
      hChildFunctionRel
      (hInvariants.isSymmClosed matchedFunction _ hMatchedFunctionRel)
  have hArgumentPair : gccPairListHasMember table (childArgument, matchedArgument) = true :=
    hInvariants.isTransClosed childArgument
      (gccRepresentative table universeList matchedArgument) matchedArgument
      hChildArgumentRel
      (hInvariants.isSymmClosed matchedArgument _ hMatchedArgumentRel)
  have hApplyPair := hInvariants.isCongClosed childFunction childArgument matchedFunction
    matchedArgument hApplyIn hMatchedIn hFunctionPair hArgumentPair
  have hRepEq := gccRepresentativeRespects universeList table hInvariants.isSymmClosed
    hInvariants.isTransClosed hInvariants.isInsideUniverse _ _ hApplyPair
  exact hValueEq.trans hRepEq.symm

/-! ## Normalization -/

/-- The apply-node step of normalization: signature hit or rebuild. -/
def gccApplyNormalStep (signature : List ((GccTerm × GccTerm) × GccTerm))
    (normalizedFunction normalizedArgument : GccTerm) : GccTerm :=
  match gccSigLookup signature (normalizedFunction, normalizedArgument) with
  | some canonical => canonical
  | none => GccTerm.apply normalizedFunction normalizedArgument

/-- Total structural normalization under a table, universe, and signature. -/
def gccNormalize (table : List (GccTerm × GccTerm)) (universeList : List GccTerm)
    (signature : List ((GccTerm × GccTerm) × GccTerm)) : GccTerm → GccTerm
  | GccTerm.symbol name => gccRepresentative table universeList (GccTerm.symbol name)
  | GccTerm.apply function argument =>
      gccApplyNormalStep signature
        (gccNormalize table universeList signature function)
        (gccNormalize table universeList signature argument)

/-- **Keystone**: every universe member normalizes to its representative. -/
theorem gccNormalizeAgreesOnUniverse (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hInvariants : GccTableInvariants equations universeList table)
    (hClosed : gccUniverseIsSubtermClosed universeList) :
    (term : GccTerm) → gccTermListHasMember universeList term = true →
    gccNormalize table universeList (gccBuildSignature table universeList universeList)
      term = gccRepresentative table universeList term
  | GccTerm.symbol _name, _ => rfl
  | GccTerm.apply function argument, hMember => by
      obtain ⟨hFunctionIn, hArgumentIn⟩ := hClosed function argument hMember
      have ihFunction := gccNormalizeAgreesOnUniverse equations universeList table
        hInvariants hClosed function hFunctionIn
      have ihArgument := gccNormalizeAgreesOnUniverse equations universeList table
        hInvariants hClosed argument hArgumentIn
      obtain ⟨foundValue, hLookup⟩ := gccSigLookupFinds table universeList universeList
        function argument hMember
      have hValue := gccSigLookupFunctional equations universeList table hInvariants
        hClosed function argument foundValue hMember hLookup
      show gccApplyNormalStep (gccBuildSignature table universeList universeList)
        (gccNormalize table universeList (gccBuildSignature table universeList universeList)
          function)
        (gccNormalize table universeList (gccBuildSignature table universeList universeList)
          argument) = gccRepresentative table universeList (GccTerm.apply function argument)
      rw [ihFunction, ihArgument]
      simp only [gccApplyNormalStep]
      rw [hLookup]
      exact hValue

/-- **Completeness**: derivable terms share their normal form. -/
theorem gccNormalizeComplete (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hInvariants : GccTableInvariants equations universeList table)
    (hClosed : gccUniverseIsSubtermClosed universeList)
    (hSides : ∀ index leftTerm rightTerm,
      gccListGetPair equations index = some (leftTerm, rightTerm) →
      gccTermListHasMember universeList leftTerm = true ∧
        gccTermListHasMember universeList rightTerm = true)
    (sourceTerm targetTerm : GccTerm)
    (hDeriv : GccDeriv equations sourceTerm targetTerm) :
    gccNormalize table universeList (gccBuildSignature table universeList universeList)
      sourceTerm =
    gccNormalize table universeList (gccBuildSignature table universeList universeList)
      targetTerm := by
  induction hDeriv with
  | byEquation equationIndex leftTerm rightTerm lookupWitness =>
      obtain ⟨hLeftIn, hRightIn⟩ := hSides equationIndex leftTerm rightTerm lookupWitness
      have hLeftNorm := gccNormalizeAgreesOnUniverse equations universeList table
        hInvariants hClosed leftTerm hLeftIn
      have hRightNorm := gccNormalizeAgreesOnUniverse equations universeList table
        hInvariants hClosed rightTerm hRightIn
      have hTablePair := hInvariants.isEquationPopulated equationIndex leftTerm rightTerm
        lookupWitness
      have hRepEq := gccRepresentativeRespects universeList table hInvariants.isSymmClosed
        hInvariants.isTransClosed hInvariants.isInsideUniverse leftTerm rightTerm hTablePair
      exact hLeftNorm.trans (hRepEq.trans hRightNorm.symm)
  | byRefl term => rfl
  | bySymm leftTerm rightTerm forwardDeriv ihForward => exact ihForward.symm
  | byTrans leftTerm middleTerm rightTerm leftDeriv rightDeriv ihLeft ihRight =>
      exact ihLeft.trans ihRight
  | byCongruence leftFunction rightFunction leftArgument rightArgument functionDeriv
      argumentDeriv ihFunction ihArgument =>
      simp only [gccNormalize]
      rw [ihFunction, ihArgument]

/-- **Soundness**: every term is derivably equal to its normal form. -/
theorem gccNormalizeSound (equations : List (GccTerm × GccTerm))
    (universeList : List GccTerm) (table : List (GccTerm × GccTerm))
    (hSound : ∀ leftTerm rightTerm,
      gccPairListHasMember table (leftTerm, rightTerm) = true →
      GccDeriv equations leftTerm rightTerm) :
    (term : GccTerm) →
    GccDeriv equations term
      (gccNormalize table universeList (gccBuildSignature table universeList universeList)
        term)
  | GccTerm.symbol name =>
      gccRepresentativeSound equations universeList table hSound (GccTerm.symbol name)
  | GccTerm.apply function argument => by
      have ihFunction := gccNormalizeSound equations universeList table hSound function
      have ihArgument := gccNormalizeSound equations universeList table hSound argument
      have hCongruence : GccDeriv equations (GccTerm.apply function argument)
          (GccTerm.apply
            (gccNormalize table universeList
              (gccBuildSignature table universeList universeList) function)
            (gccNormalize table universeList
              (gccBuildSignature table universeList universeList) argument)) :=
        GccDeriv.byCongruence function _ argument _ ihFunction ihArgument
      cases hLookup : gccSigLookup (gccBuildSignature table universeList universeList)
          (gccNormalize table universeList
            (gccBuildSignature table universeList universeList) function,
          gccNormalize table universeList
            (gccBuildSignature table universeList universeList) argument) with
      | none =>
          have hUnfold : gccNormalize table universeList
              (gccBuildSignature table universeList universeList)
              (GccTerm.apply function argument) =
              GccTerm.apply
                (gccNormalize table universeList
                  (gccBuildSignature table universeList universeList) function)
                (gccNormalize table universeList
                  (gccBuildSignature table universeList universeList) argument) := by
            simp only [gccNormalize, gccApplyNormalStep]
            rw [hLookup]
          rw [hUnfold]
          exact hCongruence
      | some foundValue =>
          have hUnfold : gccNormalize table universeList
              (gccBuildSignature table universeList universeList)
              (GccTerm.apply function argument) = foundValue := by
            simp only [gccNormalize, gccApplyNormalStep]
            rw [hLookup]
          rw [hUnfold]
          obtain ⟨matchedFunction, matchedArgument, hKeyBeq, hValueEq, _hMatchedIn⟩ :=
            gccSigLookupInversion table universeList universeList _ foundValue hLookup
          have hKeyEq := gccPairBeqEq _ _ hKeyBeq
          have hNormFunctionEq : gccNormalize table universeList
              (gccBuildSignature table universeList universeList) function =
              gccRepresentative table universeList matchedFunction :=
            congrArg Prod.fst hKeyEq
          have hNormArgumentEq : gccNormalize table universeList
              (gccBuildSignature table universeList universeList) argument =
              gccRepresentative table universeList matchedArgument :=
            congrArg Prod.snd hKeyEq
          have hMatchedFunctionSound := gccRepresentativeSound equations universeList table
            hSound matchedFunction
          have hMatchedArgumentSound := gccRepresentativeSound equations universeList table
            hSound matchedArgument
          have hMatchedApplySound := gccRepresentativeSound equations universeList table
            hSound (GccTerm.apply matchedFunction matchedArgument)
          have hBridge : GccDeriv equations
              (GccTerm.apply
                (gccNormalize table universeList
                  (gccBuildSignature table universeList universeList) function)
                (gccNormalize table universeList
                  (gccBuildSignature table universeList universeList) argument))
              (GccTerm.apply matchedFunction matchedArgument) := by
            rw [hNormFunctionEq, hNormArgumentEq]
            exact GccDeriv.byCongruence _ _ _ _
              (GccDeriv.bySymm matchedFunction _ hMatchedFunctionSound)
              (GccDeriv.bySymm matchedArgument _ hMatchedArgumentSound)
          have hToValue : GccDeriv equations
              (GccTerm.apply matchedFunction matchedArgument) foundValue := by
            rw [hValueEq]
            exact hMatchedApplySound
          exact GccDeriv.byTrans _ _ _ hCongruence (GccDeriv.byTrans _ _ _ hBridge hToValue)

/-! ## The decision procedure -/

/-- Decide ground congruence: saturate over the query universe, normalize, compare. -/
def gccDecide (equations : List (GccTerm × GccTerm)) (sourceTerm targetTerm : GccTerm) :
    Bool :=
  let universeList := gccBuildQueryUniverse equations sourceTerm targetTerm
  let table := gccSaturatedTable equations universeList
  let signature := gccBuildSignature table universeList universeList
  gccTermBeq (gccNormalize table universeList signature sourceTerm)
    (gccNormalize table universeList signature targetTerm)

/-- **Soundness of the decision**: a positive answer yields a derivation. -/
theorem gccDecideImpliesDeriv (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm)
    (hDecide : gccDecide equations sourceTerm targetTerm = true) :
    GccDeriv equations sourceTerm targetTerm := by
  have hInvariants := gccSaturatedTableIsInvariant equations
    (gccBuildQueryUniverse equations sourceTerm targetTerm)
    (gccBuildQueryUniverseHasSides equations sourceTerm targetTerm)
  have hBeq : gccTermBeq
      (gccNormalize
        (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
        (gccBuildQueryUniverse equations sourceTerm targetTerm)
        (gccBuildSignature
          (gccSaturatedTable equations
            (gccBuildQueryUniverse equations sourceTerm targetTerm))
          (gccBuildQueryUniverse equations sourceTerm targetTerm)
          (gccBuildQueryUniverse equations sourceTerm targetTerm))
        sourceTerm)
      (gccNormalize
        (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
        (gccBuildQueryUniverse equations sourceTerm targetTerm)
        (gccBuildSignature
          (gccSaturatedTable equations
            (gccBuildQueryUniverse equations sourceTerm targetTerm))
          (gccBuildQueryUniverse equations sourceTerm targetTerm)
          (gccBuildQueryUniverse equations sourceTerm targetTerm))
        targetTerm) = true := hDecide
  have hNormEq := gccTermBeqEq _ _ hBeq
  have hSourceDeriv := gccNormalizeSound equations
    (gccBuildQueryUniverse equations sourceTerm targetTerm)
    (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
    hInvariants.isSoundlyDerivable sourceTerm
  have hTargetDeriv := gccNormalizeSound equations
    (gccBuildQueryUniverse equations sourceTerm targetTerm)
    (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
    hInvariants.isSoundlyDerivable targetTerm
  have hCross : GccDeriv equations sourceTerm
      (gccNormalize
        (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
        (gccBuildQueryUniverse equations sourceTerm targetTerm)
        (gccBuildSignature
          (gccSaturatedTable equations
            (gccBuildQueryUniverse equations sourceTerm targetTerm))
          (gccBuildQueryUniverse equations sourceTerm targetTerm)
          (gccBuildQueryUniverse equations sourceTerm targetTerm))
        targetTerm) := by
    rw [← hNormEq]
    exact hSourceDeriv
  exact GccDeriv.byTrans sourceTerm _ targetTerm hCross
    (GccDeriv.bySymm targetTerm _ hTargetDeriv)

/-- **Completeness of the decision**: every derivation yields a positive answer. -/
theorem gccDerivImpliesDecide (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm)
    (hDeriv : GccDeriv equations sourceTerm targetTerm) :
    gccDecide equations sourceTerm targetTerm = true := by
  have hInvariants := gccSaturatedTableIsInvariant equations
    (gccBuildQueryUniverse equations sourceTerm targetTerm)
    (gccBuildQueryUniverseHasSides equations sourceTerm targetTerm)
  have hNormEq := gccNormalizeComplete equations
    (gccBuildQueryUniverse equations sourceTerm targetTerm)
    (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
    hInvariants (gccBuildQueryUniverseIsClosed equations sourceTerm targetTerm)
    (gccBuildQueryUniverseHasSides equations sourceTerm targetTerm)
    sourceTerm targetTerm hDeriv
  show gccTermBeq
      (gccNormalize
        (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
        (gccBuildQueryUniverse equations sourceTerm targetTerm)
        (gccBuildSignature
          (gccSaturatedTable equations
            (gccBuildQueryUniverse equations sourceTerm targetTerm))
          (gccBuildQueryUniverse equations sourceTerm targetTerm)
          (gccBuildQueryUniverse equations sourceTerm targetTerm))
        sourceTerm)
      (gccNormalize
        (gccSaturatedTable equations (gccBuildQueryUniverse equations sourceTerm targetTerm))
        (gccBuildQueryUniverse equations sourceTerm targetTerm)
        (gccBuildSignature
          (gccSaturatedTable equations
            (gccBuildQueryUniverse equations sourceTerm targetTerm))
          (gccBuildQueryUniverse equations sourceTerm targetTerm)
          (gccBuildQueryUniverse equations sourceTerm targetTerm))
        targetTerm) = true
  rw [hNormEq]
  exact gccTermBeqRefl _

/-- **The biconditional**: derivability iff the decision procedure answers `true`. -/
theorem gccDeriv_iff_decide (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm) :
    GccDeriv equations sourceTerm targetTerm ↔
      gccDecide equations sourceTerm targetTerm = true :=
  ⟨gccDerivImpliesDecide equations sourceTerm targetTerm,
    gccDecideImpliesDeriv equations sourceTerm targetTerm⟩

/-- Ground congruence is decidable — by computation, no classical axioms. -/
instance gccDerivDecidable (equations : List (GccTerm × GccTerm))
    (sourceTerm targetTerm : GccTerm) : Decidable (GccDeriv equations sourceTerm targetTerm) :=
  match hDecide : gccDecide equations sourceTerm targetTerm with
  | true => isTrue (gccDecideImpliesDeriv equations sourceTerm targetTerm hDecide)
  | false => isFalse (fun hDeriv => Bool.noConfusion
      (hDecide.symm.trans (gccDerivImpliesDecide equations sourceTerm targetTerm hDeriv)))

/-- DISSAT-UF marker: ground congruence closure is DECIDED — biconditional + instance. -/
def fxDissatUf_hasGroundCongruenceDecision : Bool := true

/-! ## Smoke tests (genuineness pins, false cases included)

Symbols: `0 = a`, `1 = b`, `2 = c`, `3 = f`, `4 = g`. -/

/- `f(a) = b, g(b) = c  ⊢  g(f(a)) = c` — expect `true`. -/
#eval gccDecide
  [(GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0), GccTerm.symbol 1),
   (GccTerm.apply (GccTerm.symbol 4) (GccTerm.symbol 1), GccTerm.symbol 2)]
  (GccTerm.apply (GccTerm.symbol 4) (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0)))
  (GccTerm.symbol 2)

/- `a = b  ⊢  f(a) = f(b)` — expect `true`. -/
#eval gccDecide [(GccTerm.symbol 0, GccTerm.symbol 1)]
  (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0))
  (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 1))

/- The classic stress pin: `f^3(a) = a, f^5(a) = a  ⊢  f(a) = a` — expect `true`. -/
#eval gccDecide
  [(GccTerm.apply (GccTerm.symbol 3)
      (GccTerm.apply (GccTerm.symbol 3)
        (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0))),
    GccTerm.symbol 0),
   (GccTerm.apply (GccTerm.symbol 3)
      (GccTerm.apply (GccTerm.symbol 3)
        (GccTerm.apply (GccTerm.symbol 3)
          (GccTerm.apply (GccTerm.symbol 3)
            (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0))))),
    GccTerm.symbol 0)]
  (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0))
  (GccTerm.symbol 0)

/- `a = b  ⊬  f(a) = g(a)` — expect `false`. -/
#eval gccDecide [(GccTerm.symbol 0, GccTerm.symbol 1)]
  (GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0))
  (GccTerm.apply (GccTerm.symbol 4) (GccTerm.symbol 0))

/- Empty equations: `⊢ a = a` — expect `true`. -/
#eval gccDecide [] (GccTerm.symbol 0) (GccTerm.symbol 0)

/- Empty equations: `⊬ a = b` — expect `false`. -/
#eval gccDecide [] (GccTerm.symbol 0) (GccTerm.symbol 1)

end FX1Poly.ComputerAlgebra
