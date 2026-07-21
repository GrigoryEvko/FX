/-! # Certified clause-proof checker

An LRAT-style hint-driven clausal proof checker. The checker consumes a CNF formula and an untrusted
proof trace of steps:

  * `addClause  (clause, unitHints)` — reverse-unit-propagation (RUP) addition: the negated clause
    literals seed a partial assignment, and each hint index must name a working-formula clause that
    is unit (extending the assignment) or falsified (conflict — accept) under the accumulated
    assignment. Strict linear checking: a hinted clause with two or more unfalsified literals rejects
    the step.
  * `addRatClause (clause, ratHints)` — resolution-asymmetric-tautology (RAT) addition on the pivot
    = head literal: every working-formula clause containing the negated pivot must carry a hint group
    whose RUP run refutes the resolvent. Coverage is checked by walking the whole working formula, so
    a missing candidate rejects. The empty clause has no pivot and is rejected here.
  * `deleteClause index` — remove the clause at a position (cons-only `removeAt`).

The trace is accepted only when some `addClause` step adds the empty clause with a valid RUP check.
Clause indices are positional against the current working formula (additions cons at index 0,
deletions shift); the checker is sound for any hint content, so positional discipline costs
completeness only, never soundness.

`cpcProofSound` is the headline: an accepted trace refutes every assignment of the original formula
(`cpcCheckProof formula steps = true → ∀ env, ¬(formula holds)`). The per-step invariant is model
transport, not model identity: RUP additions preserve the exact model set (`cpcRupAdditionEntails`,
genuine entailment via the propagation invariant `cpcRupHintsSound`), deletion only grows it, and a
RAT addition transports a model across the pivot flip (`cpcFlipEnv`, the
Cruz-Filipe/Heule/Hunt/Kaufmann/Schneider-Kamp CADE'17 model-modification argument; constructive —
the flipped assignment is named, no choice principle).

Assignments are total functions `Nat → Bool`, only ever applied — never compared, never extended as
data — so no `funext` anywhere. Propagation state is the list of literals currently forced true; a
literal is falsified when its negation is a member. Hint-driven checking is fuel-free: structural
recursion on the hint list and the step list.

Scope: the CDCL proof finder is deliberately out of scope (any external SAT solver emitting LRAT
traces supplies the untrusted search; only checking is kernel business), recorded by
`fxDissatResidue_hasCdclFinder := false`. The two capabilities that ARE checked —
`fxDissatResidue_hasRupChecker` (RUP + deletion + empty-clause verdict with full soundness) and
`fxDissatResidue_hasRatExtension` (RAT addition with model-modification soundness) — are `true`.

Init only. Structural recursion and full constructor enumeration everywhere; no `omega`, no `decide`
on `Prop`, no `Nat.sub`/`Nat.le_*`/`List.append`/`List.find?` library surface — equality tests
(`cpcNatBeq`, `cpcBoolBeq`, `cpcLiteralBeq`), list membership, stacking, and removal are purpose-built
with hand-proven laws. Per-declaration gate in the twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Boolean kit — structural case bashes, no library lemmas -/

/-- Left conjunct of a true conjunction. -/
theorem cpcAndLeft : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true
  | true, true, _ => rfl
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, hBoth => Bool.noConfusion hBoth
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Right conjunct of a true conjunction. -/
theorem cpcAndRight : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    rightFlag = true
  | true, true, _ => rfl
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, _ => rfl
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Introduce a true conjunction from both conjuncts. -/
theorem cpcAndIntro : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, true, _, _ => rfl
  | true, false, _, hRight => Bool.noConfusion hRight
  | false, true, hLeft, _ => Bool.noConfusion hLeft
  | false, false, hLeft, _ => Bool.noConfusion hLeft

/-- Case split on a true disjunction. -/
theorem cpcOrCases : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = true →
    leftFlag = true ∨ rightFlag = true
  | true, true, _ => Or.inl rfl
  | true, false, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl
  | false, false, hEither => Bool.noConfusion hEither

/-- Introduce a true disjunction from the left. -/
theorem cpcOrIntroLeft : (leftFlag rightFlag : Bool) → leftFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, _ => rfl
  | false, true, hLeft => Bool.noConfusion hLeft
  | false, false, hLeft => Bool.noConfusion hLeft

/-- Introduce a true disjunction from the right. -/
theorem cpcOrIntroRight : (leftFlag rightFlag : Bool) → rightFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, hRight => Bool.noConfusion hRight
  | false, true, _ => rfl
  | false, false, hRight => Bool.noConfusion hRight

/-- A false disjunction has both disjuncts false. -/
theorem cpcOrFalseSplit : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false →
    leftFlag = false ∧ rightFlag = false
  | false, false, _ => And.intro rfl rfl
  | false, true, hEither => Bool.noConfusion hEither
  | true, false, hEither => Bool.noConfusion hEither
  | true, true, hEither => Bool.noConfusion hEither

/-! ## Structural `Nat` equality -/

/-- Structural Boolean equality on `Nat` (avoids `Nat.beq` library lemmas). -/
def cpcNatBeq : Nat → Nat → Bool
  | Nat.zero, Nat.zero => true
  | Nat.zero, Nat.succ _ => false
  | Nat.succ _, Nat.zero => false
  | Nat.succ leftPred, Nat.succ rightPred => cpcNatBeq leftPred rightPred

/-- `cpcNatBeq` is reflexive. -/
theorem cpcNatBeqRefl : (value : Nat) → cpcNatBeq value value = true
  | Nat.zero => rfl
  | Nat.succ valuePred => cpcNatBeqRefl valuePred

/-- `cpcNatBeq` decides equality (soundness direction). -/
theorem cpcNatBeqImpliesEq : (left right : Nat) → cpcNatBeq left right = true → left = right
  | Nat.zero, Nat.zero, _ => rfl
  | Nat.zero, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, Nat.zero, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPred, Nat.succ rightPred, hBeq =>
      congrArg Nat.succ (cpcNatBeqImpliesEq leftPred rightPred hBeq)

/-! ## Literals, clauses, formulas -/

/-- A propositional literal: a variable index with a sign. -/
structure CpcLiteral where
  variableIndex : Nat
  isPositive : Bool

/-- Negation flips the sign. -/
def cpcNegate (literal : CpcLiteral) : CpcLiteral :=
  CpcLiteral.mk literal.variableIndex (Bool.not literal.isPositive)

/-- Structural Boolean equality on `Bool` (avoids `BEq` instances). -/
def cpcBoolBeq : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

/-- `cpcBoolBeq` is reflexive. -/
theorem cpcBoolBeqRefl : (flag : Bool) → cpcBoolBeq flag flag = true
  | false => rfl
  | true => rfl

/-- `cpcBoolBeq` decides equality. -/
theorem cpcBoolBeqImpliesEq : (left right : Bool) → cpcBoolBeq left right = true → left = right
  | false, false, _ => rfl
  | false, true, hBeq => Bool.noConfusion hBeq
  | true, false, hBeq => Bool.noConfusion hBeq
  | true, true, _ => rfl

/-- Boolean equality of literals. -/
def cpcLiteralBeq (left right : CpcLiteral) : Bool :=
  cpcNatBeq left.variableIndex right.variableIndex &&
    cpcBoolBeq left.isPositive right.isPositive

/-- `cpcLiteralBeq` is reflexive. -/
theorem cpcLiteralBeqRefl (literal : CpcLiteral) : cpcLiteralBeq literal literal = true :=
  cpcAndIntro (cpcNatBeq literal.variableIndex literal.variableIndex)
    (cpcBoolBeq literal.isPositive literal.isPositive)
    (cpcNatBeqRefl literal.variableIndex) (cpcBoolBeqRefl literal.isPositive)

/-- `cpcLiteralBeq` decides equality. -/
theorem cpcLiteralBeqImpliesEq (left right : CpcLiteral)
    (hBeq : cpcLiteralBeq left right = true) : left = right := by
  cases left with
  | mk leftIndex leftSign =>
      cases right with
      | mk rightIndex rightSign =>
          have hIndex : leftIndex = rightIndex :=
            cpcNatBeqImpliesEq leftIndex rightIndex
              (cpcAndLeft (cpcNatBeq leftIndex rightIndex) (cpcBoolBeq leftSign rightSign) hBeq)
          have hSign : leftSign = rightSign :=
            cpcBoolBeqImpliesEq leftSign rightSign
              (cpcAndRight (cpcNatBeq leftIndex rightIndex) (cpcBoolBeq leftSign rightSign) hBeq)
          rw [hIndex, hSign]

/-- A failed literal comparison fails in the reverse orientation too. -/
theorem cpcLiteralBeqFalseSymm (left right : CpcLiteral)
    (hFalse : cpcLiteralBeq left right = false) : cpcLiteralBeq right left = false := by
  cases hOpposite : cpcLiteralBeq right left with
  | false => rfl
  | true =>
      have hEq : right = left := cpcLiteralBeqImpliesEq right left hOpposite
      rw [hEq, cpcLiteralBeqRefl left] at hFalse
      exact Bool.noConfusion hFalse

/-- A clause is a literal list with existential (disjunctive) semantics. -/
abbrev CpcClause := List CpcLiteral

/-- Evaluate a literal under a total assignment. -/
def cpcLiteralHolds (assignment : Nat → Bool) (literal : CpcLiteral) : Bool :=
  match literal.isPositive with
  | true => assignment literal.variableIndex
  | false => Bool.not (assignment literal.variableIndex)

/-- Evaluating a negation negates the evaluation. -/
theorem cpcHoldsNegate (assignment : Nat → Bool) : (literal : CpcLiteral) →
    cpcLiteralHolds assignment (cpcNegate literal) =
      Bool.not (cpcLiteralHolds assignment literal)
  | CpcLiteral.mk _index true => rfl
  | CpcLiteral.mk index false => by
      show assignment index = Bool.not (Bool.not (assignment index))
      cases hValue : assignment index with
      | true => rfl
      | false => rfl

/-- Evaluate a clause: some literal holds. -/
def cpcClauseHolds (assignment : Nat → Bool) : CpcClause → Bool
  | [] => false
  | literal :: rest => cpcLiteralHolds assignment literal || cpcClauseHolds assignment rest

/-- Evaluate a formula: every clause holds. -/
def cpcFormulaHolds (assignment : Nat → Bool) : List CpcClause → Bool
  | [] => true
  | clause :: rest => cpcClauseHolds assignment clause && cpcFormulaHolds assignment rest

/-- Membership of a literal in a literal list. -/
def cpcLiteralMember (needle : CpcLiteral) : List CpcLiteral → Bool
  | [] => false
  | head :: tail => cpcLiteralBeq needle head || cpcLiteralMember needle tail

/-- Every literal of a list holds (conjunctive semantics — the propagation state). -/
def cpcAllLiteralsHold (assignment : Nat → Bool) : List CpcLiteral → Bool
  | [] => true
  | literal :: rest => cpcLiteralHolds assignment literal && cpcAllLiteralsHold assignment rest

/-- A member of an all-true literal list holds. -/
theorem cpcMemberHolds (assignment : Nat → Bool) : (literals : List CpcLiteral) →
    (needle : CpcLiteral) →
    cpcLiteralMember needle literals = true →
    cpcAllLiteralsHold assignment literals = true →
    cpcLiteralHolds assignment needle = true
  | [], _needle, hMember, _hAll => Bool.noConfusion hMember
  | head :: tail, needle, hMember, hAll => by
      cases cpcOrCases (cpcLiteralBeq needle head) (cpcLiteralMember needle tail) hMember with
      | inl hBeq =>
          have hEq : needle = head := cpcLiteralBeqImpliesEq needle head hBeq
          rw [hEq]
          exact cpcAndLeft (cpcLiteralHolds assignment head)
            (cpcAllLiteralsHold assignment tail) hAll
      | inr hTail =>
          exact cpcMemberHolds assignment tail needle hTail
            (cpcAndRight (cpcLiteralHolds assignment head)
              (cpcAllLiteralsHold assignment tail) hAll)

/-- Negate every literal of a list (cons-only map). -/
def cpcNegateAll : List CpcLiteral → List CpcLiteral
  | [] => []
  | literal :: rest => cpcNegate literal :: cpcNegateAll rest

/-- A falsified clause makes all its negated literals hold — the RUP seeding fact. -/
theorem cpcFalseClauseNegationsHold (assignment : Nat → Bool) : (clause : CpcClause) →
    cpcClauseHolds assignment clause = false →
    cpcAllLiteralsHold assignment (cpcNegateAll clause) = true
  | [], _hFalse => rfl
  | literal :: rest, hFalse => by
      have hSplit := cpcOrFalseSplit (cpcLiteralHolds assignment literal)
        (cpcClauseHolds assignment rest) hFalse
      show (cpcLiteralHolds assignment (cpcNegate literal) &&
        cpcAllLiteralsHold assignment (cpcNegateAll rest)) = true
      rw [cpcHoldsNegate assignment literal, hSplit.left]
      exact cpcFalseClauseNegationsHold assignment rest hSplit.right

/-! ## Partial-assignment propagation: unfalsified survivors and clause status -/

/-- The literals of a clause NOT falsified by the forced-true list (a literal is
falsified exactly when its negation is forced). -/
def cpcCollectUnfalsified (forcedLiterals : List CpcLiteral) : List CpcLiteral →
    List CpcLiteral
  | [] => []
  | literal :: rest =>
      match cpcLiteralMember (cpcNegate literal) forcedLiterals with
      | true => cpcCollectUnfalsified forcedLiterals rest
      | false => literal :: cpcCollectUnfalsified forcedLiterals rest

/-- Three-way clause status under a partial assignment. -/
inductive CpcClauseStatus where
  | isFalsified : CpcClauseStatus
  | forcesUnit (forcedLiteral : CpcLiteral) : CpcClauseStatus
  | isUnresolved : CpcClauseStatus

/-- Classify a clause: no survivor = falsified, one survivor = unit, two or more
survivors = unresolved (covers satisfied clauses too — strict linear RUP rejects them). -/
def cpcClauseStatus (forcedLiterals : List CpcLiteral) (clause : CpcClause) :
    CpcClauseStatus :=
  match cpcCollectUnfalsified forcedLiterals clause with
  | [] => CpcClauseStatus.isFalsified
  | [forcedLiteral] => CpcClauseStatus.forcesUnit forcedLiteral
  | _first :: _second :: _rest => CpcClauseStatus.isUnresolved

/-- The semantic engine: a true clause stays true after dropping falsified literals
(under an assignment satisfying every forced literal). -/
theorem cpcCollectPreservesTruth (assignment : Nat → Bool) (forcedLiterals : List CpcLiteral)
    (hForced : cpcAllLiteralsHold assignment forcedLiterals = true) :
    (clause : CpcClause) →
    cpcClauseHolds assignment clause = true →
    cpcClauseHolds assignment (cpcCollectUnfalsified forcedLiterals clause) = true
  | [], hHolds => hHolds
  | literal :: rest, hHolds => by
      have hSplit := cpcOrCases (cpcLiteralHolds assignment literal)
        (cpcClauseHolds assignment rest) hHolds
      cases hMember : cpcLiteralMember (cpcNegate literal) forcedLiterals with
      | true =>
          simp only [cpcCollectUnfalsified, hMember]
          cases hSplit with
          | inl hLiteral =>
              have hNegHolds : cpcLiteralHolds assignment (cpcNegate literal) = true :=
                cpcMemberHolds assignment forcedLiterals (cpcNegate literal) hMember hForced
              rw [cpcHoldsNegate assignment literal, hLiteral] at hNegHolds
              exact Bool.noConfusion hNegHolds
          | inr hRest =>
              exact cpcCollectPreservesTruth assignment forcedLiterals hForced rest hRest
      | false =>
          simp only [cpcCollectUnfalsified, hMember]
          cases hSplit with
          | inl hLiteral =>
              exact cpcOrIntroLeft (cpcLiteralHolds assignment literal)
                (cpcClauseHolds assignment (cpcCollectUnfalsified forcedLiterals rest)) hLiteral
          | inr hRest =>
              exact cpcOrIntroRight (cpcLiteralHolds assignment literal)
                (cpcClauseHolds assignment (cpcCollectUnfalsified forcedLiterals rest))
                (cpcCollectPreservesTruth assignment forcedLiterals hForced rest hRest)

/-- A falsified status means no survivor at all. -/
theorem cpcStatusFalsifiedCollectNil (forcedLiterals : List CpcLiteral) (clause : CpcClause)
    (hStatus : cpcClauseStatus forcedLiterals clause = CpcClauseStatus.isFalsified) :
    cpcCollectUnfalsified forcedLiterals clause = [] := by
  cases hCollect : cpcCollectUnfalsified forcedLiterals clause with
  | nil => rfl
  | cons firstSurvivor remainingSurvivors =>
      cases remainingSurvivors with
      | nil =>
          simp only [cpcClauseStatus, hCollect] at hStatus
          exact CpcClauseStatus.noConfusion hStatus
      | cons secondSurvivor tailSurvivors =>
          simp only [cpcClauseStatus, hCollect] at hStatus
          exact CpcClauseStatus.noConfusion hStatus

/-- A unit status means exactly one survivor — the forced literal. -/
theorem cpcStatusUnitCollectSingleton (forcedLiterals : List CpcLiteral) (clause : CpcClause)
    (forcedLiteral : CpcLiteral)
    (hStatus : cpcClauseStatus forcedLiterals clause =
      CpcClauseStatus.forcesUnit forcedLiteral) :
    cpcCollectUnfalsified forcedLiterals clause = [forcedLiteral] := by
  cases hCollect : cpcCollectUnfalsified forcedLiterals clause with
  | nil =>
      simp only [cpcClauseStatus, hCollect] at hStatus
      exact CpcClauseStatus.noConfusion hStatus
  | cons firstSurvivor remainingSurvivors =>
      cases remainingSurvivors with
      | nil =>
          simp only [cpcClauseStatus, hCollect] at hStatus
          injection hStatus with hFirst
          rw [hFirst]
      | cons secondSurvivor tailSurvivors =>
          simp only [cpcClauseStatus, hCollect] at hStatus
          exact CpcClauseStatus.noConfusion hStatus

/-! ## Positional indexing into the working formula -/

/-- Fetch the clause at a position (structural, four-way enumeration). -/
def cpcGetClause : Nat → List CpcClause → Option CpcClause
  | Nat.zero, [] => none
  | Nat.zero, clause :: _rest => some clause
  | Nat.succ _prevIndex, [] => none
  | Nat.succ prevIndex, _clause :: rest => cpcGetClause prevIndex rest

/-- A fetched clause of a satisfied formula is satisfied. -/
theorem cpcGetClauseHolds (assignment : Nat → Bool) : (index : Nat) →
    (formula : List CpcClause) → (clause : CpcClause) →
    cpcGetClause index formula = some clause →
    cpcFormulaHolds assignment formula = true →
    cpcClauseHolds assignment clause = true
  | Nat.zero, [], _clause, hGet, _hFormula => nomatch hGet
  | Nat.succ _prevIndex, [], _clause, hGet, _hFormula => nomatch hGet
  | Nat.zero, head :: rest, clause, hGet, hFormula => by
      injection hGet with hEq
      rw [← hEq]
      exact cpcAndLeft (cpcClauseHolds assignment head) (cpcFormulaHolds assignment rest)
        hFormula
  | Nat.succ prevIndex, head :: rest, clause, hGet, hFormula =>
      cpcGetClauseHolds assignment prevIndex rest clause hGet
        (cpcAndRight (cpcClauseHolds assignment head) (cpcFormulaHolds assignment rest)
          hFormula)

/-- Remove the clause at a position (identity when out of range). -/
def cpcRemoveClauseAt : Nat → List CpcClause → List CpcClause
  | Nat.zero, [] => []
  | Nat.zero, _removed :: rest => rest
  | Nat.succ _prevIndex, [] => []
  | Nat.succ prevIndex, kept :: rest => kept :: cpcRemoveClauseAt prevIndex rest

/-- Deletion shrinks the formula, so satisfaction is preserved (models only GROW). -/
theorem cpcRemoveClauseAtPreservesHolds (assignment : Nat → Bool) : (index : Nat) →
    (formula : List CpcClause) →
    cpcFormulaHolds assignment formula = true →
    cpcFormulaHolds assignment (cpcRemoveClauseAt index formula) = true
  | Nat.zero, [], hFormula => hFormula
  | Nat.zero, removed :: rest, hFormula =>
      cpcAndRight (cpcClauseHolds assignment removed) (cpcFormulaHolds assignment rest)
        hFormula
  | Nat.succ _prevIndex, [], hFormula => hFormula
  | Nat.succ prevIndex, kept :: rest, hFormula =>
      cpcAndIntro (cpcClauseHolds assignment kept)
        (cpcFormulaHolds assignment (cpcRemoveClauseAt prevIndex rest))
        (cpcAndLeft (cpcClauseHolds assignment kept) (cpcFormulaHolds assignment rest)
          hFormula)
        (cpcRemoveClauseAtPreservesHolds assignment prevIndex rest
          (cpcAndRight (cpcClauseHolds assignment kept) (cpcFormulaHolds assignment rest)
            hFormula))

/-! ## The LRAT hinted-RUP check -/

/-- Walk the hint indices: each hinted clause must be unit (extend the forced list) or
falsified (conflict — ACCEPT).  Missing clauses, non-unit non-falsified clauses, and
hint exhaustion all reject.  Fuel-free: structural on the hint list. -/
def cpcCheckRupHints (formula : List CpcClause) : List Nat → List CpcLiteral → Bool
  | [], _forcedLiterals => false
  | hintIndex :: remainingHints, forcedLiterals =>
      match cpcGetClause hintIndex formula with
      | none => false
      | some hintedClause =>
          match cpcClauseStatus forcedLiterals hintedClause with
          | CpcClauseStatus.isFalsified => true
          | CpcClauseStatus.forcesUnit forcedLiteral =>
              cpcCheckRupHints formula remainingHints (forcedLiteral :: forcedLiterals)
          | CpcClauseStatus.isUnresolved => false

/-- **Propagation invariant** — a successful hint walk is absurd under any assignment
satisfying the formula and every forced literal: unit steps force their literal
(semantically), and the final conflict clause is both satisfied and all-falsified. -/
theorem cpcRupHintsSound (assignment : Nat → Bool) (formula : List CpcClause) :
    (hints : List Nat) → (forcedLiterals : List CpcLiteral) →
    cpcCheckRupHints formula hints forcedLiterals = true →
    cpcFormulaHolds assignment formula = true →
    cpcAllLiteralsHold assignment forcedLiterals = true →
    False
  | [], _forcedLiterals, hCheck, _hFormula, _hForced => Bool.noConfusion hCheck
  | hintIndex :: remainingHints, forcedLiterals, hCheck, hFormula, hForced => by
      cases hGet : cpcGetClause hintIndex formula with
      | none =>
          simp only [cpcCheckRupHints, hGet] at hCheck
          exact Bool.noConfusion hCheck
      | some hintedClause =>
          simp only [cpcCheckRupHints, hGet] at hCheck
          cases hStatus : cpcClauseStatus forcedLiterals hintedClause with
          | isFalsified =>
              have hClauseHolds : cpcClauseHolds assignment hintedClause = true :=
                cpcGetClauseHolds assignment hintIndex formula hintedClause hGet hFormula
              have hCollectHolds := cpcCollectPreservesTruth assignment forcedLiterals
                hForced hintedClause hClauseHolds
              rw [cpcStatusFalsifiedCollectNil forcedLiterals hintedClause hStatus]
                at hCollectHolds
              exact Bool.noConfusion hCollectHolds
          | forcesUnit forcedLiteral =>
              rw [hStatus] at hCheck
              have hClauseHolds : cpcClauseHolds assignment hintedClause = true :=
                cpcGetClauseHolds assignment hintIndex formula hintedClause hGet hFormula
              have hCollectHolds := cpcCollectPreservesTruth assignment forcedLiterals
                hForced hintedClause hClauseHolds
              rw [cpcStatusUnitCollectSingleton forcedLiterals hintedClause forcedLiteral
                hStatus] at hCollectHolds
              have hForcedHolds : cpcLiteralHolds assignment forcedLiteral = true := by
                cases cpcOrCases (cpcLiteralHolds assignment forcedLiteral)
                    (cpcClauseHolds assignment []) hCollectHolds with
                | inl hHead => exact hHead
                | inr hNil => exact Bool.noConfusion hNil
              exact cpcRupHintsSound assignment formula remainingHints
                (forcedLiteral :: forcedLiterals) hCheck hFormula
                (cpcAndIntro (cpcLiteralHolds assignment forcedLiteral)
                  (cpcAllLiteralsHold assignment forcedLiterals) hForcedHolds hForced)
          | isUnresolved =>
              rw [hStatus] at hCheck
              exact Bool.noConfusion hCheck

/-- The RUP addition check: seed the negated clause literals, walk the hints. -/
def cpcCheckRupAddition (formula : List CpcClause) (addedClause : CpcClause)
    (unitHints : List Nat) : Bool :=
  cpcCheckRupHints formula unitHints (cpcNegateAll addedClause)

/-- **RUP soundness**: a checked addition is a genuine entailment — every assignment
satisfying the formula satisfies the added clause. -/
theorem cpcRupAdditionEntails (assignment : Nat → Bool) (formula : List CpcClause)
    (addedClause : CpcClause) (unitHints : List Nat)
    (hCheck : cpcCheckRupAddition formula addedClause unitHints = true)
    (hFormula : cpcFormulaHolds assignment formula = true) :
    cpcClauseHolds assignment addedClause = true := by
  cases hClause : cpcClauseHolds assignment addedClause with
  | true => rfl
  | false =>
      exact False.elim (cpcRupHintsSound assignment formula unitHints
        (cpcNegateAll addedClause) hCheck hFormula
        (cpcFalseClauseNegationsHold assignment addedClause hClause))

/-! ## Proof steps and the trace walker -/

/-- One RAT hint group: a resolution-candidate position with its RUP hints. -/
structure CpcRatHintGroup where
  candidateIndex : Nat
  unitHints : List Nat

/-- One step of a clausal proof trace. -/
inductive CpcProofStep where
  | addClause (addedClause : CpcClause) (unitHints : List Nat) : CpcProofStep
  | addRatClause (addedClause : CpcClause) (ratHints : List CpcRatHintGroup) : CpcProofStep
  | deleteClause (removedIndex : Nat) : CpcProofStep

/-- Look up the hint group for a candidate position. -/
def cpcRatHintLookup (targetIndex : Nat) : List CpcRatHintGroup → Option (List Nat)
  | [] => none
  | group :: remainingGroups =>
      match cpcNatBeq targetIndex group.candidateIndex with
      | true => some group.unitHints
      | false => cpcRatHintLookup targetIndex remainingGroups

/-- Drop every occurrence of a literal from a list (cons-only filter-out). -/
def cpcRemoveLiteral (removedLiteral : CpcLiteral) : List CpcLiteral → List CpcLiteral
  | [] => []
  | literal :: rest =>
      match cpcLiteralBeq literal removedLiteral with
      | true => cpcRemoveLiteral removedLiteral rest
      | false => literal :: cpcRemoveLiteral removedLiteral rest

/-- Cons-only append of literal lists (`List.append` is banned). -/
def cpcStackLiterals : List CpcLiteral → List CpcLiteral → List CpcLiteral
  | [], second => second
  | literal :: rest, second => literal :: cpcStackLiterals rest second

/-- Stacking preserves the all-true property. -/
theorem cpcStackAllHold (assignment : Nat → Bool) : (first second : List CpcLiteral) →
    cpcAllLiteralsHold assignment first = true →
    cpcAllLiteralsHold assignment second = true →
    cpcAllLiteralsHold assignment (cpcStackLiterals first second) = true
  | [], _second, _hFirst, hSecond => hSecond
  | literal :: rest, second, hFirst, hSecond =>
      cpcAndIntro (cpcLiteralHolds assignment literal)
        (cpcAllLiteralsHold assignment (cpcStackLiterals rest second))
        (cpcAndLeft (cpcLiteralHolds assignment literal)
          (cpcAllLiteralsHold assignment rest) hFirst)
        (cpcStackAllHold assignment rest second
          (cpcAndRight (cpcLiteralHolds assignment literal)
            (cpcAllLiteralsHold assignment rest) hFirst)
          hSecond)

/-- Walk the whole working formula: every clause containing the negated pivot must carry a hint
group whose RUP run refutes the resolvent (added clause plus the candidate minus the negated pivot).
A missing candidate rejects, so coverage is over the whole formula rather than the supplied hints
alone. -/
def cpcCheckRatCandidates (workingFormula : List CpcClause) (addedClause : CpcClause)
    (negatedPivot : CpcLiteral) (ratHints : List CpcRatHintGroup) :
    Nat → List CpcClause → Bool
  | _candidatePosition, [] => true
  | candidatePosition, candidate :: remainingCandidates =>
      match cpcLiteralMember negatedPivot candidate with
      | false =>
          cpcCheckRatCandidates workingFormula addedClause negatedPivot ratHints
            (Nat.succ candidatePosition) remainingCandidates
      | true =>
          match cpcRatHintLookup candidatePosition ratHints with
          | none => false
          | some unitHints =>
              cpcCheckRupHints workingFormula unitHints
                (cpcStackLiterals (cpcNegateAll addedClause)
                  (cpcNegateAll (cpcRemoveLiteral negatedPivot candidate))) &&
              cpcCheckRatCandidates workingFormula addedClause negatedPivot ratHints
                (Nat.succ candidatePosition) remainingCandidates

/-- Walk the proof trace against the working formula.  Accept ONLY when an `addClause`
step adds the empty clause with a valid RUP check.  RUP/RAT additions cons the clause;
deletions remove by position; the empty clause is rejected as a RAT addition (no
pivot). -/
def cpcCheckProofSteps : List CpcProofStep → List CpcClause → Bool
  | [], _workingFormula => false
  | CpcProofStep.addClause addedClause unitHints :: remainingSteps, workingFormula =>
      match cpcCheckRupAddition workingFormula addedClause unitHints with
      | false => false
      | true =>
          match addedClause with
          | [] => true
          | firstLiteral :: restLiterals =>
              cpcCheckProofSteps remainingSteps
                ((firstLiteral :: restLiterals) :: workingFormula)
  | CpcProofStep.addRatClause addedClause ratHints :: remainingSteps, workingFormula =>
      match addedClause with
      | [] => false
      | pivotLiteral :: restLiterals =>
          match cpcCheckRatCandidates workingFormula (pivotLiteral :: restLiterals)
              (cpcNegate pivotLiteral) ratHints Nat.zero workingFormula with
          | false => false
          | true =>
              cpcCheckProofSteps remainingSteps
                ((pivotLiteral :: restLiterals) :: workingFormula)
  | CpcProofStep.deleteClause removedIndex :: remainingSteps, workingFormula =>
      cpcCheckProofSteps remainingSteps (cpcRemoveClauseAt removedIndex workingFormula)

/-- The certified clause-proof checker: walk the trace from the input formula. -/
def cpcCheckProof (formula : List CpcClause) (steps : List CpcProofStep) : Bool :=
  cpcCheckProofSteps steps formula

/-! ## RAT soundness: the model-modification (pivot-flip) argument -/

/-- Flip the pivot's variable to whatever makes the pivot true; leave every other
variable untouched.  Only ever APPLIED — never compared as a function. -/
def cpcFlipEnv (pivotLiteral : CpcLiteral) (assignment : Nat → Bool) : Nat → Bool :=
  fun queriedIndex =>
    cond (cpcNatBeq queriedIndex pivotLiteral.variableIndex)
      pivotLiteral.isPositive (assignment queriedIndex)

/-- The flipped assignment satisfies the pivot. -/
theorem cpcFlipEnvSatisfiesPivot (assignment : Nat → Bool) : (pivotLiteral : CpcLiteral) →
    cpcLiteralHolds (cpcFlipEnv pivotLiteral assignment) pivotLiteral = true
  | CpcLiteral.mk pivotIndex true => by
      show cond (cpcNatBeq pivotIndex pivotIndex) true (assignment pivotIndex) = true
      rw [cpcNatBeqRefl pivotIndex]
      rfl
  | CpcLiteral.mk pivotIndex false => by
      show Bool.not (cond (cpcNatBeq pivotIndex pivotIndex) false (assignment pivotIndex))
        = true
      rw [cpcNatBeqRefl pivotIndex]
      rfl

/-- A true literal distinct from the negated pivot survives the flip (given the pivot
itself is false: same-variable-same-sign would contradict truth, same-variable-
opposite-sign IS the negated pivot). -/
theorem cpcFlipEnvPreservesLiteral (assignment : Nat → Bool) :
    (pivotLiteral literal : CpcLiteral) →
    cpcLiteralBeq literal (cpcNegate pivotLiteral) = false →
    cpcLiteralHolds assignment pivotLiteral = false →
    cpcLiteralHolds assignment literal = true →
    cpcLiteralHolds (cpcFlipEnv pivotLiteral assignment) literal = true
  | CpcLiteral.mk pivotIndex pivotSign, CpcLiteral.mk literalIndex literalSign,
      hNotNegated, hPivotFalse, hLiteralTrue => by
      cases hSameVariable : cpcNatBeq literalIndex pivotIndex with
      | false =>
          cases literalSign with
          | true =>
              show cond (cpcNatBeq literalIndex pivotIndex) pivotSign
                (assignment literalIndex) = true
              rw [hSameVariable]
              exact hLiteralTrue
          | false =>
              show Bool.not (cond (cpcNatBeq literalIndex pivotIndex) pivotSign
                (assignment literalIndex)) = true
              rw [hSameVariable]
              exact hLiteralTrue
      | true =>
          have hIndexEq : literalIndex = pivotIndex :=
            cpcNatBeqImpliesEq literalIndex pivotIndex hSameVariable
          subst hIndexEq
          cases literalSign with
          | true =>
              cases pivotSign with
              | true => exact Bool.noConfusion (hPivotFalse.symm.trans hLiteralTrue)
              | false =>
                  have hRefl : cpcLiteralBeq (CpcLiteral.mk literalIndex true)
                      (cpcNegate (CpcLiteral.mk literalIndex false)) = true := by
                    show (cpcNatBeq literalIndex literalIndex && cpcBoolBeq true true) = true
                    rw [cpcNatBeqRefl literalIndex]
                    rfl
                  exact Bool.noConfusion (hRefl.symm.trans hNotNegated)
          | false =>
              cases pivotSign with
              | true =>
                  have hRefl : cpcLiteralBeq (CpcLiteral.mk literalIndex false)
                      (cpcNegate (CpcLiteral.mk literalIndex true)) = true := by
                    show (cpcNatBeq literalIndex literalIndex && cpcBoolBeq false false) = true
                    rw [cpcNatBeqRefl literalIndex]
                    rfl
                  exact Bool.noConfusion (hRefl.symm.trans hNotNegated)
              | false => exact Bool.noConfusion (hPivotFalse.symm.trans hLiteralTrue)

/-- A true clause avoiding the negated pivot stays true after the flip. -/
theorem cpcFlipEnvPreservesClause (assignment : Nat → Bool) (pivotLiteral : CpcLiteral)
    (hPivotFalse : cpcLiteralHolds assignment pivotLiteral = false) :
    (clause : List CpcLiteral) →
    cpcLiteralMember (cpcNegate pivotLiteral) clause = false →
    cpcClauseHolds assignment clause = true →
    cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) clause = true
  | [], _hNoNegated, hHolds => hHolds
  | literal :: rest, hNoNegated, hHolds => by
      have hSplit := cpcOrFalseSplit (cpcLiteralBeq (cpcNegate pivotLiteral) literal)
        (cpcLiteralMember (cpcNegate pivotLiteral) rest) hNoNegated
      cases cpcOrCases (cpcLiteralHolds assignment literal)
          (cpcClauseHolds assignment rest) hHolds with
      | inl hLiteral =>
          exact cpcOrIntroLeft
            (cpcLiteralHolds (cpcFlipEnv pivotLiteral assignment) literal)
            (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) rest)
            (cpcFlipEnvPreservesLiteral assignment pivotLiteral literal
              (cpcLiteralBeqFalseSymm (cpcNegate pivotLiteral) literal hSplit.left)
              hPivotFalse hLiteral)
      | inr hRest =>
          exact cpcOrIntroRight
            (cpcLiteralHolds (cpcFlipEnv pivotLiteral assignment) literal)
            (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) rest)
            (cpcFlipEnvPreservesClause assignment pivotLiteral hPivotFalse rest
              hSplit.right hRest)

/-- Removal really removes: the removed literal is no member of the result. -/
theorem cpcRemoveLiteralNotMember (removedLiteral : CpcLiteral) :
    (literals : List CpcLiteral) →
    cpcLiteralMember removedLiteral (cpcRemoveLiteral removedLiteral literals) = false
  | [] => rfl
  | literal :: rest => by
      cases hBeq : cpcLiteralBeq literal removedLiteral with
      | true =>
          simp only [cpcRemoveLiteral, hBeq]
          exact cpcRemoveLiteralNotMember removedLiteral rest
      | false =>
          simp only [cpcRemoveLiteral, hBeq]
          show (cpcLiteralBeq removedLiteral literal ||
            cpcLiteralMember removedLiteral (cpcRemoveLiteral removedLiteral rest)) = false
          rw [cpcLiteralBeqFalseSymm literal removedLiteral hBeq,
            cpcRemoveLiteralNotMember removedLiteral rest]
          rfl

/-- A true removed-literal list lifts to the original clause (removal is a sublist). -/
theorem cpcRemoveLiteralHoldsLift (assignment : Nat → Bool) (removedLiteral : CpcLiteral) :
    (literals : List CpcLiteral) →
    cpcClauseHolds assignment (cpcRemoveLiteral removedLiteral literals) = true →
    cpcClauseHolds assignment literals = true
  | [], hHolds => hHolds
  | literal :: rest, hHolds => by
      cases hBeq : cpcLiteralBeq literal removedLiteral with
      | true =>
          simp only [cpcRemoveLiteral, hBeq] at hHolds
          exact cpcOrIntroRight (cpcLiteralHolds assignment literal)
            (cpcClauseHolds assignment rest)
            (cpcRemoveLiteralHoldsLift assignment removedLiteral rest hHolds)
      | false =>
          simp only [cpcRemoveLiteral, hBeq] at hHolds
          cases cpcOrCases (cpcLiteralHolds assignment literal)
              (cpcClauseHolds assignment (cpcRemoveLiteral removedLiteral rest)) hHolds with
          | inl hLiteral =>
              exact cpcOrIntroLeft (cpcLiteralHolds assignment literal)
                (cpcClauseHolds assignment rest) hLiteral
          | inr hRest =>
              exact cpcOrIntroRight (cpcLiteralHolds assignment literal)
                (cpcClauseHolds assignment rest)
                (cpcRemoveLiteralHoldsLift assignment removedLiteral rest hRest)

/-- A checked candidate's reduced clause (candidate minus negated pivot) is entailed
whenever the added clause is false — the per-candidate AT fact. -/
theorem cpcRatCandidateEntails (assignment : Nat → Bool) (workingFormula : List CpcClause)
    (addedClause reducedCandidate : List CpcLiteral) (unitHints : List Nat)
    (hCheck : cpcCheckRupHints workingFormula unitHints
      (cpcStackLiterals (cpcNegateAll addedClause) (cpcNegateAll reducedCandidate)) = true)
    (hFormula : cpcFormulaHolds assignment workingFormula = true)
    (hAddedFalse : cpcClauseHolds assignment addedClause = false) :
    cpcClauseHolds assignment reducedCandidate = true := by
  cases hReduced : cpcClauseHolds assignment reducedCandidate with
  | true => rfl
  | false =>
      exact False.elim (cpcRupHintsSound assignment workingFormula unitHints
        (cpcStackLiterals (cpcNegateAll addedClause) (cpcNegateAll reducedCandidate))
        hCheck hFormula
        (cpcStackAllHold assignment (cpcNegateAll addedClause)
          (cpcNegateAll reducedCandidate)
          (cpcFalseClauseNegationsHold assignment addedClause hAddedFalse)
          (cpcFalseClauseNegationsHold assignment reducedCandidate hReduced)))

/-- **The RAT model shift**: when every candidate checks, the pivot flip carries a model
of the suffix to a model of the suffix — clauses without the negated pivot survive
literally, clauses with it survive through their entailed reduced clause. -/
theorem cpcRatCandidatesSound (assignment : Nat → Bool) (workingFormula : List CpcClause)
    (addedClause : List CpcLiteral) (pivotLiteral : CpcLiteral)
    (ratHints : List CpcRatHintGroup)
    (hFormula : cpcFormulaHolds assignment workingFormula = true)
    (hAddedFalse : cpcClauseHolds assignment addedClause = false)
    (hPivotFalse : cpcLiteralHolds assignment pivotLiteral = false) :
    (candidateSuffix : List CpcClause) → (candidatePosition : Nat) →
    cpcCheckRatCandidates workingFormula addedClause (cpcNegate pivotLiteral) ratHints
      candidatePosition candidateSuffix = true →
    cpcFormulaHolds assignment candidateSuffix = true →
    cpcFormulaHolds (cpcFlipEnv pivotLiteral assignment) candidateSuffix = true
  | [], _candidatePosition, _hCheck, _hSuffix => rfl
  | candidate :: remainingCandidates, candidatePosition, hCheck, hSuffix => by
      have hCandidateHolds := cpcAndLeft (cpcClauseHolds assignment candidate)
        (cpcFormulaHolds assignment remainingCandidates) hSuffix
      have hRemaining := cpcAndRight (cpcClauseHolds assignment candidate)
        (cpcFormulaHolds assignment remainingCandidates) hSuffix
      cases hMember : cpcLiteralMember (cpcNegate pivotLiteral) candidate with
      | false =>
          simp only [cpcCheckRatCandidates, hMember] at hCheck
          exact cpcAndIntro
            (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) candidate)
            (cpcFormulaHolds (cpcFlipEnv pivotLiteral assignment) remainingCandidates)
            (cpcFlipEnvPreservesClause assignment pivotLiteral hPivotFalse candidate
              hMember hCandidateHolds)
            (cpcRatCandidatesSound assignment workingFormula addedClause pivotLiteral
              ratHints hFormula hAddedFalse hPivotFalse remainingCandidates
              (Nat.succ candidatePosition) hCheck hRemaining)
      | true =>
          simp only [cpcCheckRatCandidates, hMember] at hCheck
          cases hLookup : cpcRatHintLookup candidatePosition ratHints with
          | none =>
              rw [hLookup] at hCheck
              exact Bool.noConfusion hCheck
          | some unitHints =>
              rw [hLookup] at hCheck
              have hRup := cpcAndLeft
                (cpcCheckRupHints workingFormula unitHints
                  (cpcStackLiterals (cpcNegateAll addedClause)
                    (cpcNegateAll (cpcRemoveLiteral (cpcNegate pivotLiteral) candidate))))
                (cpcCheckRatCandidates workingFormula addedClause (cpcNegate pivotLiteral)
                  ratHints (Nat.succ candidatePosition) remainingCandidates)
                hCheck
              have hRecurse := cpcAndRight
                (cpcCheckRupHints workingFormula unitHints
                  (cpcStackLiterals (cpcNegateAll addedClause)
                    (cpcNegateAll (cpcRemoveLiteral (cpcNegate pivotLiteral) candidate))))
                (cpcCheckRatCandidates workingFormula addedClause (cpcNegate pivotLiteral)
                  ratHints (Nat.succ candidatePosition) remainingCandidates)
                hCheck
              have hReducedHolds := cpcRatCandidateEntails assignment workingFormula
                addedClause (cpcRemoveLiteral (cpcNegate pivotLiteral) candidate)
                unitHints hRup hFormula hAddedFalse
              have hReducedFlip := cpcFlipEnvPreservesClause assignment pivotLiteral
                hPivotFalse (cpcRemoveLiteral (cpcNegate pivotLiteral) candidate)
                (cpcRemoveLiteralNotMember (cpcNegate pivotLiteral) candidate)
                hReducedHolds
              exact cpcAndIntro
                (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) candidate)
                (cpcFormulaHolds (cpcFlipEnv pivotLiteral assignment) remainingCandidates)
                (cpcRemoveLiteralHoldsLift (cpcFlipEnv pivotLiteral assignment)
                  (cpcNegate pivotLiteral) candidate hReducedFlip)
                (cpcRatCandidatesSound assignment workingFormula addedClause pivotLiteral
                  ratHints hFormula hAddedFalse hPivotFalse remainingCandidates
                  (Nat.succ candidatePosition) hRecurse hRemaining)

/-! ## The headline soundness chain -/

/-- **Trace invariant**: an accepted trace refutes every model of the current working
formula.  RUP additions preserve models exactly, deletions grow them, RAT additions
transport the model across the pivot flip — the assignment is GENERALIZED through the
induction precisely so the flipped assignment can feed the recursive call. -/
theorem cpcProofStepsSound : (steps : List CpcProofStep) →
    (workingFormula : List CpcClause) → (assignment : Nat → Bool) →
    cpcCheckProofSteps steps workingFormula = true →
    cpcFormulaHolds assignment workingFormula = true →
    False
  | [], _workingFormula, _assignment, hCheck, _hFormula => Bool.noConfusion hCheck
  | CpcProofStep.addClause addedClause unitHints :: remainingSteps, workingFormula,
      assignment, hCheck, hFormula => by
      cases hRup : cpcCheckRupAddition workingFormula addedClause unitHints with
      | false =>
          simp only [cpcCheckProofSteps, hRup] at hCheck
          exact Bool.noConfusion hCheck
      | true =>
          simp only [cpcCheckProofSteps, hRup] at hCheck
          have hAddedHolds := cpcRupAdditionEntails assignment workingFormula addedClause
            unitHints hRup hFormula
          cases addedClause with
          | nil => exact Bool.noConfusion hAddedHolds
          | cons firstLiteral restLiterals =>
              exact cpcProofStepsSound remainingSteps
                ((firstLiteral :: restLiterals) :: workingFormula) assignment hCheck
                (cpcAndIntro
                  (cpcClauseHolds assignment (firstLiteral :: restLiterals))
                  (cpcFormulaHolds assignment workingFormula) hAddedHolds hFormula)
  | CpcProofStep.addRatClause addedClause ratHints :: remainingSteps, workingFormula,
      assignment, hCheck, hFormula => by
      cases addedClause with
      | nil =>
          simp only [cpcCheckProofSteps] at hCheck
          exact Bool.noConfusion hCheck
      | cons pivotLiteral restLiterals =>
          simp only [cpcCheckProofSteps] at hCheck
          cases hRat : cpcCheckRatCandidates workingFormula (pivotLiteral :: restLiterals)
              (cpcNegate pivotLiteral) ratHints Nat.zero workingFormula with
          | false =>
              rw [hRat] at hCheck
              exact Bool.noConfusion hCheck
          | true =>
              rw [hRat] at hCheck
              cases hAdded : cpcClauseHolds assignment (pivotLiteral :: restLiterals) with
              | true =>
                  exact cpcProofStepsSound remainingSteps
                    ((pivotLiteral :: restLiterals) :: workingFormula) assignment hCheck
                    (cpcAndIntro
                      (cpcClauseHolds assignment (pivotLiteral :: restLiterals))
                      (cpcFormulaHolds assignment workingFormula) hAdded hFormula)
              | false =>
                  have hPivotFalse : cpcLiteralHolds assignment pivotLiteral = false :=
                    (cpcOrFalseSplit (cpcLiteralHolds assignment pivotLiteral)
                      (cpcClauseHolds assignment restLiterals) hAdded).left
                  have hFlipFormula := cpcRatCandidatesSound assignment workingFormula
                    (pivotLiteral :: restLiterals) pivotLiteral ratHints hFormula hAdded
                    hPivotFalse workingFormula Nat.zero hRat hFormula
                  have hFlipClause : cpcClauseHolds (cpcFlipEnv pivotLiteral assignment)
                      (pivotLiteral :: restLiterals) = true :=
                    cpcOrIntroLeft
                      (cpcLiteralHolds (cpcFlipEnv pivotLiteral assignment) pivotLiteral)
                      (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment) restLiterals)
                      (cpcFlipEnvSatisfiesPivot assignment pivotLiteral)
                  exact cpcProofStepsSound remainingSteps
                    ((pivotLiteral :: restLiterals) :: workingFormula)
                    (cpcFlipEnv pivotLiteral assignment) hCheck
                    (cpcAndIntro
                      (cpcClauseHolds (cpcFlipEnv pivotLiteral assignment)
                        (pivotLiteral :: restLiterals))
                      (cpcFormulaHolds (cpcFlipEnv pivotLiteral assignment) workingFormula)
                      hFlipClause hFlipFormula)
  | CpcProofStep.deleteClause removedIndex :: remainingSteps, workingFormula, assignment,
      hCheck, hFormula =>
      cpcProofStepsSound remainingSteps (cpcRemoveClauseAt removedIndex workingFormula)
        assignment hCheck
        (cpcRemoveClauseAtPreservesHolds assignment removedIndex workingFormula hFormula)

/-- **THE THEOREM — proof-checker soundness**: an accepted trace certifies that the
original formula has NO satisfying assignment. -/
theorem cpcProofSound (formula : List CpcClause) (steps : List CpcProofStep)
    (hCheck : cpcCheckProof formula steps = true) :
    ∀ assignment : Nat → Bool, cpcFormulaHolds assignment formula = true → False :=
  fun assignment hFormula =>
    cpcProofStepsSound steps formula assignment hCheck hFormula

/-! ## Smoke tests — accepted traces and rejected malformed traces -/

/-- The positive literal of a variable. -/
def cpcPositiveLiteral (variableIndex : Nat) : CpcLiteral :=
  CpcLiteral.mk variableIndex true

/-- The negative literal of a variable. -/
def cpcNegativeLiteral (variableIndex : Nat) : CpcLiteral :=
  CpcLiteral.mk variableIndex false

/-- UNSAT smoke: `(x0) ∧ (¬x0 ∨ x1) ∧ (¬x1)`. -/
def cpcSmokeUnitChainFormula : List CpcClause :=
  [[cpcPositiveLiteral 0],
   [cpcNegativeLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 1]]

/-- Two-step RUP trace for the unit chain: derive `(x1)`, then the empty clause. -/
def cpcSmokeUnitChainTrace : List CpcProofStep :=
  [CpcProofStep.addClause [cpcPositiveLiteral 1] [0, 1],
   CpcProofStep.addClause [] [3, 0]]

#eval cpcCheckProof cpcSmokeUnitChainFormula cpcSmokeUnitChainTrace
-- expected: true

#eval cpcCheckProof cpcSmokeUnitChainFormula
  [CpcProofStep.addClause [cpcPositiveLiteral 1] [0, 99],
   CpcProofStep.addClause [] [3, 0]]
-- expected: false (FALSE case — hint index 99 is out of range: invalid proof step rejected)

/-- Satisfiable smoke: `(x0 ∨ x1)`. -/
def cpcSmokeSatisfiableFormula : List CpcClause :=
  [[cpcPositiveLiteral 0, cpcPositiveLiteral 1]]

#eval cpcCheckProof cpcSmokeSatisfiableFormula
  [CpcProofStep.addClause [cpcPositiveLiteral 0] [0]]
-- expected: false (FALSE case — bogus RUP claim on a non-implied clause rejected:
-- the walk ends unit, never in conflict)

/-- Satisfiable chain smoke: `(x0) ∧ (¬x0 ∨ x1)`. -/
def cpcSmokeChainSatisfiableFormula : List CpcClause :=
  [[cpcPositiveLiteral 0],
   [cpcNegativeLiteral 0, cpcPositiveLiteral 1]]

#eval cpcCheckProof cpcSmokeChainSatisfiableFormula
  [CpcProofStep.addClause [cpcPositiveLiteral 1] [0, 1]]
-- expected: false (FALSE case — a genuine RUP lemma but NO empty clause: truncated
-- trace rejected)

/-- The classic four-clause UNSAT square on two variables. -/
def cpcSmokeFourClauseFormula : List CpcClause :=
  [[cpcPositiveLiteral 0, cpcPositiveLiteral 1],
   [cpcPositiveLiteral 0, cpcNegativeLiteral 1],
   [cpcNegativeLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 0, cpcNegativeLiteral 1]]

/-- Trace with a mid-trace deletion: derive `(x0)`, delete a spent clause, finish. -/
def cpcSmokeFourClauseTrace : List CpcProofStep :=
  [CpcProofStep.addClause [cpcPositiveLiteral 0] [0, 1],
   CpcProofStep.deleteClause 1,
   CpcProofStep.addClause [] [0, 2, 3]]

#eval cpcCheckProof cpcSmokeFourClauseFormula cpcSmokeFourClauseTrace
-- expected: true (deletion mid-trace exercised)

/-- RAT smoke: `(x0 ∨ x1) ∧ (¬x0 ∨ x1) ∧ (¬x1)` — `(x0)` is RAT on pivot `x0`
(single resolution candidate at position 1). -/
def cpcSmokeRatFormula : List CpcClause :=
  [[cpcPositiveLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 1]]

/-- RAT trace: add `(x0)` by RAT, then the empty clause by RUP. -/
def cpcSmokeRatTrace : List CpcProofStep :=
  [CpcProofStep.addRatClause [cpcPositiveLiteral 0] [CpcRatHintGroup.mk 1 [0]],
   CpcProofStep.addClause [] [0, 2, 3]]

#eval cpcCheckProof cpcSmokeRatFormula cpcSmokeRatTrace
-- expected: true (RAT step + finishing RUP)

/-- RAT coverage-hole smoke: TWO resolution candidates but hints for only one. -/
def cpcSmokeRatMissingCandidateFormula : List CpcClause :=
  [[cpcPositiveLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 0, cpcPositiveLiteral 1],
   [cpcNegativeLiteral 0, cpcNegativeLiteral 1]]

#eval cpcCheckProof cpcSmokeRatMissingCandidateFormula
  [CpcProofStep.addRatClause [cpcPositiveLiteral 0] [CpcRatHintGroup.mk 1 [0]],
   CpcProofStep.addClause [] [0, 1, 2]]
-- expected: false (FALSE case — the position-2 candidate has no hint group: the
-- whole-formula coverage walk rejects the bogus RAT claim)

#eval cpcCheckProof cpcSmokeRatFormula [CpcProofStep.addRatClause [] []]
-- expected: false (FALSE case — the empty clause has no pivot: RAT addition rejected)

#eval cpcCheckProof cpcSmokeSatisfiableFormula []
-- expected: false (FALSE case — the empty trace proves nothing)

/-! ## Markers -/

/-- The hinted-RUP clause-proof checker with deletion, the empty-clause verdict, and full soundness
(`cpcProofSound`). -/
def fxDissatResidue_hasRupChecker : Bool := true

/-- The RAT extension: whole-formula candidate coverage plus the constructive pivot-flip
model-modification soundness (`cpcRatCandidatesSound`), folded into the same headline theorem. -/
def fxDissatResidue_hasRatExtension : Bool := true

/-- The CDCL proof finder is out of scope by architecture: search stays untrusted (any external SAT
solver emitting LRAT-style traces), and only the checker above is kernel business. -/
def fxDissatResidue_hasCdclFinder : Bool := false

end FX1Poly.ComputerAlgebra
