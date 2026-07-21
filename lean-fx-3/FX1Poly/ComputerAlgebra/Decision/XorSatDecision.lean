set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/Decision/XorSatDecision — XOR-SAT decided with two-sided certificates

Systems of F2-linear equations (XOR-SAT), decided constructively and certificate-first.
An equation is `XorSatEquation` — a strictly-ascending `variables : List Nat` support plus a
`parity : Bool` right-hand side; a system is `List XorSatEquation`.  Under an environment
`env : Nat → Bool` an equation holds when the xor-fold of `env` over its support equals its
parity (`xorSatEvalEquation`); environments are only ever applied, never `funext`ed.

## The toggle-merge crux

`xorSatToggleMerge` is the symmetric difference of two strictly-ascending variable lists,
factored as a fold of the single-element toggle `xorSatToggleOne` (insert if absent, cancel
if present — the F2 `x + x = 0`).  Its kit carries, over the `xorSatIsStrictlyAscending`
invariant:

  * preservation of strict ascent (`xorSatToggleMergePreservesAscending`);
  * the evaluation lemma `xorSatXorFoldToggleMerge` — the xor-fold of an environment over the
    toggle-merge is the `Bool` xor of the two xor-folds (structural induction through
    `xorSatXorFoldToggleOne`; unconditional, needing no ascent hypothesis);
  * the full F2 vector-space algebra: commutativity, associativity, self-cancellation
    (`xorSatToggleMergeComm` / `...Assoc` / `...SelfNil` / `...SelfCancel`), each built from
    the single-toggle commutation `xorSatToggleOneComm`, so every commutation step rides the
    strict-ascent invariant that keeps the cancellation exact;
  * the membership homomorphism `xorSatHasMemberToggleMerge` — membership in the symmetric
    difference is the xor of memberships, which is what makes pivot elimination remove a
    variable.

`xorSatCombine` xors two equations (toggle-merged supports, xored parities);
`xorSatEvalCombine`: any environment satisfying both satisfies the combination.

## Provenance and the decision

`xorSatDecide` eliminates by structural fuel over working items `XorSatWorkItem` — an
equation paired with `comboIndices`, the F2 index-combination of original equations it
equals (`xorSatWorkHasProvenance`; combos live in the same toggle-merge algebra, and the
provenance step is the fold homomorphism `xorSatSelectXorToggleMerge`:
`selectXor (merge c1 c2) = combine (selectXor c1) (selectXor c2)`).  Each round inspects the
head equation: empty support with even parity is dropped; empty support with odd parity is
UNSAT, with the head's combo as certificate; otherwise pivot on its least variable (the head
of the ascending support), combine into every tail equation containing the pivot
(`xorSatPivotTransform`), recurse, and on a satisfiable answer back-substitute the pivot
value forced by the head equation (`xorSatExtendWitness`, exact by construction —
`xorSatEnvExtendAtPivot` / `...AtOther`).

## Fuel adequacy

Each round recurses on a working list exactly one item shorter
(`xorSatPivotTransformCount`), so fuel = the working count reaches a verdict:
`xorSatDecideAuxIsSome`, specialized to `xorSatDecideTotalFuelAdequate` — the totality
certificate for `xorSatDecide`.

## The two headline theorems

  * SAT side — `xorSatDecideSatSound`: a returned witness passes the executable checker
    `xorSatCheckSystem`; `xorSatCheckSystemHoldsEachEquation`: a passing checker means every
    equation (by index, out-of-range reading as the zero equation) holds under the induced
    environment `xorSatEnvOfWitness`.
  * UNSAT side — `xorSatDecideUnsatSound`: the returned `comboIndices` select original
    equations whose F2 xor is literally the contradiction `⟨[], true⟩`
    (`xorSatSelectXor comboIndices system = xorSatContradictionEquation`); with the
    selection lemma `xorSatSelectXorSatisfied` (any model of the system satisfies the xor of
    any index selection) this refutes every candidate model, and `xorSatDecideUnsatRefutes`
    lands `False` by `Bool.noConfusion`.

## Zero-axiom

Structural recursion/induction only (on `Nat`, `List`, `Bool`, `Ordering`, `Option`, and the
verdict/equation shapes); every case split is a constructor `cases` plus `rw`; match-branch
reduction goes through explicit `show`-then-`rw` equation lemmas.  Nat facts used:
`Nat.add_zero`/`Nat.zero_add` and the hand-rolled `xorSatNatSuccAdd`; everything else —
comparator, xor, membership, and-elimination — is local.  No `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`,
`Nat.sub`/`Nat.mod`/`Nat.div`, `List.append`, wildcard match arms.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/XorSatDecision.lean`.  Marker:
`fxDissatIsland_hasXorSatDecision := true`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The structural three-way comparator on `Nat` -/

/-- Structural three-way comparison on `Nat` (no `Nat.ble`/`Nat.lt` library surface). -/
def xorSatCompareNat : Nat → Nat → Ordering
  | 0, 0 => Ordering.eq
  | 0, Nat.succ _secondInner => Ordering.lt
  | Nat.succ _firstInner, 0 => Ordering.gt
  | Nat.succ firstInner, Nat.succ secondInner => xorSatCompareNat firstInner secondInner

/-- The comparator is reflexively `eq`. -/
theorem xorSatCompareNatRefl : (value : Nat) → xorSatCompareNat value value = Ordering.eq
  | 0 => rfl
  | Nat.succ inner => xorSatCompareNatRefl inner

/-- An `eq` verdict pins the two numbers equal. -/
theorem xorSatCompareNatEqImpliesEq : (first second : Nat) →
    xorSatCompareNat first second = Ordering.eq → first = second
  | 0, 0, _heq => rfl
  | 0, Nat.succ _secondInner, hcontr => Ordering.noConfusion hcontr
  | Nat.succ _firstInner, 0, hcontr => Ordering.noConfusion hcontr
  | Nat.succ firstInner, Nat.succ secondInner, heq =>
      congrArg Nat.succ (xorSatCompareNatEqImpliesEq firstInner secondInner heq)

/-- Swapping the operands flips `lt` to `gt`. -/
theorem xorSatCompareNatLtFlips : (first second : Nat) →
    xorSatCompareNat first second = Ordering.lt → xorSatCompareNat second first = Ordering.gt
  | 0, 0, hcontr => Ordering.noConfusion hcontr
  | 0, Nat.succ _secondInner, _hlt => rfl
  | Nat.succ _firstInner, 0, hcontr => Ordering.noConfusion hcontr
  | Nat.succ firstInner, Nat.succ secondInner, hlt =>
      xorSatCompareNatLtFlips firstInner secondInner hlt

/-- Swapping the operands flips `gt` to `lt`. -/
theorem xorSatCompareNatGtFlips : (first second : Nat) →
    xorSatCompareNat first second = Ordering.gt → xorSatCompareNat second first = Ordering.lt
  | 0, 0, hcontr => Ordering.noConfusion hcontr
  | 0, Nat.succ _secondInner, hcontr => Ordering.noConfusion hcontr
  | Nat.succ _firstInner, 0, _hgt => rfl
  | Nat.succ firstInner, Nat.succ secondInner, hgt =>
      xorSatCompareNatGtFlips firstInner secondInner hgt

/-- Transitivity of the strict `lt` verdict. -/
theorem xorSatCompareNatLtTrans : (first second third : Nat) →
    xorSatCompareNat first second = Ordering.lt →
    xorSatCompareNat second third = Ordering.lt →
    xorSatCompareNat first third = Ordering.lt
  | 0, 0, _anyThird, hcontr, _hst => Ordering.noConfusion hcontr
  | 0, Nat.succ _secondInner, 0, _hfs, hcontr => Ordering.noConfusion hcontr
  | 0, Nat.succ _secondInner, Nat.succ _thirdInner, _hfs, _hst => rfl
  | Nat.succ _firstInner, 0, _anyThird, hcontr, _hst => Ordering.noConfusion hcontr
  | Nat.succ _firstInner, Nat.succ _secondInner, 0, _hfs, hcontr => Ordering.noConfusion hcontr
  | Nat.succ firstInner, Nat.succ secondInner, Nat.succ thirdInner, hfs, hst =>
      xorSatCompareNatLtTrans firstInner secondInner thirdInner hfs hst

/-- Boolean equality on `Nat` derived from the comparator. -/
def xorSatNatEqb (first second : Nat) : Bool :=
  match xorSatCompareNat first second with
  | Ordering.lt => false
  | Ordering.eq => true
  | Ordering.gt => false

/-- `xorSatNatEqb` is reflexive. -/
theorem xorSatNatEqbRefl (value : Nat) : xorSatNatEqb value value = true := by
  show (match xorSatCompareNat value value with
        | Ordering.lt => false
        | Ordering.eq => true
        | Ordering.gt => false) = true
  rw [xorSatCompareNatRefl]

/-- A true `xorSatNatEqb` pins the two numbers equal. -/
theorem xorSatNatEqbImpliesEq (first second : Nat)
    (heqb : xorSatNatEqb first second = true) : first = second := by
  cases hcomp : xorSatCompareNat first second with
  | lt =>
      exact absurd heqb (by
        show (match xorSatCompareNat first second with
              | Ordering.lt => false
              | Ordering.eq => true
              | Ordering.gt => false) ≠ true
        rw [hcomp]; exact fun hcontr => Bool.noConfusion hcontr)
  | eq => exact xorSatCompareNatEqImpliesEq first second hcomp
  | gt =>
      exact absurd heqb (by
        show (match xorSatCompareNat first second with
              | Ordering.lt => false
              | Ordering.eq => true
              | Ordering.gt => false) ≠ true
        rw [hcomp]; exact fun hcontr => Bool.noConfusion hcontr)

/-- An `lt` comparison refutes `xorSatNatEqb`. -/
theorem xorSatNatEqbOfLt (first second : Nat)
    (hlt : xorSatCompareNat first second = Ordering.lt) : xorSatNatEqb first second = false := by
  show (match xorSatCompareNat first second with
        | Ordering.lt => false
        | Ordering.eq => true
        | Ordering.gt => false) = false
  rw [hlt]

/-- A `gt` comparison refutes `xorSatNatEqb`. -/
theorem xorSatNatEqbOfGt (first second : Nat)
    (hgt : xorSatCompareNat first second = Ordering.gt) : xorSatNatEqb first second = false := by
  show (match xorSatCompareNat first second with
        | Ordering.lt => false
        | Ordering.eq => true
        | Ordering.gt => false) = false
  rw [hgt]

/-- A false `xorSatNatEqb` is symmetric. -/
theorem xorSatNatEqbFlipsFalse (first second : Nat)
    (hne : xorSatNatEqb first second = false) : xorSatNatEqb second first = false := by
  cases hcomp : xorSatCompareNat first second with
  | lt => exact xorSatNatEqbOfGt second first (xorSatCompareNatLtFlips first second hcomp)
  | eq =>
      exact absurd hne (by
        show (match xorSatCompareNat first second with
              | Ordering.lt => false
              | Ordering.eq => true
              | Ordering.gt => false) ≠ false
        rw [hcomp]; exact fun hcontr => Bool.noConfusion hcontr)
  | gt => exact xorSatNatEqbOfLt second first (xorSatCompareNatGtFlips first second hcomp)

/-- `succ first + second = succ (first + second)` — the propext-clean successor shift. -/
theorem xorSatNatSuccAdd : (first second : Nat) →
    Nat.succ first + second = Nat.succ (first + second)
  | _first, 0 => rfl
  | first, Nat.succ second => congrArg Nat.succ (xorSatNatSuccAdd first second)

/-! ## The `Bool` xor / eq / and kit (finite case analysis only) -/

/-- F2 addition on `Bool`: exclusive or. -/
def xorSatBoolXor : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

theorem xorSatBoolXorComm (leftFlag rightFlag : Bool) :
    xorSatBoolXor leftFlag rightFlag = xorSatBoolXor rightFlag leftFlag := by
  cases leftFlag <;> cases rightFlag <;> rfl

theorem xorSatBoolXorAssoc (leftFlag middleFlag rightFlag : Bool) :
    xorSatBoolXor (xorSatBoolXor leftFlag middleFlag) rightFlag
      = xorSatBoolXor leftFlag (xorSatBoolXor middleFlag rightFlag) := by
  cases leftFlag <;> cases middleFlag <;> cases rightFlag <;> rfl

theorem xorSatBoolXorFalseLeft (flag : Bool) : xorSatBoolXor false flag = flag := by
  cases flag <;> rfl

theorem xorSatBoolXorFalseRight (flag : Bool) : xorSatBoolXor flag false = flag := by
  cases flag <;> rfl

theorem xorSatBoolXorSelfFalse (flag : Bool) : xorSatBoolXor flag flag = false := by
  cases flag <;> rfl

theorem xorSatBoolXorLeftSwap (leftFlag middleFlag rightFlag : Bool) :
    xorSatBoolXor leftFlag (xorSatBoolXor middleFlag rightFlag)
      = xorSatBoolXor middleFlag (xorSatBoolXor leftFlag rightFlag) := by
  cases leftFlag <;> cases middleFlag <;> cases rightFlag <;> rfl

theorem xorSatBoolXorCancelLeft (leftFlag rightFlag : Bool) :
    xorSatBoolXor leftFlag (xorSatBoolXor leftFlag rightFlag) = rightFlag := by
  cases leftFlag <;> cases rightFlag <;> rfl

/-- Boolean equality test on `Bool`. -/
def xorSatBoolEq : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

theorem xorSatBoolEqRefl (flag : Bool) : xorSatBoolEq flag flag = true := by
  cases flag <;> rfl

theorem xorSatBoolEqImpliesEq : (leftFlag rightFlag : Bool) →
    xorSatBoolEq leftFlag rightFlag = true → leftFlag = rightFlag
  | false, false, _htrue => rfl
  | false, true, hcontr => Bool.noConfusion hcontr
  | true, false, hcontr => Bool.noConfusion hcontr
  | true, true, _htrue => rfl

theorem xorSatAndElimLeft : (leftFlag rightFlag : Bool) →
    (leftFlag && rightFlag) = true → leftFlag = true
  | true, _rightFlag, _htrue => rfl
  | false, _rightFlag, hcontr => Bool.noConfusion hcontr

theorem xorSatAndElimRight : (leftFlag rightFlag : Bool) →
    (leftFlag && rightFlag) = true → rightFlag = true
  | true, _rightFlag, htrue => htrue
  | false, _rightFlag, hcontr => Bool.noConfusion hcontr

theorem xorSatAndIntro : (leftFlag rightFlag : Bool) →
    leftFlag = true → rightFlag = true → (leftFlag && rightFlag) = true
  | true, true, _hleft, _hright => rfl
  | true, false, _hleft, hcontr => Bool.noConfusion hcontr
  | false, _rightFlag, hcontr, _hright => Bool.noConfusion hcontr

/-! ## Strictly-ascending variable lists -/

/-- Does `bound` sit strictly below the head of the list (vacuously true on `[]`)? -/
def xorSatIsBelowHead (bound : Nat) : List Nat → Bool
  | [] => true
  | head :: _restVars =>
      match xorSatCompareNat bound head with
      | Ordering.lt => true
      | Ordering.eq => false
      | Ordering.gt => false

/-- Is the variable list strictly ascending (sorted, duplicate-free)? -/
def xorSatIsStrictlyAscending : List Nat → Bool
  | [] => true
  | head :: restVars => xorSatIsBelowHead head restVars && xorSatIsStrictlyAscending restVars

theorem xorSatIsBelowHeadConsIntro (bound head : Nat) (restVars : List Nat)
    (hlt : xorSatCompareNat bound head = Ordering.lt) :
    xorSatIsBelowHead bound (head :: restVars) = true := by
  show (match xorSatCompareNat bound head with
        | Ordering.lt => true
        | Ordering.eq => false
        | Ordering.gt => false) = true
  rw [hlt]

theorem xorSatIsBelowHeadConsInversion (bound head : Nat) (restVars : List Nat)
    (hbelow : xorSatIsBelowHead bound (head :: restVars) = true) :
    xorSatCompareNat bound head = Ordering.lt := by
  cases hcomp : xorSatCompareNat bound head with
  | lt => rfl
  | eq =>
      exact absurd hbelow (by
        show (match xorSatCompareNat bound head with
              | Ordering.lt => true
              | Ordering.eq => false
              | Ordering.gt => false) ≠ true
        rw [hcomp]; exact fun hcontr => Bool.noConfusion hcontr)
  | gt =>
      exact absurd hbelow (by
        show (match xorSatCompareNat bound head with
              | Ordering.lt => true
              | Ordering.eq => false
              | Ordering.gt => false) ≠ true
        rw [hcomp]; exact fun hcontr => Bool.noConfusion hcontr)

/-- Anything strictly below a list's lower bound is itself a lower bound. -/
theorem xorSatIsBelowHeadOfLess (bound lower : Nat) (restVars : List Nat)
    (hlt : xorSatCompareNat bound lower = Ordering.lt)
    (hbelow : xorSatIsBelowHead lower restVars = true) :
    xorSatIsBelowHead bound restVars = true := by
  cases restVars with
  | nil => rfl
  | cons head tailVars =>
      exact xorSatIsBelowHeadConsIntro bound head tailVars
        (xorSatCompareNatLtTrans bound lower head hlt
          (xorSatIsBelowHeadConsInversion lower head tailVars hbelow))

/-- Boolean membership scan over a variable list. -/
def xorSatHasMember (target : Nat) : List Nat → Bool
  | [] => false
  | head :: restVars =>
      match xorSatCompareNat target head with
      | Ordering.lt => xorSatHasMember target restVars
      | Ordering.eq => true
      | Ordering.gt => xorSatHasMember target restVars

theorem xorSatHasMemberConsOfEq (target head : Nat) (restVars : List Nat)
    (heq : xorSatCompareNat target head = Ordering.eq) :
    xorSatHasMember target (head :: restVars) = true := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => xorSatHasMember target restVars
        | Ordering.eq => true
        | Ordering.gt => xorSatHasMember target restVars) = true
  rw [heq]

theorem xorSatHasMemberConsOfLt (target head : Nat) (restVars : List Nat)
    (hlt : xorSatCompareNat target head = Ordering.lt) :
    xorSatHasMember target (head :: restVars) = xorSatHasMember target restVars := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => xorSatHasMember target restVars
        | Ordering.eq => true
        | Ordering.gt => xorSatHasMember target restVars) = xorSatHasMember target restVars
  rw [hlt]

theorem xorSatHasMemberConsOfGt (target head : Nat) (restVars : List Nat)
    (hgt : xorSatCompareNat target head = Ordering.gt) :
    xorSatHasMember target (head :: restVars) = xorSatHasMember target restVars := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => xorSatHasMember target restVars
        | Ordering.eq => true
        | Ordering.gt => xorSatHasMember target restVars) = xorSatHasMember target restVars
  rw [hgt]

/-- A strict lower bound of a strictly-ascending list is never a member. -/
theorem xorSatHasMemberNotBelow : (target : Nat) → (vars : List Nat) →
    xorSatIsBelowHead target vars = true →
    xorSatIsStrictlyAscending vars = true →
    xorSatHasMember target vars = false
  | _target, [], _hbelow, _hasc => rfl
  | target, head :: restVars, hbelow, hasc => by
      have hlt : xorSatCompareNat target head = Ordering.lt :=
        xorSatIsBelowHeadConsInversion target head restVars hbelow
      rw [xorSatHasMemberConsOfLt target head restVars hlt]
      exact xorSatHasMemberNotBelow target restVars
        (xorSatIsBelowHeadOfLess target head restVars hlt (xorSatAndElimLeft _ _ hasc))
        (xorSatAndElimRight _ _ hasc)

/-! ## The single-element toggle (F2 insert-or-cancel) -/

/-- Toggle one variable in a strictly-ascending list: insert it if absent, cancel it if
present — the F2 `x + x = 0` at the single-variable level. -/
def xorSatToggleOne (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: restVars =>
      match xorSatCompareNat value head with
      | Ordering.lt => value :: head :: restVars
      | Ordering.eq => restVars
      | Ordering.gt => head :: xorSatToggleOne value restVars

theorem xorSatToggleOneNil (value : Nat) : xorSatToggleOne value [] = [value] := rfl

theorem xorSatToggleOneLt (value head : Nat) (restVars : List Nat)
    (hlt : xorSatCompareNat value head = Ordering.lt) :
    xorSatToggleOne value (head :: restVars) = value :: head :: restVars := by
  show (match xorSatCompareNat value head with
        | Ordering.lt => value :: head :: restVars
        | Ordering.eq => restVars
        | Ordering.gt => head :: xorSatToggleOne value restVars) = value :: head :: restVars
  rw [hlt]

theorem xorSatToggleOneEq (value head : Nat) (restVars : List Nat)
    (heq : xorSatCompareNat value head = Ordering.eq) :
    xorSatToggleOne value (head :: restVars) = restVars := by
  show (match xorSatCompareNat value head with
        | Ordering.lt => value :: head :: restVars
        | Ordering.eq => restVars
        | Ordering.gt => head :: xorSatToggleOne value restVars) = restVars
  rw [heq]

theorem xorSatToggleOneGt (value head : Nat) (restVars : List Nat)
    (hgt : xorSatCompareNat value head = Ordering.gt) :
    xorSatToggleOne value (head :: restVars) = head :: xorSatToggleOne value restVars := by
  show (match xorSatCompareNat value head with
        | Ordering.lt => value :: head :: restVars
        | Ordering.eq => restVars
        | Ordering.gt => head :: xorSatToggleOne value restVars)
      = head :: xorSatToggleOne value restVars
  rw [hgt]

/-- Toggling a strict lower bound prepends it. -/
theorem xorSatToggleOneFront (value : Nat) (vars : List Nat)
    (hbelow : xorSatIsBelowHead value vars = true) :
    xorSatToggleOne value vars = value :: vars := by
  cases vars with
  | nil => rfl
  | cons head restVars =>
      exact xorSatToggleOneLt value head restVars
        (xorSatIsBelowHeadConsInversion value head restVars hbelow)

/-- A strict lower bound below the toggled value stays a lower bound after the toggle. -/
theorem xorSatIsBelowHeadToggleOne (bound value : Nat) : (vars : List Nat) →
    xorSatCompareNat bound value = Ordering.lt →
    xorSatIsBelowHead bound vars = true →
    xorSatIsStrictlyAscending vars = true →
    xorSatIsBelowHead bound (xorSatToggleOne value vars) = true
  | [], hlt, _hbelow, _hasc => by
      rw [xorSatToggleOneNil]
      exact xorSatIsBelowHeadConsIntro bound value [] hlt
  | head :: restVars, hlt, hbelow, hasc => by
      have hboundHead : xorSatCompareNat bound head = Ordering.lt :=
        xorSatIsBelowHeadConsInversion bound head restVars hbelow
      cases hvh : xorSatCompareNat value head with
      | lt =>
          rw [xorSatToggleOneLt value head restVars hvh]
          exact xorSatIsBelowHeadConsIntro bound value (head :: restVars) hlt
      | eq =>
          rw [xorSatToggleOneEq value head restVars hvh]
          exact xorSatIsBelowHeadOfLess bound head restVars hboundHead
            (xorSatAndElimLeft _ _ hasc)
      | gt =>
          rw [xorSatToggleOneGt value head restVars hvh]
          exact xorSatIsBelowHeadConsIntro bound head (xorSatToggleOne value restVars) hboundHead

/-- Toggling preserves strict ascent. -/
theorem xorSatToggleOnePreservesAscending (value : Nat) : (vars : List Nat) →
    xorSatIsStrictlyAscending vars = true →
    xorSatIsStrictlyAscending (xorSatToggleOne value vars) = true
  | [], _hasc => rfl
  | head :: restVars, hasc => by
      have hbelow : xorSatIsBelowHead head restVars = true := xorSatAndElimLeft _ _ hasc
      have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
      cases hvh : xorSatCompareNat value head with
      | lt =>
          rw [xorSatToggleOneLt value head restVars hvh]
          exact xorSatAndIntro _ _ (xorSatIsBelowHeadConsIntro value head restVars hvh) hasc
      | eq =>
          rw [xorSatToggleOneEq value head restVars hvh]
          exact hrest
      | gt =>
          rw [xorSatToggleOneGt value head restVars hvh]
          exact xorSatAndIntro _ _
            (xorSatIsBelowHeadToggleOne head value restVars
              (xorSatCompareNatGtFlips value head hvh) hbelow hrest)
            (xorSatToggleOnePreservesAscending value restVars hrest)

/-- Two single-element toggles commute over a strictly-ascending list. -/
theorem xorSatToggleOneComm (firstValue secondValue : Nat) : (vars : List Nat) →
    xorSatIsStrictlyAscending vars = true →
    xorSatToggleOne firstValue (xorSatToggleOne secondValue vars)
      = xorSatToggleOne secondValue (xorSatToggleOne firstValue vars)
  | [], _hasc => by
      rw [xorSatToggleOneNil, xorSatToggleOneNil]
      cases hfs : xorSatCompareNat firstValue secondValue with
      | lt =>
          rw [xorSatToggleOneLt firstValue secondValue [] hfs,
              xorSatToggleOneGt secondValue firstValue []
                (xorSatCompareNatLtFlips firstValue secondValue hfs),
              xorSatToggleOneNil]
      | eq =>
          rw [xorSatCompareNatEqImpliesEq firstValue secondValue hfs]
      | gt =>
          rw [xorSatToggleOneGt firstValue secondValue [] hfs,
              xorSatToggleOneNil,
              xorSatToggleOneLt secondValue firstValue []
                (xorSatCompareNatGtFlips firstValue secondValue hfs)]
  | head :: restVars, hasc => by
      have hbelow : xorSatIsBelowHead head restVars = true := xorSatAndElimLeft _ _ hasc
      have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
      cases hfh : xorSatCompareNat firstValue head with
      | lt =>
          cases hsh : xorSatCompareNat secondValue head with
          | lt =>
              rw [xorSatToggleOneLt secondValue head restVars hsh,
                  xorSatToggleOneLt firstValue head restVars hfh]
              cases hfs : xorSatCompareNat firstValue secondValue with
              | lt =>
                  rw [xorSatToggleOneLt firstValue secondValue (head :: restVars) hfs,
                      xorSatToggleOneGt secondValue firstValue (head :: restVars)
                        (xorSatCompareNatLtFlips firstValue secondValue hfs),
                      xorSatToggleOneLt secondValue head restVars hsh]
              | eq =>
                  have hfeqs : firstValue = secondValue :=
                    xorSatCompareNatEqImpliesEq firstValue secondValue hfs
                  rw [xorSatToggleOneEq firstValue secondValue (head :: restVars) hfs, hfeqs,
                      xorSatToggleOneEq secondValue secondValue (head :: restVars)
                        (xorSatCompareNatRefl secondValue)]
              | gt =>
                  rw [xorSatToggleOneGt firstValue secondValue (head :: restVars) hfs,
                      xorSatToggleOneLt firstValue head restVars hfh,
                      xorSatToggleOneLt secondValue firstValue (head :: restVars)
                        (xorSatCompareNatGtFlips firstValue secondValue hfs)]
          | eq =>
              have hseqh : secondValue = head :=
                xorSatCompareNatEqImpliesEq secondValue head hsh
              have hfsLt : xorSatCompareNat firstValue secondValue = Ordering.lt := by
                rw [hseqh]; exact hfh
              rw [xorSatToggleOneEq secondValue head restVars hsh,
                  xorSatToggleOneLt firstValue head restVars hfh,
                  xorSatToggleOneGt secondValue firstValue (head :: restVars)
                    (xorSatCompareNatLtFlips firstValue secondValue hfsLt),
                  xorSatToggleOneEq secondValue head restVars hsh,
                  xorSatToggleOneFront firstValue restVars
                    (xorSatIsBelowHeadOfLess firstValue head restVars hfh hbelow)]
          | gt =>
              rw [xorSatToggleOneGt secondValue head restVars hsh,
                  xorSatToggleOneLt firstValue (head := head)
                    (restVars := xorSatToggleOne secondValue restVars) hfh,
                  xorSatToggleOneLt firstValue head restVars hfh,
                  xorSatToggleOneGt secondValue firstValue (head :: restVars)
                    (xorSatCompareNatLtFlips firstValue secondValue
                      (xorSatCompareNatLtTrans firstValue head secondValue hfh
                        (xorSatCompareNatGtFlips secondValue head hsh))),
                  xorSatToggleOneGt secondValue head restVars hsh]
      | eq =>
          have hfeqh : firstValue = head :=
            xorSatCompareNatEqImpliesEq firstValue head hfh
          cases hsh : xorSatCompareNat secondValue head with
          | lt =>
              rw [xorSatToggleOneLt secondValue head restVars hsh,
                  xorSatToggleOneGt firstValue secondValue (head :: restVars)
                    (xorSatCompareNatLtFlips secondValue firstValue
                      (by rw [hfeqh]; exact hsh)),
                  xorSatToggleOneEq firstValue head restVars hfh,
                  xorSatToggleOneFront secondValue restVars
                    (xorSatIsBelowHeadOfLess secondValue head restVars hsh hbelow)]
          | eq =>
              rw [xorSatCompareNatEqImpliesEq firstValue head hfh,
                  xorSatCompareNatEqImpliesEq secondValue head hsh]
          | gt =>
              rw [xorSatToggleOneGt secondValue head restVars hsh,
                  xorSatToggleOneEq firstValue (head := head)
                    (restVars := xorSatToggleOne secondValue restVars) hfh,
                  xorSatToggleOneEq firstValue head restVars hfh]
      | gt =>
          cases hsh : xorSatCompareNat secondValue head with
          | lt =>
              rw [xorSatToggleOneLt secondValue head restVars hsh,
                  xorSatToggleOneGt firstValue secondValue (head :: restVars)
                    (xorSatCompareNatLtFlips secondValue firstValue
                      (xorSatCompareNatLtTrans secondValue head firstValue hsh
                        (xorSatCompareNatGtFlips firstValue head hfh))),
                  xorSatToggleOneGt firstValue head restVars hfh,
                  xorSatToggleOneLt secondValue (head := head)
                    (restVars := xorSatToggleOne firstValue restVars) hsh]
          | eq =>
              rw [xorSatToggleOneEq secondValue head restVars hsh,
                  xorSatToggleOneGt firstValue head restVars hfh,
                  xorSatToggleOneEq secondValue (head := head)
                    (restVars := xorSatToggleOne firstValue restVars) hsh]
          | gt =>
              rw [xorSatToggleOneGt secondValue head restVars hsh,
                  xorSatToggleOneGt firstValue (head := head)
                    (restVars := xorSatToggleOne secondValue restVars) hfh,
                  xorSatToggleOneGt firstValue head restVars hfh,
                  xorSatToggleOneGt secondValue (head := head)
                    (restVars := xorSatToggleOne firstValue restVars) hsh,
                  xorSatToggleOneComm firstValue secondValue restVars hrest]

/-- Toggling the same variable twice is the identity on a strictly-ascending list. -/
theorem xorSatToggleOneSelfCancel (value : Nat) : (vars : List Nat) →
    xorSatIsStrictlyAscending vars = true →
    xorSatToggleOne value (xorSatToggleOne value vars) = vars
  | [], _hasc => by
      rw [xorSatToggleOneNil]
      exact xorSatToggleOneEq value value [] (xorSatCompareNatRefl value)
  | head :: restVars, hasc => by
      have hbelow : xorSatIsBelowHead head restVars = true := xorSatAndElimLeft _ _ hasc
      have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
      cases hvh : xorSatCompareNat value head with
      | lt =>
          rw [xorSatToggleOneLt value head restVars hvh,
              xorSatToggleOneEq value value (head :: restVars) (xorSatCompareNatRefl value)]
      | eq =>
          rw [xorSatToggleOneEq value head restVars hvh,
              xorSatCompareNatEqImpliesEq value head hvh,
              xorSatToggleOneFront head restVars hbelow]
      | gt =>
          rw [xorSatToggleOneGt value head restVars hvh,
              xorSatToggleOneGt value (head := head)
                (restVars := xorSatToggleOne value restVars) hvh,
              xorSatToggleOneSelfCancel value restVars hrest]

/-! ## The toggle-merge (symmetric difference) and its F2 algebra -/

/-- Symmetric difference of two strictly-ascending variable lists, as a fold of
single-element toggles of the first list into the second. -/
def xorSatToggleMerge : List Nat → List Nat → List Nat
  | [], second => second
  | firstHead :: firstRest, second =>
      xorSatToggleOne firstHead (xorSatToggleMerge firstRest second)

theorem xorSatToggleMergeNilLeft (second : List Nat) :
    xorSatToggleMerge [] second = second := rfl

theorem xorSatToggleMergeCons (firstHead : Nat) (firstRest second : List Nat) :
    xorSatToggleMerge (firstHead :: firstRest) second
      = xorSatToggleOne firstHead (xorSatToggleMerge firstRest second) := rfl

/-- The toggle-merge preserves strict ascent (of its second argument). -/
theorem xorSatToggleMergePreservesAscending : (first second : List Nat) →
    xorSatIsStrictlyAscending second = true →
    xorSatIsStrictlyAscending (xorSatToggleMerge first second) = true
  | [], _second, hsecond => hsecond
  | firstHead :: firstRest, second, hsecond =>
      xorSatToggleOnePreservesAscending firstHead (xorSatToggleMerge firstRest second)
        (xorSatToggleMergePreservesAscending firstRest second hsecond)

/-- Merging with the empty second list is the identity on strictly-ascending lists. -/
theorem xorSatToggleMergeNilRight : (first : List Nat) →
    xorSatIsStrictlyAscending first = true → xorSatToggleMerge first [] = first
  | [], _hasc => rfl
  | firstHead :: firstRest, hasc => by
      show xorSatToggleOne firstHead (xorSatToggleMerge firstRest []) = firstHead :: firstRest
      rw [xorSatToggleMergeNilRight firstRest (xorSatAndElimRight _ _ hasc)]
      exact xorSatToggleOneFront firstHead firstRest (xorSatAndElimLeft _ _ hasc)

/-- A toggle slides from outside a merge into its second argument. -/
theorem xorSatToggleOneMergeRight (value : Nat) : (first second : List Nat) →
    xorSatIsStrictlyAscending second = true →
    xorSatToggleOne value (xorSatToggleMerge first second)
      = xorSatToggleMerge first (xorSatToggleOne value second)
  | [], _second, _hsecond => rfl
  | firstHead :: firstRest, second, hsecond => by
      show xorSatToggleOne value (xorSatToggleOne firstHead (xorSatToggleMerge firstRest second))
        = xorSatToggleOne firstHead (xorSatToggleMerge firstRest (xorSatToggleOne value second))
      rw [xorSatToggleOneComm value firstHead (xorSatToggleMerge firstRest second)
            (xorSatToggleMergePreservesAscending firstRest second hsecond),
          xorSatToggleOneMergeRight value firstRest second hsecond]

/-- Merging a toggled first list equals toggling the merge. -/
theorem xorSatToggleMergeToggleOneLeft (value : Nat) : (first second : List Nat) →
    xorSatIsStrictlyAscending second = true →
    xorSatToggleMerge (xorSatToggleOne value first) second
      = xorSatToggleOne value (xorSatToggleMerge first second)
  | [], _second, _hsecond => rfl
  | firstHead :: firstRest, second, hsecond => by
      cases hvh : xorSatCompareNat value firstHead with
      | lt =>
          rw [xorSatToggleOneLt value firstHead firstRest hvh]
          rfl
      | eq =>
          rw [xorSatToggleOneEq value firstHead firstRest hvh,
              xorSatToggleMergeCons firstHead firstRest second,
              xorSatCompareNatEqImpliesEq value firstHead hvh,
              xorSatToggleOneSelfCancel firstHead (xorSatToggleMerge firstRest second)
                (xorSatToggleMergePreservesAscending firstRest second hsecond)]
      | gt =>
          rw [xorSatToggleOneGt value firstHead firstRest hvh,
              xorSatToggleMergeCons firstHead (xorSatToggleOne value firstRest) second,
              xorSatToggleMergeToggleOneLeft value firstRest second hsecond,
              xorSatToggleMergeCons firstHead firstRest second,
              xorSatToggleOneComm firstHead value (xorSatToggleMerge firstRest second)
                (xorSatToggleMergePreservesAscending firstRest second hsecond)]

/-- Associativity of the toggle-merge (strict ascent needed only on the third list). -/
theorem xorSatToggleMergeAssoc : (first second third : List Nat) →
    xorSatIsStrictlyAscending third = true →
    xorSatToggleMerge (xorSatToggleMerge first second) third
      = xorSatToggleMerge first (xorSatToggleMerge second third)
  | [], _second, _third, _hthird => rfl
  | firstHead :: firstRest, second, third, hthird => by
      show xorSatToggleMerge (xorSatToggleOne firstHead (xorSatToggleMerge firstRest second)) third
        = xorSatToggleOne firstHead (xorSatToggleMerge firstRest (xorSatToggleMerge second third))
      rw [xorSatToggleMergeToggleOneLeft firstHead (xorSatToggleMerge firstRest second) third
            hthird,
          xorSatToggleMergeAssoc firstRest second third hthird]

/-- The two merged-in lists commute over a common accumulator. -/
theorem xorSatToggleMergeSwap : (first second accum : List Nat) →
    xorSatIsStrictlyAscending accum = true →
    xorSatToggleMerge first (xorSatToggleMerge second accum)
      = xorSatToggleMerge second (xorSatToggleMerge first accum)
  | [], _second, _accum, _haccum => rfl
  | firstHead :: firstRest, second, accum, haccum => by
      show xorSatToggleOne firstHead (xorSatToggleMerge firstRest (xorSatToggleMerge second accum))
        = xorSatToggleMerge second (xorSatToggleOne firstHead (xorSatToggleMerge firstRest accum))
      rw [xorSatToggleMergeSwap firstRest second accum haccum,
          xorSatToggleOneMergeRight firstHead second (xorSatToggleMerge firstRest accum)
            (xorSatToggleMergePreservesAscending firstRest accum haccum)]

/-- Commutativity of the toggle-merge on strictly-ascending lists. -/
theorem xorSatToggleMergeComm (first second : List Nat)
    (hfirst : xorSatIsStrictlyAscending first = true)
    (hsecond : xorSatIsStrictlyAscending second = true) :
    xorSatToggleMerge first second = xorSatToggleMerge second first := by
  have hswap := xorSatToggleMergeSwap first second [] rfl
  rw [xorSatToggleMergeNilRight second hsecond, xorSatToggleMergeNilRight first hfirst] at hswap
  exact hswap

/-- The F2 self-inverse at the list level: a list toggle-merged with itself vanishes. -/
theorem xorSatToggleMergeSelfNil : (vars : List Nat) →
    xorSatIsStrictlyAscending vars = true → xorSatToggleMerge vars vars = []
  | [], _hasc => rfl
  | head :: restVars, hasc => by
      have hbelow : xorSatIsBelowHead head restVars = true := xorSatAndElimLeft _ _ hasc
      have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
      show xorSatToggleOne head (xorSatToggleMerge restVars (head :: restVars)) = []
      rw [← xorSatToggleOneFront head restVars hbelow,
          ← xorSatToggleOneMergeRight head restVars restVars hrest,
          xorSatToggleOneSelfCancel head (xorSatToggleMerge restVars restVars)
            (xorSatToggleMergePreservesAscending restVars restVars hrest),
          xorSatToggleMergeSelfNil restVars hrest]

/-- Toggle-merging the same list twice cancels. -/
theorem xorSatToggleMergeSelfCancel (first second : List Nat)
    (hfirst : xorSatIsStrictlyAscending first = true)
    (hsecond : xorSatIsStrictlyAscending second = true) :
    xorSatToggleMerge first (xorSatToggleMerge first second) = second := by
  rw [← xorSatToggleMergeAssoc first first second hsecond,
      xorSatToggleMergeSelfNil first hfirst]
  exact xorSatToggleMergeNilLeft second

/-! ## Membership through toggles: the xor homomorphism -/

/-- `xorSatNatEqb` from an `eq` comparison. -/
theorem xorSatNatEqbOfEqCompare (first second : Nat)
    (heq : xorSatCompareNat first second = Ordering.eq) : xorSatNatEqb first second = true := by
  show (match xorSatCompareNat first second with
        | Ordering.lt => false
        | Ordering.eq => true
        | Ordering.gt => false) = true
  rw [heq]

/-- Cons-level membership on a strictly-ascending list is an xor. -/
theorem xorSatHasMemberConsAscending (target head : Nat) (restVars : List Nat)
    (hasc : xorSatIsStrictlyAscending (head :: restVars) = true) :
    xorSatHasMember target (head :: restVars)
      = xorSatBoolXor (xorSatNatEqb target head) (xorSatHasMember target restVars) := by
  have hbelow : xorSatIsBelowHead head restVars = true := xorSatAndElimLeft _ _ hasc
  have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
  cases hcomp : xorSatCompareNat target head with
  | lt =>
      rw [xorSatHasMemberConsOfLt target head restVars hcomp,
          xorSatNatEqbOfLt target head hcomp, xorSatBoolXorFalseLeft]
  | eq =>
      have hteq : target = head := xorSatCompareNatEqImpliesEq target head hcomp
      rw [xorSatHasMemberConsOfEq target head restVars hcomp, hteq,
          xorSatNatEqbRefl head, xorSatHasMemberNotBelow head restVars hbelow hrest]
      rfl
  | gt =>
      rw [xorSatHasMemberConsOfGt target head restVars hcomp,
          xorSatNatEqbOfGt target head hcomp, xorSatBoolXorFalseLeft]

/-- Membership after a single toggle is an xor with the toggled variable. -/
theorem xorSatHasMemberToggleOne (target value : Nat) : (vars : List Nat) →
    xorSatIsStrictlyAscending vars = true →
    xorSatHasMember target (xorSatToggleOne value vars)
      = xorSatBoolXor (xorSatNatEqb target value) (xorSatHasMember target vars)
  | [], _hasc => by
      rw [xorSatToggleOneNil]
      cases hcomp : xorSatCompareNat target value with
      | lt =>
          rw [xorSatHasMemberConsOfLt target value [] hcomp,
              xorSatNatEqbOfLt target value hcomp, xorSatBoolXorFalseLeft]
      | eq =>
          rw [xorSatHasMemberConsOfEq target value [] hcomp,
              xorSatNatEqbOfEqCompare target value hcomp]
          rfl
      | gt =>
          rw [xorSatHasMemberConsOfGt target value [] hcomp,
              xorSatNatEqbOfGt target value hcomp, xorSatBoolXorFalseLeft]
  | head :: restVars, hasc => by
      have hrest : xorSatIsStrictlyAscending restVars = true := xorSatAndElimRight _ _ hasc
      cases hvh : xorSatCompareNat value head with
      | lt =>
          rw [xorSatToggleOneLt value head restVars hvh]
          cases htv : xorSatCompareNat target value with
          | eq =>
              have hteq : target = value := xorSatCompareNatEqImpliesEq target value htv
              have hbelowTarget : xorSatIsBelowHead target (head :: restVars) = true := by
                rw [hteq]; exact xorSatIsBelowHeadConsIntro value head restVars hvh
              rw [xorSatHasMemberConsOfEq target value (head :: restVars) htv,
                  xorSatNatEqbOfEqCompare target value htv,
                  xorSatHasMemberNotBelow target (head :: restVars) hbelowTarget hasc]
              rfl
          | lt =>
              rw [xorSatHasMemberConsOfLt target value (head :: restVars) htv,
                  xorSatNatEqbOfLt target value htv, xorSatBoolXorFalseLeft]
          | gt =>
              rw [xorSatHasMemberConsOfGt target value (head :: restVars) htv,
                  xorSatNatEqbOfGt target value htv, xorSatBoolXorFalseLeft]
      | eq =>
          have hveq : value = head := xorSatCompareNatEqImpliesEq value head hvh
          rw [xorSatToggleOneEq value head restVars hvh,
              xorSatHasMemberConsAscending target head restVars hasc, hveq,
              xorSatBoolXorCancelLeft (xorSatNatEqb target head)
                (xorSatHasMember target restVars)]
      | gt =>
          rw [xorSatToggleOneGt value head restVars hvh]
          cases hth : xorSatCompareNat target head with
          | eq =>
              have hteq : target = head := xorSatCompareNatEqImpliesEq target head hth
              have hne : xorSatNatEqb target value = false := by
                rw [hteq]
                exact xorSatNatEqbOfLt head value (xorSatCompareNatGtFlips value head hvh)
              rw [xorSatHasMemberConsOfEq target head (xorSatToggleOne value restVars) hth,
                  xorSatHasMemberConsOfEq target head restVars hth, hne,
                  xorSatBoolXorFalseLeft]
          | lt =>
              rw [xorSatHasMemberConsOfLt target head (xorSatToggleOne value restVars) hth,
                  xorSatHasMemberConsOfLt target head restVars hth,
                  xorSatHasMemberToggleOne target value restVars hrest]
          | gt =>
              rw [xorSatHasMemberConsOfGt target head (xorSatToggleOne value restVars) hth,
                  xorSatHasMemberConsOfGt target head restVars hth,
                  xorSatHasMemberToggleOne target value restVars hrest]

/-- Membership in the toggle-merge is the xor of memberships, which is what lets pivot
elimination remove a variable. -/
theorem xorSatHasMemberToggleMerge (target : Nat) : (first second : List Nat) →
    xorSatIsStrictlyAscending first = true →
    xorSatIsStrictlyAscending second = true →
    xorSatHasMember target (xorSatToggleMerge first second)
      = xorSatBoolXor (xorSatHasMember target first) (xorSatHasMember target second)
  | [], second, _hfirst, _hsecond => by
      rw [xorSatToggleMergeNilLeft]
      show xorSatHasMember target second
        = xorSatBoolXor false (xorSatHasMember target second)
      rw [xorSatBoolXorFalseLeft]
  | firstHead :: firstRest, second, hfirst, hsecond => by
      have hrest : xorSatIsStrictlyAscending firstRest = true := xorSatAndElimRight _ _ hfirst
      show xorSatHasMember target (xorSatToggleOne firstHead (xorSatToggleMerge firstRest second))
        = xorSatBoolXor (xorSatHasMember target (firstHead :: firstRest))
            (xorSatHasMember target second)
      rw [xorSatHasMemberToggleOne target firstHead (xorSatToggleMerge firstRest second)
            (xorSatToggleMergePreservesAscending firstRest second hsecond),
          xorSatHasMemberToggleMerge target firstRest second hrest hsecond,
          xorSatHasMemberConsAscending target firstHead firstRest hfirst,
          ← xorSatBoolXorAssoc]

/-! ## Witness surgery: removal and pivot extension -/

/-- Remove every occurrence of one variable from a witness list. -/
def xorSatRemoveVar (target : Nat) : List Nat → List Nat
  | [] => []
  | head :: restVars =>
      match xorSatCompareNat target head with
      | Ordering.lt => head :: xorSatRemoveVar target restVars
      | Ordering.eq => xorSatRemoveVar target restVars
      | Ordering.gt => head :: xorSatRemoveVar target restVars

theorem xorSatRemoveVarConsOfLt (target head : Nat) (restVars : List Nat)
    (hlt : xorSatCompareNat target head = Ordering.lt) :
    xorSatRemoveVar target (head :: restVars) = head :: xorSatRemoveVar target restVars := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => head :: xorSatRemoveVar target restVars
        | Ordering.eq => xorSatRemoveVar target restVars
        | Ordering.gt => head :: xorSatRemoveVar target restVars)
      = head :: xorSatRemoveVar target restVars
  rw [hlt]

theorem xorSatRemoveVarConsOfEq (target head : Nat) (restVars : List Nat)
    (heq : xorSatCompareNat target head = Ordering.eq) :
    xorSatRemoveVar target (head :: restVars) = xorSatRemoveVar target restVars := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => head :: xorSatRemoveVar target restVars
        | Ordering.eq => xorSatRemoveVar target restVars
        | Ordering.gt => head :: xorSatRemoveVar target restVars)
      = xorSatRemoveVar target restVars
  rw [heq]

theorem xorSatRemoveVarConsOfGt (target head : Nat) (restVars : List Nat)
    (hgt : xorSatCompareNat target head = Ordering.gt) :
    xorSatRemoveVar target (head :: restVars) = head :: xorSatRemoveVar target restVars := by
  show (match xorSatCompareNat target head with
        | Ordering.lt => head :: xorSatRemoveVar target restVars
        | Ordering.eq => xorSatRemoveVar target restVars
        | Ordering.gt => head :: xorSatRemoveVar target restVars)
      = head :: xorSatRemoveVar target restVars
  rw [hgt]

/-- The removed variable is absent afterwards. -/
theorem xorSatRemoveVarSelfAbsent (target : Nat) : (vars : List Nat) →
    xorSatHasMember target (xorSatRemoveVar target vars) = false
  | [] => rfl
  | head :: restVars => by
      cases hcomp : xorSatCompareNat target head with
      | lt =>
          rw [xorSatRemoveVarConsOfLt target head restVars hcomp,
              xorSatHasMemberConsOfLt target head (xorSatRemoveVar target restVars) hcomp,
              xorSatRemoveVarSelfAbsent target restVars]
      | eq =>
          rw [xorSatRemoveVarConsOfEq target head restVars hcomp,
              xorSatRemoveVarSelfAbsent target restVars]
      | gt =>
          rw [xorSatRemoveVarConsOfGt target head restVars hcomp,
              xorSatHasMemberConsOfGt target head (xorSatRemoveVar target restVars) hcomp,
              xorSatRemoveVarSelfAbsent target restVars]

/-- Removal is invisible to every other variable. -/
theorem xorSatRemoveVarKeepsOthers (probe target : Nat)
    (hne : xorSatNatEqb probe target = false) : (vars : List Nat) →
    xorSatHasMember probe (xorSatRemoveVar target vars) = xorSatHasMember probe vars
  | [] => rfl
  | head :: restVars => by
      cases hcomp : xorSatCompareNat target head with
      | eq =>
          have hheq : target = head := xorSatCompareNatEqImpliesEq target head hcomp
          have hprobeHead : xorSatNatEqb probe head = false := by
            rw [← hheq]; exact hne
          rw [xorSatRemoveVarConsOfEq target head restVars hcomp]
          cases hph : xorSatCompareNat probe head with
          | lt =>
              rw [xorSatHasMemberConsOfLt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]
          | eq =>
              exact Bool.noConfusion
                ((xorSatNatEqbOfEqCompare probe head hph).symm.trans hprobeHead)
          | gt =>
              rw [xorSatHasMemberConsOfGt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]
      | lt =>
          rw [xorSatRemoveVarConsOfLt target head restVars hcomp]
          cases hph : xorSatCompareNat probe head with
          | lt =>
              rw [xorSatHasMemberConsOfLt probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfLt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]
          | eq =>
              rw [xorSatHasMemberConsOfEq probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfEq probe head restVars hph]
          | gt =>
              rw [xorSatHasMemberConsOfGt probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfGt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]
      | gt =>
          rw [xorSatRemoveVarConsOfGt target head restVars hcomp]
          cases hph : xorSatCompareNat probe head with
          | lt =>
              rw [xorSatHasMemberConsOfLt probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfLt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]
          | eq =>
              rw [xorSatHasMemberConsOfEq probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfEq probe head restVars hph]
          | gt =>
              rw [xorSatHasMemberConsOfGt probe head (xorSatRemoveVar target restVars) hph,
                  xorSatHasMemberConsOfGt probe head restVars hph,
                  xorSatRemoveVarKeepsOthers probe target hne restVars]

/-- The environment induced by a witness list: apply-only membership, never `funext`ed. -/
def xorSatEnvOfWitness (witnessTrueSet : List Nat) : Nat → Bool :=
  fun queriedVar => xorSatHasMember queriedVar witnessTrueSet

/-- Extend a witness with an exact pivot value (removing stale pivot occurrences first). -/
def xorSatExtendWitness (pivotVar : Nat) (pivotValue : Bool)
    (witnessTrueSet : List Nat) : List Nat :=
  match pivotValue with
  | true => pivotVar :: xorSatRemoveVar pivotVar witnessTrueSet
  | false => xorSatRemoveVar pivotVar witnessTrueSet

/-- The extended witness reads back the pivot value exactly. -/
theorem xorSatEnvExtendAtPivot (pivotVar : Nat) (pivotValue : Bool)
    (witnessTrueSet : List Nat) :
    xorSatEnvOfWitness (xorSatExtendWitness pivotVar pivotValue witnessTrueSet) pivotVar
      = pivotValue := by
  cases pivotValue with
  | true =>
      show xorSatHasMember pivotVar (pivotVar :: xorSatRemoveVar pivotVar witnessTrueSet) = true
      exact xorSatHasMemberConsOfEq pivotVar pivotVar
        (xorSatRemoveVar pivotVar witnessTrueSet) (xorSatCompareNatRefl pivotVar)
  | false =>
      show xorSatHasMember pivotVar (xorSatRemoveVar pivotVar witnessTrueSet) = false
      exact xorSatRemoveVarSelfAbsent pivotVar witnessTrueSet

/-- The extended witness is invisible away from the pivot. -/
theorem xorSatEnvExtendAtOther (pivotVar : Nat) (pivotValue : Bool)
    (witnessTrueSet : List Nat) (probe : Nat)
    (hne : xorSatNatEqb probe pivotVar = false) :
    xorSatEnvOfWitness (xorSatExtendWitness pivotVar pivotValue witnessTrueSet) probe
      = xorSatEnvOfWitness witnessTrueSet probe := by
  cases pivotValue with
  | true =>
      show xorSatHasMember probe (pivotVar :: xorSatRemoveVar pivotVar witnessTrueSet)
        = xorSatHasMember probe witnessTrueSet
      cases hpp : xorSatCompareNat probe pivotVar with
      | lt =>
          rw [xorSatHasMemberConsOfLt probe pivotVar
                (xorSatRemoveVar pivotVar witnessTrueSet) hpp]
          exact xorSatRemoveVarKeepsOthers probe pivotVar hne witnessTrueSet
      | eq =>
          exact Bool.noConfusion
            ((xorSatNatEqbOfEqCompare probe pivotVar hpp).symm.trans hne)
      | gt =>
          rw [xorSatHasMemberConsOfGt probe pivotVar
                (xorSatRemoveVar pivotVar witnessTrueSet) hpp]
          exact xorSatRemoveVarKeepsOthers probe pivotVar hne witnessTrueSet
  | false =>
      show xorSatHasMember probe (xorSatRemoveVar pivotVar witnessTrueSet)
        = xorSatHasMember probe witnessTrueSet
      exact xorSatRemoveVarKeepsOthers probe pivotVar hne witnessTrueSet

/-! ## Equations, evaluation, combination -/

/-- One F2 equation: a strictly-ascending variable support and a parity right-hand side. -/
structure XorSatEquation where
  variables : List Nat
  parity : Bool

/-- Is the equation's support strictly ascending? -/
def xorSatEquationIsWellFormed (equation : XorSatEquation) : Bool :=
  xorSatIsStrictlyAscending equation.variables

/-- Xor-fold of an environment over a variable list. -/
def xorSatXorFold (env : Nat → Bool) : List Nat → Bool
  | [] => false
  | head :: restVars => xorSatBoolXor (env head) (xorSatXorFold env restVars)

/-- The xor-fold sees a single toggle as one more xor, unconditionally: duplicates cancel
exactly as F2 requires. -/
theorem xorSatXorFoldToggleOne (env : Nat → Bool) (value : Nat) : (vars : List Nat) →
    xorSatXorFold env (xorSatToggleOne value vars)
      = xorSatBoolXor (env value) (xorSatXorFold env vars)
  | [] => rfl
  | head :: restVars => by
      cases hvh : xorSatCompareNat value head with
      | lt =>
          rw [xorSatToggleOneLt value head restVars hvh]
          rfl
      | eq =>
          rw [xorSatToggleOneEq value head restVars hvh,
              xorSatCompareNatEqImpliesEq value head hvh,
              show xorSatXorFold env (head :: restVars)
                = xorSatBoolXor (env head) (xorSatXorFold env restVars) from rfl,
              xorSatBoolXorCancelLeft]
      | gt =>
          rw [xorSatToggleOneGt value head restVars hvh]
          show xorSatBoolXor (env head) (xorSatXorFold env (xorSatToggleOne value restVars))
            = xorSatBoolXor (env value) (xorSatXorFold env (head :: restVars))
          rw [xorSatXorFoldToggleOne env value restVars, xorSatBoolXorLeftSwap]
          rfl

/-- The evaluation lemma: the xor-fold over a toggle-merge is the xor of the two xor-folds. -/
theorem xorSatXorFoldToggleMerge (env : Nat → Bool) : (first second : List Nat) →
    xorSatXorFold env (xorSatToggleMerge first second)
      = xorSatBoolXor (xorSatXorFold env first) (xorSatXorFold env second)
  | [], second => by
      rw [xorSatToggleMergeNilLeft]
      show xorSatXorFold env second = xorSatBoolXor false (xorSatXorFold env second)
      rw [xorSatBoolXorFalseLeft]
  | firstHead :: firstRest, second => by
      show xorSatXorFold env (xorSatToggleOne firstHead (xorSatToggleMerge firstRest second))
        = xorSatBoolXor (xorSatXorFold env (firstHead :: firstRest)) (xorSatXorFold env second)
      rw [xorSatXorFoldToggleOne env firstHead (xorSatToggleMerge firstRest second),
          xorSatXorFoldToggleMerge env firstRest second, ← xorSatBoolXorAssoc]
      rfl

/-- Does the equation hold under the environment? -/
def xorSatEvalEquation (env : Nat → Bool) (equation : XorSatEquation) : Bool :=
  xorSatBoolEq (xorSatXorFold env equation.variables) equation.parity

/-- F2 sum of two equations: toggle-merged supports, xored parities. -/
def xorSatCombine (first second : XorSatEquation) : XorSatEquation :=
  { variables := xorSatToggleMerge first.variables second.variables,
    parity := xorSatBoolXor first.parity second.parity }

/-- The combination inherits well-formedness from its second summand. -/
theorem xorSatCombineIsWellFormed (first second : XorSatEquation)
    (hsecond : xorSatEquationIsWellFormed second = true) :
    xorSatEquationIsWellFormed (xorSatCombine first second) = true :=
  xorSatToggleMergePreservesAscending first.variables second.variables hsecond

/-- Any environment satisfying both equations satisfies their combination. -/
theorem xorSatEvalCombine (env : Nat → Bool) (first second : XorSatEquation)
    (hfirst : xorSatEvalEquation env first = true)
    (hsecond : xorSatEvalEquation env second = true) :
    xorSatEvalEquation env (xorSatCombine first second) = true := by
  have hfoldFirst : xorSatXorFold env first.variables = first.parity :=
    xorSatBoolEqImpliesEq _ _ hfirst
  have hfoldSecond : xorSatXorFold env second.variables = second.parity :=
    xorSatBoolEqImpliesEq _ _ hsecond
  show xorSatBoolEq
        (xorSatXorFold env (xorSatToggleMerge first.variables second.variables))
        (xorSatBoolXor first.parity second.parity) = true
  rw [xorSatXorFoldToggleMerge env first.variables second.variables, hfoldFirst, hfoldSecond]
  exact xorSatBoolEqRefl _

/-- Folds agree across two environments that agree away from an absent pivot. -/
theorem xorSatXorFoldAgreeOffPivot (pivotVar : Nat) (extendedEnv baseEnv : Nat → Bool)
    (hAgree : ∀ offVar : Nat, xorSatNatEqb offVar pivotVar = false →
      extendedEnv offVar = baseEnv offVar) : (vars : List Nat) →
    xorSatHasMember pivotVar vars = false →
    xorSatXorFold extendedEnv vars = xorSatXorFold baseEnv vars
  | [], _habsent => rfl
  | head :: restVars, habsent => by
      cases hph : xorSatCompareNat pivotVar head with
      | eq =>
          exact Bool.noConfusion
            ((xorSatHasMemberConsOfEq pivotVar head restVars hph).symm.trans habsent)
      | lt =>
          have hrestAbsent : xorSatHasMember pivotVar restVars = false := by
            rw [← xorSatHasMemberConsOfLt pivotVar head restVars hph]; exact habsent
          show xorSatBoolXor (extendedEnv head) (xorSatXorFold extendedEnv restVars)
            = xorSatBoolXor (baseEnv head) (xorSatXorFold baseEnv restVars)
          rw [hAgree head (xorSatNatEqbOfGt head pivotVar
                (xorSatCompareNatLtFlips pivotVar head hph)),
              xorSatXorFoldAgreeOffPivot pivotVar extendedEnv baseEnv hAgree
                restVars hrestAbsent]
      | gt =>
          have hrestAbsent : xorSatHasMember pivotVar restVars = false := by
            rw [← xorSatHasMemberConsOfGt pivotVar head restVars hph]; exact habsent
          show xorSatBoolXor (extendedEnv head) (xorSatXorFold extendedEnv restVars)
            = xorSatBoolXor (baseEnv head) (xorSatXorFold baseEnv restVars)
          rw [hAgree head (xorSatNatEqbOfLt head pivotVar
                (xorSatCompareNatGtFlips pivotVar head hph)),
              xorSatXorFoldAgreeOffPivot pivotVar extendedEnv baseEnv hAgree
                restVars hrestAbsent]

/-! ## Systems, indexed selection, and the F2 selection fold -/

/-- The zero equation `0 = 0` — satisfied by everything. -/
def xorSatZeroEquation : XorSatEquation := { variables := [], parity := false }

/-- The contradiction `0 = 1` — satisfied by nothing. -/
def xorSatContradictionEquation : XorSatEquation := { variables := [], parity := true }

/-- Does the environment satisfy every equation of the system? -/
def xorSatEvalSystem (env : Nat → Bool) : List XorSatEquation → Bool
  | [] => true
  | equation :: restEquations =>
      xorSatEvalEquation env equation && xorSatEvalSystem env restEquations

/-- Is every equation of the system well-formed? -/
def xorSatSystemIsWellFormed : List XorSatEquation → Bool
  | [] => true
  | equation :: restEquations =>
      xorSatEquationIsWellFormed equation && xorSatSystemIsWellFormed restEquations

/-- Indexed lookup; out of range reads as the zero equation. -/
def xorSatGetEquation : Nat → List XorSatEquation → XorSatEquation
  | 0, [] => xorSatZeroEquation
  | 0, equation :: _restEquations => equation
  | Nat.succ _innerIndex, [] => xorSatZeroEquation
  | Nat.succ innerIndex, _equation :: restEquations =>
      xorSatGetEquation innerIndex restEquations

theorem xorSatGetEquationIsWellFormed : (index : Nat) → (system : List XorSatEquation) →
    xorSatSystemIsWellFormed system = true →
    xorSatEquationIsWellFormed (xorSatGetEquation index system) = true
  | 0, [], _hwf => rfl
  | 0, _equation :: _restEquations, hwf => xorSatAndElimLeft _ _ hwf
  | Nat.succ _innerIndex, [], _hwf => rfl
  | Nat.succ innerIndex, _equation :: restEquations, hwf =>
      xorSatGetEquationIsWellFormed innerIndex restEquations (xorSatAndElimRight _ _ hwf)

/-- A satisfying environment satisfies every indexed equation (out of range: the zero
equation, trivially). -/
theorem xorSatEvalSystemGet (env : Nat → Bool) : (index : Nat) →
    (system : List XorSatEquation) →
    xorSatEvalSystem env system = true →
    xorSatEvalEquation env (xorSatGetEquation index system) = true
  | 0, [], _hsat => rfl
  | 0, _equation :: _restEquations, hsat => xorSatAndElimLeft _ _ hsat
  | Nat.succ _innerIndex, [], _hsat => rfl
  | Nat.succ innerIndex, _equation :: restEquations, hsat =>
      xorSatEvalSystemGet env innerIndex restEquations (xorSatAndElimRight _ _ hsat)

/-- F2 sum of the equations selected by an index list. -/
def xorSatSelectXor (comboIndices : List Nat) (system : List XorSatEquation) : XorSatEquation :=
  match comboIndices with
  | [] => xorSatZeroEquation
  | index :: restIndices =>
      xorSatCombine (xorSatGetEquation index system) (xorSatSelectXor restIndices system)

theorem xorSatSelectXorIsWellFormed : (comboIndices : List Nat) →
    (system : List XorSatEquation) →
    xorSatSystemIsWellFormed system = true →
    xorSatEquationIsWellFormed (xorSatSelectXor comboIndices system) = true
  | [], _system, _hwf => rfl
  | index :: restIndices, system, hwf =>
      xorSatCombineIsWellFormed (xorSatGetEquation index system)
        (xorSatSelectXor restIndices system)
        (xorSatSelectXorIsWellFormed restIndices system hwf)

/-- The selection lemma: any environment satisfying the whole system satisfies the F2 sum
of any index selection. -/
theorem xorSatSelectXorSatisfied (env : Nat → Bool) : (comboIndices : List Nat) →
    (system : List XorSatEquation) →
    xorSatEvalSystem env system = true →
    xorSatEvalEquation env (xorSatSelectXor comboIndices system) = true
  | [], _system, _hsat => rfl
  | index :: restIndices, system, hsat =>
      xorSatEvalCombine env (xorSatGetEquation index system)
        (xorSatSelectXor restIndices system)
        (xorSatEvalSystemGet env index system hsat)
        (xorSatSelectXorSatisfied env restIndices system hsat)

/-! ## The combine algebra (F2 vector space of equations) -/

theorem xorSatCombineZeroLeft (equation : XorSatEquation) :
    xorSatCombine xorSatZeroEquation equation = equation := by
  show XorSatEquation.mk (xorSatToggleMerge [] equation.variables)
        (xorSatBoolXor false equation.parity) = equation
  rw [xorSatToggleMergeNilLeft, xorSatBoolXorFalseLeft]

theorem xorSatCombineZeroRight (equation : XorSatEquation)
    (hwf : xorSatEquationIsWellFormed equation = true) :
    xorSatCombine equation xorSatZeroEquation = equation := by
  show XorSatEquation.mk (xorSatToggleMerge equation.variables [])
        (xorSatBoolXor equation.parity false) = equation
  rw [xorSatToggleMergeNilRight equation.variables hwf, xorSatBoolXorFalseRight]

theorem xorSatCombineComm (first second : XorSatEquation)
    (hfirst : xorSatEquationIsWellFormed first = true)
    (hsecond : xorSatEquationIsWellFormed second = true) :
    xorSatCombine first second = xorSatCombine second first := by
  show XorSatEquation.mk (xorSatToggleMerge first.variables second.variables)
        (xorSatBoolXor first.parity second.parity)
      = XorSatEquation.mk (xorSatToggleMerge second.variables first.variables)
        (xorSatBoolXor second.parity first.parity)
  rw [xorSatToggleMergeComm first.variables second.variables hfirst hsecond,
      xorSatBoolXorComm first.parity second.parity]

theorem xorSatCombineAssoc (first second third : XorSatEquation)
    (hthird : xorSatEquationIsWellFormed third = true) :
    xorSatCombine (xorSatCombine first second) third
      = xorSatCombine first (xorSatCombine second third) := by
  show XorSatEquation.mk
        (xorSatToggleMerge (xorSatToggleMerge first.variables second.variables)
          third.variables)
        (xorSatBoolXor (xorSatBoolXor first.parity second.parity) third.parity)
      = XorSatEquation.mk
        (xorSatToggleMerge first.variables
          (xorSatToggleMerge second.variables third.variables))
        (xorSatBoolXor first.parity (xorSatBoolXor second.parity third.parity))
  rw [xorSatToggleMergeAssoc first.variables second.variables third.variables hthird,
      xorSatBoolXorAssoc]

theorem xorSatCombineSelfCancel (first second : XorSatEquation)
    (hfirst : xorSatEquationIsWellFormed first = true)
    (hsecond : xorSatEquationIsWellFormed second = true) :
    xorSatCombine first (xorSatCombine first second) = second := by
  show XorSatEquation.mk
        (xorSatToggleMerge first.variables
          (xorSatToggleMerge first.variables second.variables))
        (xorSatBoolXor first.parity (xorSatBoolXor first.parity second.parity))
      = second
  rw [xorSatToggleMergeSelfCancel first.variables second.variables hfirst hsecond,
      xorSatBoolXorCancelLeft]

theorem xorSatCombineLeftSwap (first second target : XorSatEquation)
    (hfirst : xorSatEquationIsWellFormed first = true)
    (hsecond : xorSatEquationIsWellFormed second = true)
    (htarget : xorSatEquationIsWellFormed target = true) :
    xorSatCombine first (xorSatCombine second target)
      = xorSatCombine second (xorSatCombine first target) := by
  rw [← xorSatCombineAssoc first second target htarget,
      xorSatCombineComm first second hfirst hsecond,
      xorSatCombineAssoc second first target htarget]

/-! ## The fold homomorphism: selection commutes with combo toggling -/

theorem xorSatSelectXorToggleOne (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true) (index : Nat) :
    (comboIndices : List Nat) →
    xorSatIsStrictlyAscending comboIndices = true →
    xorSatSelectXor (xorSatToggleOne index comboIndices) system
      = xorSatCombine (xorSatGetEquation index system)
          (xorSatSelectXor comboIndices system)
  | [], _hasc => rfl
  | firstIndex :: restIndices, hasc => by
      have hrest : xorSatIsStrictlyAscending restIndices = true :=
        xorSatAndElimRight _ _ hasc
      cases hif : xorSatCompareNat index firstIndex with
      | lt =>
          rw [xorSatToggleOneLt index firstIndex restIndices hif]
          rfl
      | eq =>
          have hieq : index = firstIndex := xorSatCompareNatEqImpliesEq index firstIndex hif
          rw [xorSatToggleOneEq index firstIndex restIndices hif, hieq,
              show xorSatSelectXor (firstIndex :: restIndices) system
                = xorSatCombine (xorSatGetEquation firstIndex system)
                    (xorSatSelectXor restIndices system) from rfl,
              xorSatCombineSelfCancel (xorSatGetEquation firstIndex system)
                (xorSatSelectXor restIndices system)
                (xorSatGetEquationIsWellFormed firstIndex system hSystemWf)
                (xorSatSelectXorIsWellFormed restIndices system hSystemWf)]
      | gt =>
          rw [xorSatToggleOneGt index firstIndex restIndices hif]
          show xorSatCombine (xorSatGetEquation firstIndex system)
                (xorSatSelectXor (xorSatToggleOne index restIndices) system)
              = xorSatCombine (xorSatGetEquation index system)
                (xorSatCombine (xorSatGetEquation firstIndex system)
                  (xorSatSelectXor restIndices system))
          rw [xorSatSelectXorToggleOne system hSystemWf index restIndices hrest,
              xorSatCombineLeftSwap (xorSatGetEquation firstIndex system)
                (xorSatGetEquation index system) (xorSatSelectXor restIndices system)
                (xorSatGetEquationIsWellFormed firstIndex system hSystemWf)
                (xorSatGetEquationIsWellFormed index system hSystemWf)
                (xorSatSelectXorIsWellFormed restIndices system hSystemWf)]

/-- The fold homomorphism: `selectXor` sends a combo toggle-merge to an equation combination,
so the provenance invariant survives pivot elimination. -/
theorem xorSatSelectXorToggleMerge (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true) :
    (firstCombo secondCombo : List Nat) →
    xorSatIsStrictlyAscending firstCombo = true →
    xorSatIsStrictlyAscending secondCombo = true →
    xorSatSelectXor (xorSatToggleMerge firstCombo secondCombo) system
      = xorSatCombine (xorSatSelectXor firstCombo system)
          (xorSatSelectXor secondCombo system)
  | [], secondCombo, _hfirst, _hsecond => by
      rw [xorSatToggleMergeNilLeft]
      show xorSatSelectXor secondCombo system
        = xorSatCombine xorSatZeroEquation (xorSatSelectXor secondCombo system)
      rw [xorSatCombineZeroLeft]
  | firstIndex :: firstRest, secondCombo, hfirst, hsecond => by
      have hrest : xorSatIsStrictlyAscending firstRest = true :=
        xorSatAndElimRight _ _ hfirst
      show xorSatSelectXor
            (xorSatToggleOne firstIndex (xorSatToggleMerge firstRest secondCombo)) system
          = xorSatCombine
            (xorSatCombine (xorSatGetEquation firstIndex system)
              (xorSatSelectXor firstRest system))
            (xorSatSelectXor secondCombo system)
      rw [xorSatSelectXorToggleOne system hSystemWf firstIndex
            (xorSatToggleMerge firstRest secondCombo)
            (xorSatToggleMergePreservesAscending firstRest secondCombo hsecond),
          xorSatSelectXorToggleMerge system hSystemWf firstRest secondCombo hrest hsecond,
          ← xorSatCombineAssoc (xorSatGetEquation firstIndex system)
            (xorSatSelectXor firstRest system) (xorSatSelectXor secondCombo system)
            (xorSatSelectXorIsWellFormed secondCombo system hSystemWf)]

/-! ## Working items, verdicts, and the pivot transform -/

/-- A working item: the current equation plus the F2 combination of original equation
indices it equals. -/
structure XorSatWorkItem where
  equation : XorSatEquation
  comboIndices : List Nat

/-- The decision verdict: a satisfying witness (true-variable set) or an unsatisfiability
certificate (original-equation indices xoring to the contradiction). -/
inductive XorSatVerdict : Type where
  | isSatisfiable : (witnessTrueSet : List Nat) → XorSatVerdict
  | isUnsatisfiable : (comboIndices : List Nat) → XorSatVerdict

/-- Structural count of working items (the decision fuel). -/
def xorSatWorkCount : List XorSatWorkItem → Nat
  | [] => 0
  | _item :: restItems => Nat.succ (xorSatWorkCount restItems)

/-- Combine the pivot equation into every tail item whose equation contains the pivot
variable, toggle-merging the provenance combos alongside. -/
def xorSatPivotTransform (pivotVar : Nat) (pivotEquation : XorSatEquation)
    (pivotCombo : List Nat) : List XorSatWorkItem → List XorSatWorkItem
  | [] => []
  | item :: restItems =>
      match xorSatHasMember pivotVar item.equation.variables with
      | true =>
          { equation := xorSatCombine pivotEquation item.equation,
            comboIndices := xorSatToggleMerge pivotCombo item.comboIndices }
            :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems
      | false => item :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems

theorem xorSatPivotTransformConsMember (pivotVar : Nat) (pivotEquation : XorSatEquation)
    (pivotCombo : List Nat) (item : XorSatWorkItem) (restItems : List XorSatWorkItem)
    (hmem : xorSatHasMember pivotVar item.equation.variables = true) :
    xorSatPivotTransform pivotVar pivotEquation pivotCombo (item :: restItems)
      = { equation := xorSatCombine pivotEquation item.equation,
          comboIndices := xorSatToggleMerge pivotCombo item.comboIndices }
        :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems := by
  show (match xorSatHasMember pivotVar item.equation.variables with
        | true =>
            { equation := xorSatCombine pivotEquation item.equation,
              comboIndices := xorSatToggleMerge pivotCombo item.comboIndices }
              :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems
        | false => item :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems)
      = { equation := xorSatCombine pivotEquation item.equation,
          comboIndices := xorSatToggleMerge pivotCombo item.comboIndices }
        :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems
  rw [hmem]

theorem xorSatPivotTransformConsSkip (pivotVar : Nat) (pivotEquation : XorSatEquation)
    (pivotCombo : List Nat) (item : XorSatWorkItem) (restItems : List XorSatWorkItem)
    (hmem : xorSatHasMember pivotVar item.equation.variables = false) :
    xorSatPivotTransform pivotVar pivotEquation pivotCombo (item :: restItems)
      = item :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems := by
  show (match xorSatHasMember pivotVar item.equation.variables with
        | true =>
            { equation := xorSatCombine pivotEquation item.equation,
              comboIndices := xorSatToggleMerge pivotCombo item.comboIndices }
              :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems
        | false => item :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems)
      = item :: xorSatPivotTransform pivotVar pivotEquation pivotCombo restItems
  rw [hmem]

/-- The transform never changes the working count — each round shrinks by exactly one. -/
theorem xorSatPivotTransformCount (pivotVar : Nat) (pivotEquation : XorSatEquation)
    (pivotCombo : List Nat) : (tailItems : List XorSatWorkItem) →
    xorSatWorkCount (xorSatPivotTransform pivotVar pivotEquation pivotCombo tailItems)
      = xorSatWorkCount tailItems
  | [] => rfl
  | item :: restItems => by
      cases hmem : xorSatHasMember pivotVar item.equation.variables with
      | true =>
          rw [xorSatPivotTransformConsMember pivotVar pivotEquation pivotCombo item
                restItems hmem]
          exact congrArg Nat.succ
            (xorSatPivotTransformCount pivotVar pivotEquation pivotCombo restItems)
      | false =>
          rw [xorSatPivotTransformConsSkip pivotVar pivotEquation pivotCombo item
                restItems hmem]
          exact congrArg Nat.succ
            (xorSatPivotTransformCount pivotVar pivotEquation pivotCombo restItems)

/-- Is every working equation's support strictly ascending? -/
def xorSatWorkIsWellFormed : List XorSatWorkItem → Bool
  | [] => true
  | item :: restItems =>
      xorSatEquationIsWellFormed item.equation && xorSatWorkIsWellFormed restItems

theorem xorSatPivotTransformPreservesWellFormed (pivotVar : Nat)
    (pivotEquation : XorSatEquation) (pivotCombo : List Nat) :
    (tailItems : List XorSatWorkItem) →
    xorSatWorkIsWellFormed tailItems = true →
    xorSatWorkIsWellFormed
      (xorSatPivotTransform pivotVar pivotEquation pivotCombo tailItems) = true
  | [], _hwf => rfl
  | item :: restItems, hwf => by
      have hitemWf : xorSatEquationIsWellFormed item.equation = true :=
        xorSatAndElimLeft _ _ hwf
      have hrestWf : xorSatWorkIsWellFormed restItems = true := xorSatAndElimRight _ _ hwf
      cases hmem : xorSatHasMember pivotVar item.equation.variables with
      | true =>
          rw [xorSatPivotTransformConsMember pivotVar pivotEquation pivotCombo item
                restItems hmem]
          exact xorSatAndIntro _ _
            (xorSatCombineIsWellFormed pivotEquation item.equation hitemWf)
            (xorSatPivotTransformPreservesWellFormed pivotVar pivotEquation pivotCombo
              restItems hrestWf)
      | false =>
          rw [xorSatPivotTransformConsSkip pivotVar pivotEquation pivotCombo item
                restItems hmem]
          exact xorSatAndIntro _ _ hitemWf
            (xorSatPivotTransformPreservesWellFormed pivotVar pivotEquation pivotCombo
              restItems hrestWf)

/-- Provenance: every working equation is the F2 selection of its (ascending) combo over
the original system. -/
def xorSatWorkHasProvenance (system : List XorSatEquation) : List XorSatWorkItem → Prop
  | [] => True
  | item :: restItems =>
      (item.equation = xorSatSelectXor item.comboIndices system
        ∧ xorSatIsStrictlyAscending item.comboIndices = true)
      ∧ xorSatWorkHasProvenance system restItems

/-- Pivot elimination preserves provenance — via the fold homomorphism. -/
theorem xorSatPivotTransformPreservesProvenance (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true)
    (pivotVar : Nat) (pivotEquation : XorSatEquation) (pivotCombo : List Nat)
    (hPivotEq : pivotEquation = xorSatSelectXor pivotCombo system)
    (hPivotAsc : xorSatIsStrictlyAscending pivotCombo = true) :
    (tailItems : List XorSatWorkItem) →
    xorSatWorkHasProvenance system tailItems →
    xorSatWorkHasProvenance system
      (xorSatPivotTransform pivotVar pivotEquation pivotCombo tailItems)
  | [], hprov => hprov
  | item :: restItems, hprov => by
      obtain ⟨⟨hitemEq, hitemAsc⟩, hrestProv⟩ := hprov
      cases hmem : xorSatHasMember pivotVar item.equation.variables with
      | true =>
          rw [xorSatPivotTransformConsMember pivotVar pivotEquation pivotCombo item
                restItems hmem]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · show xorSatCombine pivotEquation item.equation
              = xorSatSelectXor (xorSatToggleMerge pivotCombo item.comboIndices) system
            rw [xorSatSelectXorToggleMerge system hSystemWf pivotCombo item.comboIndices
                  hPivotAsc hitemAsc, hPivotEq, hitemEq]
          · exact xorSatToggleMergePreservesAscending pivotCombo item.comboIndices hitemAsc
          · exact xorSatPivotTransformPreservesProvenance system hSystemWf pivotVar
              pivotEquation pivotCombo hPivotEq hPivotAsc restItems hrestProv
      | false =>
          rw [xorSatPivotTransformConsSkip pivotVar pivotEquation pivotCombo item
                restItems hmem]
          exact ⟨⟨hitemEq, hitemAsc⟩,
            xorSatPivotTransformPreservesProvenance system hSystemWf pivotVar
              pivotEquation pivotCombo hPivotEq hPivotAsc restItems hrestProv⟩

/-- Does the environment satisfy every working equation? -/
def xorSatCheckWork (env : Nat → Bool) : List XorSatWorkItem → Bool
  | [] => true
  | item :: restItems => xorSatEvalEquation env item.equation && xorSatCheckWork env restItems

/-! ## The fuel decider -/

/-- One elimination round per fuel unit: drop trivial heads, report the contradiction head's
combo, or pivot on the head's least variable and recurse on the transformed tail,
back-substituting the pivot value on the way out. -/
def xorSatDecideAux : Nat → List XorSatWorkItem → Option XorSatVerdict
  | 0, [] => some (XorSatVerdict.isSatisfiable [])
  | 0, _headItem :: _tailItems => none
  | Nat.succ _remainingFuel, [] => some (XorSatVerdict.isSatisfiable [])
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] false) _headCombo :: tailItems =>
      xorSatDecideAux remainingFuel tailItems
  | Nat.succ _remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] true) headCombo :: _tailItems =>
      some (XorSatVerdict.isUnsatisfiable headCombo)
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
        :: tailItems =>
      match xorSatDecideAux remainingFuel
          (xorSatPivotTransform pivotVar
            (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo tailItems) with
      | none => none
      | some (XorSatVerdict.isUnsatisfiable comboIndices) =>
          some (XorSatVerdict.isUnsatisfiable comboIndices)
      | some (XorSatVerdict.isSatisfiable recWitnessSet) =>
          some (XorSatVerdict.isSatisfiable
            (xorSatExtendWitness pivotVar
              (xorSatBoolXor headParity
                (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
              recWitnessSet))

theorem xorSatDecideAuxNil : (fuel : Nat) →
    xorSatDecideAux fuel [] = some (XorSatVerdict.isSatisfiable [])
  | 0 => rfl
  | Nat.succ _remainingFuel => rfl

theorem xorSatDecideAuxFuelOut (headItem : XorSatWorkItem)
    (tailItems : List XorSatWorkItem) :
    xorSatDecideAux 0 (headItem :: tailItems) = none := rfl

theorem xorSatDecideAuxDrop (remainingFuel : Nat) (headCombo : List Nat)
    (tailItems : List XorSatWorkItem) :
    xorSatDecideAux (Nat.succ remainingFuel)
        (XorSatWorkItem.mk (XorSatEquation.mk [] false) headCombo :: tailItems)
      = xorSatDecideAux remainingFuel tailItems := rfl

theorem xorSatDecideAuxContradiction (remainingFuel : Nat) (headCombo : List Nat)
    (tailItems : List XorSatWorkItem) :
    xorSatDecideAux (Nat.succ remainingFuel)
        (XorSatWorkItem.mk (XorSatEquation.mk [] true) headCombo :: tailItems)
      = some (XorSatVerdict.isUnsatisfiable headCombo) := rfl

theorem xorSatDecideAuxPivot (remainingFuel : Nat) (pivotVar : Nat)
    (pivotRestVars : List Nat) (headParity : Bool) (headCombo : List Nat)
    (tailItems : List XorSatWorkItem) :
    xorSatDecideAux (Nat.succ remainingFuel)
        (XorSatWorkItem.mk (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity)
          headCombo :: tailItems)
      = match xorSatDecideAux remainingFuel
            (xorSatPivotTransform pivotVar
              (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
              tailItems) with
        | none => none
        | some (XorSatVerdict.isUnsatisfiable comboIndices) =>
            some (XorSatVerdict.isUnsatisfiable comboIndices)
        | some (XorSatVerdict.isSatisfiable recWitnessSet) =>
            some (XorSatVerdict.isSatisfiable
              (xorSatExtendWitness pivotVar
                (xorSatBoolXor headParity
                  (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                recWitnessSet)) := rfl

/-- Does the optional verdict carry a verdict? -/
def xorSatIsSomeVerdict : Option XorSatVerdict → Bool
  | none => false
  | some _verdict => true

/-- `none` never equals a delivered verdict — the `Bool`-discriminator refutation. -/
theorem xorSatNoneNeSome (verdict : XorSatVerdict)
    (hcontr : (none : Option XorSatVerdict) = some verdict) : False :=
  Bool.noConfusion (congrArg xorSatIsSomeVerdict hcontr)

/-- Fuel adequacy: fuel equal to the working count always reaches a verdict. -/
theorem xorSatDecideAuxIsSome : (fuel : Nat) → (workingItems : List XorSatWorkItem) →
    xorSatWorkCount workingItems = fuel →
    xorSatIsSomeVerdict (xorSatDecideAux fuel workingItems) = true
  | 0, [], _hcount => rfl
  | 0, _headItem :: _tailItems, hcount => Nat.noConfusion hcount
  | Nat.succ _remainingFuel, [], _hcount => rfl
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] false) headCombo :: tailItems, hcount => by
      rw [xorSatDecideAuxDrop]
      exact xorSatDecideAuxIsSome remainingFuel tailItems (Nat.succ.inj hcount)
  | Nat.succ _remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] true) _headCombo :: _tailItems, _hcount => rfl
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
        :: tailItems, hcount => by
      rw [xorSatDecideAuxPivot]
      have hcountTransformed : xorSatWorkCount
          (xorSatPivotTransform pivotVar
            (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo tailItems)
          = remainingFuel :=
        (xorSatPivotTransformCount pivotVar
          (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
          tailItems).trans (Nat.succ.inj hcount)
      have hrecSome := xorSatDecideAuxIsSome remainingFuel
        (xorSatPivotTransform pivotVar
          (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo tailItems)
        hcountTransformed
      cases hrec : xorSatDecideAux remainingFuel
          (xorSatPivotTransform pivotVar
            (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
            tailItems) with
      | none =>
          rw [hrec] at hrecSome
          exact Bool.noConfusion hrecSome
      | some recVerdict =>
          cases recVerdict with
          | isSatisfiable recWitnessSet => rfl
          | isUnsatisfiable recCombo => rfl

/-! ## Back-substitution: extending a witness across one eliminated pivot -/

/-- If the extended environment satisfies the pivot equation, agrees with the base
environment away from the pivot, and the base environment satisfies the transformed tail,
then the extended environment satisfies the ORIGINAL tail. -/
theorem xorSatBackSubstituteTail (pivotVar : Nat) (pivotEquation : XorSatEquation)
    (pivotCombo : List Nat) (baseEnv extendedEnv : Nat → Bool)
    (hAgree : ∀ offVar : Nat, xorSatNatEqb offVar pivotVar = false →
      extendedEnv offVar = baseEnv offVar)
    (hPivotWf : xorSatEquationIsWellFormed pivotEquation = true)
    (hPivotMem : xorSatHasMember pivotVar pivotEquation.variables = true)
    (hPivotHolds : xorSatEvalEquation extendedEnv pivotEquation = true) :
    (tailItems : List XorSatWorkItem) →
    xorSatWorkIsWellFormed tailItems = true →
    xorSatCheckWork baseEnv
      (xorSatPivotTransform pivotVar pivotEquation pivotCombo tailItems) = true →
    xorSatCheckWork extendedEnv tailItems = true
  | [], _hwf, _hcheck => rfl
  | item :: restItems, hwf, hcheck => by
      have hitemWf : xorSatEquationIsWellFormed item.equation = true :=
        xorSatAndElimLeft _ _ hwf
      have hrestWf : xorSatWorkIsWellFormed restItems = true := xorSatAndElimRight _ _ hwf
      cases hmem : xorSatHasMember pivotVar item.equation.variables with
      | false =>
          rw [xorSatPivotTransformConsSkip pivotVar pivotEquation pivotCombo item
                restItems hmem] at hcheck
          have hitemBase : xorSatEvalEquation baseEnv item.equation = true :=
            xorSatAndElimLeft _ _ hcheck
          have hrestCheck := xorSatAndElimRight _ _ hcheck
          show (xorSatEvalEquation extendedEnv item.equation
              && xorSatCheckWork extendedEnv restItems) = true
          refine xorSatAndIntro _ _ ?_ ?_
          · show xorSatBoolEq (xorSatXorFold extendedEnv item.equation.variables)
                item.equation.parity = true
            rw [xorSatXorFoldAgreeOffPivot pivotVar extendedEnv baseEnv hAgree
                  item.equation.variables hmem]
            exact hitemBase
          · exact xorSatBackSubstituteTail pivotVar pivotEquation pivotCombo baseEnv
              extendedEnv hAgree hPivotWf hPivotMem hPivotHolds restItems hrestWf hrestCheck
      | true =>
          rw [xorSatPivotTransformConsMember pivotVar pivotEquation pivotCombo item
                restItems hmem] at hcheck
          have hcombBase : xorSatEvalEquation baseEnv
              (xorSatCombine pivotEquation item.equation) = true :=
            xorSatAndElimLeft _ _ hcheck
          have hrestCheck := xorSatAndElimRight _ _ hcheck
          have hcombAbsent : xorSatHasMember pivotVar
              (xorSatCombine pivotEquation item.equation).variables = false := by
            show xorSatHasMember pivotVar
              (xorSatToggleMerge pivotEquation.variables item.equation.variables) = false
            rw [xorSatHasMemberToggleMerge pivotVar pivotEquation.variables
                  item.equation.variables hPivotWf hitemWf, hPivotMem, hmem]
            rfl
          have hcombExtended : xorSatEvalEquation extendedEnv
              (xorSatCombine pivotEquation item.equation) = true := by
            show xorSatBoolEq
                (xorSatXorFold extendedEnv (xorSatCombine pivotEquation item.equation).variables)
                (xorSatCombine pivotEquation item.equation).parity = true
            rw [xorSatXorFoldAgreeOffPivot pivotVar extendedEnv baseEnv hAgree
                  (xorSatCombine pivotEquation item.equation).variables hcombAbsent]
            exact hcombBase
          have hitemExtended : xorSatEvalEquation extendedEnv item.equation = true := by
            rw [← xorSatCombineSelfCancel pivotEquation item.equation hPivotWf hitemWf]
            exact xorSatEvalCombine extendedEnv pivotEquation
              (xorSatCombine pivotEquation item.equation) hPivotHolds hcombExtended
          show (xorSatEvalEquation extendedEnv item.equation
              && xorSatCheckWork extendedEnv restItems) = true
          exact xorSatAndIntro _ _ hitemExtended
            (xorSatBackSubstituteTail pivotVar pivotEquation pivotCombo baseEnv
              extendedEnv hAgree hPivotWf hPivotMem hPivotHolds restItems hrestWf hrestCheck)

/-! ## SAT soundness of the fuel decider -/

/-- A returned witness satisfies every working equation under its induced environment. -/
theorem xorSatDecideAuxSatSound : (fuel : Nat) → (workingItems : List XorSatWorkItem) →
    xorSatWorkIsWellFormed workingItems = true →
    (witnessTrueSet : List Nat) →
    xorSatDecideAux fuel workingItems
      = some (XorSatVerdict.isSatisfiable witnessTrueSet) →
    xorSatCheckWork (xorSatEnvOfWitness witnessTrueSet) workingItems = true
  | 0, [], _hwf, _witnessTrueSet, _hrun => rfl
  | 0, _headItem :: _tailItems, _hwf, witnessTrueSet, hrun => by
      have hnone : (none : Option XorSatVerdict)
          = some (XorSatVerdict.isSatisfiable witnessTrueSet) := hrun
      exact False.elim (xorSatNoneNeSome _ hnone)
  | Nat.succ _remainingFuel, [], _hwf, _witnessTrueSet, _hrun => rfl
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] false) headCombo :: tailItems,
      hwf, witnessTrueSet, hrun => by
      rw [xorSatDecideAuxDrop] at hrun
      have hrestCheck := xorSatDecideAuxSatSound remainingFuel tailItems
        (xorSatAndElimRight _ _ hwf) witnessTrueSet hrun
      show (xorSatEvalEquation (xorSatEnvOfWitness witnessTrueSet) (XorSatEquation.mk [] false)
          && xorSatCheckWork (xorSatEnvOfWitness witnessTrueSet) tailItems) = true
      exact xorSatAndIntro _ _ rfl hrestCheck
  | Nat.succ _remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] true) headCombo :: _tailItems,
      _hwf, witnessTrueSet, hrun => by
      have hsome : some (XorSatVerdict.isUnsatisfiable headCombo)
          = some (XorSatVerdict.isSatisfiable witnessTrueSet) := hrun
      exact XorSatVerdict.noConfusion (Option.some.inj hsome)
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
        :: tailItems, hwf, witnessTrueSet, hrun => by
      have hheadWf : xorSatIsStrictlyAscending (pivotVar :: pivotRestVars) = true :=
        xorSatAndElimLeft _ _ hwf
      have htailWf : xorSatWorkIsWellFormed tailItems = true := xorSatAndElimRight _ _ hwf
      rw [xorSatDecideAuxPivot] at hrun
      cases hrec : xorSatDecideAux remainingFuel
          (xorSatPivotTransform pivotVar
            (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
            tailItems) with
      | none =>
          rw [hrec] at hrun
          have hnone : (none : Option XorSatVerdict)
              = some (XorSatVerdict.isSatisfiable witnessTrueSet) := hrun
          exact False.elim (xorSatNoneNeSome _ hnone)
      | some recVerdict =>
          rw [hrec] at hrun
          cases recVerdict with
          | isUnsatisfiable recCombo =>
              have hsome : some (XorSatVerdict.isUnsatisfiable recCombo)
                  = some (XorSatVerdict.isSatisfiable witnessTrueSet) := hrun
              exact XorSatVerdict.noConfusion (Option.some.inj hsome)
          | isSatisfiable recWitnessSet =>
              have hsome : some (XorSatVerdict.isSatisfiable
                  (xorSatExtendWitness pivotVar
                    (xorSatBoolXor headParity
                      (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                    recWitnessSet))
                  = some (XorSatVerdict.isSatisfiable witnessTrueSet) := hrun
              have hwitness : xorSatExtendWitness pivotVar
                  (xorSatBoolXor headParity
                    (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                  recWitnessSet = witnessTrueSet :=
                XorSatVerdict.isSatisfiable.inj (Option.some.inj hsome)
              have hrecCheck := xorSatDecideAuxSatSound remainingFuel
                (xorSatPivotTransform pivotVar
                  (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
                  tailItems)
                (xorSatPivotTransformPreservesWellFormed pivotVar
                  (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
                  tailItems htailWf)
                recWitnessSet hrec
              have hpivotAbsent : xorSatHasMember pivotVar pivotRestVars = false :=
                xorSatHasMemberNotBelow pivotVar pivotRestVars
                  (xorSatAndElimLeft _ _ hheadWf) (xorSatAndElimRight _ _ hheadWf)
              have hAgree : ∀ offVar : Nat, xorSatNatEqb offVar pivotVar = false →
                  xorSatEnvOfWitness witnessTrueSet offVar
                    = xorSatEnvOfWitness recWitnessSet offVar := by
                intro offVar hne
                rw [← hwitness]
                exact xorSatEnvExtendAtOther pivotVar
                  (xorSatBoolXor headParity
                    (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                  recWitnessSet offVar hne
              have hpivotRead : xorSatEnvOfWitness witnessTrueSet pivotVar
                  = xorSatBoolXor headParity
                      (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars) := by
                rw [← hwitness]
                exact xorSatEnvExtendAtPivot pivotVar
                  (xorSatBoolXor headParity
                    (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                  recWitnessSet
              have hrestFold : xorSatXorFold (xorSatEnvOfWitness witnessTrueSet) pivotRestVars
                  = xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars :=
                xorSatXorFoldAgreeOffPivot pivotVar
                  (xorSatEnvOfWitness witnessTrueSet) (xorSatEnvOfWitness recWitnessSet)
                  hAgree pivotRestVars hpivotAbsent
              have hheadHolds : xorSatEvalEquation (xorSatEnvOfWitness witnessTrueSet)
                  (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) = true := by
                show xorSatBoolEq
                    (xorSatBoolXor (xorSatEnvOfWitness witnessTrueSet pivotVar)
                      (xorSatXorFold (xorSatEnvOfWitness witnessTrueSet) pivotRestVars))
                    headParity = true
                rw [hpivotRead, hrestFold, xorSatBoolXorAssoc, xorSatBoolXorSelfFalse,
                    xorSatBoolXorFalseRight]
                exact xorSatBoolEqRefl headParity
              have htailCheck : xorSatCheckWork (xorSatEnvOfWitness witnessTrueSet)
                  tailItems = true :=
                xorSatBackSubstituteTail pivotVar
                  (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
                  (xorSatEnvOfWitness recWitnessSet) (xorSatEnvOfWitness witnessTrueSet)
                  hAgree hheadWf
                  (xorSatHasMemberConsOfEq pivotVar pivotVar pivotRestVars
                    (xorSatCompareNatRefl pivotVar))
                  hheadHolds tailItems htailWf hrecCheck
              show (xorSatEvalEquation (xorSatEnvOfWitness witnessTrueSet)
                    (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity)
                  && xorSatCheckWork (xorSatEnvOfWitness witnessTrueSet) tailItems) = true
              exact xorSatAndIntro _ _ hheadHolds htailCheck

/-! ## UNSAT soundness of the fuel decider -/

/-- A returned unsatisfiability combo selects original equations xoring to the literal
contradiction `⟨[], true⟩`. -/
theorem xorSatDecideAuxUnsatSound (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true) :
    (fuel : Nat) → (workingItems : List XorSatWorkItem) →
    xorSatWorkHasProvenance system workingItems →
    (comboIndices : List Nat) →
    xorSatDecideAux fuel workingItems
      = some (XorSatVerdict.isUnsatisfiable comboIndices) →
    xorSatSelectXor comboIndices system = xorSatContradictionEquation
  | 0, [], _hprov, comboIndices, hrun => by
      have hsome : some (XorSatVerdict.isSatisfiable [])
          = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
      exact XorSatVerdict.noConfusion (Option.some.inj hsome)
  | 0, _headItem :: _tailItems, _hprov, comboIndices, hrun => by
      have hnone : (none : Option XorSatVerdict)
          = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
      exact False.elim (xorSatNoneNeSome _ hnone)
  | Nat.succ _remainingFuel, [], _hprov, comboIndices, hrun => by
      have hsome : some (XorSatVerdict.isSatisfiable [])
          = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
      exact XorSatVerdict.noConfusion (Option.some.inj hsome)
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] false) _headCombo :: tailItems,
      hprov, comboIndices, hrun => by
      obtain ⟨_hheadProv, hrestProv⟩ := hprov
      rw [xorSatDecideAuxDrop] at hrun
      exact xorSatDecideAuxUnsatSound system hSystemWf remainingFuel tailItems hrestProv
        comboIndices hrun
  | Nat.succ _remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk [] true) headCombo :: _tailItems,
      hprov, comboIndices, hrun => by
      obtain ⟨⟨hheadEq, _hheadAsc⟩, _hrestProv⟩ := hprov
      have hsome : some (XorSatVerdict.isUnsatisfiable headCombo)
          = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
      have hcombo : headCombo = comboIndices :=
        XorSatVerdict.isUnsatisfiable.inj (Option.some.inj hsome)
      rw [← hcombo]
      exact hheadEq.symm
  | Nat.succ remainingFuel,
      XorSatWorkItem.mk (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
        :: tailItems, hprov, comboIndices, hrun => by
      obtain ⟨⟨hheadEq, hheadAsc⟩, hrestProv⟩ := hprov
      rw [xorSatDecideAuxPivot] at hrun
      cases hrec : xorSatDecideAux remainingFuel
          (xorSatPivotTransform pivotVar
            (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
            tailItems) with
      | none =>
          rw [hrec] at hrun
          have hnone : (none : Option XorSatVerdict)
              = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
          exact False.elim (xorSatNoneNeSome _ hnone)
      | some recVerdict =>
          rw [hrec] at hrun
          cases recVerdict with
          | isSatisfiable recWitnessSet =>
              have hsome : some (XorSatVerdict.isSatisfiable
                  (xorSatExtendWitness pivotVar
                    (xorSatBoolXor headParity
                      (xorSatXorFold (xorSatEnvOfWitness recWitnessSet) pivotRestVars))
                    recWitnessSet))
                  = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
              exact XorSatVerdict.noConfusion (Option.some.inj hsome)
          | isUnsatisfiable recCombo =>
              have hsome : some (XorSatVerdict.isUnsatisfiable recCombo)
                  = some (XorSatVerdict.isUnsatisfiable comboIndices) := hrun
              have hcombo : recCombo = comboIndices :=
                XorSatVerdict.isUnsatisfiable.inj (Option.some.inj hsome)
              have htransProv := xorSatPivotTransformPreservesProvenance system hSystemWf
                pivotVar (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity)
                headCombo hheadEq hheadAsc tailItems hrestProv
              rw [← hcombo]
              exact xorSatDecideAuxUnsatSound system hSystemWf remainingFuel
                (xorSatPivotTransform pivotVar
                  (XorSatEquation.mk (pivotVar :: pivotRestVars) headParity) headCombo
                  tailItems)
                htransProv recCombo hrec

/-! ## The initial working set and the top-level decision -/

/-- Pair each equation of a suffix with its singleton provenance combo. -/
def xorSatInitialWorkFrom : Nat → List XorSatEquation → List XorSatWorkItem
  | _startIndex, [] => []
  | startIndex, equation :: restEquations =>
      { equation := equation, comboIndices := [startIndex] }
        :: xorSatInitialWorkFrom (startIndex + 1) restEquations

theorem xorSatInitialWorkIsWellFormed : (suffixEquations : List XorSatEquation) →
    (startIndex : Nat) →
    xorSatSystemIsWellFormed suffixEquations = true →
    xorSatWorkIsWellFormed (xorSatInitialWorkFrom startIndex suffixEquations) = true
  | [], _startIndex, _hwf => rfl
  | _equation :: restEquations, startIndex, hwf =>
      xorSatAndIntro _ _ (xorSatAndElimLeft _ _ hwf)
        (xorSatInitialWorkIsWellFormed restEquations (startIndex + 1)
          (xorSatAndElimRight _ _ hwf))

/-- Checking the initial working set is checking the system. -/
theorem xorSatCheckWorkInitial (env : Nat → Bool) : (suffixEquations : List XorSatEquation) →
    (startIndex : Nat) →
    xorSatCheckWork env (xorSatInitialWorkFrom startIndex suffixEquations)
      = xorSatEvalSystem env suffixEquations
  | [], _startIndex => rfl
  | equation :: restEquations, startIndex => by
      show (xorSatEvalEquation env equation
          && xorSatCheckWork env (xorSatInitialWorkFrom (startIndex + 1) restEquations))
        = (xorSatEvalEquation env equation && xorSatEvalSystem env restEquations)
      rw [xorSatCheckWorkInitial env restEquations (startIndex + 1)]

/-- The initial working set has provenance: each equation IS its singleton selection. -/
theorem xorSatInitialWorkHasProvenance (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true) :
    (suffixEquations : List XorSatEquation) → (startIndex : Nat) →
    (∀ offset : Nat,
      xorSatGetEquation offset suffixEquations
        = xorSatGetEquation (startIndex + offset) system) →
    xorSatWorkHasProvenance system (xorSatInitialWorkFrom startIndex suffixEquations)
  | [], _startIndex, _hAgree => True.intro
  | equation :: restEquations, startIndex, hAgree => by
      refine ⟨⟨?_, rfl⟩, ?_⟩
      · have hget : xorSatGetEquation startIndex system = equation := (hAgree 0).symm
        have hwfEquation : xorSatEquationIsWellFormed equation = true := by
          rw [← hget]
          exact xorSatGetEquationIsWellFormed startIndex system hSystemWf
        show equation
          = xorSatCombine (xorSatGetEquation startIndex system) xorSatZeroEquation
        rw [hget, xorSatCombineZeroRight equation hwfEquation]
      · refine xorSatInitialWorkHasProvenance system hSystemWf restEquations
          (startIndex + 1) ?_
        intro offset
        have hshift := hAgree (offset + 1)
        have harith : startIndex + (offset + 1) = (startIndex + 1) + offset :=
          (xorSatNatSuccAdd startIndex offset).symm
        exact hshift.trans
          (congrArg (fun shiftedIndex => xorSatGetEquation shiftedIndex system) harith)

/-- The top-level decision: eliminate with fuel equal to the working count; the fallback arm
is provably dead (`xorSatDecideTotalFuelAdequate`). -/
def xorSatDecide (system : List XorSatEquation) : XorSatVerdict :=
  match xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
      (xorSatInitialWorkFrom 0 system) with
  | some verdict => verdict
  | none => XorSatVerdict.isUnsatisfiable []

/-- The executable SAT checker: does the induced environment satisfy the whole system? -/
def xorSatCheckSystem (witnessTrueSet : List Nat) (system : List XorSatEquation) : Bool :=
  xorSatEvalSystem (xorSatEnvOfWitness witnessTrueSet) system

/-- Totality certificate: at fuel equal to the working count the fuel decider delivers a
verdict, so `xorSatDecide`'s fallback arm is dead code. -/
theorem xorSatDecideTotalFuelAdequate (system : List XorSatEquation) :
    xorSatIsSomeVerdict
      (xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
        (xorSatInitialWorkFrom 0 system)) = true :=
  xorSatDecideAuxIsSome (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
    (xorSatInitialWorkFrom 0 system) rfl

/-! ## Headline theorem 1: SAT soundness -/

/-- A witness returned by `xorSatDecide` passes the executable checker. -/
theorem xorSatDecideSatSound (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true)
    (witnessTrueSet : List Nat)
    (hverdict : xorSatDecide system = XorSatVerdict.isSatisfiable witnessTrueSet) :
    xorSatCheckSystem witnessTrueSet system = true := by
  cases hrec : xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
      (xorSatInitialWorkFrom 0 system) with
  | none =>
      have hsome := xorSatDecideTotalFuelAdequate system
      rw [hrec] at hsome
      exact Bool.noConfusion hsome
  | some verdict =>
      have hdecide : xorSatDecide system = verdict := by
        show (match xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
              (xorSatInitialWorkFrom 0 system) with
          | some innerVerdict => innerVerdict
          | none => XorSatVerdict.isUnsatisfiable []) = verdict
        rw [hrec]
      have hrun : xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
          (xorSatInitialWorkFrom 0 system)
          = some (XorSatVerdict.isSatisfiable witnessTrueSet) := by
        rw [hrec, hdecide.symm.trans hverdict]
      have hcheckWork := xorSatDecideAuxSatSound
        (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
        (xorSatInitialWorkFrom 0 system)
        (xorSatInitialWorkIsWellFormed system 0 hSystemWf)
        witnessTrueSet hrun
      show xorSatEvalSystem (xorSatEnvOfWitness witnessTrueSet) system = true
      rw [← xorSatCheckWorkInitial (xorSatEnvOfWitness witnessTrueSet) system 0]
      exact hcheckWork

/-- Checker-eval agreement: a passing checker means every equation (by index; out of
range reads as the zero equation) holds under the induced environment. -/
theorem xorSatCheckSystemHoldsEachEquation (witnessTrueSet : List Nat)
    (system : List XorSatEquation)
    (hcheck : xorSatCheckSystem witnessTrueSet system = true) (index : Nat) :
    xorSatEvalEquation (xorSatEnvOfWitness witnessTrueSet)
      (xorSatGetEquation index system) = true :=
  xorSatEvalSystemGet (xorSatEnvOfWitness witnessTrueSet) index system hcheck

/-! ## Headline theorem 2: UNSAT soundness -/

/-- A combo returned by `xorSatDecide` selects original equations whose F2 xor is the
literal contradiction `⟨[], true⟩`. -/
theorem xorSatDecideUnsatSound (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true)
    (comboIndices : List Nat)
    (hverdict : xorSatDecide system = XorSatVerdict.isUnsatisfiable comboIndices) :
    xorSatSelectXor comboIndices system = xorSatContradictionEquation := by
  cases hrec : xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
      (xorSatInitialWorkFrom 0 system) with
  | none =>
      have hsome := xorSatDecideTotalFuelAdequate system
      rw [hrec] at hsome
      exact Bool.noConfusion hsome
  | some verdict =>
      have hdecide : xorSatDecide system = verdict := by
        show (match xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
              (xorSatInitialWorkFrom 0 system) with
          | some innerVerdict => innerVerdict
          | none => XorSatVerdict.isUnsatisfiable []) = verdict
        rw [hrec]
      have hrun : xorSatDecideAux (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
          (xorSatInitialWorkFrom 0 system)
          = some (XorSatVerdict.isUnsatisfiable comboIndices) := by
        rw [hrec, hdecide.symm.trans hverdict]
      exact xorSatDecideAuxUnsatSound system hSystemWf
        (xorSatWorkCount (xorSatInitialWorkFrom 0 system))
        (xorSatInitialWorkFrom 0 system)
        (xorSatInitialWorkHasProvenance system hSystemWf system 0
          (fun offset =>
            (congrArg (fun shiftedIndex => xorSatGetEquation shiftedIndex system)
              (Nat.zero_add offset)).symm))
        comboIndices hrun

/-- The refutation: an UNSAT verdict rules out every candidate model — any environment
satisfying the system would satisfy the selected xor, which is `0 = 1`. -/
theorem xorSatDecideUnsatRefutes (system : List XorSatEquation)
    (hSystemWf : xorSatSystemIsWellFormed system = true)
    (comboIndices : List Nat)
    (hverdict : xorSatDecide system = XorSatVerdict.isUnsatisfiable comboIndices)
    (env : Nat → Bool)
    (hsat : xorSatEvalSystem env system = true) : False := by
  have hselect := xorSatSelectXorSatisfied env comboIndices system hsat
  rw [xorSatDecideUnsatSound system hSystemWf comboIndices hverdict] at hselect
  exact Bool.noConfusion hselect

/-! ## Verdict extractors and the executable unsat-certificate checker -/

/-- Is the verdict a satisfiability verdict? -/
def xorSatVerdictIsSatisfiable : XorSatVerdict → Bool
  | XorSatVerdict.isSatisfiable _witnessTrueSet => true
  | XorSatVerdict.isUnsatisfiable _comboIndices => false

/-- The witness true-set of a SAT verdict (empty on UNSAT). -/
def xorSatVerdictWitnessSet : XorSatVerdict → List Nat
  | XorSatVerdict.isSatisfiable witnessTrueSet => witnessTrueSet
  | XorSatVerdict.isUnsatisfiable _comboIndices => []

/-- The certificate combo of an UNSAT verdict (empty on SAT). -/
def xorSatVerdictComboIndices : XorSatVerdict → List Nat
  | XorSatVerdict.isSatisfiable _witnessTrueSet => []
  | XorSatVerdict.isUnsatisfiable comboIndices => comboIndices

/-- Structural equality scan on variable lists. -/
def xorSatNatListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _secondHead :: _secondRest => false
  | _firstHead :: _firstRest, [] => false
  | firstHead :: firstRest, secondHead :: secondRest =>
      xorSatNatEqb firstHead secondHead && xorSatNatListBeq firstRest secondRest

/-- Structural equality of equations. -/
def xorSatEquationBeq (first second : XorSatEquation) : Bool :=
  xorSatNatListBeq first.variables second.variables
    && xorSatBoolEq first.parity second.parity

/-- Executable UNSAT-certificate checker: does the selected xor equal `0 = 1`? -/
def xorSatCheckUnsatCombo (comboIndices : List Nat) (system : List XorSatEquation) : Bool :=
  xorSatEquationBeq (xorSatSelectXor comboIndices system) xorSatContradictionEquation

/-! ## Marker -/

/-- XOR-SAT is decided on this island: fuel-adequate Gaussian-style elimination with
back-substitution, provenance-tracked two-sided certificates, checker-eval agreement, and
the literal-contradiction UNSAT selection — all zero-axiom. -/
def fxDissatIsland_hasXorSatDecision : Bool := true

/-! ## Genuineness smokes (SAT, UNSAT, and FALSE checker cases) -/

-- Satisfiable pair: x0 + x1 = 1; x1 = 1.  Witness [1] (x1 true, x0 false).
#eval xorSatVerdictIsSatisfiable (xorSatDecide
  [{ variables := [0, 1], parity := true }, { variables := [1], parity := true }])
#eval xorSatVerdictWitnessSet (xorSatDecide
  [{ variables := [0, 1], parity := true }, { variables := [1], parity := true }])
#eval xorSatCheckSystem
  (xorSatVerdictWitnessSet (xorSatDecide
    [{ variables := [0, 1], parity := true }, { variables := [1], parity := true }]))
  [{ variables := [0, 1], parity := true }, { variables := [1], parity := true }]

-- The classic UNSAT triple: x+y = 1, y+z = 1, x+z = 1 — the three xor to 0 = 1.
#eval xorSatVerdictIsSatisfiable (xorSatDecide
  [{ variables := [0, 1], parity := true }, { variables := [1, 2], parity := true },
   { variables := [0, 2], parity := true }])
#eval xorSatVerdictComboIndices (xorSatDecide
  [{ variables := [0, 1], parity := true }, { variables := [1, 2], parity := true },
   { variables := [0, 2], parity := true }])
#eval xorSatCheckUnsatCombo
  (xorSatVerdictComboIndices (xorSatDecide
    [{ variables := [0, 1], parity := true }, { variables := [1, 2], parity := true },
     { variables := [0, 2], parity := true }]))
  [{ variables := [0, 1], parity := true }, { variables := [1, 2], parity := true },
   { variables := [0, 2], parity := true }]

-- A single bare contradiction 0 = 1: UNSAT with certificate [0].
#eval xorSatVerdictIsSatisfiable (xorSatDecide [{ variables := [], parity := true }])
#eval xorSatVerdictComboIndices (xorSatDecide [{ variables := [], parity := true }])
#eval xorSatCheckUnsatCombo [0] [{ variables := [], parity := true }]

-- The empty system: satisfiable with the all-false witness [].
#eval xorSatVerdictIsSatisfiable (xorSatDecide [])
#eval xorSatVerdictWitnessSet (xorSatDecide [])
#eval xorSatCheckSystem [] []

-- Redundant but satisfiable: x0 + x1 = 0 twice; witness sets both false.
#eval xorSatVerdictIsSatisfiable (xorSatDecide
  [{ variables := [0, 1], parity := false }, { variables := [0, 1], parity := false }])
#eval xorSatCheckSystem
  (xorSatVerdictWitnessSet (xorSatDecide
    [{ variables := [0, 1], parity := false }, { variables := [0, 1], parity := false }]))
  [{ variables := [0, 1], parity := false }, { variables := [0, 1], parity := false }]

-- FALSE checker cases: wrong witnesses and wrong certificates are rejected.
#eval xorSatCheckSystem [0] [{ variables := [0], parity := false }]
#eval xorSatCheckSystem [] [{ variables := [0, 1], parity := true },
  { variables := [1], parity := true }]
#eval xorSatCheckUnsatCombo [0] [{ variables := [0, 1], parity := true },
  { variables := [1, 2], parity := true }, { variables := [0, 2], parity := true }]
#eval xorSatCheckUnsatCombo [0, 1] [{ variables := [0, 1], parity := true },
  { variables := [1, 2], parity := true }, { variables := [0, 2], parity := true }]

end FX1Poly.ComputerAlgebra
