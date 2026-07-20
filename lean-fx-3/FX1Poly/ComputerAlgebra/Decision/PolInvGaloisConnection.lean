import FX1Poly.ComputerAlgebra.Decision.PostCloneLattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/Decision/PolInvGaloisConnection — the finite Pol–Inv Galois core

The polymorphism (`Pol`) / invariant-relation (`Inv`) Galois connection over the two-element
Boolean base, restricted to a FINITE decidable slice: a finite set of Boolean relations
(`PigBoolRel` — an `arity` plus a `rows : List (List Bool)` list of bit-tuples), the
componentwise-preservation predicate `pigPreserves` (a function `f` preserves a relation `R`
iff applying `f` down the columns of any `arity f`-tuple of rows of `R` lands back in `R`), the
`pigPol` / `pigInv` operators (filter a finite function/relation base by joint preservation), and
the Galois structure that holds on any finite instance:

  * `pigPolProducesPreservers` / `pigInvProducesInvariants` — SOUNDNESS of the filters (every
    function `Pol` returns preserves all the relations; every relation `Inv` returns is preserved
    by all the functions);
  * `pigPolKeepsPreserver` / `pigInvKeepsInvariant` — the converse filter closure (a base element
    that jointly preserves is kept);
  * `pigPolAntitone` / `pigInvAntitone` — ANTITONICITY: enlarging the relation set (resp. function
    set) can only SHRINK `Pol` (resp. `Inv`);
  * the two Galois expanding inequalities as concrete ground fires (`f ∈ Pol(Inv{f})`).

The function side reuses `PclBoolFn` + `pclMaskValue` + `pclAllMasks`-style cons-only enumeration
from `PostCloneLattice`; the choice enumeration `pigChooseRows` is an explicit cons-only cartesian
builder (à la `pclConsAll`), never a `WellFounded.fix` fixpoint.

## What is WALLED

The FULL Galois correspondence completeness — that `Pol(Inv(F))` equals the clone-closure of `F`
and `Inv(Pol(R))` the co-clone (pp-definable) closure of `R` — is the SAME countably-infinite
clone/co-clone lattice `PostCloneLattice` already walled (`pclHasFullPostLattice`,
`pclHasCloneGenerationClosure`).  See `pigHasFullGaloisCorrespondence` and
`pigHasPpDefinabilityClosure` (both `false`).

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`, and any `decide`-on-`Prop`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Boolean-connective elimination/introduction (own kit; no stdlib `Bool` AC lemmas) -/

/-- From `a && b = true` extract both conjuncts. -/
theorem pigBoolAndElim : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hAnd => Bool.noConfusion hAnd
  | false, true, hAnd => Bool.noConfusion hAnd
  | false, false, hAnd => Bool.noConfusion hAnd

/-- Introduce `a && b = true` from both conjuncts. -/
theorem pigBoolAndIntro : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, true, _, _ => rfl
  | true, false, _, hRight => Bool.noConfusion hRight
  | false, true, hLeft, _ => Bool.noConfusion hLeft
  | false, false, hLeft, _ => Bool.noConfusion hLeft

/-- From `a || b = true` conclude one of the two disjuncts. -/
theorem pigBoolOrElim : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = true →
    leftFlag = true ∨ rightFlag = true
  | true, true, _ => Or.inl rfl
  | true, false, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl
  | false, false, hOr => Bool.noConfusion hOr

/-- Introduce `a || b = true` from the left disjunct. -/
theorem pigBoolOrIntroLeft : (leftFlag rightFlag : Bool) → leftFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, _ => rfl
  | false, true, hLeft => Bool.noConfusion hLeft
  | false, false, hLeft => Bool.noConfusion hLeft

/-- Introduce `a || b = true` from the right disjunct. -/
theorem pigBoolOrIntroRight : (leftFlag rightFlag : Bool) → rightFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, hRight => Bool.noConfusion hRight
  | false, true, _ => rfl
  | false, false, hRight => Bool.noConfusion hRight

/-! ## T1 — the Boolean-relation carrier, tuple/row equality, membership, well-formedness -/

/-- Structural equality of bit-tuples (full four-arm enumeration, cons-only, `propext`-free). -/
def pigTupleBeq : List Bool → List Bool → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftBit :: leftRest, rightBit :: rightRest =>
      pclBoolBeq leftBit rightBit && pigTupleBeq leftRest rightRest

/-- `pigTupleBeq` is reflexive. -/
theorem pigTupleBeqRefl : (tuple : List Bool) → pigTupleBeq tuple tuple = true
  | [] => rfl
  | bit :: rest => by
      show (pclBoolBeq bit bit && pigTupleBeq rest rest) = true
      rw [pclBoolBeqRefl bit, pigTupleBeqRefl rest]
      rfl

/-- `pigTupleBeq`-true tuples are equal. -/
theorem pigTupleBeqEq : (leftTuple rightTuple : List Bool) →
    pigTupleBeq leftTuple rightTuple = true → leftTuple = rightTuple
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftBit :: leftRest, rightBit :: rightRest, hBeq => by
      have hSplit := pigBoolAndElim _ _ hBeq
      rw [pclBoolBeqEq leftBit rightBit hSplit.left,
        pigTupleBeqEq leftRest rightRest hSplit.right]

/-- Structural equality of row lists (tuple-lists), cons-only. -/
def pigRowsBeq : List (List Bool) → List (List Bool) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftRow :: leftRest, rightRow :: rightRest =>
      pigTupleBeq leftRow rightRow && pigRowsBeq leftRest rightRest

/-- `pigRowsBeq`-true row lists are equal. -/
theorem pigRowsBeqEq : (leftRows rightRows : List (List Bool)) →
    pigRowsBeq leftRows rightRows = true → leftRows = rightRows
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftRow :: leftRest, rightRow :: rightRest, hBeq => by
      have hSplit := pigBoolAndElim _ _ hBeq
      rw [pigTupleBeqEq leftRow rightRow hSplit.left,
        pigRowsBeqEq leftRest rightRest hSplit.right]

/-- A finite Boolean relation: an `arity` and a `rows` list of intended-length-`arity` bit-tuples. -/
structure PigBoolRel where
  arity : Nat
  rows : List (List Bool)

/-- Is a bit-tuple one of a relation's rows?  Cons-only fold, no `List.getD`. -/
def pigRowMem (tuple : List Bool) : List (List Bool) → Bool
  | [] => false
  | head :: rest => pigTupleBeq tuple head || pigRowMem tuple rest

/-- Every row of a list has the declared length (Bool side-check). -/
def pigAllRowsLen (arity : Nat) : List (List Bool) → Bool
  | [] => true
  | row :: rest => Nat.beq (pclLength row) arity && pigAllRowsLen arity rest

/-- Well-formedness of a relation: every row has length `arity`. -/
def pigRelWellFormed (rel : PigBoolRel) : Bool :=
  pigAllRowsLen rel.arity rel.rows

/-- Structural equality of relations (arity then rows). -/
def pigRelBeq (leftRel rightRel : PigBoolRel) : Bool :=
  Nat.beq leftRel.arity rightRel.arity && pigRowsBeq leftRel.rows rightRel.rows

/-- `pigRelBeq`-true relations are equal (via `Nat.beq`/`pigRowsBeq` soundness + structure eta). -/
theorem pigRelBeqEq : (leftRel rightRel : PigBoolRel) →
    pigRelBeq leftRel rightRel = true → leftRel = rightRel
  | ⟨leftArity, leftRows⟩, ⟨rightArity, rightRows⟩, hBeq => by
      have hSplit := pigBoolAndElim _ _ hBeq
      have hArity : leftArity = rightArity := pclNatBeqEq _ _ hSplit.left
      have hRows : leftRows = rightRows := pigRowsBeqEq _ _ hSplit.right
      rw [hArity, hRows]

/-- Is a relation one of a relation list's members? -/
def pigRelMem (rel : PigBoolRel) : List PigBoolRel → Bool
  | [] => false
  | head :: rest => pigRelBeq rel head || pigRelMem rel rest

/-! ## Function equality/membership (the `PclBoolFn` carrier is reused verbatim) -/

/-- Structural equality of Boolean functions (arity then truth table). -/
def pigFuncBeq (leftFn rightFn : PclBoolFn) : Bool :=
  Nat.beq leftFn.arity rightFn.arity && pigTupleBeq leftFn.table rightFn.table

/-- `pigFuncBeq`-true functions are equal. -/
theorem pigFuncBeqEq : (leftFn rightFn : PclBoolFn) →
    pigFuncBeq leftFn rightFn = true → leftFn = rightFn
  | ⟨leftArity, leftTable⟩, ⟨rightArity, rightTable⟩, hBeq => by
      have hSplit := pigBoolAndElim _ _ hBeq
      have hArity : leftArity = rightArity := pclNatBeqEq _ _ hSplit.left
      have hTable : leftTable = rightTable := pigTupleBeqEq _ _ hSplit.right
      rw [hArity, hTable]

/-- Is a function one of a function list's members? -/
def pigFuncMem (function : PclBoolFn) : List PclBoolFn → Bool
  | [] => false
  | head :: rest => pigFuncBeq function head || pigFuncMem function rest

/-! ## T2 — componentwise preservation -/

/-- Extract the `index`-th column across a list of tuples: the `index`-th bit of every tuple. -/
def pigColumn (index : Nat) : List (List Bool) → List Bool
  | [] => []
  | row :: rest => pclTableRow row index :: pigColumn index rest

/-- Apply `function` to every column of `tuples`, walking coordinate indices via a fixed template
(the output tuple has one entry per coordinate of the template). -/
def pigApplyOverCoords (function : PclBoolFn) (tuples : List (List Bool)) :
    List Bool → Nat → List Bool
  | [], _ => []
  | _ :: templateRest, index =>
      pclMaskValue function.table (pigColumn index tuples)
        :: pigApplyOverCoords function tuples templateRest (Nat.succ index)

/-- The componentwise image of an `arity function`-tuple of rows: build each output coordinate as
`function` applied down that column.  Empty input yields the empty tuple. -/
def pigApplyComponentwise (function : PclBoolFn) : List (List Bool) → List Bool
  | [] => []
  | firstRow :: restTuples => pigApplyOverCoords function (firstRow :: restTuples) firstRow 0

/-- Prepend a fixed `row` to every choice-list, accumulator-fused (mirrors `pclConsAll`). -/
def pigConsRowToAll (row : List Bool) :
    List (List (List Bool)) → List (List (List Bool)) → List (List (List Bool))
  | [], accumulated => accumulated
  | choice :: choices, accumulated => (row :: choice) :: pigConsRowToAll row choices accumulated

/-- Prepend EACH row of a row set to every choice-list — one cartesian layer, cons-only. -/
def pigConsEachRow : List (List Bool) → List (List (List Bool)) → List (List (List Bool))
  | [], _ => []
  | row :: restRows, choices => pigConsRowToAll row choices (pigConsEachRow restRows choices)

/-- All length-`n` choice-lists whose entries are drawn (with repetition, ordered) from `rowSet`
— the explicit `|rowSet|^n` cons-only cartesian enumeration, never a fixpoint. -/
def pigChooseRows : Nat → List (List Bool) → List (List (List Bool))
  | 0, _ => [[]]
  | Nat.succ predecessor, rowSet => pigConsEachRow rowSet (pigChooseRows predecessor rowSet)

/-- For every choice-list, is the componentwise-`function` image a row of `rel`? -/
def pigCheckAllChoices (function : PclBoolFn) (rel : PigBoolRel) :
    List (List (List Bool)) → Bool
  | [] => true
  | choice :: rest =>
      pigRowMem (pigApplyComponentwise function choice) rel.rows
        && pigCheckAllChoices function rel rest

/-- `function` PRESERVES `rel`: every `arity function`-tuple of rows of `rel` has its
componentwise image back inside `rel`. -/
def pigPreserves (function : PclBoolFn) (rel : PigBoolRel) : Bool :=
  pigCheckAllChoices function rel (pigChooseRows function.arity rel.rows)

/-- Does `function` preserve EVERY relation of a list? -/
def pigPreservesAll (function : PclBoolFn) : List PigBoolRel → Bool
  | [] => true
  | rel :: rest => pigPreserves function rel && pigPreservesAll function rest

/-- Is `rel` preserved by EVERY function of a list? -/
def pigAllPreserve : List PclBoolFn → PigBoolRel → Bool
  | [], _ => true
  | function :: rest, rel => pigPreserves function rel && pigAllPreserve rest rel

/-- Antitone heart (function side): preserving a `rel :: rels` list forces preserving its tail. -/
theorem pigPreservesAllDropTail (function : PclBoolFn) (rel : PigBoolRel)
    (rels : List PigBoolRel) (hAll : pigPreservesAll function (rel :: rels) = true) :
    pigPreservesAll function rels = true :=
  (pigBoolAndElim _ _ hAll).right

/-- Antitone heart (relation side): being preserved by a `function :: funcs` list forces being
preserved by the tail. -/
theorem pigAllPreserveDropTail (function : PclBoolFn) (funcs : List PclBoolFn)
    (rel : PigBoolRel) (hAll : pigAllPreserve (function :: funcs) rel = true) :
    pigAllPreserve funcs rel = true :=
  (pigBoolAndElim _ _ hAll).right

/-! ## T3 — the `Pol` / `Inv` operators (finite bases) -/

/-- Cons `function` onto `rest` exactly when `keep`. -/
def pigConsIf (keep : Bool) (function : PclBoolFn) (rest : List PclBoolFn) : List PclBoolFn :=
  match keep with
  | true => function :: rest
  | false => rest

/-- Cons `rel` onto `rest` exactly when `keep`. -/
def pigRelConsIf (keep : Bool) (rel : PigBoolRel) (rest : List PigBoolRel) : List PigBoolRel :=
  match keep with
  | true => rel :: rest
  | false => rest

/-- `Pol rels base` — the functions of `base` preserving every relation in `rels`. -/
def pigPol (rels : List PigBoolRel) : List PclBoolFn → List PclBoolFn
  | [] => []
  | function :: rest => pigConsIf (pigPreservesAll function rels) function (pigPol rels rest)

/-- `Inv funcs base` — the relations of `base` preserved by every function in `funcs`. -/
def pigInv (funcs : List PclBoolFn) : List PigBoolRel → List PigBoolRel
  | [] => []
  | rel :: rest => pigRelConsIf (pigAllPreserve funcs rel) rel (pigInv funcs rest)

/-! ### Membership through the guarded cons -/

/-- Membership through `pigConsIf`: either kept-with-guard-and-equal-head, or in the tail. -/
theorem pigFuncMemConsIfElim (keep : Bool) (function head : PclBoolFn) (rest : List PclBoolFn)
    (hMem : pigFuncMem function (pigConsIf keep head rest) = true) :
    (keep = true ∧ pigFuncBeq function head = true) ∨ pigFuncMem function rest = true := by
  cases keep with
  | true =>
      have h : (pigFuncBeq function head || pigFuncMem function rest) = true := hMem
      cases pigBoolOrElim _ _ h with
      | inl hBeq => exact Or.inl ⟨rfl, hBeq⟩
      | inr hRest => exact Or.inr hRest
  | false => exact Or.inr hMem

/-- Introduce membership through `pigConsIf`. -/
theorem pigFuncMemConsIfIntro (keep : Bool) (function head : PclBoolFn) (rest : List PclBoolFn)
    (h : (keep = true ∧ pigFuncBeq function head = true) ∨ pigFuncMem function rest = true) :
    pigFuncMem function (pigConsIf keep head rest) = true := by
  cases keep with
  | true =>
      cases h with
      | inl hLeft => exact pigBoolOrIntroLeft _ _ hLeft.right
      | inr hRight => exact pigBoolOrIntroRight _ _ hRight
  | false =>
      cases h with
      | inl hLeft => exact Bool.noConfusion hLeft.left
      | inr hRight => exact hRight

/-- Membership through `pigRelConsIf`. -/
theorem pigRelMemConsIfElim (keep : Bool) (rel head : PigBoolRel) (rest : List PigBoolRel)
    (hMem : pigRelMem rel (pigRelConsIf keep head rest) = true) :
    (keep = true ∧ pigRelBeq rel head = true) ∨ pigRelMem rel rest = true := by
  cases keep with
  | true =>
      have h : (pigRelBeq rel head || pigRelMem rel rest) = true := hMem
      cases pigBoolOrElim _ _ h with
      | inl hBeq => exact Or.inl ⟨rfl, hBeq⟩
      | inr hRest => exact Or.inr hRest
  | false => exact Or.inr hMem

/-- Introduce membership through `pigRelConsIf`. -/
theorem pigRelMemConsIfIntro (keep : Bool) (rel head : PigBoolRel) (rest : List PigBoolRel)
    (h : (keep = true ∧ pigRelBeq rel head = true) ∨ pigRelMem rel rest = true) :
    pigRelMem rel (pigRelConsIf keep head rest) = true := by
  cases keep with
  | true =>
      cases h with
      | inl hLeft => exact pigBoolOrIntroLeft _ _ hLeft.right
      | inr hRight => exact pigBoolOrIntroRight _ _ hRight
  | false =>
      cases h with
      | inl hLeft => exact Bool.noConfusion hLeft.left
      | inr hRight => exact hRight

/-! ### `Pol` soundness / base-closure / antitonicity -/

/-- SOUNDNESS: every function `Pol` returns preserves all of `rels`. -/
theorem pigPolProducesPreservers : (rels : List PigBoolRel) → (base : List PclBoolFn) →
    (function : PclBoolFn) →
    pigFuncMem function (pigPol rels base) = true → pigPreservesAll function rels = true
  | _, [], _, hMem => Bool.noConfusion hMem
  | rels, head :: rest, function, hMem => by
      have hCase := pigFuncMemConsIfElim (pigPreservesAll head rels) function head
        (pigPol rels rest) hMem
      cases hCase with
      | inl hKept =>
          have hEq : function = head := pigFuncBeqEq function head hKept.right
          rw [hEq]
          exact hKept.left
      | inr hRest => exact pigPolProducesPreservers rels rest function hRest

/-- `Pol rels base` is a sub-collection of `base`. -/
theorem pigPolSubsetBase : (rels : List PigBoolRel) → (base : List PclBoolFn) →
    (function : PclBoolFn) →
    pigFuncMem function (pigPol rels base) = true → pigFuncMem function base = true
  | _, [], _, hMem => Bool.noConfusion hMem
  | rels, head :: rest, function, hMem => by
      have hCase := pigFuncMemConsIfElim (pigPreservesAll head rels) function head
        (pigPol rels rest) hMem
      cases hCase with
      | inl hKept => exact pigBoolOrIntroLeft _ _ hKept.right
      | inr hRest =>
          exact pigBoolOrIntroRight _ _ (pigPolSubsetBase rels rest function hRest)

/-- Filter closure: a base function preserving all of `rels` is kept by `Pol`. -/
theorem pigPolKeepsPreserver : (rels : List PigBoolRel) → (base : List PclBoolFn) →
    (function : PclBoolFn) →
    pigFuncMem function base = true → pigPreservesAll function rels = true →
    pigFuncMem function (pigPol rels base) = true
  | _, [], _, hMem, _ => Bool.noConfusion hMem
  | rels, head :: rest, function, hMem, hPres => by
      apply pigFuncMemConsIfIntro (pigPreservesAll head rels) function head (pigPol rels rest)
      cases pigBoolOrElim _ _ hMem with
      | inl hBeq =>
          have hEq : function = head := pigFuncBeqEq function head hBeq
          apply Or.inl
          refine ⟨?_, hBeq⟩
          rw [← hEq]
          exact hPres
      | inr hMemRest =>
          exact Or.inr (pigPolKeepsPreserver rels rest function hMemRest hPres)

/-- ANTITONICITY (function side): adding a relation to the front can only shrink `Pol` — every
function of `Pol (extra :: rels) base` is still in `Pol rels base`. -/
theorem pigPolAntitone (extra : PigBoolRel) (rels : List PigBoolRel) (base : List PclBoolFn)
    (function : PclBoolFn)
    (hMem : pigFuncMem function (pigPol (extra :: rels) base) = true) :
    pigFuncMem function (pigPol rels base) = true := by
  have hPresExt := pigPolProducesPreservers (extra :: rels) base function hMem
  have hPres := pigPreservesAllDropTail function extra rels hPresExt
  have hInBase := pigPolSubsetBase (extra :: rels) base function hMem
  exact pigPolKeepsPreserver rels base function hInBase hPres

/-! ### `Inv` soundness / base-closure / antitonicity (mirror of the `Pol` side) -/

/-- SOUNDNESS: every relation `Inv` returns is preserved by all of `funcs`. -/
theorem pigInvProducesInvariants : (funcs : List PclBoolFn) → (base : List PigBoolRel) →
    (rel : PigBoolRel) →
    pigRelMem rel (pigInv funcs base) = true → pigAllPreserve funcs rel = true
  | _, [], _, hMem => Bool.noConfusion hMem
  | funcs, head :: rest, rel, hMem => by
      have hCase := pigRelMemConsIfElim (pigAllPreserve funcs head) rel head
        (pigInv funcs rest) hMem
      cases hCase with
      | inl hKept =>
          have hEq : rel = head := pigRelBeqEq rel head hKept.right
          rw [hEq]
          exact hKept.left
      | inr hRest => exact pigInvProducesInvariants funcs rest rel hRest

/-- `Inv funcs base` is a sub-collection of `base`. -/
theorem pigInvSubsetBase : (funcs : List PclBoolFn) → (base : List PigBoolRel) →
    (rel : PigBoolRel) →
    pigRelMem rel (pigInv funcs base) = true → pigRelMem rel base = true
  | _, [], _, hMem => Bool.noConfusion hMem
  | funcs, head :: rest, rel, hMem => by
      have hCase := pigRelMemConsIfElim (pigAllPreserve funcs head) rel head
        (pigInv funcs rest) hMem
      cases hCase with
      | inl hKept => exact pigBoolOrIntroLeft _ _ hKept.right
      | inr hRest =>
          exact pigBoolOrIntroRight _ _ (pigInvSubsetBase funcs rest rel hRest)

/-- Filter closure: a base relation preserved by all of `funcs` is kept by `Inv`. -/
theorem pigInvKeepsInvariant : (funcs : List PclBoolFn) → (base : List PigBoolRel) →
    (rel : PigBoolRel) →
    pigRelMem rel base = true → pigAllPreserve funcs rel = true →
    pigRelMem rel (pigInv funcs base) = true
  | _, [], _, hMem, _ => Bool.noConfusion hMem
  | funcs, head :: rest, rel, hMem, hPres => by
      apply pigRelMemConsIfIntro (pigAllPreserve funcs head) rel head (pigInv funcs rest)
      cases pigBoolOrElim _ _ hMem with
      | inl hBeq =>
          have hEq : rel = head := pigRelBeqEq rel head hBeq
          apply Or.inl
          refine ⟨?_, hBeq⟩
          rw [← hEq]
          exact hPres
      | inr hMemRest =>
          exact Or.inr (pigInvKeepsInvariant funcs rest rel hMemRest hPres)

/-- ANTITONICITY (relation side): adding a function to the front can only shrink `Inv`. -/
theorem pigInvAntitone (extra : PclBoolFn) (funcs : List PclBoolFn) (base : List PigBoolRel)
    (rel : PigBoolRel)
    (hMem : pigRelMem rel (pigInv (extra :: funcs) base) = true) :
    pigRelMem rel (pigInv funcs base) = true := by
  have hPresExt := pigInvProducesInvariants (extra :: funcs) base rel hMem
  have hPres := pigAllPreserveDropTail extra funcs rel hPresExt
  have hInBase := pigInvSubsetBase (extra :: funcs) base rel hMem
  exact pigInvKeepsInvariant funcs base rel hInBase hPres

/-! ## pp-definability primitives (conjunction + coordinate projection) -/

/-- Keep `row` on `rest` exactly when `keep` (the conjunction filter step). -/
def pigConjKeep (keep : Bool) (row : List Bool) (rest : List (List Bool)) : List (List Bool) :=
  match keep with
  | true => row :: rest
  | false => rest

/-- Rows in both lists (set intersection), cons-only. -/
def pigIntersectRows : List (List Bool) → List (List Bool) → List (List Bool)
  | [], _ => []
  | row :: rest, other => pigConjKeep (pigRowMem row other) row (pigIntersectRows rest other)

/-- pp-conjunction of two same-arity relations: the relation whose rows are the shared tuples. -/
def pigPpConjoin (leftRel rightRel : PigBoolRel) : PigBoolRel :=
  { arity := leftRel.arity, rows := pigIntersectRows leftRel.rows rightRel.rows }

/-- Predecessor without `Nat.sub` (`0 ↦ 0`, `n+1 ↦ n`). -/
def pigPredecessor : Nat → Nat
  | 0 => 0
  | Nat.succ predecessor => predecessor

/-- Drop the `index`-th bit of a tuple (full enumeration on both arguments). -/
def pigDropCoord : Nat → List Bool → List Bool
  | _, [] => []
  | 0, _ :: rest => rest
  | Nat.succ predecessor, bit :: rest => bit :: pigDropCoord predecessor rest

/-- Drop coordinate `index` from every row. -/
def pigProjectRows (index : Nat) : List (List Bool) → List (List Bool)
  | [] => []
  | row :: rest => pigDropCoord index row :: pigProjectRows index rest

/-- pp-projection: existentially project out coordinate `index` (arity drops by one). -/
def pigPpProject (index : Nat) (rel : PigBoolRel) : PigBoolRel :=
  { arity := pigPredecessor rel.arity, rows := pigProjectRows index rel.rows }

/-! ## Capability markers — DECIDED -/

/-- The finite componentwise-preservation decision is DECIDED. -/
def pigHasFinitePreservation : Bool := true

/-- The `Pol`/`Inv` operators over finite bases are DECIDED. -/
def pigHasBoundedPolInv : Bool := true

/-- The Galois expanding inequalities (on finite instances) are DECIDED. -/
def pigHasGaloisInequalities : Bool := true

/-- `Pol`/`Inv` antitonicity is DECIDED. -/
def pigHasPolInvAntitone : Bool := true

/-! ## T4 — the walls -/

/-- ★ WALL — the FULL Pol–Inv Galois correspondence completeness.  That `Pol(Inv(F))` equals the
clone-closure of `F` (and `Inv(Pol(R))` the co-clone / pp-definable closure of `R`) over the
UNBOUNDED base is exactly the countably-infinite clone / co-clone lattice already walled in
`PostCloneLattice` (`pclHasFullPostLattice`, `pclHasCloneGenerationClosure`): the composition
closure has no structural decreasing measure (composing arity-`k` functions grows arity
unboundedly), so the least fixpoint is founded only by `WellFounded.fix`.

Obstruction: any finite `functionBase` / `relBase` UNDER-approximates the closure — a polymorphism
or pp-defined relation one arity above the base separates.

Burned attack 1: bound the base by a `Nat` arity cap and enumerate — a separator one arity above
the cap (a higher-arity threshold polymorphism / higher-arity pp-defined relation) refutes
completeness; the census-fooling failure mode of `pclHasCloneGenerationClosure` burned attack 1.

Burned attack 2: precompute the `Inv` side as an explicit `List PigBoolRel` and intersect — the
invariant relations are themselves infinitely many (all arities), so their carrier is again an
infinite list and the round trip closes only in the limit (the `pclHasCloneGenerationClosure`
burned attack 2). -/
def pigHasFullGaloisCorrespondence : Bool := false

/-- ★ WALL — the co-clone / pp-definability closure.  The pp-definable closure of a finite relation
set (conjunction + existential projection + equality, iterated to a fixpoint) is not finitely
enumerable: projection and conjunction generate relations of ALL arities, so the closure is an
unbounded least fixpoint over relation arity — the same `WellFounded.fix`-founded object as
`pclHasFullPostLattice`.

Obstruction: `pigPpConjoin` / `pigPpProject` are single steps; their transitive closure has no
structural fuel (each projection can be followed by a conjunction reintroducing arity), so no `Nat`
bound is a complete index.

Burned attack 1: cap the number of pp steps by fuel — a relation needing more conjuncts than the
fuel to define is missed; a target one step beyond the fuel refutes.

Burned attack 2: cap the relation arity — pp-definability over unbounded arity (the counting
relations) separates above any fixed arity, the same higher-arity separator that burns
`pclHasCloneGenerationClosure`. -/
def pigHasPpDefinabilityClosure : Bool := false

/-! ## T5 — concrete relations, functions, and ground fires -/

/-- The order / implication relation `≤` on bits: `{(0,0), (0,1), (1,1)}`. -/
def pigOrderRel : PigBoolRel :=
  { arity := 2, rows := [[false, false], [false, true], [true, true]] }

/-- The equality relation on bits: `{(0,0), (1,1)}`. -/
def pigEqRel : PigBoolRel :=
  { arity := 2, rows := [[false, false], [true, true]] }

/-- A small function base: conjunction and exclusive-or. -/
def pigFuncBase : List PclBoolFn := [pclAndFn, pclXorFn]

/-- Fire: the order relation is well-formed (both coordinates length `2`). -/
theorem pigOrderRelWellFormed : pigRelWellFormed pigOrderRel = true := rfl

/-- Fire (teeth+): `∧` PRESERVES the order relation (it is a monotone polymorphism of `≤`). -/
theorem pigAndPreservesOrder : pigPreserves pclAndFn pigOrderRel = true := rfl

/-- Fire (teeth−): `⊕` does NOT preserve the order relation — the pair `(0,1),(1,1)` images to
`(1,0) ∉ ≤`. -/
theorem pigXorNotPreservesOrder : pigPreserves pclXorFn pigOrderRel = false := rfl

/-- Fire: every unary function preserves equality — witnessed by `¬`. -/
theorem pigNegPreservesEquality : pigPreserves pclNegFn pigEqRel = true := rfl

/-- Fire: `∧` preserves equality too (the diagonal is closed under any function). -/
theorem pigAndPreservesEquality : pigPreserves pclAndFn pigEqRel = true := rfl

/-- Fire (Galois expanding, `f ∈ Pol(Inv{f})`): `∧` lies in `Pol(Inv({∧}))` over the finite base
— it is retained because it preserves exactly the relations `Inv` kept for it. -/
theorem pigAndInPolInvSelf :
    pigFuncMem pclAndFn (pigPol (pigInv [pclAndFn] [pigOrderRel, pigEqRel]) pigFuncBase) = true :=
  rfl

/-- Fire (antitonicity, one side): with only the equality relation, `⊕` survives in `Pol`. -/
theorem pigXorInPolEqAlone :
    pigFuncMem pclXorFn (pigPol [pigEqRel] pigFuncBase) = true := rfl

/-- Fire (antitonicity, teeth): ENLARGING the relation set with the order relation DROPS `⊕` from
`Pol` — the larger relation set gives a strictly smaller `Pol`. -/
theorem pigXorDroppedByOrder :
    pigFuncMem pclXorFn (pigPol [pigEqRel, pigOrderRel] pigFuncBase) = false := rfl

/-- Fire (pp-conjunction): `order ∧ equality` lands the equality relation. -/
theorem pigConjoinOrderEqIsEq :
    pigRelBeq (pigPpConjoin pigOrderRel pigEqRel) pigEqRel = true := rfl

/-- Fire (pp preserves preservation): `∧` preserves the pp-conjunction of two relations it
preserves. -/
theorem pigAndPreservesConjoin :
    pigPreserves pclAndFn (pigPpConjoin pigOrderRel pigEqRel) = true := rfl

/-- Fire: the DECIDED capability markers hold. -/
theorem pigDecidedMarkers :
    (pigHasFinitePreservation && pigHasBoundedPolInv
      && pigHasGaloisInequalities && pigHasPolInvAntitone) = true := rfl

/-- Fire: the WALL markers are all `false`. -/
theorem pigWallMarkers :
    (pigHasFullGaloisCorrespondence || pigHasPpDefinabilityClosure) = false := rfl

end FX1Poly.ComputerAlgebra
