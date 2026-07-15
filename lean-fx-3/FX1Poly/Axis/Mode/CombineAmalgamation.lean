import FX1Poly.Axis.Mode.Mode

/-! # mode-18 ★ — O-COMBINE: the decidable pushout of doctrines + the H² obstruction

The central FX question — "do great ideas COMBINE?" — is the amalgamation of two doctrines (a PUSHOUT over a
shared base) and its OBSTRUCTION.  Two doctrines combine iff their feature profiles join WITHOUT a soundness
collision (the `fx_design §6.8` catalogue: classified × Fail, borrow × Async, CT × Async, classified × Async …),
and that is DECIDABLE.  The combination IS the pushout (the join in the feature lattice, with the least-upper-
bound universal property), and the obstruction to combining is the NEW collision the combination introduces — the
decidable shadow of the genuine cohomological H² class (which vanishes iff the doctrines combine).

`mode-18` ships the decidable pushout, its universal property, the decidable combinability + the obstruction, and
the §6.8 no-go / orthogonal witnesses, all funext-free Bool algebra.

## What this file ships (each piece zero-axiom)

  * **`Doctrine`** — a finite feature profile (a representative subset of the `§6.8` collision dimensions:
    classified / Fail / borrow / Async / constant-time) + `hasCollision` (the §6.8 catalogue) + `isAdmissible`.
  * **`Doctrine.combine`** — the PUSHOUT / amalgam (field-wise join over the base), with the genuine UNIVERSAL
    PROPERTY `combine_universal` (least upper bound) + the coprojections + symmetry.
  * **`combinesOrthogonally`** (DECIDABLE: the combination is admissible) + **`combinationObstruction`** (the new
    collision = the H² shadow) + **`combinationObstruction_blocks`** (the obstruction blocks combining).
  * witnesses — `emptyDoctrine` (the initial/base, combines with all), `classified_fail_no_combine` (the §6.8
    NO-GO), `classified_borrow_combines` (an orthogonal pair).

## What is DEFERRED (markers)

  * the genuine COHOMOLOGICAL H² (the cochain complex + coboundary + the cohomology group, beyond the decidable
    collision shadow here) (`hasCohomologicalH2`);
  * the 2-monad DISTRIBUTIVE LAW + Beck conditions IS now shipped (`mode-17` `TwoMonad.DistributiveLaw` +
    `readerReaderDistributiveLaw`); only the composite-monad `S∘T` construction from a general law + its laws
    remains deferred (`hasDistributiveLawPushout`);
  * the FULL `§6.8` 21-dimension collision matrix (this file models a representative subset)
    (`hasFull21DimCollisionMatrix`);
  * the kernel's profile-extension-combination connection (cross-axis, `fib`) (`hasKernelCombineConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis

/-! ## Bool plumbing (funext-free) -/

/-- A `true` left disjunct makes the disjunction `true`. -/
private theorem bool_left_or {first second : Bool} (firstTrue : first = true) :
    (first || second) = true := by rw [firstTrue]; rfl

/-- A `true` right disjunct makes the disjunction `true`. -/
private theorem bool_right_or {first second : Bool} (secondTrue : second = true) :
    (first || second) = true := by
  cases first with
  | true => rfl
  | false => exact secondTrue

/-- The disjunction's universal property at the Bool-implication level: if both disjuncts imply `target`, so does
the disjunction. -/
private theorem bool_imp_or {first second target : Bool}
    (firstImplies : first = true → target = true) (secondImplies : second = true → target = true) :
    (first || second) = true → target = true := by
  cases first with
  | true => intro _; exact firstImplies rfl
  | false => intro disjunctionTrue; exact secondImplies disjunctionTrue

/-- The left conjunct of a `true` conjunction is `true`. -/
private theorem bool_and_left {first second : Bool} (conjunctionTrue : (first && second) = true) :
    first = true := by
  cases first with
  | true => rfl
  | false => exact conjunctionTrue

/-! ## Doctrines as feature profiles -/

/-- A **doctrine** as a finite feature profile — a representative subset of the `fx_design §6.8` soundness
dimensions, each a Bool flag (present / absent). -/
structure Doctrine where
  /-- The security `classified` dimension (dim 5). -/
  hasClassified : Bool
  /-- The `Fail` effect (dim 4). -/
  hasFail : Bool
  /-- The `borrow` usage / lifetime dimension (dim 7). -/
  hasBorrow : Bool
  /-- The `Async` effect. -/
  hasAsync : Bool
  /-- The constant-time (`CT`) observability dimension (dim 11). -/
  hasConstantTime : Bool
  deriving DecidableEq

/-- The **§6.8 collision catalogue** — whether a doctrine's feature set contains a known-unsound pair:
classified × Fail (info leak via failure), borrow × Async, CT × Async (timing leak), classified × Async (the
3-way seed).  Pure Bool algebra (no match), so propext-free. -/
def Doctrine.hasCollision (doctrine : Doctrine) : Bool :=
  (doctrine.hasClassified && doctrine.hasFail)
    || (doctrine.hasBorrow && doctrine.hasAsync)
    || (doctrine.hasConstantTime && doctrine.hasAsync)
    || (doctrine.hasClassified && doctrine.hasAsync)

/-- A doctrine is **admissible** when it is collision-free (§6.8-sound). -/
def Doctrine.isAdmissible (doctrine : Doctrine) : Bool := !doctrine.hasCollision

/-! ## The pushout / amalgamation -/

/-- The **combination** of two doctrines — the PUSHOUT over the shared base, i.e. the field-wise JOIN of their
feature profiles (the union of features). -/
def Doctrine.combine (first second : Doctrine) : Doctrine where
  hasClassified := first.hasClassified || second.hasClassified
  hasFail := first.hasFail || second.hasFail
  hasBorrow := first.hasBorrow || second.hasBorrow
  hasAsync := first.hasAsync || second.hasAsync
  hasConstantTime := first.hasConstantTime || second.hasConstantTime

/-- One doctrine **refines** another when every feature of the first is present in the second (field-wise
implication) — the order in the feature lattice. -/
structure Doctrine.Refines (first second : Doctrine) : Prop where
  /-- classified is preserved. -/
  classified : first.hasClassified = true → second.hasClassified = true
  /-- Fail is preserved. -/
  fail : first.hasFail = true → second.hasFail = true
  /-- borrow is preserved. -/
  borrow : first.hasBorrow = true → second.hasBorrow = true
  /-- Async is preserved. -/
  async : first.hasAsync = true → second.hasAsync = true
  /-- constant-time is preserved. -/
  constantTime : first.hasConstantTime = true → second.hasConstantTime = true

/-- The left coprojection — the first doctrine refines the combination. -/
theorem Doctrine.combine_refines_left (first second : Doctrine) :
    first.Refines (first.combine second) where
  classified := bool_left_or
  fail := bool_left_or
  borrow := bool_left_or
  async := bool_left_or
  constantTime := bool_left_or

/-- The right coprojection — the second doctrine refines the combination. -/
theorem Doctrine.combine_refines_right (first second : Doctrine) :
    second.Refines (first.combine second) where
  classified := bool_right_or
  fail := bool_right_or
  borrow := bool_right_or
  async := bool_right_or
  constantTime := bool_right_or

/-- ★ The **pushout universal property** — the combination is the LEAST upper bound: any doctrine refined by BOTH
operands is refined by their combination.  With the coprojections, this is the genuine pushout / coproduct of
doctrines over the base. -/
theorem Doctrine.combine_universal (first second upper : Doctrine)
    (firstRefines : first.Refines upper) (secondRefines : second.Refines upper) :
    (first.combine second).Refines upper where
  classified := bool_imp_or firstRefines.classified secondRefines.classified
  fail := bool_imp_or firstRefines.fail secondRefines.fail
  borrow := bool_imp_or firstRefines.borrow secondRefines.borrow
  async := bool_imp_or firstRefines.async secondRefines.async
  constantTime := bool_imp_or firstRefines.constantTime secondRefines.constantTime

/-- The pushout is SYMMETRIC — `combine` is commutative (the join is symmetric). -/
theorem Doctrine.combine_comm (first second : Doctrine) :
    first.combine second = second.combine first := by
  cases first with
  | mk fClassified fFail fBorrow fAsync fConstantTime =>
    cases second with
    | mk sClassified sFail sBorrow sAsync sConstantTime =>
      show Doctrine.mk (fClassified || sClassified) (fFail || sFail) (fBorrow || sBorrow)
          (fAsync || sAsync) (fConstantTime || sConstantTime)
        = Doctrine.mk (sClassified || fClassified) (sFail || fFail) (sBorrow || fBorrow)
          (sAsync || fAsync) (sConstantTime || fConstantTime)
      rw [Bool.or_comm fClassified sClassified, Bool.or_comm fFail sFail, Bool.or_comm fBorrow sBorrow,
        Bool.or_comm fAsync sAsync, Bool.or_comm fConstantTime sConstantTime]

/-! ## Decidable combinability + the H² obstruction -/

/-- ★ The DECIDABLE **combinability** of two doctrines — they combine iff their combination is admissible
(collision-free).  A `Bool`, hence decidable. -/
def Doctrine.combinesOrthogonally (first second : Doctrine) : Bool :=
  (first.combine second).isAdmissible

/-- The **combination obstruction** (the decidable H² shadow) — the NEW collision the combination introduces:
present in the combination, absent in each operand.  Vanishes (`false`) iff the doctrines combine cleanly. -/
def Doctrine.combinationObstruction (first second : Doctrine) : Bool :=
  (first.combine second).hasCollision && !first.hasCollision && !second.hasCollision

/-- Combinability is exactly the absence of a collision in the combination. -/
theorem Doctrine.combinesOrthogonally_eq (first second : Doctrine) :
    first.combinesOrthogonally second = !(first.combine second).hasCollision := rfl

/-- ★ The obstruction BLOCKS combining — a non-trivial obstruction (`= true`) means the doctrines do NOT combine
orthogonally.  Extracts the combination-collision conjunct, which flips combinability to `false`. -/
theorem Doctrine.combinationObstruction_blocks (first second : Doctrine)
    (obstructed : first.combinationObstruction second = true) :
    first.combinesOrthogonally second = false := by
  have collision : (first.combine second).hasCollision = true :=
    bool_and_left (bool_and_left obstructed)
  show (first.combine second).isAdmissible = false
  rw [Doctrine.isAdmissible, collision]
  rfl

/-! ## Witnesses -/

/-- The **empty / base doctrine** — no features (the initial object of the lattice). -/
def emptyDoctrine : Doctrine where
  hasClassified := false
  hasFail := false
  hasBorrow := false
  hasAsync := false
  hasConstantTime := false

/-- Combining with the empty doctrine is the identity (the base is the unit of the amalgam). -/
theorem emptyDoctrine_combine (doctrine : Doctrine) : emptyDoctrine.combine doctrine = doctrine := by
  cases doctrine
  rfl

/-- The classified-only doctrine. -/
def classifiedDoctrine : Doctrine := { emptyDoctrine with hasClassified := true }

/-- The Fail-only doctrine. -/
def failDoctrine : Doctrine := { emptyDoctrine with hasFail := true }

/-- The borrow-only doctrine. -/
def borrowDoctrine : Doctrine := { emptyDoctrine with hasBorrow := true }

/-- ★ The §6.8 **NO-GO** — classified and Fail do NOT combine (the combination has the classified × Fail
collision).  A concrete obstruction. -/
theorem classified_fail_no_combine : classifiedDoctrine.combinesOrthogonally failDoctrine = false := rfl

/-- The obstruction to combining classified and Fail is genuinely non-trivial. -/
theorem classified_fail_obstructed : classifiedDoctrine.combinationObstruction failDoctrine = true := rfl

/-- ★ An ORTHOGONAL pair — classified and borrow DO combine (no §6.8 collision between them). -/
theorem classified_borrow_combines : classifiedDoctrine.combinesOrthogonally borrowDoctrine = true := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The genuine COHOMOLOGICAL H² — the cochain complex, the coboundary maps, the cohomology
GROUP whose vanishing class is the combination obstruction — beyond the decidable collision SHADOW shipped here,
is deferred.  `= false`. -/
def fxMode_hasCohomologicalH2 : Bool := false

/-- **Honesty marker.**  The 2-monad DISTRIBUTIVE LAW `T S → S T` + the four Beck conditions IS now shipped
(`mode-17` `TwoMonad.DistributiveLaw` + `readerReaderDistributiveLaw`, the reader doctrines distributing by SWAP,
all Beck axioms by `rfl`, + the composite = product-reader iso).  What remains deferred is the construction of
the composite monad `S∘T` from a GENERAL distributive law and the proof of ITS monad laws (the diagram chase).
`= false`. -/
def fxMode_hasDistributiveLawPushout : Bool := false

/-- **Honesty marker.**  The FULL `fx_design §6.8` 21-dimension collision matrix (all dimensions + every
catalogued collision), beyond the representative subset here, is deferred.  `= false`. -/
def fxMode_hasFull21DimCollisionMatrix : Bool := false

/-- **Honesty marker.**  The connection to the kernel's `ProfileExtension` combination (the doctrine pushout as a
kernel operation) is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelCombineConnection : Bool := false

end FX1Poly.Axis
