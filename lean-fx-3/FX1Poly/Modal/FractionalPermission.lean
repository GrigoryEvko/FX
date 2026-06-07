import FX1Poly.Modal.ComplexitySemiring

/-! # FX1Poly/Modal/FractionalPermission — the §6.4 separation-logic permission algebra

§6.4 ("Separation Logic as Usage Grade") makes separation logic an instance of the usage grade: the
separating conjunction `*` is the `+` of a permission PCM, and ownership is a fractional share.  The
permission algebra is `Frac of p : rational { 0 < p ≤ 1 }`, `Zero`, `Omega`, with `Frac(p) + Frac(q) =
Frac(p + q)` when `p + q ≤ 1`, else CONFLICT (the over-allocation error).  This file ships the carrier and
its guarded partial add, the soundness theorem that the guard prevents over-allocation, and the §27.2 /
Boyland-2003 fractional-permission OVERALLOCATION bug as a rejected witness (consumed by
`FX1Poly.Typed.KnownUnsoundnessCorpus`).

It is the FIRST PARTIAL grade structure in the kernel: the shipped graded dimensions are TOTAL ordered
semirings (usage/security/complexity, `ResourceGraded.lean`) and bounded JOIN-semilattices (effect/trust/
overflow); a fractional-permission PCM is partial — `Frac(p) + Frac(q)` is undefined (CONFLICT) above the
whole.  That partiality is exactly the over-allocation discipline: you cannot hold more than the whole.

## Representation

A share is an UNNORMALIZED fraction `frac numerator denominator` intended at `numerator/denominator ∈
(0, 1]` (invariant `0 < numerator ≤ denominator`), plus `zero` (the empty share / additive unit) and
`conflict` (the over-allocation sentinel / `⊤`).  Fractions are kept unnormalized (no gcd reduction) — the
over-allocation discipline is about the `≤ 1` GUARD, not canonical form, so `frac 4 4` (= 1) and `frac 6 9`
(= 2/3) are admitted as-is.  `Omega` (the §6.4 duplicable share) is omitted here — this file isolates the
fractional core and its over-allocation bug.

## What lands here (all zero-axiom)

  * `Permission` / `Permission.add` — the carrier and the GUARDED partial add: `frac a b + frac c d` is
    `frac (a·d + c·b) (b·d)` when that fits the whole (`Nat.ble (a·d+c·b) (b·d)`), else `conflict`.
  * `Permission.naiveAdd` — the UNGUARDED (buggy) combine that omits the `≤ 1` check (the §27.2 bug is
    exactly using this instead of `add`).
  * `Permission.fitsWhole` — does a share stay within the whole (numerator ≤ denominator; `zero` yes,
    `conflict` no)?
  * `zero_add` / `add_zero` (unit), `conflict_add` / `add_conflict` (the sentinel absorbs), `add_comm`
    (combining shares is order-independent) — the lawful-monoid fragment.
  * **`add_neverOverallocates`** — SOUNDNESS: combining two fitting shares never yields an over-full
    share (every `frac` output of `add` fits the whole).  The guard's real content: an over-the-whole
    combine becomes `conflict`, never an invalid `> 1` share.
  * **`naiveAddOverallocates` / `naiveOverallocationDoesNotFit`** — the BUG: the unguarded combine of
    `2/3 + 2/3` produces `frac 12 9` (= 4/3 > 1, an impossible "more than the whole" share that does NOT
    fit).
  * **`soundAddRejectsOverallocation`** — the REJECTION: the guarded `add` yields `conflict` for the same
    `2/3 + 2/3` combine.
  * `fracExactlyFullAdmitted` / `fracExactlyFullFits` / `fracPartialAdmitted` — the guard ADMITS combines
    that stay within the whole (`1/2 + 1/2 = 1`, `1/3 + 1/3 = 2/3`).
  * `hasPositiveDenom` — does a share have a positive denominator (a well-formed `frac a b` has `0 < b`;
    `frac a 0` is excluded as `a/0` is ill-defined)?
  * **`add_assoc`** — ASSOCIATIVITY-WHERE-DEFINED, the deeper PCM law that closes the fractional core into
    a genuine lawful PARTIAL commutative monoid: combining three proper-denominator shares is association-
    order independent.  Proved by a normal-form strategy — both `(x + y) + z` and `x + (y + z)` reduce to
    `bif (triple fits the whole) then (triple share) else conflict`, where the triple is the common
    unnormalized fraction `(adf + cbf + ebd)/(bdf)`.  Conflict propagates (any pairwise over-allocation
    forces the triple over the whole), and when the triple fits, both orders give the same share.

## Honest scope boundary

The fractional core is now a complete lawful PARTIAL commutative monoid: unit (`zero_add` / `add_zero`),
commutativity (`add_comm`), associativity-where-defined (`add_assoc`, restricted to proper-denominator
shares so the cross-multiplied `Nat`-cancellation has a positive multiplier), the sentinel absorption
(`conflict_add` / `add_conflict`), the over-allocation SOUNDNESS (`add_neverOverallocates`), and the §27.2
bug rejection.  `Omega` (the §6.4 duplicable share) and gcd-normalization remain out of scope (this file
isolates the fractional over-allocation core) — that is a representation choice, not a missing law.

## Zero-axiom verification

`Permission` is a plain (non-indexed) inductive; `add` / `naiveAdd` are full 3×3 enumerations (no
overlapping patterns) with a Bool-`bif` guard, so the match compiler emits no equation-lemma `propext`;
`fitsWhole` is a 3-arm match.  The laws close by full case enumeration (`cases … <;> rfl`); `add_comm`'s
frac-frac arm by `Nat.add_comm` + `Nat.mul_comm`; `add_neverOverallocates` by cases + `injection` /
`noConfusion` with the `bif`-guard split feeding the fit.  The bug / admission witnesses are `rfl`
(concrete `Nat` computation).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The §6.4 separation-logic permission algebra carrier: `zero` (the empty share / additive unit), a
fractional share `frac numerator denominator` (intended at `numerator/denominator ∈ (0,1]`), and
`conflict` (the over-allocation sentinel — combining shares past the whole). -/
inductive Permission where
  | zero
  | frac (numerator denominator : Nat)
  | conflict

/-- Does a share fit within the whole (≤ 1)?  `zero` and a `frac` with numerator ≤ denominator do;
`conflict` (the over-allocation sentinel) does not. -/
def Permission.fitsWhole : Permission → Bool
  | .zero     => true
  | .frac a b => Nat.ble a b
  | .conflict => false

/-- **The guarded partial add** (the §6.4 `+`).  Combining two shares is defined only when the total
stays within the whole (`a/b + c/d ≤ 1`, i.e. `a·d + c·b ≤ b·d`); above the whole it is `conflict` (the
over-allocation rejection).  `zero` is the unit; `conflict` absorbs.  Full 3×3 enumeration (no overlapping
patterns), Bool-`bif` guard — propext-clean. -/
def Permission.add : Permission → Permission → Permission
  | .zero,     .zero     => .zero
  | .zero,     .frac c d => .frac c d
  | .zero,     .conflict => .conflict
  | .frac a b, .zero     => .frac a b
  | .frac a b, .frac c d =>
      bif Nat.ble (a * d + c * b) (b * d) then .frac (a * d + c * b) (b * d) else .conflict
  | .frac _ _, .conflict => .conflict
  | .conflict, .zero     => .conflict
  | .conflict, .frac _ _ => .conflict
  | .conflict, .conflict => .conflict

/-- The NAIVE (buggy) combine that OMITS the ≤-1 guard — always produces the summed share even when it
exceeds the whole.  The §27.2 / Boyland-2003 over-allocation bug is exactly using this instead of `add`. -/
def Permission.naiveAdd : Permission → Permission → Permission
  | .zero,     .zero     => .zero
  | .zero,     .frac c d => .frac c d
  | .zero,     .conflict => .conflict
  | .frac a b, .zero     => .frac a b
  | .frac a b, .frac c d => .frac (a * d + c * b) (b * d)
  | .frac _ _, .conflict => .conflict
  | .conflict, .zero     => .conflict
  | .conflict, .frac _ _ => .conflict
  | .conflict, .conflict => .conflict

/-- `zero` is the left unit for combining shares. -/
theorem Permission.zero_add (share : Permission) : Permission.add .zero share = share := by
  cases share <;> rfl

/-- `zero` is the right unit for combining shares. -/
theorem Permission.add_zero (share : Permission) : Permission.add share .zero = share := by
  cases share <;> rfl

/-- The over-allocation sentinel absorbs on the left. -/
theorem Permission.conflict_add (share : Permission) :
    Permission.add .conflict share = .conflict := by
  cases share <;> rfl

/-- The over-allocation sentinel absorbs on the right. -/
theorem Permission.add_conflict (share : Permission) :
    Permission.add share .conflict = .conflict := by
  cases share <;> rfl

/-- **Combining shares is commutative** (order-independent ownership).  The frac-frac arm: the summed
numerator and product denominator are symmetric (`Nat.add_comm` / `Nat.mul_comm`), so the guard and the
result agree both ways. -/
theorem Permission.add_comm (firstShare secondShare : Permission) :
    Permission.add firstShare secondShare = Permission.add secondShare firstShare := by
  cases firstShare with
  | zero => cases secondShare <;> rfl
  | frac a b =>
      cases secondShare with
      | zero => rfl
      | frac c d =>
          show (bif Nat.ble (a * d + c * b) (b * d) then Permission.frac (a * d + c * b) (b * d)
                else Permission.conflict)
             = (bif Nat.ble (c * b + a * d) (d * b) then Permission.frac (c * b + a * d) (d * b)
                else Permission.conflict)
          rw [Nat.add_comm (a * d) (c * b), Nat.mul_comm b d]
      | conflict => rfl
  | conflict => cases secondShare <;> rfl

/-- **Soundness — combining two fitting shares never over-allocates.**  If both inputs fit the whole,
every `frac` output of the guarded `add` also fits: the pass-through arms (`zero` + share) inherit the
input's fit, and the frac-frac arm's `bif Nat.ble (a·d+c·b) (b·d)` guard is TRUE exactly when the output
`frac (a·d+c·b) (b·d)` fits.  The guard's real content: a combine that would exceed the whole becomes
`conflict`, never an over-full share. -/
theorem Permission.add_neverOverallocates {firstShare secondShare : Permission}
    (firstFits : firstShare.fitsWhole = true) (secondFits : secondShare.fitsWhole = true)
    {resultNum resultDen : Nat}
    (isFracOutput : Permission.add firstShare secondShare = .frac resultNum resultDen) :
    Nat.ble resultNum resultDen = true := by
  cases firstShare with
  | zero =>
      cases secondShare with
      | zero => exact Permission.noConfusion isFracOutput
      | frac c d =>
          injection isFracOutput with numEq denEq
          rw [← numEq, ← denEq]; exact secondFits
      | conflict => exact Permission.noConfusion isFracOutput
  | frac a b =>
      cases secondShare with
      | zero =>
          injection isFracOutput with numEq denEq
          rw [← numEq, ← denEq]; exact firstFits
      | frac c d =>
          simp only [Permission.add] at isFracOutput
          cases hGuard : Nat.ble (a * d + c * b) (b * d) with
          | false => rw [hGuard] at isFracOutput; exact Permission.noConfusion isFracOutput
          | true =>
              rw [hGuard] at isFracOutput
              injection isFracOutput with numEq denEq
              rw [← numEq, ← denEq]; exact hGuard
      | conflict => exact Permission.noConfusion isFracOutput
  | conflict =>
      cases secondShare <;> exact Permission.noConfusion isFracOutput

/-- **The §27.2 over-allocation BUG (Boyland 2003).**  The unguarded `naiveAdd` of `2/3 + 2/3` produces
`frac 12 9` (= 4/3) — an over-full share. -/
theorem Permission.naiveAddOverallocates :
    Permission.naiveAdd (.frac 2 3) (.frac 2 3) = .frac 12 9 := rfl

/-- The naive over-allocated result `frac 12 9` does NOT fit the whole (12 > 9): an impossible "more than
the whole" share, the over-allocation unsoundness. -/
theorem Permission.naiveOverallocationDoesNotFit :
    (Permission.naiveAdd (.frac 2 3) (.frac 2 3)).fitsWhole = false := rfl

/-- **The REJECTION.**  The sound (guarded) `add` of the same `2/3 + 2/3` combine yields `conflict` — the
over-allocation is rejected, not silently producing an over-full share. -/
theorem Permission.soundAddRejectsOverallocation :
    Permission.add (.frac 2 3) (.frac 2 3) = .conflict := rfl

/-- The guard ADMITS combines that stay within the whole: `1/2 + 1/2 = 1` (`frac 4 4`). -/
theorem Permission.fracExactlyFullAdmitted :
    Permission.add (.frac 1 2) (.frac 1 2) = .frac 4 4 := rfl

/-- The admitted exactly-full share fits the whole. -/
theorem Permission.fracExactlyFullFits :
    (Permission.add (.frac 1 2) (.frac 1 2)).fitsWhole = true := rfl

/-- A partial combine within the whole is admitted: `1/3 + 1/3 = 2/3` (`frac 6 9`). -/
theorem Permission.fracPartialAdmitted :
    Permission.add (.frac 1 3) (.frac 1 3) = .frac 6 9 := rfl

/-! ## Associativity-where-defined: the partial commutative monoid law

The fractional add is a PARTIAL operation, so the PCM associativity law is conditional: it holds when the
outer denominators are positive (proper shares), the multiplier the cross-multiplied `Nat`-cancellation
needs.  The proof is a normal-form argument — both `(a/b + c/d) + e/f` and `a/b + (c/d + e/f)` reduce to
`bif (the triple fits the whole) then (the triple share) else conflict`, where the triple share is the
common unnormalized fraction `(a·d·f + c·b·f + e·b·d)/(b·d·f)`.  Conflict propagates in both directions
(any pairwise over-allocation forces the triple over the whole), and when the triple fits, both association
orders produce the same share.  The cross-multiplied `Nat` algebra is kept propext-clean by reusing the
`ComplexitySemiring` helpers `natMulAssoc` / `natRightDistrib` (`Nat.mul_assoc` and the right-distributive
`Nat.add_mul` themselves leak propext). -/

/-- Does a share have a positive denominator?  A well-formed `frac a b` carries `0 < b` (a `frac a 0` would
denote the ill-defined `a/0`); `zero` and `conflict` carry no denominator and are vacuously proper.  Supplies
the positive multiplier the cross-multiplied associativity cancellation needs. -/
def Permission.hasPositiveDenom : Permission → Bool
  | .zero     => true
  | .frac _ b => Nat.ble 1 b
  | .conflict => true

/-- The common (normal-form) numerator of the three-way share sum `a/b + c/d + e/f`, cross-multiplied to
the common denominator `b·d·f`: `a·(d·f) + (c·(b·f) + e·(b·d))`. -/
private def tripleNumerator (a b c d e f : Nat) : Nat := a * (d * f) + (c * (b * f) + e * (b * d))

/-- The common (normal-form) denominator of the three-way share sum `a/b + c/d + e/f`: `b·(d·f)`. -/
private def tripleDenominator (b d f : Nat) : Nat := b * (d * f)

/-- LEFT-association numerator identity: the cross-multiplied numerator of `(a/b + c/d) + e/f` is the
normal-form triple numerator. -/
private theorem leftNumeratorEqualsTriple (a b c d e f : Nat) :
    (a * d + c * b) * f + e * (b * d) = tripleNumerator a b c d e f := by
  show (a * d + c * b) * f + e * (b * d) = a * (d * f) + (c * (b * f) + e * (b * d))
  rw [natRightDistrib (a * d) (c * b) f, natMulAssoc a d f, natMulAssoc c b f, Nat.add_assoc]

/-- RIGHT-association numerator identity: the cross-multiplied numerator of `a/b + (c/d + e/f)` is the SAME
normal-form triple numerator. -/
private theorem rightNumeratorEqualsTriple (a b c d e f : Nat) :
    a * (d * f) + (c * f + e * d) * b = tripleNumerator a b c d e f := by
  show a * (d * f) + (c * f + e * d) * b = a * (d * f) + (c * (b * f) + e * (b * d))
  rw [natRightDistrib (c * f) (e * d) b, natMulAssoc c f b, natMulAssoc e d b,
    Nat.mul_comm f b, Nat.mul_comm d b]

/-- LEFT-association denominator identity: `(b·d)·f` is the normal-form triple denominator `b·(d·f)`. -/
private theorem leftDenominatorEqualsTriple (b d f : Nat) :
    (b * d) * f = tripleDenominator b d f := natMulAssoc b d f

/-- From the triple fitting the whole, the LEFT inner pair `a/b + c/d` also fits: scaling `a·d + c·b` by
the positive `f` lands below `a·(d·f) + c·(b·f) ≤ tripleNumerator ≤ tripleDenominator = (b·d)·f`, then
cancel the positive `f`. -/
private theorem tripleFitsImpliesLeftPairFits (a b c d e f : Nat) (fPos : 0 < f)
    (tripleFits : Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f) = true) :
    Nat.ble (a * d + c * b) (b * d) = true := by
  have tripleLe : tripleNumerator a b c d e f ≤ tripleDenominator b d f :=
    Nat.le_of_ble_eq_true tripleFits
  have innerScaledEq : (a * d + c * b) * f = a * (d * f) + c * (b * f) := by
    rw [natRightDistrib (a * d) (c * b) f, natMulAssoc a d f, natMulAssoc c b f]
  have leTriple : a * (d * f) + c * (b * f) ≤ tripleNumerator a b c d e f := by
    show a * (d * f) + c * (b * f) ≤ a * (d * f) + (c * (b * f) + e * (b * d))
    rw [← Nat.add_assoc]; exact Nat.le_add_right _ _
  have scaledLe : (a * d + c * b) * f ≤ (b * d) * f := by
    rw [innerScaledEq, leftDenominatorEqualsTriple b d f] at *
    exact Nat.le_trans leTriple tripleLe
  exact Nat.ble_eq_true_of_le (Nat.le_of_mul_le_mul_right scaledLe fPos)

/-- From the triple fitting the whole, the RIGHT inner pair `c/d + e/f` also fits: drop the leading
`a·(d·f)` term, factor the positive `b` out of `c·(b·f) + e·(b·d) = b·(c·f + e·d)`, then cancel `b`. -/
private theorem tripleFitsImpliesRightPairFits (a b c d e f : Nat) (bPos : 0 < b)
    (tripleFits : Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f) = true) :
    Nat.ble (c * f + e * d) (d * f) = true := by
  have tripleLe : tripleNumerator a b c d e f ≤ tripleDenominator b d f :=
    Nat.le_of_ble_eq_true tripleFits
  have dropLeading : c * (b * f) + e * (b * d) ≤ tripleDenominator b d f := by
    show c * (b * f) + e * (b * d) ≤ b * (d * f)
    exact Nat.le_trans (Nat.le_add_left _ _) tripleLe
  have factored : b * (c * f + e * d) ≤ b * (d * f) := by
    have collect : c * (b * f) + e * (b * d) = b * (c * f + e * d) := by
      rw [Nat.mul_add, Nat.mul_comm c (b * f), Nat.mul_comm e (b * d),
        natMulAssoc b f c, natMulAssoc b d e, Nat.mul_comm f c, Nat.mul_comm d e]
    rw [← collect]; exact dropLeading
  exact Nat.ble_eq_true_of_le (Nat.le_of_mul_le_mul_left factored bPos)

/-- LEFT association `(a/b + c/d) + e/f` reduces to the triple normal form `bif (triple fits) then triple
else conflict`. -/
private theorem leftAssociationNormalizesToTriple (a b c d e f : Nat) (fPos : 0 < f) :
    Permission.add (Permission.add (.frac a b) (.frac c d)) (.frac e f)
      = bif Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f)
        then .frac (tripleNumerator a b c d e f) (tripleDenominator b d f) else .conflict := by
  show Permission.add
        (bif Nat.ble (a * d + c * b) (b * d) then Permission.frac (a * d + c * b) (b * d)
         else Permission.conflict) (Permission.frac e f) = _
  cases hInner : Nat.ble (a * d + c * b) (b * d) with
  | false =>
      rw [Bool.cond_false]
      show Permission.conflict = _
      cases hTriple : Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f) with
      | false => rw [Bool.cond_false]
      | true =>
          exact absurd (tripleFitsImpliesLeftPairFits a b c d e f fPos hTriple)
            (by rw [hInner]; decide)
  | true =>
      rw [Bool.cond_true]
      show (bif Nat.ble ((a * d + c * b) * f + e * (b * d)) ((b * d) * f)
            then Permission.frac ((a * d + c * b) * f + e * (b * d)) ((b * d) * f)
            else Permission.conflict) = _
      rw [leftNumeratorEqualsTriple a b c d e f, leftDenominatorEqualsTriple b d f]

/-- RIGHT association `a/b + (c/d + e/f)` reduces to the SAME triple normal form. -/
private theorem rightAssociationNormalizesToTriple (a b c d e f : Nat) (bPos : 0 < b) :
    Permission.add (.frac a b) (Permission.add (.frac c d) (.frac e f))
      = bif Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f)
        then .frac (tripleNumerator a b c d e f) (tripleDenominator b d f) else .conflict := by
  show Permission.add (Permission.frac a b)
        (bif Nat.ble (c * f + e * d) (d * f) then Permission.frac (c * f + e * d) (d * f)
         else Permission.conflict) = _
  cases hInner : Nat.ble (c * f + e * d) (d * f) with
  | false =>
      rw [Bool.cond_false]
      show Permission.conflict = _
      cases hTriple : Nat.ble (tripleNumerator a b c d e f) (tripleDenominator b d f) with
      | false => rw [Bool.cond_false]
      | true =>
          exact absurd (tripleFitsImpliesRightPairFits a b c d e f bPos hTriple)
            (by rw [hInner]; decide)
  | true =>
      rw [Bool.cond_true]
      show (bif Nat.ble (a * (d * f) + (c * f + e * d) * b) (b * (d * f))
            then Permission.frac (a * (d * f) + (c * f + e * d) * b) (b * (d * f))
            else Permission.conflict) = _
      rw [rightNumeratorEqualsTriple a b c d e f]
      show (bif Nat.ble (tripleNumerator a b c d e f) (b * (d * f))
            then Permission.frac (tripleNumerator a b c d e f) (b * (d * f)) else Permission.conflict) = _
      rfl

/-- **Associativity-where-defined** — the deeper PCM law that closes the fractional core into a genuine
lawful PARTIAL commutative monoid: combining three proper-denominator shares is association-order
independent.  Both `(x + y) + z` and `x + (y + z)` reduce to the same triple normal form; conflict
propagates and, when the triple fits, both orders give the same share.  The hypotheses `firstProper` /
`thirdProper` (positive OUTER denominators) supply the multipliers the inner `Nat`-cancellations need — the
middle denominator is unconstrained. -/
theorem Permission.add_assoc {firstShare secondShare thirdShare : Permission}
    (firstProper : firstShare.hasPositiveDenom = true)
    (thirdProper : thirdShare.hasPositiveDenom = true) :
    Permission.add (Permission.add firstShare secondShare) thirdShare
      = Permission.add firstShare (Permission.add secondShare thirdShare) := by
  cases firstShare with
  | zero =>
      rw [Permission.zero_add, Permission.zero_add]
  | conflict =>
      rw [Permission.conflict_add, Permission.conflict_add, Permission.conflict_add]
  | frac a b =>
      cases secondShare with
      | zero => rw [Permission.add_zero, Permission.zero_add]
      | conflict =>
          rw [Permission.add_conflict, Permission.conflict_add, Permission.add_conflict]
      | frac c d =>
          cases thirdShare with
          | zero => rw [Permission.add_zero, Permission.add_zero]
          | conflict =>
              rw [Permission.add_conflict, Permission.add_conflict, Permission.add_conflict]
          | frac e f =>
              have bPos : 0 < b := Nat.le_of_ble_eq_true firstProper
              have fPos : 0 < f := Nat.le_of_ble_eq_true thirdProper
              rw [leftAssociationNormalizesToTriple a b c d e f fPos,
                rightAssociationNormalizesToTriple a b c d e f bPos]

/-- Non-vacuity — a concrete proper triple where all three pairwise sums fit (`1/4 + 1/4 + 1/4 = 3/4 ≤ 1`),
so `add_assoc` is not vacuously discharging a never-satisfiable hypothesis.  The `hasPositiveDenom` premises
close by `rfl` (the predicate reduces definitionally on a concrete `frac`) — no `decide`, no axioms. -/
theorem Permission.add_assoc_smoke :
    Permission.add (Permission.add (.frac 1 4) (.frac 1 4)) (.frac 1 4)
      = Permission.add (.frac 1 4) (Permission.add (.frac 1 4) (.frac 1 4)) :=
  Permission.add_assoc (firstProper := rfl) (thirdProper := rfl)

end FX1Poly.Modal
