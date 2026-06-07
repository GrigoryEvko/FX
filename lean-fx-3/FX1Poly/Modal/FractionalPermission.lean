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

## Honest scope boundary

Associativity-where-defined (the deeper PCM law) is NOT proved here.  It IS true — conflict propagates
(any pairwise share-sum exceeding the whole forces the total to exceed it, so both association orders
conflict) and when the total fits, both orders produce the same unnormalized fraction `(adf+cbf+ebd)/
(bdf)` — but the proof is an intricate cross-multiplied Nat-inequality case analysis (the `Nat.add_mul`
propext-trap zone), deferred as a follow-up.  This file ships the carrier, the lawful-monoid fragment, the
over-allocation SOUNDNESS, and the §27.2 bug rejection — the content the corpus entry consumes.

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

end FX1Poly.Modal
