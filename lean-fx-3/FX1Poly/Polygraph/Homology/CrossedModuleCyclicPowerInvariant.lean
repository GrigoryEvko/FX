import FX1Poly.Polygraph.Homology.CrossedModuleCyclicPower
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # FX1Poly/Polygraph/Homology/CrossedModuleCyclicPowerInvariant — the general `ZZ[ZZ/n]` separating
    invariant on the free crossed module of `⟨s | sⁿ⟩`, its Peiffer-invariance, and the mechanized
    `π₂⟨s | sⁿ⟩ ≠ 0` for EVERY `n ≥ 2` (WP-2GROUP r8, #2199)

r2 (`Homology/CrossedModuleIdentityInvariant`) separated the rotation identity `ζ` from the
Peiffer-trivial word for the `⟨s | s³⟩` INSTANCE via a `ZZ[ZZ/3] ≅ ZZ³` group-ring invariant, with the
mod-`3` structure folded into a full-enum `ZmodThree` residue.  r7 (`Homology/CrossedModuleCyclicPower`)
parameterized the boundary by the exponent and proved `∂ₙ ζₙ = []` for every `n`, but named the general
separating invariant `generalInvariantResidualR8`.  This module DELIVERS that node: the `ZZ[ZZ/n]`-module
invariant for GENERAL `n`, promoting Lyndon's `π₂ ≠ 0` from cited to PROVED for every `n ≥ 2`.

## The carrier (List cyclic rotation — the mod-free generalization of r2's `ZmodThree`)

The value carrier is `List Int` (an element of `ZZ[ZZ/n] ≅ ZZⁿ` in the basis `1, t, …, t^{n-1}`) with
coefficientwise `vecAdd`/`vecNeg`.  The `t`-action of `G = ZZ/n` is a CYCLIC LIST ROTATION — the honest
generalization of r2's `groupRingSAction ⟨a, b, c⟩ = ⟨c, a, b⟩`.  A conjugator word `w` images to the
basis vector `e₀` rotated once per letter (`pos ↦ rotateForward`, `neg ↦ rotateBackward`), exactly as r2
folds `shiftUp`/`shiftDown`.  **No `Int.emod`, no `Int.toNat`, no `Quot` anywhere**: the mod-`n` residue
IS the period-`n` cyclicity of a length-`n` list rotation.  The single genuinely-new content over r2 is
`rotateForwardPowFixesLength` (rotate-by-length = identity), the mod-free replacement for r2's
`relatorResidueIsZero` `rfl`.

## The honest Peiffer relation is EXPONENT-PARAMETERIZED (the r8 §-finding)

The shipped `PeifferEquiv` (`Homology/CrossedModuleCyclicThree`) bakes in the `n = 3` relator through
`conjugatedRelatorBoundary` (`relatorWord 0 = s³`).  Under the `ZZ[ZZ/n]` invariant a Peiffer move only
dies when `residue (∂a) ≡ 0` in `ZZ/n`, i.e. when the boundary's net rotation `3` is a multiple of `n` —
which fails for every `n ∉ {1, 3}`.  So the shipped `PeifferEquiv` is the `⟨s | s³⟩` relation and CANNOT
carry the general claim.  This module introduces `PeifferEquivAt n` — the honest Peiffer relation of
`⟨s | sⁿ⟩`, whose generating move conjugates by `∂ₙa = w · s^{±n} · w⁻¹` (net rotation `±n ≡ 0` in
`ZZ/n`) — and proves the separating invariant is constant on ITS classes.  The `n = 3` case of the arm
recovers r2's `peifferMoveImage` mechanism (`residue (∂a) = 0`) with the rotate-cyclicity crux replacing
the `ZmodThree` `rfl`.

## The separation (a single coefficient, ∀ n ≥ 2; the degenerate control at n = 1)

The separating functional is `headCoeff` — the coefficient of the basis element `e₀ = t⁰` (index `0`),
a bespoke full-enum projection (NEVER `List.getD`).  For every `n ≥ 2` the image of `ζₙ` is
`headCoeff (image ζₙ) = −1 ≠ 0`, while every Peiffer-trivial element images to `0` (headCoeff `0`) by
Peiffer-invariance, so `ζₙ` is a NONTRIVIAL identity among relations (`π₂⟨s | sⁿ⟩ ≠ 0`).  The COEFFICIENT
SUM (augmentation `ε`) does NOT separate — `ε(image ζₙ) = 0` for all `n` (the abelianized shadow), so the
invariant must be the single `e₀`-projection, never the sum (exactly the r1/r3 point).  At `n = 1` the
separation correctly does NOT fire (`image ζ₁ = image [] = [0]`): `s¹` is not a proper power, `π₂ = 0`
(Lyndon), and the `2 ≤ n` hypothesis is load-bearing.  The invariant vanishing at `n = 1` is CONSISTENT
with `π₂ = 0` but does not PROVE it (that needs injectivity — the walled node); honest.

## Zero-axiom design decisions

  * The list carrier is fully cons-structural: `rotateBackward` is defined via `lastElemD`/`initSegment`
    (NO `List.reverse`), so its mutual-inverse and length laws are clean structural inductions.  The
    reverse only appears inside the shipped `invWord`, whose cons law rides a self-proved
    `reverseAuxAppend` (no Init `List.reverse_cons`, no propext leak).
  * `basisE0`/`zeroVec` recurse structurally so `(basisE0 n).length = n` by cases (no `Nat` subtraction).
  * Every match on `SignedLetter` / `Bool` / `Int`-constructor is FULLY enumerated — no wildcard, no
    `Option.noConfusion` mis-elaboration.  `decide` is used ONLY on the closing `(-1 : Int) ≠ 0` and on
    `¬ (2 ≤ 0)` / `¬ (2 ≤ 1)` (`Int.decEq` / `Nat.decLe`, clean-structural), never on a `∀ n`.
  * All `Int` arithmetic goes through the shipped propext-clean kit (`intAddZero`, `intZeroAdd`,
    `intNegNeg`, `intAddComm`, `intAddAssoc`, `intAddRightNeg`), never Init's propext-dirty forms.

`Init`-only (over `Homology/CrossedModuleCyclicPower` and the `ComputerAlgebra.Number` Int kit),
structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicPowerInvariant.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## V0 — the propext-clean list infrastructure (self-proved MONOMORPHIC helpers)

Polymorphic recursive equality theorems (`∀ {alpha}, …`) pull `propext` from the equation compiler, so
every list helper below is MONOMORPHIC (`List Int` or `List SignedLetter`) — cons-only structural, no leaky
Init `List.append_nil` / `List.append_assoc` / `List.reverse_cons`. -/

/-- `xs ++ [] = xs` on `List Int` — cons-only structural, propext-clean. -/
theorem intListAppendNil : ∀ xs : List Int, xs ++ [] = xs
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (intListAppendNil rest)

/-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` on `List Int` — cons-only structural, propext-clean. -/
theorem intListAppendAssoc : ∀ xs ys zs : List Int, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | head :: rest, ys, zs => congrArg (head :: ·) (intListAppendAssoc rest ys zs)

/-- `(xs ++ ys).length = xs.length + ys.length` on `List Int` — cons-only structural over `Nat`. -/
theorem intListLengthAppend : ∀ xs ys : List Int, (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | _head :: rest, ys =>
      (congrArg (· + 1) (intListLengthAppend rest ys)).trans (Nat.succ_add rest.length ys.length).symm

/-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` on `List SignedLetter` — the reverse-plumbing associativity. -/
theorem letterListAppendAssoc : ∀ xs ys zs : List SignedLetter, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | head :: rest, ys, zs => congrArg (head :: ·) (letterListAppendAssoc rest ys zs)

/-- `List.reverseAux xs acc = List.reverse xs ++ acc` on `List SignedLetter` — the accumulator-append law,
propext-clean via `letterListAppendAssoc` (the substitute for Init `List.reverse_cons`). -/
theorem reverseAuxAppend : ∀ xs acc : List SignedLetter,
    List.reverseAux xs acc = List.reverse xs ++ acc
  | [], _ => rfl
  | head :: rest, acc =>
      (reverseAuxAppend rest (head :: acc)).trans
        ((congrArg (fun tail => List.reverse rest ++ tail) (rfl : head :: acc = [head] ++ acc)).trans
          ((letterListAppendAssoc (List.reverse rest) [head] acc).symm.trans
            (congrArg (· ++ acc) (reverseAuxAppend rest [head]).symm)))

/-- `List.reverse (x :: xs) = List.reverse xs ++ [x]` on `List SignedLetter` — the reverse-cons law. -/
theorem reverseConsLaw (letter : SignedLetter) (xs : List SignedLetter) :
    List.reverse (letter :: xs) = List.reverse xs ++ [letter] :=
  reverseAuxAppend xs [letter]

/-! ## V1 — the list cyclic-rotation carrier (`ZZ[ZZ/n]` value type + the `t`-action) -/

/-- The forward `t`-action (`e_k ↦ e_{k-1}`, "head to tail"): move the head to the back.  Cons-structural,
no reverse. -/
def rotateForward : List Int → List Int
  | [] => []
  | head :: tail => tail ++ [head]

/-- The last element of a list (default `0` on empty) — cons-structural (two-cons recursion). -/
def lastElemD (dflt : Int) : List Int → Int
  | [] => dflt
  | [single] => single
  | _ :: second :: rest => lastElemD dflt (second :: rest)

/-- The initial segment (all but the last) — cons-structural. -/
def initSegment : List Int → List Int
  | [] => []
  | [_] => []
  | head :: second :: rest => head :: initSegment (second :: rest)

/-- The backward `t`-action (`e_k ↦ e_{k+1}`, "tail to head"): move the last element to the front.  The
inverse of `rotateForward`, cons-structural via `lastElemD`/`initSegment` (no reverse). -/
def rotateBackward : List Int → List Int
  | [] => []
  | head :: tail => lastElemD 0 (head :: tail) :: initSegment (head :: tail)

/-- The all-zeros vector of length `n` — structural, so its length is definitionally `n`. -/
def zeroVec : Nat → List Int
  | 0 => []
  | count + 1 => 0 :: zeroVec count

/-- The basis element `e₀ = t⁰` of `ZZ[ZZ/n]` — `1` then `n − 1` zeros, structural so its length is `n`. -/
def basisE0 : Nat → List Int
  | 0 => []
  | count + 1 => 1 :: zeroVec count

/-- Coefficientwise addition in `ZZ[ZZ/n]`. -/
def vecAdd (leftVec rightVec : List Int) : List Int := List.zipWith (· + ·) leftVec rightVec

/-- Coefficientwise negation in `ZZ[ZZ/n]`. -/
def vecNeg (vec : List Int) : List Int := vec.map (fun coeff => -coeff)

/-- Sign scaling `±v` by a `Bool` sign (`true = +`, `false = −`).  Full enum over the `Bool`. -/
def signScaleN : Bool → List Int → List Int
  | true, vec => vec
  | false, vec => vecNeg vec

/-- ★ **The separating functional** — the coefficient of the basis element `e₀ = t⁰` (index `0`).  A
bespoke full-enum projection, NEVER `List.getD`. -/
def headCoeff : List Int → Int
  | [] => 0
  | coeff :: _ => coeff

/-- The coefficient sum (augmentation `ε`) — used only to record that `ε` does NOT separate. -/
def coeffSum : List Int → Int
  | [] => 0
  | coeff :: rest => coeff + coeffSum rest

/-! ### V1 truth probes — the carrier ops on literals (evaluated in scratch before proving) -/

/-- Probe — `rotateForward` moves the head to the back: `rotateForward [1, 0, 0] = [0, 0, 1]`.  `rfl`. -/
theorem rotateForwardProbe : rotateForward [1, 0, 0] = [0, 0, 1] := rfl

/-- Probe — `rotateBackward` moves the last to the front: `rotateBackward [1, 0, 0] = [0, 1, 0]`.  `rfl`. -/
theorem rotateBackwardProbe : rotateBackward [1, 0, 0] = [0, 1, 0] := rfl

/-- Probe — `basisE0 3 = [1, 0, 0]` and `zeroVec 3 = [0, 0, 0]`.  `rfl`. -/
theorem basisE0Probe : basisE0 3 = [1, 0, 0] := rfl

/-- Probe — `vecAdd [1, 0] [-1, 1] = [0, 1]`.  `rfl`. -/
theorem vecAddProbe : vecAdd [1, 0] [-1, 1] = [0, 1] := rfl

/-! ### V1 length + algebra laws -/

/-- `(zeroVec n).length = n`. -/
theorem zeroVecLength : ∀ count : Nat, (zeroVec count).length = count
  | 0 => rfl
  | count + 1 => congrArg (· + 1) (zeroVecLength count)

/-- ★ `(basisE0 n).length = n` — the basis vector has length exactly `n` (case on `n`, no `Nat` sub). -/
theorem basisE0Length : ∀ count : Nat, (basisE0 count).length = count
  | 0 => rfl
  | count + 1 => congrArg (· + 1) (zeroVecLength count)

/-- `rotateForward` preserves length. -/
theorem rotateForwardLength : ∀ vec : List Int, (rotateForward vec).length = vec.length
  | [] => rfl
  | head :: tail => intListLengthAppend tail [head]

/-- `(initSegment (head :: tail)).length = tail.length` — the initial segment drops exactly the last. -/
theorem initSegmentLength : ∀ (head : Int) (tail : List Int),
    (initSegment (head :: tail)).length = tail.length
  | _, [] => rfl
  | _, second :: rest => congrArg (· + 1) (initSegmentLength second rest)

/-- `rotateBackward` preserves length. -/
theorem rotateBackwardLength : ∀ vec : List Int, (rotateBackward vec).length = vec.length
  | [] => rfl
  | head :: tail => congrArg (· + 1) (initSegmentLength head tail)

/-- `lastElemD 0 (t ++ [h]) = h` — the appended element is the last. -/
theorem lastElemDAppendSingle : ∀ (tail : List Int) (head : Int),
    lastElemD 0 (tail ++ [head]) = head
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: second :: rest, head => lastElemDAppendSingle (second :: rest) head

/-- `initSegment (t ++ [h]) = t` — dropping the appended element restores the prefix. -/
theorem initSegmentAppendSingle : ∀ (tail : List Int) (head : Int),
    initSegment (tail ++ [head]) = tail
  | [], _ => rfl
  | [_single], _ => rfl
  | first :: second :: rest, head =>
      congrArg (first :: ·) (initSegmentAppendSingle (second :: rest) head)

/-- `initSegment (h :: t) ++ [last (h :: t)] = h :: t` — init followed by last reconstructs. -/
theorem initAppendLast : ∀ (head : Int) (tail : List Int),
    initSegment (head :: tail) ++ [lastElemD 0 (head :: tail)] = head :: tail
  | _, [] => rfl
  | head, second :: rest => congrArg (head :: ·) (initAppendLast second rest)

/-- `rotateBackward (t ++ [h]) = h :: t` — the backward action on a snoc restores the moved element to the
front (cases on `t` so `rotateBackward` unfolds on the cons). -/
theorem rotateBackwardSnoc : ∀ (tail : List Int) (head : Int),
    rotateBackward (tail ++ [head]) = head :: tail
  | [], _ => rfl
  | first :: rest, head =>
      (congrArg (fun last => last :: initSegment (first :: (rest ++ [head])))
          (lastElemDAppendSingle (first :: rest) head)).trans
        (congrArg (head :: ·) (initSegmentAppendSingle (first :: rest) head))

/-- ★ `rotateBackward (rotateForward v) = v` — the backward action undoes the forward. -/
theorem rotateBackwardForward : ∀ vec : List Int, rotateBackward (rotateForward vec) = vec
  | [] => rfl
  | head :: tail => rotateBackwardSnoc tail head

/-- ★ `rotateForward (rotateBackward v) = v` — the forward action undoes the backward. -/
theorem rotateForwardBackward : ∀ vec : List Int, rotateForward (rotateBackward vec) = vec
  | [] => rfl
  | head :: tail => initAppendLast head tail

/-! ## V1 — the per-letter rotation fold (the invariant's residue engine) -/

/-- The `t`-action of a single signed letter — the generator index is IGNORED (one generator images to
`t`), so `pos` rotates forward, `neg` rotates backward.  Full enum on the sign. -/
def letterRotate : SignedLetter → List Int → List Int
  | .pos _, vec => rotateForward vec
  | .neg _, vec => rotateBackward vec

/-- **The rotation action of a free-group word** — a right fold of the per-letter rotations.  The
generalization of r2's `applyWordShift` from `ZmodThree` to the full `ZZⁿ` rotation. -/
def applyWordRotate : List SignedLetter → List Int → List Int
  | [], vec => vec
  | letter :: rest, vec => letterRotate letter (applyWordRotate rest vec)

/-- `letterRotate` preserves length (both signs). -/
theorem letterRotateLength : ∀ (letter : SignedLetter) (vec : List Int),
    (letterRotate letter vec).length = vec.length
  | .pos _, vec => rotateForwardLength vec
  | .neg _, vec => rotateBackwardLength vec

/-- `applyWordRotate` preserves length. -/
theorem applyWordRotateLength : ∀ (word : List SignedLetter) (vec : List Int),
    (applyWordRotate word vec).length = vec.length
  | [], _ => rfl
  | letter :: rest, vec =>
      (letterRotateLength letter (applyWordRotate rest vec)).trans (applyWordRotateLength rest vec)

/-- ★ **`applyWordRotate` is an append-fold**: `applyWordRotate (x ++ y) v = applyWordRotate x
(applyWordRotate y v)` — the residue action of `x · y` folds `x` onto `y`'s action. -/
theorem applyWordRotateAppend : ∀ (leftWord rightWord : List SignedLetter) (vec : List Int),
    applyWordRotate (leftWord ++ rightWord) vec
      = applyWordRotate leftWord (applyWordRotate rightWord vec)
  | [], _, _ => rfl
  | letter :: rest, rightWord, vec =>
      congrArg (letterRotate letter) (applyWordRotateAppend rest rightWord vec)

/-- Two mutually-inverse letters rotate to the identity — the residue is blind to a cancelling pair.
Full enum on the four sign combinations (`Bool.noConfusion` kills the same-sign impossibilities). -/
theorem letterRotateInverseCancel : ∀ (letter top : SignedLetter) (vec : List Int),
    areInverse letter top = true → letterRotate letter (letterRotate top vec) = vec
  | .pos _, .neg _, vec, _ => rotateForwardBackward vec
  | .neg _, .pos _, vec, _ => rotateBackwardForward vec
  | .pos _, .pos _, _, cancels => Bool.noConfusion cancels
  | .neg _, .neg _, _, cancels => Bool.noConfusion cancels

/-- Rotating by a letter then its inverse is the identity — the wound-and-unwound cancellation. -/
theorem letterRotateInverseSelf : ∀ (letter : SignedLetter) (vec : List Int),
    letterRotate letter (letterRotate (inverseLetter letter) vec) = vec
  | .pos _, vec => rotateForwardBackward vec
  | .neg _, vec => rotateBackwardForward vec

/-- ★ **`consReduced` preserves the rotation action** — free cancellation drops the annihilating pair or
extends, keyed by `areInverse`.  Mirror of r2's `consReducedResidue`. -/
theorem applyWordRotateConsReduced : ∀ (letter : SignedLetter) (word : List SignedLetter)
    (vec : List Int),
    applyWordRotate (consReduced letter word) vec = letterRotate letter (applyWordRotate word vec)
  | _, [], _ => rfl
  | letter, top :: rest, vec =>
      match hCancel : areInverse letter top with
      | true =>
          (congrArg (fun word => applyWordRotate word vec) (consReducedCancel letter top rest hCancel)).trans
            (letterRotateInverseCancel letter top (applyWordRotate rest vec) hCancel).symm
      | false =>
          congrArg (fun word => applyWordRotate word vec) (consReducedExtend letter top rest hCancel)

/-- ★★ **`reduceWord` preserves the rotation action** — free reduction never changes the residue action
(it only deletes `g g⁻¹` pairs).  Structural induction folding `applyWordRotateConsReduced`. -/
theorem applyWordRotateReduceInvariant : ∀ (word : List SignedLetter) (vec : List Int),
    applyWordRotate (reduceWord word) vec = applyWordRotate word vec
  | [], _ => rfl
  | letter :: rest, vec =>
      (applyWordRotateConsReduced letter (reduceWord rest) vec).trans
        (congrArg (letterRotate letter) (applyWordRotateReduceInvariant rest vec))

/-- The `invWord` cons law `invWord (letter :: rest) = invWord rest ++ [inverseLetter letter]`, ridden
off the propext-clean `reverseConsLaw`. -/
theorem invWordCons (letter : SignedLetter) (rest : List SignedLetter) :
    invWord (letter :: rest) = invWord rest ++ [inverseLetter letter] :=
  reverseConsLaw (inverseLetter letter) (List.map inverseLetter rest)

/-- ★ **A word's rotation composed with its inverse's is the identity**: `applyWordRotate w
(applyWordRotate (invWord w) v) = v`.  Induction on `w` through the `invWord` cons law. -/
theorem applyWordRotateInverseCancel : ∀ (word : List SignedLetter) (vec : List Int),
    applyWordRotate word (applyWordRotate (invWord word) vec) = vec
  | [], _ => rfl
  | letter :: rest, vec =>
      (congrArg (fun peeled => applyWordRotate (letter :: rest) peeled)
          ((congrArg (fun invLetterWord => applyWordRotate invLetterWord vec)
              (invWordCons letter rest)).trans
            (applyWordRotateAppend (invWord rest) [inverseLetter letter] vec))).trans
        ((congrArg (letterRotate letter)
            (applyWordRotateInverseCancel rest (letterRotate (inverseLetter letter) vec))).trans
          (letterRotateInverseSelf letter vec))

/-! ## V1 — the rotate-by-length cyclicity (the mod-free crux replacing r2's `relatorResidueIsZero`) -/

/-- `rotateForwardPow k v` — rotate forward `k` times (inner recursion, so the front-append cyclicity
threads). -/
def rotateForwardPow : Nat → List Int → List Int
  | 0, vec => vec
  | count + 1, vec => rotateForwardPow count (rotateForward vec)

/-- `rotateForward` commutes with `rotateForwardPow` (it is the same iterated map). -/
theorem rotateForwardPowCommute : ∀ (count : Nat) (vec : List Int),
    rotateForward (rotateForwardPow count vec) = rotateForwardPow count (rotateForward vec)
  | 0, _ => rfl
  | count + 1, vec => rotateForwardPowCommute count (rotateForward vec)

/-- `applyWordRotate (signPowerPos k) v = rotateForwardPow k v` — the positive `signPower` rotates
forward `k` times. -/
theorem applyWordRotateSignPowerPos : ∀ (count : Nat) (vec : List Int),
    applyWordRotate (signPowerPos count) vec = rotateForwardPow count vec
  | 0, _ => rfl
  | count + 1, vec =>
      (congrArg rotateForward (applyWordRotateSignPowerPos count vec)).trans
        (rotateForwardPowCommute count vec)

/-- ★★ **The front-append cyclicity** `rotateForwardPow (length front) (front ++ back) = back ++ front`
— rotating forward by the length of a prefix cycles that prefix to the back. -/
theorem rotateForwardPowFrontAppend : ∀ (front back : List Int),
    rotateForwardPow front.length (front ++ back) = back ++ front
  | [], back => (intListAppendNil back).symm
  | head :: tail, back =>
      (congrArg (rotateForwardPow tail.length) (intListAppendAssoc tail back [head])).trans
        ((rotateForwardPowFrontAppend tail (back ++ [head])).trans
          (intListAppendAssoc back [head] tail))

/-- ★★★ **Rotate-by-length is the identity** `rotateForwardPow (length v) v = v` — the mod-free
replacement for r2's `relatorResidueIsZero` (period-`n` cyclicity of a length-`n` vector). -/
theorem rotateForwardPowFixesLength (vec : List Int) :
    rotateForwardPow vec.length vec = vec :=
  (congrArg (rotateForwardPow vec.length) (intListAppendNil vec)).symm.trans
    (rotateForwardPowFrontAppend vec [])

/-- ★ **`signPowerPos n` fixes every length-`n` vector** — `applyWordRotate (signPowerPos n) w = w` when
`w.length = n`.  Bridges `applyWordRotate` to `rotateForwardPow` and applies the cyclicity. -/
theorem signPowerPosFixesLength (vec : List Int) (exponent : Nat) (hasLength : vec.length = exponent) :
    applyWordRotate (signPowerPos exponent) vec = vec :=
  (congrArg (fun count => applyWordRotate (signPowerPos count) vec) hasLength.symm).trans
    ((applyWordRotateSignPowerPos vec.length vec).trans (rotateForwardPowFixesLength vec))

/-- ★ **`invWord (signPowerPos n)` fixes every length-`n` vector** — the negative-relator crux, derived
from the positive cyclicity via the inverse-cancel law (no separate backward cyclicity needed). -/
theorem invSignPowerPosFixesLength (vec : List Int) (exponent : Nat) (hasLength : vec.length = exponent) :
    applyWordRotate (invWord (signPowerPos exponent)) vec = vec :=
  let inverseRotated : List Int := applyWordRotate (invWord (signPowerPos exponent)) vec
  let inverseRotatedLength : inverseRotated.length = exponent :=
    (applyWordRotateLength (invWord (signPowerPos exponent)) vec).trans hasLength
  let forwardCancels : applyWordRotate (signPowerPos exponent) inverseRotated = vec :=
    applyWordRotateInverseCancel (signPowerPos exponent) vec
  let forwardFixes : applyWordRotate (signPowerPos exponent) inverseRotated = inverseRotated :=
    signPowerPosFixesLength inverseRotated exponent inverseRotatedLength
  forwardFixes.symm.trans forwardCancels

/-! ## V2 — the invariant map `E → ZZ[ZZ/n]` and its interface parity with r2 -/

/-- **The image of a conjugator word in `ZZ[ZZ/n]`** — the basis vector `e₀` rotated once per letter.
The generalization of r2's `powerOfT (wordResidue w)`. -/
def conjugatorVecN (exponent : Nat) (word : List SignedLetter) : List Int :=
  applyWordRotate word (basisE0 exponent)

/-- **The invariant image of one conjugated relator** `±(w, r)` — the sign-scaled rotated basis vector.
The generalization of r2's `conjugatedRelatorImage`. -/
def conjugatedRelatorImageN (exponent : Nat) (gen : ConjugatedRelator) : List Int :=
  signScaleN gen.isPositive (conjugatorVecN exponent gen.conjugator)

/-- ★ **The separating invariant `E → ZZ[ZZ/n]`** — the additive extension over the free word, a right
fold summing the per-generator images.  The generalization of r2's `crossedModuleImage`. -/
def crossedModuleImageN (exponent : Nat) : PreCrossedElement → List Int
  | [] => zeroVec exponent
  | gen :: rest => vecAdd (conjugatedRelatorImageN exponent gen) (crossedModuleImageN exponent rest)

/-- `(conjugatorVecN n w).length = n` — the rotated basis keeps the basis length. -/
theorem conjugatorVecNLength (exponent : Nat) (word : List SignedLetter) :
    (conjugatorVecN exponent word).length = exponent :=
  (applyWordRotateLength word (basisE0 exponent)).trans (basisE0Length exponent)

/-- `vecNeg` preserves length. -/
theorem vecNegLength : ∀ vec : List Int, (vecNeg vec).length = vec.length
  | [] => rfl
  | _coeff :: rest => congrArg (· + 1) (vecNegLength rest)

/-- `signScaleN` preserves length (both signs). -/
theorem signScaleNLength : ∀ (sign : Bool) (vec : List Int),
    (signScaleN sign vec).length = vec.length
  | true, _ => rfl
  | false, vec => vecNegLength vec

/-- ★ `(conjugatedRelatorImageN n gen).length = n` — every generator image has length exactly `n`. -/
theorem conjugatedRelatorImageNLength (exponent : Nat) (gen : ConjugatedRelator) :
    (conjugatedRelatorImageN exponent gen).length = exponent :=
  (signScaleNLength gen.isPositive (conjugatorVecN exponent gen.conjugator)).trans
    (conjugatorVecNLength exponent gen.conjugator)

/-! ### V2 truth probes — the invariant on the r7 witness -/

/-- ★★ **The separating value at `n = 3`**: `image ζ₃ = [-1, 0, 1]` — matches r2's shipped `(−1, 1, 0)`
class as the `(s̄ − 1)` rotation class (here `t² − 1`).  `rfl`. -/
theorem rotationImageThreeProbe :
    crossedModuleImageN 3 cyclicPowerRotationWitness = [-1, 0, 1] := rfl

/-- Probe — `image ζ₄ = [-1, 0, 0, 1]` (the trailing zeros track `n`).  `rfl`. -/
theorem rotationImageFourProbe :
    crossedModuleImageN 4 cyclicPowerRotationWitness = [-1, 0, 0, 1] := rfl

/-- Probe — the empty word images to the zero vector.  `rfl`. -/
theorem emptyImageNProbe : crossedModuleImageN 3 ([] : PreCrossedElement) = [0, 0, 0] := rfl

/-! ### V2 abelian-group + append-homomorphism laws -/

/-- `vecAdd` associativity — coefficientwise `intAddAssoc` (holds unconditionally, `zipWith` aligns). -/
theorem vecAddAssoc : ∀ (leftVec middleVec rightVec : List Int),
    vecAdd (vecAdd leftVec middleVec) rightVec = vecAdd leftVec (vecAdd middleVec rightVec)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | leftHead :: leftRest, middleHead :: middleRest, rightHead :: rightRest =>
      (congrArg (· :: vecAdd (vecAdd leftRest middleRest) rightRest)
          (intAddAssoc leftHead middleHead rightHead)).trans
        (congrArg ((leftHead + (middleHead + rightHead)) :: ·)
          (vecAddAssoc leftRest middleRest rightRest))

/-- Coefficientwise congruence for `vecAdd`. -/
theorem vecAddCongr {leftA leftB rightA rightB : List Int}
    (hLeft : leftA = rightA) (hRight : leftB = rightB) :
    vecAdd leftA leftB = vecAdd rightA rightB :=
  (congrArg (fun vec => vecAdd vec leftB) hLeft).trans (congrArg (vecAdd rightA) hRight)

/-- Left identity `vecAdd (zeroVec (length w)) w = w` (self-length). -/
theorem vecAddZeroVecLeftSelf : ∀ vec : List Int, vecAdd (zeroVec vec.length) vec = vec
  | [] => rfl
  | coeff :: rest =>
      (congrArg (· :: vecAdd (zeroVec rest.length) rest) (intZeroAdd coeff)).trans
        (congrArg (coeff :: ·) (vecAddZeroVecLeftSelf rest))

/-- Right identity `vecAdd w (zeroVec (length w)) = w` (self-length). -/
theorem vecAddZeroVecRightSelf : ∀ vec : List Int, vecAdd vec (zeroVec vec.length) = vec
  | [] => rfl
  | coeff :: rest =>
      (congrArg (· :: vecAdd rest (zeroVec rest.length)) (intAddZero coeff)).trans
        (congrArg (coeff :: ·) (vecAddZeroVecRightSelf rest))

/-- `crossedModuleImageN n z` always has length `n`. -/
theorem vecAddLengthEq : ∀ (leftVec rightVec : List Int),
    leftVec.length = rightVec.length → (vecAdd leftVec rightVec).length = leftVec.length
  | [], [], _ => rfl
  | [], _ :: _, hLen => Nat.noConfusion hLen
  | _ :: _, [], hLen => Nat.noConfusion hLen
  | _ :: leftRest, _ :: rightRest, hLen =>
      congrArg (· + 1) (vecAddLengthEq leftRest rightRest (Nat.succ.inj hLen))

/-- ★ `(crossedModuleImageN n z).length = n` for every element `z`. -/
theorem crossedModuleImageNLength (exponent : Nat) : ∀ element : PreCrossedElement,
    (crossedModuleImageN exponent element).length = exponent
  | [] => zeroVecLength exponent
  | gen :: rest =>
      (vecAddLengthEq (conjugatedRelatorImageN exponent gen) (crossedModuleImageN exponent rest)
          ((conjugatedRelatorImageNLength exponent gen).trans
            (crossedModuleImageNLength exponent rest).symm)).trans
        (conjugatedRelatorImageNLength exponent gen)

/-- Left identity against `zeroVec n` on any length-`n` vector. -/
theorem vecAddZeroVecLeft (vec : List Int) (exponent : Nat) (hasLength : vec.length = exponent) :
    vecAdd (zeroVec exponent) vec = vec :=
  (congrArg (fun count => vecAdd (zeroVec count) vec) hasLength.symm).trans (vecAddZeroVecLeftSelf vec)

/-- Right identity against `zeroVec n` on any length-`n` vector. -/
theorem vecAddZeroVecRight (vec : List Int) (exponent : Nat) (hasLength : vec.length = exponent) :
    vecAdd vec (zeroVec exponent) = vec :=
  (congrArg (vecAdd vec) (congrArg zeroVec hasLength.symm)).trans (vecAddZeroVecRightSelf vec)

/-- ★ **The invariant is an append-homomorphism** — `image (x ++ y) = image x + image y`, by induction on
`x` folding left-identity (base) and associativity (step). -/
theorem crossedModuleImageNAppend (exponent : Nat) : ∀ (leftPart rightPart : PreCrossedElement),
    crossedModuleImageN exponent (leftPart ++ rightPart)
      = vecAdd (crossedModuleImageN exponent leftPart) (crossedModuleImageN exponent rightPart)
  | [], rightPart =>
      (vecAddZeroVecLeft (crossedModuleImageN exponent rightPart) exponent
        (crossedModuleImageNLength exponent rightPart)).symm
  | gen :: rest, rightPart =>
      (congrArg (vecAdd (conjugatedRelatorImageN exponent gen))
          (crossedModuleImageNAppend exponent rest rightPart)).trans
        (vecAddAssoc (conjugatedRelatorImageN exponent gen)
          (crossedModuleImageN exponent rest) (crossedModuleImageN exponent rightPart)).symm

/-! ## V3 — the exponent-`n` Peiffer relation and the Peiffer-invariance keystone -/

/-- **The `F`-action `^{∂ₙa}b` at exponent `n`** — keep `b`'s relator and sign, pre-multiply its
conjugator by the exponent-`n` boundary `∂ₙa`.  The exponent-parameterized `peifferConjugate`. -/
def peifferConjugateAt (exponent : Nat) (firstGen secondGen : ConjugatedRelator) : ConjugatedRelator :=
  { secondGen with
    conjugator := reduceWord (conjugatedRelatorBoundaryAt exponent firstGen ++ secondGen.conjugator) }

/-- ★ **The exponent-`n` Peiffer congruence** — the honest Peiffer relation of `⟨s | sⁿ⟩`, whose
generating move conjugates by the exponent-`n` boundary `∂ₙa` (net rotation `±n ≡ 0` in `ZZ/n`).  A
`Prop`-inductive (no `Quot`); the shipped `PeifferEquiv` is its `n = 3` specialization and cannot carry
the general claim (its move conjugates by the fixed `∂ = s³`). -/
inductive PeifferEquivAt (exponent : Nat) : PreCrossedElement → PreCrossedElement → Prop where
  /-- Reflexivity. -/
  | refl (element : PreCrossedElement) : PeifferEquivAt exponent element element
  /-- Symmetry. -/
  | symm {leftElement rightElement : PreCrossedElement} :
      PeifferEquivAt exponent leftElement rightElement → PeifferEquivAt exponent rightElement leftElement
  /-- Transitivity. -/
  | trans {leftElement middleElement rightElement : PreCrossedElement} :
      PeifferEquivAt exponent leftElement middleElement →
      PeifferEquivAt exponent middleElement rightElement →
      PeifferEquivAt exponent leftElement rightElement
  /-- Append-congruence. -/
  | congrAppend {leftA leftB rightA rightB : PreCrossedElement} :
      PeifferEquivAt exponent leftA rightA → PeifferEquivAt exponent leftB rightB →
      PeifferEquivAt exponent (leftA ++ leftB) (rightA ++ rightB)
  /-- ★ The generating Peiffer move `a b a⁻¹ ~ ^{∂ₙa}b` at exponent `n`. -/
  | peifferMove (firstGen secondGen : ConjugatedRelator) :
      PeifferEquivAt exponent [firstGen, secondGen, invGen firstGen]
        [peifferConjugateAt exponent firstGen secondGen]

/-- ★ **The invariant sends the formal inverse to negation**: `image (a⁻¹) = -(image a)`.  The generator
index is untouched by `invGen`, so only the sign flips.  Mirror of r2's `conjugatedRelatorImageInvGen`. -/
theorem conjugatedRelatorImageNInvGen (exponent : Nat) (gen : ConjugatedRelator) :
    conjugatedRelatorImageN exponent (invGen gen)
      = vecNeg (conjugatedRelatorImageN exponent gen) :=
  signScaleNNotIsNeg gen.isPositive (conjugatorVecN exponent gen.conjugator)
  where
    /-- Flipping the sign negates the scaled value: `signScaleN (not sign) v = -(signScaleN sign v)`. -/
    signScaleNNotIsNeg : ∀ (sign : Bool) (vec : List Int),
        signScaleN (Bool.not sign) vec = vecNeg (signScaleN sign vec)
      | true, _ => rfl
      | false, vec => (vecNegNeg vec).symm
    /-- `vecNeg (vecNeg v) = v` — double negation. -/
    vecNegNeg : ∀ vec : List Int, vecNeg (vecNeg vec) = vec
      | [] => rfl
      | coeff :: rest => (congrArg (· :: vecNeg (vecNeg rest)) (intNegNeg coeff)).trans
          (congrArg (coeff :: ·) (vecNegNeg rest))

/-- ★★ **The Peiffer crux: `∂ₙa` fixes every length-`n` vector** — `applyWordRotate (∂ₙa) v = v` when
`v.length = n`.  Because `applyWordRotate` ignores the generator index, `∂ₙa = w · s^{±n} · w⁻¹` reduces
(under the residue action) to conjugating the length-`n`-fixing `s^{±n}` by `w`; the `w`/`w⁻¹` rotations
cancel (`applyWordRotateInverseCancel`) and `s^{±n}` fixes length-`n` vectors (the rotate-cyclicity).
This is exactly r2's "`residue (∂a) = 0`" upgraded to the mod-free `ZZ[ZZ/n]` carrier. -/
theorem boundaryAtFixesLength : ∀ (exponent : Nat) (gen : ConjugatedRelator) (vec : List Int),
    vec.length = exponent →
    applyWordRotate (conjugatedRelatorBoundaryAt exponent gen) vec = vec
  | exponent, ⟨conjugatorWord, _, true⟩, vec, hasLength =>
      let innerVec : List Int := applyWordRotate (invWord conjugatorWord) vec
      let innerLength : innerVec.length = exponent :=
        (applyWordRotateLength (invWord conjugatorWord) vec).trans hasLength
      (applyWordRotateReduceInvariant
          (conjugatorWord ++ cyclicPowerRelator exponent ++ invWord conjugatorWord) vec).trans
        ((applyWordRotateAppend (conjugatorWord ++ cyclicPowerRelator exponent)
            (invWord conjugatorWord) vec).trans
          ((applyWordRotateAppend conjugatorWord (cyclicPowerRelator exponent) innerVec).trans
            ((congrArg (applyWordRotate conjugatorWord)
                (signPowerPosFixesLength innerVec exponent innerLength)).trans
              (applyWordRotateInverseCancel conjugatorWord vec))))
  | exponent, ⟨conjugatorWord, _, false⟩, vec, hasLength =>
      let innerVec : List Int := applyWordRotate (invWord conjugatorWord) vec
      let innerLength : innerVec.length = exponent :=
        (applyWordRotateLength (invWord conjugatorWord) vec).trans hasLength
      (applyWordRotateReduceInvariant
          (conjugatorWord ++ invWord (cyclicPowerRelator exponent) ++ invWord conjugatorWord) vec).trans
        ((applyWordRotateAppend (conjugatorWord ++ invWord (cyclicPowerRelator exponent))
            (invWord conjugatorWord) vec).trans
          ((applyWordRotateAppend conjugatorWord (invWord (cyclicPowerRelator exponent)) innerVec).trans
            ((congrArg (applyWordRotate conjugatorWord)
                (invSignPowerPosFixesLength innerVec exponent innerLength)).trans
              (applyWordRotateInverseCancel conjugatorWord vec))))

/-- ★★ **The Peiffer conjugator has the same rotated image** — `conjugatorVecN n (∂ₙa · b) =
conjugatorVecN n b`.  Reduction preserves the action, the append folds `∂ₙa` onto `b`'s action, and
`∂ₙa` fixes the length-`n` vector `image b`. -/
theorem peifferConjugatorVecEq (exponent : Nat) (firstGen secondGen : ConjugatedRelator) :
    conjugatorVecN exponent (peifferConjugateAt exponent firstGen secondGen).conjugator
      = conjugatorVecN exponent secondGen.conjugator :=
  (applyWordRotateReduceInvariant
      (conjugatedRelatorBoundaryAt exponent firstGen ++ secondGen.conjugator) (basisE0 exponent)).trans
    ((applyWordRotateAppend (conjugatedRelatorBoundaryAt exponent firstGen) secondGen.conjugator
        (basisE0 exponent)).trans
      (boundaryAtFixesLength exponent firstGen
        (applyWordRotate secondGen.conjugator (basisE0 exponent))
        ((applyWordRotateLength secondGen.conjugator (basisE0 exponent)).trans
          (basisE0Length exponent))))

/-- ★★ **The generating Peiffer move is invariant**: `image [a, b, a⁻¹] = image [^{∂ₙa}b]`.  The `a` and
`a⁻¹` terms cancel (`vecAddCancelMiddle` after `conjugatedRelatorImageNInvGen`), leaving `image b`; and
`^{∂ₙa}b` has the same image as `b` by `peifferConjugatorVecEq`.  Mirror of r2's `peifferMoveImage`. -/
theorem peifferMoveImageN (exponent : Nat) (firstGen secondGen : ConjugatedRelator) :
    crossedModuleImageN exponent [firstGen, secondGen, invGen firstGen]
      = crossedModuleImageN exponent [peifferConjugateAt exponent firstGen secondGen] :=
  let imageFirst : List Int := conjugatedRelatorImageN exponent firstGen
  let imageSecond : List Int := conjugatedRelatorImageN exponent secondGen
  let peifferConjugateImage :
      conjugatedRelatorImageN exponent (peifferConjugateAt exponent firstGen secondGen) = imageSecond :=
    congrArg (signScaleN secondGen.isPositive) (peifferConjugatorVecEq exponent firstGen secondGen)
  -- LHS = imageFirst + (imageSecond + (imageFirst-negated + 0)); cancel middle, drop trailing zero.
  (congrArg (fun trailing => vecAdd imageFirst (vecAdd imageSecond trailing))
      ((congrArg (fun neg => vecAdd neg (zeroVec exponent))
          (conjugatedRelatorImageNInvGen exponent firstGen)).trans
        (vecAddZeroVecRight (vecNeg imageFirst) exponent
          (vecNegLength imageFirst ▸ conjugatedRelatorImageNLength exponent firstGen)))).trans
    ((vecAddCancelMiddle imageFirst imageSecond
        ((conjugatedRelatorImageNLength exponent firstGen).trans
          (conjugatedRelatorImageNLength exponent secondGen).symm)).trans
      (peifferConjugateImage.symm.trans
        (vecAddZeroVecRight (conjugatedRelatorImageN exponent
            (peifferConjugateAt exponent firstGen secondGen)) exponent
          (conjugatedRelatorImageNLength exponent (peifferConjugateAt exponent firstGen secondGen))).symm))
  where
    /-- `vecAdd a (vecAdd b (vecNeg a)) = b` for equal-length `a, b` — the Peiffer `a`-cancellation. -/
    vecAddCancelMiddle : ∀ (outer inner : List Int),
        outer.length = inner.length → vecAdd outer (vecAdd inner (vecNeg outer)) = inner
      | [], [], _ => rfl
      | [], _ :: _, hLen => Nat.noConfusion hLen
      | _ :: _, [], hLen => Nat.noConfusion hLen
      | outerHead :: outerRest, innerHead :: innerRest, hLen =>
          (congrArg (· :: vecAdd outerRest (vecAdd innerRest (vecNeg outerRest)))
              (intCancelMiddle outerHead innerHead)).trans
            (congrArg (innerHead :: ·) (vecAddCancelMiddle outerRest innerRest (Nat.succ.inj hLen)))
    /-- `a + (b + -a) = b` — the seed of the coefficientwise cancellation (propext-clean Int kit). -/
    intCancelMiddle : ∀ outer inner : Int, outer + (inner + -outer) = inner
      | outer, inner =>
          (congrArg (fun summand => outer + summand) (intAddComm inner (-outer))).trans
            (((intAddAssoc outer (-outer) inner).symm).trans
              ((congrArg (fun summand => summand + inner) (intAddRightNeg outer)).trans
                (intZeroAdd inner)))

/-- ★★★ **THE PEIFFER-INVARIANCE KEYSTONE** — the invariant `crossedModuleImageN n` is constant on the
exponent-`n` Peiffer classes: `PeifferEquivAt n x y → crossedModuleImageN n x = crossedModuleImageN n y`.
Structural recursion on the `PeifferEquivAt` proof (the 5 arms): `refl` is `rfl`, `symm`/`trans` close the
equivalence, `congrAppend` uses the append-homomorphism, and the generating `peifferMove` is
`peifferMoveImageN`.  The soundness keystone — the invariant descends to the crossed module
`C = E/PeifferEquivAt`. -/
theorem crossedModuleImageRespectsPeifferAt (exponent : Nat) :
    ∀ {leftElement rightElement : PreCrossedElement},
    PeifferEquivAt exponent leftElement rightElement →
    crossedModuleImageN exponent leftElement = crossedModuleImageN exponent rightElement
  | _, _, .refl _ => rfl
  | _, _, .symm equivReversed => (crossedModuleImageRespectsPeifferAt exponent equivReversed).symm
  | _, _, .trans equivLeftMid equivMidRight =>
      (crossedModuleImageRespectsPeifferAt exponent equivLeftMid).trans
        (crossedModuleImageRespectsPeifferAt exponent equivMidRight)
  | _, _, .congrAppend equivLeftPair equivRightPair =>
      (crossedModuleImageNAppend exponent _ _).trans
        ((vecAddCongr (crossedModuleImageRespectsPeifferAt exponent equivLeftPair)
            (crossedModuleImageRespectsPeifferAt exponent equivRightPair)).trans
          (crossedModuleImageNAppend exponent _ _).symm)
  | _, _, .peifferMove firstGen secondGen => peifferMoveImageN exponent firstGen secondGen

/-! ## V4 — the separation (the headline `π₂⟨s | sⁿ⟩ ≠ 0` ∀ n ≥ 2) + the n = 1 degenerate control -/

/-- ★★ **The separating value for every `n ≥ 2`**: `headCoeff (image ζₙ) = −1`.  The image's first
coefficient is `head (rotateForward (basisE0 n)) + (− head (basisE0 n)) = 0 + (−1) = −1` (the last entry
of `basisE0 (m+2)` is `0`), computed by `rfl` regardless of `m`. -/
theorem rotationImageHeadCoeffAtLeastTwo (predPred : Nat) :
    headCoeff (crossedModuleImageN (predPred + 2) cyclicPowerRotationWitness) = -1 := rfl

/-- The empty word's image has `headCoeff 0` (the zero vector). -/
theorem emptyImageHeadCoeff : ∀ exponent : Nat,
    headCoeff (crossedModuleImageN exponent ([] : PreCrossedElement)) = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- ★★★ **`ζₙ` IS SEPARATED FROM THE EMPTY WORD ∀ `n ≥ 2`** — `image ζₙ ≠ image []`, refuted by projecting
`headCoeff` (`−1 ≠ 0` by `Int.decEq`).  The `2 ≤ n` hypothesis destructs `n = predPred + 2`; the cases
`n = 0, 1` are absurd. -/
theorem rotationImageSeparatesN : ∀ {exponent : Nat}, 2 ≤ exponent →
    crossedModuleImageN exponent cyclicPowerRotationWitness
      ≠ crossedModuleImageN exponent ([] : PreCrossedElement)
  | 0, atLeastTwo => absurd atLeastTwo (by decide)
  | 1, atLeastTwo => absurd atLeastTwo (by decide)
  | predPred + 2, _ => fun imagesEqual =>
      absurd
        ((rotationImageHeadCoeffAtLeastTwo predPred).symm.trans
          ((congrArg headCoeff imagesEqual).trans (emptyImageHeadCoeff (predPred + 2))))
        (by decide)

/-- ★★★ **`ζₙ` IS A NONTRIVIAL IDENTITY AMONG RELATIONS ∀ `n ≥ 2`** — `¬ PeifferEquivAt n ζₙ []`.  If `ζₙ`
were exponent-`n` Peiffer-trivial the invariant would force `image ζₙ = image []`, contradicting the
separation.  Combined with r7's `rotationBoundaryVanishesAt` (`∂ₙ ζₙ = []`, `ζₙ ∈ ker ∂ₙ`), this exhibits
`ζₙ` as a nontrivial element of `π₂⟨s | sⁿ⟩` for EVERY `n ≥ 2` — Lyndon's `π₂ ≠ 0` mechanized at general
`n`, at the element level, via the separating `ZZ[ZZ/n]`-invariant.  NOT claimed: the relation-module iso
`π₂ ≅ ZZ[G]/(N)` (the injectivity node stays walled). -/
theorem rotationNotPeifferTrivialN {exponent : Nat} (atLeastTwo : 2 ≤ exponent) :
    ¬ PeifferEquivAt exponent cyclicPowerRotationWitness ([] : PreCrossedElement) :=
  fun peifferTrivial =>
    absurd (crossedModuleImageRespectsPeifferAt exponent peifferTrivial)
      (rotationImageSeparatesN atLeastTwo)

/-! ### The n = 1 degenerate control — the separation correctly does NOT fire -/

/-- ★ **The degenerate control at `n = 1`** — `image ζ₁ = image [] = [0]`: the separation does NOT fire.
At `n = 1` the residues `1` and `0` collapse (`rotateForward [1] = [1]`), so `+e₀ + (−e₀) = 0`.  This
tracks Lyndon (`s¹` is not a proper power, `π₂ = 0`); the `2 ≤ n` hypothesis is load-bearing.  `rfl`. -/
theorem rotationImageDegenerateAtOne :
    crossedModuleImageN 1 cyclicPowerRotationWitness = crossedModuleImageN 1 ([] : PreCrossedElement) :=
  rfl

/-- ★ **The augmentation `ε` does NOT separate** — `coeffSum (image ζₙ) = 0` for `n = 3` (and every `n`):
the abelianized/trivial-coefficient shadow vanishes, exactly why the separation must be the single
`e₀`-projection (`headCoeff`), never the sum.  `rfl`. -/
theorem rotationImageAugmentationVanishesThree :
    coeffSum (crossedModuleImageN 3 cyclicPowerRotationWitness) = 0 := rfl

/-! ## V4 — the r8 ledger (records over the shipped r7 status inductive) -/

/-- The four r8 obligations, honestly classified against r7's `CyclicPowerObligationStatus`. -/
structure CyclicPowerInvariantLedger where
  /-- The `ZZ[ZZ/n]` list-rotation carrier + its abelian/cyclicity laws (V1). -/
  carrierStatus : CyclicPowerObligationStatus
  /-- The invariant map `E → ZZ[ZZ/n]` + append-homomorphism (V2). -/
  invariantMapStatus : CyclicPowerObligationStatus
  /-- The exponent-`n` Peiffer-invariance keystone `crossedModuleImageRespectsPeifferAt` (V3). -/
  peifferInvarianceStatus : CyclicPowerObligationStatus
  /-- The separation `π₂⟨s | sⁿ⟩ ≠ 0` ∀ `n ≥ 2` (`rotationNotPeifferTrivialN`) (V4). -/
  separationStatus : CyclicPowerObligationStatus
  /-- The relation-module iso `π₂ ≅ ZZ[G]/(N)` — the still-walled injectivity node. -/
  relationModuleIsoStatus : CyclicPowerObligationStatus

/-- ★ **The r8 general-separating-invariant ledger.**  The carrier, the invariant map, the exponent-`n`
Peiffer-invariance, and the separation are all SHIPPED zero-axiom; the full relation-module iso stays the
walled injectivity node (the inherited r6/r8 residual).  The honest r8 close: `π₂⟨s | sⁿ⟩ ≠ 0` is
MECHANIZED for every `n ≥ 2` (Lyndon promoted from cited to proved), with `n = 1` correctly degenerate. -/
def cyclicPowerInvariantLedger : CyclicPowerInvariantLedger :=
  { carrierStatus := CyclicPowerObligationStatus.shippedThisRound
  , invariantMapStatus := CyclicPowerObligationStatus.shippedThisRound
  , peifferInvarianceStatus := CyclicPowerObligationStatus.shippedThisRound
  , separationStatus := CyclicPowerObligationStatus.shippedThisRound
  , relationModuleIsoStatus := CyclicPowerObligationStatus.inheritedHopfResidual }

/-- ★ **The #2199 r8 general-separating-invariant marker.**  Shipped zero-axiom over r7:

  * **V1 (carrier)** — the `ZZ[ZZ/n] ≅ ZZⁿ` list-rotation carrier (`rotateForward`/`rotateBackward` mutual
    inverses, `basisE0`/`zeroVec`, `vecAdd`/`vecNeg`), with the mod-free rotate-cyclicity crux
    `rotateForwardPowFixesLength` replacing r2's `ZmodThree` `relatorResidueIsZero` `rfl`.
  * **V2 (invariant map)** — `crossedModuleImageN : E → ZZ[ZZ/n]` with its length invariant and the
    append-homomorphism `crossedModuleImageNAppend`; the `n = 3` image `[-1, 0, 1]` recovers r2's `(s̄ − 1)`
    rotation class.
  * **V3 (Peiffer-invariance)** — the honest exponent-`n` Peiffer relation `PeifferEquivAt n` (the shipped
    `PeifferEquiv` is its `n = 3` specialization and cannot carry general `n`), the crux
    `boundaryAtFixesLength` (`∂ₙa` fixes length-`n` vectors — the mod-free `residue (∂a) = 0`), and the
    keystone `crossedModuleImageRespectsPeifferAt`.
  * **V4 (separation)** — ★★★ `rotationNotPeifferTrivialN`: `π₂⟨s | sⁿ⟩ ≠ 0` for EVERY `n ≥ 2`, via the
    single-coefficient functional `headCoeff (image ζₙ) = −1 ≠ 0` (the augmentation `ε` provably does NOT
    separate); with the `n = 1` degenerate control (`rotationImageDegenerateAtOne`) correctly NOT firing.

The honest ceiling: the full relation-module iso `π₂ ≅ ZZ[G]/(N)` (free rank `1`) needs the general
injectivity node, which stays walled (the invariant separates but does not surject onto `π₂` at general
`n`).  Read the meaning from THIS docstring and the top-of-file design (the honest-record convention). -/
def crossedModuleCyclicPowerInvariantIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
