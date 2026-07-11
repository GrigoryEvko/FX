import FX1Poly.Polygraph.Homology.HopfShadowCokerGroupIsoCertificate

/-! # FX1Poly/Polygraph/Homology/HopfShadowCokerGroupIsoReflectsCertificate — the REFLECTS converse
    `nf v = nf w -> cokerRel v w`, the retraction round-trip, and the two-sided setoid iso
    (TOWER-ANICK r9, #2144)

## What r8 left, and what this r9 file DISCHARGES

r8 (`Homology/HopfShadowCokerGroupIsoCertificate`) shipped `nf : ZZ^2 / im(M) -> ZZ/3` as a well-defined
SURJECTIVE group homomorphism with a section (`cokerSectionRoundTrip`), three distinct classes
(`cokerRepsAreDistinct*`), and the group-hom law (`cokerAdditionLaw`), all resting on the KEYSTONE
`intResidue3Add`.  It NAMED the missing converse `nf v = nf w -> cokerRel v w` (injectivity) as the
residual `hopfShadowCokerGroupIsoReflectsIsNamedNode`, whose witness recipe its docstring already spelled:
"`nf v = nf w` gives `phi(v - w) = 3 k`; then `b := k`, `a := k - (v.1 - w.1)`".

This r9 file discharges exactly that residual, ADDITIVELY (r8 is untouched / frozen).  Delivered:

  * ★ `intResidue3ZeroDivides` — the CONSTRUCTIVE div-by-3 extraction `intResidue3 x = 0 -> exists k, x = 3 k`,
    built by the SAME period-3 structural recursion as `natResidue3` (never `Int.emod`, never any `x / 3`);
    the sole kit dependency is `intMulNeg`.  Backed by `natResidue3ZeroDivides` (period-3 on `n + 3`);
  * ★ `intResidue3Neg` / `intResidue3Sub` — the residue of a negation / a difference, lifting the keystone
    `intResidue3Add` across `-` through `negZmod3` (`intResidue3Neg` rides `negZmod3Involutive`);
  * ★ `reflectsFirst` / `reflectsSecond` — the two witness-component identities `d1 = -(k - d1) + k` and
    (given `d1 - d2 = 3 k`) `d2 = -(k - d1) - 2 k`, the explicit `im(M)`-membership reconstruction;
  * ★★ `cokerNormalFormReflects` — THE REFLECTS (injectivity) direction `nf v = nf w -> cokerRel v w`, the
    r8-named node `hopfShadowCokerGroupIsoReflectsIsNamedNode` discharged: residue-zero on the difference
    (`intResidue3Sub` + `addZmod3RightNeg`), the cross-sub rearrangement (`intCrossSubRearrange`), the
    constructive `k` (`intResidue3ZeroDivides`), the witnesses `a = k - (v.1 - w.1)`, `b = k`;
  * ★★ `cokerRetractionRoundTrip` — the RETRACTION `cokerRel v (rep (nf v))`, free from reflects + the r8
    section;
  * the r9 completion markers `hopfShadowCokerGroupIsoReflectsIsComplete` (the injectivity node discharged)
    and `hopfShadowCokerGroupIsoTwoSidedIsComplete` (section + retraction + respects + reflects together are
    the two-sided setoid iso `coker M ~= ZZ/3`, never `Quot`).

## Zero-axiom / LANE-LAW design decisions

  * SETOID route: the two-sided iso is section (`cokerSectionRoundTrip`, r8) + retraction
    (`cokerRetractionRoundTrip`) + well-definedness (`cokerNormalFormRespects`, r8) + injectivity
    (`cokerNormalFormReflects`), all as explicit witnesses over `intResidue3`.  NEVER `Quot` / `Quot.sound`.
  * The div-by-3 extraction is CONSTRUCTIVE, mirroring `natResidue3`/`intResidue3ThreeMultiple`: base
    `0/1/2` (the `1`/`2` arms are `ZmodThree.noConfusion` on the defeq residue, never `decide`), period step
    `n + 3` folds the recursion, the `negSucc` sign arm rides `negZmod3EqZeroImpliesZero`.
  * All `Int` arithmetic rides the propext-CLEAN kit (`FX1Poly.ComputerAlgebra`): `intMulNeg`, `intNegSub`,
    `intSubEqAddNeg`, `intAddAssoc`, `intAddLeftNeg`, `intAddRightNeg`, `intNegAdd`, `intNegNeg`,
    `intZeroAdd`, `intAddZero` + the r8-locals `intCrossSubRearrange` / `threeTimesRightExpand`.  Init's
    `Int.add_comm` / `add_assoc` / `mul_neg` are NEVER opened.
  * Every `match` on `ZmodThree` is FULLY enumerated (`negZmod3Involutive` / `negZmod3EqZeroImpliesZero`
    are 3-arm) — no `_ =>` wildcard, no match-compiler propext leak.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Structural
recursion only (fuel/`Nat`).  Per-declaration gated (and independently `#print axioms`-cross-checked for the
load-bearing decls) in `FX1PolyAudit/Polygraph/Homology/HopfShadowCokerGroupIsoReflectsCertificate.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## BRICK 1 — the `ZmodThree` negation facts the residue-of-negation lift needs -/

/-- `negZmod3` is an involution — the 3-arm `rfl` enum. -/
theorem negZmod3Involutive : ∀ residue : ZmodThree, negZmod3 (negZmod3 residue) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `negZmod3 r = 0` forces `r = 0` — the `residue0` arm is `rfl`, the `residue1`/`residue2` arms are
`ZmodThree.noConfusion` on the defeq-reduced residue (never `decide`; no `DecidableEq ZmodThree`). -/
theorem negZmod3EqZeroImpliesZero : ∀ residue : ZmodThree,
    negZmod3 residue = ZmodThree.residue0 → residue = ZmodThree.residue0
  | .residue0, _ => rfl
  | .residue1, negatedIsZero => ZmodThree.noConfusion negatedIsZero
  | .residue2, negatedIsZero => ZmodThree.noConfusion negatedIsZero

/-! ## BRICK 2 — the residue of a negation and of a difference (lifting the keystone across `-`) -/

/-- The residue of a negation is the negation of the residue: `residue (-x) = -(residue x)`.  Sign-split
on the `Int` constructor; the `negSucc` arm collapses the double negation via `negZmod3Involutive`. -/
theorem intResidue3Neg : ∀ value : Int, intResidue3 (-value) = negZmod3 (intResidue3 value)
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc predecessor => (negZmod3Involutive (natResidue3 (predecessor + 1))).symm

/-- The residue of a difference: `residue (a - b) = residue a + (-(residue b))`.  Subtraction IS addition
of the negation (`intSubEqAddNeg`), then the KEYSTONE `intResidue3Add` plus `intResidue3Neg`. -/
theorem intResidue3Sub (minuend subtrahend : Int) :
    intResidue3 (minuend - subtrahend)
      = addZmod3 (intResidue3 minuend) (negZmod3 (intResidue3 subtrahend)) :=
  (congrArg intResidue3 (intSubEqAddNeg minuend subtrahend)).trans
    ((intResidue3Add minuend (-subtrahend)).trans
      (congrArg (addZmod3 (intResidue3 minuend)) (intResidue3Neg subtrahend)))

/-! ## BRICK 3 — the CONSTRUCTIVE div-by-3 extraction (mirroring `natResidue3` / `intResidue3ThreeMultiple`)

There is no `x = 3 * (x / 3)` and no repo `intDiv3`; this produces the quotient CONSTRUCTIVELY by the same
period-3 structural recursion the residue itself runs on — the honest constructive converse of
`intResidue3ThreeMultiple`. -/

/-- The `Nat` residue is `0` only on multiples of three, WITH the constructive witness `value = 3 * k`.
Period-3 structural recursion: base `0` is `k = 0`; the `1`/`2` bases are `ZmodThree.noConfusion` (the
residue reduces to `residue1`/`residue2`, impossible against `residue0`); the `value + 3` step folds the
recursion (`3 * (k + 1) = 3 * k + 3` definitionally). -/
theorem natResidue3ZeroDivides :
    ∀ value : Nat, natResidue3 value = ZmodThree.residue0 → ∃ quotient : Nat, value = 3 * quotient
  | 0, _ => ⟨0, rfl⟩
  | 1, residueIsZero => ZmodThree.noConfusion residueIsZero
  | 2, residueIsZero => ZmodThree.noConfusion residueIsZero
  | value + 3, residueIsZero =>
      match natResidue3ZeroDivides value residueIsZero with
      | ⟨quotient, quotientEq⟩ => ⟨quotient + 1, congrArg (· + 3) quotientEq⟩

/-- ★ The `Int` residue is `0` only on multiples of three, WITH the constructive witness `x = 3 * k`.  The
`ofNat` arm folds `natResidue3ZeroDivides` (`Int.ofNat (3 k) = 3 * Int.ofNat k` definitionally); the
`negSucc` arm peels `negZmod3` (`negZmod3EqZeroImpliesZero`) then negates the witness through `intMulNeg`
(`negSucc n = -(ofNat (n+1))`, `-(ofNat k) = negOfNat k` definitionally). -/
theorem intResidue3ZeroDivides :
    ∀ value : Int, intResidue3 value = ZmodThree.residue0 → ∃ quotient : Int, value = 3 * quotient
  | .ofNat natValue, residueIsZero =>
      match natResidue3ZeroDivides natValue residueIsZero with
      | ⟨quotientNat, quotientEq⟩ => ⟨Int.ofNat quotientNat, congrArg Int.ofNat quotientEq⟩
  | .negSucc predecessor, residueIsZero =>
      match natResidue3ZeroDivides (predecessor + 1)
          (negZmod3EqZeroImpliesZero (natResidue3 (predecessor + 1)) residueIsZero) with
      | ⟨quotientNat, quotientEq⟩ =>
          ⟨Int.negOfNat quotientNat,
            (congrArg (fun exponent => -(Int.ofNat exponent)) quotientEq).trans
              (intMulNeg 3 (Int.ofNat quotientNat)).symm⟩

/-! ## BRICK 4 — the two subtractive keystones the witness components need -/

/-- `(a - b) + b = a` — expand the difference, reassociate, cancel `-b + b`. -/
theorem intSubAddCancel (target base : Int) : (target - base) + base = target :=
  (congrArg (· + base) (intSubEqAddNeg target base)).trans
    ((intAddAssoc target (-base) base).trans
      ((congrArg (target + ·) (intAddLeftNeg base)).trans (intAddZero target)))

/-- `a - (a - b) = b` — expand both differences, flip `-(a + -b) = -a + b`, reassociate, cancel `a + -a`. -/
theorem intSubSubCancel (whole part : Int) : whole - (whole - part) = part :=
  (intSubEqAddNeg whole (whole - part)).trans
    ((congrArg (whole + ·)
        ((congrArg Int.neg (intSubEqAddNeg whole part)).trans
          ((intNegAdd whole (-part)).trans (congrArg (-whole + ·) (intNegNeg part))))).trans
      ((intAddAssoc whole (-whole) part).symm.trans
        ((congrArg (· + part) (intAddRightNeg whole)).trans (intZeroAdd part))))

/-- `(p - q) - (2 q) = p - (q + 2 q)` — expand both differences, reassociate, refold the merged `-(q + 2 q)`. -/
theorem intSubSubMerge (head twice : Int) :
    (head - twice) - (2 * twice) = head - (twice + 2 * twice) :=
  (intSubEqAddNeg (head - twice) (2 * twice)).trans
    ((congrArg (· + -(2 * twice)) (intSubEqAddNeg head twice)).trans
      ((intAddAssoc head (-twice) (-(2 * twice))).trans
        ((congrArg (head + ·) (intNegAdd twice (2 * twice)).symm).trans
          (intSubEqAddNeg head (twice + 2 * twice)).symm)))

/-! ## BRICK 5 — the two witness-component identities `d1 = -(k - d1) + k` and `d2 = -(k - d1) - 2 k` -/

/-- The first `im(M)`-column reconstruction `d1 = -(k - d1) + k` (independent of the `3 k` relation).  With
`a := k - d1`, `b := k`, this is the first component `d1 = -a + b` of the `cokerRel` membership. -/
theorem reflectsFirst (firstDelta multiple : Int) :
    firstDelta = -(multiple - firstDelta) + multiple :=
  ((congrArg (· + multiple) (intNegSub multiple firstDelta)).trans
    (intSubAddCancel firstDelta multiple)).symm

/-- The second `im(M)`-column reconstruction `d2 = -(k - d1) - 2 k`, given `d1 - d2 = 3 k`.  With
`a := k - d1`, `b := k`, this is the second component `d2 = -a - 2 b` of the `cokerRel` membership.  Rides
`intSubSubMerge`, `threeTimesRightExpand` (r8), the `3 k` relation, and `intSubSubCancel`. -/
theorem reflectsSecond (firstDelta secondDelta multiple : Int)
    (relationDelta : firstDelta - secondDelta = 3 * multiple) :
    secondDelta = -(multiple - firstDelta) - 2 * multiple :=
  ((congrArg (· - 2 * multiple) (intNegSub multiple firstDelta)).trans
    ((intSubSubMerge firstDelta multiple).trans
      ((congrArg (firstDelta - ·) (threeTimesRightExpand multiple).symm).trans
        ((congrArg (firstDelta - ·) relationDelta.symm).trans
          (intSubSubCancel firstDelta secondDelta))))).symm

/-! ## BRICK 6 — THE REFLECTS (injectivity) direction, the retraction, and the completion markers -/

/-- ★★ **THE REFLECTS (injectivity) direction** `nf v = nf w -> cokerRel v w` — the r8-named node
`hopfShadowCokerGroupIsoReflectsIsNamedNode` discharged.  Mechanics: `nf v = nf w` gives
`intResidue3 ((v.1 - w.1) - (v.2 - w.2)) = 0` (`intResidue3Sub` substituted with `h` + `addZmod3RightNeg`,
after the `intCrossSubRearrange` cross-sub rearrangement); `intResidue3ZeroDivides` extracts the
CONSTRUCTIVE `k` with `(v.1 - w.1) - (v.2 - w.2) = 3 k`; the witnesses are `a := k - (v.1 - w.1)`, `b := k`
(`reflectsFirst` / `reflectsSecond`). -/
theorem cokerNormalFormReflects (leftPair rightPair : Int × Int)
    (normalFormsAgree : cokerNormalForm leftPair = cokerNormalForm rightPair) :
    cokerRel leftPair rightPair :=
  let differenceResidueIsZero :
      intResidue3 ((leftPair.1 - rightPair.1) - (leftPair.2 - rightPair.2)) = ZmodThree.residue0 :=
    (congrArg intResidue3
        (intCrossSubRearrange leftPair.1 leftPair.2 rightPair.1 rightPair.2).symm).trans
      ((intResidue3Sub (leftPair.1 - leftPair.2) (rightPair.1 - rightPair.2)).trans
        ((congrArg
            (fun residue => addZmod3 residue (negZmod3 (intResidue3 (rightPair.1 - rightPair.2))))
            normalFormsAgree).trans
          (addZmod3RightNeg (intResidue3 (rightPair.1 - rightPair.2)))))
  match intResidue3ZeroDivides
      ((leftPair.1 - rightPair.1) - (leftPair.2 - rightPair.2)) differenceResidueIsZero with
  | ⟨multiple, relationDelta⟩ =>
      ⟨multiple - (leftPair.1 - rightPair.1), multiple,
        reflectsFirst (leftPair.1 - rightPair.1) multiple,
        reflectsSecond (leftPair.1 - rightPair.1) (leftPair.2 - rightPair.2) multiple relationDelta⟩

/-- ★★ **THE RETRACTION round-trip** `cokerRel v (rep (nf v))` — the other half of the bijection, free from
reflects + the r8 section `cokerSectionRoundTrip` (`nf (rep (nf v)) = nf v`, so `v` and `rep (nf v)` share a
normal form, hence are `cokerRel`-related). -/
theorem cokerRetractionRoundTrip (pair : Int × Int) :
    cokerRel pair (cokerRep (cokerNormalForm pair)) :=
  cokerNormalFormReflects pair (cokerRep (cokerNormalForm pair))
    (cokerSectionRoundTrip (cokerNormalForm pair)).symm

/-! ### Truth-probes — the reflects witnesses on concrete same-class pairs (positive, negative, large `d`) -/

/-- Probe — the explicit-witness `cokerRel (0, -3) ~ (0, 0)` with `a = b = 1`, MATCHING the r8 verifier
witness (difference `d = (0, 3)`, `k = 1`).  `rfl` on both components. -/
theorem cokerRelConcreteWitnessProbe : cokerRel (0, -3) (0, 0) := ⟨1, 1, rfl, rfl⟩

/-- Probe — a NEGATIVE `a`-witness: `cokerRel (1, 0) ~ (-5, 0)` with `a = -4`, `b = 2` (difference
`d1 = 6`, `d2 = 0`, `k = 2`).  `rfl` on both components. -/
theorem cokerRelNegativeWitnessProbe : cokerRel (1, 0) (-5, 0) := ⟨-4, 2, rfl, rfl⟩

/-- Probe — the REFLECTS machinery run on the concrete same-class pair `(0, -3) ~ (0, 0)` (both `nf = 0`). -/
theorem cokerReflectsConcreteProbe : cokerRel (0, -3) (0, 0) :=
  cokerNormalFormReflects (0, -3) (0, 0) rfl

/-- Probe — REFLECTS on a NEGATIVE-difference same-class pair `(-5, 0) ~ (1, 0)` (both `nf = residue1`). -/
theorem cokerReflectsNegativeProbe : cokerRel (-5, 0) (1, 0) :=
  cokerNormalFormReflects (-5, 0) (1, 0) rfl

/-- Probe — REFLECTS on a LARGE lattice vector `(1, -8) ~ (0, 0)` (difference `9 = 3 * 3`, both `nf = 0`). -/
theorem cokerReflectsLargeProbe : cokerRel (1, -8) (0, 0) :=
  cokerNormalFormReflects (1, -8) (0, 0) rfl

/-- Probe — the CONSTRUCTIVE div-by-3 extraction on a concrete large positive `9 = 3 * 3`. -/
theorem intResidue3ZeroDividesConcreteProbe : ∃ quotient : Int, (9 : Int) = 3 * quotient :=
  intResidue3ZeroDivides 9 rfl

/-- Probe — the CONSTRUCTIVE div-by-3 extraction on a concrete large NEGATIVE `-9 = 3 * (-3)`. -/
theorem intResidue3ZeroDividesNegativeProbe : ∃ quotient : Int, (-9 : Int) = 3 * quotient :=
  intResidue3ZeroDivides (-9) rfl

/-! ## The r9 ledger markers (honest scope) — the REFLECTS node discharged, the two-sided iso assembled -/

/-- ★ **The REFLECTS (injectivity) node is DISCHARGED.**  This r9 file ships `cokerNormalFormReflects`
(`nf v = nf w -> cokerRel v w`) via the CONSTRUCTIVE div-by-3 extraction `intResidue3ZeroDivides` and the
explicit `im(M)`-membership witnesses `a = k - (v.1 - w.1)`, `b = k` (`reflectsFirst` / `reflectsSecond`),
all zero-axiom over the frozen r8 keystone `intResidue3Add`.  This is the honest upgrade of the r8-named
residual `hopfShadowCokerGroupIsoReflectsIsNamedNode` (r8 stays frozen; this NEW file discharges it).  Read
the meaning from THIS docstring (the honest-record convention).  `= true`. -/
def hopfShadowCokerGroupIsoReflectsIsComplete : Bool := true

/-- ★★ **The TWO-SIDED setoid iso `coker M ~= ZZ/3` is ASSEMBLED** (TOWER-ANICK #2144 r9).  With the r8
half — section `cokerSectionRoundTrip` (`nf (rep r) = r`), well-definedness `cokerNormalFormRespects`
(`nf` constant on `cokerRel` classes), group-hom law `cokerAdditionLaw`, three distinct classes
`cokerRepsAreDistinct*` — and the r9 half — injectivity `cokerNormalFormReflects` (`nf v = nf w -> cokerRel
v w`) and the retraction `cokerRetractionRoundTrip` (`cokerRel v (rep (nf v))`) — the normal form `nf` is a
BIJECTIVE group homomorphism `ZZ^2 / im(M) -> ZZ/3` on the setoid: both round-trips hold, `nf` is
well-defined and injective on classes, and it is additive.  The literal Hopf-shadow coker group iso is
thereby delivered two-sided, zero-axiom, SETOID-based (never `Quot`).  No overclaim.  Read the meaning from
THIS docstring (the honest-record convention). -/
def hopfShadowCokerGroupIsoTwoSidedIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
