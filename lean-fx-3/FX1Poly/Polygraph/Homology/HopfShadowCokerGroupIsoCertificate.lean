import FX1Poly.Polygraph.Homology.HopfShadowCokerSmithCertificate

/-! # FX1Poly/Polygraph/Homology/HopfShadowCokerGroupIsoCertificate — the LITERAL coker group iso
    `coker M = ZZ^2 / im(M) -> ZZ/3` as a setoid normal form (no `Quot`), delivering the r7-named
    residual `hopfShadowCokerGroupIsoIsNamedNode` at the SET-plus-group-hom level (TOWER-ANICK r8, #2144)

## What r7 left, and what this r8 file DELIVERS

r7 (`Homology/HopfShadowCokerSmithCertificate`) shipped the coker's Smith INVARIANT `<0, [3]>` backed by
a machine-checked unimodular reduction certificate `M = [[-1,1],[-1,-2]] -> diag(1, 3)`, and NAMED the
literal type-level carrier iso `coker M = ZZ/3` as `hopfShadowCokerGroupIsoIsNamedNode`: the
setoid/canonical-representative route with normal form `nf(v1, v2) = (v1 - v2) mod 3`, whose KEYSTONE
`intResidue3_add` (mod-3 additivity over `Int`) rides the flagged `Int.add_comm` propext minefield.

This r8 file discharges the bulk of that residual, ADDITIVELY (r7 is untouched).  The normal form is the
mod-3 reduction of the certified second coordinate: from the r7 row-word the unimodular `U = [[-1,0],[1,-1]]`
sends `im(M)` onto `ZZ x 3ZZ`, and `(U v).2 = v1 - v2`, so `nf(v) = intResidue3 (v.1 - v.2)`.  Delivered:

  * `cokerNormalForm` / `cokerRep` — the projection to `ZmodThree` and a canonical representative on the
    first coordinate `(k, 0)` (BRICK A);
  * ★ `cokerSectionRoundTrip` — the SECTION `nf (rep r) = r` (a full bijection needs both round-trips;
    this half ships) and `cokerRepsAreDistinct*` — the three residue classes are pairwise distinct
    (`ZmodThree.noConfusion`, never `decide` — no `DecidableEq ZmodThree` is shipped);
  * ★★ `intResidue3Add` — THE KEYSTONE the r7 node called `intResidue3_add`: mod-3 additivity over `Int`,
    routed entirely through the propext-clean Int kit + `subNatNat` bridges (BRICK C);
  * ★★ `cokerNormalFormRespects` — the WELL-DEFINEDNESS lemma: `nf` is constant on `cokerRel` classes,
    so `nf` descends to a genuine function on the quotient `ZZ^2 / im(M)` (BRICK D);
  * ★★ `cokerAdditionLaw` — the GROUP HOMOMORPHISM law `nf (v .+. w) = nf v + nf w` in `ZmodThree`, a
    direct corollary of the keystone (r7 slated this for a later round; it lands here).

So `nf : ZZ^2 / im(M) -> ZZ/3` is a well-defined SURJECTIVE group homomorphism with a section and three
distinct classes — the coker iso delivered at the set-plus-group-hom level.

## What this file does NOT deliver — the correctly-smaller residual, named IN THIS FILE

It does NOT ship the REFLECTS (injectivity) direction `nf v = nf w -> cokerRel v w`, hence not the
retraction round-trip `cokerRel v (rep (nf v))` nor the assembled two-sided iso record.  That converse is
the residual named here as `hopfShadowCokerGroupIsoReflectsIsNamedNode`: it needs the explicit witness
extraction (`nf v = nf w` gives `phi(v - w) = 3 k`; then `b := k`, `a := k - (v.1 - w.1)` reconstructs the
`im(M)` membership) — a case analysis on `ZmodThree` plus a `subNatNat`-magnitude argument, its own arc.

## Zero-axiom / LANE-LAW design decisions

  * SETOID route: `nf` is an explicit `Int -> ZmodThree` reduction (`intResidue3`) with round-trips, NEVER
    `Quot` / `Quot.sound`.  `intResidue3` avoids `Int.emod` (propext-dirty) — it is structural
    (`natResidue3` period-3 on `n + 3`, sign-split on the `Int` constructor).
  * All `Int` arithmetic rides the propext-CLEAN kit (`FX1Poly.ComputerAlgebra`): `intAddComm` /
    `intAddAssoc` / `intSubEqAddNeg` / `intNegAdd` / `intNegSub` / `intNegNeg` / `intAddRightNeg` /
    `intAddLeftNeg` / `intRightDistrib` / `intOneMul` and the `subNatNat` bridges
    (`intSubNatNatSuccSucc` / `intSubNatNatZeroRight` / `intSubNatNatZeroLeftSucc`), NEVER Init's
    propext-dirty `Int.add_comm` / `add_assoc` / `neg_add` / `add_mul`.  The 4-term swap `intAddSwapMiddle`
    lives off-closure (`IntToNatCycle`), so it is hand-rolled locally (`intAddSwapMiddleLocal`) from
    `intAddComm` + `intAddAssoc` — no new import edge.
  * The keystone cross-sign arms mirror the shipped `intOfNatAddSubNatNat` double-recursion precedent
    (`ComputerAlgebra/Number/IntAddAssociativity`): base `intSubNatNatZeroRight` / `intSubNatNatZeroLeftSucc`,
    step `intSubNatNatSuccSucc`.  The `negSucc/negSucc` arm rides `negZmod3AddDistrib` (9-arm `rfl`) with a
    single clean `Nat.succ_add` bridge.
  * Every `match` on `ZmodThree` is FULLY enumerated (9-arm Cayley for `addZmod3Comm` / `negZmod3AddDistrib`,
    3-arm for `natResidue3Succ` bases) — no `_ =>` wildcard, no match-compiler propext leak.  Distinctness
    is `ZmodThree.noConfusion`, never `decide` (no `DecidableEq ZmodThree`).

The iso is SETOID-based (explicit `nf` + round-trips), never `Quot`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Structural recursion only (fuel/`Nat`).
Per-declaration gated (and independently `#print axioms`-cross-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/HopfShadowCokerGroupIsoCertificate.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## BRICK A — the normal form, the canonical representative, the section, and class distinctness -/

/-- The mod-3 residue of a `Nat`, structural (period 3 on `n + 3`) — never `Nat.mod`. -/
def natResidue3 : Nat → ZmodThree
  | 0 => .residue0
  | 1 => .residue1
  | 2 => .residue2
  | value + 3 => natResidue3 value

/-- The mod-3 residue of an `Int`, sign-split on the constructor: `negSucc n = -(n+1)` reduces to the
negation of the positive residue.  Avoids `Int.emod` (propext-dirty). -/
def intResidue3 : Int → ZmodThree
  | .ofNat valueNat => natResidue3 valueNat
  | .negSucc valuePredecessor => negZmod3 (natResidue3 (valuePredecessor + 1))

/-- ★ **The coker normal form** `nf(v1, v2) = (v1 - v2) mod 3`.  From the r7 row-word the unimodular
`U = [[-1,0],[1,-1]]` sends `im(M)` onto `ZZ x 3ZZ` and `(U v).2 = v1 - v2`, so the second-coordinate
mod-3 residue is the canonical projection `ZZ^2 -> ZZ/3` with kernel `im(M)`. -/
def cokerNormalForm (pair : Int × Int) : ZmodThree := intResidue3 (pair.1 - pair.2)

/-- The canonical representative of a residue: place it on the first coordinate so `nf (rep r) = r`. -/
def cokerRep : ZmodThree → Int × Int
  | .residue0 => (0, 0)
  | .residue1 => (1, 0)
  | .residue2 => (2, 0)

/-- Probe — the three representatives image to their residues (`rfl`). -/
theorem cokerNormalFormRepZeroProbe : cokerNormalForm (0, 0) = ZmodThree.residue0 := rfl
/-- Probe — `nf (1, 0) = residue1` (`rfl`). -/
theorem cokerNormalFormRepOneProbe : cokerNormalForm (1, 0) = ZmodThree.residue1 := rfl
/-- Probe — `nf (2, 0) = residue2` (`rfl`). -/
theorem cokerNormalFormRepTwoProbe : cokerNormalForm (2, 0) = ZmodThree.residue2 := rfl
/-- Probe — the first `im(M)` generator (column `(-1, -1)`) images to `0` (`rfl`). -/
theorem cokerNormalFormGeneratorOneProbe : cokerNormalForm (-1, -1) = ZmodThree.residue0 := rfl
/-- Probe — the second `im(M)` generator (column `(1, -2)`) images to `0` (`rfl`). -/
theorem cokerNormalFormGeneratorTwoProbe : cokerNormalForm (1, -2) = ZmodThree.residue0 := rfl
/-- Probe — a LARGE lattice vector `(1, -8)` (difference `9 = 3 * 3`) images to `0` (`rfl`). -/
theorem cokerNormalFormLargeProbe : cokerNormalForm (1, -8) = ZmodThree.residue0 := rfl
/-- Probe — a NEGATIVE representative `(-5, 0)` (difference `-5`, residue `1`) images to `residue1` (`rfl`). -/
theorem cokerNormalFormNegativeProbe : cokerNormalForm (-5, 0) = ZmodThree.residue1 := rfl
/-- Probe — a mixed large vector `(10, 3)` (difference `7`, residue `1`) images to `residue1` (`rfl`). -/
theorem cokerNormalFormMixedProbe : cokerNormalForm (10, 3) = ZmodThree.residue1 := rfl
/-- Probe — a doubly-negative vector `(-4, 0)` (difference `-4`, residue `2`) images to `residue2` (`rfl`). -/
theorem cokerNormalFormNegTwoProbe : cokerNormalForm (-4, 0) = ZmodThree.residue2 := rfl

/-- ★ **The SECTION round-trip** `nf (rep r) = r` — a full bijection needs both round-trips; this half
ships here.  Three-arm `rfl` over `ZmodThree`. -/
theorem cokerSectionRoundTrip : ∀ residue : ZmodThree, cokerNormalForm (cokerRep residue) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- ★ The three residue classes have DISTINCT normal forms: `residue0 != residue1`
(`ZmodThree.noConfusion`, never `decide` — no `DecidableEq ZmodThree`). -/
theorem cokerRepsAreDistinctZeroOne :
    cokerNormalForm (cokerRep ZmodThree.residue0) ≠ cokerNormalForm (cokerRep ZmodThree.residue1) :=
  fun classesEqual => ZmodThree.noConfusion classesEqual
/-- ★ `residue1 != residue2` normal forms. -/
theorem cokerRepsAreDistinctOneTwo :
    cokerNormalForm (cokerRep ZmodThree.residue1) ≠ cokerNormalForm (cokerRep ZmodThree.residue2) :=
  fun classesEqual => ZmodThree.noConfusion classesEqual
/-- ★ `residue0 != residue2` normal forms. -/
theorem cokerRepsAreDistinctZeroTwo :
    cokerNormalForm (cokerRep ZmodThree.residue0) ≠ cokerNormalForm (cokerRep ZmodThree.residue2) :=
  fun classesEqual => ZmodThree.noConfusion classesEqual

/-! ## BRICK B — the `ZmodThree` / `Nat`-residue scaffold for the keystone -/

/-- `addZmod3` commutes — the fully-enumerated 9-arm Cayley diagonal (no wildcard). -/
theorem addZmod3Comm : ∀ leftResidue rightResidue : ZmodThree,
    addZmod3 leftResidue rightResidue = addZmod3 rightResidue leftResidue
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- `negZmod3` distributes over `addZmod3` — the 9-arm Cayley `rfl`. -/
theorem negZmod3AddDistrib : ∀ leftResidue rightResidue : ZmodThree,
    negZmod3 (addZmod3 leftResidue rightResidue)
      = addZmod3 (negZmod3 leftResidue) (negZmod3 rightResidue)
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- The `Nat` residue advances by one `shiftUp` per successor — structural, base `0/1/2` `rfl`, step
`n + 3` folds the period. -/
theorem natResidue3Succ : ∀ value : Nat, natResidue3 (value + 1) = shiftUp (natResidue3 value)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | value + 3 => natResidue3Succ value

/-- ★ The `Nat` residue is additive: `residue (a + b) = residue a + residue b` in `ZmodThree`.  Induction
on the second summand, step riding `natResidue3Succ` + the RIGHT-operand shift distribution
`shiftUpAddZmod3Right`. -/
theorem natResidue3Add : ∀ leftValue rightValue : Nat,
    natResidue3 (leftValue + rightValue)
      = addZmod3 (natResidue3 leftValue) (natResidue3 rightValue)
  | leftValue, 0 => (addZmod3ZeroRight (natResidue3 leftValue)).symm
  | leftValue, rightValue + 1 =>
      (natResidue3Succ (leftValue + rightValue)).trans
        ((congrArg shiftUp (natResidue3Add leftValue rightValue)).trans
          ((shiftUpAddZmod3Right (natResidue3 leftValue) (natResidue3 rightValue)).trans
            (congrArg (addZmod3 (natResidue3 leftValue)) (natResidue3Succ rightValue).symm)))

/-- The shift balance: raising the left operand by one and lowering the right by one cancels.  Rides the
LEFT distribution `shiftUpAddZmod3`, the RIGHT distribution `shiftDownAddZmod3Right`, and the
`shiftUp (shiftDown _) = id` round-trip. -/
theorem addZmod3ShiftBalance (leftResidue rightResidue : ZmodThree) :
    addZmod3 (shiftUp leftResidue) (shiftDown rightResidue) = addZmod3 leftResidue rightResidue :=
  (shiftUpAddZmod3 leftResidue (shiftDown rightResidue)).symm.trans
    ((congrArg shiftUp (shiftDownAddZmod3Right leftResidue rightResidue).symm).trans
      (shiftUpShiftDown (addZmod3 leftResidue rightResidue)))

/-! ## BRICK C — the KEYSTONE `intResidue3Add` (the r7-named `intResidue3_add`) and the 3-multiple -/

/-- The `subNatNat` step bridge: raising both `Nat` arguments by one leaves the residue combination fixed.
`natResidue3Succ` on both operands, then `shiftDownNegIsNegShiftUp` + `addZmod3ShiftBalance`. -/
theorem natResidueSubStepBridge (leftValue rightValue : Nat) :
    addZmod3 (natResidue3 (leftValue + 1)) (negZmod3 (natResidue3 (rightValue + 1)))
      = addZmod3 (natResidue3 leftValue) (negZmod3 (natResidue3 rightValue)) :=
  (congrArg (fun residue => addZmod3 residue (negZmod3 (natResidue3 (rightValue + 1))))
      (natResidue3Succ leftValue)).trans
    ((congrArg (fun residue => addZmod3 (shiftUp (natResidue3 leftValue)) (negZmod3 residue))
        (natResidue3Succ rightValue)).trans
      ((congrArg (addZmod3 (shiftUp (natResidue3 leftValue)))
          (shiftDownNegIsNegShiftUp (natResidue3 rightValue)).symm).trans
        (addZmod3ShiftBalance (natResidue3 leftValue) (negZmod3 (natResidue3 rightValue)))))

/-- ★ **The `subNatNat` residue law** `residue (subNatNat p q) = residue p + (-(residue q))`.  Double
structural recursion mirroring `intOfNatAddSubNatNat` (`ComputerAlgebra/Number/IntAddAssociativity`): the
two bases are `intSubNatNatZeroRight` / `intSubNatNatZeroLeftSucc`, the step is `intSubNatNatSuccSucc`
threaded through `natResidueSubStepBridge`. -/
theorem intResidue3SubNatNat : ∀ leftValue rightValue : Nat,
    intResidue3 (Int.subNatNat leftValue rightValue)
      = addZmod3 (natResidue3 leftValue) (negZmod3 (natResidue3 rightValue))
  | leftValue, 0 =>
      (congrArg intResidue3 (intSubNatNatZeroRight leftValue)).trans
        (addZmod3ZeroRight (natResidue3 leftValue)).symm
  | 0, rightValue + 1 =>
      (congrArg intResidue3 (intSubNatNatZeroLeftSucc rightValue)).trans
        (addZmod3ZeroLeft (negZmod3 (natResidue3 (rightValue + 1)))).symm
  | leftValue + 1, rightValue + 1 =>
      (congrArg intResidue3 (intSubNatNatSuccSucc leftValue rightValue)).trans
        ((intResidue3SubNatNat leftValue rightValue).trans
          (natResidueSubStepBridge leftValue rightValue).symm)

/-- The `Nat` bridge for the `negSucc/negSucc` add arm: `(m+1)+(n+1) = (m+n)+2`, a single `Nat.succ_add`
under `Nat.succ` (clean; never `Nat.add_mul`). -/
theorem natAddTwoBridge (leftValue rightValue : Nat) :
    (leftValue + 1) + (rightValue + 1) = (leftValue + rightValue) + 2 :=
  congrArg Nat.succ (Nat.succ_add leftValue rightValue)

/-- ★★ **THE KEYSTONE** — mod-3 additivity over `Int`: `residue (a + b) = residue a + residue b`.  This is
the `intResidue3_add` the r7 node `hopfShadowCokerGroupIsoIsNamedNode` named as the propext wall; it is
discharged here through the clean kit.  Four-arm constructor bash on the `Int` summands: `ofNat/ofNat`
is `natResidue3Add`; the two cross-sign arms route through `intResidue3SubNatNat` (with `addZmod3Comm` on
one side); the `negSucc/negSucc` arm rides `negZmod3AddDistrib` with the `natAddTwoBridge` shift.  No
`Int.add_comm` opened. -/
theorem intResidue3Add : ∀ leftValue rightValue : Int,
    intResidue3 (leftValue + rightValue)
      = addZmod3 (intResidue3 leftValue) (intResidue3 rightValue)
  | .ofNat leftNat, .ofNat rightNat => natResidue3Add leftNat rightNat
  | .ofNat leftNat, .negSucc rightNat => intResidue3SubNatNat leftNat (rightNat + 1)
  | .negSucc leftNat, .ofNat rightNat =>
      (intResidue3SubNatNat rightNat (leftNat + 1)).trans
        (addZmod3Comm (natResidue3 rightNat) (negZmod3 (natResidue3 (leftNat + 1))))
  | .negSucc leftNat, .negSucc rightNat =>
      (congrArg (fun index => negZmod3 (natResidue3 index))
          (natAddTwoBridge leftNat rightNat).symm).trans
        ((congrArg negZmod3 (natResidue3Add (leftNat + 1) (rightNat + 1))).trans
          (negZmod3AddDistrib (natResidue3 (leftNat + 1)) (natResidue3 (rightNat + 1))))

/-- The `Nat` residue of any multiple of three is `0` — structural (`3 * (n+1) = 3 * n + 3` folds the
period). -/
theorem natResidue3ThreeMul : ∀ value : Nat, natResidue3 (3 * value) = ZmodThree.residue0
  | 0 => rfl
  | value + 1 => natResidue3ThreeMul value

/-- ★ The `Int` residue of any multiple of three is `0` — the two sign arms fold
`natResidue3ThreeMul` (the `negSucc` arm under `negZmod3`). -/
theorem intResidue3ThreeMultiple : ∀ value : Int, intResidue3 (3 * value) = ZmodThree.residue0
  | .ofNat valueNat => natResidue3ThreeMul valueNat
  | .negSucc valueNat => congrArg negZmod3 (natResidue3ThreeMul (valueNat + 1))

/-! ## BRICK D — the coker relation, the group-hom addition law, and well-definedness (respects)

The `Int` 4-term swap `intAddSwapMiddle` lives off the r7 closure (`IntToNatCycle`), so it is hand-rolled
locally from `intAddComm` + `intAddAssoc` — no new import edge, lane law honored. -/

/-- Local 4-term swap `(a + b) + (c + d) = (a + c) + (b + d)` from `intAddComm` + `intAddAssoc` (the kit
`intAddSwapMiddle` is off-closure). -/
theorem intAddSwapMiddleLocal (firstLeft firstRight secondLeft secondRight : Int) :
    (firstLeft + firstRight) + (secondLeft + secondRight)
      = (firstLeft + secondLeft) + (firstRight + secondRight) :=
  (intAddAssoc firstLeft firstRight (secondLeft + secondRight)).trans
    ((congrArg (firstLeft + ·) (intAddAssoc firstRight secondLeft secondRight).symm).trans
      ((congrArg (fun middle => firstLeft + (middle + secondRight)) (intAddComm firstRight secondLeft)).trans
        ((congrArg (firstLeft + ·) (intAddAssoc secondLeft firstRight secondRight)).trans
          (intAddAssoc firstLeft secondLeft (firstRight + secondRight)).symm)))

/-- `(a + c) - (b + d) = (a - b) + (c - d)` — expand the negation, swap the middle atoms, refold. -/
theorem intAddSubAddRearrange (firstA firstB secondC secondD : Int) :
    (firstA + secondC) - (firstB + secondD) = (firstA - firstB) + (secondC - secondD) :=
  (intSubEqAddNeg (firstA + secondC) (firstB + secondD)).trans
    ((congrArg ((firstA + secondC) + ·) (intNegAdd firstB secondD)).trans
      ((intAddSwapMiddleLocal firstA secondC (-firstB) (-secondD)).trans
        ((congrArg (fun leftPart => leftPart + (secondC + -secondD))
            (intSubEqAddNeg firstA firstB).symm).trans
          (congrArg (fun rightPart => (firstA - firstB) + rightPart)
            (intSubEqAddNeg secondC secondD).symm))))

/-- Componentwise coker addition on representatives `(v1 + w1, v2 + w2)`. -/
def cokerPairAdd (leftPair rightPair : Int × Int) : Int × Int :=
  (leftPair.1 + rightPair.1, leftPair.2 + rightPair.2)

/-- ★★ **THE GROUP HOMOMORPHISM LAW** `nf (v .+. w) = nf v + nf w` in `ZmodThree` — a direct corollary of
the keystone `intResidue3Add` after the `(a+c)-(b+d) = (a-b)+(c-d)` rearrangement.  (r7 slated this for a
later round; the keystone landing brings it into r8.) -/
theorem cokerAdditionLaw (leftPair rightPair : Int × Int) :
    cokerNormalForm (cokerPairAdd leftPair rightPair)
      = addZmod3 (cokerNormalForm leftPair) (cokerNormalForm rightPair) :=
  (congrArg intResidue3
      (intAddSubAddRearrange leftPair.1 leftPair.2 rightPair.1 rightPair.2)).trans
    (intResidue3Add (leftPair.1 - leftPair.2) (rightPair.1 - rightPair.2))

/-- `y + (x - y) = x` — the reconstruction cancellation used by `respects`. -/
theorem intAddSubCancelLeft (baseValue targetValue : Int) :
    baseValue + (targetValue - baseValue) = targetValue :=
  (congrArg (baseValue + ·) (intSubEqAddNeg targetValue baseValue)).trans
    ((congrArg (baseValue + ·) (intAddComm targetValue (-baseValue))).trans
      ((intAddAssoc baseValue (-baseValue) targetValue).symm.trans
        ((congrArg (· + targetValue) (intAddRightNeg baseValue)).trans
          (intZeroAdd targetValue))))

/-- `(p - q) - (r - s) = (p - r) - (q - s)` — the two atoms `-q` and `-r` swap groups (via
`intAddSwapMiddleLocal` twice and one `intAddComm`). -/
theorem intCrossSubRearrange (pValue qValue rValue sValue : Int) :
    (pValue - qValue) - (rValue - sValue) = (pValue - rValue) - (qValue - sValue) :=
  calc (pValue - qValue) - (rValue - sValue)
      = (pValue + -qValue) - (rValue - sValue) :=
        congrArg (· - (rValue - sValue)) (intSubEqAddNeg pValue qValue)
    _ = (pValue + -qValue) + -(rValue - sValue) := intSubEqAddNeg (pValue + -qValue) (rValue - sValue)
    _ = (pValue + -qValue) + (sValue - rValue) :=
        congrArg ((pValue + -qValue) + ·) (intNegSub rValue sValue)
    _ = (pValue + -qValue) + (sValue + -rValue) :=
        congrArg ((pValue + -qValue) + ·) (intSubEqAddNeg sValue rValue)
    _ = (pValue + sValue) + (-qValue + -rValue) :=
        intAddSwapMiddleLocal pValue (-qValue) sValue (-rValue)
    _ = (pValue + sValue) + (-rValue + -qValue) :=
        congrArg ((pValue + sValue) + ·) (intAddComm (-qValue) (-rValue))
    _ = (pValue + -rValue) + (sValue + -qValue) :=
        (intAddSwapMiddleLocal pValue (-rValue) sValue (-qValue)).symm
    _ = (pValue + -rValue) + (sValue - qValue) :=
        congrArg ((pValue + -rValue) + ·) (intSubEqAddNeg sValue qValue).symm
    _ = (pValue + -rValue) + -(qValue - sValue) :=
        congrArg ((pValue + -rValue) + ·) (intNegSub qValue sValue).symm
    _ = (pValue - rValue) + -(qValue - sValue) :=
        congrArg (· + -(qValue - sValue)) (intSubEqAddNeg pValue rValue).symm
    _ = (pValue - rValue) - (qValue - sValue) := (intSubEqAddNeg (pValue - rValue) (qValue - sValue)).symm

/-- `3 * value = value + 2 * value` from `intRightDistrib` (`3 = 1 + 2` definitionally) and `intOneMul`. -/
theorem threeTimesRightExpand (value : Int) : (3 : Int) * value = value + 2 * value :=
  (intRightDistrib 1 2 value).trans (congrArg (· + 2 * value) (intOneMul value))

/-- **The coker equivalence** `v ~ w` iff `v - w` lies in the column span of `M = [[-1,1],[-1,-2]]`:
`v - w = a * col0 + b * col1` with `col0 = (-1, -1)`, `col1 = (1, -2)`.  The setoid relation for the
quotient `ZZ^2 / im(M)` — NEVER `Quot`. -/
def cokerRel (leftPair rightPair : Int × Int) : Prop :=
  ∃ aWitness bWitness : Int,
    leftPair.1 - rightPair.1 = -aWitness + bWitness
      ∧ leftPair.2 - rightPair.2 = -aWitness - 2 * bWitness

/-- `(-a + b) - (-a - 2b) = 3b` — the flanking `-a` cancels, leaving `b + 2b = 3b`. -/
theorem cokerWitnessAlgebra (aWitness bWitness : Int) :
    (-aWitness + bWitness) - (-aWitness - 2 * bWitness) = 3 * bWitness :=
  calc (-aWitness + bWitness) - (-aWitness - 2 * bWitness)
      = (-aWitness + bWitness) + -(-aWitness - 2 * bWitness) :=
        intSubEqAddNeg (-aWitness + bWitness) (-aWitness - 2 * bWitness)
    _ = (-aWitness + bWitness) + -((-aWitness) + -(2 * bWitness)) :=
        congrArg (fun term => (-aWitness + bWitness) + -term) (intSubEqAddNeg (-aWitness) (2 * bWitness))
    _ = (-aWitness + bWitness) + (-(-aWitness) + -(-(2 * bWitness))) :=
        congrArg ((-aWitness + bWitness) + ·) (intNegAdd (-aWitness) (-(2 * bWitness)))
    _ = (-aWitness + bWitness) + (aWitness + -(-(2 * bWitness))) :=
        congrArg (fun term => (-aWitness + bWitness) + (term + -(-(2 * bWitness)))) (intNegNeg aWitness)
    _ = (-aWitness + bWitness) + (aWitness + 2 * bWitness) :=
        congrArg (fun term => (-aWitness + bWitness) + (aWitness + term)) (intNegNeg (2 * bWitness))
    _ = (-aWitness + aWitness) + (bWitness + 2 * bWitness) :=
        intAddSwapMiddleLocal (-aWitness) bWitness aWitness (2 * bWitness)
    _ = 0 + (bWitness + 2 * bWitness) :=
        congrArg (· + (bWitness + 2 * bWitness)) (intAddLeftNeg aWitness)
    _ = bWitness + 2 * bWitness := intZeroAdd (bWitness + 2 * bWitness)
    _ = 3 * bWitness := (threeTimesRightExpand bWitness).symm

/-- ★★ **WELL-DEFINEDNESS (respects)** — `nf` is constant on `cokerRel` classes, so `nf` descends to a
genuine function on the quotient `ZZ^2 / im(M)`.  From the witnesses, `phi(v) - phi(w) = 3 b`
(`intCrossSubRearrange` + `cokerWitnessAlgebra`); then `phi(v) = phi(w) + 3 b`, so
`intResidue3 (phi v) = intResidue3 (phi w) + intResidue3 (3 b)` (keystone) `= intResidue3 (phi w) + 0`
(`intResidue3ThreeMultiple`) `= intResidue3 (phi w)`. -/
theorem cokerNormalFormRespects (leftPair rightPair : Int × Int)
    (related : cokerRel leftPair rightPair) :
    cokerNormalForm leftPair = cokerNormalForm rightPair :=
  match related with
  | ⟨aWitness, bWitness, hFirst, hSecond⟩ =>
      let deltaEq :
          (leftPair.1 - leftPair.2) - (rightPair.1 - rightPair.2) = 3 * bWitness :=
        (intCrossSubRearrange leftPair.1 leftPair.2 rightPair.1 rightPair.2).trans
          ((congrArg (· - (leftPair.2 - rightPair.2)) hFirst).trans
            ((congrArg ((-aWitness + bWitness) - ·) hSecond).trans
              (cokerWitnessAlgebra aWitness bWitness)))
      (congrArg intResidue3
          ((intAddSubCancelLeft (rightPair.1 - rightPair.2) (leftPair.1 - leftPair.2)).symm.trans
            (congrArg ((rightPair.1 - rightPair.2) + ·) deltaEq))).trans
        ((intResidue3Add (rightPair.1 - rightPair.2) (3 * bWitness)).trans
          ((congrArg (addZmod3 (intResidue3 (rightPair.1 - rightPair.2)))
              (intResidue3ThreeMultiple bWitness)).trans
            (addZmod3ZeroRight (intResidue3 (rightPair.1 - rightPair.2)))))

/-! ## The r8 ledger markers (honest scope) — NODE 1 (set + group-hom) shipped; REFLECTS stays named -/

/-- ★ **The REFLECTS (injectivity) direction is a NAMED node.**  This r8 file ships `nf` as a
well-defined SURJECTIVE group homomorphism `ZZ^2 / im(M) -> ZZ/3` with a section (`cokerSectionRoundTrip`),
three distinct classes (`cokerRepsAreDistinct*`), and the group-hom law (`cokerAdditionLaw`), all resting
on the KEYSTONE `intResidue3Add`.  It does NOT ship the converse `nf v = nf w -> cokerRel v w`
(injectivity), hence not the retraction round-trip `cokerRel v (rep (nf v))` nor the two-sided iso record.
That residual — the explicit `im(M)`-membership witness extraction (`nf v = nf w` gives `phi(v - w) = 3 k`;
then `b := k`, `a := k - (v.1 - w.1)`), a `ZmodThree` case analysis plus a `subNatNat`-magnitude argument —
is the correctly-smaller residual `cokerNormalFormReflects` for a later round.  Read the meaning from THIS
docstring (the honest-record convention).  `= true`. -/
def hopfShadowCokerGroupIsoReflectsIsNamedNode : Bool := true

/-- ★ **The TOWER-ANICK (#2144) r8 Hopf-shadow coker GROUP-ISO node-one marker.**  Shipped zero-axiom,
additively over the frozen r7 certificate (`hopfShadowCokerGroupIsoIsNamedNode` stays; this NEW file is the
honest upgrade at the set-plus-group-hom level):

  * `cokerNormalForm` = `(v1 - v2) mod 3` + `cokerRep` + nine `rfl` truth-probes on concrete cosets
    (reps, both `im(M)` generators, large, negative, mixed);
  * ★ `cokerSectionRoundTrip` (section `nf (rep r) = r`) + `cokerRepsAreDistinct*` (three distinct classes,
    `noConfusion`);
  * ★★ `intResidue3Add` — THE KEYSTONE (the r7-named `intResidue3_add`), mod-3 additivity over `Int`
    through the propext-clean kit + `subNatNat` bridges, `Int.add_comm` never opened;
  * ★★ `cokerNormalFormRespects` — WELL-DEFINEDNESS on the quotient `ZZ^2 / im(M)`;
  * ★★ `cokerAdditionLaw` — the GROUP HOMOMORPHISM law `nf (v .+. w) = nf v + nf w`.

The literal coker carrier map is thereby delivered as a well-defined surjective group homomorphism onto
`ZZ/3`, discharging the bulk of the r7 residual `hopfShadowCokerGroupIsoIsNamedNode`.  The REFLECTS
(injectivity) converse — and with it the retraction and the two-sided iso record — stays the newly-named
smaller residual `hopfShadowCokerGroupIsoReflectsIsNamedNode`.  No overclaim.  Read the meaning from THIS
docstring (the honest-record convention). -/
def hopfShadowCokerGroupIsoNodeOneIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
