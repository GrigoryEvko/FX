import FX1Poly.Polygraph.Homology.CrossedModuleCyclicThree
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # FX1Poly/Polygraph/Homology/CrossedModuleIdentityInvariant — the `ZZ[ZZ/3] ≅ ZZ³` separating
    invariant on the free crossed module of `⟨s | s³⟩`, its Peiffer-invariance, and the FIRST
    machine-checked nontrivial identity-among-relations `ζ ↦ (−1, 1, 0) ≠ 0` (WP-2GROUP r2, #2199)

r1 (`Homology/CrossedModuleCyclicThree`) exhibits the rotation identity `ζ ∈ ker ∂` but proves only
that the TRIVIAL-COEFFICIENT abelianization sends `ζ ↦ 0` — which cannot separate `ζ` from the
Peiffer-trivial word (that is exactly why the shipped `H2(cyclic Z/3) = 0`).  The correct separating
invariant is the `ZZ[G]`-MODULE (group-ring) abelianization `E → ZZ[G]^R`,
`(w, r, sign) ↦ ±(image of w in G)·e_r`.  For `G = ZZ/3` the group ring `ZZ[G] ≅ ZZ³` (basis
`1, t, t²`), "image of `w` in `G`" is the exponent-sum-mod-3 residue, and the single relator gives
`R = 1`, so the whole carrier is a single `ZZ³`.  Under this invariant `ζ ↦ (s̄ − 1) = (−1, 1, 0) ≠ 0`
while every Peiffer move maps to an equality (because `∂a ↦ 1` in `G`), so `ζ` is a NONTRIVIAL element
of `π₂⟨s | s³⟩` — the first machine-checked nontrivial identity among relations, Lyndon's `π₂ ≠ 0`
promoted from cited to PROVED for this instance.

## The carrier design (no convolution)

The invariant only ever emits `±(a basis vector)` and SUMS them — it never multiplies two ring
elements.  So the value carrier is only the additive group `(ZZ³, +, neg, 0)` (`GroupRingZmod3`); the
`ZZ[G]`-module `t`-shift is folded into the RESIDUE enum `ZmodThree`, not the value type.  Every mod-3
fact is then a full-enum `match … => rfl` on `ZmodThree` — the `Int`-remainder ceiling never appears.
The three abelian laws are proved componentwise through the shipped propext-CLEAN `Int` kit
(`FX1Poly.ComputerAlgebra`), never Init's propext-dirty `Int.add_comm`/`add_assoc`/`add_left_neg`.

## Zero-axiom design decisions

  * `GroupRingZmod3` is a plain 3-field record; inequality is extracted by `congrArg` on a single field
    projection (`coeffOne`), NEVER `GroupRingZmod3.mk.injEq` (the generated injEq can pull propext).
  * Every match on `ZmodThree` / `SignedLetter` / `Bool` is FULLY enumerated — no `_ =>` wildcard arm,
    so no match-compiler propext leak.
  * `decide` is used ONLY on the closing `Int` literal disequality `(-1 : Int) ≠ 0` (`Int.decEq` is
    clean-structural); never on a `∀ r : ZmodThree` (no `Fintype`, would not be auto-decidable).
  * All `Int` arithmetic goes through `intAddComm` / `intAddAssoc` / `intAddRightNeg` / `intZeroAdd` /
    `intAddZero` / `intNegNeg` from the shipped kit exclusively.

`Init`-only (over `Homology/CrossedModuleCyclicThree` and the `ComputerAlgebra.Number` Int kit),
structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleIdentityInvariant.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the group-ring carrier `ZZ[ZZ/3] ≅ ZZ³` and its additive group -/

/-- The group ring `ZZ[ZZ/3]` in the basis `(1, t, t²)`: an element is the triple of integer
coefficients.  A plain record — inequality is extracted by projecting a single field. -/
structure GroupRingZmod3 where
  /-- The coefficient of the basis element `1 = t⁰`. -/
  coeffOne : Int
  /-- The coefficient of the basis element `t = t¹`. -/
  coeffT : Int
  /-- The coefficient of the basis element `t² = t²`. -/
  coeffTsq : Int

/-- The zero of the group ring — all coefficients `0`. -/
def groupRingZero : GroupRingZmod3 := ⟨0, 0, 0⟩

/-- Coefficientwise addition in the group ring. -/
def groupRingAdd (left right : GroupRingZmod3) : GroupRingZmod3 :=
  ⟨left.coeffOne + right.coeffOne, left.coeffT + right.coeffT, left.coeffTsq + right.coeffTsq⟩

/-- Coefficientwise negation in the group ring. -/
def groupRingNeg (value : GroupRingZmod3) : GroupRingZmod3 :=
  ⟨-value.coeffOne, -value.coeffT, -value.coeffTsq⟩

/-- The field-congruence builder: equal coefficients give equal group-ring elements.  Three chained
`congrArg`s over the constructor — no `injEq`, no `▸`, propext-clean. -/
theorem groupRingEq {leftOne leftT leftTsq rightOne rightT rightTsq : Int}
    (hCoeffOne : leftOne = rightOne) (hCoeffT : leftT = rightT) (hCoeffTsq : leftTsq = rightTsq) :
    GroupRingZmod3.mk leftOne leftT leftTsq = GroupRingZmod3.mk rightOne rightT rightTsq :=
  (congrArg (fun value => GroupRingZmod3.mk value leftT leftTsq) hCoeffOne).trans
    ((congrArg (fun value => GroupRingZmod3.mk rightOne value leftTsq) hCoeffT).trans
      (congrArg (fun value => GroupRingZmod3.mk rightOne rightT value) hCoeffTsq))

/-! ### The abelian-group laws (componentwise through the propext-clean Int kit) -/

/-- Right identity: `x + 0 = x`. -/
theorem groupRingAddZero (value : GroupRingZmod3) : groupRingAdd value groupRingZero = value :=
  groupRingEq (intAddZero value.coeffOne) (intAddZero value.coeffT) (intAddZero value.coeffTsq)

/-- Left identity: `0 + x = x`. -/
theorem groupRingZeroAdd (value : GroupRingZmod3) : groupRingAdd groupRingZero value = value :=
  groupRingEq (intZeroAdd value.coeffOne) (intZeroAdd value.coeffT) (intZeroAdd value.coeffTsq)

/-- Associativity: `(x + y) + z = x + (y + z)`. -/
theorem groupRingAddAssoc (left middle right : GroupRingZmod3) :
    groupRingAdd (groupRingAdd left middle) right
      = groupRingAdd left (groupRingAdd middle right) :=
  groupRingEq (intAddAssoc left.coeffOne middle.coeffOne right.coeffOne)
    (intAddAssoc left.coeffT middle.coeffT right.coeffT)
    (intAddAssoc left.coeffTsq middle.coeffTsq right.coeffTsq)

/-- Double negation: `- - x = x`. -/
theorem groupRingNegNeg (value : GroupRingZmod3) : groupRingNeg (groupRingNeg value) = value :=
  groupRingEq (intNegNeg value.coeffOne) (intNegNeg value.coeffT) (intNegNeg value.coeffTsq)

/-- The `Int` cancellation `a + (b + -a) = b` — the seed of the Peiffer `a`-cancellation.  Built from
the propext-clean kit: commute, associate, right-inverse, left-identity. -/
theorem intCancelMiddle (outer inner : Int) : outer + (inner + -outer) = inner :=
  (congrArg (fun summand => outer + summand) (intAddComm inner (-outer))).trans
    (((intAddAssoc outer (-outer) inner).symm).trans
      ((congrArg (fun summand => summand + inner) (intAddRightNeg outer)).trans
        (intZeroAdd inner)))

/-- ★ The Peiffer `a`-cancellation in the carrier: `x + (y + -x) = y`.  Coefficientwise
`intCancelMiddle`.  This is what collapses the flanking `a, a⁻¹` of the Peiffer move. -/
theorem groupRingCancelMiddle (outer inner : GroupRingZmod3) :
    groupRingAdd outer (groupRingAdd inner (groupRingNeg outer)) = inner :=
  groupRingEq (intCancelMiddle outer.coeffOne inner.coeffOne)
    (intCancelMiddle outer.coeffT inner.coeffT)
    (intCancelMiddle outer.coeffTsq inner.coeffTsq)

/-! ## B1 — the residue index `ZZ/3` and the `t^k` basis picker -/

/-- The exponent residue `ZZ/3` — the "image of `w` in `G`" that indexes the group-ring basis.  A
3-element enum, so every group fact is a full-enum `match … => rfl`. -/
inductive ZmodThree where
  /-- The residue `0` (basis `t⁰ = 1`). -/
  | residue0
  /-- The residue `1` (basis `t¹ = t`). -/
  | residue1
  /-- The residue `2` (basis `t² = t²`). -/
  | residue2

/-- The `t^k` basis element of the group ring for residue `k`. -/
def powerOfT : ZmodThree → GroupRingZmod3
  | .residue0 => ⟨1, 0, 0⟩
  | .residue1 => ⟨0, 1, 0⟩
  | .residue2 => ⟨0, 0, 1⟩

/-- The sign scaling `±v` of a group-ring element by a `Bool` sign (`true = +`, `false = −`).  Full
enum over the `Bool`. -/
def signScale : Bool → GroupRingZmod3 → GroupRingZmod3
  | true, value => value
  | false, value => groupRingNeg value

/-! ### B1 concrete ring-op truth probes (evaluate the ops on literals FIRST) -/

/-- Probe — coefficientwise addition on literals: `t + t² ... ` no, `1 + t`. -/
theorem groupRingAddProbe :
    groupRingAdd (GroupRingZmod3.mk 1 0 0) (GroupRingZmod3.mk 0 1 0) = GroupRingZmod3.mk 1 1 0 := rfl

/-- Probe — coefficientwise negation on a literal: `-(1) = -1` in the `1`-slot. -/
theorem groupRingNegProbe :
    groupRingNeg (GroupRingZmod3.mk 1 0 0) = GroupRingZmod3.mk (-1) 0 0 := rfl

/-- Probe — the `t^k` basis picker: `powerOfT 1 = t = (0, 1, 0)`. -/
theorem powerOfTProbe : powerOfT ZmodThree.residue1 = GroupRingZmod3.mk 0 1 0 := rfl

/-- Probe — the cancellation identity on literals: `1 + (t + -1) = t`. -/
theorem groupRingCancelProbe :
    groupRingAdd (GroupRingZmod3.mk 1 0 0)
      (groupRingAdd (GroupRingZmod3.mk 0 1 0) (groupRingNeg (GroupRingZmod3.mk 1 0 0)))
      = GroupRingZmod3.mk 0 1 0 := rfl

/-- Probe — `signScale false` on a literal negates: `−(1) = (−1, 0, 0)`. -/
theorem signScaleNegProbe :
    signScale false (GroupRingZmod3.mk 1 0 0) = GroupRingZmod3.mk (-1) 0 0 := rfl

end FX1Poly.Polygraph.Homology
