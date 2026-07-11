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

/-! ## B2 — the residue "image of `w` in `G`" and the invariant map `E → ZZ[ZZ/3]` -/

/-- One `t`-shift up in `ZZ/3` (the residue of appending the single generator `s`). -/
def shiftUp : ZmodThree → ZmodThree
  | .residue0 => .residue1
  | .residue1 => .residue2
  | .residue2 => .residue0

/-- One `t`-shift down in `ZZ/3` (the residue of appending `s⁻¹`). -/
def shiftDown : ZmodThree → ZmodThree
  | .residue0 => .residue2
  | .residue1 => .residue0
  | .residue2 => .residue1

/-- The residue shift of a single signed letter — the generator index is IGNORED (there is one
generator), so `pos` shifts up and `neg` shifts down.  Full enum on the sign. -/
def letterShift : SignedLetter → ZmodThree → ZmodThree
  | .pos _, residue => shiftUp residue
  | .neg _, residue => shiftDown residue

/-- **The image of a free-group word in `G = ZZ/3`** — the exponent-sum residue, a right fold of the
per-letter shifts starting from `residue0`. -/
def wordResidue : List SignedLetter → ZmodThree
  | [] => .residue0
  | letter :: rest => letterShift letter (wordResidue rest)

/-- **The invariant image of one conjugated relator** `±(w, r)` in the group ring: the sign-scaled
`t^(image of w in G)` basis element.  (The single relator collapses `R = 1`, so there is one `ZZ³`.) -/
def conjugatedRelatorImage (gen : ConjugatedRelator) : GroupRingZmod3 :=
  signScale gen.isPositive (powerOfT (wordResidue gen.conjugator))

/-- ★ **The separating invariant `E → ZZ[ZZ/3]`** — the additive extension of `conjugatedRelatorImage`
over the free word of the pre-crossed carrier, a right fold summing the per-generator images. -/
def crossedModuleImage : PreCrossedElement → GroupRingZmod3
  | [] => groupRingZero
  | gen :: rest => groupRingAdd (conjugatedRelatorImage gen) (crossedModuleImage rest)

/-- ★ **The invariant is an append-homomorphism** — `image (x ++ y) = image x + image y`, by induction
on `x` folding left-identity (base) and associativity (step).  This is the `congrAppend`-compatibility
that lets the invariant respect the Peiffer congruence. -/
theorem crossedModuleImageAppend : ∀ (leftPart rightPart : PreCrossedElement),
    crossedModuleImage (leftPart ++ rightPart)
      = groupRingAdd (crossedModuleImage leftPart) (crossedModuleImage rightPart)
  | [], rightPart => (groupRingZeroAdd (crossedModuleImage rightPart)).symm
  | gen :: rest, rightPart =>
      (congrArg (groupRingAdd (conjugatedRelatorImage gen))
          (crossedModuleImageAppend rest rightPart)).trans
        (groupRingAddAssoc (conjugatedRelatorImage gen)
          (crossedModuleImage rest) (crossedModuleImage rightPart)).symm

/-! ### B2 truth probes — the invariant on the r1 witnesses -/

/-- ★★ **The separating value: `image ζ = (−1, 1, 0)`** — the group-ring image of the rotation identity
`ζ = (s, ρ)·(1, ρ)⁻¹`.  `t¹ − t⁰ = (s̄ − 1)·e_ρ`, exactly the Lyndon rotation class.  `rfl`. -/
theorem rotationIdentityImageIsSeparating :
    crossedModuleImage rotationIdentityWitness = GroupRingZmod3.mk (-1) 1 0 := rfl

/-- Probe — the empty pre-crossed word images to `0`. -/
theorem emptyImageIsZero :
    crossedModuleImage ([] : PreCrossedElement) = groupRingZero := rfl

/-- Probe — the r1 concrete Peiffer probe images coherently: both `[a, b, a⁻¹]` and `[^{∂a}b]` land on
the SAME value `(0, 1, 0)`, confirming the invariant respects the Peiffer move on this instance. -/
theorem peifferProbeImageCoherent :
    crossedModuleImage [peifferProbeFirst, peifferProbeSecond, invGen peifferProbeFirst]
      = crossedModuleImage [peifferConjugate peifferProbeFirst peifferProbeSecond] := rfl

/-- Probe — that shared Peiffer-probe value is `(0, 1, 0)`, DISTINCT from `ζ`'s `(−1, 1, 0)`: the
invariant genuinely separates. -/
theorem peifferProbeImageValue :
    crossedModuleImage [peifferProbeFirst, peifferProbeSecond, invGen peifferProbeFirst]
      = GroupRingZmod3.mk 0 1 0 := rfl

/-! ## B3 — the residue group `ZZ/3`: Cayley table and the shift-distribution laws

The soundness keystone needs the residue "image of `w` in `G`" to be a group homomorphism from the
free group: it must send `reduceWord` to itself, `++` to `addZmod3`, and `invWord` to `negZmod3`.
Every fact below is a full-enum `match … => rfl` on `ZmodThree` (the residue is a 3-element group,
never an `Int`-remainder). -/

/-- The group operation of `ZZ/3` — the fully-enumerated Cayley table (nine arms, no wildcard). -/
def addZmod3 : ZmodThree → ZmodThree → ZmodThree
  | .residue0, .residue0 => .residue0
  | .residue0, .residue1 => .residue1
  | .residue0, .residue2 => .residue2
  | .residue1, .residue0 => .residue1
  | .residue1, .residue1 => .residue2
  | .residue1, .residue2 => .residue0
  | .residue2, .residue0 => .residue2
  | .residue2, .residue1 => .residue0
  | .residue2, .residue2 => .residue1

/-- The group negation of `ZZ/3`. -/
def negZmod3 : ZmodThree → ZmodThree
  | .residue0 => .residue0
  | .residue1 => .residue2
  | .residue2 => .residue1

/-- Left identity of `addZmod3`. -/
theorem addZmod3ZeroLeft : ∀ residue : ZmodThree, addZmod3 ZmodThree.residue0 residue = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- Right identity of `addZmod3`. -/
theorem addZmod3ZeroRight : ∀ residue : ZmodThree, addZmod3 residue ZmodThree.residue0 = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- Right inverse of `addZmod3`: `r + (-r) = 0`. -/
theorem addZmod3RightNeg : ∀ residue : ZmodThree,
    addZmod3 residue (negZmod3 residue) = ZmodThree.residue0
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `shiftUp` undoes `shiftDown`. -/
theorem shiftUpShiftDown : ∀ residue : ZmodThree, shiftUp (shiftDown residue) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `shiftDown` undoes `shiftUp`. -/
theorem shiftDownShiftUp : ∀ residue : ZmodThree, shiftDown (shiftUp residue) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `shiftUp` distributes over `addZmod3` on the LEFT operand (`+1` is a translation). -/
theorem shiftUpAddZmod3 : ∀ (leftResidue rightResidue : ZmodThree),
    shiftUp (addZmod3 leftResidue rightResidue) = addZmod3 (shiftUp leftResidue) rightResidue
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- `shiftDown` distributes over `addZmod3` on the LEFT operand. -/
theorem shiftDownAddZmod3 : ∀ (leftResidue rightResidue : ZmodThree),
    shiftDown (addZmod3 leftResidue rightResidue) = addZmod3 (shiftDown leftResidue) rightResidue
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- `letterShift` distributes over `addZmod3` on the LEFT operand. -/
theorem letterShiftAddZmod3 : ∀ (letter : SignedLetter) (leftResidue rightResidue : ZmodThree),
    letterShift letter (addZmod3 leftResidue rightResidue)
      = addZmod3 (letterShift letter leftResidue) rightResidue
  | .pos _, leftResidue, rightResidue => shiftUpAddZmod3 leftResidue rightResidue
  | .neg _, leftResidue, rightResidue => shiftDownAddZmod3 leftResidue rightResidue

/-- `shiftUp` distributes over `addZmod3` on the RIGHT operand. -/
theorem shiftUpAddZmod3Right : ∀ (leftResidue rightResidue : ZmodThree),
    shiftUp (addZmod3 leftResidue rightResidue) = addZmod3 leftResidue (shiftUp rightResidue)
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- `shiftDown` distributes over `addZmod3` on the RIGHT operand. -/
theorem shiftDownAddZmod3Right : ∀ (leftResidue rightResidue : ZmodThree),
    shiftDown (addZmod3 leftResidue rightResidue) = addZmod3 leftResidue (shiftDown rightResidue)
  | .residue0, .residue0 => rfl
  | .residue0, .residue1 => rfl
  | .residue0, .residue2 => rfl
  | .residue1, .residue0 => rfl
  | .residue1, .residue1 => rfl
  | .residue1, .residue2 => rfl
  | .residue2, .residue0 => rfl
  | .residue2, .residue1 => rfl
  | .residue2, .residue2 => rfl

/-- `letterShift` distributes over `addZmod3` on the RIGHT operand. -/
theorem letterShiftAddZmod3Right : ∀ (letter : SignedLetter) (leftResidue rightResidue : ZmodThree),
    letterShift letter (addZmod3 leftResidue rightResidue)
      = addZmod3 leftResidue (letterShift letter rightResidue)
  | .pos _, leftResidue, rightResidue => shiftUpAddZmod3Right leftResidue rightResidue
  | .neg _, leftResidue, rightResidue => shiftDownAddZmod3Right leftResidue rightResidue

/-- `shiftDown` on a negated residue equals negation of `shiftUp`. -/
theorem shiftDownNegIsNegShiftUp : ∀ residue : ZmodThree,
    shiftDown (negZmod3 residue) = negZmod3 (shiftUp residue)
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `shiftUp` on a negated residue equals negation of `shiftDown`. -/
theorem shiftUpNegIsNegShiftDown : ∀ residue : ZmodThree,
    shiftUp (negZmod3 residue) = negZmod3 (shiftDown residue)
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- Shifting by the inverse letter on a negated residue equals negation of the forward shift. -/
theorem letterShiftInverseNeg : ∀ (letter : SignedLetter) (residue : ZmodThree),
    letterShift (inverseLetter letter) (negZmod3 residue) = negZmod3 (letterShift letter residue)
  | .pos _, residue => shiftDownNegIsNegShiftUp residue
  | .neg _, residue => shiftUpNegIsNegShiftDown residue

/-! ### B3 — the residue is a `++`/`reduceWord`/`invWord` homomorphism -/

/-- Fold a word's per-letter shifts onto a starting residue (the residue action of a word). -/
def applyWordShift : List SignedLetter → ZmodThree → ZmodThree
  | [], residue => residue
  | letter :: rest, residue => letterShift letter (applyWordShift rest residue)

/-- `wordResidue` of a concatenation folds the left word's shifts onto the right word's residue. -/
theorem wordResidueAppend : ∀ (leftPart rightPart : List SignedLetter),
    wordResidue (leftPart ++ rightPart) = applyWordShift leftPart (wordResidue rightPart)
  | [], _ => rfl
  | letter :: rest, rightPart =>
      congrArg (letterShift letter) (wordResidueAppend rest rightPart)

/-- The word action is `addZmod3` by the word's residue (`+1`/`-1` shifts distribute). -/
theorem applyWordShiftIsAdd : ∀ (word : List SignedLetter) (residue : ZmodThree),
    applyWordShift word residue = addZmod3 (wordResidue word) residue
  | [], residue => (addZmod3ZeroLeft residue).symm
  | letter :: rest, residue =>
      (congrArg (letterShift letter) (applyWordShiftIsAdd rest residue)).trans
        (letterShiftAddZmod3 letter (wordResidue rest) residue)

/-- ★ **`wordResidue` is a `++`-homomorphism**: `residue (x ++ y) = residue x + residue y`. -/
theorem wordResidueAppendAdd (leftPart rightPart : List SignedLetter) :
    wordResidue (leftPart ++ rightPart)
      = addZmod3 (wordResidue leftPart) (wordResidue rightPart) :=
  (wordResidueAppend leftPart rightPart).trans (applyWordShiftIsAdd leftPart (wordResidue rightPart))

/-- Two inverse letters shift to the identity — the residue is blind to a cancelling pair. -/
theorem letterShiftInverseCancel : ∀ (letter top : SignedLetter) (residue : ZmodThree),
    areInverse letter top = true → letterShift letter (letterShift top residue) = residue
  | .pos _, .neg _, residue, _ => shiftUpShiftDown residue
  | .neg _, .pos _, residue, _ => shiftDownShiftUp residue
  | .pos _, .pos _, _, cancels => Bool.noConfusion cancels
  | .neg _, .neg _, _, cancels => Bool.noConfusion cancels

/-- ★ **`consReduced` preserves residue**: prepending through the free-cancellation guard leaves the
residue equal to the plain letter-shift, keyed by the `areInverse` guard (cancel drops both, extend
keeps).  Mirrors r1's `isReducedConsReduced`. -/
theorem consReducedResidue : ∀ (letter : SignedLetter) (word : List SignedLetter),
    wordResidue (consReduced letter word) = letterShift letter (wordResidue word)
  | _, [] => rfl
  | letter, top :: rest =>
      match hCancel : areInverse letter top with
      | true =>
          (congrArg wordResidue (consReducedCancel letter top rest hCancel)).trans
            (letterShiftInverseCancel letter top (wordResidue rest) hCancel).symm
      | false =>
          congrArg wordResidue (consReducedExtend letter top rest hCancel)

/-- ★★ **`reduceWord` preserves residue** — the highest-content lemma: free reduction never changes
the image of `w` in `G` (it only deletes `g g⁻¹` pairs).  Structural induction folding
`consReducedResidue`. -/
theorem reduceResiduePreserved : ∀ word : List SignedLetter,
    wordResidue (reduceWord word) = wordResidue word
  | [] => rfl
  | letter :: rest =>
      (consReducedResidue letter (reduceWord rest)).trans
        (congrArg (letterShift letter) (reduceResiduePreserved rest))

/-- `List.map inverseLetter` negates the residue (each letter flips sign). -/
theorem wordResidueMapInverse : ∀ word : List SignedLetter,
    wordResidue (List.map inverseLetter word) = negZmod3 (wordResidue word)
  | [] => rfl
  | letter :: rest =>
      (congrArg (letterShift (inverseLetter letter)) (wordResidueMapInverse rest)).trans
        (letterShiftInverseNeg letter (wordResidue rest))

/-- Reversal preserves residue (`ZZ/3` is abelian) — the accumulator-general form. -/
theorem wordResidueReverseAux : ∀ (word accumulator : List SignedLetter),
    wordResidue (List.reverseAux word accumulator)
      = addZmod3 (wordResidue word) (wordResidue accumulator)
  | [], accumulator => (addZmod3ZeroLeft (wordResidue accumulator)).symm
  | frontLetter :: remainingWord, accumulator =>
      (wordResidueReverseAux remainingWord (frontLetter :: accumulator)).trans
        (((letterShiftAddZmod3Right frontLetter (wordResidue remainingWord)
              (wordResidue accumulator)).symm).trans
          (letterShiftAddZmod3 frontLetter (wordResidue remainingWord) (wordResidue accumulator)))

/-- Reversal preserves residue. -/
theorem wordResidueReverse (word : List SignedLetter) :
    wordResidue (List.reverse word) = wordResidue word :=
  (wordResidueReverseAux word []).trans (addZmod3ZeroRight (wordResidue word))

/-- ★ **`invWord` negates residue**: `residue (w⁻¹) = -(residue w)` — reverse then flip each sign. -/
theorem wordResidueInvWord (word : List SignedLetter) :
    wordResidue (invWord word) = negZmod3 (wordResidue word) :=
  (wordResidueReverse (List.map inverseLetter word)).trans (wordResidueMapInverse word)

/-- The relator `ρ = s³` has residue `0` in `G = ZZ/3` (three up-shifts return to the start); every
other relator index is the empty word, residue `0`. -/
theorem relatorResidueIsZero : ∀ relatorIndex : Nat,
    wordResidue (relatorWord relatorIndex) = ZmodThree.residue0
  | 0 => rfl
  | _ + 1 => rfl

/-- The inverse relator also has residue `0`. -/
theorem invRelatorResidueIsZero (relatorIndex : Nat) :
    wordResidue (invWord (relatorWord relatorIndex)) = ZmodThree.residue0 :=
  (wordResidueInvWord (relatorWord relatorIndex)).trans
    (congrArg negZmod3 (relatorResidueIsZero relatorIndex))

/-- ★ **A conjugated relator-body has residue `0`**: `residue (w · r · w⁻¹) = residue r = 0` — the
`w` and `w⁻¹` residues cancel additively, independent of `w`. -/
theorem conjugationResidueZero (conjugatorWord relatorBody : List SignedLetter)
    (relatorZero : wordResidue relatorBody = ZmodThree.residue0) :
    wordResidue (reduceWord (conjugatorWord ++ relatorBody ++ invWord conjugatorWord))
      = ZmodThree.residue0 :=
  calc wordResidue (reduceWord (conjugatorWord ++ relatorBody ++ invWord conjugatorWord))
      = wordResidue (conjugatorWord ++ relatorBody ++ invWord conjugatorWord) :=
        reduceResiduePreserved _
    _ = addZmod3 (wordResidue (conjugatorWord ++ relatorBody))
          (wordResidue (invWord conjugatorWord)) := wordResidueAppendAdd _ _
    _ = addZmod3 (addZmod3 (wordResidue conjugatorWord) (wordResidue relatorBody))
          (wordResidue (invWord conjugatorWord)) :=
        congrArg (fun leftRes => addZmod3 leftRes (wordResidue (invWord conjugatorWord)))
          (wordResidueAppendAdd conjugatorWord relatorBody)
    _ = addZmod3 (addZmod3 (wordResidue conjugatorWord) ZmodThree.residue0)
          (wordResidue (invWord conjugatorWord)) :=
        congrArg (fun midRes => addZmod3 (addZmod3 (wordResidue conjugatorWord) midRes)
          (wordResidue (invWord conjugatorWord))) relatorZero
    _ = addZmod3 (addZmod3 (wordResidue conjugatorWord) ZmodThree.residue0)
          (negZmod3 (wordResidue conjugatorWord)) :=
        congrArg (fun invRes => addZmod3 (addZmod3 (wordResidue conjugatorWord) ZmodThree.residue0)
          invRes) (wordResidueInvWord conjugatorWord)
    _ = addZmod3 (wordResidue conjugatorWord) (negZmod3 (wordResidue conjugatorWord)) :=
        congrArg (fun leftRes => addZmod3 leftRes (negZmod3 (wordResidue conjugatorWord)))
          (addZmod3ZeroRight (wordResidue conjugatorWord))
    _ = ZmodThree.residue0 := addZmod3RightNeg (wordResidue conjugatorWord)

/-- ★★ **The Peiffer crux: `residue (∂a) = 0`** — the boundary of any conjugated relator maps to the
identity of `G` (both signs), because `∂a = w · ρ^±1 · w⁻¹` and `residue ρ = 0`.  This is exactly the
B4-docstring "`r ↦ 1` in `G`" that makes the Peiffer move invisible in `ZZ[G]`. -/
theorem boundaryResidueIsZero : ∀ gen : ConjugatedRelator,
    wordResidue (conjugatedRelatorBoundary gen) = ZmodThree.residue0
  | ⟨conjugatorWord, relatorIndex, true⟩ =>
      conjugationResidueZero conjugatorWord (relatorWord relatorIndex)
        (relatorResidueIsZero relatorIndex)
  | ⟨conjugatorWord, relatorIndex, false⟩ =>
      conjugationResidueZero conjugatorWord (invWord (relatorWord relatorIndex))
        (invRelatorResidueIsZero relatorIndex)

end FX1Poly.Polygraph.Homology
