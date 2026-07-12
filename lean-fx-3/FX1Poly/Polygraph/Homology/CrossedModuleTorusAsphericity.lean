import FX1Poly.Polygraph.Homology.CrossedModuleCyclicPowerInvariant
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # FX1Poly/Polygraph/Homology/CrossedModuleTorusAsphericity — the `ZZ[ZZ^2]` relation-module invariant
    on the free crossed module of the torus presentation `⟨a, b | [a, b]⟩`, its Peiffer-invariance, and
    the machine-checked kernel-vanishing witnesses + Fox-Jacobian record (WP-2GROUP r9, #2199)

r7 (`Homology/CrossedModuleCyclicPower`) opened the two-generator direction: it introduced the commutator
relator `[a, b] = a b a^{-1} b^{-1}` (`commutatorRelator`) and exercised the multi-generator carrier
(`commutatorBoundaryIsReduced`, `commutatorSelfInverseVanishes`), but shipped NO torus boundary and NO
torus Peiffer relation, naming the two-generator asphericity `asphericityResidualR9` in its arc ledger.
r8 (`Homology/CrossedModuleCyclicPowerInvariant`) delivered the `ZZ[ZZ/n]` list-rotation invariant for the
CYCLIC presentation `⟨s | s^n⟩` and mechanized `π₂⟨s | s^n⟩ ≠ 0` at the element level (Lyndon's PROPER-power
side).  This module delivers the COMPLEMENTARY torus footing: the abelian relation-module invariant for
`⟨a, b | [a, b]⟩`, its Peiffer-invariance, and the machine-checked kernel-vanishing (the aspherical side).

## THE PRESENTED STATEMENT vs THE CLASSICAL THEOREM (the honest-record convention; the r8 precedent)

The CLASSICAL theorem is Lyndon's Identity Theorem: `[a, b]` is not a proper power in `F(a, b)`, so the
torus is a torsion-free one-relator group, its presentation 2-complex is aspherical (`= K(ZZ^2, 1) = T^2`),
and `π₂⟨a, b | [a, b]⟩ = 0`.  Equivalently, the relation module `ker(∂₂)` is `0` because the Fox Jacobian
`∂₂ = (∂[a,b]/∂a, ∂[a,b]/∂b) = (1 - b, a - 1)` is INJECTIVE over the group ring `ZZ[ZZ^2]` (Laurent
polynomials `ZZ[a^±, b^±]`, an integral DOMAIN: `y·(1 - b) = 0 ⟹ y = 0` since `1 - b ≠ 0`).

This module does NOT claim `π₂ = 0`.  The invariant method can only ever EXHIBIT nonzero `π₂` elements
(r8's `ζ`); the vanishing direction needs the relation-module INJECTIVITY — the same node r8 walled
(`relationModuleIsoStatus := inheritedHopfResidual`).  What is SHIPPED here is the honest scoped
sub-statement, three ways:

  * **The `ZZ[ZZ^2]`-coefficient invariant** `torusImageCoeffAt`, an additive functional on the free
    pre-crossed carrier `E`, valued in the coefficients of the abelianized relation module.
  * **Its Peiffer-invariance** `torusImageRespectsPeiffer` — the invariant is constant on the torus Peiffer
    classes, so it descends to the crossed module `C = E / PeifferEquivTorus` (the SOUNDNESS keystone; the
    mirror of r8's `crossedModuleImageRespectsPeifferAt`, but LIGHTER: the crux is
    `abWordTorus [a, b] = (0, 0)`, an `rfl`, with NO rotate-by-length cyclicity).
  * **Machine-checked kernel-vanishing** — every torus kernel identity of the rotation/nesting shapes
    (`torusKernelWitnessOne/Three/Four`) has invariant image `0`, the OPPOSITE of r8's separating `ζ`;
    with the ζ-mirror contrast `torusContrastWitnessTwo` (nonzero image `a - 1` but NOT in the kernel) and
    the Fox-Jacobian pair `(1 - b, a - 1)` recorded with its nonzero coefficients (the Koszul regular
    sequence).  This is the abelianized/Alexander vanishing — CONSISTENT with `π₂ = 0`, still short of it.

The universal `π₂⟨a, b | [a, b]⟩ = 0` (Lyndon) and the Koszul shift-injectivity `y·(1 - b) = 0 ⟹ y = 0`
stay walled (`relationModuleInjectivityStatus`, `koszulShiftInjectivityStatus`).  Read the meaning from
THIS docstring and the ledger (`crossedModuleTorusAsphericityLedger`), never from an overclaimed name.

## The carrier — a coefficient-query on the `ZZ^2`-abelianization (funext-free)

`ZZ[ZZ^2]` is infinite-dimensional, so r8's fixed-length `List Int` cyclic-rotation carrier has NO torus
analogue.  Instead the invariant is stated POINTWISE: `abWordTorus w : ZZ^2` is the abelianization of a
conjugator word `w` (the per-generator exponent sums `(expGen 0 w, expGen 1 w)` — the Fox augmentation),
and `torusImageCoeffAt target x` sums the signed contributions of the generators of `x` whose conjugator
abelianizes to the monomial `target`.  The keystone is `∀ target, coeff target x = coeff target y` — a
`∀`-of-coefficients statement, NEVER a function equality, so NO funext (funext leaks).  The whole invariant
uses no polynomial multiplication and no normalizer.

## Zero-axiom design decisions

  * `expGenTorus` reduce-invariance rides `consReducedCancel`/`consReducedExtend` + the cancelling-pair
    fact `expGenLetterInverseCancel`, whose generator-equality is extracted by the OWN structural
    `torusNatEqOfBeqTrue` (never Init `Nat.eq_of_beq_eq_true`, never `Nat.beq_self`, never `propext`).
  * `signInt` is REUSED from `Homology/CrossedModuleRelationModule` (transitively imported), never
    redefined (the umbrella duplicate-global trap).  All generic helpers are `torus`-prefixed
    (`torusMatchedInt`, `torusProdMkEq`, `torusIntAddCongr`, `torusIntCancelMiddle`) to avoid collision.
  * Every match on `SignedLetter`/`Bool`/`Int`-constructor/`Nat` is FULLY enumerated (no wildcard).  The
    two concrete abelianization facts `abWordTorus commutatorRelator = (0, 0)` and the witnesses close by
    `rfl` at LITERAL monomials.  Non-emptiness of the contrast boundary is a Bool `wordBeq … oneWord =
    false` (`rfl`), never a `≠` through `Nat.succ_ne_zero`.
  * All `Int` arithmetic goes through the shipped propext-clean kit (`intAddZero`, `intZeroAdd`,
    `intAddComm`, `intAddAssoc`, `intAddRightNeg`, `intNegNeg`, `intNegZero`, `intNegAdd`), never Init's
    propext-dirty forms.  `ZZ^2 = Int × Int` (product of the shipped `Int`); no new `ZZ^2` type, no `Quot`.

`Init`-only (over `Homology/CrossedModuleCyclicPowerInvariant` and the `ComputerAlgebra.Number` Int kit),
structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/CrossedModuleTorusAsphericity.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## V0 — small propext-clean helpers (all `torus`-prefixed to dodge the duplicate-global trap) -/

/-- `Nat.beq a b = true → a = b`, an OWN structural double-recursion (never Init's `Nat.eq_of_beq_eq_true`,
which is not gated here).  Full enum over the four `0`/`succ` shapes; `Bool.noConfusion` on the mixed
shapes, `congrArg (· + 1)` on the recursive shape. -/
theorem torusNatEqOfBeqTrue : ∀ (leftValue rightValue : Nat),
    Nat.beq leftValue rightValue = true → leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, isEqual => Bool.noConfusion isEqual
  | _ + 1, 0, isEqual => Bool.noConfusion isEqual
  | leftPredecessor + 1, rightPredecessor + 1, isEqual =>
      congrArg (· + 1) (torusNatEqOfBeqTrue leftPredecessor rightPredecessor isEqual)

/-- Assemble a pair equality from its two component equalities — the funext-free `Int × Int` reassembler. -/
theorem torusProdMkEq (leftFirst rightFirst leftSecond rightSecond : Int)
    (hFirst : leftFirst = rightFirst) (hSecond : leftSecond = rightSecond) :
    (leftFirst, leftSecond) = (rightFirst, rightSecond) :=
  (congrArg (fun value => (value, leftSecond)) hFirst).trans
    (congrArg (fun value => (rightFirst, value)) hSecond)

/-- Coefficientwise congruence for `Int` addition (the `vecAddCongr` analogue at scalar width). -/
theorem torusIntAddCongr {leftA rightA leftB rightB : Int}
    (hLeft : leftA = rightA) (hRight : leftB = rightB) : leftA + leftB = rightA + rightB :=
  (congrArg (fun value => value + leftB) hLeft).trans (congrArg (fun value => rightA + value) hRight)

/-- `outer + (inner + -outer) = inner` — the Peiffer `a`-cancellation seed (propext-clean Int kit). -/
theorem torusIntCancelMiddle (outer inner : Int) : outer + (inner + -outer) = inner :=
  (congrArg (fun summand => outer + summand) (intAddComm inner (-outer))).trans
    ((intAddAssoc outer (-outer) inner).symm.trans
      ((congrArg (fun summand => summand + inner) (intAddRightNeg outer)).trans (intZeroAdd inner)))

/-! ## V1 — the `ZZ^2`-abelianization of free-group words (the invariant's residue engine) -/

/-- The `Bool`-guarded integer contribution: `true ↦ value`, `false ↦ 0`.  A full-enum `Bool` match — the
propext-clean replacement for a `Bool`-conditioned `if`. -/
def torusMatchedInt (isMatch : Bool) (value : Int) : Int :=
  match isMatch with
  | true => value
  | false => 0

/-- `torusMatchedInt m 1 + torusMatchedInt m (-1) = 0` — the same-guard `+1`/`-1` cancellation. -/
theorem torusMatchedIntCancelPair : ∀ isMatch : Bool,
    torusMatchedInt isMatch 1 + torusMatchedInt isMatch (-1) = 0
  | true => intAddRightNeg 1
  | false => rfl

/-- `torusMatchedInt m (-1) + torusMatchedInt m 1 = 0` — the reversed same-guard cancellation. -/
theorem torusMatchedIntCancelPairRev : ∀ isMatch : Bool,
    torusMatchedInt isMatch (-1) + torusMatchedInt isMatch 1 = 0
  | true => intAddLeftNeg 1
  | false => rfl

/-- `torusMatchedInt m (-1) = -(torusMatchedInt m 1)` — negation commutes through the `+1`/`-1` guard. -/
theorem torusMatchedIntNegPos : ∀ isMatch : Bool,
    torusMatchedInt isMatch (-1) = -(torusMatchedInt isMatch 1)
  | true => rfl
  | false => intNegZero.symm

/-- `torusMatchedInt m 1 = -(torusMatchedInt m (-1))` — the reversed negation-through-guard. -/
theorem torusMatchedIntNegNeg : ∀ isMatch : Bool,
    torusMatchedInt isMatch 1 = -(torusMatchedInt isMatch (-1))
  | true => (intNegNeg 1).symm
  | false => intNegZero.symm

/-- The per-generator exponent contribution of a single signed letter: `+1` for `pos g` when `g = target`,
`-1` for `neg g` when `g = target`, else `0`.  The generator match dispatches on `Nat.beq` (full enum). -/
def expGenLetter (target : Nat) : SignedLetter → Int
  | .pos generator => torusMatchedInt (Nat.beq target generator) 1
  | .neg generator => torusMatchedInt (Nat.beq target generator) (-1)

/-- **The per-generator exponent sum** `expGen target w` — the coefficient of `target` in the Fox
augmentation of `w`, a right fold of the per-letter contributions.  `abWordTorus` reads it at `0` and `1`. -/
def expGenTorus (target : Nat) : List SignedLetter → Int
  | [] => 0
  | letter :: rest => expGenLetter target letter + expGenTorus target rest

/-- `expGenLetter target (inverseLetter L) = -(expGenLetter target L)` — inverting a letter negates its
exponent contribution (both signs, via the guard-negation lemmas). -/
theorem expGenLetterInverse : ∀ (target : Nat) (letter : SignedLetter),
    expGenLetter target (inverseLetter letter) = -(expGenLetter target letter)
  | target, .pos generator => torusMatchedIntNegPos (Nat.beq target generator)
  | target, .neg generator => torusMatchedIntNegNeg (Nat.beq target generator)

/-- ★ **Mutually-inverse letters cancel in every coordinate** — `expGenLetter target letter +
expGenLetter target top = 0` when `areInverse letter top = true`.  Unlike r8's rotation (which ignores the
generator), the additive residue DOES read the generator, so the cancel uses `torusNatEqOfBeqTrue` to align
the two generators; the same-sign shapes are `areInverse = false`, killed by `Bool.noConfusion`. -/
theorem expGenLetterInverseCancel : ∀ (target : Nat) (letter top : SignedLetter),
    areInverse letter top = true → expGenLetter target letter + expGenLetter target top = 0
  | target, .pos leftGen, .neg rightGen, sameGen =>
      (congrArg
          (fun generator =>
            torusMatchedInt (Nat.beq target leftGen) 1 + torusMatchedInt (Nat.beq target generator) (-1))
          (torusNatEqOfBeqTrue leftGen rightGen sameGen).symm).trans
        (torusMatchedIntCancelPair (Nat.beq target leftGen))
  | target, .neg leftGen, .pos rightGen, sameGen =>
      (congrArg
          (fun generator =>
            torusMatchedInt (Nat.beq target leftGen) (-1) + torusMatchedInt (Nat.beq target generator) 1)
          (torusNatEqOfBeqTrue leftGen rightGen sameGen).symm).trans
        (torusMatchedIntCancelPairRev (Nat.beq target leftGen))
  | _, .pos _, .pos _, sameGen => Bool.noConfusion sameGen
  | _, .neg _, .neg _, sameGen => Bool.noConfusion sameGen

/-- ★ **`consReduced` preserves the exponent sum** — free cancellation drops the annihilating pair (cancel
case, via `expGenLetterInverseCancel`) or extends (extend case).  Mirror of r8's
`applyWordRotateConsReduced` for the additive residue. -/
theorem expGenTorusConsReduced (target : Nat) : ∀ (letter : SignedLetter) (word : List SignedLetter),
    expGenTorus target (consReduced letter word) = expGenLetter target letter + expGenTorus target word
  | _, [] => rfl
  | letter, top :: rest =>
      match hCancel : areInverse letter top with
      | true =>
          (congrArg (fun reducedWord => expGenTorus target reducedWord)
              (consReducedCancel letter top rest hCancel)).trans
            ((intZeroAdd (expGenTorus target rest)).symm.trans
              ((congrArg (fun value => value + expGenTorus target rest)
                  (expGenLetterInverseCancel target letter top hCancel).symm).trans
                (intAddAssoc (expGenLetter target letter) (expGenLetter target top)
                  (expGenTorus target rest))))
      | false =>
          congrArg (fun reducedWord => expGenTorus target reducedWord)
            (consReducedExtend letter top rest hCancel)

/-- ★★ **`reduceWord` preserves the exponent sum** — free reduction never changes the Fox augmentation. -/
theorem expGenTorusReduceInvariant (target : Nat) : ∀ word : List SignedLetter,
    expGenTorus target (reduceWord word) = expGenTorus target word
  | [] => rfl
  | letter :: rest =>
      (expGenTorusConsReduced target letter (reduceWord rest)).trans
        (congrArg (fun value => expGenLetter target letter + value)
          (expGenTorusReduceInvariant target rest))

/-- ★ **The exponent sum is an append-homomorphism** — `expGen target (x ++ y) = expGen target x +
expGen target y`. -/
theorem expGenTorusAppend (target : Nat) : ∀ leftWord rightWord : List SignedLetter,
    expGenTorus target (leftWord ++ rightWord)
      = expGenTorus target leftWord + expGenTorus target rightWord
  | [], rightWord => (intZeroAdd (expGenTorus target rightWord)).symm
  | letter :: rest, rightWord =>
      (congrArg (fun value => expGenLetter target letter + value)
          (expGenTorusAppend target rest rightWord)).trans
        (intAddAssoc (expGenLetter target letter) (expGenTorus target rest)
          (expGenTorus target rightWord)).symm

/-- ★ **The exponent sum sends the free inverse to negation** — `expGen target (invWord w) =
-(expGen target w)`, through the `invWord` cons law + `intNegAdd`. -/
theorem expGenTorusInvWord : ∀ (target : Nat) (word : List SignedLetter),
    expGenTorus target (invWord word) = -(expGenTorus target word)
  | _, [] => intNegZero.symm
  | target, letter :: rest =>
      (congrArg (fun reversedWord => expGenTorus target reversedWord) (invWordCons letter rest)).trans
        ((expGenTorusAppend target (invWord rest) [inverseLetter letter]).trans
          ((congrArg (fun value => value + expGenTorus target [inverseLetter letter])
              (expGenTorusInvWord target rest)).trans
            ((congrArg (fun value => -(expGenTorus target rest) + value)
                ((intAddZero (expGenLetter target (inverseLetter letter))).trans
                  (expGenLetterInverse target letter))).trans
              ((intAddComm (-(expGenTorus target rest)) (-(expGenLetter target letter))).trans
                (intNegAdd (expGenLetter target letter) (expGenTorus target rest)).symm))))

/-! ## V1 — the `ZZ^2` value (`Int × Int`) and its pair operations -/

/-- **The abelianization of a conjugator word in `ZZ^2`** — the pair of per-generator exponent sums
`(expGen 0 w, expGen 1 w)` (the image of `w` in `ZZ^2 = F(a, b)^{ab}`). -/
def abWordTorus (word : List SignedLetter) : Int × Int := (expGenTorus 0 word, expGenTorus 1 word)

/-- Coefficientwise addition in `ZZ^2`. -/
def torusPairAdd (leftPair rightPair : Int × Int) : Int × Int :=
  (leftPair.1 + rightPair.1, leftPair.2 + rightPair.2)

/-- Coefficientwise negation in `ZZ^2`. -/
def torusPairNeg (pair : Int × Int) : Int × Int := (-pair.1, -pair.2)

/-- `torusPairAdd (0, 0) p = p` — the left identity of `ZZ^2` addition. -/
theorem torusPairAddZeroLeft (pair : Int × Int) : torusPairAdd (0, 0) pair = pair :=
  torusProdMkEq (0 + pair.1) pair.1 (0 + pair.2) pair.2 (intZeroAdd pair.1) (intZeroAdd pair.2)

/-- `torusPairAdd p (0, 0) = p` — the right identity of `ZZ^2` addition. -/
theorem torusPairAddZeroRight (pair : Int × Int) : torusPairAdd pair (0, 0) = pair :=
  torusProdMkEq (pair.1 + 0) pair.1 (pair.2 + 0) pair.2 (intAddZero pair.1) (intAddZero pair.2)

/-- `torusPairAdd p (torusPairNeg p) = (0, 0)` — coefficientwise `p + (-p) = 0`. -/
theorem torusPairAddNegCancel (pair : Int × Int) : torusPairAdd pair (torusPairNeg pair) = (0, 0) :=
  torusProdMkEq (pair.1 + -pair.1) 0 (pair.2 + -pair.2) 0 (intAddRightNeg pair.1) (intAddRightNeg pair.2)

/-- `abWordTorus (reduceWord w) = abWordTorus w` — free reduction preserves the `ZZ^2`-abelianization. -/
theorem abWordTorusReduceInvariant (word : List SignedLetter) :
    abWordTorus (reduceWord word) = abWordTorus word :=
  torusProdMkEq (expGenTorus 0 (reduceWord word)) (expGenTorus 0 word)
    (expGenTorus 1 (reduceWord word)) (expGenTorus 1 word)
    (expGenTorusReduceInvariant 0 word) (expGenTorusReduceInvariant 1 word)

/-- `abWordTorus (x ++ y) = torusPairAdd (abWordTorus x) (abWordTorus y)` — the abelianization is an
append-homomorphism. -/
theorem abWordTorusAppend (leftWord rightWord : List SignedLetter) :
    abWordTorus (leftWord ++ rightWord) = torusPairAdd (abWordTorus leftWord) (abWordTorus rightWord) :=
  torusProdMkEq (expGenTorus 0 (leftWord ++ rightWord)) (expGenTorus 0 leftWord + expGenTorus 0 rightWord)
    (expGenTorus 1 (leftWord ++ rightWord)) (expGenTorus 1 leftWord + expGenTorus 1 rightWord)
    (expGenTorusAppend 0 leftWord rightWord) (expGenTorusAppend 1 leftWord rightWord)

/-- `abWordTorus (invWord w) = torusPairNeg (abWordTorus w)` — the abelianization sends the free inverse to
negation. -/
theorem abWordTorusInvWord (word : List SignedLetter) :
    abWordTorus (invWord word) = torusPairNeg (abWordTorus word) :=
  torusProdMkEq (expGenTorus 0 (invWord word)) (-(expGenTorus 0 word))
    (expGenTorus 1 (invWord word)) (-(expGenTorus 1 word))
    (expGenTorusInvWord 0 word) (expGenTorusInvWord 1 word)

/-! ### V1 truth probes — the abelianization on the commutator relator (both concrete `rfl`) -/

/-- ★ **The commutator abelianizes to `(0, 0)`** — `abWordTorus [a, b] = (0, 0)`, because `a` and `a^{-1}`
cancel in the `a`-exponent and `b`, `b^{-1}` cancel in the `b`-exponent.  This is the Peiffer-invariance
seed (the torus mirror of r8's "net rotation `n ≡ 0`", but a plain `rfl` — NO cyclicity needed). -/
theorem abWordTorusCommutatorRelator : abWordTorus commutatorRelator = (0, 0) := rfl

/-- ★ The inverse commutator also abelianizes to `(0, 0)` (`[a, b]^{-1} = b a b^{-1} a^{-1}`).  `rfl`. -/
theorem abWordTorusInvCommutatorRelator : abWordTorus (invWord commutatorRelator) = (0, 0) := rfl

/-! ## V2 — the torus boundary and the crossed-module invariant `E → ZZ[ZZ^2]` -/

/-- **The boundary of a single conjugated relator against `[a, b]`**, valued in the free group `F(a, b)`:
positive `(w, [a, b])` maps to `w · [a, b] · w^{-1}`, negative to `w · [a, b]^{-1} · w^{-1}`.  The
commutator analogue of r7's `conjugatedRelatorBoundaryAt` (whose relator is a single-generator power). -/
def commutatorConjugatedBoundary (gen : ConjugatedRelator) : List SignedLetter :=
  match gen.isPositive with
  | true =>
      reduceWord (gen.conjugator ++ commutatorRelator ++ invWord gen.conjugator)
  | false =>
      reduceWord (gen.conjugator ++ invWord commutatorRelator ++ invWord gen.conjugator)

/-- **The crossed-module boundary `∂ : E → F(a, b)`** against `[a, b]`, the reduced product of the
per-generator boundaries.  The torus `partialBoundary`. -/
def torusPartialBoundary : PreCrossedElement → List SignedLetter
  | [] => oneWord
  | gen :: rest => mulWord (commutatorConjugatedBoundary gen) (torusPartialBoundary rest)

/-- ★★ **A conjugated `(0, 0)`-body abelianizes to `(0, 0)`** — `abWordTorus (reduceWord (c · body ·
c^{-1})) = (0, 0)` whenever `abWordTorus body = (0, 0)`.  Reduction preserves the abelianization, the appends
fold `c`'s and `c^{-1}`'s exponents, the `(0, 0)`-body drops out, and `c`/`c^{-1}` cancel.  The single crux
of Peiffer-invariance, factored over the body. -/
theorem conjugatedBodyAbelianizesToZero (conjugatorWord bodyWord : List SignedLetter)
    (bodyIsZero : abWordTorus bodyWord = (0, 0)) :
    abWordTorus (reduceWord (conjugatorWord ++ bodyWord ++ invWord conjugatorWord)) = (0, 0) :=
  (abWordTorusReduceInvariant (conjugatorWord ++ bodyWord ++ invWord conjugatorWord)).trans
    ((abWordTorusAppend (conjugatorWord ++ bodyWord) (invWord conjugatorWord)).trans
      ((congrArg (fun pair => torusPairAdd pair (abWordTorus (invWord conjugatorWord)))
          (abWordTorusAppend conjugatorWord bodyWord)).trans
        ((congrArg
            (fun pair =>
              torusPairAdd (torusPairAdd (abWordTorus conjugatorWord) pair)
                (abWordTorus (invWord conjugatorWord)))
            bodyIsZero).trans
          ((congrArg
              (fun pair =>
                torusPairAdd (torusPairAdd (abWordTorus conjugatorWord) (0, 0)) pair)
              (abWordTorusInvWord conjugatorWord)).trans
            ((congrArg (fun pair => torusPairAdd pair (torusPairNeg (abWordTorus conjugatorWord)))
                (torusPairAddZeroRight (abWordTorus conjugatorWord))).trans
              (torusPairAddNegCancel (abWordTorus conjugatorWord)))))))

/-- ★★ **The torus boundary abelianizes to `(0, 0)`** — `abWordTorus (commutatorConjugatedBoundary g) =
(0, 0)` for every generator (both signs).  The relator abelianizes to `(0, 0)` (`abWordTorusCommutatorRelator`)
so the conjugated body is a `(0, 0)`-body.  The Peiffer crux. -/
theorem commutatorConjugatedBoundaryAbelianizesToZero : ∀ gen : ConjugatedRelator,
    abWordTorus (commutatorConjugatedBoundary gen) = (0, 0)
  | ⟨conjugatorWord, _, true⟩ =>
      conjugatedBodyAbelianizesToZero conjugatorWord commutatorRelator abWordTorusCommutatorRelator
  | ⟨conjugatorWord, _, false⟩ =>
      conjugatedBodyAbelianizesToZero conjugatorWord (invWord commutatorRelator)
        abWordTorusInvCommutatorRelator

/-- `Bool` equality on `Int` — full-enum over the two constructors, `Nat.beq` on the payloads.  Used only
as an opaque monomial-match; NO correctness lemma is needed (the invariant rewrites it by `congrArg` on
honest `abWordTorus` equalities). -/
def intBeqTorus : Int → Int → Bool
  | .ofNat leftValue, .ofNat rightValue => Nat.beq leftValue rightValue
  | .negSucc leftValue, .negSucc rightValue => Nat.beq leftValue rightValue
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => false

/-- `Bool` equality on `ZZ^2` monomials — both coordinates agree. -/
def torusPairBeq (leftPair rightPair : Int × Int) : Bool :=
  match intBeqTorus leftPair.1 rightPair.1 with
  | true => intBeqTorus leftPair.2 rightPair.2
  | false => false

/-- The signed contribution of one generator at a target monomial: `signInt gen.isPositive` when the
generator's conjugator abelianizes to `target`, else `0`.  A full-enum `Bool` guard. -/
def torusSignContribGuarded (shouldCount : Bool) (sign : Bool) : Int :=
  match shouldCount with
  | true => signInt sign
  | false => 0

/-- **The `ZZ[ZZ^2]`-coefficient contribution of one conjugated relator** at a target monomial. -/
def torusCoeffContribution (target : Int × Int) (gen : ConjugatedRelator) : Int :=
  torusSignContribGuarded (torusPairBeq (abWordTorus gen.conjugator) target) gen.isPositive

/-- ★ **The relation-module invariant `E → ZZ[ZZ^2]`, read at a target monomial** — `torusImageCoeffAt
target x` is the coefficient of `target` in the abelianized relation-module image of `x`, an additive fold
of the per-generator signed contributions.  The funext-free `crossedModuleImageN`. -/
def torusImageCoeffAt (target : Int × Int) : PreCrossedElement → Int
  | [] => 0
  | gen :: rest => torusCoeffContribution target gen + torusImageCoeffAt target rest

/-- ★ **The invariant is an append-homomorphism at every target** — `coeff target (x ++ y) = coeff target x
+ coeff target y`. -/
theorem torusImageCoeffAtAppend (target : Int × Int) : ∀ leftPart rightPart : PreCrossedElement,
    torusImageCoeffAt target (leftPart ++ rightPart)
      = torusImageCoeffAt target leftPart + torusImageCoeffAt target rightPart
  | [], rightPart => (intZeroAdd (torusImageCoeffAt target rightPart)).symm
  | gen :: rest, rightPart =>
      (congrArg (fun value => torusCoeffContribution target gen + value)
          (torusImageCoeffAtAppend target rest rightPart)).trans
        (intAddAssoc (torusCoeffContribution target gen) (torusImageCoeffAt target rest)
          (torusImageCoeffAt target rightPart)).symm

/-- `signInt (Bool.not b) = -(signInt b)` — the formal inverse flips the augmentation sign. -/
theorem torusSignIntNotIsNeg : ∀ sign : Bool, signInt (Bool.not sign) = -(signInt sign)
  | true => rfl
  | false => (intNegNeg 1).symm

/-- `torusSignContribGuarded m (Bool.not b) = -(torusSignContribGuarded m b)` — negation through the guard. -/
theorem torusSignContribGuardedNeg : ∀ (shouldCount sign : Bool),
    torusSignContribGuarded shouldCount (Bool.not sign) = -(torusSignContribGuarded shouldCount sign)
  | true, sign => torusSignIntNotIsNeg sign
  | false, _ => intNegZero.symm

/-- ★ **The invariant sends the formal inverse to negation** — `coeff target (invGen g) = -(coeff target g)`.
`invGen` keeps the conjugator (so the target-match is unchanged) and flips the sign. -/
theorem torusCoeffContributionInvGen (target : Int × Int) (gen : ConjugatedRelator) :
    torusCoeffContribution target (invGen gen) = -(torusCoeffContribution target gen) :=
  torusSignContribGuardedNeg (torusPairBeq (abWordTorus gen.conjugator) target) gen.isPositive

/-! ## V3 — the torus Peiffer relation and the Peiffer-invariance keystone -/

/-- **The `F`-action `^{∂a}b` for the torus** — keep `b`'s relator and sign, pre-multiply its conjugator by
the commutator boundary `∂a`.  The commutator `peifferConjugate`. -/
def peifferConjugateTorus (firstGen secondGen : ConjugatedRelator) : ConjugatedRelator :=
  { secondGen with
    conjugator := reduceWord (commutatorConjugatedBoundary firstGen ++ secondGen.conjugator) }

/-- ★ **The torus Peiffer congruence** on `E`, whose generating move `a b a^{-1} ~ ^{∂a}b` conjugates by the
commutator boundary `∂a`.  A `Prop`-inductive (no `Quot`); NOT reusable from r8's `PeifferEquivAt`, whose
move conjugates by a single-generator power boundary. -/
inductive PeifferEquivTorus : PreCrossedElement → PreCrossedElement → Prop where
  /-- Reflexivity. -/
  | refl (element : PreCrossedElement) : PeifferEquivTorus element element
  /-- Symmetry. -/
  | symm {leftElement rightElement : PreCrossedElement} :
      PeifferEquivTorus leftElement rightElement → PeifferEquivTorus rightElement leftElement
  /-- Transitivity. -/
  | trans {leftElement middleElement rightElement : PreCrossedElement} :
      PeifferEquivTorus leftElement middleElement → PeifferEquivTorus middleElement rightElement →
      PeifferEquivTorus leftElement rightElement
  /-- Append-congruence. -/
  | congrAppend {leftA leftB rightA rightB : PreCrossedElement} :
      PeifferEquivTorus leftA rightA → PeifferEquivTorus leftB rightB →
      PeifferEquivTorus (leftA ++ leftB) (rightA ++ rightB)
  /-- ★ The generating Peiffer move `a b a^{-1} ~ ^{∂a}b`. -/
  | peifferMove (firstGen secondGen : ConjugatedRelator) :
      PeifferEquivTorus [firstGen, secondGen, invGen firstGen]
        [peifferConjugateTorus firstGen secondGen]

/-- ★★ **The Peiffer conjugator has the same abelianization** — `abWordTorus (∂a · b)^{red} = abWordTorus b`.
Reduction preserves the abelianization, the append folds `∂a` onto `b`, and `∂a` abelianizes to `(0, 0)`
(`commutatorConjugatedBoundaryAbelianizesToZero`). -/
theorem peifferConjugateTorusAbEq (firstGen secondGen : ConjugatedRelator) :
    abWordTorus (peifferConjugateTorus firstGen secondGen).conjugator
      = abWordTorus secondGen.conjugator :=
  (abWordTorusReduceInvariant (commutatorConjugatedBoundary firstGen ++ secondGen.conjugator)).trans
    ((abWordTorusAppend (commutatorConjugatedBoundary firstGen) secondGen.conjugator).trans
      ((congrArg (fun pair => torusPairAdd pair (abWordTorus secondGen.conjugator))
          (commutatorConjugatedBoundaryAbelianizesToZero firstGen)).trans
        (torusPairAddZeroLeft (abWordTorus secondGen.conjugator))))

/-- ★★ **The Peiffer conjugate has the same coefficient contribution** — `coeff target (^{∂a}b) =
coeff target b`, since it has `b`'s sign and the same conjugator abelianization. -/
theorem peifferConjugateTorusCoeffEq (target : Int × Int) (firstGen secondGen : ConjugatedRelator) :
    torusCoeffContribution target (peifferConjugateTorus firstGen secondGen)
      = torusCoeffContribution target secondGen :=
  congrArg (fun pair => torusSignContribGuarded (torusPairBeq pair target) secondGen.isPositive)
    (peifferConjugateTorusAbEq firstGen secondGen)

/-- ★★ **The generating Peiffer move is invariant** — `coeff target [a, b, a^{-1}] = coeff target [^{∂a}b]`.
The `a`/`a^{-1}` contributions cancel (`torusCoeffContributionInvGen` + `torusIntCancelMiddle`), leaving
`coeff target b`; and `^{∂a}b` has the same contribution as `b` (`peifferConjugateTorusCoeffEq`).  Mirror of
r8's `peifferMoveImageN` — but the cancellation is a plain scalar `a + (b + -a) = b`. -/
theorem peifferMoveImageTorus (target : Int × Int) (firstGen secondGen : ConjugatedRelator) :
    torusImageCoeffAt target [firstGen, secondGen, invGen firstGen]
      = torusImageCoeffAt target [peifferConjugateTorus firstGen secondGen] :=
  (congrArg (fun value => torusCoeffContribution target firstGen +
        (torusCoeffContribution target secondGen + value))
      ((intAddZero (torusCoeffContribution target (invGen firstGen))).trans
        (torusCoeffContributionInvGen target firstGen))).trans
    ((torusIntCancelMiddle (torusCoeffContribution target firstGen)
        (torusCoeffContribution target secondGen)).trans
      ((intAddZero (torusCoeffContribution target (peifferConjugateTorus firstGen secondGen))).trans
        (peifferConjugateTorusCoeffEq target firstGen secondGen)).symm)

/-- ★★★ **THE PEIFFER-INVARIANCE KEYSTONE** — the invariant `torusImageCoeffAt target` is constant on the
torus Peiffer classes: `PeifferEquivTorus x y → ∀ target, coeff target x = coeff target y`.  Structural
recursion on the `PeifferEquivTorus` proof (the 5 arms): `refl` is `rfl`, `symm`/`trans` close the
equivalence, `congrAppend` uses the append-homomorphism, and the generating `peifferMove` is
`peifferMoveImageTorus`.  The soundness keystone — the invariant descends to the crossed module
`C = E / PeifferEquivTorus`.  The `∀ target` conclusion keeps this a coefficient statement (NO funext). -/
theorem torusImageRespectsPeiffer (target : Int × Int) :
    ∀ {leftElement rightElement : PreCrossedElement},
    PeifferEquivTorus leftElement rightElement →
    torusImageCoeffAt target leftElement = torusImageCoeffAt target rightElement
  | _, _, .refl _ => rfl
  | _, _, .symm equivReversed => (torusImageRespectsPeiffer target equivReversed).symm
  | _, _, .trans equivLeftMid equivMidRight =>
      (torusImageRespectsPeiffer target equivLeftMid).trans
        (torusImageRespectsPeiffer target equivMidRight)
  | _, _, .congrAppend equivLeftPair equivRightPair =>
      (torusImageCoeffAtAppend target _ _).trans
        ((torusIntAddCongr (torusImageRespectsPeiffer target equivLeftPair)
            (torusImageRespectsPeiffer target equivRightPair)).trans
          (torusImageCoeffAtAppend target _ _).symm)
  | _, _, .peifferMove firstGen secondGen => peifferMoveImageTorus target firstGen secondGen

/-! ## V4 — the kernel-vanishing witnesses, the ζ-mirror contrast, and the Fox-Jacobian record

Every torus kernel identity (`∂ = []`) of the rotation/nesting shapes images to `0` — the OPPOSITE of r8's
separating `ζ`.  This is the abelianized/Alexander vanishing (CONSISTENT with `π₂ = 0`); it does NOT prove
`π₂ = 0` (that needs the relation-module injectivity, walled).  The contrast `torusContrastWitnessTwo` is
the ζ-mirror: nonzero image (`a - 1`) but its boundary is a genuine reduced word, NOT in the kernel. -/

/-- Kernel witness `id₁ = [(a, r, +), (a, r, -)]` — the trivial conjugated cancellation `g · g^{-1}`. -/
def torusKernelWitnessOne : PreCrossedElement :=
  [⟨[SignedLetter.pos 0], 0, true⟩, ⟨[SignedLetter.pos 0], 0, false⟩]

/-- ★ **`id₁ ∈ ker ∂`** — `∂ id₁ = []` (`(a [a,b] a^{-1})(a [a,b] a^{-1})^{-1}` telescopes).  `rfl`. -/
theorem torusKernelWitnessOneInKernel : torusPartialBoundary torusKernelWitnessOne = oneWord := rfl

/-- ★ **`id₁` images to `0` at `a`** — `coeff (1, 0) id₁ = 1 + (-1) = 0`.  `rfl`. -/
theorem torusKernelWitnessOneImageVanishesAtA :
    torusImageCoeffAt (1, 0) torusKernelWitnessOne = 0 := rfl

/-- ★ **`id₁` images to `0` at the unit** — `coeff (0, 0) id₁ = 0`.  `rfl`. -/
theorem torusKernelWitnessOneImageVanishesAtUnit :
    torusImageCoeffAt (0, 0) torusKernelWitnessOne = 0 := rfl

/-- The ζ-mirror contrast `id₂ = [(a, r, +), (1, r, -)]` — r8's separating `ζ` shape transplanted to the
torus.  NONZERO image (`a - 1`) but, unlike r8's `ζ`, NOT in the kernel. -/
def torusContrastWitnessTwo : PreCrossedElement :=
  [⟨[SignedLetter.pos 0], 0, true⟩, ⟨[], 0, false⟩]

/-- ★ **`id₂` has NONZERO image at `a`** — `coeff (1, 0) id₂ = 1` (the `a`-monomial of `a - 1`).  `rfl`. -/
theorem torusContrastWitnessTwoImageAtA :
    torusImageCoeffAt (1, 0) torusContrastWitnessTwo = 1 := rfl

/-- ★ **`id₂` has image `-1` at the unit** — `coeff (0, 0) id₂ = -1` (the `1`-monomial of `a - 1`).  `rfl`. -/
theorem torusContrastWitnessTwoImageAtUnit :
    torusImageCoeffAt (0, 0) torusContrastWitnessTwo = -1 := rfl

/-- ★★ **`id₂` is NOT in the kernel** — `∂ id₂ ≠ []`, recorded as `wordBeq (∂ id₂) oneWord = false` (the
boundary is a genuine length-`10` reduced word `[a, [a,b]] · [a,b]^{-1}`).  `rfl`.  This is why the invariant
CANNOT prove `π₂ ≠ 0` for the torus (its only in-kernel rotations force the conjugator into `⟨[a,b]⟩`, whose
abelianization is `(0, 0)`) — fully CONSISTENT with the classical `π₂ = 0`. -/
theorem torusContrastWitnessTwoNotInKernel :
    wordBeq (torusPartialBoundary torusContrastWitnessTwo) oneWord = false := rfl

/-- Kernel witness `id₃ = [(r, r, +), (1, r, -)]` (`w = r = [a, b]`) — the primitive-centralizer rotation. -/
def torusKernelWitnessThree : PreCrossedElement :=
  [⟨commutatorRelator, 0, true⟩, ⟨[], 0, false⟩]

/-- ★ **`id₃ ∈ ker ∂`** — `∂ id₃ = []` (`([a,b] [a,b] [a,b]^{-1})([a,b])^{-1} = [a,b] [a,b]^{-1} = []`).
`rfl`. -/
theorem torusKernelWitnessThreeInKernel : torusPartialBoundary torusKernelWitnessThree = oneWord := rfl

/-- ★ **`id₃` images to `0` at the unit** — `coeff (0, 0) id₃ = 1 + (-1) = 0` (the conjugator `[a, b]`
abelianizes to `(0, 0)`, so both generators sit at the unit monomial and cancel).  `rfl`. -/
theorem torusKernelWitnessThreeImageVanishesAtUnit :
    torusImageCoeffAt (0, 0) torusKernelWitnessThree = 0 := rfl

/-- Kernel witness `id₄ = [(a, r, +), (b, r, +), (b, r, -), (a, r, -)]` — a nested conjugated cancellation. -/
def torusKernelWitnessFour : PreCrossedElement :=
  [⟨[SignedLetter.pos 0], 0, true⟩, ⟨[SignedLetter.pos 1], 0, true⟩,
   ⟨[SignedLetter.pos 1], 0, false⟩, ⟨[SignedLetter.pos 0], 0, false⟩]

/-- ★ **`id₄ ∈ ker ∂`** — `∂ id₄ = []` (nested telescoping).  `rfl`. -/
theorem torusKernelWitnessFourInKernel : torusPartialBoundary torusKernelWitnessFour = oneWord := rfl

/-- ★ **`id₄` images to `0` at `a`** — `coeff (1, 0) id₄ = 1 + (-1) = 0`.  `rfl`. -/
theorem torusKernelWitnessFourImageVanishesAtA :
    torusImageCoeffAt (1, 0) torusKernelWitnessFour = 0 := rfl

/-- ★ **`id₄` images to `0` at `b`** — `coeff (0, 1) id₄ = 1 + (-1) = 0`.  `rfl`. -/
theorem torusKernelWitnessFourImageVanishesAtB :
    torusImageCoeffAt (0, 1) torusKernelWitnessFour = 0 := rfl

/-! ### The Fox-Jacobian record — `∂[a,b]/∂a = 1 - b`, `∂[a,b]/∂b = a - 1` (the Koszul regular sequence)

The two Fox derivatives, projected into `ZZ[ZZ^2]`, are recorded as coefficient functions on monomials.
Their nonzero coefficients WITNESS the Jacobian `(1 - b, a - 1)` — the regular sequence whose injectivity
(over the domain `ZZ[ZZ^2]`) is the classical `ker(∂₂) = 0`.  The witnesses are positive `rfl` records; the
injectivity itself is the walled node. -/

/-- The projected Fox derivative `∂[a,b]/∂a = 1 - b` as a monomial-coefficient function (`+1` at `1`, `-1`
at `b`). -/
def foxDerivACoeff (monomial : Int × Int) : Int :=
  torusMatchedInt (torusPairBeq monomial (0, 0)) 1 + torusMatchedInt (torusPairBeq monomial (0, 1)) (-1)

/-- The projected Fox derivative `∂[a,b]/∂b = a - 1` as a monomial-coefficient function (`+1` at `a`, `-1`
at `1`). -/
def foxDerivBCoeff (monomial : Int × Int) : Int :=
  torusMatchedInt (torusPairBeq monomial (1, 0)) 1 + torusMatchedInt (torusPairBeq monomial (0, 0)) (-1)

/-- ★ `∂[a,b]/∂a` has coefficient `+1` at the unit monomial `1` (the `1` of `1 - b`, nonzero).  `rfl`. -/
theorem foxDerivACoeffAtUnit : foxDerivACoeff (0, 0) = 1 := rfl

/-- ★ `∂[a,b]/∂a` has coefficient `-1` at the `b` monomial (the `-b` of `1 - b`).  `rfl`. -/
theorem foxDerivACoeffAtB : foxDerivACoeff (0, 1) = -1 := rfl

/-- ★ `∂[a,b]/∂b` has coefficient `+1` at the `a` monomial (the `a` of `a - 1`, nonzero).  `rfl`. -/
theorem foxDerivBCoeffAtA : foxDerivBCoeff (1, 0) = 1 := rfl

/-- ★ `∂[a,b]/∂b` has coefficient `-1` at the unit monomial `1` (the `-1` of `a - 1`).  `rfl`. -/
theorem foxDerivBCoeffAtUnit : foxDerivBCoeff (0, 0) = -1 := rfl

/-! ## V4 — the r9 torus-asphericity ledger (records over the shipped r7 status inductive) -/

/-- The seven r9 torus obligations, honestly classified against r7's `CyclicPowerObligationStatus`. -/
structure CrossedModuleTorusAsphericityLedger where
  /-- The `ZZ^2`-abelianization carrier + its append/reduce/inverse laws (V1). -/
  torusCarrierStatus : CyclicPowerObligationStatus
  /-- The invariant `torusImageCoeffAt : E → ZZ[ZZ^2]` + append-homomorphism (V2). -/
  torusInvariantMapStatus : CyclicPowerObligationStatus
  /-- The Peiffer-invariance keystone `torusImageRespectsPeiffer` (V3). -/
  torusPeifferInvarianceStatus : CyclicPowerObligationStatus
  /-- The machine-checked kernel-vanishing witnesses + the ζ-mirror contrast (V4). -/
  kernelVanishingWitnessStatus : CyclicPowerObligationStatus
  /-- The Fox-Jacobian pair `(1 - b, a - 1)` recorded with its nonzero coefficients (V4). -/
  foxJacobianStatus : CyclicPowerObligationStatus
  /-- The Koszul shift-injectivity `y·(1 - b) = 0 ⟹ y = 0` — the walled hard lemma. -/
  koszulShiftInjectivityStatus : CyclicPowerObligationStatus
  /-- The relation-module injectivity `ker(∂₂) = 0` (the universal `π₂ = 0`, Lyndon) — the walled node. -/
  relationModuleInjectivityStatus : CyclicPowerObligationStatus

/-- ★ **The r9 torus-asphericity ledger.**  The abelianization carrier, the invariant map, the
Peiffer-invariance, the kernel-vanishing witnesses, and the Fox-Jacobian record are all SHIPPED zero-axiom;
the Koszul shift-injectivity and the full relation-module injectivity (the universal `π₂⟨a, b | [a, b]⟩ = 0`)
stay walled (the same injectivity node r8 named `inheritedHopfResidual`).  The honest r9 close: the torus
relation-module invariant, its Peiffer-invariance, and the machine-checked kernel-vanishing are delivered;
the classical `π₂ = 0` (Lyndon) is CITED, never claimed. -/
def crossedModuleTorusAsphericityLedger : CrossedModuleTorusAsphericityLedger :=
  { torusCarrierStatus := CyclicPowerObligationStatus.shippedThisRound
  , torusInvariantMapStatus := CyclicPowerObligationStatus.shippedThisRound
  , torusPeifferInvarianceStatus := CyclicPowerObligationStatus.shippedThisRound
  , kernelVanishingWitnessStatus := CyclicPowerObligationStatus.shippedThisRound
  , foxJacobianStatus := CyclicPowerObligationStatus.shippedThisRound
  , koszulShiftInjectivityStatus := CyclicPowerObligationStatus.inheritedHopfResidual
  , relationModuleInjectivityStatus := CyclicPowerObligationStatus.inheritedHopfResidual }

/-- ★ **The #2199 r9 torus-asphericity marker.**  Shipped zero-axiom over r7's commutator opening:

  * **V1 (carrier)** — the `ZZ^2`-abelianization `abWordTorus` (`expGenTorus` reduce-invariance + append +
    inverse), with the concrete `abWordTorus [a, b] = (0, 0)` `rfl` (the Peiffer crux seed — no cyclicity).
  * **V2 (invariant map)** — `torusImageCoeffAt : E → ZZ[ZZ^2]`, the funext-free coefficient-query, with its
    append-homomorphism `torusImageCoeffAtAppend` and the torus boundary `commutatorConjugatedBoundary` whose
    abelianization vanishes (`commutatorConjugatedBoundaryAbelianizesToZero`).
  * **V3 (Peiffer-invariance)** — the torus Peiffer relation `PeifferEquivTorus` (conjugating by `∂a`) and the
    keystone `torusImageRespectsPeiffer` (the invariant descends to `C = E / PeifferEquivTorus`).
  * **V4 (kernel-vanishing + Fox-Jacobian)** — ★ the three kernel witnesses (`id₁`, `id₃`, `id₄`: `∂ = []`
    AND image `0`), the ζ-mirror contrast (`id₂`: image `a - 1 ≠ 0` but `∂ ≠ []`, NOT in the kernel), and the
    Fox-Jacobian pair `(1 - b, a - 1)` with its nonzero coefficients (the Koszul regular sequence).

THE PRESENTED STATEMENT (this file) is the `ZZ[ZZ^2]` relation-module invariant + its Peiffer-invariance +
the machine-checked kernel-vanishing.  THE CLASSICAL THEOREM `π₂⟨a, b | [a, b]⟩ = 0` (Lyndon: `[a, b]` not a
proper power ⟹ aspherical ⟹ `T^2 = K(ZZ^2, 1)`) needs the relation-module INJECTIVITY (`ker(∂₂) = 0` over the
domain `ZZ[ZZ^2]`), which stays walled — the invariant vanishes on the tested kernel but does not certify
injectivity.  Read the meaning from THIS docstring and the ledger, never from an overclaimed name. -/
def crossedModuleTorusAsphericityIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
