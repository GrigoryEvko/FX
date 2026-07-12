import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupStructureTheorem

/-! # FX1Poly/Polygraph/Homology/CrossedModuleCyclicPower — the free crossed module of the GENERAL cyclic
    presentation `⟨s | sⁿ⟩` (the parameterized boundary + the general rotation identity `∂ζₙ = []` for ALL
    `n`, provable off the shipped `signPower` kit) AND the first two-generator opening `⟨a, b | [a, b]⟩`
    (the multi-generator carrier exercised, Lyndon's `π₂ = 0` side, the H₂ cross-check star)
    (WP-2GROUP r7, #2199)

r1–r6 closed the `⟨s | s³⟩` INSTANCE unconditionally (`Homology/CrossedModuleCyclicThree` …
`Homology/CrossedModuleFreeGroupMeasureInduction`: `π₂⟨s | s³⟩ ≅ ker(N) ≅ ZZ[G]` with a TOWER-ANICK Hopf
bridge).  r7 is the honest GENERALIZATION off that closed instance: it parameterizes the boundary by the
exponent `n`, proves the rotation identity vanishes for EVERY `n` as a genuine theorem (not the shipped
`n = 3` `rfl`), and opens the complementary two-generator direction so the H₂ cross-check star can be
named in both rows.

## The two classical fixtures (hand-worked, boundaries evaluated by hand)

### Fixture A — general cyclic `⟨s | sⁿ⟩` (n ≥ 1), presenting `ZZ/n`

Relator `ρₙ = sⁿ`; Fox derivative `∂₂ = N = 1 + s + … + s^{n-1}`; `π₂ = ker(N) =` augmentation ideal
`(s − 1)`, free `ZZ`-rank `n − 1`, cyclic `ZZ[G]`-module `≅ ZZ[G]/(N)`.  Lyndon's dichotomy: `sⁿ` is a
proper power for `n ≥ 2` ⟹ `π₂ ≠ 0`; `n = 1` (trivial group) is not a proper power ⟹ `π₂ = 0`.

Rotation witness `ζₙ = [(s, ρₙ, +), (1, ρₙ, −)]`.  BOUNDARY BY HAND:
`∂ζₙ = (s · sⁿ · s⁻¹) · (sⁿ)⁻¹ = sⁿ · s⁻ⁿ = []` — vanishes for ALL `n` (`ZZ` abelian, the conjugation
collapses).  This is `rotationBoundaryVanishesAt`, a GENERAL theorem via the shipped `signPower` /
`exponentSum` kit (`exponentSum ∂ζₙ = n + (−n) = 0`, and a reduced word of exponent `0` over one
generator is `[]`).  The `n = 3` special case is defeq to the shipped `rotationIdentityBoundaryVanishes`
(`cyclicPowerBoundaryThreeMatchesShipped`).

### Fixture B — two-generator aspherical `⟨a, b | [a, b]⟩`, presenting `ZZ²`

Relator `[a, b] = a b a⁻¹ b⁻¹` — a GENUINE 4-letter reduced word over TWO generators (the first exercise
of the multi-generator carrier).  `[a, b]` is NOT a proper power (primitive commutator) ⟹ by Lyndon the
presentation 2-complex is aspherical (`K(ZZ², 1) = T²`) ⟹ `π₂ = 0`.  BOUNDARY BY HAND:
`∂(1, [a, b]) = reduceWord [a, b] = [a, b]` (already reduced, `commutatorBoundaryIsReduced`) and
`[a, b] · [a, b]⁻¹ = []` telescopes (`commutatorSelfInverseVanishes`).  Fox derivatives `∂_a[a,b] = 1 − b`,
`∂_b[a,b] = a − 1`; `ker(∂₂) = 0` (Koszul regular sequence `(a − 1, b − 1)` in `ZZ[ZZ²]`).

### ★ The H₂ cross-check star (the payload of #2199's "H₂ footing")

| presentation            | abelianized H₂ (trivial coeffs) | π₂ (identities among relations) |
| ----------------------- | ------------------------------- | ------------------------------- |
| `⟨s|sⁿ⟩` (proper, n≥2)  | **0**                           | **≠ 0** (rotation ζₙ)           |
| `⟨a,b|[a,b]⟩` (aspher.) | **ZZ** (= H₂(T²))               | **0**                           |

π₂ and abelianized H₂ are INDEPENDENT invariants — either can vanish while the other does not, in BOTH
directions.  The shipped tower only ever saw the top row; Fixture B delivers the bottom row and completes
the cross-check (`h2CrossCheckStar`).

## THE ARC LEDGER — the rungs to the H₂ cross-check star + the honest ceilings

  * **r7 (this round)** — the general `⟨s | sⁿ⟩` boundary + the kernel witness `∂ζₙ = []` ∀`n` (PROVED),
    the proper-power certificate ∀`n ≥ 2` (`cyclicPowerRelatorProperPower`), AND the two-generator opening
    `⟨a, b | [a, b]⟩` (carrier exercised, Lyndon's `π₂ = 0` side named, the H₂ cross-check star recorded).
  * **r8 (named residual)** — the general `ZZ[ZZ/n]` separating invariant (`ZmodThree → ZmodN`,
    `GroupRingZmod3 → GroupRingZmodN`) ⟹ general `π₂⟨s | sⁿ⟩ ≠ 0` MECHANIZED (Lyndon promoted from cited
    to proved for every `n ≥ 2`).  A distinct clean carrier; NOT attempted this round.
  * **r9 (named residual)** — the two-generator asphericity `π₂⟨a, b | [a, b]⟩ = 0` via the `ZZ[ZZ²]`
    Fox–Koszul argument (a distinct clean carrier).  NOT attempted this round.
  * **inherited residual** — the Hopf-shadow coker iso (r6's `hopfShadowCokerIsZmodThreeIsNamedNode`,
    Smith-cert / `Quot`-walled).

  ★ **The no-quotient scoping (the honest ceiling that never moves).**  `π₂` is PRESENTED, never
  quotiented: the Peiffer relation is DATA (`PeifferEquiv`, a `Prop`-inductive), the identities-among-
  relations kernel is a PREDICATE (`partialBoundaryAt n x = oneWord`).  No `Quot` anywhere in the lane.
  The full `π₂ ≅ ker` iso at general scope needs the free-crossed-module normal form (the r6 measure
  induction), which the instance closed but the general `n` reopens as the r8 injectivity node.

## Zero-axiom design decisions

  * `cyclicPowerRelator`, `conjugatedRelatorBoundaryAt`, `partialBoundaryAt` are the exponent-parameterized
    generalizations of r1's `relatorWord 0` / `conjugatedRelatorBoundary` / `partialBoundary`; the boundary
    dispatches on `isPositive : Bool` through a full-enum match (no wildcard, no `dite`).
  * `rotationBoundaryVanishesAt` rides the shipped crux `reduceWordIsSignPowerOverGenZero` +
    `exponentSumConjugation` + `exponentSumInvWord` + the propext-clean `Int` kit (`intAddZero`,
    `intAddRightNeg`); NO new confluence diamond, NO `Nat` subtraction, NO `WellFounded.fix`.
  * The multi-generator probes close by `rfl` at LITERAL generators (`Nat.beq 0 1 = false`,
    `Nat.beq 1 1 = true`) — never the propext-leaking `Nat.beq_self`.
  * The two H₂-cross-check rows and the arc ledger are plain records over full-enum status inductives.

`Init`-only (over `Homology/CrossedModuleFreeGroupStructureTheorem` and the `ComputerAlgebra.Number` Int
kit), structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicPower.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the general cyclic relator `sⁿ` and the exponent-parameterized boundary -/

/-- The general cyclic relator `ρₙ = sⁿ` over generator `0` — the exponent-parameterized generalization of
r1's hardcoded `relatorWord 0 = s³`.  Definitionally the positive `signPower`. -/
def cyclicPowerRelator (exponent : Nat) : List SignedLetter := signPowerPos exponent

/-- **The boundary of a single conjugated relator against `sⁿ`**, valued in the free group `F(s)`: a
positive `(w, ρₙ)` maps to `w · sⁿ · w⁻¹`; a negative one to `w · s⁻ⁿ · w⁻¹`.  The generalization of r1's
`conjugatedRelatorBoundary` reading `cyclicPowerRelator exponent` instead of `relatorWord`. -/
def conjugatedRelatorBoundaryAt (exponent : Nat) (gen : ConjugatedRelator) : List SignedLetter :=
  match gen.isPositive with
  | true =>
      reduceWord (gen.conjugator ++ cyclicPowerRelator exponent ++ invWord gen.conjugator)
  | false =>
      reduceWord (gen.conjugator ++ invWord (cyclicPowerRelator exponent) ++ invWord gen.conjugator)

/-- **The crossed-module boundary `∂ₙ : E → F(s)`** against `sⁿ`, the reduced product of the per-generator
boundaries.  The exponent-parameterized `partialBoundary`. -/
def partialBoundaryAt (exponent : Nat) : PreCrossedElement → List SignedLetter
  | [] => oneWord
  | gen :: rest => mulWord (conjugatedRelatorBoundaryAt exponent gen) (partialBoundaryAt exponent rest)

/-- The rotation-witness first generator `(s, ρₙ, +)` — conjugates the relator by `s`. -/
def cyclicPowerConjugatorGen : ConjugatedRelator := ⟨[SignedLetter.pos 0], 0, true⟩

/-- The rotation-witness second generator `(1, ρₙ, −)` — the inverse of the un-conjugated relator. -/
def cyclicPowerRelatorInverseGen : ConjugatedRelator := invGen ⟨[], 0, true⟩

/-- ★ **The general rotation identity `ζₙ = (s, ρₙ) · (1, ρₙ)⁻¹`** as a pre-crossed element.  The witness
does NOT depend on `n` (the exponent enters ONLY through the boundary `∂ₙ`); it is literally r1's
`rotationIdentityWitness`. -/
def cyclicPowerRotationWitness : PreCrossedElement :=
  [cyclicPowerConjugatorGen, cyclicPowerRelatorInverseGen]

/-! ### B1 truth probes — evaluate the parameterized boundary on concrete `n` BEFORE proving -/

/-- Probe — `ρ₃ = s³` reconstructs r1's fixed relator: `cyclicPowerRelator 3 = relatorWord 0`.  `rfl`. -/
theorem cyclicPowerRelatorThreeMatchesRelatorWord : cyclicPowerRelator 3 = relatorWord 0 := rfl

/-- Probe — the general witness is r1's rotation witness: `cyclicPowerRotationWitness =
rotationIdentityWitness`.  `rfl`. -/
theorem cyclicPowerRotationWitnessMatchesShipped :
    cyclicPowerRotationWitness = rotationIdentityWitness := rfl

/-- Probe — at `n = 3` the parameterized boundary is defeq to the shipped one: `∂₃ ζ₃ = ∂ ζ` (both `[]`).
The general def specializes to r1's `rotationIdentityBoundaryVanishes`.  `rfl`. -/
theorem cyclicPowerBoundaryThreeMatchesShipped :
    partialBoundaryAt 3 cyclicPowerRotationWitness = partialBoundary rotationIdentityWitness := rfl

/-- Probe — `∂₂ ζ₂ = []` (n = 2: `s² · s⁻² = 1`).  `rfl` on the concrete reduced-word evaluation. -/
theorem rotationBoundaryVanishesAtTwoProbe :
    partialBoundaryAt 2 cyclicPowerRotationWitness = oneWord := rfl

/-- Probe — `∂₅ ζ₅ = []` (n = 5: `s⁵ · s⁻⁵ = 1`).  `rfl`. -/
theorem rotationBoundaryVanishesAtFiveProbe :
    partialBoundaryAt 5 cyclicPowerRotationWitness = oneWord := rfl

/-- Probe — `∂₀ ζ₀ = []` (n = 0: the empty relator, `1 · 1 = 1`).  `rfl`. -/
theorem rotationBoundaryVanishesAtZeroProbe :
    partialBoundaryAt 0 cyclicPowerRotationWitness = oneWord := rfl

/-- Probe (the conjugation collapse, evaluated) — `∂₄⁺(s, ρ₄) = s⁴` (the `s`-conjugation cancels
inside-out).  `rfl`. -/
theorem powerConjugationCollapsesFourProbe :
    conjugatedRelatorBoundaryAt 4 cyclicPowerConjugatorGen = cyclicPowerRelator 4 := rfl

/-! ## B4a — the two-generator relator `[a, b]` (the multi-generator carrier, truth-probed) -/

/-- The commutator relator `[a, b] = a b a⁻¹ b⁻¹` as a GENUINE 4-letter reduced word over TWO generators
(`0 = a`, `1 = b`) — the first word in the lane that exercises the multi-generator carrier non-vacuously. -/
def commutatorRelator : List SignedLetter :=
  [SignedLetter.pos 0, SignedLetter.pos 1, SignedLetter.neg 0, SignedLetter.neg 1]

/-- ★ Probe — `[a, b]` is ALREADY REDUCED: `reduceWord [a, b] = [a, b]` (no adjacent inverse pair — the
two distinct generators cannot cancel).  `rfl` — the multi-generator carrier's first genuine reduction. -/
theorem commutatorBoundaryIsReduced : reduceWord commutatorRelator = commutatorRelator := rfl

/-- ★ Probe — `[a, b] · [a, b]⁻¹ = []` telescopes (`a b a⁻¹ b⁻¹ · b a b⁻¹ a⁻¹`, inside-out).  `rfl`. -/
theorem commutatorSelfInverseVanishes :
    mulWord commutatorRelator (invWord commutatorRelator) = oneWord := rfl

/-- Probe — distinct generators do NOT cancel: `areInverse a b⁻¹ = false` (`Nat.beq 0 1 = false`).  The
multi-generator carrier genuinely distinguishes `a` from `b`.  `rfl`. -/
theorem distinctGeneratorsDoNotCancel :
    areInverse (SignedLetter.pos 0) (SignedLetter.neg 1) = false := rfl

/-- Probe — a generator cancels its OWN inverse: `areInverse b b⁻¹ = true` (`Nat.beq 1 1 = true`).  `rfl`
(never `Nat.beq_self`). -/
theorem generatorCancelsOwnInverse :
    areInverse (SignedLetter.pos 1) (SignedLetter.neg 1) = true := rfl

/-! ## B2 — ★ the general theorem `∂ζₙ = []` for ALL `n` (off the shipped `signPower` kit) -/

/-- `signPower (exponentSum sⁿ) = sⁿ` — a reduced positive `signPower` is fixed by the round-trip through
its exponent sum (crux forward + `reduceWordSignPowerPos` back).  No `exponentSum`-value computation needed. -/
theorem signPowerExponentSumRelator (exponent : Nat) :
    signPower (exponentSum (cyclicPowerRelator exponent)) = cyclicPowerRelator exponent :=
  (reduceWordIsSignPowerOverGenZero (allLettersSignPowerPos exponent)).symm.trans
    (reduceWordSignPowerPos exponent)

/-- The conjugation word `s · sⁿ · s⁻¹` is over generator `0`. -/
theorem firstConjWordOverGenZero (exponent : Nat) :
    AllLettersOverGenZero
      ([SignedLetter.pos 0] ++ cyclicPowerRelator exponent ++ invWord [SignedLetter.pos 0]) :=
  allLettersAppend (allLettersAppend (.consPos [] .nil) (allLettersSignPowerPos exponent))
    (allLettersInvWord (.consPos [] .nil))

/-- ★★ **The conjugation collapse `∂ₙ⁺(s, ρₙ) = sⁿ`** — for every exponent, the `s`-conjugation of the
relator cancels (`ZZ` abelian): the crux sends the boundary to `signPower (exponentSum (s · sⁿ · s⁻¹))`,
`exponentSumConjugation` fixes that exponent at `exponentSum sⁿ`, and `signPowerExponentSumRelator` returns
`sⁿ`.  The general-`n` Fox-derivative fixture (the `n = 3` case is the shipped
`conjugatedRelatorBoundaryIsRelatorOverGenZero`). -/
theorem powerConjugationCollapses (exponent : Nat) :
    conjugatedRelatorBoundaryAt exponent cyclicPowerConjugatorGen = cyclicPowerRelator exponent :=
  (reduceWordIsSignPowerOverGenZero (firstConjWordOverGenZero exponent)).trans
    ((congrArg signPower
        ((exponentSumReduceInvariant
              ([SignedLetter.pos 0] ++ cyclicPowerRelator exponent
                ++ invWord [SignedLetter.pos 0])).symm.trans
          (exponentSumConjugation [SignedLetter.pos 0] (cyclicPowerRelator exponent)))).trans
      (signPowerExponentSumRelator exponent))

/-- The first generator's boundary has exponent sum `exponentSum sⁿ` (the `s`-conjugator cancels). -/
theorem firstGenBoundaryExponent (exponent : Nat) :
    exponentSum (conjugatedRelatorBoundaryAt exponent cyclicPowerConjugatorGen)
      = exponentSum (cyclicPowerRelator exponent) :=
  exponentSumConjugation [SignedLetter.pos 0] (cyclicPowerRelator exponent)

/-- The second generator's boundary has exponent sum `−(exponentSum sⁿ)` (`s⁻ⁿ`, un-conjugated). -/
theorem secondGenBoundaryExponent (exponent : Nat) :
    exponentSum (conjugatedRelatorBoundaryAt exponent cyclicPowerRelatorInverseGen)
      = -(exponentSum (cyclicPowerRelator exponent)) :=
  (exponentSumConjugation [] (invWord (cyclicPowerRelator exponent))).trans
    (exponentSumInvWord (cyclicPowerRelator exponent))

/-- The first generator's boundary is over generator `0`. -/
theorem firstGenBoundaryOverGenZero (exponent : Nat) :
    AllLettersOverGenZero (conjugatedRelatorBoundaryAt exponent cyclicPowerConjugatorGen) :=
  allLettersReduceWord (firstConjWordOverGenZero exponent)

/-- The second generator's boundary is over generator `0`. -/
theorem secondGenBoundaryOverGenZero (exponent : Nat) :
    AllLettersOverGenZero (conjugatedRelatorBoundaryAt exponent cyclicPowerRelatorInverseGen) :=
  allLettersReduceWord
    (allLettersAppend (allLettersAppend AllLettersOverGenZero.nil
        (allLettersInvWord (allLettersSignPowerPos exponent)))
      (allLettersInvWord AllLettersOverGenZero.nil))

/-- ★★★ **`∂ₙ ζₙ = []` FOR ALL `n`** — the general rotation identity is in `ker ∂ₙ` for EVERY exponent, a
genuine theorem (not the shipped `n = 3` `rfl`).  The whole boundary is `reduceWord` of an over-gen-0 word,
so the crux sends it to `signPower (exponentSum …)`; the exponent telescopes
`exponentSum sⁿ + (−(exponentSum sⁿ) + 0) = 0` (`intAddZero` + `intAddRightNeg`), and `signPower 0 = []`.
The single genuine general theorem the round rests on — `ζₙ` is a candidate generator of `π₂⟨s | sⁿ⟩` for
every `n` (Lyndon), delivered off the single-generator `signPower` discipline. -/
theorem rotationBoundaryVanishesAt (exponent : Nat) :
    partialBoundaryAt exponent cyclicPowerRotationWitness = oneWord :=
  let relatorExponent : Int := exponentSum (cyclicPowerRelator exponent)
  let firstBoundary : List SignedLetter :=
    conjugatedRelatorBoundaryAt exponent cyclicPowerConjugatorGen
  let secondBoundary : List SignedLetter :=
    conjugatedRelatorBoundaryAt exponent cyclicPowerRelatorInverseGen
  let outerWord : List SignedLetter := firstBoundary ++ reduceWord (secondBoundary ++ oneWord)
  let outerOver : AllLettersOverGenZero outerWord :=
    allLettersAppend (firstGenBoundaryOverGenZero exponent)
      (allLettersReduceWord
        (allLettersAppend (secondGenBoundaryOverGenZero exponent) AllLettersOverGenZero.nil))
  let secondReducedExponent :
      exponentSum (reduceWord (secondBoundary ++ oneWord)) = -relatorExponent :=
    (exponentSumReduceInvariant (secondBoundary ++ oneWord)).trans
      ((exponentSumAppend secondBoundary oneWord).trans
        ((intAddZero (exponentSum secondBoundary)).trans (secondGenBoundaryExponent exponent)))
  let outerExponentZero : exponentSum outerWord = 0 :=
    (exponentSumAppend firstBoundary (reduceWord (secondBoundary ++ oneWord))).trans
      ((congrArg (fun summand => summand + exponentSum (reduceWord (secondBoundary ++ oneWord)))
          (firstGenBoundaryExponent exponent)).trans
        ((congrArg (fun summand => relatorExponent + summand) secondReducedExponent).trans
          (intAddRightNeg relatorExponent)))
  (reduceWordIsSignPowerOverGenZero outerOver).trans (congrArg signPower outerExponentZero)

/-! ## B3 — the proper-power certificate ∀ `n ≥ 2` + the NAMED general separating invariant (r8)

★ **The Lyndon hypothesis, generalized.**  For `n ≥ 2` the relator `sⁿ` is a proper power (base `s`,
primitive; exponent `n`), so by Lyndon's Identity Theorem `π₂⟨s | sⁿ⟩ ≠ 0`, cyclic on `ζₙ`.  This module
ships the certificate (`cyclicPowerRelatorProperPower`) — the general kernel-checked Lyndon hypothesis.

★ **The r8 node (STATED, not proved).**  The MECHANIZATION of `π₂⟨s | sⁿ⟩ ≠ 0` at general `n` needs the
`ZZ[ZZ/n]`-module separating invariant generalizing r2's `crossedModuleImage : E → ZZ[ZZ/3]` — a residue
enum `ZmodN` (in place of `ZmodThree`) and a value carrier `GroupRingZmodN` (in place of `GroupRingZmod3`)
with `ζₙ ↦ (s̄ − 1) ≠ 0` and Peiffer-invariance.  That is a DISTINCT clean carrier (the mod-`n` residue
ceiling appears where mod-3 was full-enum `rfl`), NOT attempted this round; named `generalInvariantResidualR8`
in the arc ledger.  The `n = 3` instance is the shipped r2 `rotationIdentityImageIsSeparating`. -/

/-- `sⁿ = (s)ⁿ` as a word power — the single generator is the base, the exponent is `n`. -/
theorem signPowerPosIsWordPower : ∀ exponent : Nat,
    signPowerPos exponent = wordPower [SignedLetter.pos 0] exponent
  | 0 => rfl
  | count + 1 =>
      congrArg (fun tail => SignedLetter.pos 0 :: tail) (signPowerPosIsWordPower count)

/-- A certificate that the general cyclic relator `sⁿ` is a proper power `base^exponent` with
`exponent ≥ 2` — the Lyndon hypothesis for `⟨s | sⁿ⟩` at general `n`. -/
structure CyclicPowerProperPowerCertificate where
  /-- The exponent `n`. -/
  exponent : Nat
  /-- The base word (`s`, primitive). -/
  base : List SignedLetter
  /-- The relator reconstructs as `base^exponent`. -/
  reconstructsAsPower : cyclicPowerRelator exponent = wordPower base exponent
  /-- The exponent is at least two (a genuine proper power). -/
  exponentAtLeastTwo : 2 ≤ exponent

/-- ★ **`sⁿ` is a proper power for every `n ≥ 2`** (base `[s]`, exponent `n`) — the general Lyndon
Identity Theorem hypothesis for `⟨s | sⁿ⟩`, kernel-checked.  This is what forces `π₂⟨s | sⁿ⟩ ≠ 0`
(Lyndon 1950); its MECHANIZATION is the r8 node.  The `n = 3` case is r1's
`cyclicThreeRelatorProperPower`. -/
def cyclicPowerRelatorProperPower (exponent : Nat) (isAtLeastTwo : 2 ≤ exponent) :
    CyclicPowerProperPowerCertificate :=
  { exponent := exponent
  , base := [SignedLetter.pos 0]
  , reconstructsAsPower := signPowerPosIsWordPower exponent
  , exponentAtLeastTwo := isAtLeastTwo }

/-! ## B4b — the H₂ cross-check star + the arc ledger -/

/-- The honest status of one rung of the r7 arc. -/
inductive CyclicPowerObligationStatus where
  /-- Shipped this round, zero-axiom. -/
  | shippedThisRound
  /-- The r8 named residual — the general `ZZ[ZZ/n]` separating invariant (distinct clean carrier). -/
  | generalInvariantResidualR8
  /-- The r9 named residual — two-generator asphericity `π₂⟨a, b | [a, b]⟩ = 0` (distinct clean carrier). -/
  | asphericityResidualR9
  /-- The inherited r6 residual — the Hopf-shadow coker iso (Smith-cert / `Quot`-walled). -/
  | inheritedHopfResidual

/-- The abelianized (trivial-coefficient) `H₂` of a presentation's 2-complex. -/
inductive AbelianizedHomologyShadow where
  /-- `H₂ = 0`. -/
  | vanishes
  /-- `H₂ = ZZ` (free of rank one). -/
  | freeRankOne

/-- The `π₂` (module of identities among relations) status of a presentation. -/
inductive PiTwoStatus where
  /-- `π₂ ≠ 0`. -/
  | nontrivial
  /-- `π₂ = 0` (aspherical). -/
  | trivial

/-- One row of the H₂ cross-check: a presentation's abelianized `H₂` shadow, its `π₂`, and where the
general-scope mechanization stands. -/
structure H2CrossCheckRow where
  /-- The abelianized `H₂` (trivial coefficients). -/
  abelianizedH2 : AbelianizedHomologyShadow
  /-- The `π₂` (identities among relations). -/
  piTwo : PiTwoStatus
  /-- Where the general-scope mechanization of this row's `π₂` claim stands. -/
  establishment : CyclicPowerObligationStatus

/-- ★ **The H₂ cross-check star** — `π₂` and abelianized `H₂` are INDEPENDENT invariants, either vanishing
while the other does not, in BOTH directions.  The two complementary rows. -/
structure H2CrossCheckStar where
  /-- `⟨s | sⁿ⟩` (proper power, `n ≥ 2`): abelianized `H₂ = 0` but `π₂ ≠ 0`. -/
  cyclicProperPowerRow : H2CrossCheckRow
  /-- `⟨a, b | [a, b]⟩` (aspherical): abelianized `H₂ = ZZ` but `π₂ = 0`. -/
  commutatorAsphericalRow : H2CrossCheckRow

/-- ★★ **The cross-check star, filled.**  Top row `⟨s | sⁿ⟩`: `H₂ = 0` (r-shipped `n = 3`
`cyclicThreeDegreeTwoHomologyIsZero`), `π₂ ≠ 0` (mechanized at general `n` by the r8 invariant, cited
Lyndon).  Bottom row `⟨a, b | [a, b]⟩`: `H₂ = ZZ = H₂(T²)`, `π₂ = 0` (the r9 asphericity node, cited
Lyndon).  The tower only ever saw the top row; the commutator carrier (this file) delivers the bottom. -/
def h2CrossCheckStar : H2CrossCheckStar :=
  { cyclicProperPowerRow :=
      { abelianizedH2 := AbelianizedHomologyShadow.vanishes
      , piTwo := PiTwoStatus.nontrivial
      , establishment := CyclicPowerObligationStatus.generalInvariantResidualR8 }
  , commutatorAsphericalRow :=
      { abelianizedH2 := AbelianizedHomologyShadow.freeRankOne
      , piTwo := PiTwoStatus.trivial
      , establishment := CyclicPowerObligationStatus.asphericityResidualR9 } }

/-- The six-rung ledger of the r7 arc. -/
structure CyclicPowerArcLedger where
  /-- `∂ₙ ζₙ = []` ∀ `n` (`rotationBoundaryVanishesAt`). -/
  generalBoundaryVanishing : CyclicPowerObligationStatus
  /-- `sⁿ` proper power ∀ `n ≥ 2` (`cyclicPowerRelatorProperPower`). -/
  properPowerCertificate : CyclicPowerObligationStatus
  /-- The general `ZZ[ZZ/n]` separating invariant ⟹ general `π₂ ≠ 0` mechanized. -/
  generalSeparatingInvariant : CyclicPowerObligationStatus
  /-- The two-generator carrier exercised (`commutatorBoundaryIsReduced`,
  `commutatorSelfInverseVanishes`). -/
  twoGeneratorCarrier : CyclicPowerObligationStatus
  /-- `π₂⟨a, b | [a, b]⟩ = 0` via the `ZZ[ZZ²]` Fox–Koszul argument. -/
  twoGeneratorAsphericity : CyclicPowerObligationStatus
  /-- The inherited Hopf-shadow coker iso (r6 named node). -/
  inheritedHopfCoker : CyclicPowerObligationStatus

/-- ★ **The r7 arc ledger.**  The general boundary vanishing, the proper-power certificate, and the
two-generator carrier are SHIPPED zero-axiom; the general `ZZ[ZZ/n]` separating invariant (r8) and the
two-generator asphericity (r9) are named residuals (distinct clean carriers); the Hopf-shadow coker is the
inherited r6 wall.  The honest r7 close: the `⟨s | sⁿ⟩` boundary + kernel witness are general theorems, the
Lyndon hypothesis is certified ∀ `n ≥ 2`, and the complementary two-generator direction is opened with the
H₂ cross-check star recorded. -/
def cyclicPowerArcLedger : CyclicPowerArcLedger :=
  { generalBoundaryVanishing := CyclicPowerObligationStatus.shippedThisRound
  , properPowerCertificate := CyclicPowerObligationStatus.shippedThisRound
  , generalSeparatingInvariant := CyclicPowerObligationStatus.generalInvariantResidualR8
  , twoGeneratorCarrier := CyclicPowerObligationStatus.shippedThisRound
  , twoGeneratorAsphericity := CyclicPowerObligationStatus.asphericityResidualR9
  , inheritedHopfCoker := CyclicPowerObligationStatus.inheritedHopfResidual }

/-- ★ **The #2199 r7 general-cyclic + two-generator marker.**  Shipped zero-axiom over the closed
`⟨s | s³⟩` instance:

  * **B1 (parameterized boundary)** — `cyclicPowerRelator` / `conjugatedRelatorBoundaryAt` /
    `partialBoundaryAt` generalize r1's `n = 3` hardcode; the `n = 3` specialization is defeq to the shipped
    boundary (`cyclicPowerBoundaryThreeMatchesShipped`).
  * **B2 (the general theorem)** — ★★★ `rotationBoundaryVanishesAt`: `∂ₙ ζₙ = []` for EVERY `n`, a genuine
    theorem off the shipped `signPower` / `exponentSum` kit (not the `n = 3` `rfl`), with the conjugation
    collapse `∂ₙ⁺(s, ρₙ) = sⁿ` (`powerConjugationCollapses`) as the Fox-derivative fixture.
  * **B3 (Lyndon hypothesis)** — `cyclicPowerRelatorProperPower`: `sⁿ` is a proper power ∀ `n ≥ 2`; the
    MECHANIZATION of `π₂ ≠ 0` at general `n` is the named `ZZ[ZZ/n]` invariant (r8).
  * **B4 (two-generator opening + cross-check)** — the multi-generator carrier exercised for the first time
    (`commutatorBoundaryIsReduced`, `commutatorSelfInverseVanishes`); the H₂ cross-check star recorded
    (`h2CrossCheckStar`: `H₂(ZZ/n) = 0` vs `π₂ ≠ 0` against `H₂(ZZ²) = ZZ` vs `π₂ = 0` — INDEPENDENT in
    both directions); the two-generator asphericity `π₂⟨a, b | [a, b]⟩ = 0` named (r9).

The honest ceilings: `π₂` is PRESENTED not quotiented (Peiffer as data, kernel as predicate — no `Quot`);
the general `π₂ ≅ ker` iso reopens as the r8 injectivity node; the Hopf-shadow coker stays the inherited r6
wall.  Read the meaning from THIS docstring and the top-of-file arc ledger (the honest-record convention). -/
def crossedModuleCyclicPowerArcIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
