import FX1Poly.Polygraph.Homology.FreeGroupReducedWord

/-! # FX1Poly/Polygraph/Homology/CrossedModuleCyclicThree — the free crossed module of the cyclic-order-
    three presentation `⟨s | s³⟩`, its Peiffer congruence, the ROTATION identity witness in `ker ∂`, and
    the honest `pi_2 ≠ 0` ledger (WP-2GROUP r1 bricks B2..B5, #2199)

The DECIDED cyclic-order-three walker `⟨s | sss ⟹ id⟩` presents `ZZ/3`; the shipped abelianized chain
complex (`Homology/CyclicThreeChainComplex`) reads `H1 = ZZ/3` and `H2 = 0`.  But `H2 = 0` is the
TRIVIAL-COEFFICIENT shadow — it says nothing about `pi_2` (the module of identities among relations),
which for a one-relator group is governed by Lyndon's Identity Theorem, NOT by the abelianized `H2`.
This module opens the UN-abelianized layer: the free crossed `F`-module on the single relator, its
boundary `∂` valued in the FREE GROUP `F(s)` (not in `ZZ`), the Peiffer congruence, and the genuine
identity `ζ ∈ ker ∂`.

## The data (hand-worked, Whitehead's free crossed module)

`F = F(s)` free on one generator; `R = {ρ}`, `ρ = sss`; `G = F/⟪ρ⟫ = ⟨s | s³⟩ = ZZ/3`.  The pre-crossed
carrier `E` is the free group on the conjugated relators `(w, ρ)`; the boundary is `∂(w, ρ) = w ρ w^-1`
(a REDUCED WORD in `F(s)`, via `Homology/FreeGroupReducedWord`).  The Peiffer relation `a b a^-1 ~
^{∂a}b` (with the `F`-action `^f(w, r) = (f·w, r)`) cuts `E` down to the crossed module `C`.

## ★ The rotation identity (Lyndon 1950)

Because `ρ = s³ = (s)³` is a PROPER POWER (exponent `3 ≥ 2`), `s` commutes with `ρ`, so
`ζ = (s, ρ)·(1, ρ)^-1` has `∂ζ = s·s³·s^-1·(s³)^-1 = 1` — `ζ ∈ ker ∂`, the generator of `pi_2`.
`rotationIdentityBoundaryVanishes` proves `∂ζ = []` by `rfl` on the reduced-word computation.

**Lyndon's Identity Theorem** (Lyndon 1950, *Cohomology theory of groups with a single defining
relation*, Ann. Math. 52): for `⟨X | r⟩`, if `r` is NOT a proper power then `pi_2 = 0` (aspherical); if
`r = w^m` with `m ≥ 2` then `pi_2 ≠ 0`, cyclic on the rotation identity `ζ = ^w(r)·r^-1`.  For
`⟨s | s³⟩`: `m = 3 ≥ 2`, so `pi_2 ≠ 0`.  This module STATES + cites the theorem and PROVES its hypothesis
(`s³` is a proper power) and the kernel-membership of `ζ`; it does NOT mechanize non-triviality (see B4).

## ★ The abelianized-shadow correspondence (Brown–Huebschmann 1982)

The shipped `cyclicThreeChainComplex` is the trivial-coefficient tensor `ZZ ⊗_{ZZ[G]}` of the
Reidemeister–Fox–Lyndon partial free resolution.  Under it `ζ` DIES: `exponentSum ∂ζ = 0`
(`rotationIdentityAbelianShadowVanishes`), which is exactly why the shipped `H2(cyclic Z/3) = 0`
(`cyclicThreeDegreeTwoHomologyIsZero`).  So `pi_2` carries STRICTLY MORE than the abelianized `H2`; the
degree-2 boundary `d2 = [[-3]]` is the augmented Fox derivative `ε(1 + s + s²) = 3`, recovered here as
`exponentSum ∂(1, ρ) = 3` (`relatorAbelianShadowIsThree`).  This is the Brown–Huebschmann Proposition
(Brown–Huebschmann 1982, *Identities among relations*, LMS Lecture Notes 48) that r1 STATES + cites; the
mechanized module-iso is a named residual, not claimed here.

## Zero-axiom design decisions

  * `ConjugatedRelator`, `ProperPowerCertificate`, `CrossedModuleNonTrivialityLedger` are plain records;
    `PeifferEquiv` is a `Prop`-valued inductive relation (refl/symm/trans/append-congruence + the single
    Peiffer move) — NO `Quot`, NO `Quot.sound`; statements are up-to-`PeifferEquiv`, never a quotient.
  * `partialBoundary` / `conjugatedRelatorBoundary` dispatch on `isPositive : Bool` through a full-enum
    match; the witness `∂ζ = []` and the concrete Peiffer coherence close by `rfl` on the reduced-word
    computation (all generators are `0`, so `Nat.beq 0 0` reduces definitionally).
  * `exponentSum` lands in `Int`; the shadow probes close by `rfl` on `Int` literal reductions.

`Init`-only (over `Homology/FreeGroupReducedWord`), structural, zero axioms.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicThree.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## B2 — the pre-crossed carrier and the boundary into the free group -/

/-- A conjugated relator `±(w, r)`: a generator of the pre-crossed free group `E`.  `conjugator` is the
element `w ∈ F` (kept as a reduced word), `relationIndex` selects the relator `r`, and `isPositive` is
its sign in `E`. -/
structure ConjugatedRelator where
  /-- The conjugating element `w ∈ F`, a reduced word. -/
  conjugator : List SignedLetter
  /-- Which relator this conjugates. -/
  relationIndex : Nat
  /-- The sign of this generator in the free group `E`. -/
  isPositive : Bool

/-- An element of the pre-crossed carrier `E`: a formal word of conjugated relators. -/
abbrev PreCrossedElement := List ConjugatedRelator

/-- The relator words of the presentation: relator `0` is `ρ = sss`; there are no others. -/
def relatorWord : Nat → List SignedLetter
  | 0 => [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0]
  | _ + 1 => []

/-- The formal inverse of a conjugated relator in `E` — flips the sign, keeps the conjugator and
relator. -/
def invGen (gen : ConjugatedRelator) : ConjugatedRelator :=
  { gen with isPositive := Bool.not gen.isPositive }

/-- **The boundary of a single conjugated relator**, valued in the FREE GROUP `F(s)`: a positive
`(w, r)` maps to the reduced word `w · ρ_r · w^-1`; a negative one to its inverse `w · ρ_r^-1 · w^-1`. -/
def conjugatedRelatorBoundary (gen : ConjugatedRelator) : List SignedLetter :=
  match gen.isPositive with
  | true =>
      reduceWord (gen.conjugator ++ relatorWord gen.relationIndex ++ invWord gen.conjugator)
  | false =>
      reduceWord (gen.conjugator ++ invWord (relatorWord gen.relationIndex) ++ invWord gen.conjugator)

/-- **The crossed-module boundary `∂ : E → F`**, the reduced product of the per-generator boundaries. -/
def partialBoundary : PreCrossedElement → List SignedLetter
  | [] => oneWord
  | gen :: rest => mulWord (conjugatedRelatorBoundary gen) (partialBoundary rest)

/-- ★ **`∂` lands in reduced words** — the crossed-module boundary genuinely returns an element of the
free group `F(s)` (a reduced word), because every step is a `mulWord = reduceWord (·)`. -/
theorem partialBoundaryIsReduced : ∀ element : PreCrossedElement,
    isReducedWord (partialBoundary element) = true
  | [] => rfl
  | gen :: rest => reduceWordProducesReduced (conjugatedRelatorBoundary gen ++ partialBoundary rest)

/-! ### The Peiffer congruence (a Prop-valued inductive relation; NO `Quot`) -/

/-- The `F`-action result `^{∂a}b` of the Peiffer move: keep `b`'s relator and sign, but pre-multiply
its conjugator by the boundary of `a`.  With the action `^f(w, r) = (f·w, r)` and `f = ∂a` this is
exactly the crossed-module Peiffer target. -/
def peifferConjugate (firstGen secondGen : ConjugatedRelator) : ConjugatedRelator :=
  { secondGen with
    conjugator := reduceWord (conjugatedRelatorBoundary firstGen ++ secondGen.conjugator) }

/-- ★ **The Peiffer congruence** on the pre-crossed carrier `E`, an inductively-generated equivalence:
reflexivity, symmetry, transitivity, append-congruence, and the single generating **Peiffer move**
`a b a^-1 ~ ^{∂a}b`.  Quotienting `E` by this relation yields the crossed module `C`; it is a
`Prop`-valued inductive — statements are proved up-to-`PeifferEquiv`, NEVER via `Quot.sound`. -/
inductive PeifferEquiv : PreCrossedElement → PreCrossedElement → Prop where
  /-- Reflexivity. -/
  | refl (element : PreCrossedElement) : PeifferEquiv element element
  /-- Symmetry. -/
  | symm {left right : PreCrossedElement} : PeifferEquiv left right → PeifferEquiv right left
  /-- Transitivity. -/
  | trans {left middle right : PreCrossedElement} :
      PeifferEquiv left middle → PeifferEquiv middle right → PeifferEquiv left right
  /-- Append-congruence: the relation is a congruence for the group operation of `E`. -/
  | congrAppend {leftA leftB rightA rightB : PreCrossedElement} :
      PeifferEquiv leftA rightA → PeifferEquiv leftB rightB →
      PeifferEquiv (leftA ++ leftB) (rightA ++ rightB)
  /-- ★ The generating Peiffer move `a b a^-1 ~ ^{∂a}b`. -/
  | peifferMove (firstGen secondGen : ConjugatedRelator) :
      PeifferEquiv [firstGen, secondGen, invGen firstGen] [peifferConjugate firstGen secondGen]

/-! ### The concrete Peiffer coherence truth probe (hand-diff on cyclic-3) -/

/-- The first probe generator `a = (s, ρ)`. -/
def peifferProbeFirst : ConjugatedRelator := ⟨[SignedLetter.pos 0], 0, true⟩

/-- The second probe generator `b = (s, ρ)`. -/
def peifferProbeSecond : ConjugatedRelator := ⟨[SignedLetter.pos 0], 0, true⟩

/-- ★ **The Peiffer move preserves the boundary — CONCRETE hand-diff.**  Both `∂(a b a^-1)` and
`∂(^{∂a}b)` reduce to the SAME free-group word `s³`, so `∂` is invariant under the Peiffer generator on
this instance: this is the coherence that lets `∂` descend to the crossed module `C = E/PeifferEquiv`.
The `^{∂a}` action genuinely moves `b`'s conjugator (`s ↦ s⁴`), yet the boundary is unchanged.  `rfl`. -/
theorem peifferMovePreservesBoundary :
    partialBoundary [peifferProbeFirst, peifferProbeSecond, invGen peifferProbeFirst]
      = partialBoundary [peifferConjugate peifferProbeFirst peifferProbeSecond] := rfl

/-- The shared boundary value of the Peiffer probe — both sides are `s³ = [pos 0, pos 0, pos 0]`. -/
theorem peifferMoveProbeBoundaryValue :
    partialBoundary [peifferProbeFirst, peifferProbeSecond, invGen peifferProbeFirst]
      = [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0] := rfl

/-! ## B3 — the rotation identity `ζ` and its kernel membership -/

/-- ★ **The rotation identity `ζ = (s, ρ)·(1, ρ)^-1`** as a pre-crossed element.  The proper-power
witness of `pi_2` for `⟨s | s³⟩`: the first generator conjugates `ρ` by `s`, the second is the inverse
of the un-conjugated relator. -/
def rotationIdentityWitness : PreCrossedElement :=
  [⟨[SignedLetter.pos 0], 0, true⟩, invGen ⟨[], 0, true⟩]

/-- ★★ **`∂ζ = 1`: the rotation identity is in `ker ∂`.**  The free-group computation
`(s·s³·s^-1)·(s³)^-1 = s³·s^-3 = 1` reduces to the empty word.  So `ζ` is a genuine identity among the
relations — a candidate generator of `pi_2(⟨s | s³⟩)`.  `rfl` on the reduced-word evaluation. -/
theorem rotationIdentityBoundaryVanishes : partialBoundary rotationIdentityWitness = oneWord := rfl

/-! ## B4 — the non-triviality invariant: the honest `pi_2 ≠ 0` ledger

Kernel-membership `∂ζ = 1` alone does NOT prove `ζ` is a nontrivial element of `pi_2` — it could be
Peiffer-trivial.  Non-triviality needs a SEPARATING INVARIANT that distinguishes `ζ` from the
Peiffer-trivial word.

★ **The trivial-coefficient shadow CANNOT separate `ζ`** (the load-bearing honesty).  Under the shipped
abelianization `ζ ↦ 0` (`rotationIdentityAbelianShadowVanishes` below), which is exactly why the shipped
`H2(cyclic Z/3) = 0`.  The correct separating invariant is the `ZZ[G]`-MODULE (group-ring)
abelianization `E → ZZ[G]^R`, `(w, r, sign) ↦ ±(image of w in G)·e_r`; for `G = ZZ/3`,
`ZZ[G] ≅ ZZ³`, "image of `w`" is the exponent-sum mod 3, and `ζ ↦ (s̄ − 1)·e_ρ = (−1, 1, 0) ≠ 0`, while
the Peiffer move maps to `0` (because `r ↦ 1` in `G`).  That invariant is PROVABLE (no new axioms, no
free-group associativity) but is a DISTINCT clean carrier — the named r2 node below. -/

/-- The word power `base^count` — `base` concatenated `count` times. -/
def wordPower (base : List SignedLetter) : Nat → List SignedLetter
  | 0 => []
  | count + 1 => base ++ wordPower base count

/-- A certificate that a relator word is a PROPER POWER `base^exponent` with `exponent ≥ 2` — the
Lyndon hypothesis that forces `pi_2 ≠ 0`. -/
structure ProperPowerCertificate where
  /-- The base word. -/
  base : List SignedLetter
  /-- The exponent. -/
  exponent : Nat
  /-- The relator reconstructs as `base^exponent`. -/
  reconstructsAsPower : relatorWord 0 = wordPower base exponent
  /-- The exponent is at least two (a genuine proper power). -/
  exponentAtLeastTwo : 2 ≤ exponent

/-- ★ **`ρ = s³` is a proper power** (`base = [s]`, `exponent = 3 ≥ 2`) — the Lyndon Identity Theorem
hypothesis for `⟨s | s³⟩`, kernel-checked.  This is what forces `pi_2 ≠ 0` (Lyndon 1950). -/
def cyclicThreeRelatorProperPower : ProperPowerCertificate :=
  { base := [SignedLetter.pos 0]
  , exponent := 3
  , reconstructsAsPower := rfl
  , exponentAtLeastTwo := Nat.le.step Nat.le.refl }

/-- The exponent-sum abelianization `F(s) → ZZ` (the trivial-coefficient shadow): `pos ↦ +1`,
`neg ↦ −1`.  This is the map under which the un-abelianized `∂` becomes the shipped integer `d2`. -/
def exponentSum : List SignedLetter → Int
  | [] => 0
  | SignedLetter.pos _ :: rest => 1 + exponentSum rest
  | SignedLetter.neg _ :: rest => -1 + exponentSum rest

/-- ★ **`∂(1, ρ)` abelianizes to `3`** — the augmented Fox derivative `ε(1 + s + s²) = 3` that the
shipped `d2 = [[-3]]` carries (target − source `= 0 − 3`).  The un-abelianized boundary of the
un-conjugated relator is `s³`; its exponent sum is `3`. -/
theorem relatorAbelianShadowIsThree :
    exponentSum (conjugatedRelatorBoundary ⟨[], 0, true⟩) = 3 := rfl

/-- ★★ **`ζ` DIES in the trivial-coefficient shadow** — `exponentSum ∂ζ = 0`.  This is precisely why
the shipped `H2(cyclic Z/3) = 0` sees nothing: the trivial-coefficient complex provably CANNOT separate
`ζ` from the Peiffer-trivial word.  Separating `ζ` needs the `ZZ[G]`-module invariant (r2). -/
theorem rotationIdentityAbelianShadowVanishes :
    exponentSum (partialBoundary rotationIdentityWitness) = 0 := rfl

/-- The status of one `pi_2 ≠ 0` obligation, honestly classified. -/
inductive NonTrivialityObligationStatus where
  /-- Shipped this round, zero-axiom. -/
  | shippedThisRound
  /-- The named r2 residual — provable, a distinct clean carrier, not attempted this round. -/
  | separatingInvariantResidual

/-- The honest `pi_2(⟨s | s³⟩) ≠ 0` ledger: what r1 ships and what the r2 separating invariant owes. -/
structure CrossedModuleNonTrivialityLedger where
  /-- `ζ ∈ ker ∂` (`rotationIdentityBoundaryVanishes`). -/
  kernelWitnessStatus : NonTrivialityObligationStatus
  /-- `ρ = s³` is a proper power (`cyclicThreeRelatorProperPower`). -/
  properPowerStatus : NonTrivialityObligationStatus
  /-- The `ZZ[G] ≅ ZZ³` separating invariant `ζ ↦ (−1, 1, 0) ≠ 0` with Peiffer-invariance. -/
  separatingInvariantStatus : NonTrivialityObligationStatus

/-- ★ **The assembled `pi_2 ≠ 0` ledger.**  Kernel-witness SHIPPED (`rotationIdentityBoundaryVanishes`);
proper-power hypothesis SHIPPED (`cyclicThreeRelatorProperPower`); the `ZZ[G]`-module SEPARATING
INVARIANT is the named r2 residual (its full design is pinned in the B4 docstring — provable, no new
axioms).  The honest r1 stance: `ζ` is exhibited IN the kernel, `pi_2 ≠ 0` is CITED (Lyndon) with its
hypothesis proved, but non-triviality is NOT claimed without the separating invariant. -/
def cyclicThreeNonTrivialityLedger : CrossedModuleNonTrivialityLedger :=
  { kernelWitnessStatus := NonTrivialityObligationStatus.shippedThisRound
  , properPowerStatus := NonTrivialityObligationStatus.shippedThisRound
  , separatingInvariantStatus := NonTrivialityObligationStatus.separatingInvariantResidual }

/-! ## B5 — the bridge to the shipped abelianized complex, and the #2199 ledger

### The correspondence (Brown–Huebschmann 1982), NAMED to the shipped walker read-offs

The shipped `Homology/CyclicThreeChainComplex` reads, kernel-checked:

  * `cyclicThreeDegreeOneHomologyIsZmodThree` — `H1(cyclic Z/3) = ZZ/3` (free rank 0, factor `[3]`);
  * `cyclicThreeDegreeTwoHomologyIsZero` — `H2(cyclic Z/3) = 0`.

Those are the TRIVIAL-COEFFICIENT `ZZ ⊗_{ZZ[G]}` homology of the Reidemeister–Fox–Lyndon resolution.
This module supplies the UN-abelianized layer above `d2`:

  * the shipped `d2 = [[-3]]` is the augmented Fox derivative `ε(1 + s + s²) = 3`, recovered here as
    `relatorAbelianShadowIsThree` (`exponentSum ∂(1, ρ) = 3`);
  * `H2 = 0` is the trivial-coefficient shadow: `ζ` dies (`rotationIdentityAbelianShadowVanishes`,
    `exponentSum ∂ζ = 0`), so `pi_2` carries STRICTLY MORE than the abelianized `H2`.

**No isomorphism is claimed.**  The Brown–Huebschmann module-level correspondence `pi_2 ≅ H2(G; ZZ[G])`
is the mechanized r2 node; r1 states + cites it and ships the two numeric down-payments above.

### What the H2-SQUIER-NOGO machine inherits

`Homology/SquierNoGoInterface` wants a NON-TRUNCATED / infinite-basis substrate to state
`H_3`-non-finiteness (its `carrierDegreeThreeChainIsAlwaysFinite` wall).  This module contributes the
FIRST non-`ZZ`-valued boundary in the lane: `∂` lands in the free group `F(s)` via
`Homology/FreeGroupReducedWord`, not in `IntMatrix`.  The reduced-word kit + the Peiffer congruence are
the substrate a genuine `pi_n` / identities-among-relations tower can grow on — the named successor to
the finite-`ZZ`-module carrier.

### The #2199 state — what r1 opened, what remains

  * **B1 — the free-group reduced-word kit** (`Homology/FreeGroupReducedWord`): SHIPPED, zero-axiom.
  * **B2 — the pre-crossed carrier + Peiffer congruence**: SHIPPED.  `ConjugatedRelator`,
    `partialBoundary` (into `F(s)`, `partialBoundaryIsReduced`), `PeifferEquiv` (Prop inductive, no
    `Quot`), and the CONCRETE Peiffer coherence hand-diff (`peifferMovePreservesBoundary`, both sides
    `s³`).
  * **B3 — the boundary + the cyclic-3 kernel witness**: SHIPPED.  `rotationIdentityWitness = ζ`,
    ★★ `rotationIdentityBoundaryVanishes` (`∂ζ = []`, `ζ ∈ ker ∂`), with the Lyndon dichotomy STATED +
    cited and its hypothesis proved (`cyclicThreeRelatorProperPower`).
  * **B4 — the non-triviality invariant**: the HONEST named r2 node.  Kernel-witness + proper-power
    SHIPPED; the `ZZ[G] ≅ ZZ³` separating invariant (`ζ ↦ (−1, 1, 0) ≠ 0`, Peiffer-invariant) is the
    named residual, full design pinned.  Non-triviality NOT claimed without it.
  * **B5 — the bridge + ledger**: SHIPPED.  The abelianized-shadow correspondence named to the shipped
    `cyclicThreeDegree{One,Two}Homology…`, the two numeric down-payments, the Squier inheritance note.

### The named residuals (multi-round; NEVER papered)

  * **R1 — free-group associativity + inverse laws** (the cancellation-confluence diamond,
    `Homology/FreeGroupReducedWord` DEFERRED): `mulWord` associativity and `mulWord a (invWord a) = []`.
    Needed for the GENERAL `∂`-descent `PeifferEquiv x y → partialBoundary x = partialBoundary y` (r1
    ships it only CONCRETELY, `peifferMovePreservesBoundary`).
  * **R2 — the `ZZ[G] ≅ ZZ³` separating invariant** (`CrossedModuleIdentityInvariant`): exponent-sum-mod-3
    image-in-`G`, module abelianization, Peiffer-invariance, `ζ ↦ (−1, 1, 0) ≠ 0` ⟹ `pi_2 ≠ 0`
    MECHANIZED (Lyndon promoted from cited to proved).
  * **R3 — the Brown–Huebschmann module iso** `pi_2 ≅ H2(G; ZZ[G])` connecting this layer to the shipped
    abelianized `H2`.

Citations: Lyndon 1950 (Identity Theorem, Ann. Math. 52); Whitehead 1949 (free crossed modules);
Brown–Huebschmann 1982 (Identities among relations, LMS LN 48); Brown, *Cohomology of Groups* (the
periodic `ZZ/3` resolution the shipped complex tensors). -/

/-- ★ **The #2199 crossed-module footing ledger marker.**  What r1 opened, zero-axiom: the free-group
reduced-word kit (B1), the pre-crossed carrier + Peiffer congruence with the concrete coherence hand-diff
(B2), ★★ the rotation identity `ζ ∈ ker ∂` with Lyndon's dichotomy stated + its proper-power hypothesis
proved (B3), the honest `pi_2 ≠ 0` ledger with the `ZZ[G]` separating invariant named as the r2 node
(B4), and the abelianized-shadow bridge to the shipped `H1 = ZZ/3` / `H2 = 0` (B5).  Read the meaning
from THIS docstring (the honest-record convention). -/
def crossedModuleCyclicThreeFootingIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
