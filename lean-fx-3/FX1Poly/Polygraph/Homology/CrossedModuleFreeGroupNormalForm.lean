import FX1Poly.Polygraph.Homology.CrossedModuleRelationModule

/-! # FX1Poly/Polygraph/Homology/CrossedModuleFreeGroupNormalForm — the group-enrichment of the
    pre-crossed carrier `E`, the residue-keyed normal-form kit, and the honest injectivity/iso
    adjudication for the free crossed module of `⟨s | s³⟩` (WP-2GROUP r4, #2199)

r3 (`Homology/CrossedModuleRelationModule`) shipped the SURJECTION `identities ↠ ker(N)` and NAMED the
injectivity half `relationModuleInjectivityObligation` (`image x = 0 ⟹ PeifferEquiv x []`) as the
Brown–Huebschmann structure-theorem residual.  r4 adjudicates that named obligation at the ENCODING
level — and the verdict is that it is **not provable as stated against the shipped `PeifferEquiv`**.

## The truth-probe verdict (B1, the crux)

`PreCrossedElement = List ConjugatedRelator` with `++` is the free **MONOID** on `ConjugatedRelator`;
`invGen` is a bare `Bool`-flip, not a group inverse.  The shipped `PeifferEquiv` (r1) has exactly one
generating move, `peifferMove : [a, b, a⁻¹] ~ [^{∂a}b]`, which is strictly 3-letters → 1-letter — it
cannot even ENGAGE a two-letter identity.  So the two-letter word `[genE0, invGen genE0]` is a genuine
identity (`crossedModuleImage = 0`, machine-checked in `moralCounterexampleImageIsZero`) that no
`PeifferEquiv` constructor can reduce to `[]`.  The r3 docstring's "PeifferEquiv is a sub-congruence"
sharpens to: **the shipped relation is the wrong (too-fine) relation; the intended object (r1's own
design docstring calls `E` "the free GROUP on the conjugated relators") is a group, and the shipped
congruence presents (free monoid)/(Peiffer move), which is not a group.**  Refuting the obligation by a
homomorphism invariant is provably impossible — `crossedModuleImage` is the finest peifferMove-respecting
invariant and it sends `[genE0, invGen genE0] ↦ 0 = image []`, so `image = 0` is consistent with (but
does not entail) PeifferEquiv-triviality.  Hence `relationModuleInjectivityObligation` (r3, kept
byte-intact) is NOT proved here; it is retargeted at the group-enriched relation below.

## The additive fix — the group-enrichment congruence

`FreeCrossedModuleEquiv` re-closes over `PeifferEquiv` and ADDS the two free-group cancellations
(`consInvCancel : [g, invGen g] ~ []`, `invConsCancel : [invGen g, g] ~ []`) that make `E` a group.
`PeifferEquiv` is UNTOUCHED (byte-intact, zero external dependents outside the three crossed-module
files).  Against the enriched relation:

  * soundness EXTENDS for free — `crossedModuleImageRespectsFreeCrossed` (the two new ctors preserve
    the image by `groupRingAddRightNeg`/`groupRingAddLeftNeg` + `conjugatedRelatorImageInvGen`);
  * r2's non-triviality STRENGTHENS — `rotationIdentityNotFreeCrossedTrivial` (a coarser relation still
    cannot relate `ζ` to `[]`, because `image ζ = (−1, 1, 0) ≠ 0`);
  * the two clean self-attacks `ζ ++ ζ⁻¹` and `(s·ζ) ++ (s·ζ)⁻¹` REDUCE to `[]` by pure
    double-cancellation (`freeCrossedSandwichCancel`) — the enrichment does what `PeifferEquiv` could not.

## r4 scope (honest)

Shipped: the enrichment, its soundness, the strengthened non-triviality, the two self-attacks, the
residue-keyed sort/measure normal-form kit, and the retargeted injectivity/iso ledger.  DEFERRED to r5
(the R1-hungry structure theorem `freeCrossedModuleNormalFormResidual`): the GENERAL
`FreeCrossedModuleEquiv x (realize (image x))` — the conjugator normalization `⟨w, 0, ·⟩ ~ genE_{residue w}`
and the twisted swap's `s^{k+3} → s^k` strip need r1's residual R1 (`reduceWord` associativity +
`mulWord a (invWord a) = []`), which is NOT shipped.  r4 keeps its machine-checked derivations to
LITERAL-generator cancellations, where every `∂genE_j = s³` is concrete.

## Zero-axiom design decisions

  * `FreeCrossedModuleEquiv` is a `Prop`-valued inductive (embed-Peiffer + re-closed
    refl/symm/trans/congrAppend + the two cancellations) — NO `Quot`, NO `Quot.sound`.
  * Every match on `FreeCrossedModuleEquiv` / `ZmodThree` / `Bool` is FULLY enumerated — no `_ =>`
    wildcard, so no match-compiler propext leak.
  * The residue key comparator `zmodThreeLe` is a full-enum 9-arm `Bool` table (never `Nat.decLt`
    via propext, never an `Int` remainder); the sort recurses structurally (never `WellFounded.fix`).
  * All `Int` arithmetic goes through the shipped propext-clean kit (`intAddRightNeg`/`intAddLeftNeg`),
    never Init's propext-dirty forms; group-ring equalities go through `groupRingEq` (single-field
    `congrArg`), never `mk.injEq`.

`Init`-only (over `Homology/CrossedModuleRelationModule`), structural, zero axioms.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupNormalForm.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the truth-probe: the shipped `PeifferEquiv` cannot reduce a two-letter identity

The concrete two-letter identity `[genE0, invGen genE0]` (`e₀ · e₀⁻¹`) has `crossedModuleImage = 0`, so
it satisfies the hypothesis of `relationModuleInjectivityObligation`; yet the shipped `PeifferEquiv`
provides no reducing move (its only generator `peifferMove` needs a 3-letter `[a, b, a⁻¹]` pattern).
The two positive facts below are machine-checked; the negative fact (no `PeifferEquiv` derivation) is the
documented verdict of the recon (no peifferMove-respecting invariant separates it from `[]`). -/

/-- ★ **Truth-probe (machine-checked half 1).**  The two-letter identity `[genE0, invGen genE0]` images
to `0`, so it satisfies the hypothesis of the r3 injectivity obligation. -/
theorem moralCounterexampleImageIsZero :
    crossedModuleImage [genE0, invGen genE0] = groupRingZero := rfl

/-- ★ **Truth-probe (machine-checked half 2).**  The same two-letter identity is a genuine identity —
its boundary vanishes (`e₀ · e₀⁻¹` telescopes to `1` in `F(s)`). -/
theorem moralCounterexampleBoundaryVanishes :
    partialBoundary [genE0, invGen genE0] = oneWord := rfl

/-! ## B1 — the group-enrichment congruence (`PeifferEquiv` untouched, additive) -/

/-- ★ **The group-enriched crossed-module congruence.**  Re-closes over `PeifferEquiv` (`ofPeiffer`)
and ADDS the two free-group cancellations making `E = List ConjugatedRelator` a GROUP: `[g, invGen g]`
and `[invGen g, g]` each collapse to `[]`.  A `Prop`-valued inductive — statements are up-to-
`FreeCrossedModuleEquiv`, NEVER via `Quot.sound`. -/
inductive FreeCrossedModuleEquiv : PreCrossedElement → PreCrossedElement → Prop where
  /-- Every Peiffer equivalence is a free-crossed equivalence (embed the r1 relation, incl. peifferMove). -/
  | ofPeiffer {left right : PreCrossedElement} :
      PeifferEquiv left right → FreeCrossedModuleEquiv left right
  /-- Reflexivity (re-closed over the enriched relation). -/
  | refl (element : PreCrossedElement) : FreeCrossedModuleEquiv element element
  /-- Symmetry. -/
  | symm {left right : PreCrossedElement} :
      FreeCrossedModuleEquiv left right → FreeCrossedModuleEquiv right left
  /-- Transitivity. -/
  | trans {left middle right : PreCrossedElement} :
      FreeCrossedModuleEquiv left middle → FreeCrossedModuleEquiv middle right →
      FreeCrossedModuleEquiv left right
  /-- Append-congruence: the relation is a congruence for the group operation of `E`. -/
  | congrAppend {leftA leftB rightA rightB : PreCrossedElement} :
      FreeCrossedModuleEquiv leftA rightA → FreeCrossedModuleEquiv leftB rightB →
      FreeCrossedModuleEquiv (leftA ++ leftB) (rightA ++ rightB)
  /-- ★ The right free-group cancellation `[g, g⁻¹] ~ []`. -/
  | consInvCancel (gen : ConjugatedRelator) :
      FreeCrossedModuleEquiv [gen, invGen gen] ([] : PreCrossedElement)
  /-- ★ The left free-group cancellation `[g⁻¹, g] ~ []`. -/
  | invConsCancel (gen : ConjugatedRelator) :
      FreeCrossedModuleEquiv [invGen gen, gen] ([] : PreCrossedElement)

/-! ## B1 — the soundness extension (the invariant respects the two new cancellations) -/

/-- The group-ring right inverse: `v + (−v) = 0`.  Coefficientwise `intAddRightNeg` through the
propext-clean kit. -/
theorem groupRingAddRightNeg (value : GroupRingZmod3) :
    groupRingAdd value (groupRingNeg value) = groupRingZero :=
  groupRingEq (intAddRightNeg value.coeffOne) (intAddRightNeg value.coeffT)
    (intAddRightNeg value.coeffTsq)

/-- The group-ring left inverse: `(−v) + v = 0`.  Coefficientwise `intAddLeftNeg`. -/
theorem groupRingAddLeftNeg (value : GroupRingZmod3) :
    groupRingAdd (groupRingNeg value) value = groupRingZero :=
  groupRingEq (intAddLeftNeg value.coeffOne) (intAddLeftNeg value.coeffT)
    (intAddLeftNeg value.coeffTsq)

/-- The right cancellation preserves the image: `image [g, invGen g] = image []`.  The trailing
`groupRingZero` unfolds (`groupRingAddZero`), the inverse images to negation
(`conjugatedRelatorImageInvGen`), and `v + (−v) = 0` (`groupRingAddRightNeg`). -/
theorem consInvCancelImage (gen : ConjugatedRelator) :
    crossedModuleImage [gen, invGen gen] = crossedModuleImage ([] : PreCrossedElement) :=
  (congrArg (groupRingAdd (conjugatedRelatorImage gen))
      (groupRingAddZero (conjugatedRelatorImage (invGen gen)))).trans
    ((congrArg (groupRingAdd (conjugatedRelatorImage gen))
        (conjugatedRelatorImageInvGen gen)).trans
      (groupRingAddRightNeg (conjugatedRelatorImage gen)))

/-- The left cancellation preserves the image: `image [invGen g, g] = image []`.  Symmetric to
`consInvCancelImage`, closing with the left inverse `(−v) + v = 0` (`groupRingAddLeftNeg`). -/
theorem invConsCancelImage (gen : ConjugatedRelator) :
    crossedModuleImage [invGen gen, gen] = crossedModuleImage ([] : PreCrossedElement) :=
  (congrArg (groupRingAdd (conjugatedRelatorImage (invGen gen)))
      (groupRingAddZero (conjugatedRelatorImage gen))).trans
    ((congrArg (fun negated => groupRingAdd negated (conjugatedRelatorImage gen))
        (conjugatedRelatorImageInvGen gen)).trans
      (groupRingAddLeftNeg (conjugatedRelatorImage gen)))

/-- ★★★ **The invariant respects the group-enriched congruence** —
`FreeCrossedModuleEquiv x y → crossedModuleImage x = crossedModuleImage y`.  Structural recursion on the
`FreeCrossedModuleEquiv` proof: `ofPeiffer` reuses r2's `crossedModuleImageRespectsPeiffer`, the re-closed
`refl`/`symm`/`trans`/`congrAppend` mirror r2's structure, and the two cancellations are
`consInvCancelImage`/`invConsCancelImage`.  Soundness EXTENDS to the enriched relation with no new `Int`
work. -/
theorem crossedModuleImageRespectsFreeCrossed :
    ∀ {leftElement rightElement : PreCrossedElement},
    FreeCrossedModuleEquiv leftElement rightElement →
    crossedModuleImage leftElement = crossedModuleImage rightElement
  | _, _, .ofPeiffer peiffer => crossedModuleImageRespectsPeiffer peiffer
  | _, _, .refl _ => rfl
  | _, _, .symm equivReversed => (crossedModuleImageRespectsFreeCrossed equivReversed).symm
  | _, _, .trans equivLeftMid equivMidRight =>
      (crossedModuleImageRespectsFreeCrossed equivLeftMid).trans
        (crossedModuleImageRespectsFreeCrossed equivMidRight)
  | _, _, .congrAppend equivLeftPair equivRightPair =>
      (crossedModuleImageAppend _ _).trans
        ((groupRingAddCongr (crossedModuleImageRespectsFreeCrossed equivLeftPair)
            (crossedModuleImageRespectsFreeCrossed equivRightPair)).trans
          (crossedModuleImageAppend _ _).symm)
  | _, _, .consInvCancel gen => consInvCancelImage gen
  | _, _, .invConsCancel gen => invConsCancelImage gen

/-! ## B1 — the moral counterexample reduces under the enrichment (what `PeifferEquiv` could not) -/

/-- ★ **The two-letter identity reduces under the enrichment.**  `[genE0, invGen genE0]` collapses to
`[]` by the new right cancellation — the exact move the shipped `PeifferEquiv` lacks. -/
theorem moralCounterexampleReducesUnderEnrichment :
    FreeCrossedModuleEquiv [genE0, invGen genE0] ([] : PreCrossedElement) :=
  FreeCrossedModuleEquiv.consInvCancel genE0

/-! ## B1 — the strengthened non-triviality: `ζ` stays nontrivial over the coarser relation -/

/-- ★★ **`ζ` is nontrivial even over the group-enriched relation** — `¬ FreeCrossedModuleEquiv ζ []`.
A coarser relation than `PeifferEquiv` still cannot relate `ζ` to `[]`, because the invariant respects it
(`crossedModuleImageRespectsFreeCrossed`) and `image ζ = (−1, 1, 0) ≠ 0 = image []`
(r2 `rotationIdentityImageNeqEmptyImage`).  This STRENGTHENS r2's `rotationIdentityNotPeifferTrivial`
to the enriched relation, so the enrichment threatens nothing r2 shipped. -/
theorem rotationIdentityNotFreeCrossedTrivial :
    ¬ FreeCrossedModuleEquiv rotationIdentityWitness ([] : PreCrossedElement) :=
  fun freeCrossedTrivial =>
    absurd (crossedModuleImageRespectsFreeCrossed freeCrossedTrivial)
      rotationIdentityImageNeqEmptyImage

/-! ## B1 — the clean self-attacks: the rotation orbit's `x ++ x⁻¹` reduce to `[]`

Two genuine identities (all `∂ = []`, all `image = 0`) that the shipped `PeifferEquiv` cannot reduce but
the enrichment can, by pure DOUBLE cancellation (no swap, no R1).  Both have the sandwich shape
`[outer, invGen inner, inner, invGen outer]`: the middle `[invGen inner, inner]` cancels, then the
flanking `[outer, invGen outer]` cancels. -/

/-- ★ **The double-cancellation sandwich** — `[outer, invGen inner, inner, invGen outer] ~ []` by two
free-group cancellations (`invConsCancel inner` inside, `consInvCancel outer` outside), threaded through
`congrAppend`/`refl`.  This is the r4 acceptance move the shipped `PeifferEquiv` lacks. -/
theorem freeCrossedSandwichCancel (outerGen innerGen : ConjugatedRelator) :
    FreeCrossedModuleEquiv [outerGen, invGen innerGen, innerGen, invGen outerGen]
      ([] : PreCrossedElement) :=
  FreeCrossedModuleEquiv.trans
    (FreeCrossedModuleEquiv.congrAppend
      (FreeCrossedModuleEquiv.refl [outerGen])
      (FreeCrossedModuleEquiv.congrAppend
        (FreeCrossedModuleEquiv.invConsCancel innerGen)
        (FreeCrossedModuleEquiv.refl [invGen outerGen])))
    (FreeCrossedModuleEquiv.consInvCancel outerGen)

/-- ★ Self-attack 1 — `ζ ++ ζ⁻¹ = [genE1, invGen genE0, genE0, invGen genE1]` is a genuine identity. -/
theorem selfAttackOneBoundaryVanishes :
    partialBoundary [genE1, invGen genE0, genE0, invGen genE1] = oneWord := rfl

/-- ★ Self-attack 1 — its image is `0` (satisfies the injectivity hypothesis). -/
theorem selfAttackOneImageIsZero :
    crossedModuleImage [genE1, invGen genE0, genE0, invGen genE1] = groupRingZero := rfl

/-- ★★ Self-attack 1 — `ζ ++ ζ⁻¹` REDUCES to `[]` under the enrichment (double cancellation). -/
theorem selfAttackOneReduces :
    FreeCrossedModuleEquiv [genE1, invGen genE0, genE0, invGen genE1] ([] : PreCrossedElement) :=
  freeCrossedSandwichCancel genE1 genE0

/-- ★ Self-attack 3 — `(s·ζ) ++ (s·ζ)⁻¹ = [genE2, invGen genE1, genE1, invGen genE2]` is a genuine
identity (the `s`-orbit member, `∂ = s³·s⁻³ = 1`). -/
theorem selfAttackThreeBoundaryVanishes :
    partialBoundary [genE2, invGen genE1, genE1, invGen genE2] = oneWord := rfl

/-- ★ Self-attack 3 — its image is `0`. -/
theorem selfAttackThreeImageIsZero :
    crossedModuleImage [genE2, invGen genE1, genE1, invGen genE2] = groupRingZero := rfl

/-- ★★ Self-attack 3 — `(s·ζ) ++ (s·ζ)⁻¹` REDUCES to `[]` under the enrichment. -/
theorem selfAttackThreeReduces :
    FreeCrossedModuleEquiv [genE2, invGen genE1, genE1, invGen genE2] ([] : PreCrossedElement) :=
  freeCrossedSandwichCancel genE2 genE1

/-! ## B2 — the residue-keyed normal-form kit: the sort primitive + the `(length, inversions)` measure

The r4 normal-form kit is the SORT half of the deferred structure theorem (the CANCEL half is the two
`FreeCrossedModuleEquiv` cancellations above).  The normal form groups generators by their residue class
`0 ≤ 1 ≤ 2` (the `realizeAugmentationZeroIdentity a b c = repeatGen a genE0 ++ repeatGen b genE1 ++
repeatGen c genE2` shape of r3).  `sortByResidue` is an insertion sort keyed by the residue of the
conjugator, proved to PRODUCE a residue-sorted word (`sortByResidueProducesSorted`, mirroring r1's
`reduceWordProducesReduced`); `residueInversions` is the second lexicographic measure coordinate the r5
structure induction will recurse on.  The key comparator `zmodThreeLe` is a full-enum 9-arm `Bool` table
(never `Nat.decLt` via propext, never an `Int` remainder). -/

/-- The residue sort key of a generator — the image of its conjugator in `G = ZZ/3`. -/
def conjugatorResidueKey (gen : ConjugatedRelator) : ZmodThree := wordResidue gen.conjugator

/-- The residue-key order `0 ≤ 1 ≤ 2` — the fully-enumerated 9-arm `Bool` table (no wildcard, no
`Nat.decLt`, no `Int` remainder). -/
def zmodThreeLe : ZmodThree → ZmodThree → Bool
  | .residue0, .residue0 => true
  | .residue0, .residue1 => true
  | .residue0, .residue2 => true
  | .residue1, .residue0 => false
  | .residue1, .residue1 => true
  | .residue1, .residue2 => true
  | .residue2, .residue0 => false
  | .residue2, .residue1 => false
  | .residue2, .residue2 => true

/-- The order is reflexive. -/
theorem zmodThreeLeRefl : ∀ key : ZmodThree, zmodThreeLe key key = true
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `residue0` is the bottom of the order: `0 ≤ k` for every `k`. -/
theorem zmodThreeLeResidue0Bottom : ∀ key : ZmodThree, zmodThreeLe ZmodThree.residue0 key = true
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- Totality (in `false`-contrapositive form): when `a ≤ b` fails, `b ≤ a` holds.  Full enum over the
nine key pairs (`Bool.noConfusion` kills the six `a ≤ b = true` diagonals-and-above). -/
theorem zmodThreeLeTotalFalse : ∀ (leftKey rightKey : ZmodThree),
    zmodThreeLe leftKey rightKey = false → zmodThreeLe rightKey leftKey = true
  | .residue0, .residue0, notLe => Bool.noConfusion notLe
  | .residue0, .residue1, notLe => Bool.noConfusion notLe
  | .residue0, .residue2, notLe => Bool.noConfusion notLe
  | .residue1, .residue0, _ => rfl
  | .residue1, .residue1, notLe => Bool.noConfusion notLe
  | .residue1, .residue2, notLe => Bool.noConfusion notLe
  | .residue2, .residue0, _ => rfl
  | .residue2, .residue1, _ => rfl
  | .residue2, .residue2, notLe => Bool.noConfusion notLe

/-- The insertion guard: when the incoming generator sorts first (`goesFirst = true`) it is prepended
whole, otherwise the head is kept and the already-inserted tail follows.  A full-enum `Bool` match — the
propext-clean replacement for a `Bool`-conditioned `if` (mirrors r1's `consReducedGuarded`). -/
def insertGuarded (goesFirst : Bool) (gen head : ConjugatedRelator)
    (rest insertedRest : PreCrossedElement) : PreCrossedElement :=
  match goesFirst with
  | true => gen :: head :: rest
  | false => head :: insertedRest

/-- Insert one generator into a residue-sorted word, keyed by `zmodThreeLe` on the residue keys.
Structural on the word (never `WellFounded.fix`). -/
def insertByResidue (gen : ConjugatedRelator) : PreCrossedElement → PreCrossedElement
  | [] => [gen]
  | head :: rest =>
      insertGuarded (zmodThreeLe (conjugatorResidueKey gen) (conjugatorResidueKey head))
        gen head rest (insertByResidue gen rest)

/-- When the incoming generator sorts first, `insertByResidue` prepends it whole. -/
theorem insertByResidueLe (gen head : ConjugatedRelator) (rest : PreCrossedElement)
    (inOrder : zmodThreeLe (conjugatorResidueKey gen) (conjugatorResidueKey head) = true) :
    insertByResidue gen (head :: rest) = gen :: head :: rest :=
  congrArg (fun flag => insertGuarded flag gen head rest (insertByResidue gen rest)) inOrder

/-- When the incoming generator does not sort first, `insertByResidue` keeps the head and recurses. -/
theorem insertByResidueGt (gen head : ConjugatedRelator) (rest : PreCrossedElement)
    (outOfOrder : zmodThreeLe (conjugatorResidueKey gen) (conjugatorResidueKey head) = false) :
    insertByResidue gen (head :: rest) = head :: insertByResidue gen rest :=
  congrArg (fun flag => insertGuarded flag gen head rest (insertByResidue gen rest)) outOfOrder

/-- **The residue sort** — insertion sort keyed by the conjugator residue.  A right fold: sort the tail,
then insert the head.  Structural on the input word. -/
def sortByResidue : PreCrossedElement → PreCrossedElement
  | [] => []
  | gen :: rest => insertByResidue gen (sortByResidue rest)

/-- The sortedness step: carry the tail verdict when the boundary pair is in order, otherwise reject.
Full-enum `Bool` match (mirrors r1's `isReducedStep`). -/
def sortedStep (inOrder tailVerdict : Bool) : Bool :=
  match inOrder with
  | true => tailVerdict
  | false => false

/-- Residue-sortedness scanning FROM a known previous key: the empty tail is sorted; a `gen :: rest`
tail is sorted when `prevKey ≤ key(gen)` and `rest` continues sorted from `key(gen)`.  Single-cons
structural recursion. -/
def isSortedByResidueFrom (prevKey : ZmodThree) : PreCrossedElement → Bool
  | [] => true
  | gen :: rest =>
      sortedStep (zmodThreeLe prevKey (conjugatorResidueKey gen))
        (isSortedByResidueFrom (conjugatorResidueKey gen) rest)

/-- **A word is residue-sorted** when its keys are non-decreasing — scanned from the bottom key
`residue0` (which is `≤` everything, so it imposes no head constraint). -/
def isSortedByResidue (word : PreCrossedElement) : Bool :=
  isSortedByResidueFrom ZmodThree.residue0 word

/-- When the boundary pair is in order, `sortedStep` passes the tail verdict through. -/
theorem sortedStepOfInOrder (inOrder tailVerdict : Bool) (inOrderHolds : inOrder = true) :
    sortedStep inOrder tailVerdict = tailVerdict :=
  congrArg (fun flag => sortedStep flag tailVerdict) inOrderHolds

/-- `sortedStep b t = true` forces the carried tail verdict `t = true`. -/
theorem sortedStepTrueImpliesTail : ∀ (inOrder tailVerdict : Bool),
    sortedStep inOrder tailVerdict = true → tailVerdict = true
  | true, _, stepHolds => stepHolds
  | false, _, stepHolds => Bool.noConfusion stepHolds

/-- `sortedStep b t = true` forces the in-order flag `b = true`. -/
theorem sortedStepTrueImpliesFirst : ∀ (inOrder tailVerdict : Bool),
    sortedStep inOrder tailVerdict = true → inOrder = true
  | true, _, _ => rfl
  | false, _, stepHolds => Bool.noConfusion stepHolds

/-- ★ **Insertion preserves residue-sortedness FROM a floor key** — if `prevKey ≤ key(gen)` and `word`
is sorted from `prevKey`, then inserting `gen` keeps it sorted from `prevKey`.  Structural recursion on
`word`: `[]` reduces the singleton guard; `head :: rest` splits on whether `gen` sorts before `head`,
reducing the two guards (`insertByResidueLe`/`Gt`) and, in the out-of-order case, recursing under the
head with totality (`zmodThreeLeTotalFalse`). -/
theorem insertByResidueSortedFrom : ∀ (prevKey : ZmodThree) (gen : ConjugatedRelator)
    (word : PreCrossedElement),
    zmodThreeLe prevKey (conjugatorResidueKey gen) = true →
    isSortedByResidueFrom prevKey word = true →
    isSortedByResidueFrom prevKey (insertByResidue gen word) = true
  | prevKey, gen, [], prevLe, _ =>
      sortedStepOfInOrder (zmodThreeLe prevKey (conjugatorResidueKey gen)) true prevLe
  | prevKey, gen, head :: rest, prevLe, sortedTail =>
      match hGuard : zmodThreeLe (conjugatorResidueKey gen) (conjugatorResidueKey head) with
      | true =>
          let tailIsSorted : isSortedByResidueFrom (conjugatorResidueKey head) rest = true :=
            sortedStepTrueImpliesTail _ _ sortedTail
          (congrArg (isSortedByResidueFrom prevKey) (insertByResidueLe gen head rest hGuard)).trans
            ((sortedStepOfInOrder (zmodThreeLe prevKey (conjugatorResidueKey gen))
                (isSortedByResidueFrom (conjugatorResidueKey gen) (head :: rest)) prevLe).trans
              ((sortedStepOfInOrder (zmodThreeLe (conjugatorResidueKey gen) (conjugatorResidueKey head))
                  (isSortedByResidueFrom (conjugatorResidueKey head) rest) hGuard).trans
                tailIsSorted))
      | false =>
          let firstTrue : zmodThreeLe prevKey (conjugatorResidueKey head) = true :=
            sortedStepTrueImpliesFirst _ _ sortedTail
          let tailIsSorted : isSortedByResidueFrom (conjugatorResidueKey head) rest = true :=
            sortedStepTrueImpliesTail _ _ sortedTail
          let headLeGen : zmodThreeLe (conjugatorResidueKey head) (conjugatorResidueKey gen) = true :=
            zmodThreeLeTotalFalse (conjugatorResidueKey gen) (conjugatorResidueKey head) hGuard
          let recursed :
              isSortedByResidueFrom (conjugatorResidueKey head) (insertByResidue gen rest) = true :=
            insertByResidueSortedFrom (conjugatorResidueKey head) gen rest headLeGen tailIsSorted
          (congrArg (isSortedByResidueFrom prevKey) (insertByResidueGt gen head rest hGuard)).trans
            ((sortedStepOfInOrder (zmodThreeLe prevKey (conjugatorResidueKey head))
                (isSortedByResidueFrom (conjugatorResidueKey head) (insertByResidue gen rest))
                firstTrue).trans
              recursed)

/-- ★★ **`sortByResidue` produces a residue-sorted word** — the normal-form soundness of the sort half,
by structural induction folding `insertByResidueSortedFrom` from the bottom key `residue0`.  Mirrors r1's
`reduceWordProducesReduced`. -/
theorem sortByResidueProducesSorted : ∀ word : PreCrossedElement,
    isSortedByResidue (sortByResidue word) = true
  | [] => rfl
  | gen :: rest =>
      insertByResidueSortedFrom ZmodThree.residue0 gen (sortByResidue rest)
        (zmodThreeLeResidue0Bottom (conjugatorResidueKey gen))
        (sortByResidueProducesSorted rest)

/-! ### B2 — the lexicographic `(length, inversions)` measure (r5's structure-induction fuel) -/

/-- The first measure coordinate — the number of generators (cancellation drops it by two). -/
def preCrossedLength (element : PreCrossedElement) : Nat := element.length

/-- The out-of-order count against a pivot key — the number of later generators whose key sorts strictly
before the pivot.  Full-enum `Bool` match on the order guard. -/
def residueInversionsFrom (pivotKey : ZmodThree) : PreCrossedElement → Nat
  | [] => 0
  | gen :: rest =>
      match zmodThreeLe pivotKey (conjugatorResidueKey gen) with
      | true => residueInversionsFrom pivotKey rest
      | false => residueInversionsFrom pivotKey rest + 1

/-- The second measure coordinate — the total residue-inversion count (a residue swap drops it while
preserving length).  Structural right fold. -/
def residueInversions : PreCrossedElement → Nat
  | [] => 0
  | gen :: rest => residueInversionsFrom (conjugatorResidueKey gen) rest + residueInversions rest

/-! ### B2 probes — evaluate the sort/measure on concrete inputs FIRST -/

/-- ★ Probe (eval) — the sort groups by residue: `[genE1, genE0]` (keys `1, 0`) sorts to `[genE0, genE1]`
(keys `0, 1`). -/
theorem sortByResidueSwapsProbe : sortByResidue [genE1, genE0] = [genE0, genE1] := rfl

/-- ★ Probe — the sorted output is residue-sorted (the produced-sorted theorem, evaluated). -/
theorem sortByResidueSortedProbe : isSortedByResidue [genE0, genE1] = true := rfl

/-- ★ Probe — a sorted word has zero residue inversions. -/
theorem residueInversionsSortedIsZero : residueInversions [genE0, genE1] = 0 := rfl

/-- ★ Probe — the unsorted `[genE1, genE0]` has exactly one residue inversion (the pair `1 > 0`). -/
theorem residueInversionsUnsortedIsOne : residueInversions [genE1, genE0] = 1 := rfl

end FX1Poly.Polygraph.Homology
