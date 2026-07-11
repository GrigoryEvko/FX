import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupStructureTheorem

/-! # FX1Poly/Polygraph/Homology/CrossedModuleFreeGroupMeasureInduction — the measure induction that
    lands the general well-formed residual, and thereby the UNCONDITIONAL free-crossed-module instance
    iso `π₂⟨s | s³⟩ ≅ ker(N)` (WP-2GROUP r6, #2199)

r5 (`Homology/CrossedModuleFreeGroupStructureTheorem`) proved the residual→injectivity→iso bridge and
INHABITED the guarded residual `freeCrossedModuleNormalFormResidualWellFormed` only on concrete
well-formed elements (the shuffled commutator); the GENERAL residual (the measure induction) stayed the
Brown–Huebschmann structure-theorem wall.  r6 discharges it, zero-axiom, and feeds the shipped
`freeCrossedModulePiTwoIsoOfResidual` to produce an UNCONDITIONAL `FreeCrossedModulePiTwoIso` inhabitant.

## The route (recon-confirmed): normalize-first, then insert-into-canonical-form

The single missing move that unlocks arbitrary-conjugator normalization is **self-conjugation of a
generator by itself** (`selfConjugateShiftRaw g : [g] ~ [peifferConjugate g g]`), whose twist prepends
`∂g = s³` to the conjugator and re-reduces.  Off it:

  * **B1 (the atomic layer).**  `selfConjugateShiftRaw`/`selfConjugateShiftEq` (the self-shift),
    `freeCrossedInvGenCongr` (the formal-inverse congruence, via `invGenInvGen`), the genE-form commute
    `freeCrossedGenEFormCommute` (positive-left via `commutePosLeft`, both-negative via the crossed-inverse
    anti-congruence `invListCongr`), and `commutePastBlock` (float a genE-form through a homogeneous
    block).
  * **B2 (the phase inductions).**  Two structural power-normalizations `normalizePosPower` /
    `normalizeNegPower` (each recursing on the exponent magnitude via the `k+3` strips), their `Int`-level
    packaging `normalizeSignPowerInt`, and the arbitrary-conjugator `normalizeGen` (self-shift to a
    signPower, normalize, residue-bridge via `reduceResiduePreserved` — NEVER the exponentSum↔residue
    bridge).  Each well-formed single generator lands on its genE-form.
  * **B3 (the general residual + the iso).**  `prependGenEForm` (insert one genE-form into a realized
    form: float past prior blocks by `commutePastBlock`, extend/cancel its own block), `prependGen`
    (normalize the head, then insert; image preserved by r4 soundness), `appendRealize` (the structural
    list induction), the residual `freeCrossedResidualWellFormed`, and the UNCONDITIONAL
    `freeCrossedModulePiTwoIso := freeCrossedModulePiTwoIsoOfResidual freeCrossedResidualWellFormed`.

## Zero-axiom design decisions

  * Every match on `Bool` / `ZmodThree` / `Int`-constructor / the equiv proofs is FULLY enumerated — no
    `_ =>` wildcard, so no match-compiler propext leak.  Structural recursion throughout (the `k+3`
    strip pattern, `repeatGenPos`/list structure), NEVER `WellFounded.fix`.
  * All residue tracking goes through `wordResidue` (definitionally connected via `shiftUp`/`shiftDown`),
    never `exponentSum`; the one Int-crossing-zero use routes through the shipped propext-clean
    `intSubNatNatLeftSurplus`.  Group-ring equalities go through `groupRingEq`, never `mk.injEq`.
  * The two list identities `listAppendNilRight`/`listAppendAssociative` are proved locally by structural
    induction (no reliance on Init lemmas that might carry `propext`).

`Init`-only (over `Homology/CrossedModuleFreeGroupStructureTheorem`), structural, zero axioms.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupMeasureInduction.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1a — the formal-inverse congruence + the self-conjugation shift -/

/-- `Bool.not` is an involution — the two-case base for `invGenInvGen`. -/
theorem notNotBool : ∀ flag : Bool, Bool.not (Bool.not flag) = flag
  | true => rfl
  | false => rfl

/-- The formal inverse is an involution on conjugated relators: `(g⁻¹)⁻¹ = g` (only the sign flips,
`not (not sign) = sign`). -/
theorem invGenInvGen (gen : ConjugatedRelator) : invGen (invGen gen) = gen :=
  congrArg (fun sign => ConjugatedRelator.mk gen.conjugator gen.relationIndex sign)
    (notNotBool gen.isPositive)

/-- ★ **The formal-inverse congruence** — `[g] ~ [g'] → [g⁻¹] ~ [g'⁻¹]`.  Sandwich `g'⁻¹` around the
hypothesis: `[g⁻¹] ~ [g'⁻¹, g', g⁻¹] ~ [g'⁻¹, g, g⁻¹] ~ [g'⁻¹]` using `invConsCancel g'` / the hypothesis
(reversed) / `consInvCancel g`.  Lets the whole normalizer piggyback the negative sign on the positive
one. -/
theorem freeCrossedInvGenCongr {gen genPrime : ConjugatedRelator}
    (hEquiv : FreeCrossedModuleEquiv [gen] [genPrime]) :
    FreeCrossedModuleEquiv [invGen gen] [invGen genPrime] :=
  let step1 : FreeCrossedModuleEquiv [invGen gen] [invGen genPrime, genPrime, invGen gen] :=
    FreeCrossedModuleEquiv.symm
      (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.invConsCancel genPrime)
        (FreeCrossedModuleEquiv.refl [invGen gen]))
  let step2 : FreeCrossedModuleEquiv [invGen genPrime, genPrime, invGen gen]
      [invGen genPrime, gen, invGen gen] :=
    FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [invGen genPrime])
      (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.symm hEquiv)
        (FreeCrossedModuleEquiv.refl [invGen gen]))
  let step3 : FreeCrossedModuleEquiv [invGen genPrime, gen, invGen gen] [invGen genPrime] :=
    FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [invGen genPrime])
      (FreeCrossedModuleEquiv.consInvCancel gen)
  FreeCrossedModuleEquiv.trans step1 (FreeCrossedModuleEquiv.trans step2 step3)

/-- ★★ **The self-conjugation shift (raw)** — `[g] ~ [^{∂g}g]`.  `peifferMove g g` sends `[g, g, g⁻¹]`
to `[^{∂g}g]`, and `[g, g, g⁻¹] ~ [g]` by tail cancellation (`consInvCancel g`).  Pure structure — the
single move that touches an arbitrary conjugator (it pre-multiplies by `∂g` and re-reduces). -/
theorem selfConjugateShiftRaw (gen : ConjugatedRelator) :
    FreeCrossedModuleEquiv [gen] [peifferConjugate gen gen] :=
  (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [gen])
      (FreeCrossedModuleEquiv.consInvCancel gen)).symm.trans
    (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove gen gen))

/-- ★★ **The self-shift with a computed target conjugator** — for an over-gen-0 word `w`, self-conjugating
`⟨w, 0, +⟩` yields `⟨reduceWord(s³ ++ w), 0, +⟩`; if that reduced word is `result`, the shift lands on
`⟨result, 0, +⟩`.  The workhorse converting an arbitrary conjugator to a `signPower`. -/
theorem selfConjugateShiftEq {conjugatorWord result : List SignedLetter}
    (over : AllLettersOverGenZero conjugatorWord)
    (reducesTo : reduceWord (relatorWord 0 ++ conjugatorWord) = result) :
    FreeCrossedModuleEquiv [⟨conjugatorWord, 0, true⟩] [⟨result, 0, true⟩] :=
  let peifferConjugateEq :
      peifferConjugate ⟨conjugatorWord, 0, true⟩ ⟨conjugatorWord, 0, true⟩ = ⟨result, 0, true⟩ :=
    congrArg (fun conj => ConjugatedRelator.mk conj 0 true)
      ((congrArg (fun boundary => reduceWord (boundary ++ conjugatorWord))
          (conjugatedRelatorBoundaryIsRelatorOverGenZero over)).trans reducesTo)
  Eq.mp (congrArg (fun target => FreeCrossedModuleEquiv [⟨conjugatorWord, 0, true⟩] [target])
      peifferConjugateEq)
    (selfConjugateShiftRaw ⟨conjugatorWord, 0, true⟩)

/-! ## B1b — the genE-form commute (positive-left, both-negative via the anti-congruence) -/

/-- ★ **The positive-left commute** — with a positive-signed genE-form on the left (so `∂ = s³`), any two
genE-forms commute: `[⟨sᶦᵃ, 0, +⟩, ⟨sᶦᵇ, 0, sb⟩] ~ [⟨sᶦᵇ, 0, sb⟩, ⟨sᶦᵃ, 0, +⟩]`.  `freeCrossedAdjacentSwap`
twists the right letter to `⟨sᶦᵇ⁺³, 0, sb⟩`, and the `s^{k+3} → s^k` strip returns it (positive strip
`freeCrossedSignPowerStrip`; negative via `freeCrossedInvGenCongr`). -/
theorem commutePosLeft (powerLeft powerRight : Nat) (signRight : Bool) :
    FreeCrossedModuleEquiv
      [⟨signPowerPos powerLeft, 0, true⟩, ⟨signPowerPos powerRight, 0, signRight⟩]
      [⟨signPowerPos powerRight, 0, signRight⟩, ⟨signPowerPos powerLeft, 0, true⟩] :=
  let twistedEq :
      peifferConjugate ⟨signPowerPos powerLeft, 0, true⟩ ⟨signPowerPos powerRight, 0, signRight⟩
        = ⟨signPowerPos (powerRight + 3), 0, signRight⟩ :=
    congrArg (fun conj => ConjugatedRelator.mk conj 0 signRight)
      ((congrArg (fun boundary => reduceWord (boundary ++ signPowerPos powerRight))
          (conjugatedRelatorBoundaryIsRelatorOverGenZero (allLettersSignPowerPos powerLeft))).trans
        ((congrArg reduceWord (signPowerPosAppend 3 powerRight)).trans
          ((reduceWordSignPowerPos (3 + powerRight)).trans
            (congrArg signPowerPos (Nat.add_comm 3 powerRight)))))
  let strip :
      FreeCrossedModuleEquiv [⟨signPowerPos (powerRight + 3), 0, signRight⟩]
        [⟨signPowerPos powerRight, 0, signRight⟩] :=
    match signRight with
    | true => freeCrossedSignPowerStrip powerRight
    | false => freeCrossedInvGenCongr (freeCrossedSignPowerStrip powerRight)
  FreeCrossedModuleEquiv.trans
    (freeCrossedAdjacentSwap ⟨signPowerPos powerLeft, 0, true⟩ ⟨signPowerPos powerRight, 0, signRight⟩)
    (FreeCrossedModuleEquiv.congrAppend
      (Eq.mp (congrArg (fun twisted =>
            FreeCrossedModuleEquiv [twisted] [⟨signPowerPos powerRight, 0, signRight⟩]) twistedEq.symm)
        strip)
      (FreeCrossedModuleEquiv.refl [⟨signPowerPos powerLeft, 0, true⟩]))

/-! ### The crossed-inverse anti-congruence (for the both-negative commute) -/

/-- Structural right-nil for lists (proved locally to stay off Init lemmas). -/
theorem listAppendNilRight {elementType : Type} : ∀ (elements : List elementType),
    elements ++ [] = elements
  | [] => rfl
  | head :: tail => congrArg (fun rest => head :: rest) (listAppendNilRight tail)

/-- Structural append-associativity for lists (proved locally). -/
theorem listAppendAssociative {elementType : Type} : ∀ (front middle back : List elementType),
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | head :: tail, middle, back =>
      congrArg (fun rest => head :: rest) (listAppendAssociative tail middle back)

/-- The crossed-module inverse of a word: reverse and formally-invert each generator (directly, tail
first). -/
def crossedInverse : PreCrossedElement → PreCrossedElement
  | [] => []
  | gen :: rest => crossedInverse rest ++ [invGen gen]

/-- The crossed inverse is an anti-homomorphism for `++`: `crossedInverse (u ++ v) = crossedInverse v ++
crossedInverse u`.  Structural on `u`, folding `listAppendAssociative`/`listAppendNilRight`. -/
theorem crossedInverseAppend : ∀ (frontWord backWord : PreCrossedElement),
    crossedInverse (frontWord ++ backWord) = crossedInverse backWord ++ crossedInverse frontWord
  | [], backWord => (listAppendNilRight (crossedInverse backWord)).symm
  | gen :: rest, backWord =>
      (congrArg (fun tailInverse => tailInverse ++ [invGen gen])
          (crossedInverseAppend rest backWord)).trans
        (listAppendAssociative (crossedInverse backWord) (crossedInverse rest) [invGen gen])

/-- The Peiffer twist commutes with the formal inverse on the right operand:
`^{∂a}(b⁻¹) = (^{∂a}b)⁻¹` (both keep `a`'s boundary-shift and flip only `b`'s sign). -/
theorem peifferConjugateInvGenRight (firstGen secondGen : ConjugatedRelator) :
    peifferConjugate firstGen (invGen secondGen) = invGen (peifferConjugate firstGen secondGen) := rfl

/-- The Peiffer congruence transported through the crossed inverse — the `PeifferEquiv` half of the
anti-congruence.  The generating `peifferMove a b` maps to `peifferMove a (invGen b)` after
`invGenInvGen` and `peifferConjugateInvGenRight`. -/
theorem peifferInvListCongr : ∀ {leftWord rightWord : PreCrossedElement},
    PeifferEquiv leftWord rightWord →
    FreeCrossedModuleEquiv (crossedInverse leftWord) (crossedInverse rightWord)
  | _, _, .refl element => FreeCrossedModuleEquiv.refl (crossedInverse element)
  | _, _, .symm hReversed => FreeCrossedModuleEquiv.symm (peifferInvListCongr hReversed)
  | _, _, .trans hLeftMid hMidRight =>
      FreeCrossedModuleEquiv.trans (peifferInvListCongr hLeftMid) (peifferInvListCongr hMidRight)
  | _, _, @PeifferEquiv.congrAppend leftA leftB rightA rightB hPairLeft hPairRight =>
      Eq.mp (congrArg (fun rebuilt =>
            FreeCrossedModuleEquiv (crossedInverse (leftA ++ leftB)) rebuilt)
          (crossedInverseAppend rightA rightB).symm)
        (Eq.mp (congrArg (fun rebuilt =>
              FreeCrossedModuleEquiv rebuilt (crossedInverse rightB ++ crossedInverse rightA))
            (crossedInverseAppend leftA leftB).symm)
          (FreeCrossedModuleEquiv.congrAppend (peifferInvListCongr hPairRight)
            (peifferInvListCongr hPairLeft)))
  | _, _, .peifferMove firstGen secondGen =>
      let lhsEq : crossedInverse [firstGen, secondGen, invGen firstGen]
          = [firstGen, invGen secondGen, invGen firstGen] :=
        congrArg (fun head => (head :: [invGen secondGen, invGen firstGen] : PreCrossedElement))
          (invGenInvGen firstGen)
      Eq.mp (congrArg (fun rebuilt =>
            FreeCrossedModuleEquiv rebuilt [invGen (peifferConjugate firstGen secondGen)]) lhsEq.symm)
        (Eq.mp (congrArg (fun twisted =>
              FreeCrossedModuleEquiv [firstGen, invGen secondGen, invGen firstGen] [twisted])
            (peifferConjugateInvGenRight firstGen secondGen))
          (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove firstGen (invGen secondGen))))

/-- ★★ **The crossed-inverse anti-congruence** — `x ~ y → crossedInverse x ~ crossedInverse y`.  Structural
on the `FreeCrossedModuleEquiv` proof; `congrAppend` flips the pair order (`crossedInverseAppend`), the two
cancellations map to themselves (`invGenInvGen`), and `ofPeiffer` reuses `peifferInvListCongr`.  This is
what turns a positive-left commute into a both-negative one. -/
theorem invListCongr : ∀ {leftWord rightWord : PreCrossedElement},
    FreeCrossedModuleEquiv leftWord rightWord →
    FreeCrossedModuleEquiv (crossedInverse leftWord) (crossedInverse rightWord)
  | _, _, .ofPeiffer peiffer => peifferInvListCongr peiffer
  | _, _, .refl element => FreeCrossedModuleEquiv.refl (crossedInverse element)
  | _, _, .symm hReversed => FreeCrossedModuleEquiv.symm (invListCongr hReversed)
  | _, _, .trans hLeftMid hMidRight =>
      FreeCrossedModuleEquiv.trans (invListCongr hLeftMid) (invListCongr hMidRight)
  | _, _, @FreeCrossedModuleEquiv.congrAppend leftA leftB rightA rightB hPairLeft hPairRight =>
      Eq.mp (congrArg (fun rebuilt =>
            FreeCrossedModuleEquiv (crossedInverse (leftA ++ leftB)) rebuilt)
          (crossedInverseAppend rightA rightB).symm)
        (Eq.mp (congrArg (fun rebuilt =>
              FreeCrossedModuleEquiv rebuilt (crossedInverse rightB ++ crossedInverse rightA))
            (crossedInverseAppend leftA leftB).symm)
          (FreeCrossedModuleEquiv.congrAppend (invListCongr hPairRight) (invListCongr hPairLeft)))
  | _, _, .consInvCancel gen =>
      let lhsEq : crossedInverse [gen, invGen gen] = [gen, invGen gen] :=
        congrArg (fun head => (head :: [invGen gen] : PreCrossedElement)) (invGenInvGen gen)
      Eq.mp (congrArg (fun rebuilt =>
            FreeCrossedModuleEquiv rebuilt (crossedInverse ([] : PreCrossedElement))) lhsEq.symm)
        (FreeCrossedModuleEquiv.consInvCancel gen)
  | _, _, .invConsCancel gen =>
      let lhsEq : crossedInverse [invGen gen, gen] = [invGen gen, gen] :=
        congrArg (fun head => ([invGen gen, head] : PreCrossedElement)) (invGenInvGen gen)
      Eq.mp (congrArg (fun rebuilt =>
            FreeCrossedModuleEquiv rebuilt (crossedInverse ([] : PreCrossedElement))) lhsEq.symm)
        (FreeCrossedModuleEquiv.invConsCancel gen)

/-- ★ **The both-negative commute** — two negative-signed genE-forms commute, via the anti-congruence of
the positive-left commute (`invListCongr (commutePosLeft …)`, whose crossed inverse is exactly the
sign-flipped swapped pair). -/
theorem commuteBothNeg (powerLeft powerRight : Nat) :
    FreeCrossedModuleEquiv
      [⟨signPowerPos powerLeft, 0, false⟩, ⟨signPowerPos powerRight, 0, false⟩]
      [⟨signPowerPos powerRight, 0, false⟩, ⟨signPowerPos powerLeft, 0, false⟩] :=
  invListCongr (commutePosLeft powerRight powerLeft true)

/-- ★★ **The genE-form commute** — any two genE-forms commute up to `~`.  Full case split on the two signs:
positive-left directly (`commutePosLeft`), negative-positive by symmetry, both-negative by
`commuteBothNeg`. -/
theorem freeCrossedGenEFormCommute (powerLeft powerRight : Nat) (signLeft signRight : Bool) :
    FreeCrossedModuleEquiv
      [⟨signPowerPos powerLeft, 0, signLeft⟩, ⟨signPowerPos powerRight, 0, signRight⟩]
      [⟨signPowerPos powerRight, 0, signRight⟩, ⟨signPowerPos powerLeft, 0, signLeft⟩] :=
  match signLeft, signRight with
  | true, true => commutePosLeft powerLeft powerRight true
  | true, false => commutePosLeft powerLeft powerRight false
  | false, true => FreeCrossedModuleEquiv.symm (commutePosLeft powerRight powerLeft false)
  | false, false => commuteBothNeg powerLeft powerRight

/-- ★ **Float a genE-form through a homogeneous block** — a genE-form commutes to the far side of a block
of `count` copies of another genE-form.  Structural on `count`, one `freeCrossedGenEFormCommute` per step. -/
theorem commutePastBlock (powerMove : Nat) (signMove : Bool) (powerBlock : Nat) (signBlock : Bool) :
    ∀ count : Nat,
    FreeCrossedModuleEquiv
      (⟨signPowerPos powerMove, 0, signMove⟩ :: repeatGenPos count ⟨signPowerPos powerBlock, 0, signBlock⟩)
      (repeatGenPos count ⟨signPowerPos powerBlock, 0, signBlock⟩ ++ [⟨signPowerPos powerMove, 0, signMove⟩])
  | 0 => FreeCrossedModuleEquiv.refl _
  | count + 1 =>
      let moveGen : ConjugatedRelator := ⟨signPowerPos powerMove, 0, signMove⟩
      let blockGen : ConjugatedRelator := ⟨signPowerPos powerBlock, 0, signBlock⟩
      let step1 : FreeCrossedModuleEquiv (moveGen :: repeatGenPos (count + 1) blockGen)
          (blockGen :: (moveGen :: repeatGenPos count blockGen)) :=
        FreeCrossedModuleEquiv.congrAppend
          (freeCrossedGenEFormCommute powerMove powerBlock signMove signBlock)
          (FreeCrossedModuleEquiv.refl (repeatGenPos count blockGen))
      let step2 : FreeCrossedModuleEquiv (blockGen :: (moveGen :: repeatGenPos count blockGen))
          (repeatGenPos (count + 1) blockGen ++ [moveGen]) :=
        FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [blockGen])
          (commutePastBlock powerMove signMove powerBlock signBlock count)
      FreeCrossedModuleEquiv.trans step1 step2

/-! ### B1 truth probes -/

/-- ★ Probe (the swap-then-strip, evaluated on a concrete out-of-order pair) — `[genE0, genE1] ~
[genE1, genE0]`: the positive-left commute moves `genE0` past `genE1`. -/
theorem genEFormCommuteProbe :
    FreeCrossedModuleEquiv [genE0, genE1] [genE1, genE0] :=
  freeCrossedGenEFormCommute 0 1 true true

/-- ★ Probe (both-negative commute) — `[genE1⁻¹, genE2⁻¹] ~ [genE2⁻¹, genE1⁻¹]`. -/
theorem genEFormCommuteBothNegProbe :
    FreeCrossedModuleEquiv [invGen genE1, invGen genE2] [invGen genE2, invGen genE1] :=
  freeCrossedGenEFormCommute 1 2 false false

/-- ★ Probe (self-shift) — self-conjugating `genE0` prepends `s³`: `[genE0] ~ [⟨s³, 0, +⟩]`. -/
theorem selfConjugateShiftProbe :
    FreeCrossedModuleEquiv [genE0]
      [⟨[SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0], 0, true⟩] :=
  selfConjugateShiftEq (conjugatorWord := []) .nil rfl

/-- ★ **The B1 atomic-layer marker.**  Shipped zero-axiom: the formal-inverse congruence
(`freeCrossedInvGenCongr` via `invGenInvGen`), the self-conjugation shift
(`selfConjugateShiftRaw`/`selfConjugateShiftEq`), the genE-form commute (`freeCrossedGenEFormCommute`,
positive-left + both-negative via the crossed-inverse anti-congruence `invListCongr`), and the block float
`commutePastBlock`.  Read the meaning from THIS docstring. -/
def freeCrossedMeasureAtomicLayerIsComplete : Bool := true

/-! ## B2 — the NORMALIZE phase inductions: every well-formed generator lands on its genE-form -/

/-- The positive genE-form of a residue class: `genE0`/`genE1`/`genE2` for `residue0`/`1`/`2` (each
`⟨signPowerPos j, 0, +⟩` with `wordResidue (signPowerPos j) = residue_j`). -/
def genEformOfResidue : ZmodThree → ConjugatedRelator
  | .residue0 => genE0
  | .residue1 => genE1
  | .residue2 => genE2

/-- The signed genE-form of a residue class — the positive genE-form for `+`, its formal inverse for `-`. -/
def genEformSigned (sign : Bool) (residue : ZmodThree) : ConjugatedRelator :=
  match sign with
  | true => genEformOfResidue residue
  | false => invGen (genEformOfResidue residue)

/-- `shiftUp` has order three (the `ZZ/3` residue action). -/
theorem shiftUpThree : ∀ residue : ZmodThree, shiftUp (shiftUp (shiftUp residue)) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- `shiftDown` has order three. -/
theorem shiftDownThree : ∀ residue : ZmodThree, shiftDown (shiftDown (shiftDown residue)) = residue
  | .residue0 => rfl
  | .residue1 => rfl
  | .residue2 => rfl

/-- Free reduction fixes a negative `signPower` (already reduced). -/
theorem reduceWordSignPowerNeg : ∀ count : Nat, reduceWord (signPowerNeg count) = signPowerNeg count
  | 0 => rfl
  | count + 1 =>
      (congrArg (consReduced (SignedLetter.neg 0)) (reduceWordSignPowerNeg count)).trans
        (consReducedNegSignPowerNeg count)

/-- ★★ **The negative-power strip** `⟨s⁻⁽ᵏ⁺³⁾, 0, +⟩ ~ ⟨s⁻ᵏ, 0, +⟩` — self-conjugating a negative power by
itself prepends `∂ = s³` and cancels three of the `s⁻¹`s (a direct `reduceWord` computation, no
`exponentSum`). -/
theorem freeCrossedSignPowerNegStrip (count : Nat) :
    FreeCrossedModuleEquiv [⟨signPowerNeg (count + 3), 0, true⟩] [⟨signPowerNeg count, 0, true⟩] :=
  selfConjugateShiftEq (allLettersSignPowerNeg (count + 3))
    ((congrArg
          (fun tail => consReduced (SignedLetter.pos 0)
            (consReduced (SignedLetter.pos 0) (consReduced (SignedLetter.pos 0) tail)))
          (reduceWordSignPowerNeg (count + 3))).trans
      ((congrArg
            (fun tail => consReduced (SignedLetter.pos 0) (consReduced (SignedLetter.pos 0) tail))
            (consReducedPosSignPowerNeg (count + 2))).trans
        ((congrArg (consReduced (SignedLetter.pos 0)) (consReducedPosSignPowerNeg (count + 1))).trans
          (consReducedPosSignPowerNeg count))))

/-- ★ **The positive-power normalization** — `⟨sᵏ, 0, +⟩ ~ [genE-form of its residue]`, structural on `k`
via the `k+3` strip (`freeCrossedSignPowerStrip`), residue tracked by `wordResidue` and reconciled with
`shiftUpThree`. -/
theorem normalizePosPower : ∀ count : Nat,
    FreeCrossedModuleEquiv [⟨signPowerPos count, 0, true⟩]
      [genEformOfResidue (wordResidue (signPowerPos count))]
  | 0 => FreeCrossedModuleEquiv.refl _
  | 1 => FreeCrossedModuleEquiv.refl _
  | 2 => FreeCrossedModuleEquiv.refl _
  | count + 3 =>
      Eq.mp (congrArg (fun residue =>
            FreeCrossedModuleEquiv [⟨signPowerPos (count + 3), 0, true⟩] [genEformOfResidue residue])
          (shiftUpThree (wordResidue (signPowerPos count))).symm)
        (FreeCrossedModuleEquiv.trans (freeCrossedSignPowerStrip count) (normalizePosPower count))

/-- ★ **The negative-power normalization** — `⟨s⁻ᵏ, 0, +⟩ ~ [genE-form of its residue]`, structural on `k`
via the negative strip; the bases `k = 1, 2` are a single self-shift (`selfConjugateShiftEq`, the reduced
word computed by `rfl`), `k = 0` is `refl`. -/
theorem normalizeNegPower : ∀ count : Nat,
    FreeCrossedModuleEquiv [⟨signPowerNeg count, 0, true⟩]
      [genEformOfResidue (wordResidue (signPowerNeg count))]
  | 0 => FreeCrossedModuleEquiv.refl _
  | 1 => selfConjugateShiftEq (allLettersSignPowerNeg 1) rfl
  | 2 => selfConjugateShiftEq (allLettersSignPowerNeg 2) rfl
  | count + 3 =>
      Eq.mp (congrArg (fun residue =>
            FreeCrossedModuleEquiv [⟨signPowerNeg (count + 3), 0, true⟩] [genEformOfResidue residue])
          (shiftDownThree (wordResidue (signPowerNeg count))).symm)
        (FreeCrossedModuleEquiv.trans (freeCrossedSignPowerNegStrip count) (normalizeNegPower count))

/-- ★ **The `Int`-level power normalization** — `⟨sᵉ, 0, +⟩ ~ [genE-form of its residue]` for every exponent
`e`, dispatching on the `Int` constructor to the positive/negative power normalizations. -/
theorem normalizeSignPowerInt : ∀ exponent : Int,
    FreeCrossedModuleEquiv [⟨signPower exponent, 0, true⟩]
      [genEformOfResidue (wordResidue (signPower exponent))]
  | Int.ofNat count => normalizePosPower count
  | Int.negSucc predecessor => normalizeNegPower (predecessor + 1)

/-- ★★ **Normalize a positive well-formed generator** — `⟨w, 0, +⟩ ~ [genE-form of `wordResidue w`]` for any
over-gen-0 conjugator `w`.  Self-shift `w` to the signPower `reduceWord(s³ ++ w)`, normalize that power, and
carry the residue back via `reduceResiduePreserved` (the residue of `s³ ++ w` is that of `w`, since
`∂ρ` has residue `0`) — the whole conjugator reduced with NO `exponentSum↔residue` bridge. -/
theorem normalizeGenTrue {conjugatorWord : List SignedLetter}
    (over : AllLettersOverGenZero conjugatorWord) :
    FreeCrossedModuleEquiv [⟨conjugatorWord, 0, true⟩]
      [genEformOfResidue (wordResidue conjugatorWord)] :=
  let shiftedExponent : Int := exponentSum (relatorWord 0 ++ conjugatorWord)
  let shift : FreeCrossedModuleEquiv [⟨conjugatorWord, 0, true⟩]
      [⟨signPower shiftedExponent, 0, true⟩] :=
    selfConjugateShiftEq over
      (reduceWordIsSignPowerOverGenZero (allLettersAppend allLettersRelatorWordZero over))
  let normalized := FreeCrossedModuleEquiv.trans shift (normalizeSignPowerInt shiftedExponent)
  let residueBridge : wordResidue (signPower shiftedExponent) = wordResidue conjugatorWord :=
    (congrArg wordResidue
        (reduceWordIsSignPowerOverGenZero
          (allLettersAppend allLettersRelatorWordZero over)).symm).trans
      ((reduceResiduePreserved (relatorWord 0 ++ conjugatorWord)).trans
        ((wordResidueAppendAdd (relatorWord 0) conjugatorWord).trans
          ((congrArg (fun residue => addZmod3 residue (wordResidue conjugatorWord))
              (relatorResidueIsZero 0)).trans
            (addZmod3ZeroLeft (wordResidue conjugatorWord)))))
  Eq.mp (congrArg (fun residue =>
        FreeCrossedModuleEquiv [⟨conjugatorWord, 0, true⟩] [genEformOfResidue residue]) residueBridge)
    normalized

/-- ★★ **Normalize a well-formed generator (either sign)** — `⟨w, 0, sign⟩ ~ [signed genE-form of
`wordResidue w`]`.  The positive sign is `normalizeGenTrue`; the negative sign piggybacks it through
`freeCrossedInvGenCongr` (since `⟨w, 0, -⟩ = (⟨w, 0, +⟩)⁻¹`). -/
theorem normalizeGen (sign : Bool) {conjugatorWord : List SignedLetter}
    (over : AllLettersOverGenZero conjugatorWord) :
    FreeCrossedModuleEquiv [⟨conjugatorWord, 0, sign⟩]
      [genEformSigned sign (wordResidue conjugatorWord)] :=
  match sign with
  | true => normalizeGenTrue over
  | false => freeCrossedInvGenCongr (normalizeGenTrue over)

/-! ### B2 truth probes -/

/-- ★ Probe (arbitrary unreduced conjugator normalized) — `⟨s s⁻¹ s, 0, +⟩ ~ genE1` (residue `1`). -/
theorem normalizeGenProbe :
    FreeCrossedModuleEquiv
      [⟨[SignedLetter.pos 0, SignedLetter.neg 0, SignedLetter.pos 0], 0, true⟩] [genE1] :=
  normalizeGenTrue (.consPos _ (.consNeg _ (.consPos _ .nil)))

/-- ★ Probe (negative power normalized) — `⟨s⁻⁴, 0, +⟩ ~ genE2` (residue `−4 ≡ 2`). -/
theorem normalizeNegPowerProbe :
    FreeCrossedModuleEquiv [⟨signPowerNeg 4, 0, true⟩] [genE2] :=
  normalizeNegPower 4

/-- ★ **The B2 NORMALIZE marker.**  Shipped zero-axiom: the residue-generic genE-form `genEformOfResidue`,
the two structural power normalizations (`normalizePosPower`/`normalizeNegPower` off the two strips), their
`Int` packaging `normalizeSignPowerInt`, and the arbitrary-conjugator `normalizeGen` — every well-formed
single generator lands on its genE-form, image preserved (r4 soundness).  Read the meaning from THIS
docstring. -/
def freeCrossedMeasureNormalizeIsComplete : Bool := true

/-! ## B3 — insert a genE-form into a realized form, assemble the residual, deliver the iso -/

/-- Prepend a generator onto a same-generator block: `g :: repeatGen a g ~ repeatGen (a + 1) g`.  For
`a ≥ 0` the block extends (definitional); for `a < 0` the leading `g⁻¹` cancels (`consInvCancel`). -/
theorem prependSameGen (gen : ConjugatedRelator) : ∀ scale : Int,
    FreeCrossedModuleEquiv (gen :: repeatGen scale gen) (repeatGen (scale + 1) gen)
  | Int.ofNat _ => FreeCrossedModuleEquiv.refl _
  | Int.negSucc 0 => FreeCrossedModuleEquiv.consInvCancel gen
  | Int.negSucc (predecessor + 1) =>
      FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.consInvCancel gen)
        (FreeCrossedModuleEquiv.refl (repeatGenPos (predecessor + 1) (invGen gen)))

/-- Prepend a formal inverse onto a same-generator block: `g⁻¹ :: repeatGen a g ~ repeatGen (a + (-1)) g`.
For `a > 0` the leading `g` cancels (`invConsCancel`); for `a ≤ 0` the negative block extends. -/
theorem prependInvGen (gen : ConjugatedRelator) : ∀ scale : Int,
    FreeCrossedModuleEquiv (invGen gen :: repeatGen scale gen) (repeatGen (scale + (-1)) gen)
  | Int.ofNat 0 => FreeCrossedModuleEquiv.refl _
  | Int.ofNat (count + 1) =>
      Eq.mp (congrArg (fun target => FreeCrossedModuleEquiv
            (invGen gen :: repeatGen (Int.ofNat (count + 1)) gen) target)
          (congrArg (fun scaleValue => repeatGen scaleValue gen) (intSubNatNatLeftSurplus count 1)).symm)
        (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.invConsCancel gen)
          (FreeCrossedModuleEquiv.refl (repeatGenPos count gen)))
  | Int.negSucc _ => FreeCrossedModuleEquiv.refl _

/-- Float a genE-form past a whole `Int`-scaled block: dispatch on the block's sign to `commutePastBlock`
(a positive block is `repeatGenPos count`, a negative block is `repeatGenPos (·) (invGen block)`). -/
theorem commuteGenEPastBlockList (powerMove : Nat) (signMove : Bool) (powerBlock : Nat)
    (signBlock : Bool) : ∀ scale : Int,
    FreeCrossedModuleEquiv
      (⟨signPowerPos powerMove, 0, signMove⟩ :: repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩)
      (repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩ ++ [⟨signPowerPos powerMove, 0, signMove⟩])
  | Int.ofNat count => commutePastBlock powerMove signMove powerBlock signBlock count
  | Int.negSucc predecessor =>
      commutePastBlock powerMove signMove powerBlock (Bool.not signBlock) (predecessor + 1)

/-- Float a genE-form past a block that sits in front of a tail: `g :: (block ++ tail) ~ block ++
(g :: tail)`.  `commuteGenEPastBlockList` moves `g` to the block's far side, then `listAppendAssociative`
regroups. -/
theorem commutePastBlockIntoTail (powerMove : Nat) (signMove : Bool) (powerBlock : Nat)
    (signBlock : Bool) (scale : Int) (tailWord : PreCrossedElement) :
    FreeCrossedModuleEquiv
      (⟨signPowerPos powerMove, 0, signMove⟩ ::
        (repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩ ++ tailWord))
      (repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩ ++
        (⟨signPowerPos powerMove, 0, signMove⟩ :: tailWord)) :=
  Eq.mp (congrArg (fun rebuilt => FreeCrossedModuleEquiv
        (⟨signPowerPos powerMove, 0, signMove⟩ ::
          (repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩ ++ tailWord)) rebuilt)
      (listAppendAssociative (repeatGen scale ⟨signPowerPos powerBlock, 0, signBlock⟩)
        [⟨signPowerPos powerMove, 0, signMove⟩] tailWord))
    (FreeCrossedModuleEquiv.congrAppend
      (commuteGenEPastBlockList powerMove signMove powerBlock signBlock scale)
      (FreeCrossedModuleEquiv.refl tailWord))

/-- Realize is a right-associated triple concatenation of blocks. -/
theorem realizeRightAssoc (targetOne targetT targetTsq : Int) :
    realizeAugmentationZeroIdentity targetOne targetT targetTsq
      = repeatGen targetOne genE0 ++ (repeatGen targetT genE1 ++ repeatGen targetTsq genE2) :=
  listAppendAssociative (repeatGen targetOne genE0) (repeatGen targetT genE1) (repeatGen targetTsq genE2)

/-- ★ **Prepend a residue-0 genE-form into a realized form** — insert `genE0` (or `genE0⁻¹`) into block 0,
extending/cancelling that block. -/
theorem prependAtResidue0 (sign : Bool) (w : GroupRingZmod3) :
    FreeCrossedModuleEquiv
      (genEformSigned sign ZmodThree.residue0
        :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue0)) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue0)) w).coeffT
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue0)) w).coeffTsq) :=
  match sign with
  | true =>
      let base : FreeCrossedModuleEquiv
          (genE0 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          ((repeatGen (w.coeffOne + 1) genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2) :=
        FreeCrossedModuleEquiv.congrAppend
          (FreeCrossedModuleEquiv.congrAppend (prependSameGen genE0 w.coeffOne)
            (FreeCrossedModuleEquiv.refl (repeatGen w.coeffT genE1)))
          (FreeCrossedModuleEquiv.refl (repeatGen w.coeffTsq genE2))
      let targetEq :
          ((repeatGen (w.coeffOne + 1) genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2)
            = ((repeatGen (1 + w.coeffOne) genE0 ++ repeatGen (0 + w.coeffT) genE1)
                ++ repeatGen (0 + w.coeffTsq) genE2) :=
        (congrArg (fun value =>
              (repeatGen value genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2)
            (intAddComm w.coeffOne 1)).trans
          ((congrArg (fun value =>
                (repeatGen (1 + w.coeffOne) genE0 ++ repeatGen value genE1) ++ repeatGen w.coeffTsq genE2)
              (intZeroAdd w.coeffT).symm).trans
            (congrArg (fun value =>
                (repeatGen (1 + w.coeffOne) genE0 ++ repeatGen (0 + w.coeffT) genE1) ++ repeatGen value genE2)
              (intZeroAdd w.coeffTsq).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (genE0 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq) base
  | false =>
      let base : FreeCrossedModuleEquiv
          (invGen genE0 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          ((repeatGen (w.coeffOne + (-1)) genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2) :=
        FreeCrossedModuleEquiv.congrAppend
          (FreeCrossedModuleEquiv.congrAppend (prependInvGen genE0 w.coeffOne)
            (FreeCrossedModuleEquiv.refl (repeatGen w.coeffT genE1)))
          (FreeCrossedModuleEquiv.refl (repeatGen w.coeffTsq genE2))
      let targetEq :
          ((repeatGen (w.coeffOne + (-1)) genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2)
            = ((repeatGen (-1 + w.coeffOne) genE0 ++ repeatGen (0 + w.coeffT) genE1)
                ++ repeatGen (0 + w.coeffTsq) genE2) :=
        (congrArg (fun value =>
              (repeatGen value genE0 ++ repeatGen w.coeffT genE1) ++ repeatGen w.coeffTsq genE2)
            (intAddComm w.coeffOne (-1))).trans
          ((congrArg (fun value =>
                (repeatGen (-1 + w.coeffOne) genE0 ++ repeatGen value genE1) ++ repeatGen w.coeffTsq genE2)
              (intZeroAdd w.coeffT).symm).trans
            (congrArg (fun value =>
                (repeatGen (-1 + w.coeffOne) genE0 ++ repeatGen (0 + w.coeffT) genE1) ++ repeatGen value genE2)
              (intZeroAdd w.coeffTsq).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (invGen genE0 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq)
        base

/-- ★ **Prepend a residue-1 genE-form into a realized form** — commute `genE1` (or its inverse) past block 0
(`commutePastBlockIntoTail`), then extend/cancel block 1.  Worked in right-associated realize form. -/
theorem prependAtResidue1 (sign : Bool) (w : GroupRingZmod3) :
    FreeCrossedModuleEquiv
      (genEformSigned sign ZmodThree.residue1
        :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue1)) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue1)) w).coeffT
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue1)) w).coeffTsq) :=
  match sign with
  | true =>
      let tail : PreCrossedElement := repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2
      let commuted : FreeCrossedModuleEquiv
          (genE1 :: (repeatGen w.coeffOne genE0 ++ tail))
          (repeatGen w.coeffOne genE0 ++ (genE1 :: tail)) :=
        commutePastBlockIntoTail 1 true 0 true w.coeffOne tail
      let extended : FreeCrossedModuleEquiv (genE1 :: tail)
          (repeatGen (w.coeffT + 1) genE1 ++ repeatGen w.coeffTsq genE2) :=
        FreeCrossedModuleEquiv.congrAppend (prependSameGen genE1 w.coeffT)
          (FreeCrossedModuleEquiv.refl (repeatGen w.coeffTsq genE2))
      let assembled : FreeCrossedModuleEquiv
          (genE1 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          (repeatGen w.coeffOne genE0 ++
            (repeatGen (w.coeffT + 1) genE1 ++ repeatGen w.coeffTsq genE2)) :=
        FreeCrossedModuleEquiv.trans
          (Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
                (repeatGen w.coeffOne genE0 ++ (genE1 :: tail)))
              (congrArg (genE1 :: ·) (realizeRightAssoc w.coeffOne w.coeffT w.coeffTsq)).symm) commuted)
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffOne genE0))
            extended)
      let targetEq :
          (repeatGen w.coeffOne genE0 ++ (repeatGen (w.coeffT + 1) genE1 ++ repeatGen w.coeffTsq genE2))
            = realizeAugmentationZeroIdentity (0 + w.coeffOne) (1 + w.coeffT) (0 + w.coeffTsq) :=
        (congrArg (fun value =>
              repeatGen w.coeffOne genE0 ++ (repeatGen value genE1 ++ repeatGen w.coeffTsq genE2))
            (intAddComm w.coeffT 1)).trans
          ((congrArg (fun value =>
                repeatGen value genE0 ++ (repeatGen (1 + w.coeffT) genE1 ++ repeatGen w.coeffTsq genE2))
              (intZeroAdd w.coeffOne).symm).trans
            ((congrArg (fun value =>
                  repeatGen (0 + w.coeffOne) genE0
                    ++ (repeatGen (1 + w.coeffT) genE1 ++ repeatGen value genE2))
                (intZeroAdd w.coeffTsq).symm).trans
              (realizeRightAssoc (0 + w.coeffOne) (1 + w.coeffT) (0 + w.coeffTsq)).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (genE1 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq)
        assembled
  | false =>
      let tail : PreCrossedElement := repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2
      let commuted : FreeCrossedModuleEquiv
          (invGen genE1 :: (repeatGen w.coeffOne genE0 ++ tail))
          (repeatGen w.coeffOne genE0 ++ (invGen genE1 :: tail)) :=
        commutePastBlockIntoTail 1 false 0 true w.coeffOne tail
      let extended : FreeCrossedModuleEquiv (invGen genE1 :: tail)
          (repeatGen (w.coeffT + (-1)) genE1 ++ repeatGen w.coeffTsq genE2) :=
        FreeCrossedModuleEquiv.congrAppend (prependInvGen genE1 w.coeffT)
          (FreeCrossedModuleEquiv.refl (repeatGen w.coeffTsq genE2))
      let assembled : FreeCrossedModuleEquiv
          (invGen genE1 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          (repeatGen w.coeffOne genE0 ++
            (repeatGen (w.coeffT + (-1)) genE1 ++ repeatGen w.coeffTsq genE2)) :=
        FreeCrossedModuleEquiv.trans
          (Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
                (repeatGen w.coeffOne genE0 ++ (invGen genE1 :: tail)))
              (congrArg (invGen genE1 :: ·) (realizeRightAssoc w.coeffOne w.coeffT w.coeffTsq)).symm)
            commuted)
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffOne genE0))
            extended)
      let targetEq :
          (repeatGen w.coeffOne genE0
              ++ (repeatGen (w.coeffT + (-1)) genE1 ++ repeatGen w.coeffTsq genE2))
            = realizeAugmentationZeroIdentity (0 + w.coeffOne) (-1 + w.coeffT) (0 + w.coeffTsq) :=
        (congrArg (fun value =>
              repeatGen w.coeffOne genE0 ++ (repeatGen value genE1 ++ repeatGen w.coeffTsq genE2))
            (intAddComm w.coeffT (-1))).trans
          ((congrArg (fun value =>
                repeatGen value genE0 ++ (repeatGen (-1 + w.coeffT) genE1 ++ repeatGen w.coeffTsq genE2))
              (intZeroAdd w.coeffOne).symm).trans
            ((congrArg (fun value =>
                  repeatGen (0 + w.coeffOne) genE0
                    ++ (repeatGen (-1 + w.coeffT) genE1 ++ repeatGen value genE2))
                (intZeroAdd w.coeffTsq).symm).trans
              (realizeRightAssoc (0 + w.coeffOne) (-1 + w.coeffT) (0 + w.coeffTsq)).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (invGen genE1 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq)
        assembled

/-- ★ **Prepend a residue-2 genE-form into a realized form** — commute `genE2` (or its inverse) past blocks
0 and 1, then extend/cancel block 2.  Worked in right-associated realize form. -/
theorem prependAtResidue2 (sign : Bool) (w : GroupRingZmod3) :
    FreeCrossedModuleEquiv
      (genEformSigned sign ZmodThree.residue2
        :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue2)) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue2)) w).coeffT
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign ZmodThree.residue2)) w).coeffTsq) :=
  match sign with
  | true =>
      let innerCommuted : FreeCrossedModuleEquiv
          (genE2 :: (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2))
          (repeatGen w.coeffT genE1 ++ (repeatGen (w.coeffTsq + 1) genE2)) :=
        FreeCrossedModuleEquiv.trans
          (commutePastBlockIntoTail 2 true 1 true w.coeffT (repeatGen w.coeffTsq genE2))
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffT genE1))
            (prependSameGen genE2 w.coeffTsq))
      let assembled : FreeCrossedModuleEquiv
          (genE2 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          (repeatGen w.coeffOne genE0 ++
            (repeatGen w.coeffT genE1 ++ repeatGen (w.coeffTsq + 1) genE2)) :=
        FreeCrossedModuleEquiv.trans
          (Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
                (repeatGen w.coeffOne genE0
                  ++ (genE2 :: (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2))))
              (congrArg (genE2 :: ·) (realizeRightAssoc w.coeffOne w.coeffT w.coeffTsq)).symm)
            (commutePastBlockIntoTail 2 true 0 true w.coeffOne
              (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2)))
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffOne genE0))
            innerCommuted)
      let targetEq :
          (repeatGen w.coeffOne genE0 ++ (repeatGen w.coeffT genE1 ++ repeatGen (w.coeffTsq + 1) genE2))
            = realizeAugmentationZeroIdentity (0 + w.coeffOne) (0 + w.coeffT) (1 + w.coeffTsq) :=
        (congrArg (fun value =>
              repeatGen w.coeffOne genE0 ++ (repeatGen w.coeffT genE1 ++ repeatGen value genE2))
            (intAddComm w.coeffTsq 1)).trans
          ((congrArg (fun value =>
                repeatGen value genE0 ++ (repeatGen w.coeffT genE1 ++ repeatGen (1 + w.coeffTsq) genE2))
              (intZeroAdd w.coeffOne).symm).trans
            ((congrArg (fun value =>
                  repeatGen (0 + w.coeffOne) genE0
                    ++ (repeatGen value genE1 ++ repeatGen (1 + w.coeffTsq) genE2))
                (intZeroAdd w.coeffT).symm).trans
              (realizeRightAssoc (0 + w.coeffOne) (0 + w.coeffT) (1 + w.coeffTsq)).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (genE2 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq)
        assembled
  | false =>
      let innerCommuted : FreeCrossedModuleEquiv
          (invGen genE2 :: (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2))
          (repeatGen w.coeffT genE1 ++ (repeatGen (w.coeffTsq + (-1)) genE2)) :=
        FreeCrossedModuleEquiv.trans
          (commutePastBlockIntoTail 2 false 1 true w.coeffT (repeatGen w.coeffTsq genE2))
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffT genE1))
            (prependInvGen genE2 w.coeffTsq))
      let assembled : FreeCrossedModuleEquiv
          (invGen genE2 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
          (repeatGen w.coeffOne genE0 ++
            (repeatGen w.coeffT genE1 ++ repeatGen (w.coeffTsq + (-1)) genE2)) :=
        FreeCrossedModuleEquiv.trans
          (Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
                (repeatGen w.coeffOne genE0
                  ++ (invGen genE2 :: (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2))))
              (congrArg (invGen genE2 :: ·) (realizeRightAssoc w.coeffOne w.coeffT w.coeffTsq)).symm)
            (commutePastBlockIntoTail 2 false 0 true w.coeffOne
              (repeatGen w.coeffT genE1 ++ repeatGen w.coeffTsq genE2)))
          (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl (repeatGen w.coeffOne genE0))
            innerCommuted)
      let targetEq :
          (repeatGen w.coeffOne genE0
              ++ (repeatGen w.coeffT genE1 ++ repeatGen (w.coeffTsq + (-1)) genE2))
            = realizeAugmentationZeroIdentity (0 + w.coeffOne) (0 + w.coeffT) (-1 + w.coeffTsq) :=
        (congrArg (fun value =>
              repeatGen w.coeffOne genE0 ++ (repeatGen w.coeffT genE1 ++ repeatGen value genE2))
            (intAddComm w.coeffTsq (-1))).trans
          ((congrArg (fun value =>
                repeatGen value genE0 ++ (repeatGen w.coeffT genE1 ++ repeatGen (-1 + w.coeffTsq) genE2))
              (intZeroAdd w.coeffOne).symm).trans
            ((congrArg (fun value =>
                  repeatGen (0 + w.coeffOne) genE0
                    ++ (repeatGen value genE1 ++ repeatGen (-1 + w.coeffTsq) genE2))
                (intZeroAdd w.coeffT).symm).trans
              (realizeRightAssoc (0 + w.coeffOne) (0 + w.coeffT) (-1 + w.coeffTsq)).symm))
      Eq.mp (congrArg (fun rhs => FreeCrossedModuleEquiv
            (invGen genE2 :: realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq) rhs) targetEq)
        assembled

/-- ★★ **Insert one genE-form into a realized form** — `[signed genE-form of residue] ++ realize w ~
realize (image genE-form + w)`, dispatching on the residue to the three block insertions. -/
theorem prependGenEForm (sign : Bool) (residue : ZmodThree) (w : GroupRingZmod3) :
    FreeCrossedModuleEquiv
      ([genEformSigned sign residue] ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign residue)) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign residue)) w).coeffT
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign residue)) w).coeffTsq) :=
  match residue with
  | .residue0 => prependAtResidue0 sign w
  | .residue1 => prependAtResidue1 sign w
  | .residue2 => prependAtResidue2 sign w

/-- ★★ **Prepend one well-formed generator into a realized form** — `[⟨w', 0, sign⟩] ++ realize v ~ realize
(image ⟨w', 0, sign⟩ + v)`.  Normalize the head to its genE-form, insert it (`prependGenEForm`), and carry
the image equality back through r4 soundness (`crossedModuleImageRespectsFreeCrossed`). -/
theorem prependGen (conjugatorWord : List SignedLetter) (sign : Bool)
    (over : AllLettersOverGenZero conjugatorWord) (w : GroupRingZmod3) :
    FreeCrossedModuleEquiv
      ([⟨conjugatorWord, 0, sign⟩] ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage ⟨conjugatorWord, 0, sign⟩) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage ⟨conjugatorWord, 0, sign⟩) w).coeffT
        (groupRingAdd (conjugatedRelatorImage ⟨conjugatorWord, 0, sign⟩) w).coeffTsq) :=
  let normalized : FreeCrossedModuleEquiv [⟨conjugatorWord, 0, sign⟩]
      [genEformSigned sign (wordResidue conjugatorWord)] := normalizeGen sign over
  let imageEq :
      conjugatedRelatorImage (genEformSigned sign (wordResidue conjugatorWord))
        = conjugatedRelatorImage ⟨conjugatorWord, 0, sign⟩ :=
    (groupRingAddZero (conjugatedRelatorImage (genEformSigned sign (wordResidue conjugatorWord)))).symm.trans
      ((crossedModuleImageRespectsFreeCrossed normalized).symm.trans
        (groupRingAddZero (conjugatedRelatorImage ⟨conjugatorWord, 0, sign⟩)))
  let bridged : FreeCrossedModuleEquiv
      ([⟨conjugatorWord, 0, sign⟩] ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign (wordResidue conjugatorWord))) w).coeffOne
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign (wordResidue conjugatorWord))) w).coeffT
        (groupRingAdd (conjugatedRelatorImage (genEformSigned sign (wordResidue conjugatorWord))) w).coeffTsq) :=
    FreeCrossedModuleEquiv.trans
      (FreeCrossedModuleEquiv.congrAppend normalized
        (FreeCrossedModuleEquiv.refl (realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)))
      (prependGenEForm sign (wordResidue conjugatorWord) w)
  Eq.mp (congrArg (fun image => FreeCrossedModuleEquiv
        ([⟨conjugatorWord, 0, sign⟩] ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
        (realizeAugmentationZeroIdentity (groupRingAdd image w).coeffOne (groupRingAdd image w).coeffT
          (groupRingAdd image w).coeffTsq)) imageEq) bridged

/-- ★★★ **The append-realize induction** — for every well-formed element and value, `element ++ realize v
~ realize (image element + v)`.  Structural on the element list: `[]` collapses `groupRingZeroAdd`; the
cons peels the head with `prependGen`, folds the tail with the IH, and reassociates the image sum
(`groupRingAddAssoc`).  Setting `v = 0` gives the residual. -/
theorem appendRealize : ∀ (element : PreCrossedElement), AllRelatorIndexZero element →
    AllConjugatorsOverGenZero element → ∀ (w : GroupRingZmod3),
    FreeCrossedModuleEquiv
      (element ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
      (realizeAugmentationZeroIdentity (groupRingAdd (crossedModuleImage element) w).coeffOne
        (groupRingAdd (crossedModuleImage element) w).coeffT
        (groupRingAdd (crossedModuleImage element) w).coeffTsq)
  | [], _, _, w =>
      Eq.mp (congrArg (fun value => FreeCrossedModuleEquiv
            (realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq)
            (realizeAugmentationZeroIdentity value.coeffOne value.coeffT value.coeffTsq))
          (groupRingZeroAdd w).symm)
        (FreeCrossedModuleEquiv.refl (realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq))
  | gen :: rest, .cons _ _ indexIsZero restIndex, .cons _ _ over restOver, w =>
      let genPrime : ConjugatedRelator := ⟨gen.conjugator, 0, gen.isPositive⟩
      let genEq : gen = genPrime :=
        congrArg (fun index => ConjugatedRelator.mk gen.conjugator index gen.isPositive) indexIsZero
      let ih := appendRealize rest restIndex restOver w
      let step1 : FreeCrossedModuleEquiv (genPrime :: (rest ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq))
          (genPrime :: realizeAugmentationZeroIdentity (groupRingAdd (crossedModuleImage rest) w).coeffOne
            (groupRingAdd (crossedModuleImage rest) w).coeffT (groupRingAdd (crossedModuleImage rest) w).coeffTsq) :=
        FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [genPrime]) ih
      let step2 := prependGen gen.conjugator gen.isPositive over (groupRingAdd (crossedModuleImage rest) w)
      let combined := FreeCrossedModuleEquiv.trans step1 step2
      let valueEq :
          groupRingAdd (conjugatedRelatorImage genPrime) (groupRingAdd (crossedModuleImage rest) w)
            = groupRingAdd (crossedModuleImage (gen :: rest)) w :=
        (groupRingAddAssoc (conjugatedRelatorImage genPrime) (crossedModuleImage rest) w).symm
      Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
            (realizeAugmentationZeroIdentity (groupRingAdd (crossedModuleImage (gen :: rest)) w).coeffOne
              (groupRingAdd (crossedModuleImage (gen :: rest)) w).coeffT
              (groupRingAdd (crossedModuleImage (gen :: rest)) w).coeffTsq))
          (congrArg (fun head => head :: (rest ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq))
            genEq.symm))
        (Eq.mp (congrArg (fun value => FreeCrossedModuleEquiv
              (genPrime :: (rest ++ realizeAugmentationZeroIdentity w.coeffOne w.coeffT w.coeffTsq))
              (realizeAugmentationZeroIdentity value.coeffOne value.coeffT value.coeffTsq)) valueEq)
          combined)

/-- ★★★ **THE GENERAL WELL-FORMED RESIDUAL** — every well-formed element reduces, under the group-enriched
relation, to its residue-vector normal form `realize (image x)`.  The measure induction: `appendRealize`
with `v = 0`, then `element ++ realize 0 = element` and `realize (image x + 0) = realize (image x)`.  This
inhabits r5's `freeCrossedModuleNormalFormResidualWellFormed`, closing the Brown–Huebschmann
structure-theorem wall. -/
theorem freeCrossedResidualWellFormed : freeCrossedModuleNormalFormResidualWellFormed :=
  fun element relatorGuard conjugatorGuard =>
    Eq.mp (congrArg (fun value => FreeCrossedModuleEquiv element
          (realizeAugmentationZeroIdentity value.coeffOne value.coeffT value.coeffTsq))
        (groupRingAddZero (crossedModuleImage element)))
      (Eq.mp (congrArg (fun start => FreeCrossedModuleEquiv start
            (realizeAugmentationZeroIdentity (groupRingAdd (crossedModuleImage element) groupRingZero).coeffOne
              (groupRingAdd (crossedModuleImage element) groupRingZero).coeffT
              (groupRingAdd (crossedModuleImage element) groupRingZero).coeffTsq))
          (listAppendNilRight element))
        (appendRealize element relatorGuard conjugatorGuard groupRingZero))

/-! ### B3 — the iso delivered UNCONDITIONALLY -/

/-- ★★★ **THE INSTANCE ISO, UNCONDITIONAL** — feeding the now-proved residual to the shipped r5 assembly
`freeCrossedModulePiTwoIsoOfResidual` produces the `π₂⟨s | s³⟩ ≅ ker(N)` witness bundle with NO hypothesis:
the instance presentation, the enriched congruence, the FIRST machine-checked relation-module iso. -/
def freeCrossedModulePiTwoIso : FreeCrossedModulePiTwoIso :=
  freeCrossedModulePiTwoIsoOfResidual freeCrossedResidualWellFormed

/-- ★★ **The zero-image corollary (unconditional)** — a well-formed element with vanishing image is
`~`-trivial: `image x = 0 ⟹ x ~ []`.  Off the now-proved residual via r5's injectivity bridge. -/
theorem freeCrossedWellFormedImageZeroReduces {element : PreCrossedElement}
    (relatorGuard : AllRelatorIndexZero element) (conjugatorGuard : AllConjugatorsOverGenZero element)
    (imageIsZero : crossedModuleImage element = groupRingZero) :
    FreeCrossedModuleEquiv element ([] : PreCrossedElement) :=
  freeCrossedModuleNormalFormWellFormedImpliesInjectivity freeCrossedResidualWellFormed element
    relatorGuard conjugatorGuard imageIsZero

/-! ### B3/B4 truth probes (self-attacks against the GENERAL theorem) -/

/-- ★ Self-attack 1 — the shuffled commutator through the GENERAL residual reproduces r5's manual reduction
(`image = 0`, `realize 0 0 0 = []`). -/
theorem shuffledCommutatorGeneralResidual :
    FreeCrossedModuleEquiv [genE0, genE1, invGen genE0, invGen genE1] ([] : PreCrossedElement) :=
  freeCrossedWellFormedImageZeroReduces shuffledCommutatorAllRelatorIndexZero
    shuffledCommutatorAllConjugatorsOverGenZero rfl

/-- ★ Self-attack 2 — a maximally out-of-order three-class scramble `[genE2, genE2, genE1, genE1, genE0,
genE0]` normalizes to `realize 2 2 2 = [genE0, genE0, genE1, genE1, genE2, genE2]`. -/
theorem scrambleGeneralResidual :
    FreeCrossedModuleEquiv [genE2, genE2, genE1, genE1, genE0, genE0]
      (realizeAugmentationZeroIdentity
        (crossedModuleImage [genE2, genE2, genE1, genE1, genE0, genE0]).coeffOne
        (crossedModuleImage [genE2, genE2, genE1, genE1, genE0, genE0]).coeffT
        (crossedModuleImage [genE2, genE2, genE1, genE1, genE0, genE0]).coeffTsq) :=
  freeCrossedResidualWellFormed [genE2, genE2, genE1, genE1, genE0, genE0]
    (.cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl .nil))))))
    (.cons _ _ (.consPos _ (.consPos _ .nil)) (.cons _ _ (.consPos _ (.consPos _ .nil))
      (.cons _ _ (.consPos _ .nil) (.cons _ _ (.consPos _ .nil) (.cons _ _ .nil (.cons _ _ .nil .nil))))))

/-- ★ Self-attack 3 — an unreduced negative-conjugator generator reduces through the general residual:
`[⟨s⁻¹ s⁻¹, 0, +⟩]` (residue `2`) lands on `realize (image) = [genE2]`. -/
theorem unreducedGeneralResidual :
    FreeCrossedModuleEquiv [⟨[SignedLetter.neg 0, SignedLetter.neg 0], 0, true⟩]
      (realizeAugmentationZeroIdentity
        (crossedModuleImage [⟨[SignedLetter.neg 0, SignedLetter.neg 0], 0, true⟩]).coeffOne
        (crossedModuleImage [⟨[SignedLetter.neg 0, SignedLetter.neg 0], 0, true⟩]).coeffT
        (crossedModuleImage [⟨[SignedLetter.neg 0, SignedLetter.neg 0], 0, true⟩]).coeffTsq) :=
  freeCrossedResidualWellFormed [⟨[SignedLetter.neg 0, SignedLetter.neg 0], 0, true⟩]
    (.cons _ _ rfl .nil) (.cons _ _ (.consNeg _ (.consNeg _ .nil)) .nil)

/-! ## B4 — the honest r6 ledger

The Brown–Huebschmann general wall is now DISCHARGED; the H2 feed remains r3's `ε(N) = 3`
(`normAugmentationMatchesRelatorShadow`) name-only.  Only the general well-formed residual flips at the
literal delivery `freeCrossedResidualWellFormed`. -/

/-- The r6 ledger, honestly classified against r3's `RelationModuleObligationStatus`. -/
structure FreeCrossedModuleMeasureInductionLedger where
  /-- The atomic layer (self-shift, inverse congruence, genE-form commute, block float). -/
  atomicLayerStatus : RelationModuleObligationStatus
  /-- The NORMALIZE phase inductions (every well-formed generator to its genE-form). -/
  normalizeStatus : RelationModuleObligationStatus
  /-- The single-genE-form insertion into a realized form (`prependGenEForm`). -/
  insertionStatus : RelationModuleObligationStatus
  /-- The GENERAL well-formed residual — the measure induction, r5's remaining wall.  NOW SHIPPED. -/
  generalWellFormedResidualStatus : RelationModuleObligationStatus
  /-- The UNCONDITIONAL instance iso `π₂⟨s | s³⟩ ≅ ker(N)` (`freeCrossedModulePiTwoIso`). -/
  unconditionalIsoStatus : RelationModuleObligationStatus

/-- ★ **The r6 measure-induction ledger.**  Every obligation SHIPPED zero-axiom; ★ the GENERAL well-formed
residual FLIPS to `shipped` (the honest flip AT the literal delivery `freeCrossedResidualWellFormed`), and
the instance iso is delivered UNCONDITIONALLY.  The honest reading: r6 discharges the Brown–Huebschmann
structure-theorem wall of r3/r4/r5 by the recon-confirmed normalize-then-insert measure induction, feeds
r5's shipped `freeCrossedModulePiTwoIsoOfResidual`, and lands the first machine-checked relation-module
isomorphism. -/
def crossedModuleFreeGroupMeasureInductionLedger : FreeCrossedModuleMeasureInductionLedger :=
  { atomicLayerStatus := RelationModuleObligationStatus.shipped
  , normalizeStatus := RelationModuleObligationStatus.shipped
  , insertionStatus := RelationModuleObligationStatus.shipped
  , generalWellFormedResidualStatus := RelationModuleObligationStatus.shipped
  , unconditionalIsoStatus := RelationModuleObligationStatus.shipped }

/-- ★ **The #2199 r6 measure-induction marker.**  Shipped zero-axiom over r5:

  * **B1 (atomic)** — the self-conjugation shift, the formal-inverse congruence, the genE-form commute
    (both-negative via the crossed-inverse anti-congruence), and the block float.
  * **B2 (NORMALIZE)** — every well-formed single generator reduces to its genE-form (`normalizeGen`), via
    two structural power normalizations off the two strips, residue tracked through `wordResidue` (no
    `exponentSum↔residue` bridge).
  * **B3 (the residual + the iso)** — the single-genE-form insertion `prependGenEForm` (commute past prior
    blocks + extend/cancel the home block), the append-realize induction `appendRealize`, ★★★ the GENERAL
    residual `freeCrossedResidualWellFormed` inhabiting r5's `freeCrossedModuleNormalFormResidualWellFormed`,
    the unconditional zero-image corollary, and ★★★ the UNCONDITIONAL instance iso `freeCrossedModulePiTwoIso
    := freeCrossedModulePiTwoIsoOfResidual freeCrossedResidualWellFormed`.
  * **B4 (ledger)** — every obligation SHIPPED; ★ the general well-formed residual FLIPS to `shipped` at the
    literal delivery; the H2 feed stays r3's `ε(N) = 3` name-only, the Brown–Huebschmann wall discharged.

The honest r6 close: `π₂⟨s | s³⟩ ≅ ker(N) ≅ ZZ[G]` (free rank `1`) holds at instance scope with NO
hypothesis — the first machine-checked relation-module isomorphism, the instance presentation, the enriched
congruence.  Read the meaning from THIS docstring (the honest-record convention). -/
def crossedModuleFreeGroupMeasureInductionIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
