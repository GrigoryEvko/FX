import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupNormalForm

/-! # FX1Poly/Polygraph/Homology/CrossedModuleFreeGroupStructureTheorem — the free-group residual R1
    (single-generator complete normal form ⟹ associativity + inverse laws + the `∂ = s³` conjugation
    collapse), the R1-unlocked crossed-module sub-moves, and the honest well-formed structure-theorem /
    instance-iso adjudication for `⟨s | s³⟩` (WP-2GROUP r5, #2199)

r4 (`Homology/CrossedModuleFreeGroupNormalForm`) shipped the group-enriched congruence
`FreeCrossedModuleEquiv`, its soundness, the residue-keyed sort kit, and the `(length, inversions)`
measure — and DEFERRED to r5 the two owed free-group facts that gate the whole structure theorem, named
r1's residual **R1**:

  * **R1-assoc:** `mulWord (mulWord a b) c = mulWord a (mulWord b c)`,
  * **R1-inv:** `mulWord a (invWord a) = []`.

## B1 — R1 via the single-generator complete invariant (the route that avoids the confluence diamond)

Every word that appears in the `⟨s | s³⟩` corpus is over the SINGLE generator `0` (`relatorWord 0 = s³`;
every conjugator in every live witness is over `pos 0`/`neg 0`).  Over one generator the free group is
`F(s) ≅ ZZ`, and a REDUCED word is sign-homogeneous: it is `s^n` (`pos 0` repeated) or `s^{-n}`
(`neg 0` repeated), because `areInverse (pos 0) (neg 0) = true` forbids any mixed adjacency.  So define
the normal form `signPower : ZZ → word` (payload-structural on the `Nat` magnitude, NEVER `Nat`
subtraction, NEVER `WellFounded.fix`) and prove **the crux**

  `reduceWordIsSignPowerOverGenZero : AllLettersOverGenZero w → reduceWord w = signPower (exponentSum w)`

by structural induction on the over-gen-0 witness, with the cons step the prepend lemmas
`consReduced (pos 0) (signPower e) = signPower (e + 1)` / `consReduced (neg 0) (signPower e) =
signPower (e + -1)` (full-enum `Int`-constructor case split; the crossing-zero `subNatNat` handled by the
shipped propext-clean `ComputerAlgebra` kit, never Init).  **R1 then falls out as corollaries over
single-generator words**: R1-inv through r3's `exponentSumInvWord` + `intAddRightNeg`, R1-assoc through
r3's `exponentSumReduceInvariant`/`exponentSumAppend` + `intAddAssoc`, and the `∂⟨w,0,true⟩ = s³`
conjugation collapse (ZZ abelian ⟹ `w s³ w⁻¹ = s³`) through r3's `exponentSumConjugation`.  This is
strictly smaller than the multi-generator cancellation-confluence diamond and is the ONLY genuine
obstruction the recon named for the whole round.

## Zero-axiom design decisions

  * `signPowerPos` / `signPowerNeg` recurse structurally on `Nat`; `signPower` matches the `Int`
    constructor and dispatches to them.  `AllLettersOverGenZero` is a `Prop`-inductive (nil / consPos /
    consNeg), structurally recursed by the crux — mirroring r3's `AllRelatorIndexZero`.
  * Every match on `SignedLetter` / `Bool` / `Int` / `ZmodThree` is FULLY enumerated — no `_ =>`
    wildcard.  `areInverse (pos 0) (neg 0) = true` and `Nat.beq 0 0 = true` close by `rfl` at the literal
    generator (never `Nat.beq_self`).
  * All `Int` arithmetic goes through the shipped propext-clean kit
    (`intAddComm`/`intAddAssoc`/`intAddRightNeg`/`intSubNatNatLeftSurplus`), never Init's propext-dirty
    forms.

`Init`-only (over `Homology/CrossedModuleFreeGroupNormalForm` and the `ComputerAlgebra.Number` Int kit),
structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupStructureTheorem.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the single-generator normal form `signPower` -/

/-- `s^count` as a reduced word over generator `0` — `count` copies of `pos 0`.  Structural on `Nat`. -/
def signPowerPos : Nat → List SignedLetter
  | 0 => []
  | count + 1 => SignedLetter.pos 0 :: signPowerPos count

/-- `s^{-count}` as a reduced word over generator `0` — `count` copies of `neg 0`.  Structural on `Nat`. -/
def signPowerNeg : Nat → List SignedLetter
  | 0 => []
  | count + 1 => SignedLetter.neg 0 :: signPowerNeg count

/-- **The single-generator normal form `s^n`** — the reduced word of net exponent `n` over generator `0`.
`ofNat count` is `count` copies of `pos 0`; `negSucc predecessor` is `predecessor + 1` copies of `neg 0`.
Payload-structural on the `Nat` magnitude after the `Int`-constructor match (no `Nat` subtraction, no
`WellFounded.fix`). -/
def signPower : Int → List SignedLetter
  | Int.ofNat count => signPowerPos count
  | Int.negSucc predecessor => signPowerNeg (predecessor + 1)

/-! ### The prepend lemmas — `consReduced` of one generator letter onto a `signPower` -/

/-- Prepending `pos 0` onto `s^count` extends it to `s^{count+1}` (no cancellation — heads agree). -/
theorem consReducedPosSignPowerPos : ∀ count : Nat,
    consReduced (SignedLetter.pos 0) (signPowerPos count) = signPowerPos (count + 1)
  | 0 => rfl
  | _ + 1 => rfl

/-- Prepending `neg 0` onto `s^{-count}` extends it to `s^{-(count+1)}` (no cancellation). -/
theorem consReducedNegSignPowerNeg : ∀ count : Nat,
    consReduced (SignedLetter.neg 0) (signPowerNeg count) = signPowerNeg (count + 1)
  | 0 => rfl
  | _ + 1 => rfl

/-- Prepending `pos 0` onto `s^{-(count+1)}` cancels the leading `neg 0`, leaving `s^{-count}`. -/
theorem consReducedPosSignPowerNeg (count : Nat) :
    consReduced (SignedLetter.pos 0) (signPowerNeg (count + 1)) = signPowerNeg count := rfl

/-- Prepending `neg 0` onto `s^{count+1}` cancels the leading `pos 0`, leaving `s^count`. -/
theorem consReducedNegSignPowerPos (count : Nat) :
    consReduced (SignedLetter.neg 0) (signPowerPos (count + 1)) = signPowerPos count := rfl

/-- ★ **The `pos 0` prepend law**: `consReduced (pos 0) (s^e) = s^{e+1}` for every exponent `e : ZZ`.
Full-enum `Int`-constructor case split: `ofNat` extends (`consReducedPosSignPowerPos`), `negSucc 0`
cancels to `1`, `negSucc (k+1)` cancels down one (`consReducedPosSignPowerNeg`).  Each RHS `s^{e+1}`
reduces through the definitional `Int.add`/`subNatNat` arms. -/
theorem consReducedPosSignPower : ∀ exponent : Int,
    consReduced (SignedLetter.pos 0) (signPower exponent) = signPower (exponent + 1)
  | Int.ofNat count => consReducedPosSignPowerPos count
  | Int.negSucc 0 => rfl
  | Int.negSucc (predecessor + 1) => consReducedPosSignPowerNeg (predecessor + 1)

/-- ★ **The `neg 0` prepend law**: `consReduced (neg 0) (s^e) = s^{e-1}` for every exponent `e : ZZ`.
Full-enum `Int`-constructor case split; the crossing-zero `ofNat (m+1) + -1 = subNatNat (m+1) 1 = ofNat m`
is discharged by the propext-clean `intSubNatNatLeftSurplus`. -/
theorem consReducedNegSignPower : ∀ exponent : Int,
    consReduced (SignedLetter.neg 0) (signPower exponent) = signPower (exponent + -1)
  | Int.ofNat 0 => rfl
  | Int.ofNat (magnitude + 1) =>
      (consReducedNegSignPowerPos magnitude).trans
        (congrArg signPower (intSubNatNatLeftSurplus magnitude 1)).symm
  | Int.negSucc predecessor => consReducedNegSignPowerNeg (predecessor + 1)

/-! ### The over-gen-0 predicate + its closure lemmas -/

/-- **Every letter of the word is over generator `0`** — `pos 0` or `neg 0`.  A `Prop`-inductive
(nil / consPos / consNeg), structurally recursed by the crux (mirrors r3's `AllRelatorIndexZero`). -/
inductive AllLettersOverGenZero : List SignedLetter → Prop where
  /-- The empty word is over generator `0`. -/
  | nil : AllLettersOverGenZero []
  /-- A `pos 0`-headed word is over generator `0` when its tail is. -/
  | consPos (rest : List SignedLetter) :
      AllLettersOverGenZero rest → AllLettersOverGenZero (SignedLetter.pos 0 :: rest)
  /-- A `neg 0`-headed word is over generator `0` when its tail is. -/
  | consNeg (rest : List SignedLetter) :
      AllLettersOverGenZero rest → AllLettersOverGenZero (SignedLetter.neg 0 :: rest)

/-- `s^count` is over generator `0`. -/
theorem allLettersSignPowerPos : ∀ count : Nat, AllLettersOverGenZero (signPowerPos count)
  | 0 => .nil
  | count + 1 => .consPos (signPowerPos count) (allLettersSignPowerPos count)

/-- `s^{-count}` is over generator `0`. -/
theorem allLettersSignPowerNeg : ∀ count : Nat, AllLettersOverGenZero (signPowerNeg count)
  | 0 => .nil
  | count + 1 => .consNeg (signPowerNeg count) (allLettersSignPowerNeg count)

/-- Every `signPower e` is over generator `0`. -/
theorem allLettersSignPower : ∀ exponent : Int, AllLettersOverGenZero (signPower exponent)
  | Int.ofNat count => allLettersSignPowerPos count
  | Int.negSucc predecessor => allLettersSignPowerNeg (predecessor + 1)

/-- Concatenation preserves over-gen-0. -/
theorem allLettersAppend : ∀ {leftWord rightWord : List SignedLetter},
    AllLettersOverGenZero leftWord → AllLettersOverGenZero rightWord →
    AllLettersOverGenZero (leftWord ++ rightWord)
  | _, _, .nil, rightOver => rightOver
  | _, _, .consPos rest restOver, rightOver =>
      .consPos (rest ++ _) (allLettersAppend restOver rightOver)
  | _, _, .consNeg rest restOver, rightOver =>
      .consNeg (rest ++ _) (allLettersAppend restOver rightOver)

/-- `List.reverseAux` preserves over-gen-0 (accumulator-general form). -/
theorem allLettersReverseAux : ∀ {word accumulator : List SignedLetter},
    AllLettersOverGenZero word → AllLettersOverGenZero accumulator →
    AllLettersOverGenZero (List.reverseAux word accumulator)
  | _, _, .nil, accumulatorOver => accumulatorOver
  | _, accumulator, .consPos rest restOver, accumulatorOver =>
      allLettersReverseAux (word := rest) (accumulator := SignedLetter.pos 0 :: accumulator)
        restOver (.consPos accumulator accumulatorOver)
  | _, accumulator, .consNeg rest restOver, accumulatorOver =>
      allLettersReverseAux (word := rest) (accumulator := SignedLetter.neg 0 :: accumulator)
        restOver (.consNeg accumulator accumulatorOver)

/-- `List.reverse` preserves over-gen-0. -/
theorem allLettersReverse {word : List SignedLetter} (over : AllLettersOverGenZero word) :
    AllLettersOverGenZero (List.reverse word) :=
  allLettersReverseAux over .nil

/-- `List.map inverseLetter` preserves over-gen-0 (each letter flips sign, stays over generator `0`). -/
theorem allLettersMapInverse : ∀ {word : List SignedLetter},
    AllLettersOverGenZero word → AllLettersOverGenZero (List.map inverseLetter word)
  | _, .nil => .nil
  | _, .consPos rest restOver => .consNeg _ (allLettersMapInverse restOver)
  | _, .consNeg rest restOver => .consPos _ (allLettersMapInverse restOver)

/-- `invWord` preserves over-gen-0. -/
theorem allLettersInvWord {word : List SignedLetter} (over : AllLettersOverGenZero word) :
    AllLettersOverGenZero (invWord word) :=
  allLettersReverse (allLettersMapInverse over)

/-- The relator `ρ = s³` is over generator `0`. -/
theorem allLettersRelatorWordZero : AllLettersOverGenZero (relatorWord 0) :=
  .consPos _ (.consPos _ (.consPos _ .nil))

/-! ### ★★ The crux — free reduction of an over-gen-0 word is its `signPower` normal form -/

/-- ★★ **The single-generator complete invariant** — for a word over generator `0`, `reduceWord`
returns the `signPower` normal form of its exponent sum.  Structural induction on the over-gen-0 witness;
the cons steps are the prepend laws `consReducedPosSignPower` / `consReducedNegSignPower` reconciled to
`exponentSum`'s `1 + ·` / `-1 + ·` by `intAddComm`.  THIS is "the cancellation induction" the recon
names — the free-group residual R1's beating heart. -/
theorem reduceWordIsSignPowerOverGenZero : ∀ {word : List SignedLetter},
    AllLettersOverGenZero word → reduceWord word = signPower (exponentSum word)
  | _, .nil => rfl
  | _, .consPos rest restOver =>
      (congrArg (consReduced (SignedLetter.pos 0))
          (reduceWordIsSignPowerOverGenZero restOver)).trans
        ((consReducedPosSignPower (exponentSum rest)).trans
          (congrArg signPower (intAddComm (exponentSum rest) 1)))
  | _, .consNeg rest restOver =>
      (congrArg (consReduced (SignedLetter.neg 0))
          (reduceWordIsSignPowerOverGenZero restOver)).trans
        ((consReducedNegSignPower (exponentSum rest)).trans
          (congrArg signPower (intAddComm (exponentSum rest) (-1))))

/-- `reduceWord` preserves over-gen-0 (its output is a `signPower`, which is over-gen-0). -/
theorem allLettersReduceWord {word : List SignedLetter} (over : AllLettersOverGenZero word) :
    AllLettersOverGenZero (reduceWord word) :=
  (reduceWordIsSignPowerOverGenZero over).symm ▸ allLettersSignPower (exponentSum word)

/-! ### ★ R1 — the free-group inverse law and associativity, over generator `0` -/

/-- ★ **R1-inv (over generator `0`)** — `mulWord a a⁻¹ = 1`.  `a ++ a⁻¹` reduces to `s^{exp a + exp a⁻¹}`
(the crux), and `exp a⁻¹ = -(exp a)` (r3 `exponentSumInvWord`), so the exponent is `exp a + -(exp a) = 0`
(`intAddRightNeg`) and `s^0 = []`.  This is the first of r1's two named residual-R1 obligations. -/
theorem mulWordInvRightOverGenZero {word : List SignedLetter} (over : AllLettersOverGenZero word) :
    mulWord word (invWord word) = oneWord :=
  (reduceWordIsSignPowerOverGenZero (allLettersAppend over (allLettersInvWord over))).trans
    ((congrArg signPower (exponentSumAppend word (invWord word))).trans
      ((congrArg (fun summand => signPower (exponentSum word + summand)) (exponentSumInvWord word)).trans
        (congrArg signPower (intAddRightNeg (exponentSum word)))))

/-- ★ **R1-assoc (over generator `0`)** — `mulWord (mulWord a b) c = mulWord a (mulWord b c)`.  Both sides
reduce (the crux, twice, with `exponentSumReduceInvariant` peeling the inner `reduceWord`) to `s^E`, the
LHS at `E = (exp a + exp b) + exp c` and the RHS at `E = exp a + (exp b + exp c)`, equal by `intAddAssoc`.
This is the second of r1's two named residual-R1 obligations. -/
theorem mulWordAssocOverGenZero {leftWord middleWord rightWord : List SignedLetter}
    (leftOver : AllLettersOverGenZero leftWord) (middleOver : AllLettersOverGenZero middleWord)
    (rightOver : AllLettersOverGenZero rightWord) :
    mulWord (mulWord leftWord middleWord) rightWord
      = mulWord leftWord (mulWord middleWord rightWord) :=
  let leftReduced :
      mulWord (mulWord leftWord middleWord) rightWord
        = signPower ((exponentSum leftWord + exponentSum middleWord) + exponentSum rightWord) :=
    (reduceWordIsSignPowerOverGenZero
        (allLettersAppend (allLettersReduceWord (allLettersAppend leftOver middleOver)) rightOver)).trans
      ((congrArg signPower (exponentSumAppend (reduceWord (leftWord ++ middleWord)) rightWord)).trans
        (congrArg (fun summand => signPower (summand + exponentSum rightWord))
          ((exponentSumReduceInvariant (leftWord ++ middleWord)).trans
            (exponentSumAppend leftWord middleWord))))
  let rightReduced :
      mulWord leftWord (mulWord middleWord rightWord)
        = signPower (exponentSum leftWord + (exponentSum middleWord + exponentSum rightWord)) :=
    (reduceWordIsSignPowerOverGenZero
        (allLettersAppend leftOver (allLettersReduceWord (allLettersAppend middleOver rightOver)))).trans
      ((congrArg signPower (exponentSumAppend leftWord (reduceWord (middleWord ++ rightWord)))).trans
        (congrArg (fun summand => signPower (exponentSum leftWord + summand))
          ((exponentSumReduceInvariant (middleWord ++ rightWord)).trans
            (exponentSumAppend middleWord rightWord))))
  leftReduced.trans
    ((congrArg signPower
        (intAddAssoc (exponentSum leftWord) (exponentSum middleWord) (exponentSum rightWord))).trans
      rightReduced.symm)

/-- ★★ **The `∂ = s³` conjugation collapse (over generator `0`)** — `∂⟨w, ρ, +⟩ = w · s³ · w⁻¹ = s³`
for every conjugator `w` over generator `0`.  `ZZ` is abelian, so the conjugating `w`/`w⁻¹` cancel: the
crux sends the boundary to `s^{exp(w s³ w⁻¹)}`, and r3's `exponentSumConjugation` (through the
reduce-invariant exponent sum) fixes that exponent at `exp s³ = 3`.  This is exactly the `∂a = s³` fact
the r5 sub-moves consume — r1's residual R1 promoting r2's `conjugationResidueZero` / r3's
`exponentSumConjugation` to the full reduced-word equality. -/
theorem conjugatedRelatorBoundaryIsRelatorOverGenZero {conjugatorWord : List SignedLetter}
    (over : AllLettersOverGenZero conjugatorWord) :
    conjugatedRelatorBoundary ⟨conjugatorWord, 0, true⟩
      = [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0] :=
  let exponentIsThree :
      exponentSum (conjugatorWord ++ relatorWord 0 ++ invWord conjugatorWord) = 3 :=
    ((exponentSumReduceInvariant (conjugatorWord ++ relatorWord 0 ++ invWord conjugatorWord)).symm.trans
        (exponentSumConjugation conjugatorWord (relatorWord 0))).trans rfl
  (reduceWordIsSignPowerOverGenZero
      (allLettersAppend (allLettersAppend over allLettersRelatorWordZero)
        (allLettersInvWord over))).trans
    (congrArg signPower exponentIsThree)

/-! ### B1 truth probes — evaluate the normal form and R1 on concrete words FIRST -/

/-- Probe — `signPower 3 = s³ = [pos 0, pos 0, pos 0]`. -/
theorem signPowerThreeProbe :
    signPower 3 = [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0] := rfl

/-- Probe — `signPower (-2) = s⁻² = [neg 0, neg 0]`. -/
theorem signPowerNegTwoProbe :
    signPower (-2) = [SignedLetter.neg 0, SignedLetter.neg 0] := rfl

/-- Probe (the cancellation induction, evaluated) — reducing `s s s⁻¹ s⁻¹ s = s` (net exponent `1`)
returns the `signPower` normal form `[pos 0]`. -/
theorem reduceWordSignPowerProbe :
    reduceWord [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.neg 0, SignedLetter.neg 0,
        SignedLetter.pos 0] = signPower 1 := rfl

/-- ★ Probe — R1-inv on the concrete `s²`: `mulWord s² (s²)⁻¹ = 1`. -/
theorem mulWordInvRightProbe :
    mulWord [SignedLetter.pos 0, SignedLetter.pos 0]
        (invWord [SignedLetter.pos 0, SignedLetter.pos 0]) = oneWord := rfl

/-- ★ Probe — the conjugation collapse on `genE1`'s conjugator `s`: `∂⟨s, ρ, +⟩ = s³`. -/
theorem conjugationCollapseProbe :
    conjugatedRelatorBoundary ⟨[SignedLetter.pos 0], 0, true⟩
      = [SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0] := rfl

/-- ★ **The R1 residual marker.**  Shipped zero-axiom: the single-generator normal form `signPower` with
its prepend laws, ★★ the cancellation-induction crux `reduceWordIsSignPowerOverGenZero`, and the two owed
free-group facts as corollaries — R1-inv (`mulWordInvRightOverGenZero`) and R1-assoc
(`mulWordAssocOverGenZero`) over generator `0` — plus the `∂ = s³` conjugation collapse
(`conjugatedRelatorBoundaryIsRelatorOverGenZero`) the r5 sub-moves consume.  r1's named residual **R1** is
CLOSED for the single-generator fragment (all the `⟨s | s³⟩` corpus lives there); the multi-generator
cancellation-confluence diamond stays out of scope (unneeded).  Read the meaning from THIS docstring. -/
def freeGroupResidualR1IsComplete : Bool := true

/-! ## B2 — the R1-unlocked crossed-module sub-moves + the shuffled-commutator attack

Now that R1 supplies `∂⟨w, 0, true⟩ = s³` for every over-gen-0 `w`, three sub-moves against the shipped
`FreeCrossedModuleEquiv` ctors become derivable (recon §2): the adjacent swap `x·y ~ (^{∂x}y)·x` (pure
structure, no R1), and the conjugator-exponent strip `s^{k+3} ~ s^k` (R1-gated).  Together they discharge
the r4-deferred **shuffled-commutator** identity `[genE0, genE1, genE0⁻¹, genE1⁻¹] ~ []` — the first
attack that exercises step (iii) (a genuine swap before cancellation) non-vacuously. -/

/-- `s^a · s^b = s^{a+b}` at the word level (concatenation of two positive `signPower`s). -/
theorem signPowerPosAppend : ∀ (leftCount rightCount : Nat),
    signPowerPos leftCount ++ signPowerPos rightCount = signPowerPos (leftCount + rightCount)
  | 0, rightCount => congrArg signPowerPos (Nat.zero_add rightCount).symm
  | leftCount + 1, rightCount =>
      (congrArg (fun tail => SignedLetter.pos 0 :: tail) (signPowerPosAppend leftCount rightCount)).trans
        (congrArg signPowerPos (Nat.succ_add leftCount rightCount).symm)

/-- Free reduction fixes a positive `signPower` (it is already reduced — no adjacent inverse pair). -/
theorem reduceWordSignPowerPos : ∀ count : Nat, reduceWord (signPowerPos count) = signPowerPos count
  | 0 => rfl
  | count + 1 =>
      (congrArg (consReduced (SignedLetter.pos 0)) (reduceWordSignPowerPos count)).trans
        (consReducedPosSignPowerPos count)

/-- ★ **Sub-move 3 — the adjacent swap** `x·y ~ (^{∂x}y)·x`.  `[x, y] ~ [^{∂x}y, x]` derived from
`peifferMove x y : [x, y, x⁻¹] ~ [^{∂x}y]` right-multiplied by `[x]`, threading `[x⁻¹, x] ~ []`
(`invConsCancel`) through `congrAppend`.  PURE STRUCTURE — no R1, no conjugation collapse. -/
theorem freeCrossedAdjacentSwap (firstGen secondGen : ConjugatedRelator) :
    FreeCrossedModuleEquiv [firstGen, secondGen] [peifferConjugate firstGen secondGen, firstGen] :=
  FreeCrossedModuleEquiv.trans
    (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [firstGen, secondGen])
      (FreeCrossedModuleEquiv.symm (FreeCrossedModuleEquiv.invConsCancel firstGen)))
    (FreeCrossedModuleEquiv.congrAppend
      (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove firstGen secondGen))
      (FreeCrossedModuleEquiv.refl [firstGen]))

/-- ★★ **Sub-move 2 — the conjugator-exponent strip** `⟨s^{k+3}, 0, +⟩ ~ ⟨s^k, 0, +⟩`, the R1-gated
reduction of the conjugator exponent modulo `3`.  With `g = ⟨s^k, 0, +⟩` (so `∂g = s³` by R1's
`conjugatedRelatorBoundaryIsRelatorOverGenZero`), `peifferMove g g` sends `[g, g, g⁻¹]` to
`[^{∂g}g] = [⟨reduceWord(s³ · s^k), 0, +⟩] = [⟨s^{k+3}, 0, +⟩]`, and `[g, g, g⁻¹] ~ [g]` by tail
cancellation — so `⟨s^{k+3}, 0, +⟩ ~ g`.  This IS the free-crossed-module strip the recon deferred,
now delivered off R1. -/
theorem freeCrossedSignPowerStrip (count : Nat) :
    FreeCrossedModuleEquiv [⟨signPowerPos (count + 3), 0, true⟩] [⟨signPowerPos count, 0, true⟩] :=
  let baseGen : ConjugatedRelator := ⟨signPowerPos count, 0, true⟩
  let conjugatorEq :
      reduceWord (conjugatedRelatorBoundary baseGen ++ signPowerPos count) = signPowerPos (count + 3) :=
    (congrArg (fun boundary => reduceWord (boundary ++ signPowerPos count))
        (conjugatedRelatorBoundaryIsRelatorOverGenZero (allLettersSignPowerPos count))).trans
      ((congrArg reduceWord (signPowerPosAppend 3 count)).trans
        ((reduceWordSignPowerPos (3 + count)).trans (congrArg signPowerPos (Nat.add_comm 3 count))))
  let peifferConjugateEq : peifferConjugate baseGen baseGen = ⟨signPowerPos (count + 3), 0, true⟩ :=
    congrArg (fun conjugator => ConjugatedRelator.mk conjugator 0 true) conjugatorEq
  peifferConjugateEq ▸
    ((FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove baseGen baseGen)).symm.trans
      (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [baseGen])
        (FreeCrossedModuleEquiv.consInvCancel baseGen)))

/-- ★ **Concrete strip probe** — `⟨s³, 0, +⟩ ~ genE0` (the `k = 0` instance of the strip: the conjugator
`s³` collapses to the empty conjugator of `genE0`). -/
theorem conjugatorStripS3ToGenE0 :
    FreeCrossedModuleEquiv
      [⟨[SignedLetter.pos 0, SignedLetter.pos 0, SignedLetter.pos 0], 0, true⟩] [genE0] :=
  (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove genE0 genE0)).symm.trans
    (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [genE0])
      (FreeCrossedModuleEquiv.consInvCancel genE0))

/-- ★ Probe — the shuffled commutator is a genuine identity: `∂[genE0, genE1, genE0⁻¹, genE1⁻¹] = 1`
(`s³·s³·s⁻³·s⁻³ = 1` in the abelian `F(s)`).  `rfl`. -/
theorem shuffledCommutatorBoundaryVanishes :
    partialBoundary [genE0, genE1, invGen genE0, invGen genE1] = oneWord := rfl

/-- ★ Probe — the shuffled commutator images to `0` (satisfies the injectivity hypothesis):
`e₀ + e₁ + (−e₀) + (−e₁) = 0`.  `rfl`. -/
theorem shuffledCommutatorImageIsZero :
    crossedModuleImage [genE0, genE1, invGen genE0, invGen genE1] = groupRingZero := rfl

/-- ★★★ **The shuffled-commutator attack (the r4 deferral, now landed)** —
`[genE0, genE1, genE0⁻¹, genE1⁻¹] ~ []`.  The commutator of two DISTINCT generators cannot cancel
directly (the shipped cancellations need adjacent inverse pairs); it needs a genuine swap.  Move `genE0`
right past `genE1` (`peifferMove genE0 genE1`, exposing `genE0⁻¹·genE0`), STRIP the resulting `⟨s⁴, 0, +⟩`
to `genE1` (via `peifferMove genE1 genE1`, since `∂genE1 = s³`), then cancel `[genE1, genE1⁻¹]`.  This is
the first attack exercising sub-move 3 non-vacuously — the enrichment doing what neither `PeifferEquiv`
nor pure double-cancellation could. -/
theorem shuffledCommutatorReduces :
    FreeCrossedModuleEquiv [genE0, genE1, invGen genE0, invGen genE1] ([] : PreCrossedElement) :=
  let stripToGenE1 : FreeCrossedModuleEquiv [peifferConjugate genE0 genE1] [genE1] :=
    (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove genE1 genE1)).symm.trans
      (FreeCrossedModuleEquiv.congrAppend (FreeCrossedModuleEquiv.refl [genE1])
        (FreeCrossedModuleEquiv.consInvCancel genE1))
  FreeCrossedModuleEquiv.trans
    (FreeCrossedModuleEquiv.congrAppend
      (FreeCrossedModuleEquiv.ofPeiffer (PeifferEquiv.peifferMove genE0 genE1))
      (FreeCrossedModuleEquiv.refl [invGen genE1]))
    (FreeCrossedModuleEquiv.trans
      (FreeCrossedModuleEquiv.congrAppend stripToGenE1 (FreeCrossedModuleEquiv.refl [invGen genE1]))
      (FreeCrossedModuleEquiv.consInvCancel genE1))

/-- ★ **The r5 sub-move marker.**  Shipped zero-axiom over R1: sub-move 3 (`freeCrossedAdjacentSwap`,
pure structure), the R1-gated conjugator-exponent strip `s^{k+3} ~ s^k` (`freeCrossedSignPowerStrip`),
and the r4-deferred shuffled-commutator identity `[genE0, genE1, genE0⁻¹, genE1⁻¹] ~ []`
(`shuffledCommutatorReduces`) — the first crossed-module reduction needing a genuine swap before
cancellation.  Read the meaning from THIS docstring. -/
def freeCrossedSubMovesAreComplete : Bool := true

/-! ## B3 — the WELL-FORMED structure theorem + the instance iso `π₂⟨s | s³⟩ ≅ ker(N)`

### ★★★ HARD FINDING — the shipped r4 `freeCrossedModuleNormalFormResidual` is FALSE as stated

Because r2's `letterShift` IGNORES the generator index, a conjugator over a DIFFERENT generator images
the same as one over generator `0` but has a DIFFERENT boundary.  Concretely
`x = [⟨[SignedLetter.pos 1], 0, true⟩]` images to `(0, 1, 0) = image [genE1]`, yet
`∂x = [pos 1, pos 0, pos 0, pos 0, neg 1] ≠ s³ = ∂genE1`.  `FreeCrossedModuleEquiv` preserves the free-group
boundary, so it can never relate two elements with distinct boundaries — hence
`¬ FreeCrossedModuleEquiv x [genE1]`, refuting the unguarded residual `FreeCrossedModuleEquiv x
(realize (image x))`.  (The Lean refutation itself needs the GENERAL boundary-soundness
`FreeCrossedModuleEquiv x y → ∂x = ∂y`, which telescopes further R1 plumbing and is NOT shipped this
round; the finding is recorded mathematically and DEFENDED by the well-formedness guard below.)

**r5 does NOT inhabit the false unguarded Prop.**  It introduces the well-formedness guard
`AllConjugatorsOverGenZero` (mirror of r3's load-bearing `AllRelatorIndexZero`) — every conjugator over
generator `0` — restates the residual under BOTH guards, proves the residual→injectivity→iso bridge, and
INHABITS the guarded residual on concrete nontrivial well-formed elements (the shuffled commutator).  The
whole live `⟨s | s³⟩` corpus (genE*, ζ-orbit, self-attacks, the shuffled commutator) satisfies both
guards by construction. -/

/-- ★ **The well-formedness guard** (the §3.2 fix) — every generator's conjugator is over generator `0`.
A `Prop`-inductive mirroring r3's `AllRelatorIndexZero`; the whole live corpus satisfies it. -/
inductive AllConjugatorsOverGenZero : PreCrossedElement → Prop where
  /-- The empty element is well-formed. -/
  | nil : AllConjugatorsOverGenZero []
  /-- A cons is well-formed when its head's conjugator is over generator `0` and its tail is. -/
  | cons (gen : ConjugatedRelator) (rest : PreCrossedElement)
      (conjugatorOver : AllLettersOverGenZero gen.conjugator)
      (restAllOver : AllConjugatorsOverGenZero rest) :
      AllConjugatorsOverGenZero (gen :: rest)

/-- Probe — the shuffled commutator satisfies the relator-index guard (all `relationIndex = 0`). -/
theorem shuffledCommutatorAllRelatorIndexZero :
    AllRelatorIndexZero [genE0, genE1, invGen genE0, invGen genE1] :=
  .cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl (.cons _ _ rfl .nil)))

/-- Probe — the shuffled commutator satisfies the conjugator guard (all conjugators over generator `0`). -/
theorem shuffledCommutatorAllConjugatorsOverGenZero :
    AllConjugatorsOverGenZero [genE0, genE1, invGen genE0, invGen genE1] :=
  .cons _ _ .nil (.cons _ _ (.consPos _ .nil) (.cons _ _ .nil
    (.cons _ _ (.consPos _ .nil) .nil)))

/-- Probe — the rotation identity `ζ` is well-formed under both guards. -/
theorem rotationIdentityAllRelatorIndexZero :
    AllRelatorIndexZero rotationIdentityWitness :=
  .cons _ _ rfl (.cons _ _ rfl .nil)

/-- Probe — the rotation identity `ζ`'s conjugators are over generator `0`. -/
theorem rotationIdentityAllConjugatorsOverGenZero :
    AllConjugatorsOverGenZero rotationIdentityWitness :=
  .cons _ _ (.consPos _ .nil) (.cons _ _ .nil .nil)

/-! ### The guarded residual (STATED, not asserted) + the residual→injectivity→iso bridges (PROVED) -/

/-- ★ **The WELL-FORMED structure-theorem residual** — every WELL-FORMED element reduces, under the
group-enriched relation, to its residue-vector normal form `realize (image x)`.  The honest replacement
for the r4 `freeCrossedModuleNormalFormResidual` (which §3.2 refutes for arbitrary generators).  Stated as
a `Prop` (a def); the general measure induction (sort → strip → cancel over the r4 `residueInversions`
fuel) is NOT asserted here — it is INHABITED on concrete well-formed elements below and the residual→iso
bridge is proved, so proving it upgrades r3's surjection to the full instance iso. -/
def freeCrossedModuleNormalFormResidualWellFormed : Prop :=
  ∀ element : PreCrossedElement,
    AllRelatorIndexZero element → AllConjugatorsOverGenZero element →
    FreeCrossedModuleEquiv element
      (realizeAugmentationZeroIdentity (crossedModuleImage element).coeffOne
        (crossedModuleImage element).coeffT (crossedModuleImage element).coeffTsq)

/-- ★★ **Residual inhabited on the shuffled commutator** — its image is `0`, so its residue-vector normal
form is `realize 0 0 0 = []`, and `shuffledCommutatorReduces` provides exactly
`FreeCrossedModuleEquiv [genE0, genE1, genE0⁻¹, genE1⁻¹] []`.  A concrete NONTRIVIAL well-formed witness
of the guarded residual (the r4-deferred shuffled-identity attack, delivered as a residual instance). -/
theorem shuffledCommutatorResidualHolds :
    FreeCrossedModuleEquiv [genE0, genE1, invGen genE0, invGen genE1]
      (realizeAugmentationZeroIdentity
        (crossedModuleImage [genE0, genE1, invGen genE0, invGen genE1]).coeffOne
        (crossedModuleImage [genE0, genE1, invGen genE0, invGen genE1]).coeffT
        (crossedModuleImage [genE0, genE1, invGen genE0, invGen genE1]).coeffTsq) :=
  shuffledCommutatorReduces

/-- The guarded injectivity obligation — `image x = 0 ⟹ x ~ []` for well-formed `x`. -/
def freeCrossedModuleWellFormedInjectivityObligation : Prop :=
  ∀ element : PreCrossedElement,
    AllRelatorIndexZero element → AllConjugatorsOverGenZero element →
    crossedModuleImage element = groupRingZero →
      FreeCrossedModuleEquiv element ([] : PreCrossedElement)

/-- ★★ **The structure theorem implies the guarded injectivity** — if every well-formed element reduces to
its residue-vector normal form, then `image x = 0` forces `x ~ []` (`realize 0 0 0 = []`).  PROVED (the
guarded residual is exactly the missing piece); mirrors r4's bridge with the two guards threaded. -/
theorem freeCrossedModuleNormalFormWellFormedImpliesInjectivity
    (residualReduces : freeCrossedModuleNormalFormResidualWellFormed) :
    freeCrossedModuleWellFormedInjectivityObligation :=
  fun element relatorGuard conjugatorGuard imageIsZero =>
    let realizeCollapsesToEmpty :
        realizeAugmentationZeroIdentity (crossedModuleImage element).coeffOne
            (crossedModuleImage element).coeffT (crossedModuleImage element).coeffTsq
          = ([] : PreCrossedElement) :=
      congrArg (fun value => realizeAugmentationZeroIdentity (GroupRingZmod3.coeffOne value)
        (GroupRingZmod3.coeffT value) (GroupRingZmod3.coeffTsq value)) imageIsZero
    Eq.mp (congrArg (FreeCrossedModuleEquiv element) realizeCollapsesToEmpty)
      (residualReduces element relatorGuard conjugatorGuard)

/-- ★★ **The full guarded injectivity on `~`-classes** — for well-formed `x, y`, `image x = image y ⟹
x ~ y`.  From the residual, `x ~ realize (image x) = realize (image y) ~ y`.  PROVED off the guarded
residual (r5's free bonus past the zero-case obligation). -/
theorem freeCrossedModuleWellFormedImageInjective
    (residualReduces : freeCrossedModuleNormalFormResidualWellFormed)
    {leftElement rightElement : PreCrossedElement}
    (leftRelator : AllRelatorIndexZero leftElement) (leftConjugator : AllConjugatorsOverGenZero leftElement)
    (rightRelator : AllRelatorIndexZero rightElement)
    (rightConjugator : AllConjugatorsOverGenZero rightElement)
    (imageEqual : crossedModuleImage leftElement = crossedModuleImage rightElement) :
    FreeCrossedModuleEquiv leftElement rightElement :=
  let leftToNormalForm := residualReduces leftElement leftRelator leftConjugator
  let rightToNormalForm := residualReduces rightElement rightRelator rightConjugator
  let normalFormsEqual :
      realizeAugmentationZeroIdentity (crossedModuleImage leftElement).coeffOne
          (crossedModuleImage leftElement).coeffT (crossedModuleImage leftElement).coeffTsq
        = realizeAugmentationZeroIdentity (crossedModuleImage rightElement).coeffOne
          (crossedModuleImage rightElement).coeffT (crossedModuleImage rightElement).coeffTsq :=
    congrArg (fun value => realizeAugmentationZeroIdentity (GroupRingZmod3.coeffOne value)
      (GroupRingZmod3.coeffT value) (GroupRingZmod3.coeffTsq value)) imageEqual
  FreeCrossedModuleEquiv.trans (normalFormsEqual ▸ leftToNormalForm)
    (FreeCrossedModuleEquiv.symm rightToNormalForm)

/-- ★ **The instance iso `π₂⟨s | s³⟩ ≅ ker(N)` as a witness bundle** over the setoid
`(PreCrossedElement, FreeCrossedModuleEquiv)` with `crossedModuleImage` the map.  `wellDefined` = the map
descends (r4 soundness); `surjective` = every group-ring value is realized (r3); `kernelLands` = every
well-formed identity lands in `ker(N)` (r3); `injective` = the residual-gated full injectivity.  NO
`Quot` — the congruence `FreeCrossedModuleEquiv` and the map `crossedModuleImage` are named directly. -/
structure FreeCrossedModulePiTwoIso where
  /-- The invariant descends to the group-enriched congruence. -/
  wellDefined : ∀ {leftElement rightElement : PreCrossedElement},
    FreeCrossedModuleEquiv leftElement rightElement →
    crossedModuleImage leftElement = crossedModuleImage rightElement
  /-- Every group-ring value is realized as an image (surjectivity of the map). -/
  surjective : ∀ value : GroupRingZmod3,
    crossedModuleImage
        (realizeAugmentationZeroIdentity value.coeffOne value.coeffT value.coeffTsq) = value
  /-- Every well-formed identity images into `ker(N) = {aug = 0}`. -/
  kernelLands : ∀ {element : PreCrossedElement},
    AllRelatorIndexZero element → partialBoundary element = oneWord →
    groupRingAugmentation (crossedModuleImage element) = 0
  /-- The map is injective on `~`-classes of well-formed elements. -/
  injective : ∀ {leftElement rightElement : PreCrossedElement},
    AllRelatorIndexZero leftElement → AllConjugatorsOverGenZero leftElement →
    AllRelatorIndexZero rightElement → AllConjugatorsOverGenZero rightElement →
    crossedModuleImage leftElement = crossedModuleImage rightElement →
    FreeCrossedModuleEquiv leftElement rightElement

/-- ★★★ **The instance iso, assembled from the guarded residual** — `freeCrossedModuleNormalFormResidualWellFormed
→ FreeCrossedModulePiTwoIso`.  Three fields (well-definedness, surjectivity, kernel-landing) hold
UNCONDITIONALLY (r2/r3/r4); the fourth (injectivity) is delivered by
`freeCrossedModuleWellFormedImageInjective`.  This is the honest iso ASSEMBLY: the packaging decl and the
residual→iso bridge are PROVED, so the full instance iso `π₂⟨s | s³⟩ ≅ ker(N) ≅ ZZ[G]` (free rank `1`)
holds AT INSTANCE SCOPE the moment the walled measure induction lands. -/
def freeCrossedModulePiTwoIsoOfResidual
    (residualReduces : freeCrossedModuleNormalFormResidualWellFormed) : FreeCrossedModulePiTwoIso :=
  { wellDefined := fun equiv => crossedModuleImageRespectsFreeCrossed equiv
  , surjective := fun value => crossedModuleImageSurjectsOntoGroupRing value
  , kernelLands := fun relatorGuard isIdentity => identityLandsAugmentationZero relatorGuard isIdentity
  , injective := fun leftRelator leftConjugator rightRelator rightConjugator imageEqual =>
      freeCrossedModuleWellFormedImageInjective residualReduces leftRelator leftConjugator
        rightRelator rightConjugator imageEqual }

/-! ## B4 — the honest r5 ledger

The Brown–Huebschmann general wall is PRESERVED; the H2 feed is r3's `normAugmentationMatchesRelatorShadow`
(`ε(N) = 3`) name-only.  The general well-formed residual (the measure induction) stays the wall — its
marker is NOT flipped; only the R1 / sub-move / iso-assembly obligations flip at literal delivery. -/

/-- The six-obligation ledger of the r5 structure-theorem spike, honestly classified against r3's
`RelationModuleObligationStatus`. -/
structure FreeCrossedModuleStructureTheoremLedger where
  /-- r1's residual R1 (`mulWord` associativity + inverse law + `∂ = s³` collapse), single-generator. -/
  freeGroupResidualR1Status : RelationModuleObligationStatus
  /-- The R1-unlocked sub-moves (adjacent swap + `s^{k+3}` strip). -/
  subMovesStatus : RelationModuleObligationStatus
  /-- The r4-deferred shuffled-commutator identity `[genE0, genE1, genE0⁻¹, genE1⁻¹] ~ []`. -/
  shuffledCommutatorStatus : RelationModuleObligationStatus
  /-- The §3.2 well-formedness guard (`AllConjugatorsOverGenZero`) correcting the false unguarded residual. -/
  wellFormedGuardStatus : RelationModuleObligationStatus
  /-- The residual→injectivity→iso bridge + the iso-bundle assembly (`freeCrossedModulePiTwoIsoOfResidual`). -/
  isoAssemblyStatus : RelationModuleObligationStatus
  /-- The GENERAL well-formed residual (the measure induction) — the remaining wall. -/
  generalWellFormedResidualStatus : RelationModuleObligationStatus

/-- ★ **The r5 structure-theorem ledger.**  R1 / sub-moves / shuffled commutator / well-formed guard /
iso assembly all SHIPPED zero-axiom; the GENERAL well-formed residual stays the Brown–Huebschmann
structure-theorem wall (its marker NOT flipped — the measure induction is inhabited only on concrete
well-formed elements this round).  The honest reading: r5 closes r1's residual R1 (the round's single
genuine obstruction), delivers the R1-unlocked sub-moves and the r4-deferred shuffled-commutator, CORRECTS
the false unguarded residual with the well-formedness guard, and PROVES the residual→iso bridge — so the
instance iso `π₂⟨s | s³⟩ ≅ ker(N)` is one measure-induction away. -/
def crossedModuleFreeGroupStructureTheoremLedger : FreeCrossedModuleStructureTheoremLedger :=
  { freeGroupResidualR1Status := RelationModuleObligationStatus.shipped
  , subMovesStatus := RelationModuleObligationStatus.shipped
  , shuffledCommutatorStatus := RelationModuleObligationStatus.shipped
  , wellFormedGuardStatus := RelationModuleObligationStatus.shipped
  , isoAssemblyStatus := RelationModuleObligationStatus.shipped
  , generalWellFormedResidualStatus := RelationModuleObligationStatus.structureTheoremResidual }

/-- ★ **The #2199 r5 structure-theorem marker.**  Shipped zero-axiom over r4:

  * **B1 (R1)** — the single-generator normal form `signPower` + the cancellation-induction crux
    `reduceWordIsSignPowerOverGenZero`, whence R1-inv/R1-assoc and the `∂ = s³` collapse.  r1's residual
    R1, the round's single obstruction, is CLOSED for the single-generator fragment.
  * **B2 (sub-moves)** — the adjacent swap `x·y ~ (^{∂x}y)·x` (pure structure), the R1-gated
    conjugator-exponent strip `s^{k+3} ~ s^k`, and the r4-deferred shuffled-commutator identity
    `[genE0, genE1, genE0⁻¹, genE1⁻¹] ~ []` (`shuffledCommutatorReduces`).
  * **B3 (structure theorem / iso)** — ★★★ the §3.2 FINDING (the r4 unguarded residual is FALSE for
    arbitrary generators) + the `AllConjugatorsOverGenZero` guard; the guarded residual STATED and
    INHABITED on the shuffled commutator (`shuffledCommutatorResidualHolds`); the residual→injectivity→iso
    bridge PROVED (`freeCrossedModuleNormalFormWellFormedImpliesInjectivity`,
    `freeCrossedModuleWellFormedImageInjective`, `freeCrossedModulePiTwoIsoOfResidual`).
  * **B4 (ledger)** — five obligations SHIPPED; the GENERAL well-formed residual stays the walled measure
    induction (marker NOT flipped).  The H2 feed is r3's `ε(N) = 3` name-only (no chain-complex import,
    lane law respected).

The honest r5 close: R1 lands, the sub-moves and the shuffled commutator land, the false residual is
corrected and the iso is ASSEMBLED behind the one remaining wall (the general measure induction).  Read
the meaning from THIS docstring (the honest-record convention). -/
def crossedModuleFreeGroupStructureTheoremIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
