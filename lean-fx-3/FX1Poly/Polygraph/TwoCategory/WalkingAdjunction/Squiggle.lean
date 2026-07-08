/-! # The ORIENTED squiggle normal-form carrier (RV Def 3.1.2) — SQ-1

This file ships the *data* of the Riehl–Verity oriented squiggle normal form (arXiv:1310.8279 §3.1,
Def 3.1.2): a strictly-undulating level string in which every level carries an `L`/`R` port orientation.
It is a standalone, `Init`-only, zero-axiom carrier: an inductive `PortSide`, a `SquiggleLetter`
record `(level, side)`, the list-based `SquiggleString`, a decidable strict-undulation well-formedness
predicate, and a hand-rolled `DecidableEq` (the decision procedure on normal forms).

## What this carrier is — and the honest wall in front of its *evaluator*

The carrier here is genuinely *oriented*: `SquiggleLetter.side : PortSide` records the boundary object
(`L` or `R`) each level sits on, exactly the Δ₊ vs Δ₊^op orientation the retired variance-blind fold
`monotoneMapOf` (`List Nat`, no object) could not carry.

**BUT the oriented carrier does not rescue a left-to-right *fold* into it.** The machine-checked no-go
`arcMatching_cupAtoms_locallyIndistinguishable`
(`WalkingAdjunction/SaturatedMatchingCanonicalization.lean`) proves that a genuine base-block cup
`(L·R) ◁ η` and the embedded tip cup inside `embeddedTipCapRedex` carry **literally equal** per-atom
spine data `(leftContext.length, generatorDom.length, generatorCod.length) = (2, 0, 2)`, yet the two
must receive OPPOSITE variance — the first is a covariant face, the second an op-degeneracy (a cap
closes its strand in the *future* of the fold). The polarity is therefore NOT a function of any atom's
local (or running-prefix) data; it is fixed by the GLOBAL planar matching (which cup pairs with which
cap). Reading the port object per level does not expose that future pairing, so any left-to-right
per-atom evaluator `squiggleOf` populating this carrier lands in exactly the refuted class
(`covariantMonotoneMapOf_notSound` and its op-dual, on `embeddedTipCapConv`). This is recorded as the
honesty marker `fxMode_hasOrientedSquiggleFoldSoundness := false`.

The faithful oriented carrier of the RV squiggle is the boundary planar *matching* `matchingOf`
(`DiagramType`, `WalkingAdjunction/MatchingDecision.lean`), whose orientation content is the `partner`
connectivity, not a per-level projection. This `SquiggleString` type remains the honest RV Def 3.1.2
*target representation* — its `DecidableEq` is the decision procedure on normal forms — decoupled from
the dead fold; a faithful populator must be matching-derived (global), not a spine fold.

Raw Lean 4 + `Init`; every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free (full-enum matches, structural recursion on the level list, `Nat.beq`/`Bool` ops).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## SQ-1a — the port orientation and its decidable equality -/

/-- The boundary object a squiggle level sits on: `leftPort` (`L`) or `rightPort` (`R`).
This is the RV orientation tag (Δ₊ vs Δ₊^op) the variance-blind `List Nat` fold could not carry. -/
inductive PortSide where
  | leftPort : PortSide
  | rightPort : PortSide

/-- Decidable equality on `PortSide`, hand-rolled full-enum (no wildcard arm) so it is propext-clean. -/
def portSideDecEq (firstSide secondSide : PortSide) : Decidable (firstSide = secondSide) :=
  match firstSide, secondSide with
  | .leftPort,  .leftPort  => isTrue rfl
  | .rightPort, .rightPort => isTrue rfl
  | .leftPort,  .rightPort => isFalse (fun equal => PortSide.noConfusion equal)
  | .rightPort, .leftPort  => isFalse (fun equal => PortSide.noConfusion equal)

instance : DecidableEq PortSide := portSideDecEq

/-! ## SQ-1b — the oriented squiggle letter and string -/

/-- One symbol of the oriented squiggle string: the `level` reached after this atom acts, tagged with
the `side` (port object) that level sits on. Non-dependent by design so its `DecidableEq` is structural
and free of the indexed-`DecidableEq` propext leak. -/
structure SquiggleLetter where
  level : Nat
  side  : PortSide

/-- Decidable equality on `SquiggleLetter`: cascade `Nat.decEq` on the level then `portSideDecEq` on the
side, projecting field equalities with `congrArg` and reconstructing by `subst` (no `injEq` simp lemma,
so no propext). -/
def squiggleLetterDecEq (firstLetter secondLetter : SquiggleLetter) : Decidable (firstLetter = secondLetter) :=
  match firstLetter, secondLetter with
  | ⟨firstLevel, firstSideValue⟩, ⟨secondLevel, secondSideValue⟩ =>
    match Nat.decEq firstLevel secondLevel with
    | isFalse levelsDiffer =>
        isFalse (fun equal => levelsDiffer (congrArg SquiggleLetter.level equal))
    | isTrue levelsEqual =>
        match portSideDecEq firstSideValue secondSideValue with
        | isFalse sidesDiffer =>
            isFalse (fun equal => sidesDiffer (congrArg SquiggleLetter.side equal))
        | isTrue sidesEqual =>
            isTrue (by subst levelsEqual; subst sidesEqual; rfl)

instance : DecidableEq SquiggleLetter := squiggleLetterDecEq

/-- The oriented squiggle string — the RV Def 3.1.2 level word carrier. -/
abbrev SquiggleString := List SquiggleLetter

/-- Decidable equality on `SquiggleString`, via the propext-clean `Init` list instance over the
hand-rolled `SquiggleLetter` decider (the same pattern the shipped `spineListDecEq` uses). This is the
decision procedure on oriented normal forms. -/
def squiggleStringDecEq : DecidableEq SquiggleString :=
  @instDecidableEqList SquiggleLetter squiggleLetterDecEq

/-! ## SQ-1c — strict-undulation well-formedness (RV Def 3.1.2)

A squiggle is *strictly undulating* when consecutive levels differ by exactly one (each atom is a unit
cup/cap raising or lowering the level by one) AND the direction strictly alternates (a rise is followed
by a fall and vice versa — no monotone run, no repeated cusp). Structural recursion on the level list,
carrying the previous level and the previous step direction; unit-step and alternation are `Nat.beq` /
`Bool` computations, so the predicate is decidable and propext-clean. -/

/-- Tail worker: `previousLevel` is the level of the already-consumed letter and `previousDirection` is
`none` at the first step, `some true` if that step rose, `some false` if it fell. -/
def isStrictlyUndulatingFrom : Nat → Option Bool → SquiggleString → Bool
  | _previousLevel, _previousDirection, [] => true
  | previousLevel, previousDirection, letter :: remainingLetters =>
    let currentLevel := letter.level
    let stepRises := previousLevel + 1 == currentLevel
    let stepFalls := currentLevel + 1 == previousLevel
    let stepIsUnit := stepRises || stepFalls
    match previousDirection with
    | none =>
        stepIsUnit && isStrictlyUndulatingFrom currentLevel (some stepRises) remainingLetters
    | some previousRose =>
        stepIsUnit && (stepRises != previousRose)
          && isStrictlyUndulatingFrom currentLevel (some stepRises) remainingLetters

/-- The oriented squiggle is strictly undulating (RV Def 3.1.2 well-formedness). The empty and
singleton strings are trivially undulating; longer strings must have unit steps that alternate. -/
def isStrictlyUndulating : SquiggleString → Bool
  | [] => true
  | letter :: remainingLetters => isStrictlyUndulatingFrom letter.level none remainingLetters

/-! ## SQ-1 smoke facts (each `rfl`, zero-axiom) -/

/-- A genuine zigzag starting at `1`, then `1 ↓ 0 ↑ 1`, is strictly undulating (unit steps that
alternate). -/
theorem isStrictlyUndulating_zigzag :
    isStrictlyUndulating
      [⟨1, .leftPort⟩, ⟨0, .rightPort⟩, ⟨1, .leftPort⟩] = true := rfl

/-- A monotone staircase `1 ↑ 2 ↑ 3` is NOT strictly undulating (the second rise repeats the first
direction), so the RV Def 3.1.2 well-formedness rejects it. -/
theorem not_isStrictlyUndulating_staircase :
    isStrictlyUndulating [⟨1, .leftPort⟩, ⟨2, .rightPort⟩, ⟨3, .leftPort⟩] = false := rfl

/-- A non-unit jump `0 → 2` is NOT strictly undulating (the step is not a single cup/cap). -/
theorem not_isStrictlyUndulating_jump :
    isStrictlyUndulating [⟨0, .leftPort⟩, ⟨2, .rightPort⟩] = false := rfl

/-- The `DecidableEq` genuinely separates orientations: two letters equal in `level` but differing in
`side` are distinguished (the carrier is oriented, not a bare `Nat` string). -/
theorem squiggleLetter_side_discriminated :
    (⟨0, .leftPort⟩ : SquiggleLetter) ≠ ⟨0, .rightPort⟩ :=
  fun equal => PortSide.noConfusion (congrArg SquiggleLetter.side equal)

/-! ## SQ-1 honesty markers -/

/-- **ESTABLISHED.** The oriented squiggle *carrier* (RV Def 3.1.2 level word with `L`/`R` port tags),
its decidable strict-undulation well-formedness, and its structural `DecidableEq` are shipped, standalone
and zero-axiom. The carrier records the orientation the retired `monotoneMapOf` (`List Nat`, no object)
could not. `= true`. -/
def fxMode_hasOrientedSquiggleCarrier : Bool := true

/-- **REFUTED — the honest wall.** A left-to-right per-atom *evaluator* `squiggleOf` populating this
oriented carrier from spine data is NOT sound for saturated convertibility. The machine-checked no-go
`arcMatching_cupAtoms_locallyIndistinguishable` gives two cups with identical local data `(2, 0, 2)`
that must read opposite variance (the discriminating cap lies in the fold's *future*); reading the port
object per level does not expose it, so the oriented fold lands in the class refuted by
`covariantMonotoneMapOf_notSound` and its op-dual on `embeddedTipCapConv`. The variance is GLOBAL — the
faithful carrier is the boundary matching `matchingOf` (`partner` connectivity), not a level string.
`= false`. -/
def fxMode_hasOrientedSquiggleFoldSoundness : Bool := false

end FX1Poly.Polygraph
