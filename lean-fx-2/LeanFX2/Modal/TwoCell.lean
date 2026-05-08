import LeanFX2.Modal.Foundation

/-! # Modal/TwoCell — 2-cells between modalities (D4.0a, tracker #1699)

A `TwoCell sourceModality targetModality` is a 2-cell in the
2-category whose objects are modes (`Foundation/Mode.lean`),
whose 1-cells are modalities (`Modal/Foundation.lean`), and whose
2-cells are inhabitants of this inductive.

The bare 2-cell inductive is the LOAD-BEARING Day 4 unblock atom
for the modal-adjunction layer (D4.2 Adjunction, D4.3 BoxPath,
D4.5 full ♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain, D4.6 mode bridge, D4.8 2LTT).
Without `TwoCell`, the canonical adjunction unit and counit (e.g.
`unitFlatSharp : identity ⇒ compose flat sharp`) collapse to
1-cell label equalities — a structural lie that conflates "the
labels are equal" with "there is a natural transformation".

## Design RFC

The TwoCell encoding is load-bearing for D4.5 (pentagon
coherence), D4.6 (mode bridge), and D4.8 (2LTT integration).
Three options were considered:

* **Option A — freely-generated inductive** with `refl` / `vert` /
  `horiz` ctors plus coherence laws bolted on as further ctors
  later (D4.0b #1700).
  Pro: directly matches the categorical 2-cell shape; structural
  recursion on TwoCell admits induction-based coherence proofs;
  no Step / ParRed / Compat cascade.
  Con: every coherence equation lives as a separate ctor or a
  separate theorem proven by induction on TwoCell — hand-work
  for assoc / left-id / right-id / exchange laws, but those are
  out of scope for this atom.

* **Option B — `∃`-witness via ChainMorphism**.  Define `TwoCell A
  B := ∃ chain, ChainMorphism A chain ∧ ChainMorphism B chain`,
  exploiting an unspecified "chain" primitive.
  Pro: `trans` / `refl` / `sym` come from `Exists` for free.
  Con: REQUIRES the chain primitive (not present in lean-fx-2);
  consuming a TwoCell forces an `Exists.elim` at every site;
  reduction rules (definitional 2-cell equalities) are awkward
  to attach.  Out of scope to invent the chain primitive for
  THIS atom.

* **Option C — Step-rewrite quotient**.  Define `TwoCell` as
  inductive whose equations are enforced via `Step` / `ParRed`
  rewrites mirroring the existing FX kernel's Step discipline.
  Pro: matches the FX kernel's Reduction-layer vocabulary;
  reduction rules become first-class.
  Con: requires Step rules + ParRed mirrors + Compat cascade
  for every law (raw-and-typed parity per `WORKING_RULES.md`
  Discipline #23); this is the `Ty.cumul` anti-pattern in
  reverse — Modal-layer features should NOT push reduction
  rules down into Reduction layer when an inductive suffices
  (see `WORKING_RULES.md` Discipline #15: cumulativity is a
  Conv rule, NOT a Ty constructor; symmetrically, 2-cells are
  an inductive, NOT a Step rule).

**Decision: Option A.**  The 2-cell is a genuine categorical
construct — not a definitional reduction.  An inductive matches
the math directly.  Coherence laws (assoc, left-id, right-id,
exchange) are deferred to D4.0b #1700, where they ship as
theorems proven by structural induction on TwoCell.  This atom
ships ONLY the inductive + 3 core ctors.

## What ships (D4.0a, this atom — #1699)

* `TwoCell : {sourceMode targetMode : Mode} →
            Modality sourceMode targetMode →
            Modality sourceMode targetMode → Type`
  — the 2-cell inductive between parallel 1-cells (same source,
  same target mode).

* `TwoCell.refl : TwoCell modality modality` — the identity
  2-cell at any modality.  Witnesses reflexivity of the 2-cell
  relation.

* `TwoCell.vert : TwoCell modA modB → TwoCell modB modC →
                  TwoCell modA modC` — vertical composition of
  2-cells.  Sequential composition along a fixed mode pair.

* `TwoCell.horiz` — horizontal composition (a.k.a. whiskering /
  Godement product).  RESTRICTED to same-mode in this atom
  because `Modality.compose` is currently same-mode only;
  cross-mode `composeOpen` is a follow-up atom (D4.0c #1701).
  See ctor docstring for the same-mode signature shipped here.

## What is NOT shipped here

* **Coherence laws** (D4.0b #1700, deferred).  Associativity of
  vertical composition, left/right identity for vertical, the
  middle-four exchange law, and unit-vs-vertical coherence ship
  as theorems proven by induction on TwoCell in a follow-up
  file `Modal/TwoCellLaws.lean`.

* **Cross-mode horizontal composition** (D4.0c #1701, deferred).
  Generalising `Modality.compose` from same-mode
  `Modality m m → Modality m m → Modality m m` to cross-mode
  `Modality s m → Modality m t → Modality s t` is a pure
  Modal/Foundation extension; once it lands, the same-mode
  `TwoCell.horiz` ctor here generalises straightforwardly to
  cross-mode without changing this file's surface.

* **Adjunction structure** (D4.2 #1329).  `Adjoint`, `unitOf`,
  `counitOf`, triangle identities, naturality squares all ship
  in `Modal/Adjunction.lean` once this atom plus D4.0b laws
  land.

## Downstream consumers

* `Modal/Adjunction.lean` (D4.2 #1329) — `Adjoint` predicate;
  `flatAdjSharp : Adjoint Modality.flat Modality.sharp`;
  triangle identities `(ε □) ∘ (□ η) = id □` and
  `(◇ ε) ∘ (η ◇) = id ◇`.
* `Modal/BoxPath.lean` (D4.3 #1330) — `□` commutes with
  `Path` / `Id` via 2-cells.
* `Modal/Cohesive.lean` (D4.4 #1331) — uniqueness theorems for
  `flat` / `sharp` already ship; the `♭ ⊣ ♯` adjunction unit /
  counit await this file.
* `Modal/Bridge.lean` (D4.6 #1333) — strict ↔ observational
  ↔ univalent transfer expressed via 2-cells.
* `Modal/`2LTT`.lean` (D4.8 #1335) — outer/inner 2LTT
  integration: bridge between `strict` and `observational`
  modes via 2-cells.
* `Smoke/Modal.lean` — modal computation rules referencing
  `TwoCell.refl` (currently aspirational docstring).

## Zero-axiom commitment

Per `CLAUDE.md` "Zero-axiom commitment — ABSOLUTE": every
shipped declaration in this file is verified by
`#assert_no_axioms` and a corresponding `#print axioms` smoke
audit.  No `axiom`, `sorry`, `admit`, `noncomputable`,
`Classical.*`, `propext`, or `Quot.sound` appears in the
transitive dependency closure.

## Match-compiler hygiene

Per `WORKING_RULES.md` Discipline #4, `Modality.compose` is
marked `@[reducible]` upstream so that `TwoCell.horiz`'s indices
(which contain `Modality.compose`) elaborate without unifier
failures during constructor-application typechecking.

Per `WORKING_RULES.md` Discipline #2 (wildcards always leak
propext), no theorem in this file pattern-matches on TwoCell
with a wildcard arm.  This atom ships no theorems at all —
coherence laws come in D4.0b #1700.

## Root status

* Layer: kernel
* Load-bearing for: Modal/Adjunction, Modal/BoxPath,
  Modal/Cohesive (cohesive adjunction), Modal/Bridge,
  Modal/`2LTT`, Smoke/AuditPhase12A4TwoCell,
  Smoke/AuditPhase12A4Day4
* Axiom budget: zero (verified via `#assert_no_axioms` in
  `Tools/AuditAll/AuditModalTwoCell.lean`)
-/

namespace LeanFX2

/-- Two-cells between parallel modalities.

`TwoCell sourceModality targetModality` is the type of 2-cells
from `sourceModality` to `targetModality`, where both 1-cells
share the same source mode and the same target mode.

In categorical terms: `TwoCell` is the hom-set of 2-cells in the
2-category whose objects are `Mode`, whose 1-cells (between
modes) are `Modality`, and whose composition of 1-cells is
`Modality.compose` (currently same-mode only;
cross-mode `composeOpen` is D4.0c #1701).

This is the freely-generated inductive (Option A in the file
RFC): `refl` for identity 2-cells, `vert` for vertical
composition along a parallel pair of 1-cells, `horiz` for
horizontal composition (whiskering) of 2-cells across composed
1-cells.  Coherence laws (associativity, left/right identity,
middle-four exchange) are deferred to D4.0b #1700, where they
ship as theorems by induction on `TwoCell`.
-/
inductive TwoCell : {sourceMode targetMode : Mode} →
    Modality sourceMode targetMode →
    Modality sourceMode targetMode → Type
  /-- Identity 2-cell.

  For every modality `someModality`, there is a canonical 2-cell
  `refl someModality : TwoCell someModality someModality`.
  Witnesses reflexivity of the 2-cell relation; serves as the
  unit of vertical composition (left- and right-identity laws
  for `vert` ship in D4.0b #1700).
  -/
  | refl {sourceMode targetMode : Mode}
      (someModality : Modality sourceMode targetMode) :
      TwoCell someModality someModality
  /-- Vertical composition.

  Given a 2-cell `firstCell : TwoCell modAlpha modBeta` and a
  2-cell `secondCell : TwoCell modBeta modGamma`, vertical
  composition gives a 2-cell `vert firstCell secondCell :
  TwoCell modAlpha modGamma`.

  The two cells must share the middle 1-cell `modBeta` to be
  vertically composable.  Categorically: this is sequential
  composition along a fixed (sourceMode, targetMode) pair.
  Associativity and left/right identity laws for `vert` ship
  in D4.0b #1700.
  -/
  | vert {sourceMode targetMode : Mode}
      {modAlpha modBeta modGamma : Modality sourceMode targetMode}
      (firstCell : TwoCell modAlpha modBeta)
      (secondCell : TwoCell modBeta modGamma) :
      TwoCell modAlpha modGamma
  /-- Horizontal composition (whiskering / Godement product) at a
  shared mode.

  Given:
  * a 2-cell `outerCell : TwoCell outerSource outerTarget`
    between parallel 1-cells `outerSource, outerTarget :
    Modality someMode someMode`, and
  * a 2-cell `innerCell : TwoCell innerSource innerTarget`
    between parallel 1-cells `innerSource, innerTarget :
    Modality someMode someMode`,

  horizontal composition gives a 2-cell
  `horiz outerCell innerCell :
   TwoCell (compose outerSource innerSource)
           (compose outerTarget innerTarget)`.

  Restricted to same-mode (the three Modality slots all live at
  `Modality someMode someMode`) because `Modality.compose` is
  itself same-mode only.  Cross-mode horizontal composition
  generalises straightforwardly once `composeOpen` lands
  (D4.0c #1701).  The middle-four exchange law relating
  `vert` and `horiz` ships in D4.0b #1700.
  -/
  | horiz {someMode : Mode}
      {outerSource outerTarget : Modality someMode someMode}
      {innerSource innerTarget : Modality someMode someMode}
      (outerCell : TwoCell outerSource outerTarget)
      (innerCell : TwoCell innerSource innerTarget) :
      TwoCell (Modality.compose outerSource innerSource)
              (Modality.compose outerTarget innerTarget)

end LeanFX2
