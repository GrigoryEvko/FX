import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEquivCandidate

/-! # FX1Poly/Core/CarrierCombinatorTable
    — the carrier-aware binary-flat-former table (FTGEN-5.2 substrate, the unification dispatch)

The carrier-aware reducibility candidates shipped so far — `carrierAwarePairCandidate` (product) and
`carrierAwareEitherCandidate` (coproduct) — are each a former-specific way to ASSEMBLE two carrier
candidates into the former's type candidate, paired with a former-specific CELL the type code is built from.
Wiring each into the denote-keyed reducibility relation as its own bespoke inductive arm (`dataFlatProduct`,
a would-be `dataFlatEither`, ...) proliferates arms: every arm costs a case across ~12 inversion / backbone
lemmas, and each new carrier-aware former repeats the whole cascade.

This file is the DATA TABLE that collapses that proliferation.  `CarrierCombinator` is the finite tag set of
carrier-aware binary flat formers; the three dispatch functions read a former's CELL builder, its candidate
ASSEMBLER, and (per root generator) its combinator.  With this table, ONE table-driven arm
(`dataFlatCarrierAware`, landing next) keyed on `combinator` replaces every bespoke `dataFlatX` arm, and the
content-free `dataFlat` arm's gate becomes the single principled condition `carrierCombinator? = none` (no
more threading `≠ gen_productCode`, `≠ gen_eitherCode`, ... at every site).  Adding a carrier-aware former
then costs exactly: a `CarrierCombinator` constructor + three table rows + the former's candidate — and ZERO
new inductive arms or inversion cases.

What lands here (all zero-axiom):

  * `CarrierCombinator` — the tag set: `pairLike` (product), `coproductLike` (either), `equivLike` (equiv).
  * `CarrierCombinator.cell` — the per-tag cell builder (`pairLike ↦ product cell`, `coproductLike ↦ either
    cell`, `equivLike ↦ equiv cell`).
  * `CarrierCombinator.assemble` — the per-tag candidate assembler (`pairLike ↦ carrierAwarePairCandidate`,
    `coproductLike ↦ carrierAwareEitherCandidate`, `equivLike ↦ carrierAwareEquivCandidate`).
  * `Generator.carrierCombinator?` — the per-root-generator dispatch (the `isFlatDataCode` if-chain idiom):
    `gen_productCode ↦ some pairLike`, `gen_eitherCode ↦ some coproductLike`, `gen_equivCode ↦ some equivLike`,
    else `none`.
  * `CarrierCombinator.cell_carrierCombinator?` — the round-trip: a table-built cell's root dispatches back to
    its combinator (the inversions' "this cell IS carrier-aware" witness).
  * `CarrierCombinator.cell_inj` — cell injectivity in (combinator, first code, second code): the table arm's
    shape-inversion finisher (diagonal by the per-cell `cases`, off-diagonal by a root-generator clash).
  * `CarrierCombinator.assemble_congr` / `assemble_isReducibilityCandidate` / `assemble_headExpansionClosed` —
    the assembled candidate is congruent in its carriers (the `deterministic` finisher), a Girard reducibility
    candidate, and head-expansion-closed — each a per-tag dispatch to the candidate's own theorem.

## Zero-axiom verification

`cases` over the two-tag enum dispatching to the shipped per-candidate theorems; the dispatch / cell builders
are `if`-chains over decidable `Generator` equality (concrete roots compute by `rfl`); the off-diagonal cell
clash is a `show`-coerced closed `Generator` disequality by `decide` (the open-goal coercion idiom).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware binary-flat-former tag set.**  The finite set of flat type-formers whose reducibility
candidate is assembled CARRIER-RECURSIVELY from its two child candidates: `pairLike` (`gen_productCode`),
`coproductLike` (`gen_eitherCode`), and `equivLike` (`gen_equivCode`).  The sum / arrow flat formers are NOT
here — sum has no intro generators (content-free), arrow is not engine-reachable (functions type at
`gen_piTyCode`) — so they stay on the content-free `dataFlat` lane (`carrierCombinator? = none`).  The
`equivLike` row carries the `(f, isEquiv f)` Σ-unfold of an equivalence (FTGEN-5.4 `carrierAwareEquivCandidate`,
its components reducible functions between the carriers) — the typed equivalence-as-capability the
definitional-univalence frontier (FTGEN-5.6, `Id_U ↝ equivCode`) consumes. -/
inductive CarrierCombinator where
  | pairLike
  | coproductLike
  | equivLike

/-- **The per-tag cell builder.**  The type CELL each carrier-aware former builds from its two carrier codes —
the product cell for `pairLike`, the either cell for `coproductLike`.  The table arm concludes on
`combinator.cell firstCode secondCode`, so a concrete combinator yields a concrete cell with concrete `()`
payload (sidestepping the generic-`mkGen`-payload dependency a raw-`Generator`-field arm would incur). -/
def CarrierCombinator.cell {scope : Nat} :
    CarrierCombinator → RawTerm scope → RawTerm scope → RawTerm scope
  | .pairLike, firstCode, secondCode =>
      .mkGen .gen_productCode () (.childCons firstCode (.childCons secondCode .childNil))
  | .coproductLike, firstCode, secondCode =>
      .mkGen .gen_eitherCode () (.childCons firstCode (.childCons secondCode .childNil))
  | .equivLike, firstCode, secondCode =>
      .mkGen .gen_equivCode () (.childCons firstCode (.childCons secondCode .childNil))

/-- **The per-tag candidate assembler.**  The reducibility candidate each carrier-aware former assembles from
its two carrier candidates — `carrierAwarePairCandidate` for `pairLike`, `carrierAwareEitherCandidate` for
`coproductLike`, `carrierAwareEquivCandidate` for `equivLike`.  The candidate the table arm stores. -/
def CarrierCombinator.assemble {scope : Nat} :
    CarrierCombinator → (RawTerm scope → Prop) → (RawTerm scope → Prop) → (RawTerm scope → Prop)
  | .pairLike, firstCandidate, secondCandidate =>
      carrierAwarePairCandidate firstCandidate secondCandidate
  | .coproductLike, firstCandidate, secondCandidate =>
      carrierAwareEitherCandidate firstCandidate secondCandidate
  | .equivLike, firstCandidate, secondCandidate =>
      carrierAwareEquivCandidate firstCandidate secondCandidate

/-- **The per-root-generator dispatch into the carrier-combinator table.**  The carrier-aware flat formers map
to their combinator, every other generator to `none` (the content-free `dataFlat` lane and all non-flat
generators).  The `isFlatDataCode` if-chain idiom — propext-clean over decidable `Generator` equality, and
the single principled gate the content-free `dataFlat` arm reads (`carrierCombinator? = none`). -/
def Generator.carrierCombinator? (generator : Generator) : Option CarrierCombinator :=
  if generator = .gen_productCode then some .pairLike
  else if generator = .gen_eitherCode then some .coproductLike
  else if generator = .gen_equivCode then some .equivLike
  else none

/-- **Round-trip: a table-built cell's root dispatches back to its combinator.**  `(combinator.cell firstCode
secondCode).rootGenerator.carrierCombinator? = some combinator` — the witness the table arm's inversions use
to recognize a carrier-aware cell (and to clash it against the non-carrier-aware formers). -/
theorem CarrierCombinator.cell_carrierCombinator? {scope : Nat} (combinator : CarrierCombinator)
    (firstCode secondCode : RawTerm scope) :
    (combinator.cell firstCode secondCode).rootGenerator.carrierCombinator? = some combinator := by
  cases combinator <;> rfl

/-- **The carrier-aware cell builder is injective in `(combinator, firstCode, secondCode)`.**  Equal cells
have equal combinators and equal carrier codes: diagonal (same combinator) by the per-cell constructor
injection (`cases` on the equality, as in `productCodeCell_inj` / `eitherCodeCell_inj`), off-diagonal by a
root-generator clash.  The shape-inversion finisher the table arm's `deterministic` case consumes.  Uniform
over the 3×3 combinator grid: each diagonal closes by `cases cellsEqual`, each off-diagonal by the
root-generator disequality (`by decide` reduces `.rootGenerator` of each concrete cell). -/
theorem CarrierCombinator.cell_inj {scope : Nat}
    {combinator1 combinator2 : CarrierCombinator}
    {firstCode1 secondCode1 firstCode2 secondCode2 : RawTerm scope}
    (cellsEqual : combinator1.cell firstCode1 secondCode1 = combinator2.cell firstCode2 secondCode2) :
    combinator1 = combinator2 ∧ firstCode1 = firstCode2 ∧ secondCode1 = secondCode2 := by
  cases combinator1 <;> cases combinator2 <;>
    first
      | (cases cellsEqual; exact ⟨rfl, rfl, rfl⟩)
      | exact Generator.noConfusion (congrArg RawTerm.rootGenerator cellsEqual)

/-- **The assembled candidate is congruent in its carriers.**  Pointwise-equivalent carriers yield
pointwise-equivalent assembled candidates — a per-tag dispatch to `carrierAwarePairCandidate_congr` /
`carrierAwareEitherCandidate_congr`.  The finisher the table arm's `deterministic` case needs once the carrier
induction hypotheses align the carriers, without `funext`. -/
theorem CarrierCombinator.assemble_congr {scope : Nat} (combinator : CarrierCombinator)
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (combinator.assemble firstCandidate1 secondCandidate1)
      (combinator.assemble firstCandidate2 secondCandidate2) := by
  cases combinator
  · exact carrierAwarePairCandidate_congr firstIff secondIff
  · exact carrierAwareEitherCandidate_congr firstIff secondIff
  · exact carrierAwareEquivCandidate_congr firstIff secondIff

/-- **The assembled candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — a per-tag dispatch to the
candidate's own bundle, uniformly in the carriers.  The validity the table arm's formation FT consumes. -/
theorem CarrierCombinator.assemble_isReducibilityCandidate {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (combinator.assemble firstCandidate secondCandidate) := by
  cases combinator
  · exact carrierAwarePairCandidate_isReducibilityCandidate firstCandidate secondCandidate
  · exact carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate
  · exact carrierAwareEquivCandidate_isReducibilityCandidate firstCandidate secondCandidate

/-- **The assembled candidate is head-expansion-closed** — Π-codomain-ready (the FT's Π-introduction arm
property), a per-tag dispatch to the candidate's own theorem. -/
theorem CarrierCombinator.assemble_headExpansionClosed {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (combinator.assemble firstCandidate secondCandidate) := by
  cases combinator
  · exact carrierAwarePairCandidate_headExpansionClosed firstCandidate secondCandidate
  · exact carrierAwareEitherCandidate_headExpansionClosed firstCandidate secondCandidate
  · exact carrierAwareEquivCandidate_headExpansionClosed firstCandidate secondCandidate

/-- **The assembled candidate is forward-closed under one `Step`** (CR2, member level) — a per-tag dispatch to
`dataTaitCandidate.closedUnderStep` (the assembled candidate IS a `dataTaitCandidate` of its value predicate in
each tag).  The member-forward-closure leg the carrier-aware arm incurs in `ReducibleTypeAtDenote.memberForward
Closed`. -/
theorem CarrierCombinator.assemble_closedUnderStep {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop) {term reduct : RawTerm scope}
    (member : combinator.assemble firstCandidate secondCandidate term) (step : Step term reduct) :
    combinator.assemble firstCandidate secondCandidate reduct := by
  cases combinator <;> exact dataTaitCandidate.closedUnderStep member step

/-- **The assembled candidate is closed under member weak-head expansion** — a per-tag dispatch to
`dataTaitCandidate_memberWeakHeadExpansion`.  The member-weak-head-expansion leg the carrier-aware arm incurs in
`ReducibleTypeAtDenote.memberWeakHeadExpansion`. -/
theorem CarrierCombinator.assemble_memberWeakHeadExpansion {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop) {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct) (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : combinator.assemble firstCandidate secondCandidate reduct) :
    combinator.assemble firstCandidate secondCandidate source := by
  cases combinator <;>
    exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember

/-! ## Inversion helpers for the table-driven `dataFlatCarrierAware` arm

Each is a one-line discharge the carrier-aware arm's case incurs in the reducibility relation's inversions:
a carrier-aware cell is flat-rooted, weak-head-normal, and its root maps to a combinator — so it clashes
against every non-carrier-aware former (`piTyCode` / `universeCode` / `emptyCode` / the content-free flat
`sumCode` lane) and against the content-free `dataFlat` arm's `carrierCombinator? = none` gate. -/

/-- **A carrier-aware cell is flat-rooted.**  `(combinator.cell fc sc).rootGenerator.isFlatDataCode = true` —
the fact the `neutral`-arm clash and the weak-head-normality helper consume. -/
theorem CarrierCombinator.cell_isFlatDataCode {scope : Nat} (combinator : CarrierCombinator)
    (firstCode secondCode : RawTerm scope) :
    (combinator.cell firstCode secondCode).rootGenerator.isFlatDataCode = true := by
  cases combinator <;> rfl

/-- **A carrier-aware cell is weak-head-normal.**  Flat formers head no β/ι, so a table-built cell admits no
`WeakHeadStep` — the `whnfExpand` / `candidateAtWhnfReduct` clash for the carrier-aware arm. -/
theorem CarrierCombinator.cell_noWeakHeadStep {scope : Nat} (combinator : CarrierCombinator)
    (firstCode secondCode : RawTerm scope) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep (combinator.cell firstCode secondCode) reduct :=
  fun reduct => noWeakHeadStep_of_isFlatDataCode (cell_isFlatDataCode combinator firstCode secondCode) reduct

/-- **A carrier-aware cell differs from any non-carrier-aware-rooted term.**  When `other`'s root has no
combinator, it is not a table-built cell — the clash the carrier-aware arm incurs in the `piType` /
`universeCode` / `dataEmpty` / content-free-flat shape inversions (supply `other`'s `carrierCombinator? = none`
by `rfl`). -/
theorem CarrierCombinator.cell_ne_of_carrierCombinator?_none {scope : Nat} (combinator : CarrierCombinator)
    (firstCode secondCode : RawTerm scope) {other : RawTerm scope}
    (otherNone : other.rootGenerator.carrierCombinator? = none) :
    combinator.cell firstCode secondCode ≠ other := by
  intro cellEqualsOther
  have roundTrip := cell_carrierCombinator? combinator firstCode secondCode
  rw [cellEqualsOther, otherNone] at roundTrip
  exact Bool.noConfusion (congrArg Option.isSome roundTrip)

/-- **A carrier-aware cell's root is NOT outside the table.**  `(combinator.cell fc sc).rootGenerator.carrier
Combinator? ≠ none` — the clash the carrier-aware arm incurs against the content-free `dataFlat` arm's
`carrierCombinator? = none` gate (and the `candidateIffFlatCandidate` inversion's gate). -/
theorem CarrierCombinator.cell_carrierCombinator?_ne_none {scope : Nat} (combinator : CarrierCombinator)
    (firstCode secondCode : RawTerm scope) :
    (combinator.cell firstCode secondCode).rootGenerator.carrierCombinator? ≠ none := by
  rw [cell_carrierCombinator?]
  intro isNone
  exact Bool.noConfusion (congrArg Option.isSome isNone)

end FX1Poly.Core
