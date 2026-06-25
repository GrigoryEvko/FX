import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareOptionModelCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareListModelCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierCombinatorTable
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationCodeFormers

/-! # FX1Poly/Core/UnaryCarrierCombinatorTable
    — the carrier-aware UNARY-flat-former table (gate-1 swap 3 substrate, the arity-1 unification dispatch)

`CarrierCombinatorTable.lean` collapses the BINARY carrier-aware flat formers (`pairLike` / `coproductLike` /
`equivLike`, each `firstCode secondCode`) into one table-driven inductive arm.  Option (and, after swap 4, list)
are carrier-aware too — their reducibility candidate is assembled from their SINGLE element carrier — but they are
UNARY, so they cannot ride the binary arm: that arm stores two codes / two candidates / two reducibles, and forcing
a unary former onto it would fabricate a nonexistent second carrier.  They currently sit on the content-free
`dataFlat` lane (`carrierCombinator? = none`), which records no element reducibility — exactly the gap the
`optionMatch` some-branch residue (`optionSomeBranchMemberIfReachesSome`) cannot bridge.

This file is the UNARY twin of `CarrierCombinatorTable.lean`: `UnaryCarrierCombinator` is the finite tag set of
carrier-aware unary flat formers, and the dispatch functions read a former's CELL builder, its MODEL candidate
ASSEMBLER, and (per root generator) its unary combinator.  With it, ONE table-driven unary arm
(`dataUnaryCarrierAware`, landing in the swap-3 cascade) keyed on the unary combinator carries option (and list)
off the content-free `dataFlat` lane.  Adding a carrier-aware unary former then costs a `UnaryCarrierCombinator`
constructor + the table rows + the former's reach-aware candidate — and ZERO new inductive arms.

This is deliberately the ARITY-1 instance toward the route-(b) unification (one arity-indexed carrier-aware arm
replacing `dataFlat` + `dataFlatCarrierAware`): the binary table is the arity-2 instance, this is arity-1.

What lands here (all zero-axiom):

  * `UnaryCarrierCombinator` — the tag set: `optionLike` (option).  (`listLike` joins it at swap 4.)
  * `UnaryCarrierCombinator.cell` — the per-tag cell builder (`optionLike ↦ option type cell`).
  * `UnaryCarrierCombinator.assembleModel` — the per-tag MODEL candidate assembler (`optionLike ↦ the
    Ω-fork-free `reachAwareOptionCandidate`).  Unlike the binary `assemble` (NF-value), this stores the reach-aware
    MODEL candidate directly — option was never on a carrier-aware arm, so there is no legacy NF-value arm to keep.
  * `Generator.unaryCarrierCombinator?` — the per-root-generator dispatch (`gen_optionCode ↦ some optionLike`, else
    `none`).
  * the round-trip / injectivity / subst / cell-SN inversion helpers + the five candidate-property dispatches
    (`assembleModel_{isReducibilityCandidate,headExpansionClosed,closedUnderStep,memberWeakHeadExpansion,congr}`),
    each a per-tag dispatch to the shipped `reachAwareOptionCandidate_*` theorem — all UNCONDITIONAL (the reach-aware
    candidate's validity / closure need NO obligations on the element carrier, unlike the binary projection arm).
  * the cross-table clash `cell_carrierCombinator?_eq_none` — a unary cell's BINARY dispatch is `none`, so the unary
    arm clashes against the binary `dataFlatCarrierAware` arm in the joint inversions.

## Zero-axiom verification

`cases` over the one-tag enum dispatching to the shipped per-candidate theorems; the dispatch / cell builders are
`if`-chains over decidable `Generator` equality (concrete roots compute by `rfl`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace sweep.
-/

namespace FX1Poly.Core

open StepStar

/-- **The carrier-aware unary-flat-former tag set.**  The finite set of flat type-formers whose reducibility
candidate is assembled CARRIER-RECURSIVELY from a SINGLE child candidate: `optionLike` (`gen_optionCode`) and
`listLike` (`gen_listCode`, RECURSIVE — the cons tail is itself a list member).  The binary formers (product /
either / equiv) live in `CarrierCombinator`; the content-free formers (sum / bool / nat) stay on the `dataFlat`
lane. -/
inductive UnaryCarrierCombinator where
  | optionLike
  | listLike

/-- **The per-tag cell builder.**  The type CELL each carrier-aware unary former builds from its single carrier
code — the option type cell for `optionLike`.  The unary arm concludes on `combinator.cell elementCode`, so a
concrete combinator yields a concrete cell with concrete `()` payload. -/
def UnaryCarrierCombinator.cell {scope : Nat} :
    UnaryCarrierCombinator → RawTerm scope → RawTerm scope
  | .optionLike, elementCode =>
      .mkGen .gen_optionCode () (.childCons elementCode .childNil)
  | .listLike, elementCode =>
      .mkGen .gen_listCode () (.childCons elementCode .childNil)

/-- **The per-tag MODEL candidate assembler.**  The reach-aware reducibility candidate each carrier-aware unary
former assembles from its single carrier candidate — `reachAwareOptionCandidate` for `optionLike`.  The Ω-fork-free
model candidate the unary arm stores. -/
def UnaryCarrierCombinator.assembleModel {scope : Nat} :
    UnaryCarrierCombinator → (RawTerm scope → Prop) → (RawTerm scope → Prop)
  | .optionLike, elementCandidate =>
      reachAwareOptionCandidate elementCandidate
  | .listLike, elementCandidate =>
      reachAwareListCandidate elementCandidate

/-- **The per-root-generator dispatch into the unary-carrier-combinator table.**  The carrier-aware unary flat
formers map to their combinator, every other generator to `none` (the binary formers, the content-free `dataFlat`
lane, and all non-flat generators).  The single principled gate the unary arm reads
(`unaryCarrierCombinator? = some _`). -/
def Generator.unaryCarrierCombinator? (generator : Generator) : Option UnaryCarrierCombinator :=
  if generator = .gen_optionCode then some .optionLike
  else if generator = .gen_listCode then some .listLike
  else none

/-- **Round-trip: a table-built cell's root dispatches back to its unary combinator.**  The witness the unary
arm's inversions use to recognize a carrier-aware unary cell. -/
theorem UnaryCarrierCombinator.cell_unaryCarrierCombinator? {scope : Nat} (combinator : UnaryCarrierCombinator)
    (elementCode : RawTerm scope) :
    (combinator.cell elementCode).rootGenerator.unaryCarrierCombinator? = some combinator := by
  cases combinator <;> rfl

/-- **The unary cell builder is injective in `(combinator, elementCode)`.**  Equal cells have equal combinators
and equal carrier codes — diagonal (same combinator) by the per-cell constructor injection.  The shape-inversion
finisher the unary arm's `deterministic` case consumes. -/
theorem UnaryCarrierCombinator.cell_inj {scope : Nat}
    {combinator1 combinator2 : UnaryCarrierCombinator}
    {elementCode1 elementCode2 : RawTerm scope}
    (cellsEqual : combinator1.cell elementCode1 = combinator2.cell elementCode2) :
    combinator1 = combinator2 ∧ elementCode1 = elementCode2 := by
  cases combinator1 <;> cases combinator2 <;>
    first
      | (cases cellsEqual; exact ⟨rfl, rfl⟩)
      | exact Generator.noConfusion (congrArg RawTerm.rootGenerator cellsEqual)

/-- **Substitution commutes with the unary cell builder.**  A per-tag dispatch by `rfl` (a concrete flat cell is
a `mkGen` whose `subst` pushes into the child by definitional reduction); the symbolic-combinator bridge the
generic carrier-aware formation FT needs. -/
theorem UnaryCarrierCombinator.cell_subst {scope targetScope : Nat} (combinator : UnaryCarrierCombinator)
    (substitution : RawTermSubst scope targetScope) (elementCode : RawTerm scope) :
    RawTerm.subst substitution (combinator.cell elementCode)
      = combinator.cell (RawTerm.subst substitution elementCode) := by
  cases combinator <;> rfl

/-- **A unary carrier-aware cell is strongly normalizing when its carrier is.**  A flat former heads no redex, so
its only steps are congruence through the single carrier; a per-tag dispatch to the shipped
`optionCode_isStronglyNormalizing_of_element`. -/
theorem UnaryCarrierCombinator.cell_isStronglyNormalizing_of_element {scope : Nat}
    (combinator : UnaryCarrierCombinator) {elementCode : RawTerm scope}
    (elementStronglyNormalizing : IsStronglyNormalizing elementCode) :
    IsStronglyNormalizing (combinator.cell elementCode) := by
  cases combinator
  · exact optionCode_isStronglyNormalizing_of_element elementStronglyNormalizing
  · exact listCode_isStronglyNormalizing_of_element elementStronglyNormalizing

/-- **The model-assembled candidate is congruent in its carrier.**  Pointwise-equivalent carrier yields
pointwise-equivalent assembled candidate — a per-tag dispatch to `reachAwareOptionCandidate_congr`.  The finisher
the unary arm's `deterministic` case needs once the carrier IH aligns the carrier, without `funext`. -/
theorem UnaryCarrierCombinator.assembleModel_congr {scope : Nat} (combinator : UnaryCarrierCombinator)
    {elementCandidate1 elementCandidate2 : RawTerm scope → Prop}
    (elementIff : PointwiseIff elementCandidate1 elementCandidate2) :
    PointwiseIff (combinator.assembleModel elementCandidate1)
      (combinator.assembleModel elementCandidate2) := by
  cases combinator
  · exact reachAwareOptionCandidate_congr elementIff
  · exact reachAwareListCandidate_congr elementIff

/-- **The model-assembled candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — a per-tag dispatch to the
reach-aware candidate's own bundle, UNCONDITIONAL in the carrier (the reach-aware candidate's validity needs no
obligation on the element carrier).  The validity the unary arm's formation FT consumes. -/
theorem UnaryCarrierCombinator.assembleModel_isReducibilityCandidate {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCandidate : RawTerm scope → Prop) :
    IsReducibilityCandidate (combinator.assembleModel elementCandidate) := by
  cases combinator
  · exact reachAwareOptionCandidate_isReducibilityCandidate elementCandidate
  · exact reachAwareListCandidate_isReducibilityCandidate elementCandidate

/-- **The model-assembled candidate is head-expansion-closed** — Π-codomain-ready, a per-tag dispatch to
`reachAwareOptionCandidate_headExpansionClosed` (UNCONDITIONAL: the reach-aware candidate's head-expansion closure
needs no element obligation — the no-drift strip closes it). -/
theorem UnaryCarrierCombinator.assembleModel_headExpansionClosed {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCandidate : RawTerm scope → Prop) :
    HeadExpansionClosed (combinator.assembleModel elementCandidate) := by
  cases combinator
  · exact reachAwareOptionCandidate_headExpansionClosed
  · exact reachAwareListCandidate_headExpansionClosed

/-- **The model-assembled candidate is forward-closed under one `Step`** (member CR2) — a per-tag dispatch to
`reachAwareOptionCandidate_closedUnderStep`.  The member-forward-closure leg the unary arm incurs in
`ReducibleTypeAtDenote.memberForwardClosed`. -/
theorem UnaryCarrierCombinator.assembleModel_closedUnderStep {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCandidate : RawTerm scope → Prop)
    {term reduct : RawTerm scope}
    (member : combinator.assembleModel elementCandidate term) (step : Step term reduct) :
    combinator.assembleModel elementCandidate reduct := by
  cases combinator
  · exact reachAwareOptionCandidate_closedUnderStep member step
  · exact reachAwareListCandidate_closedUnderStep member step

/-- **The model-assembled candidate is closed under member weak-head expansion** — a per-tag dispatch to
`reachAwareOptionCandidate_memberWeakHeadExpansion` (UNCONDITIONAL: the carrier conjunct lifts by
`dataTaitCandidate_memberWeakHeadExpansion`, the reach clause by the no-drift strip — neither needs an element
obligation).  The member-weak-head-expansion leg the unary arm incurs in
`ReducibleTypeAtDenote.memberWeakHeadExpansion`. -/
theorem UnaryCarrierCombinator.assembleModel_memberWeakHeadExpansion {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCandidate : RawTerm scope → Prop)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct) (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : combinator.assembleModel elementCandidate reduct) :
    combinator.assembleModel elementCandidate source := by
  cases combinator
  · exact reachAwareOptionCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember
  · exact reachAwareListCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember

/-! ## Inversion helpers for the table-driven `dataUnaryCarrierAware` arm -/

/-- **A unary carrier-aware cell is flat-rooted.**  `(combinator.cell ec).rootGenerator.isFlatDataCode = true` —
the fact the `neutral`-arm clash and the weak-head-normality helper consume. -/
theorem UnaryCarrierCombinator.cell_isFlatDataCode {scope : Nat} (combinator : UnaryCarrierCombinator)
    (elementCode : RawTerm scope) :
    (combinator.cell elementCode).rootGenerator.isFlatDataCode = true := by
  cases combinator <;> rfl

/-- **A unary carrier-aware cell is weak-head-normal.**  Flat formers head no β/ι, so a table-built cell admits no
`WeakHeadStep` — the `whnfExpand` / `candidateAtWhnfReduct` clash for the unary arm. -/
theorem UnaryCarrierCombinator.cell_noWeakHeadStep {scope : Nat} (combinator : UnaryCarrierCombinator)
    (elementCode : RawTerm scope) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep (combinator.cell elementCode) reduct :=
  fun reduct => noWeakHeadStep_of_isFlatDataCode (cell_isFlatDataCode combinator elementCode) reduct

/-- **A unary carrier-aware cell's root is NOT outside the unary table.**  The clash the unary arm incurs against
the content-free `dataFlat` arm's `unaryCarrierCombinator? = none` gate. -/
theorem UnaryCarrierCombinator.cell_unaryCarrierCombinator?_ne_none {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCode : RawTerm scope) :
    (combinator.cell elementCode).rootGenerator.unaryCarrierCombinator? ≠ none := by
  rw [cell_unaryCarrierCombinator?]
  intro isNone
  exact Bool.noConfusion (congrArg Option.isSome isNone)

/-- **A unary carrier-aware cell differs from any non-unary-rooted term.**  When `other`'s root has no unary
combinator, it is not a table-built unary cell — the clash the unary arm incurs in the shape inversions. -/
theorem UnaryCarrierCombinator.cell_ne_of_unaryCarrierCombinator?_none {scope : Nat}
    (combinator : UnaryCarrierCombinator) (elementCode : RawTerm scope) {other : RawTerm scope}
    (otherNone : other.rootGenerator.unaryCarrierCombinator? = none) :
    combinator.cell elementCode ≠ other := by
  intro cellEqualsOther
  have roundTrip := cell_unaryCarrierCombinator? combinator elementCode
  rw [cellEqualsOther, otherNone] at roundTrip
  exact Bool.noConfusion (congrArg Option.isSome roundTrip)

/-- **★ Cross-table clash: a unary carrier-aware cell's BINARY dispatch is `none`.**  `(combinator.cell ec).root
Generator.carrierCombinator? = none` — the option type cell roots at `gen_optionCode`, which is none of the binary
formers, so the unary arm clashes against the binary `dataFlatCarrierAware` arm (and the binary arm's cells clash
against the unary arm symmetrically by their `unaryCarrierCombinator? = none`). -/
theorem UnaryCarrierCombinator.cell_carrierCombinator?_eq_none {scope : Nat} (combinator : UnaryCarrierCombinator)
    (elementCode : RawTerm scope) :
    (combinator.cell elementCode).rootGenerator.carrierCombinator? = none := by
  cases combinator <;> rfl

end FX1Poly.Core
