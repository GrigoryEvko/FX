import FX1Poly.Core.DataTaitCandidate
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate

/-! # FX1Poly/Core/FlatCodeTaitCandidate
    — per-flat-code value predicates + the pinned data Tait candidates (CAN-6 / FLAT-CANON substrate)

The five FLAT binary data type-code formers (`gen_productCode` / `gen_sumCode` / `gen_eitherCode` /
`gen_arrowCode` / `gen_equivCode`, the `flatTypingRuleDescOf` table) need reducibility candidates to
participate in the §5 candidate bridge — exactly as `emptyTypeCell` was pinned to `emptyTaitCandidate` and
for the same reason: the generic `neutral` arm of `ReducibleTypeStepDenote` / `ReducibleTypeStepBounded`
over-fires on flat-code-rooted type cells, collapsing every flat code's candidate to the whole
`IsStronglyNormalizing` set and making the canonicity member bridge for closed values unprovable.

This file supplies everything the relation edit consumes:

  * `Generator.isFlatDataCode` — the `Bool` classifier for the 5 flat formers (the `neutral`-arm gate).
  * Per-code value predicates: `isPairValue` (product, reused), `isEitherValue` (either, reused),
    `isArrowFunctionValue` (arrow: a λ cell), `isEquivIntroValue` (equiv: an `equivIntro` cell), and for
    `gen_sumCode` the empty predicate — HONEST status: the Generator table has NO sum-injection intro
    generators (no engine types any value at a sum code), so the sum lane's canonical-form set is empty,
    exactly like `emptyTypeCell`'s.  If sum intro forms ever land, this row must change WITH them.
  * `flatCodeValuePredicate` — the per-generator dispatch.
  * `flatCodeTaitCandidate` — `dataTaitCandidate` at that predicate; ALL candidate metatheory (CR1/CR2/CR3,
    head-expansion closure, member weak-head expansion, closed-member canonicity) is inherited from the
    generic `dataTaitCandidate` theorems instantly.
  * `noWeakHeadStep_of_isFlatDataCode` — a flat-code-rooted term is weak-head-normal (every `WeakHeadStep`
    constructor pins an application/eliminator root; flat formers head no β/ι).  The fact the new `dataFlat`
    arm's inversions and forward closure consume (the root is STABLE along `StepStar`, so the pinned
    candidate re-fires).

## Zero-axiom verification

`Bool`-valued if-chains over decidable `Generator` equality (the `flatTypingRuleDescOf` pattern; concrete
roots compute by `rfl`/`decide`), existential value predicates, instances of the shipped generic
`dataTaitCandidate` theorems, and a `cases` refutation over `WeakHeadStep`/`IotaHeadStep` (every arm pins a
concrete non-flat root).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The flat-data-code classifier** — `true` exactly on the five `flatTypingRuleDescOf` formers.  The
`neutral`-arm gate of the candidate-bridge edit: the generic neutral arm must NOT fire on these roots, so
the dedicated `dataFlat` arm can pin their candidates. -/
def Generator.isFlatDataCode (generator : Generator) : Bool :=
  if generator = .gen_productCode then true
  else if generator = .gen_sumCode then true
  else if generator = .gen_eitherCode then true
  else if generator = .gen_arrowCode then true
  else if generator = .gen_equivCode then true
  else false

/-- A λ cell (Church-style: domain annotation + body). -/
abbrev arrowFunctionCell {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
    RawTerm scope :=
  .mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))

/-- **Arrow values: λ cells.**  The canonical-form predicate for `gen_arrowCode` — the natural value head of
a (non-dependent) function code.  HONEST status: no current engine types a λ at an arrow code (functions are
typed at `gen_piTyCode`), so this lane's canonicity is presently about the MODEL's candidate only. -/
def isArrowFunctionValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)), term = arrowFunctionCell domainAnn body

/-- An `equivIntro` cell (forward and backward functions). -/
abbrev equivIntroValueCell {scope : Nat} (forwardFn backwardFn : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_equivIntro () (.childCons forwardFn (.childCons backwardFn .childNil))

/-- **Equiv values: `equivIntro` cells.**  The canonical-form predicate for `gen_equivCode`. -/
def isEquivIntroValue {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ forwardFn backwardFn : RawTerm scope, term = equivIntroValueCell forwardFn backwardFn

/-- **The per-flat-code value-predicate dispatch.**  Product → pairs, either → injections, arrow → λ cells,
equiv → `equivIntro` cells, sum → the EMPTY predicate (no sum-injection intro generators exist — the honest
empty-like lane), and the empty predicate on every non-flat generator (those rows are never consulted: the
`dataFlat` arm fires only under `isFlatDataCode = true`). -/
def flatCodeValuePredicate {scope : Nat} (generator : Generator) : RawTerm scope → Prop :=
  if generator = .gen_productCode then isPairValue
  else if generator = .gen_sumCode then fun _ => False
  else if generator = .gen_eitherCode then isEitherValue
  else if generator = .gen_arrowCode then isArrowFunctionValue
  else if generator = .gen_equivCode then isEquivIntroValue
  else fun _ => False

/-- **The pinned flat-code Tait candidate** — the head-expansion-closed data candidate at that code's value
predicate.  What the `dataFlat` arm of the candidate-bridge edit assigns to every flat-code-rooted type
cell. -/
def flatCodeTaitCandidate {scope : Nat} (generator : Generator) : RawTerm scope → Prop :=
  dataTaitCandidate (flatCodeValuePredicate generator)

/-- **Every flat-code Tait candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from the
generic `dataTaitCandidate` bundle, uniformly in the generator. -/
theorem flatCodeTaitCandidate_isReducibilityCandidate {scope : Nat} (generator : Generator) :
    IsReducibilityCandidate (flatCodeTaitCandidate (scope := scope) generator) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **Every flat-code Tait candidate is head-expansion-closed** — Π-codomain-ready (the FT's Π-introduction
arm property), instant from the generic theorem. -/
theorem flatCodeTaitCandidate_headExpansionClosed {scope : Nat} (generator : Generator) :
    HeadExpansionClosed (flatCodeTaitCandidate (scope := scope) generator) :=
  dataTaitCandidate_headExpansionClosed

/-- **Member weak-head expansion for every flat-code Tait candidate** — instant from the generic theorem. -/
theorem flatCodeTaitCandidate_memberWeakHeadExpansion {scope : Nat} {generator : Generator}
    {source reduct : RawTerm scope} (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : flatCodeTaitCandidate generator reduct) :
    flatCodeTaitCandidate generator source :=
  dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember

/-- **Closed flat-code canonicity (candidate level): a closed member reduces to a value of that code's
canonical form** — instant from the generic `closedReducesToValue`. -/
theorem flatCodeTaitCandidate.closedReducesToValue {generator : Generator} {term : RawTerm 0}
    (member : flatCodeTaitCandidate generator term) :
    ∃ value : RawTerm 0, StepStar term value ∧ flatCodeValuePredicate generator value ∧
      RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue member

/-- **A flat-code-rooted term admits no weak-head step.**  Every `WeakHeadStep` constructor pins the source
root to `gen_app` (β / function congruence) or an eliminator generator (root-ι / scrutinee congruence) —
none of which is a flat former.  The weak-head normality the `dataFlat` arm's inversions and forward
closure consume: along any `StepStar` from a flat-code-rooted term the root is stable, so the pinned
candidate re-fires. -/
theorem noWeakHeadStep_of_isFlatDataCode {scope : Nat} {term : RawTerm scope}
    (flatRooted : term.rootGenerator.isFlatDataCode = true) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep term reduct := by
  intro reduct weakHeadStep
  cases weakHeadStep with
  | beta => exact nomatch flatRooted
  | appCongruence _ => exact nomatch flatRooted
  | rootIota iotaStep => cases iotaStep <;> exact nomatch flatRooted
  | scrutineeBoolElim _ => exact nomatch flatRooted
  | scrutineeFst _ => exact nomatch flatRooted
  | scrutineeSnd _ => exact nomatch flatRooted
  | scrutineeNatElim _ => exact nomatch flatRooted
  | scrutineeNatRec _ => exact nomatch flatRooted
  | scrutineeListElim _ => exact nomatch flatRooted
  | scrutineeOptionMatch _ => exact nomatch flatRooted
  | scrutineeEitherMatch _ => exact nomatch flatRooted
  | scrutineeIdJ _ => exact nomatch flatRooted
  | scrutineeIdStrictRec _ => exact nomatch flatRooted
  | pathBeta _ => exact nomatch flatRooted
  | quotRecMk _ => exact nomatch flatRooted
  | quotElimMk _ => exact nomatch flatRooted
  | truncRecIntro _ => exact nomatch flatRooted
  | pathAppCongruence _ => exact nomatch flatRooted
  | scrutineeQuotRec _ => exact nomatch flatRooted
  | scrutineeQuotElim _ => exact nomatch flatRooted
  | scrutineeTruncRec _ => exact nomatch flatRooted

end FX1Poly.Core
