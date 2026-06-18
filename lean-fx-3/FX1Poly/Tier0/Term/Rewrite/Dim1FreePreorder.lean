import FX1Poly.Core.Rewriting.Confluence.Newman
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepOverBundleConv

/-! # Tier0/Term — the dim-1 rewrite preorder: StepOver as the 1-cell generators (term-2)

`term-1` showed `RawTerm` is the INITIAL ALGEBRA of its signature — the dim-0 universal property
(terms as 0-cells / objects).  `term-2` is the MIDDLE of the term ω-category: the dim-1 structure,
where single rewrite steps are the 1-cells (morphisms BETWEEN terms) and `StepOver` over a rule-table
bundle is their generating set.

The honest shape of this rung is fixed by one fact: the reduction relations (`Step`, `StepStar`,
`StepOver bundle`, `ReflTransClosure (StepOver bundle)`) are `Prop`-valued, so the dim-1 hom is a
SUBSINGLETON.  The dim-1 category is therefore a PREORDER (a thin category), and "`StepOver` is the
freely-generated rewriting relation" (the `term-2` premise) means precisely:

  **`ReflTransClosure (StepOver bundle)` is the LEAST reflexive-transitive relation containing the
  one-step generators `StepOver bundle`** — the free-preorder universal property.

That is the genuine, previously-absent content this file ships.  The rewriting METATHEORY — confluence,
the modular-SN criterion, decidable Conv — is already surfaced in `term-0`; this rung adds the
categorical dim-1 PACKAGING those markers did not have (the closure carried `refl`/`single`/`trans` as
DATA but no universal property and no category laws).  The proof-RELEVANT (∞,ω) refinement — where
distinct reduction PATHS are distinct 1-cells and 2-cells fill the critical-pair branchings — is the
SEPARATE harder rung (`term-4` Squier coherence / `term-17` free strict ω-category); here the
`Prop`-truncation collapses all of that to the thin preorder, which is exactly why the laws below hold
by proof irrelevance.

## What this file ships (each zero-axiom)

  * **`ReflTransCocone rel`** — a model of the free-preorder spec over a relation `rel`: a target
    relation that is reflexive, composable, and receives the one-step generators `rel`.
  * **`ReflTransClosure.mediate`** — the universal property (existence): the mediating map from the
    free closure into any cocone; equivalently `ReflTransClosure rel` is contained in every
    reflexive-transitive relation containing `rel`, i.e. it is the LEAST such relation.
  * **`ReflTransClosure.mediate_unique`** — uniqueness, pointwise (by `Prop` proof irrelevance: the
    thin-category collapse).
  * **`ReflTransClosure.selfCocone`** + **`mediate_selfCocone`** — the closure is itself a cocone (the
    INITIAL one); mediating it is the identity.
  * **`ReflTransClosure.leftIdentity` / `rightIdentity` / `assoc`** — the (thin) category laws on the
    composition `trans`; each holds definitionally by proof irrelevance.
  * **`StepOver.freelyGenerated`** + **`StepOver.toFreelyGenerated`** — the freely-generated rewriting
    relation over a rule-table bundle, and the one-step generator inclusion.

The `fxIotaBundle` instance is bridged to the bespoke `StepStar` substrate by the shipped
`reflTransClosure_fxIotaBundle_iff_stepStar`, and is confluent by the shipped
`StepOver.fxIotaBundleConfluent` (surfaced as the `term-0` marker `fxTerm_hasRawConfluence`).

## Zero-axiom verification

One structure, one structural induction (`mediate`), one data witness (`selfCocone`), and the
proof-irrelevance `rfl` laws.  `cases`/`induction` on `ReflTransClosure` is propext-clean (its indices
are free variables, not constructor patterns).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TermDim1Rewrite.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- A **model of the free-preorder spec** over a relation `rel` (a "rewrite cocone"): a target
`relation` that is reflexive, composable (transitive), and receives the one-step generators `rel`.  The
free reflexive-transitive closure `ReflTransClosure rel` is the INITIAL such model. -/
structure ReflTransCocone (rel : Carrier → Carrier → Prop) where
  /-- The target relation receiving the closure. -/
  relation : Carrier → Carrier → Prop
  /-- The target is reflexive. -/
  reflexivity : ∀ point, relation point point
  /-- The target composes (is transitive). -/
  composition : ∀ {source middle goal : Carrier},
    relation source middle → relation middle goal → relation source goal
  /-- The target receives the one-step generators. -/
  embedsGenerator : ∀ {source goal : Carrier}, rel source goal → relation source goal

/-- ★ **Free-preorder universal property (existence / least closure).**  The mediating map from the
free reflexive-transitive closure into any cocone, by structural recursion on the reduction chain —
equivalently, `ReflTransClosure rel` is contained in every reflexive-transitive relation containing
`rel`, i.e. it is the LEAST such relation. -/
theorem ReflTransClosure.mediate {rel : Carrier → Carrier → Prop}
    (cocone : ReflTransCocone rel) {source goal : Carrier}
    (chain : ReflTransClosure rel source goal) : cocone.relation source goal := by
  induction chain with
  | refl point => exact cocone.reflexivity point
  | head firstStep _restChain inductionHypothesis =>
      exact cocone.composition (cocone.embedsGenerator firstStep) inductionHypothesis

/-- ★ **Free-preorder universal property (uniqueness, pointwise).**  Any mediating map agrees with
`mediate`.  Holds by definitional proof irrelevance — `cocone.relation source goal` is a `Prop`, so the
dim-1 hom is a subsingleton (the thin-category collapse).  This is precisely why the proof-RELEVANT
(∞,ω) 1-cells are the separate `term-4` / `term-17` rungs. -/
theorem ReflTransClosure.mediate_unique {rel : Carrier → Carrier → Prop}
    (cocone : ReflTransCocone rel) {source goal : Carrier}
    (other : ReflTransClosure rel source goal → cocone.relation source goal)
    (chain : ReflTransClosure rel source goal) :
    other chain = ReflTransClosure.mediate cocone chain := rfl

/-- The free closure is itself a cocone — the INITIAL one: reflexive (`refl`), composable (`trans`),
and receiving the generators (`single`). -/
def ReflTransClosure.selfCocone (rel : Carrier → Carrier → Prop) : ReflTransCocone rel where
  relation := ReflTransClosure rel
  reflexivity := ReflTransClosure.refl
  composition := ReflTransClosure.trans
  embedsGenerator := ReflTransClosure.single

/-- Mediating the closure into ITSELF is the identity (by proof irrelevance) — `ReflTransClosure rel`
is the initial cocone. -/
theorem ReflTransClosure.mediate_selfCocone {rel : Carrier → Carrier → Prop}
    {source goal : Carrier} (chain : ReflTransClosure rel source goal) :
    ReflTransClosure.mediate (ReflTransClosure.selfCocone rel) chain = chain := rfl

/-! ## The (thin) category laws on the composition `trans`

Each holds definitionally by `Prop` proof irrelevance — the hom `ReflTransClosure rel _ _` is a
subsingleton, so terms and reduction sequences form a PREORDER / thin category, not a proof-relevant
one.  Stated explicitly so the dim-1 category claim is non-vacuous (and honestly thin). -/

/-- Left identity: `refl` is a left unit for composition. -/
theorem ReflTransClosure.leftIdentity {rel : Carrier → Carrier → Prop} {source goal : Carrier}
    (chain : ReflTransClosure rel source goal) :
    ReflTransClosure.trans (ReflTransClosure.refl source) chain = chain := rfl

/-- Right identity: `refl` is a right unit for composition. -/
theorem ReflTransClosure.rightIdentity {rel : Carrier → Carrier → Prop} {source goal : Carrier}
    (chain : ReflTransClosure rel source goal) :
    ReflTransClosure.trans chain (ReflTransClosure.refl goal) = chain := rfl

/-- Associativity of composition. -/
theorem ReflTransClosure.assoc {rel : Carrier → Carrier → Prop}
    {start middleLeft middleRight goal : Carrier}
    (firstChain : ReflTransClosure rel start middleLeft)
    (secondChain : ReflTransClosure rel middleLeft middleRight)
    (thirdChain : ReflTransClosure rel middleRight goal) :
    ReflTransClosure.trans (ReflTransClosure.trans firstChain secondChain) thirdChain
      = ReflTransClosure.trans firstChain (ReflTransClosure.trans secondChain thirdChain) := rfl

/-! ## The bundle instance: StepOver as the 1-cell generators -/

/-- The **freely-generated rewriting relation** over a rule-table bundle: the reflexive-transitive
closure of the one-step `StepOver bundle` 1-cell generators — the homs of the dim-1 (thin) category of
terms and reduction sequences. -/
abbrev StepOver.freelyGenerated (bundle : RuleTableBundle) {scope : Nat}
    (source target : RawTerm scope) : Prop :=
  ReflTransClosure (fun first second : RawTerm scope => StepOver bundle first second) source target

/-- The one-step **generator inclusion**: a single `StepOver bundle` 1-cell is a (length-one) chain of
the freely-generated relation. -/
theorem StepOver.toFreelyGenerated {bundle : RuleTableBundle} {scope : Nat}
    {source target : RawTerm scope} (step : StepOver bundle source target) :
    StepOver.freelyGenerated bundle source target :=
  ReflTransClosure.single step

end FX1Poly.Core
