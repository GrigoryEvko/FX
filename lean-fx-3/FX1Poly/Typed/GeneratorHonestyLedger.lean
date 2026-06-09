import FX1Poly.Typed.SemanticTierSoundness
import FX1Poly.Typed.ClassifierRefinement
import FX1Poly.Typed.ValueElimHostFold
import FX1Poly.Typed.GeneratorHonestyOverview
import FX1Poly.Typed.TypingHeadKindClassifier
import FX1Poly.Core.EtaRootClassifier

/-! # FX1Poly/Typed/GeneratorHonestyLedger — the honesty-arc capstone (HON-17)

The honesty arc asks: does the 197-generator polygraph table TRUTHFULLY encode its meanings, or are the names a
façade?  Across HON-1..HON-15 the arc shipped, per generator, an honest static classifier (`hasSomeTypingRule`),
an honest operational classifier (`hasRedexHead`), their unified tier (`semanticTier`), the soundness of the
reserved verdict (HON-5/6/7), the faithfulness of the live eliminators (HON-12/13/14), and the strict-refinement
relationship to the grown untypability decision (HON-8).  This file is the CAPSTONE: it bundles those results
into a single machine-checked ledger, `GeneratorHonestyLedger`, with four pillars — the structural answer "yes,
honestly classified, and here is the bundled proof":

  * **`reservedIsDead`** (SOUNDNESS, HON-7) — a generator the tier brands `reserved` is semantically dead: its
    cells are grown-untyped AND fire no root redex.  (`semanticTierReservedSound`.)
  * **`unionStrictlyRefinesGrown`** (REFINEMENT, HON-8) — the full-union classifier `hasSomeTypingRule` strictly
    refines the grown-only untypability decision `isUntypableHead`: refinement + containment + a strict witness
    (`gen_boolTrue`, grown-untypable yet union-typed).  (`hasSomeTypingRuleStrictlyRefinesUntypableHead`.)
  * **`boolElimFaithful`** (FAITHFULNESS, HON-14 representative) — a live eliminator computes its EXACT host
    meaning: `boolElim` on a host bool reduces to `cond`.  (`boolElimHostFold`; the full faithfulness set —
    fst/snd↝Prod, optionMatch↝Option.elim, eitherMatch↝Sum.elim, idJ↝Eq.rec, natElim↝Nat.mul, listElim↝
    List.length — is in `ValueElimHostFold` / `NatElimFaithfulMul` / `ListElimFaithfulLength`.)
  * **`axesComplementary`** (NON-VACUITY, HON-3) — neither classifier axis alone suffices: `natElim` reduces but
    is statically reserved, `boolTrue` is typed but not a redex head — both LIVE, caught by complementary axes.

`generatorHonestyLedgerHolds` proves the ledger, each pillar discharged by its shipped theorem.  Build-time
`#eval`s print the ACTUAL per-metric COUNTS on every default build — for each verification metric, how many of
the 197 generators satisfy it (typed / redex-head / eta-head / live / reserved / untypable, with the grown-vs-
standalone and typed-vs-reduces cross-cuts).  The counts are the SCOPE (how much of the table carries meaning);
`generatorHonestyLedgerHolds` is the GUARANTEE (the classifiers folded into those counts are sound).

What this ledger does NOT assert: the exact generator count (HON-9 count-pin is deferred — kernel-reducing a
197-element filter is heavyweight; the HON-4 `#eval` reports it by compiled execution), nor faithfulness of every
single eliminator inside the structure (one representative; the full set is cited above).

## Zero-axiom

`GeneratorHonestyLedger` is a `Prop`-valued structure (an iterated conjunction); `generatorHonestyLedgerHolds`
populates each field with a shipped zero-axiom theorem (`semanticTierReservedSound`,
`hasSomeTypingRuleStrictlyRefinesUntypableHead`, `boolElimHostFold`, the two complementarity witnesses).  The
`#eval` is a print command, not an audited declaration.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  `generatorHonestyLedgerHolds` is audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The four-pillar generator-honesty ledger.**  A `Prop`-valued bundle of the honesty arc's headline results:
the tier verdict is sound (reserved ⟹ dead), the union classifier strictly refines the grown decision, the live
eliminators faithfully compute their host folds, and the classifier axes are genuinely complementary. -/
structure GeneratorHonestyLedger : Prop where
  /-- SOUNDNESS: a reserved generator is semantically dead — grown-untyped AND operationally inert. -/
  reservedIsDead : ∀ {g : Generator}, semanticTier g = .reserved →
    (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
       {subject classifier : RawTerm scope},
       RawTerm.headGenerator subject = g → ¬ HasTypeDescPi profile context subject classifier) ∧
    (∀ {scope : Nat} (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope),
       RawTerm.hasRootStepSource (RawTerm.mkGen g payload children) = false)
  /-- REFINEMENT: the full-union static classifier strictly refines the grown-only untypability decision. -/
  unionStrictlyRefinesGrown :
    (∀ g : Generator, hasSomeTypingRule g = false → isUntypableHead g = true) ∧
    (∀ g : Generator, isUntypableHead g = false → hasSomeTypingRule g = true) ∧
    (∃ g : Generator, isUntypableHead g = true ∧ hasSomeTypingRule g = true)
  /-- FAITHFULNESS (representative): the `boolElim` eliminator computes its exact host fold `cond`. -/
  boolElimFaithful : ∀ {scope : Nat} (selector : Bool) (thenBranch elseBranch : RawTerm scope),
    StepStar (boolElimCell (rawBoolCell selector) thenBranch elseBranch)
      (cond selector thenBranch elseBranch)
  /-- NON-VACUITY: the two classifier axes are complementary — neither alone classifies the live table. -/
  axesComplementary :
    (Generator.gen_natElim.hasRedexHead = true ∧ hasSomeTypingRule .gen_natElim = false
       ∧ semanticTier .gen_natElim = .live) ∧
    (hasSomeTypingRule .gen_boolTrue = true ∧ Generator.gen_boolTrue.hasRedexHead = false
       ∧ semanticTier .gen_boolTrue = .live)

/-- **★ The honesty capstone holds.**  Every pillar discharged by its shipped zero-axiom theorem: soundness by
`semanticTierReservedSound`, refinement by `hasSomeTypingRuleStrictlyRefinesUntypableHead`, faithfulness by
`boolElimHostFold`, complementarity by the two `GeneratorSemanticTier` witnesses.  The single machine-checked
object certifying that the 197-generator table is honestly classified. -/
theorem generatorHonestyLedgerHolds : GeneratorHonestyLedger :=
  { reservedIsDead := fun reserved => semanticTierReservedSound reserved
    unionStrictlyRefinesGrown := hasSomeTypingRuleStrictlyRefinesUntypableHead
    boolElimFaithful := fun selector thenBranch elseBranch => boolElimHostFold selector thenBranch elseBranch
    axesComplementary := ⟨natElim_reducesButUntyped_stillLive, boolTrue_typedNotRedex_stillLive⟩ }

/-- Count the generators (of the 197) satisfying a `Bool` metric. -/
private def countWhere (metric : Generator → Bool) : Nat := (allGenerators.filter metric).length

-- ★ Build-time honesty COUNTS.  Fires on every default build that (re)elaborates this file: the ACTUAL number of
-- the 197 generators checked against each verification metric (not a slogan).  Every count folds a shipped
-- zero-axiom classifier over the full `Generator.fromTag` enumeration; `generatorHonestyLedgerHolds` above proves
-- those classifiers SOUND.  (A `#eval` print command takes no doc comment, so these are plain line comments.)
#eval IO.println s!"FX1Poly generator-honesty counts (of {allGenerators.length} generators):"
#eval IO.println s!"  typed by some engine (hasSomeTypingRule) : {countWhere hasSomeTypingRule}  [grown {countWhere (fun g => hasSomeTypingRule g && !isUntypableHead g)} | standalone-only {countWhere (fun g => hasSomeTypingRule g && isUntypableHead g)}]"
#eval IO.println s!"  beta/iota redex head (hasRedexHead)      : {countWhere (·.hasRedexHead)}  [also-typed {countWhere (fun g => hasSomeTypingRule g && g.hasRedexHead)} | reduces-but-untyped {countWhere (fun g => g.hasRedexHead && !hasSomeTypingRule g)}]"
#eval IO.println s!"  eta source head (hasEtaSourceHead)       : {countWhere (·.hasEtaSourceHead)}    beta/iota/eta union : {countWhere (·.hasRedexHeadBetaEta)}"
#eval IO.println s!"  semantically LIVE (typed or reduces)     : {countWhere (fun g => decide (semanticTier g = .live))}    RESERVED (neither) : {countWhere (fun g => decide (semanticTier g = .reserved))}"
#eval IO.println s!"  grown engine proves UNTYPABLE            : {countWhere isUntypableHead}  (= {allGenerators.length} - {countWhere (fun g => hasSomeTypingRule g && !isUntypableHead g)} grown-typed)"

end FX1Poly.Typed
