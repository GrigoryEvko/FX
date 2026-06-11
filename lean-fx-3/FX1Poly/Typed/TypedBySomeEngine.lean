import FX1Poly.Typed.TypingHeadKindClassifier
import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Typed.HasTypeDescDataIntro

/-! # FX1Poly/Typed/TypedBySomeEngine — the honest TOTAL static-typing classifier over all 203 generators

The kernel's `Generator` enum has 203 constructors, but only a minority carry STATIC semantics — a typing rule
in SOME engine.  The shipped classifiers (`typingRoleOf`, `typingHeadKindOf`, `isUntypableHead`) route
EXCLUSIVELY through the GROWN engine `HasTypeDescPi`'s three tables (`typingRuleDescOf` / `introRuleDescOf` /
`elimRuleDescOf`).  Consequently they brand every data constructor / eliminator and every flat / base type-code
as "untypable" — e.g. `isUntypableHead gen_boolTrue = true` — even though `gen_boolTrue` IS typed (by the
data-intro engine `HasTypeDescDataIntro`).  That CONFLATES two genuinely different kinds of generator:

  * a MEANINGFUL head not typed by the grown engine but typed by a standalone engine (`gen_boolTrue`,
    `gen_fst`, `gen_arrowCode`, `gen_boolCode`, ...), versus
  * a genuinely RESERVED name typed by NO engine at all (`gen_hilbertSpace`, `gen_quantumGate`, ...).

`isUntypableHead` is sound only RELATIVE to the grown engine; read as a global "untyped" verdict it overclaims
on the standalone-engine heads.  This file ships the honest repair: `hasSomeTypingRule`, the first predicate
that consults EVERY typing engine's selector, so a generator is statically LIVE iff some engine types a cell
headed by it — distinguishing the meaningful data heads from the reserved-name zoo.

  * `hasSomeTypingRule` — the total classifier (decidable, `rfl`-computing): the union of the grown-engine
    trio, the flat formers (`flatTypingRuleDescOf`), the nullary base type-codes (`baseTypeRuleDescOf`), the
    nullary data constructors (`dataIntroNullaryRuleDescOf`), the sixteen standalone intro/elim heads (typed by
    `HasTypeDescNatIntro` / `IdIntro` / `OptionIntro` / `EitherIntro` / `PairIntro` / `ListIntro` / `BoolElim` /
    `IdElim` / `OptionMatch` / `EitherMatch` / `SigmaProjection`, which key on hardcoded arms not tables), and
    the two bespoke heads (`gen_var` / `gen_universeCode`).
  * LIVE / RESERVED witnesses by `rfl` — one per engine family, plus reserved exemplars.
  * **`isUntypableHead_overclaims_boolTrue` / `_fst`** (★) — the machine-checked HONESTY statements: the grown
    classifier reports `untypable = true` on heads that `hasSomeTypingRule` reports `true` (genuinely typed),
    pinning the overclaim.  `classifiersAgree_hilbertSpace` shows the two AGREE on a genuinely reserved head.

## Cascade-freedom

A future typed generator becomes one new `…RuleDescOf` row (absorbed by the matching `isSome` disjunct with no
change here) or, for a new standalone engine, one new `decide` disjunct.  The sixteen inline `decide`
equalities are the standalone engines that key on hardcoded arms rather than tables; folding them into
`…RuleDescOf`-style tables (so this classifier needs no per-engine disjunct) is the natural follow-on, as is
the negative-soundness characterization (`hasSomeTypingRule g = false → no engine types g`).

## Zero-axiom

`Option.isSome` over the pure-syntax selectors + `decide` over `DecidableEq Generator`, `||`-combined — NO
wildcard match (so propext-clean per the match-compiler discipline); every witness is `rfl` / `⟨rfl, rfl⟩`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The honest total static-typing classifier.**  `true` iff SOME typing engine types a cell headed by `g`.
Consults every engine's selector: the grown-engine trio (`typingRuleDescOf` / `introRuleDescOf` /
`elimRuleDescOf`), the flat data formers (`flatTypingRuleDescOf`), the nullary base type-codes
(`baseTypeRuleDescOf`), the nullary data constructors (`dataIntroNullaryRuleDescOf`), the sixteen standalone
intro/elim heads (which key on hardcoded arms, hence the explicit `decide` equalities), and the two bespoke
typed heads (`gen_var` / `gen_universeCode`).  Unlike `isUntypableHead`, this does NOT conflate the meaningful
data heads with the reserved-name zoo. -/
def hasSomeTypingRule (g : Generator) : Bool :=
  (typingRuleDescOf g).isSome || (introRuleDescOf g).isSome || (elimRuleDescOf g).isSome
  || (flatTypingRuleDescOf g).isSome || (baseTypeRuleDescOf g).isSome
  || (dataIntroNullaryRuleDescOf g).isSome
  || decide (g = .gen_natZero) || decide (g = .gen_natSucc) || decide (g = .gen_refl)
  || decide (g = .gen_optionNone) || decide (g = .gen_optionSome)
  || decide (g = .gen_eitherInl) || decide (g = .gen_eitherInr)
  || decide (g = .gen_pair) || decide (g = .gen_listNil) || decide (g = .gen_listCons)
  || decide (g = .gen_boolElim) || decide (g = .gen_idJ)
  || decide (g = .gen_optionMatch) || decide (g = .gen_eitherMatch)
  || decide (g = .gen_fst) || decide (g = .gen_snd)
  || decide (g = .gen_var) || decide (g = .gen_universeCode)
  || decide (g = .gen_intervalCode) || decide (g = .gen_bridgeCode)
  || decide (g = .gen_interval0) || decide (g = .gen_interval1)
  || decide (g = .gen_pathLam) || decide (g = .gen_pathApp)

/-! ## LIVE witnesses — one per engine family, by `rfl` -/

/-- Formation former (`typingRuleDescOf`). -/
theorem hasSomeTypingRule_piTyCode : hasSomeTypingRule .gen_piTyCode = true := rfl
/-- Flat data former (`flatTypingRuleDescOf`). -/
theorem hasSomeTypingRule_arrowCode : hasSomeTypingRule .gen_arrowCode = true := rfl
/-- Nullary base type-code (`baseTypeRuleDescOf`). -/
theorem hasSomeTypingRule_boolCode : hasSomeTypingRule .gen_boolCode = true := rfl
/-- Nullary data constructor (`dataIntroNullaryRuleDescOf`). -/
theorem hasSomeTypingRule_boolTrue : hasSomeTypingRule .gen_boolTrue = true := rfl
/-- Standalone-engine data constructor (`HasTypeDescNatIntro`). -/
theorem hasSomeTypingRule_natZero : hasSomeTypingRule .gen_natZero = true := rfl
/-- Standalone-engine data eliminator (`HasTypeDescSigmaProjection`). -/
theorem hasSomeTypingRule_fst : hasSomeTypingRule .gen_fst = true := rfl
/-- Grown-engine introduction (`HasTypeDescPi.piIntro`). -/
theorem hasSomeTypingRule_lam : hasSomeTypingRule .gen_lam = true := rfl
/-- Bespoke typed head (`HasTypeDesc.var`). -/
theorem hasSomeTypingRule_var : hasSomeTypingRule .gen_var = true := rfl

/-! ## RESERVED witnesses — genuinely typed by NO engine, by `rfl` -/

/-- A tier-★ extension name with no static semantics. -/
theorem hasSomeTypingRule_hilbertSpace : hasSomeTypingRule .gen_hilbertSpace = false := rfl
/-- The recursive eliminators are statically RESERVED (no formation/intro/elim engine types them). -/
theorem hasSomeTypingRule_natElim : hasSomeTypingRule .gen_natElim = false := rfl
/-- `gen_idCode` is only ever a CLASSIFIER (of `refl`), never formed as a subject. -/
theorem hasSomeTypingRule_idCode : hasSomeTypingRule .gen_idCode = false := rfl
/-- `gen_unit` IS typed (the UNIT-1 flip): the data-intro nullary table types the unit value at
`unitCode`.  This theorem previously pinned `= false` ("in no table"); the row landing flipped it. -/
theorem hasSomeTypingRule_unit : hasSomeTypingRule .gen_unit = true := rfl
/-- Another reserved-zoo name. -/
theorem hasSomeTypingRule_quantumGate : hasSomeTypingRule .gen_quantumGate = false := rfl

/-! ## ★ The conflation exposer — `isUntypableHead` overclaims on genuinely-typed heads -/

/-- **★ The grown-only classifier OVERCLAIMS on `gen_boolTrue`.**  It reports `isUntypableHead = true`, yet
`gen_boolTrue` is statically typed (by the data-intro engine), as the honest classifier reports.  This is the
machine-checked statement of the conflation that `hasSomeTypingRule` repairs: "untypable by the grown engine"
is NOT "typed by no engine". -/
theorem isUntypableHead_overclaims_boolTrue :
    isUntypableHead .gen_boolTrue = true ∧ hasSomeTypingRule .gen_boolTrue = true := ⟨rfl, rfl⟩

/-- **★ The same overclaim on the Σ first projection `gen_fst`** (typed by `HasTypeDescSigmaProjection`). -/
theorem isUntypableHead_overclaims_fst :
    isUntypableHead .gen_fst = true ∧ hasSomeTypingRule .gen_fst = true := ⟨rfl, rfl⟩

/-- **★ Contrast: on a genuinely reserved head the two classifiers AGREE** — both report no typing.  So the
honest classifier strictly REFINES `isUntypableHead`: it agrees on the genuinely-reserved names and only
disagrees (correctly) on the standalone-engine heads. -/
theorem classifiersAgree_hilbertSpace :
    isUntypableHead .gen_hilbertSpace = true ∧ hasSomeTypingRule .gen_hilbertSpace = false := ⟨rfl, rfl⟩

end FX1Poly.Typed
