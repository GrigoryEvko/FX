import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundExceedsUnionDischarge
import FX1Poly.Typed.Metatheory.Reducibility.Fundamental.BoundedGrownFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedFormationLeafArms
import FX1Poly.Typed.Engine.Union.HasTypeUnion

/-! # FX1Poly/Typed/BoundedUnionFundamental
    — the NATIVE union fundamental theorem, conditional on the three table-arm FTs (TYTAB-4 step 3)

The native-union analogue of `HasTypeDescPi.fundamentalAtBoundedSucc` (`BoundedGrownFundamental.lean`): given a
`BoundExceedsUnion env bound d` budget, every `HasTypeUnionOver` derivation satisfies the `+1`-closing
bound-reducible conclusion `FundamentalConclusionAtBoundedSucc`.  Dispatch by `BoundExceedsUnion.rec` — induction
on the BUDGET, mirroring the grown `BoundExceedsPi.rec` dispatch (the universe leaf gets its `belowBound` from the
budget, no global invariant).

This is the SKELETON: the three STRUCTURAL arms are discharged inline from shipped building blocks, and the three
TABLE arms (`formationRule` / `intro` / `elim`) are taken as explicit FT premises — exactly as the grown
`fundamentalAtBoundedSuccFromFormation` took its single `formationFundamental` premise.  TYTAB-4 step 4 discharges
the three premises at the kernel bundle (the genuine FTGEN-bounded construction over the rule tables); step 5
reflects the closed instance to native SN.

## The six native arms

  * `formationRule` / `intro` / `elim` — the three table-arm FT premises, fed the rec's per-obligation IH
    (`premisesFundamental`), the membership gate (`isFormationRule`/`isIntro`/`isElim`), and (formation) the
    level-source gate / (intro) the `sideCondition`.
  * `conv` — the verbatim grown conv block (`BoundedGrownFundamental.lean` lines 73-81): read the reclassifier
    universe member off its IH, gate-extract `belowBound`, transport the subject member along the conversion.
  * `var` — `fundamentalVarAtBoundedSucc` (the leaf, bound-independent).
  * `universeFormation` — `fundamentalUniverseFormationAtBoundedSucc` fed the budget's carried `belowBound`.

## Zero-axiom verification

One `BoundExceedsUnion.rec` application; arms reuse the shipped grown master / leaf FTs / conv transport helpers
(`convMemberUnderClosingSubstitutionBounded` / `reducibleTypeAtBoundFromUniverseMemberBounded` /
`universeCodeReducibleAtBounded_belowBound`).  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- **The native union fundamental theorem, conditional on the three table-arm FTs (TYTAB-4 step 3).**  Under a
`BoundExceedsUnion env bound d` budget plus the `formationRule` / `intro` / `elim` table-arm FT premises, every
`HasTypeUnionOver` derivation satisfies the `+1`-closing bound-reducible conclusion.  `BoundExceedsUnion.rec`
dispatch (induction on the budget); the three structural arms are discharged inline (conv→the verbatim grown
block, var/universeFormation→the shipped leaf FTs fed the budget gate), the three table arms are the premises
(discharged at the kernel bundle in step 4). -/
theorem HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms {bundle : TypingTableBundle} {profile : PolyProfile}
    (env : Nat → Nat) (bound : Nat)
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope} {generator : Generator}
        {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
        {rule : FormationRule} {levels : List LevelExpr} {carrier : RawTerm scope} {level : LevelExpr}
        {flag : UniverseFlag},
        bundle.formationRule generator = some rule →
        (∀ levelExpr, levelExpr ∈ level :: levels → LevelExpr.denote levelExpr env < bound) →
        (∀ obligation (_hmem : obligation ∈ rule.obligations profile context children levels carrier level flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
          (rule.outputType scope levels level flag))
    (introFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : IntroRule}
        {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
        {level0 level1 : LevelExpr} {flag : UniverseFlag},
        bundle.intro generator = some rule →
        rule.sideCondition scope args →
        (∀ obligation (_hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
          (rule.outputType scope args params))
    (elimFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope} {generator : Generator} {rule : ElimRule}
        {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
        {level0 level1 : LevelExpr} {flag : UniverseFlag},
        bundle.elim generator = some rule →
        (∀ obligation (_hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
          FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
            obligation.classifier) →
        FundamentalConclusionAtBoundedSucc env bound context (rule.memberCell scope args)
          (rule.outputType scope args params)) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
      (d : HasTypeUnionOver bundle profile context subject classifier),
      BoundExceedsUnion env bound d →
        FundamentalConclusionAtBoundedSucc env bound context subject classifier := by
  intro scope context subject classifier d budget
  refine BoundExceedsUnion.rec
    (motive := fun {_scope} {_context} {_subject} {_classifier} _d _budget =>
      FundamentalConclusionAtBoundedSucc env bound _context _subject _classifier)
    ?formationRule ?intro ?elim ?conv ?var ?universeFormation budget
  · -- formationRule: the table-arm FT premise
    intro _scope _context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold formationLevelsBelowBound _premisesBudget premisesFundamental
    exact formationFundamental isFormationRule formationLevelsBelowBound premisesFundamental
  · -- intro: the table-arm FT premise
    intro _scope _context generator rule args params level0 level1 flag isIntro sideHolds
      _premisesHold _premisesBudget premisesFundamental
    exact introFundamental isIntro sideHolds premisesFundamental
  · -- elim: the table-arm FT premise
    intro _scope _context generator rule args params level0 level1 flag isElim
      _premisesHold _premisesBudget premisesFundamental
    exact elimFundamental isElim premisesFundamental
  · -- conv: the verbatim grown conv block (sub-budgets unused; level gate-extracted from the IH member)
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped _subjectBudget _reclassifierBudget subjectFundamental reclassifierFundamental
    intro _targetScope substitution envReducible
    have reMember := reclassifierFundamental substitution envReducible
    rw [subst_universeCodeCell] at reMember
    obtain ⟨reCand, reCandReducible, reCandIn⟩ := reMember
    have belowBound := universeCodeReducibleAtBounded_belowBound reCandReducible
    exact convMemberUnderClosingSubstitutionBounded env bound
      (subjectFundamental substitution envReducible)
      (reducibleTypeAtBoundFromUniverseMemberBounded env bound ⟨reCand, reCandReducible, reCandIn⟩ belowBound)
      converts
  · -- var: the shipped leaf FT
    intro _scope context index
    exact fundamentalVarAtBoundedSucc env bound context index
  · -- universeFormation: the shipped leaf FT fed the budget's carried belowBound
    intro _scope context levelExpr flag belowBound
    exact fundamentalUniverseFormationAtBoundedSucc env bound context levelExpr flag belowBound

end FX1Poly.Typed
