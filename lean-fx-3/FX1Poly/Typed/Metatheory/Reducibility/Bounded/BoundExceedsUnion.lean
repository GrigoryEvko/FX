import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Tier0.Type.Level.LevelExprSimplify

/-! # FX1Poly/Typed/BoundExceedsUnion
    — the per-derivation universe-level budget for the NATIVE union engine (TYTAB-4 step 1)

`BoundExceedsPi.lean` (BFT-12a) defines the per-derivation universe-level budget for the GROWN engine
`HasTypeDescPi`, on which `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c) dispatches by `BoundExceedsPi.rec`
(induction on the BUDGET, not the derivation — so the universe leaves get their `belowBound` from the budget).
The NATIVE union fundamental theorem (TYTAB-4 / the gate-1 keystone of TYTAB-2-FT) must mirror this: it will
dispatch by `BoundExceedsUnion.rec` over the six native `HasTypeUnionOver` arms.  This file is that budget.

## What each arm carries (mirroring BoundExceedsPi, specialized to the union's structure)

The union `HasTypeUnionOver` is a SINGLE inductive (no mutual telescope — every premise is reflected into a
`∀ obligation ∈ rule.obligations …` list quantified inside the arm), so this budget is a SINGLE indexed `Prop`
family (simpler than the mutual `BoundExceedsPi`/`BoundExceedsPiTelescope`).

  * `conv` threads the subject + reclassifier sub-budgets (their universe levels are gate-extracted from the
    members the IHs produce, never from a budget — exactly as BoundExceedsPi.conv).
  * `formationRule` threads a per-obligation sub-budget for every child obligation, PLUS the one per-term gate
    the union carries directly: `formationLevelsBelowBound`, that the bound exceeds the denotation of every
    LEVEL SOURCE `level :: levels` of the formation node.  The formation arm's output is a universe code
    `Type@L`, and the FT needs `denote L < bound`; across all four families `L` is built SOLELY from the level
    sources — `lzero` for a nullary base-type former (so `0 < bound`, implied since `denote level env ≥ 0`),
    `lmaxAll levels` for the flat / cumulative formers, and the carrier `level` for the term-indexed formers.
    Carrying the level-source bounds rather than the OUTPUT-TERM equation keeps `BoundExceedsUnion.existsBound`
    BUNDLE-GENERIC (it reads `level` / `levels` straight off the node, never decoding the abstract bundle's
    output term); the FT — which must inspect the output to build its reducibility witness anyway — decodes the
    output shape and reads the matching level bound.  This is the union analogue of the grown formation arm's
    universe-level fuel, generalized from the single `nullaryBelowBound` `0 < bound` to the whole level set.
  * `intro` / `elim` thread ONLY the per-obligation sub-budgets: their outputs are DATA types / substituted
    codomains (a constructor's data type, an eliminator's result type), NOT universe codes, so there is no
    universe-level gate to carry — the data type's reducibility is the SN candidate (via the bounded `neutral`
    arm) and the codomain's comes from its own formation, neither needing a budget level.
  * `var` carries nothing (a variable touches no universe level of its own).
  * `universeFormation` carries `belowBound : denote (lsucc levelExpr) < bound` — the native universe leaf, the
    direct analogue of the grown formation engine's `universeFormation` fuel: `Type@levelExpr : Type@(levelExpr+1)`
    has its classifier level `levelExpr+1` budget-carried (no IH to gate-extract it from).

## The discharge plan (TYTAB-4 steps 2-5)

`BoundExceedsUnion.existsBound` (step 2) will supply a bound + budget for any concrete union derivation (recurse
over the obligation lists with SUM bounds).  Then `HasTypeUnion.fundamentalAtBoundedSucc` (step 3) runs
`BoundExceedsUnion.rec`: var / universeFormation / conv mirror the shipped bounded leaf / inline arms; the three
table arms consume their generic bounded FTs (step 4).  The closed reflection (step 5) gives
`IsStronglyNormalizing subject` = the native SN gate.

## Zero-axiom verification

A single strictly-positive indexed inductive `Prop` family over `HasTypeUnionOver` derivations (`BoundExceedsUnion`
appears only in premises).  Inductives introduce no axioms.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The per-derivation universe-level budget for the native union engine (indexed inductive `Prop`).**
`BoundExceedsUnion env bound d` threads the budget down every `HasTypeUnionOver` constructor; the per-term gates
it carries directly are the formation arm's level-source bounds (`formationLevelsBelowBound`) and the
`universeFormation` leaf's classifier-level fuel (`belowBound`).
The native analogue of `BoundExceedsPi`; SINGLE (non-mutual) because the union reflects its premises into
`∀ obligation ∈ …` lists rather than a sibling telescope inductive. -/
inductive BoundExceedsUnion {bundle : TypingTableBundle} {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    {scope : Nat} → {context : TypingContext profile scope} → {subject classifier : RawTerm scope} →
    HasTypeUnionOver bundle profile context subject classifier → Prop where
  | formationRule {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : FormationRule)
      (levels : List LevelExpr) (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
      (isFormationRule : bundle.formationRule generator = some rule)
      {premisesHold : ∀ obligation,
        obligation ∈ rule.obligations profile context children levels carrier level flag →
          HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier}
      (usabilityHolds : ∀ obligation,
        obligation ∈ rule.obligations profile context children levels carrier level flag →
          obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
      (formationLevelsBelowBound : ∀ levelExpr, levelExpr ∈ level :: levels →
        LevelExpr.denote levelExpr env < bound)
      (premisesBudget : ∀ obligation
        (hmem : obligation ∈ rule.obligations profile context children levels carrier level flag),
        BoundExceedsUnion env bound (premisesHold obligation hmem)) :
      BoundExceedsUnion env bound (HasTypeUnionOver.formationRule context generator payload children
        rule levels carrier level flag isFormationRule premisesHold usabilityHolds)
  | intro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : IntroRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isIntro : bundle.intro generator = some rule)
      (sideHolds : rule.sideCondition scope args)
      {premisesHold : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
          HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier}
      (usabilityHolds : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
          obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
      (premisesBudget : ∀ obligation
        (hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
        BoundExceedsUnion env bound (premisesHold obligation hmem)) :
      BoundExceedsUnion env bound (HasTypeUnionOver.intro context generator rule args params
        level0 level1 flag isIntro sideHolds premisesHold usabilityHolds)
  | elim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : ElimRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isElim : bundle.elim generator = some rule)
      {premisesHold : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
          HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier}
      (usabilityHolds : ∀ obligation,
        obligation ∈ rule.obligations scope context args params level0 level1 flag →
          obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
      (premisesBudget : ∀ obligation
        (hmem : obligation ∈ rule.obligations scope context args params level0 level1 flag),
        BoundExceedsUnion env bound (premisesHold obligation hmem)) :
      BoundExceedsUnion env bound (HasTypeUnionOver.elim context generator rule args params
        level0 level1 flag isElim premisesHold usabilityHolds)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      {typed : HasTypeUnionOver bundle profile context subject classifier}
      {converts : Conv classifier reclassifier}
      {reclassifierTyped : HasTypeUnionOver bundle profile context reclassifier
        (universeCodeCell levelExpr flag)}
      (subjectBudget : BoundExceedsUnion env bound typed)
      (reclassifierBudget : BoundExceedsUnion env bound reclassifierTyped) :
      BoundExceedsUnion env bound (HasTypeUnionOver.conv levelExpr flag typed converts reclassifierTyped)
  | var {scope : Nat} (context : TypingContext profile scope) (index : Fin scope)
      {useModality : ObligationModality}
      (isAccessible : context.isAccessibleAtModality index useModality = true) :
      BoundExceedsUnion env bound (HasTypeUnionOver.var context index isAccessible)
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (belowBound : LevelExpr.denote levelExpr.lsucc env < bound) :
      BoundExceedsUnion env bound (HasTypeUnionOver.universeFormation context levelExpr flag)

end FX1Poly.Typed
