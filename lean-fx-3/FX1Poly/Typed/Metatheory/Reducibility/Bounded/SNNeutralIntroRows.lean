import FX1Poly.Typed.Metatheory.Reducibility.Bounded.TermIndexedFormationRows
import FX1Poly.Typed.Engine.Formation.IntroConstructorStrongNormalization

/-! # FX1Poly/Typed/SNNeutralIntroRows
    — the SN-neutral data/identity-constructor intro FT members (TYTAB-4 step 4, the intro side's
      recursive-constructor cases over SN-neutral output types)

The non-nullary introducers whose OUTPUT type is SN-neutral (its bounded reducibility candidate is
`IsStronglyNormalizing` — Σ / list / option / Id / bridge / nat all take the `neutral` arm; only
product / either / equiv get a content-bearing carrier-aware candidate).  For such an introducer the
member witness is uniform: the output type is reducible-as-type via the `neutral` arm (candidate
`IsStronglyNormalizing`), and the constructed cell lies in that candidate because it is SN — which the
intro-constructor SN engine (`introConstructorCellStronglyNormalizingOfChildren`) supplies from the
children's SN, themselves read off the obligation IHs through `stronglyNormalizing_of_memberAtBoundedSucc`.

This file ships the `gen_natSucc` (output `Nat`, a nullary neutral base type) and `gen_refl` (output
`Id A a a`, a term-indexed neutral former) rows — the two output-type shapes (nullary base + term-indexed
former) that need no cumulative-table machinery.  `optionSome` / `optionNone` / `listCons` / `listNil`
(cumulative-former output) and `pathLam` (bridge output) follow the identical witness shape over their
families' weak-head-rigidity.

## Zero-axiom verification

`stronglyNormalizing_of_memberAtBoundedSucc` (child SN off the IH) + `introConstructorCellStronglyNormalizingOfChildren`
(cell SN) + the `neutral` reducibility arm (output type) with weak-head-rigidity from the `rfl`-normality (nat) /
`termIndexedFormationGenerator_noWeakHeadStep` (Id).  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The `gen_natSucc` intro FT member: `natSucc(n)` is a bound-reducible member of `Nat` given `n` is.  Output
type `Nat` is the nullary neutral base type (candidate `IsStronglyNormalizing`); the cell `natSucc(n)` lies in it
because it is SN — the predecessor's SN (off the obligation IH) feeds the intro-constructor SN engine. -/
theorem fundamentalNatSuccIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren natSuccIntroRule.argShifts scope}
    {params : RawTermChildren natSuccIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ natSuccIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (natSuccIntroRule.memberCell scope args)
      (natSuccIntroRule.outputType scope args params) := by
  match args with
  | .childCons child .childNil =>
    intro targetScope substitution envReducible
    have childFundamental :
        FundamentalConclusionAtBoundedSucc env bound context child (natTypeCell (scope := scope)) :=
      premisesFundamental
        { scope := scope, context := context, subject := child, classifier := natTypeCell }
        (List.Mem.head _)
    have childSN : IsStronglyNormalizing (RawTerm.subst substitution child) :=
      stronglyNormalizing_of_memberAtBoundedSucc (childFundamental substitution envReducible)
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (fun reduct weakHeadStep =>
          RawTerm.isStepNormalForm_blocks_step
            (show RawTerm.isStepNormalForm (natTypeCell (scope := targetScope + 1)) from rfl)
            reduct weakHeadStep.toStep)
        (show Generator.gen_natCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_natCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_natCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_natSucc ⟨childSN, True.intro⟩

/-- The `gen_refl` intro FT member: `refl(a)` is a bound-reducible member of `Id A a a` given the witness `a` is
a member of its type `A`.  Output type `Id A a a` is a term-indexed neutral former (candidate
`IsStronglyNormalizing`, via the `neutral` arm at the term-indexed weak-head-rigidity); the cell `refl(a)` lies
in it because it is SN — the witness's SN (off the obligation IH) feeds the intro-constructor SN engine. -/
theorem fundamentalReflIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren reflIntroRule.argShifts scope}
    {params : RawTermChildren reflIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ reflIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (reflIntroRule.memberCell scope args)
      (reflIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons witness .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution envReducible
    have witnessFundamental :
        FundamentalConclusionAtBoundedSucc env bound context witness typeParam0 :=
      premisesFundamental
        { scope := scope, context := context, subject := witness, classifier := typeParam0 }
        (List.Mem.head _)
    have witnessSN : IsStronglyNormalizing (RawTerm.subst substitution witness) :=
      stronglyNormalizing_of_memberAtBoundedSucc (witnessFundamental substitution envReducible)
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (termIndexedFormationGenerator_noWeakHeadStep termIndexedFormerDescOf_idCode)
        (show Generator.gen_idCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_idCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_idCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_refl ⟨witnessSN, True.intro⟩

end FX1Poly.Typed
