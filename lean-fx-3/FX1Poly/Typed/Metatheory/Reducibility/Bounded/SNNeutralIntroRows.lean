import FX1Poly.Typed.Metatheory.Reducibility.Bounded.TermIndexedFormationRows
import FX1Poly.Typed.Engine.Formation.IntroConstructorStrongNormalization
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction

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
type `Nat` is the canonical-forms data candidate `dataTaitCandidate IsNatStructured` (DEP-NAT-MODEL pinned nat to
the `dataFlat` arm with the recursive structured-numeral predicate — the SAME candidate the dependent `natElim`
reducibility decomposes); the cell `natSucc(n)` lies in it because the predecessor is a structured member
(`natMemberAtBounded_dataTaitCandidate` off the obligation IH), and `natSuccStructuredMember` closes `succ` over
a structured member.  The `subst` commutes through `natSucc` by `rfl` (`subst_natSuccCell`), so the goal aligns
definitionally. -/
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
    have childMember : dataTaitCandidate IsNatStructured (RawTerm.subst substitution child) :=
      natMemberAtBounded_dataTaitCandidate (childFundamental substitution envReducible)
    refine ⟨dataTaitCandidate (flatCodeValuePredicate (natTypeCell (scope := targetScope + 1)).rootGenerator),
        ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataFlat
        (show (natTypeCell (scope := targetScope + 1)).rootGenerator.isFlatDataCode = true from rfl)
        (show (natTypeCell (scope := targetScope + 1)).rootGenerator.carrierCombinator? = none from rfl)
    · exact natSuccStructuredMember childMember

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

/-- The `gen_listCons` intro FT member: `cons(head, tail)` is a bound-reducible member of `List(A)` given
`head : A` and `tail : List(A)` are.  Output type `List(A)` is a cumulative neutral former (candidate
`IsStronglyNormalizing`, via the `neutral` arm at the cumulative weak-head-rigidity
`formationGenerator_noWeakHeadStep typingRuleDescOf_listCode`); the cell `cons(head, tail)` lies in it because
it is SN — both children's SN (off the obligation IHs) feed the intro-constructor SN engine. -/
theorem fundamentalListConsIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren listConsIntroRule.argShifts scope}
    {params : RawTermChildren listConsIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ listConsIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (listConsIntroRule.memberCell scope args)
      (listConsIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons head (.childCons tail .childNil), .childCons elementType .childNil =>
    intro targetScope substitution envReducible
    have headFundamental :
        FundamentalConclusionAtBoundedSucc env bound context head elementType :=
      premisesFundamental
        { scope := scope, context := context, subject := head, classifier := elementType }
        (List.Mem.head _)
    have tailFundamental :
        FundamentalConclusionAtBoundedSucc env bound context tail (listTypeCell elementType) :=
      premisesFundamental
        { scope := scope, context := context, subject := tail, classifier := listTypeCell elementType }
        (List.Mem.tail _ (List.Mem.head _))
    have headSN : IsStronglyNormalizing (RawTerm.subst substitution head) :=
      stronglyNormalizing_of_memberAtBoundedSucc (headFundamental substitution envReducible)
    have tailSN : IsStronglyNormalizing (RawTerm.subst substitution tail) :=
      stronglyNormalizing_of_memberAtBoundedSucc (tailFundamental substitution envReducible)
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep typingRuleDescOf_listCode)
        (show Generator.gen_listCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_listCons
        ⟨headSN, tailSN, True.intro⟩

/-- The `gen_optionSome` intro FT member: `some(a)` is a bound-reducible member of `option(A)` given `a : A`.
Output type `option(A)` is a cumulative neutral former (candidate `IsStronglyNormalizing`); the cell `some(a)`
lies in it because it is SN — the value's SN (off the obligation IH) feeds the intro-constructor SN engine. -/
theorem fundamentalOptionSomeIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren optionSomeIntroRule.argShifts scope}
    {params : RawTermChildren optionSomeIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ optionSomeIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (optionSomeIntroRule.memberCell scope args)
      (optionSomeIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons value .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution envReducible
    have valueFundamental :
        FundamentalConclusionAtBoundedSucc env bound context value typeParam0 :=
      premisesFundamental
        { scope := scope, context := context, subject := value, classifier := typeParam0 }
        (List.Mem.head _)
    have valueSN : IsStronglyNormalizing (RawTerm.subst substitution value) :=
      stronglyNormalizing_of_memberAtBoundedSucc (valueFundamental substitution envReducible)
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep typingRuleDescOf_optionCode)
        (show Generator.gen_optionCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_optionSome ⟨valueSN, True.intro⟩

/-- The `gen_listNil` intro FT member: `nil` is a bound-reducible member of `List(A)` (formedness premise on the
free `A`).  Output type `List(A)` is a cumulative neutral former (candidate `IsStronglyNormalizing`); the value
cell `nil` is a closed nullary normal-form leaf, hence SN, hence in that candidate — no member obligation is
consumed (the constructor is childless). -/
theorem fundamentalListNilIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren listNilIntroRule.argShifts scope}
    {params : RawTermChildren listNilIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (_premisesFundamental : ∀ obligation,
        obligation ∈ listNilIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (listNilIntroRule.memberCell scope args)
      (listNilIntroRule.outputType scope args params) := by
  match args, params with
  | .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution _envReducible
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep typingRuleDescOf_listCode)
        (show Generator.gen_listCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_listNil True.intro

/-- The `gen_optionNone` intro FT member: `none` is a bound-reducible member of `option(A)` (formedness premise
on the free `A`).  Output type `option(A)` is a cumulative neutral former (candidate `IsStronglyNormalizing`);
the value cell `none` is a closed nullary normal-form leaf, hence SN, hence in that candidate — no member
obligation is consumed (the constructor is childless). -/
theorem fundamentalOptionNoneIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren optionNoneIntroRule.argShifts scope}
    {params : RawTermChildren optionNoneIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (_premisesFundamental : ∀ obligation,
        obligation ∈ optionNoneIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (optionNoneIntroRule.memberCell scope args)
      (optionNoneIntroRule.outputType scope args params) := by
  match args, params with
  | .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution _envReducible
    refine ⟨IsStronglyNormalizing, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep typingRuleDescOf_optionCode)
        (show Generator.gen_optionCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_emptyCode by decide) rfl
    · exact introConstructorCellStronglyNormalizingOfChildren introRuleOf_optionNone True.intro

end FX1Poly.Typed
