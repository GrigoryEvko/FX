import FX1Poly.Typed.Metatheory.Reducibility.Bounded.TermIndexedFormationRows
import FX1Poly.Typed.Engine.Formation.IntroConstructorStrongNormalization
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate

/-! # FX1Poly/Typed/SNNeutralIntroRows
    — the SN-neutral data/identity-constructor intro FT members (TYTAB-4 step 4, the intro side's
      recursive-constructor cases over SN-neutral output types)

The non-nullary introducers over data / identity output types, in TWO witness shapes that the DEP-* model
migrations split apart:

  * **SN-neutral output** (`gen_refl`, output `Id A a a` — a term-indexed neutral former whose bounded
    candidate is `IsStronglyNormalizing`): the output type is reducible-as-type via the `neutral` arm, and the
    constructed cell lies in that candidate because it is SN, supplied from the children's SN (off the
    obligation IHs through `stronglyNormalizing_of_memberAtBoundedSucc`) by the intro-constructor SN engine
    `introConstructorCellStronglyNormalizingOfChildren`.
  * **Flat-data output** (`gen_natSucc` → `Nat`; `gen_listCons` / `gen_listNil` → `List A`; `gen_optionSome`
    / `gen_optionNone` → `option A`): DEP-NAT/LIST/OPTION-MODEL pinned these data codes to the content-free
    `dataFlat` arm at their value candidates (`dataTaitCandidate IsNatStructured` / `IsListStructured` /
    `isOptionValue`), so the dependent eliminators can read the scrutinee's canonical structure.  The
    constructed cell lies in the candidate by its constructor closure member — `natSuccStructuredMember` /
    `listConsStructuredMember` (RECURSIVE: the same-type child member off `nat`/`listMemberAtBounded_dataTait\
    Candidate`), `optionSomeDataTaitMember` (the foreign payload's SN), or the nullary value members
    `listNilStructuredMember` / `dataTaitCandidate.memberOfValue` for `nil` / `none`.

`pathLam` (bridge output) follows the SN-neutral shape over its family's weak-head-rigidity.

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
        (show (natTypeCell (scope := targetScope + 1)).rootGenerator.isTermIndexedCode = false from rfl)
        (show (natTypeCell (scope := targetScope + 1)).rootGenerator.unaryCarrierCombinator? = none from rfl)
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
    -- DEP-ID: `Id A a a` is term-indexed-REDUCIBLE (`gen_idCode.isTermIndexedCode = true`, carved out of the
    -- flat codes), so its reducibility candidate reads BOTH endpoints off the arity-3 cell — the two-endpoint
    -- based-refl predicate `isReflValueBetween a a` via the `dataTermIndexed` arm.  `refl(a)` lies in it by
    -- `reflDataTaitMemberBetween` (the witness's SN, off the obligation IH, reaches the value; both endpoints
    -- are the SAME reflected point `a`, so both endpoint conversions are `Conv.refl`).
    refine ⟨dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode
        (RawTerm.subst substitution witness) (RawTerm.subst substitution witness)),
        ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataTermIndexed
    · exact reflDataTaitMemberBetween witnessSN (Conv.refl _) (Conv.refl _)

/-- The `gen_listCons` intro FT member: `cons(head, tail)` is a bound-reducible member of `List(A)` given
`head : A` and `tail : List(A)` are.  Output type `List(A)` is a content-free flat data former (DEP-LIST-MODEL
pins `gen_listCode` to `dataTaitCandidate IsListStructured` via the `dataFlat` arm); the cell `cons(head, tail)`
lies in it by `listConsStructuredMember` — the head's SN (off its obligation IH) and the tail's STRUCTURED
membership (off its obligation IH through `listMemberAtBounded_dataTaitCandidate`, the recursive tail bridge,
the `natSucc` predecessor analogue) close `cons` over the structured candidate at OPEN scope. -/
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
    -- GATE1-SWAP4: `List(A)` routes through the UNARY carrier-aware arm (`dataUnaryCarrierAware` @ `listLike`),
    -- so its candidate is the RECURSIVE `reachAwareListCandidate elementCandidate`.  The head's element membership
    -- comes off the head obligation; the tail's reach-aware membership off the tail obligation
    -- (`listMemberAtBounded_carrierAware`), realigned to the head's element candidate by determinism.
    obtain ⟨elementCandidate, elementReducible, headInElement⟩ := headFundamental substitution envReducible
    obtain ⟨tailElementCandidate, tailElementReducible, tailReachAware⟩ :=
      listMemberAtBounded_carrierAware (tailFundamental substitution envReducible)
    have candidatesEquiv : PointwiseIff tailElementCandidate elementCandidate :=
      ReducibleTypeAtBounded.deterministic tailElementReducible elementReducible
    have tailReachAwareAligned :
        reachAwareListCandidate elementCandidate (RawTerm.subst substitution tail) :=
      (reachAwareListCandidate_congr candidatesEquiv (RawTerm.subst substitution tail)).mp tailReachAware
    refine ⟨reachAwareListCandidate elementCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataUnaryCarrierAware
        (combinator := UnaryCarrierCombinator.listLike) elementReducible
    · exact reachAwareListCandidate.memberOfReducibleCons elementReducible.isReducibilityCandidate
        headInElement tailReachAwareAligned

/-- The `gen_optionSome` intro FT member: `some(a)` is a bound-reducible member of `option(A)` given `a : A`.
Output type `option(A)` routes through the UNARY carrier-aware arm (`dataUnaryCarrierAware` @ `optionLike`), so
its bounded candidate is `reachAwareOptionCandidate elementCandidate` over the element type's candidate (taken
directly off the value obligation's element-reducibility at the bound); `some(a)` lies in it by
`memberOfReducibleSome` — the some-reach clause holds because `some(a)` reaches only itself, carrying `a`'s
element membership. -/
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
    obtain ⟨elementCandidate, elementReducible, valueInElement⟩ :=
      valueFundamental substitution envReducible
    refine ⟨reachAwareOptionCandidate elementCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataUnaryCarrierAware
        (combinator := UnaryCarrierCombinator.optionLike) elementReducible
    · exact reachAwareOptionCandidate.memberOfReducibleSome
        elementReducible.isReducibilityCandidate valueInElement

/-- The `gen_listNil` intro FT member: `nil` is a bound-reducible member of `List(A)` (formedness premise on the
free `A`).  Output type `List(A)` routes through the UNARY carrier-aware arm (`dataUnaryCarrierAware` @ `listLike`)
post gate-1 swap 4: the element type's reducibility is recovered from the formedness obligation — a universe MEMBER
of `Type@level0` at the bound — bridged to an element-TYPE reducibility by
`reducibleTypeAtBoundFromUniverseMemberBounded` (below-bound gate read back off the universe code's own
reducibility).  The bounded candidate is therefore `reachAwareListCandidate elementCandidate`, and the value cell
`nil` lies in it by `reachAwareListCandidate_memberOfNormalNil`: it is a closed nullary normal-form leaf whose
cons-reach clauses are vacuous (`nil` reaches no `cons`).  The recursive twin of
`fundamentalOptionNoneIntroRowAtBoundedSucc`. -/
theorem fundamentalListNilIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren listNilIntroRule.argShifts scope}
    {params : RawTermChildren listNilIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ listNilIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (listNilIntroRule.memberCell scope args)
      (listNilIntroRule.outputType scope args params) := by
  match args, params with
  | .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution envReducible
    have typeMember :=
      premisesFundamental
        { scope := scope, context := context, subject := typeParam0,
          classifier := universeCodeCell level0 flag }
        (List.Mem.head _)
        substitution envReducible
    rw [subst_universeCodeCell] at typeMember
    have belowBound : LevelExpr.denote level0 env < bound := by
      obtain ⟨_universeCandidate, universeReducible, _typeParamInUniverse⟩ := typeMember
      exact universeCodeReducibleAtBounded_belowBound universeReducible
    obtain ⟨elementCandidate, elementReducible⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound typeMember belowBound
    refine ⟨reachAwareListCandidate elementCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataUnaryCarrierAware
        (combinator := UnaryCarrierCombinator.listLike) elementReducible
    · exact reachAwareListCandidate_memberOfNormalNil

/-- The `gen_optionNone` intro FT member: `none` is a bound-reducible member of `option(A)` (formedness premise
on the free `A`).  Output type `option(A)` routes through the UNARY carrier-aware arm (`dataUnaryCarrierAware`
@ `optionLike`): the element type's reducibility is recovered from the formedness obligation — a universe MEMBER
of `Type@level0` at the bound — bridged to an element-TYPE reducibility by
`reducibleTypeAtBoundFromUniverseMemberBounded`, whose below-bound gate is read back off the universe code's own
reducibility (`universeCodeReducibleAtBounded_belowBound`).  The bounded candidate is therefore
`reachAwareOptionCandidate elementCandidate`, and the value cell `none` lies in it by `memberOfNormalNone`: it is
a closed nullary normal-form leaf whose some-reach clause is vacuous (`none` reaches no `some`). -/
theorem fundamentalOptionNoneIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren optionNoneIntroRule.argShifts scope}
    {params : RawTermChildren optionNoneIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ optionNoneIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (optionNoneIntroRule.memberCell scope args)
      (optionNoneIntroRule.outputType scope args params) := by
  match args, params with
  | .childNil, .childCons typeParam0 .childNil =>
    intro targetScope substitution envReducible
    have typeMember :=
      premisesFundamental
        { scope := scope, context := context, subject := typeParam0,
          classifier := universeCodeCell level0 flag }
        (List.Mem.head _)
        substitution envReducible
    rw [subst_universeCodeCell] at typeMember
    have belowBound : LevelExpr.denote level0 env < bound := by
      obtain ⟨_universeCandidate, universeReducible, _typeParamInUniverse⟩ := typeMember
      exact universeCodeReducibleAtBounded_belowBound universeReducible
    obtain ⟨elementCandidate, elementReducible⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound typeMember belowBound
    refine ⟨reachAwareOptionCandidate elementCandidate, ?typeReducible, ?valueMember⟩
    · exact ReducibleTypeStepBounded.dataUnaryCarrierAware
        (combinator := UnaryCarrierCombinator.optionLike) elementReducible
    · exact reachAwareOptionCandidate.memberOfNormalNone
        (show RawTerm.isStepNormalForm optionNoneCell from rfl)

end FX1Poly.Typed
