import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType

/-! # FX1Poly/Typed/HasTypeUnionMatchInversion — NATIVE-37 part d: per-head inversions for the
    two-branch-match eliminator heads (boolElim / optionMatch / eitherMatch) + their REVERSE ADEQUACY.

This file extends the inversion substrate established in `HasTypeUnionInversion` (four heads:
pathLam / lam / natElim / natSucc) to the three two-branch-match data-eliminator heads.  All three are
survivors of the SAME unified union arm — `elim` (the TYTAB-1 elim-collapse arm that subsumes the six
former eliminator arms) — pinned to their respective rows by the shipped `elimRuleOf_cases` eleven-row
inverter.

## The per-head inversion (the established recipe, replicated against the unified elim arm)

Each inversion takes a FREE subject + a `subjectShape : subject = <head-cell>` hypothesis, then
`induction`s the union derivation (safe at a free index — never at the concrete cell index).  In the
unified `elim` arm, `elimRuleOf_cases` splits into the eleven eliminator rows; exactly ONE row survives
— the row whose `memberCell` head IS this inversion's head — and surfaces the three RECURSIVE union
premises (scrutinee + both branches) by feeding `List.Mem` witnesses (`.head` / `.tail .head` /
`.tail .tail .head`) into the arm's `premisesHold` obligation discharger.  Each of the other ten rows
dies by `elimMemberCellRootGenerator` head-clash: its member-cell root generator is the row's generator,
which clashes with this head.  Every non-`elim` arm dies by one of the prior killer classes (table-none
`rfl`, `subjectIs…` head-clash, spec/row head-clash).

The row's params supply the existential type indices (`optionMatch` / `eitherMatch`'s element types) and
the result type, which the `induction` motive equates to the ambient classifier — so `Conv.refl`
discharges each reverse-adequacy reclassification leg.

## ★ Reverse adequacy (closes the boolElim / optionMatch / eitherMatch share of fold 29)

For each family, a theorem of the form: a union typing of a `<head>`-headed subject yields the surfaced
RECURSIVE union premises (the honest surplus — the union types MORE, e.g. an eliminator whose scrutinee
is a computed value), AND when those surfaced premises happen to land in the bespoke engines (scrutinee
in the data-intro engine, branches in the grown engine) the bespoke `HasTypeDesc<Family>` derivation is
RECONSTRUCTED.  The honest-surplus disjunct is precisely the gap between the union-recursive scrutinee /
branch premises and the bespoke engine-specific premises: the union admits a scrutinee typed by ANY
native family, whereas the bespoke engine demands the inlined nullary data-intro row (`dataIntroNullary`) /
`HasTypeDescOptionIntro` / `HasTypeDescEitherIntro` and grown branches.  The reverse adequacy is therefore stated in the
RELATIVIZED form: the union derivation yields the bespoke derivation GIVEN that the surfaced premises are
bespoke-shaped (the reconstruction hypotheses); without them the surfaced union premises are the surplus.

## Zero-axiom

Free-subject `induction` + the shipped eleven-row inverter `elimRuleOf_cases` + the member-cell
head-projection `elimMemberCellRootGenerator` + head-generator no-confusion + `rcases subjectShape with
⟨⟩` child drilling + `premisesHold` discharge via `List.Mem.head` / `.tail` witnesses.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionMatchInversion.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the boolElim head -/

/-- **★ Inversion at the boolElim head (DEPENDENT).**  A union typing of a `boolElimCell`-headed subject is
EXACTLY a dependent two-branch-match typing at the `gen_boolElim` row: the scrutinee is union-typed at
`Bool`, the then-branch at `subst0 motive boolTrueCell`, the else-branch at `subst0 motive boolFalseCell`
(the motive at the boolean VALUES), and the eliminator's natural output `subst0 motive scrutinee` is
convertible to the ambient classifier.  The branch typings are classifier-INDEPENDENT (so the `conv` arm
passes them through and only composes the output-conversion leg); the conversion leg is what the iota
subject-reduction uses to retype the reduct.  No grown disjunct: `boolElimCell` is untypable in the grown
engine (a recursive eliminator in no host root). -/
theorem HasTypeUnion.invertAtBoolElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = boolElimCell motive scrutinee thenBranch elseBranch) :
    HasTypeUnion profile context scrutinee boolTypeCell ∧
    HasTypeUnion profile context thenBranch (RawTerm.subst0 motive boolTrueCell) ∧
    HasTypeUnion profile context elseBranch (RawTerm.subst0 motive boolFalseCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `boolElim` row (no type params, `params = childNil`;
  -- obligation order `[scrutinee, thenBranch, elseBranch, motive]`; `outputType = subst0 motive scrutinee`).
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := boolElimRule)
      (show elimRuleOf Generator.gen_boolElim = some boolElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argScrut (.childCons _argThen (.childCons _argElse .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      outputConv⟩

/-- **★ Inversion at the boolElim head, ALL FOUR premises (incl. the extended-context motive).**  The
`invertAtBoolElimHead` companion that ADDITIONALLY surfaces the motive obligation — the motive is union-typed
at a universe (`∃ level flag`) over the one-`bool`-binder extended context `context.cons boolTypeCell` (the
`boolElimRule` fourth obligation).  This is exactly the premise needed to REBUILD a `boolElim` cell when one
of its children steps (the eliminator-congruence subject reduction, gate 2 of #1697): the rebuilt cell's
`elim` arm requires all four obligations, and the motive one is the only one the plain three-premise
inversion drops.  Same recipe: induct the union derivation at a free subject, refute every arm except the
`gen_boolElim` elim survivor, which surfaces all four obligations from `premisesHold`; the `conv` arm threads
them through (classifier-independent) and composes its conversion onto the output leg. -/
theorem HasTypeUnion.invertAtBoolElimHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = boolElimCell motive scrutinee thenBranch elseBranch) :
    HasTypeUnion profile context scrutinee boolTypeCell ∧
    HasTypeUnion profile context thenBranch (RawTerm.subst0 motive boolTrueCell) ∧
    HasTypeUnion profile context elseBranch (RawTerm.subst0 motive boolFalseCell) ∧
    (∃ (motiveLevel : LevelExpr) (motiveFlag : UniverseFlag),
      HasTypeUnion profile (context.cons boolTypeCell) motive
        (universeCodeCell motiveLevel motiveFlag)) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `boolElim` row surfacing ALL four obligations;
  -- the motive obligation's universe levels are the row's existential `level0`/`flag`.
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := boolElimRule)
      (show elimRuleOf Generator.gen_boolElim = some boolElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argScrut (.childCons _argThen (.childCons _argElse .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      ⟨level0, flag, obligationsHold _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))⟩,
      outputConv⟩

/-! ## (1) Inversion at the optionMatch head -/

/-- **★ Inversion at the optionMatch head (DEPENDENT).**  A union typing of an `optionMatchCell`-headed
subject is EXACTLY a dependent two-branch-match typing at the `gen_optionMatch` row: for some element type
`A`, the scrutinee is union-typed at `option(A)`, the None branch is union-typed at the nullary
`subst0 motive optionNoneCell`, the Some branch is union-typed at the dependent some-branch type
`optionMatchDependentSomeBranchType motive A = (a : A) → motive (some a)`, the eliminator output
`subst0 motive scrutinee` is the classifier, and the motive is union-typed at a universe under one
`option(A)` binder.  No grown disjunct (`optionMatchCell` is a recursive eliminator, untypable in the
grown engine). -/
theorem HasTypeUnion.invertAtOptionMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionMatchCell motive noneBranch someBranch scrutinee) :
    ∃ elementType : RawTerm scope,
      HasTypeUnion profile context scrutinee (optionTypeCell elementType) ∧
      HasTypeUnion profile context noneBranch (RawTerm.subst0 motive optionNoneCell) ∧
      HasTypeUnion profile context someBranch
        (optionMatchDependentSomeBranchType motive elementType) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile (context.cons (optionTypeCell elementType)) motive
          (universeCodeCell resultLevel resultFlag)) := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `optionMatch` row (params `[A, _B]`; obligation
  -- order `[scrutinee, noneBranch, someBranch, motive]`; `outputType = subst0 motive scrutinee`).
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := optionMatchElimRule)
      (show elimRuleOf Generator.gen_optionMatch = some optionMatchElimRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argNone (.childCons _argSome (.childCons _argScrut .childNil))),
    .childCons typeParamA (.childCons _typeParamB .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeParamA, obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      outputConv,
      level0, flag,
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

/-- **★ The optionMatch some-branch is fibrantly usable (A1-CONJUNCT-WIRE surfacing).**  Reads the
`usabilityHolds` conjunct the eliminator-head inversion now surfaces, at the some-branch obligation
(index 2, modality fibrant): the redex's own typing certifies the handler usable, so the select-then-apply
ι reduct can feed `unionAppCellTyped` the handler's use-site usability with NO extra hypothesis. -/
theorem HasTypeUnion.optionMatchSomeBranchUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionMatchCell motive noneBranch someBranch scrutinee) :
    context.isSubjectUsableAtModality someBranch .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := optionMatchElimRule)
      (show elimRuleOf Generator.gen_optionMatch = some optionMatchElimRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argMotive (.childCons _argNone (.childCons _argSome (.childCons _argScrut .childNil))),
    .childCons _typeParamA (.childCons _typeParamB .childNil),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-! ## (1) Inversion at the eitherMatch head -/

/-- **★ Inversion at the eitherMatch head.**  A union typing of an `eitherMatchCell`-headed subject is
EXACTLY a two-branch-match typing at the `gen_eitherMatch` row: for some left/right types `A`, `B`, the
scrutinee is union-typed at `either(A, B)`, the left branch is union-typed at the handler `A → C`, and
the right branch is union-typed at `B → C`.  No grown disjunct (`eitherMatchCell` is a recursive
eliminator, untypable in the grown engine). -/
theorem HasTypeUnion.invertAtEitherMatchHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherMatchCell motive leftBranch rightBranch scrutinee) :
    ∃ (leftType rightType : RawTerm scope),
      HasTypeUnion profile context scrutinee (eitherTypeCell leftType rightType) ∧
      HasTypeUnion profile context leftBranch
        (eitherMatchDependentInlBranchType motive leftType) ∧
      HasTypeUnion profile context rightBranch
        (eitherMatchDependentInrBranchType motive rightType) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile (context.cons (eitherTypeCell leftType rightType)) motive
          (universeCodeCell resultLevel resultFlag)) := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `eitherMatch` row (params `[A, B]`; obligation
  -- order `[scrutinee, leftBranch, rightBranch, motive]`; `outputType = subst0 motive scrutinee`).
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := eitherMatchElimRule)
      (show elimRuleOf Generator.gen_eitherMatch = some eitherMatchElimRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argLeft (.childCons _argRight (.childCons _argScrut .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeParamA, typeParamB, obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      outputConv,
      level0, flag,
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

/-- **★ The eitherMatch left/right branches are fibrantly usable (A1-CONJUNCT-WIRE surfacing).**  Reads the
surfaced `usabilityHolds` conjunct at the left-branch (index 1) and right-branch (index 2) obligations, both
fibrant: the redex's typing certifies both handlers usable, so the inl/inr select-then-apply ι reducts feed
`unionAppCellTyped` the handler usability with no extra hypothesis. -/
theorem HasTypeUnion.eitherMatchBranchesUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherMatchCell motive leftBranch rightBranch scrutinee) :
    context.isSubjectUsableAtModality leftBranch .fibrant = true ∧
    context.isSubjectUsableAtModality rightBranch .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := eitherMatchElimRule)
      (show elimRuleOf Generator.gen_eitherMatch = some eitherMatchElimRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argMotive (.childCons _argLeft (.childCons _argRight (.childCons _argScrut .childNil))),
    .childCons _typeParamA (.childCons _typeParamB .childNil),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨usableHold _ (List.Mem.tail _ (List.Mem.head _)),
      usableHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- **★ The `optionSome` payload is fibrantly usable (A1-CONJUNCT-WIRE surfacing).**  Reads the introducer-head
`usabilityHolds` at the value obligation (index 0): the redex's typing certifies the constructor payload usable,
so the some-ι reduct feeds `unionAppCellTyped` the argument usability with no extra hypothesis. -/
theorem HasTypeUnion.optionSomeValueUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionSomeCell payloadValue) :
    context.isSubjectUsableAtModality payloadValue .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, usableHold⟩ :=
    derivation.invertAtIntroHeadGenericUsable (rule := optionSomeIntroRule)
      (show introRuleOf Generator.gen_optionSome = some optionSomeIntroRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argValue .childNil, .childCons _typeParam0 .childNil, subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.head _)

/-- **★ The `eitherInl` payload is fibrantly usable (A1-CONJUNCT-WIRE surfacing).** -/
theorem HasTypeUnion.eitherInlValueUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherInlCell payloadValue) :
    context.isSubjectUsableAtModality payloadValue .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, usableHold⟩ :=
    derivation.invertAtIntroHeadGenericUsable (rule := eitherInlIntroRule)
      (show introRuleOf Generator.gen_eitherInl = some eitherInlIntroRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argValue .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.head _)

/-- **★ The `eitherInr` payload is fibrantly usable (A1-CONJUNCT-WIRE surfacing).** -/
theorem HasTypeUnion.eitherInrValueUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherInrCell payloadValue) :
    context.isSubjectUsableAtModality payloadValue .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, usableHold⟩ :=
    derivation.invertAtIntroHeadGenericUsable (rule := eitherInrIntroRule)
      (show introRuleOf Generator.gen_eitherInr = some eitherInrIntroRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argValue .childNil, .childCons _typeParam0 (.childCons _typeParam1 .childNil),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.head _)

end FX1Poly.Typed
