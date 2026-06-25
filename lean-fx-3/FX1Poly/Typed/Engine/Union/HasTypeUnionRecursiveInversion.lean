import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/HasTypeUnionRecursiveInversion — NATIVE-37 part d: per-head inversions for the
    remaining recursive eliminator heads (natRec and listElim).

The `natElim` head shipped in `HasTypeUnionInversion`; this file adds its `gen_natRec` twin (the
`natRecElimRule` row of `elimRuleOf`) and the `listElim` head (the `listElimRule` row).

  * **natRec** — survivor is the unified `elim` arm pinned to the `gen_natRec` row.  Surfaced premises:
    the scrutinee union-typed at `Nat`, the base (zero) branch union-typed at the classifier.  Identical
    in shape to `invertAtNatElimHead`, only the surviving row differs (`natRecElimRule` vs `natElimRule`,
    same `[1, 0, 2, 0]` arg shifts and obligation list `[scrutinee@Nat, base@result, step@scope+2]`).
  * **listElim** — survivor is the unified `elim` arm pinned to the `gen_listElim` row.  Surfaced premises:
    the scrutinee UNION-typed at `List(elementType)` (the NATIVE-42 re-shape made the scrutinee premise
    union-recursive, retiring the last zoo judgment named inside the union), the nil/cons branches
    UNION-typed at the result / 3-arg curried step type.  THE TYTAB-1 ELIM-COLLAPSE RESHAPE: the nil/cons
    branches were GROWN premises in the pre-collapse `listElim` arm; the unified `elimRuleOf` table makes
    every branch a union obligation (`ElimRuleTable.listElimRule.obligations`), so the surfaced branch
    premises are now `HasTypeUnion`, not `HasTypeDescPi`.  The reverse adequacy for listElim is therefore
    RELATIVIZED like every other head (the scrutinee reconstruction map is where computed-list scrutinees
    fall outside the bespoke engine).

## Zero-axiom

Free-subject `induction` + the shipped `elimRuleOf_cases` row inverter + the `elimMemberCellRootGenerator`
head-projection helper + `rcases subjectShape with ⟨⟩`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the natRec head -/

/-- **★ Inversion at the natRec head.**  A union typing of a `natRecCell`-headed subject is EXACTLY a
recursive-eliminator typing at the `gen_natRec` row of `elimRuleOf`: the scrutinee is union-typed at `Nat`
and the base (zero) branch is union-typed at the classifier.  (The motive and step branch are stored, not
surfaced — premise parity with the natElim twin.)  No grown disjunct: `natRecCell` is untypable in the
grown engine.  The `gen_natRec` twin of `HasTypeUnion.invertAtNatElimHead`. -/
theorem HasTypeUnion.invertAtNatRecHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `natRec` row (no type params, `params = childNil`;
  -- obligation order `[scrutinee, baseBranch, stepBranch, motive]`; `outputType = subst0 motive scrutinee`).
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := natRecElimRule)
      (show elimRuleOf Generator.gen_natRec = some natRecElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argStep (.childCons _argScrut .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      outputConv⟩

/-- **★ Full inversion at the natRec head — all four DEPENDENT `natRecElimRule` premises surfaced.**  The richer
twin of `invertAtNatRecHead`, and the `gen_natRec` mirror of `invertAtNatElimHeadAllPremises`: a union typing of
a `natRecCell`-headed subject surfaces the scrutinee at `Nat`, the base branch at its dependent zero type
`subst0 motive natZeroCell`, the step branch at the two-binder dependent succ type
`natElimDependentSuccBranchType motive` in `(context.cons natTypeCell).cons motive`, the motive's universe
formedness over `context.cons natTypeCell`, and the `Conv` of the dependent output `subst0 motive scrutinee` to
the ambient classifier.  `natRecElimRule` is structurally identical to `natElimRule` (same `[1, 0, 2, 0]` arg
shifts, same dependent obligation list, shared `natElimDependentSuccBranchType`), so the surviving-row body is
the natElim body verbatim with the `gen_natRec` row as survivor.  The exact premise set the unconditional
natRec-succ subject reduction needs.  No grown disjunct (`natRecCellHasNoTyping`). -/
theorem HasTypeUnion.invertAtNatRecHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = natRecCell motive zeroBranch stepBranch scrutinee) :
    ∃ (resultLevel : FX1Poly.Universe.LevelExpr)
      (resultFlag : FX1Poly.Universe.UniverseFlag),
      HasTypeUnion profile context scrutinee natTypeCell ∧
      HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
      HasTypeUnion profile ((context.cons natTypeCell).cons motive)
        stepBranch (natElimDependentSuccBranchType motive) ∧
      HasTypeUnion profile (context.cons natTypeCell) motive
        (universeCodeCell resultLevel resultFlag) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `natRec` row surfacing ALL four obligations;
  -- the motive obligation's universe levels are the row's existential `level0`/`flag` (here OUTERMOST).
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := natRecElimRule)
      (show elimRuleOf Generator.gen_natRec = some natRecElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argStep (.childCons _argScrut .childNil))),
    .childNil, subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨level0, flag,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
      outputConv⟩

/-! ## (1) Inversion at the listElim head -/

/-- **★ Inversion at the listElim head.**  A union typing of a `listElimCell`-headed subject is EXACTLY a
listElim typing at the `gen_listElim` row of `elimRuleOf`: the scrutinee is UNION-typed at `List(elementType)`
(the NATIVE-42 union-recursive premise), the nil branch is UNION-typed at the classifier, the cons branch is
UNION-typed at the 3-arg curried step type.  THE TYTAB-1 RESHAPE: the nil/cons branch premises were GROWN
(`HasTypeDescPi`) before the elim collapse; the unified `listElimRule.obligations` makes every branch a union
obligation, so they surface UNION-typed here.  No grown disjunct: `listElimCell` is untypable in the grown
engine. -/
theorem HasTypeUnion.invertAtListElimHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = listElimCell motive scrutinee nilBranch consBranch) :
    ∃ elementType : RawTerm scope,
      HasTypeUnion profile context scrutinee (listTypeCell elementType) ∧
      HasTypeUnion profile context nilBranch (RawTerm.subst0 motive listNilCell) ∧
      HasTypeUnion profile context consBranch
        (listElimDependentConsBranchType motive elementType) ∧
      Conv (RawTerm.subst0 motive scrutinee) classifier ∧
      (∃ (resultLevel : LevelExpr) (resultFlag : UniverseFlag),
        HasTypeUnion profile (context.cons (listTypeCell elementType)) motive
          (universeCodeCell resultLevel resultFlag)) := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `listElim` row (params `[A, _resultType]`;
  -- cell `listElimCell motive scrutinee nilBranch consBranch`; obligation order
  -- `[scrutinee, nilBranch, consBranch, motive]`; `outputType = subst0 motive scrutinee`).
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := listElimRule)
      (show elimRuleOf Generator.gen_listElim = some listElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argScrut (.childCons _argNil (.childCons _argCons .childNil))),
    .childCons typeParamElement (.childCons _resultType .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeParamElement, obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      outputConv,
      level0, flag,
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

end FX1Poly.Typed
