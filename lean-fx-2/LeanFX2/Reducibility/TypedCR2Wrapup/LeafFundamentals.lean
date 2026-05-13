import LeanFX2.Reducibility.TypedCR2Compound

/-! # LeanFX2.Reducibility.TypedCR2Wrapup.LeafFundamentals

The `Reducible.step_preserves` headline + the leaf fundamental
cases (`natSucc`, `listNil`/`listCons`, `optionNone`/`optionSome`,
`eitherInl`/`eitherInr`) and their `_stable` companions.

## Root status

Layer 3 metatheory leaf.  First slice of the K12.20.U wrap-up. -/

namespace LeanFX2




/-! ## K12.20.U typed CR2 wrap-up — unified `Reducible.step_preserves`

Combined headline lemma bundling all 25 per-arm CR2 helpers
(K12.20.{C-T}) into a single structurally-recursive theorem on
Ty.  Each Ty constructor's arm dispatches to the matching per-
arm helper; the eight **strong-compound** arms (arrow / sigmaTy
/ path / glue / equiv / refine / record / codata) receive their
`subTyCR2` hypothesis as a recursive `Reducible.step_preserves`
call at the strict sub-Ty position.  This is the canonical CR2
lemma downstream fundamental-theorem cases (K12.21-K12.26) will
consume — no manual per-arm dispatch needed at each call site.

**Termination**: structural recursion on `ty : Ty level scope`.
Recursive calls land on strict sub-Ty positions ONLY, all at
the SAME scope as the parent ctor:

* `Ty.arrow _ codomain`: recurses on `codomain`
* `Ty.sigmaTy first _`: recurses on `first` (secondType lives
  at scope+1 — sigmaTy's CR2 closure only needs firstType)
* `Ty.path carrier _ _`: recurses on `carrier` (left/right are
  RawTerm endpoints, not Ty)
* `Ty.glue base _`: recurses on `base` (boundary is RawTerm)
* `Ty.equiv _ carrierB`: recurses on `carrierB`
* `Ty.refine base _`: recurses on `base` (predicate is RawTerm)
* `Ty.record single`: recurses on `single`
* `Ty.codata _ output`: recurses on `output` (stateType is
  packed into unfold/initial-state, not exposed)

Every recursive call lands at the SAME (level, scope) as the
parent ctor — this sidesteps the **sibling-Ty wall** and the
**substituted-codomain wall** (per
`feedback_lean_reducible_sibling_ty_block.md`).  The 7 weak-
compound arms (piTy / id / idStrict / oeq / listType /
optionType / eitherType) and the 10 SN-direct arms (unit /
bool / nat / empty / interval / universe / tyVar / session /
effect / modal) make NO recursive call — they just dispatch.

**Compound-arm CR2 sweep COMPLETE** with this wrap-up: 15
strong/weak compound + 10 SN-direct = all 25 Ty constructors
covered.  Next: K12.20.V — `ReducibleSubst.singleton` / `lift`
infrastructure for the Term.lam fundamental-theorem case
proper, plus K12.21-K12.26 fundamental theorem cases. -/
theorem Reducible.step_preserves
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    ∀ (ty : Ty level scope)
      {sourceRaw targetRaw : RawTerm scope}
      {source : Term context ty sourceRaw}
      {target : Term context ty targetRaw},
      Reducible ty source →
      RawStep.parProgress sourceRaw targetRaw →
      Reducible ty target
  -- SN-direct arms (10): plain SN preservation.
  | Ty.unit, _, _, _, _ => Reducible.step_preserves_unit
  | Ty.bool, _, _, _, _ => Reducible.step_preserves_bool
  | Ty.nat,  _, _, _, _ => Reducible.step_preserves_nat
  | Ty.empty, _, _, _, _ => Reducible.step_preserves_empty
  | Ty.interval, _, _, _, _ => Reducible.step_preserves_interval
  | Ty.universe _ _, _, _, _, _ => Reducible.step_preserves_universe
  | Ty.tyVar _, _, _, _, _ => Reducible.step_preserves_tyVar
  | Ty.session _, _, _, _, _ => Reducible.step_preserves_session
  | Ty.effect _ _, _, _, _, _ => Reducible.step_preserves_effect
  | Ty.modal _ _, _, _, _, _ => Reducible.step_preserves_modal
  -- Weak-compound arms (7): SN-only closure, no subTyCR2 hypothesis.
  | Ty.piTy _ _, _, _, _, _ => Reducible.step_preserves_piTy
  | Ty.id _ _ _, _, _, _, _ => Reducible.step_preserves_id
  | Ty.idStrict _ _ _, _, _, _, _ => Reducible.step_preserves_idStrict
  | Ty.oeq _ _ _, _, _, _, _ => Reducible.step_preserves_oeq
  | Ty.listType _, _, _, _, _ => Reducible.step_preserves_listType
  | Ty.optionType _, _, _, _, _ => Reducible.step_preserves_optionType
  | Ty.eitherType _ _, _, _, _, _ => Reducible.step_preserves_eitherType
  -- Strong-compound arms (8): subTyCR2 dispatched via recursive
  -- `Reducible.step_preserves` at the strict sub-Ty position.
  | Ty.arrow _ codomain, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_arrow reducible rawStep
          (Reducible.step_preserves codomain)
  | Ty.sigmaTy first _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_sigmaTy
          (Reducible.step_preserves first) reducible rawStep
  | Ty.path carrier _ _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_path
          (Reducible.step_preserves carrier) reducible rawStep
  | Ty.glue base _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_glue
          (Reducible.step_preserves base) reducible rawStep
  | Ty.equiv _ carrierB, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_equiv
          (Reducible.step_preserves carrierB) reducible rawStep
  | Ty.refine base _, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_refine
          (Reducible.step_preserves base) reducible rawStep
  | Ty.record single, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_record
          (Reducible.step_preserves single) reducible rawStep
  | Ty.codata _ output, _, _, _, _ =>
      fun reducible rawStep =>
        Reducible.step_preserves_codata
          (Reducible.step_preserves output) reducible rawStep

/-- **K12.20.V natSucc case** — first unary recursive introducer.
Reducible at Ty.nat unfolds to SN; subst commutes with natSucc
definitionally; raw lift via `RawTerm.natSucc_isStronglyNormalizing`. -/
theorem Reducible.fundamental_natSucc
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {predRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predRaw}
    (predIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                        (Term.subst termSubst predecessor)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.natSucc predecessor)) :=
  RawTerm.natSucc_isStronglyNormalizing predIH

/-- Natural successor preserves fundamental stability when the
predecessor is stable. -/
theorem Reducible.fundamental_natSucc_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {predRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predRaw}
    (predecessorIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.natSucc predecessor)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.natSucc_isStronglyNormalizing
    (predecessorIsStable rhoIsInjective termRenaming)

/-- **K12.20.V.0 listNil fundamental case** — canonical list
nil introduction at the K12.8 SN-output candidate. -/
theorem Reducible.fundamental_listNil_at_listType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope} :
    Reducible ((Ty.listType elementType).subst sigma)
      (Term.subst termSubst
        (Term.listNil (elementType := elementType))) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.listNil_isStronglyNormalizing
  · intro motiveType nilRaw consRaw nilBranch consBranch
      nilIsSN consIsSN _consApplicationIsSN
    exact Term.listElim_listNil_isStronglyNormalizing
      nilIsSN
      consIsSN

/-- List nil introduction is stable under future-world renamings. -/
theorem Reducible.fundamental_listNil_at_listType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope} :
    IsRenamingStableReducible ((Ty.listType elementType).subst sigma)
      (Term.subst termSubst
        (Term.listNil (elementType := elementType))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.listNil_isStronglyNormalizing
  · intro motiveType nilRaw consRaw nilBranch consBranch
      nilIsSN consIsSN _consApplicationIsSN
    exact Term.listElim_listNil_isStronglyNormalizing
      nilIsSN
      consIsSN

/-- **K12.20.V.1 listCons fundamental case** — canonical list
cons introduction at the K12.8 SN-output candidate. -/
theorem Reducible.fundamental_listCons_at_listType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIH :
      Reducible (elementType.subst sigma)
        (Term.subst termSubst headTerm))
    (tailIH :
      Reducible ((Ty.listType elementType).subst sigma)
        (Term.subst termSubst tailTerm)) :
    Reducible ((Ty.listType elementType).subst sigma)
      (Term.subst termSubst
        (Term.listCons headTerm tailTerm)) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.listCons_isStronglyNormalizing
      (Reducible.isStronglyNormalizing headIH)
      (Reducible.isStronglyNormalizing tailIH)
  · intro motiveType nilRaw consRaw nilBranch consBranch
      nilIsSN consIsSN consApplicationIsSN
    exact Term.listElim_listCons_isStronglyNormalizing
      (Reducible.isStronglyNormalizing headIH)
      (Reducible.isStronglyNormalizing tailIH)
      nilIsSN
      consIsSN
      (consApplicationIsSN
        (Term.subst termSubst headTerm)
        (Term.subst termSubst tailTerm)
        headIH
        (Reducible.isStronglyNormalizing tailIH))

/-- List cons introduction preserves fundamental stability. -/
theorem Reducible.fundamental_listCons_at_listType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsStable :
      IsRenamingStableReducible (elementType.subst sigma)
        (Term.subst termSubst headTerm))
    (tailIsStable :
      IsRenamingStableReducible ((Ty.listType elementType).subst sigma)
        (Term.subst termSubst tailTerm)) :
    IsRenamingStableReducible ((Ty.listType elementType).subst sigma)
      (Term.subst termSubst
        (Term.listCons headTerm tailTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  let renamedHead := Term.rename termRenaming (Term.subst termSubst headTerm)
  let renamedTail := Term.rename termRenaming (Term.subst termSubst tailTerm)
  let renamedHeadReducible := headIsStable rhoIsInjective termRenaming
  let renamedTailReducible := tailIsStable rhoIsInjective termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.listCons_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedHeadReducible)
      (Reducible.isStronglyNormalizing renamedTailReducible)
  · intro motiveType nilRaw consRaw nilBranch consBranch
      nilIsSN consIsSN consApplicationIsSN
    exact Term.listElim_listCons_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedHeadReducible)
      (Reducible.isStronglyNormalizing renamedTailReducible)
      nilIsSN
      consIsSN
      (consApplicationIsSN
        renamedHead
        renamedTail
        renamedHeadReducible
        (Reducible.isStronglyNormalizing renamedTailReducible))

/-- **K12.20.W.0 optionNone fundamental case** — canonical option
none introduction at the K12.8 SN-output candidate. -/
theorem Reducible.fundamental_optionNone_at_optionType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope} :
    Reducible ((Ty.optionType elementType).subst sigma)
      (Term.subst termSubst
        (Term.optionNone (elementType := elementType))) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.optionNone_isStronglyNormalizing
  · intro motiveType noneRaw someRaw noneBranch someBranch
      noneIsSN someIsSN _someApplicationIsSN
    exact Term.optionMatch_optionNone_isStronglyNormalizing
      noneIsSN
      someIsSN

/-- Option none introduction is stable under future-world renamings. -/
theorem Reducible.fundamental_optionNone_at_optionType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope} :
    IsRenamingStableReducible ((Ty.optionType elementType).subst sigma)
      (Term.subst termSubst
        (Term.optionNone (elementType := elementType))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.optionNone_isStronglyNormalizing
  · intro motiveType noneRaw someRaw noneBranch someBranch
      noneIsSN someIsSN _someApplicationIsSN
    exact Term.optionMatch_optionNone_isStronglyNormalizing
      noneIsSN
      someIsSN

/-- **K12.20.W optionSome fundamental case** — canonical option
introduction at the K12.8 SN-output candidate.

The option candidate stores exactly the eliminator result needed for
M04: when a `Some` value is scrutinized, the supplied some-branch
application is strongly normalizing for every reducible payload. -/
theorem Reducible.fundamental_optionSome_at_optionType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIH :
      Reducible (elementType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    Reducible ((Ty.optionType elementType).subst sigma)
      (Term.subst termSubst (Term.optionSome valueTerm)) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.optionSome_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
  · intro motiveType noneRaw someRaw noneBranch someBranch
      noneIsSN someIsSN someApplicationIsSN
    exact Term.optionMatch_optionSome_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
      noneIsSN
      someIsSN
      (someApplicationIsSN
        (Term.subst termSubst valueTerm)
        valueIH)

/-- Option some introduction preserves fundamental stability. -/
theorem Reducible.fundamental_optionSome_at_optionType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsStable :
      IsRenamingStableReducible (elementType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    IsRenamingStableReducible ((Ty.optionType elementType).subst sigma)
      (Term.subst termSubst (Term.optionSome valueTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  let renamedValue := Term.rename termRenaming (Term.subst termSubst valueTerm)
  let renamedValueReducible := valueIsStable rhoIsInjective termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.optionSome_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
  · intro motiveType noneRaw someRaw noneBranch someBranch
      noneIsSN someIsSN someApplicationIsSN
    exact Term.optionMatch_optionSome_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
      noneIsSN
      someIsSN
      (someApplicationIsSN
        renamedValue
        renamedValueReducible)

/-- **K12.20.X.1 eitherInl fundamental case** — canonical left
injection at the K12.8 either SN-output candidate. -/
theorem Reducible.fundamental_eitherInl_at_eitherType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIH :
      Reducible (leftType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    Reducible ((Ty.eitherType leftType rightType).subst sigma)
      (Term.subst termSubst
        (Term.eitherInl (rightType := rightType) valueTerm)) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.eitherInl_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftIsSN rightIsSN leftApplicationIsSN _rightApplicationIsSN
    exact Term.eitherMatch_eitherInl_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
      leftIsSN
      rightIsSN
      (leftApplicationIsSN
        (Term.subst termSubst valueTerm)
        valueIH)

/-- Either left injection preserves fundamental stability. -/
theorem Reducible.fundamental_eitherInl_at_eitherType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsStable :
      IsRenamingStableReducible (leftType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    IsRenamingStableReducible ((Ty.eitherType leftType rightType).subst sigma)
      (Term.subst termSubst
        (Term.eitherInl (rightType := rightType) valueTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  let renamedValue := Term.rename termRenaming (Term.subst termSubst valueTerm)
  let renamedValueReducible := valueIsStable rhoIsInjective termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.eitherInl_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftIsSN rightIsSN leftApplicationIsSN _rightApplicationIsSN
    exact Term.eitherMatch_eitherInl_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
      leftIsSN
      rightIsSN
      (leftApplicationIsSN
        renamedValue
        renamedValueReducible)

/-- **K12.20.X.2 eitherInr fundamental case** — canonical right
injection at the K12.8 either SN-output candidate. -/
theorem Reducible.fundamental_eitherInr_at_eitherType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIH :
      Reducible (rightType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    Reducible ((Ty.eitherType leftType rightType).subst sigma)
      (Term.subst termSubst
        (Term.eitherInr (leftType := leftType) valueTerm)) := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.eitherInr_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftIsSN rightIsSN _leftApplicationIsSN rightApplicationIsSN
    exact Term.eitherMatch_eitherInr_isStronglyNormalizing
      (Reducible.isStronglyNormalizing valueIH)
      leftIsSN
      rightIsSN
      (rightApplicationIsSN
        (Term.subst termSubst valueTerm)
        valueIH)

/-- Either right injection preserves fundamental stability. -/
theorem Reducible.fundamental_eitherInr_at_eitherType_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsStable :
      IsRenamingStableReducible (rightType.subst sigma)
        (Term.subst termSubst valueTerm)) :
    IsRenamingStableReducible ((Ty.eitherType leftType rightType).subst sigma)
      (Term.subst termSubst
        (Term.eitherInr (leftType := leftType) valueTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  let renamedValue := Term.rename termRenaming (Term.subst termSubst valueTerm)
  let renamedValueReducible := valueIsStable rhoIsInjective termRenaming
  refine ⟨?_, ?_⟩
  · exact RawTerm.eitherInr_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftIsSN rightIsSN _leftApplicationIsSN rightApplicationIsSN
    exact Term.eitherMatch_eitherInr_isStronglyNormalizing
      (Reducible.isStronglyNormalizing renamedValueReducible)
      leftIsSN
      rightIsSN
      (rightApplicationIsSN
        renamedValue
        renamedValueReducible)


end LeanFX2
