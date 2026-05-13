import LeanFX2.Reducibility.TypedCR2Compound

/-! # LeanFX2.Reducibility.TypedCR2Wrapup — K12.20.U `Reducible.step_preserves`

The unified typed CR2 cascade wrap-up.  Combines the per-arm
forward-step closures from `TypedCR2Direct` (SN-direct) and
`TypedCR2Compound` (specialized closures) into one headline
theorem.

## What ships

* `Reducible.step_preserves` — for every typed `Step` from a
  Reducible term, the target is Reducible at the same Ty.
  Dispatch over all 25 Ty arms via the per-arm CR2 lemmas.
* Supporting lemmas for `Reducible.cr2` (typed) — the K12.20.U1
  headline tied to `Reducible.step_preserves`.
* Cross-arm interaction lemmas (the wrap-up may include lemmas
  that combine multiple arm closures, e.g. for Ty.arrow's domain
  preservation via codomain Reducible.cr2).

## Root status

Layer 3 metatheory leaf.  K12.20.U typed CR2 cascade headline.
Consumed by the typed Fundamental modules and the K12.27 M04
strong-normalization corollary. -/

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

/-- **K12.20.AO.1 intervalOpp fundamental case** — cubical interval
negation.  Unary intro to the closed-leaf `Ty.interval`; identical
single-line pattern as `fundamental_natSucc`. -/
theorem Reducible.fundamental_intervalOpp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.intervalOpp innerValue)) :=
  RawTerm.intervalOpp_isStronglyNormalizing innerIH

/-- Interval negation preserves fundamental stability. -/
theorem Reducible.fundamental_intervalOpp_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.intervalOpp innerValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalOpp_isStronglyNormalizing
    (innerIsStable rhoIsInjective termRenaming)

/-- **K12.20.AO.2 intervalMeet fundamental case** — cubical interval
meet (∧).  Binary intro to `Ty.interval`; both subterms substitute
componentwise and the binary SN helper closes both arguments. -/
theorem Reducible.fundamental_intervalMeet
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalMeet leftValue rightValue)) :=
  RawTerm.intervalMeet_isStronglyNormalizing leftIH rightIH

/-- Interval meet preserves fundamental stability. -/
theorem Reducible.fundamental_intervalMeet_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst leftValue))
    (rightIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst rightValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.intervalMeet leftValue rightValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalMeet_isStronglyNormalizing
    (leftIsStable rhoIsInjective termRenaming)
    (rightIsStable rhoIsInjective termRenaming)

/-- **K12.20.AO.3 intervalJoin fundamental case** — cubical interval
join (∨).  Sister to intervalMeet; same binary shape. -/
theorem Reducible.fundamental_intervalJoin
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                        (Term.subst termSubst leftValue))
    (rightIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst rightValue)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.intervalJoin leftValue rightValue)) :=
  RawTerm.intervalJoin_isStronglyNormalizing leftIH rightIH

/-- Interval join preserves fundamental stability. -/
theorem Reducible.fundamental_intervalJoin_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst leftValue))
    (rightIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst rightValue)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.intervalJoin leftValue rightValue)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.intervalJoin_isStronglyNormalizing
    (leftIsStable rhoIsInjective termRenaming)
    (rightIsStable rhoIsInjective termRenaming)

/-- **K12.20.AP.1 sessionRecv fundamental case** — session-type
receive operation.  Result type `Ty.session protocolStep` is
SN-direct (`Reducibility.lean:667`); `Term.subst` distributes
componentwise over `sessionRecv`
(`LeanFX2/Term/Subst.lean:363-364`); the unary K12.20.AL.1 SN
helper closes the proof in one line. -/
theorem Reducible.fundamental_sessionRecv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst (Term.sessionRecv channel)) :=
  RawTerm.sessionRecv_isStronglyNormalizing channelIH

/-- Session receive preserves fundamental stability. -/
theorem Reducible.fundamental_sessionRecv_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst channel)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst (Term.sessionRecv channel)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.sessionRecv_isStronglyNormalizing
    (channelIsStable rhoIsInjective termRenaming)

/-- **K12.20.AP.2 sessionSend fundamental case** — session-type
send operation bundles a channel with an arbitrary-typed payload.
Channel lives at `Ty.session protocolStep` (SN-direct) so `channelIH`
IS SN; payload lives at arbitrary `payloadType`, so its SN witness
is extracted via the K12.18 closure-elimination lemma
`Reducible.isStronglyNormalizing` (lines 639-669) before feeding
the K12.20.AL.2 binary helper. -/
theorem Reducible.fundamental_sessionSend
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIH : Reducible ((Ty.session protocolStep).subst sigma)
                           (Term.subst termSubst channel))
    (payloadIH : Reducible (payloadType.subst sigma)
                           (Term.subst termSubst payload)) :
    Reducible ((Ty.session protocolStep).subst sigma)
              (Term.subst termSubst
                (Term.sessionSend protocolStep channel payload)) :=
  RawTerm.sessionSend_isStronglyNormalizing channelIH
    (Reducible.isStronglyNormalizing payloadIH)

/-- Session send preserves fundamental stability. -/
theorem Reducible.fundamental_sessionSend_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {protocolStep : RawTerm scope}
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIsStable :
      IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
        (Term.subst termSubst channel))
    (payloadIsStable :
      IsRenamingStableReducible (payloadType.subst sigma)
        (Term.subst termSubst payload)) :
    IsRenamingStableReducible ((Ty.session protocolStep).subst sigma)
      (Term.subst termSubst
        (Term.sessionSend protocolStep channel payload)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.sessionSend_isStronglyNormalizing
    (channelIsStable rhoIsInjective termRenaming)
    (Reducible.isStronglyNormalizing
      (payloadIsStable rhoIsInjective termRenaming))

/-- **K12.20.AQ effectPerform fundamental case** — algebraic effect
operation invocation bundles an operation tag with arguments.
Both subterms have arbitrary-Ty payloads — operationTag at
`Ty.effect operationSignature.argumentCarrier effectTag` (SN-direct
per Reducibility.lean:668 so operationIH IS SN); arguments at
the arbitrary `operationSignature.argumentCarrier` (needs SN
extraction via `Reducible.isStronglyNormalizing` per K12.20.AP.2).
Result type `Ty.effect resultCarrier effectTag` after subst is
also SN-direct.  The K12.20.AL.3 binary SN helper closes the
proof in one line. -/
theorem Reducible.fundamental_effectPerform
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIH :
      Reducible
        ((Ty.effect operationSignature.argumentCarrier effectTag).subst sigma)
        (Term.subst termSubst operationTag))
    (argumentsIH :
      Reducible (operationSignature.argumentCarrier.subst sigma)
                (Term.subst termSubst arguments)) :
    Reducible
      ((Ty.effect operationSignature.resultCarrier effectTag).subst sigma)
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)) :=
  RawTerm.effectPerform_isStronglyNormalizing operationIH
    (Reducible.isStronglyNormalizing argumentsIH)

/-- Effect performance preserves fundamental stability. -/
theorem Reducible.fundamental_effectPerform_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIsStable :
      IsRenamingStableReducible
        ((Ty.effect operationSignature.argumentCarrier effectTag).subst sigma)
        (Term.subst termSubst operationTag))
    (argumentsAreStable :
      IsRenamingStableReducible
        (operationSignature.argumentCarrier.subst sigma)
        (Term.subst termSubst arguments)) :
    IsRenamingStableReducible
      ((Ty.effect operationSignature.resultCarrier effectTag).subst sigma)
      (Term.subst termSubst
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.effectPerform_isStronglyNormalizing
    (operationIsStable rhoIsInjective termRenaming)
    (Reducible.isStronglyNormalizing
      (argumentsAreStable rhoIsInjective termRenaming))

/-- **K12.20.AR.3 universeCode fundamental case** — universe-code
nullary intro at outer level.  Output `Ty.universe outerLevel
levelLe` is SN-direct (Reducibility.lean:330); `Term.subst` on
universeCode is identity (`LeanFX2/Term/Subst.lean:379-380`);
`Reducible Ty.universe _` unfolds to `Term.isStronglyNormalizing
_`.  Direct lift via the K12.20.AR.2 SN helper. -/
theorem Reducible.fundamental_universeCode
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.universeCode (context := sourceCtx)
                  innerLevel outerLevel cumulOk levelLe)) :=
  RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Universe-code introduction is stable under future-world renamings. -/
theorem Reducible.fundamental_universeCode_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
      (Term.subst termSubst
        (Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe)) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Type-code arrow fundamental endpoint with explicit payload SN
premises.

`Term.arrowCode` stores schematic raw payloads rather than typed child
terms.  Since the raw reduction relation has congruence under
`RawTerm.arrowCode`, those payloads must be known strongly normalizing
after substitution.  This theorem names that obligation for the
identity-only M04 chain instead of hiding it behind an impossible
unconditional constructor case. -/
theorem Reducible.fundamental_arrowCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (domainCodeRaw.subst sigma.forRaw))
    (codomainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (codomainCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.arrowCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  RawTerm.arrowCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Type-code dependent-Pi fundamental endpoint with explicit payload
SN premises.

The codomain raw payload is scoped under the binder, so its substituted
SN premise is over `sigma.forRaw.lift`.  This is the binder-shaped
counterpart to `fundamental_arrowCode_of_payloads`. -/
theorem Reducible.fundamental_piTyCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (domainCodeRaw.subst sigma.forRaw))
    (codomainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (codomainCodeRaw.subst sigma.forRaw.lift)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.piTyCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  RawTerm.piTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Type-code dependent-Sigma fundamental endpoint with explicit
payload SN premises.

The second raw payload is scoped under the binder, so the premise uses
`sigma.forRaw.lift`, matching `Term.subst` for `sigmaTyCode`. -/
theorem Reducible.fundamental_sigmaTyCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw : RawTerm scope}
    {secondCodeRaw : RawTerm (scope + 1)}
    (firstCodeIsSN :
      RawTerm.isStronglyNormalizing
        (firstCodeRaw.subst sigma.forRaw))
    (secondCodeIsSN :
      RawTerm.isStronglyNormalizing
        (secondCodeRaw.subst sigma.forRaw.lift)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.sigmaTyCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  RawTerm.sigmaTyCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Type-code product fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_productCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN :
      RawTerm.isStronglyNormalizing
        (firstCodeRaw.subst sigma.forRaw))
    (secondCodeIsSN :
      RawTerm.isStronglyNormalizing
        (secondCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.productCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  RawTerm.productCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Type-code sum fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_sumCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.sumCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  RawTerm.sumCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Type-code either fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_eitherCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.eitherCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  RawTerm.eitherCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Type-code equivalence fundamental endpoint with explicit
same-scope payload SN premises. -/
theorem Reducible.fundamental_equivCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftTypeCodeRaw.subst sigma.forRaw))
    (rightTypeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightTypeCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.equivCode (context := sourceCtx)
                  outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw)) :=
  RawTerm.equivCode_isStronglyNormalizing
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- Type-code list fundamental endpoint with an explicit element-code
SN premise. -/
theorem Reducible.fundamental_listCode_of_payload
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN :
      RawTerm.isStronglyNormalizing
        (elementCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.listCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  RawTerm.listCode_isStronglyNormalizing elementCodeIsSN

/-- Type-code option fundamental endpoint with an explicit
element-code SN premise. -/
theorem Reducible.fundamental_optionCode_of_payload
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN :
      RawTerm.isStronglyNormalizing
        (elementCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.optionCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  RawTerm.optionCode_isStronglyNormalizing elementCodeIsSN

/-- Type-code identity fundamental endpoint with explicit carrier and
endpoint-code SN premises. -/
theorem Reducible.fundamental_idCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (typeCodeRaw.subst sigma.forRaw))
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.idCode (context := sourceCtx)
                  outerLevel levelLe
                  typeCodeRaw leftCodeRaw rightCodeRaw)) :=
  RawTerm.idCode_isStronglyNormalizing
    typeCodeIsSN leftCodeIsSN rightCodeIsSN

/-- Identity-substitution arrow-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_arrowCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.arrowCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  Reducible.fundamental_arrowCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      domainCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      codomainCodeIsTypeCode)

/-- Identity-substitution Pi-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_piTyCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.piTyCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  Reducible.fundamental_piTyCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      domainCodeIsTypeCode)
    (RawTerm.subst_identity_lift_isStronglyNormalizing
      (RawTerm.isStronglyNormalizing_of_typeCode codomainCodeIsTypeCode))

/-- Identity-substitution Sigma-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_sigmaTyCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw : RawTerm scope}
    {secondCodeRaw : RawTerm (scope + 1)}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.sigmaTyCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  Reducible.fundamental_sigmaTyCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      firstCodeIsTypeCode)
    (RawTerm.subst_identity_lift_isStronglyNormalizing
      (RawTerm.isStronglyNormalizing_of_typeCode secondCodeIsTypeCode))

/-- Identity-substitution product-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_productCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.productCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  Reducible.fundamental_productCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      firstCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      secondCodeIsTypeCode)

/-- Identity-substitution sum-code endpoint from named type-code payload
evidence. -/
theorem Reducible.fundamental_identity_sumCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.sumCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_sumCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightCodeIsTypeCode)

/-- Identity-substitution either-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_eitherCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.eitherCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_eitherCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightCodeIsTypeCode)

/-- Identity-substitution equivalence-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_equivCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCodeRaw)
    (rightTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.equivCode (context := sourceCtx)
                  outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw)) :=
  Reducible.fundamental_equivCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftTypeCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightTypeCodeIsTypeCode)

/-- Identity-substitution list-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_listCode_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.listCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  Reducible.fundamental_listCode_of_payload
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      elementCodeIsTypeCode)

/-- Identity-substitution option-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_optionCode_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.optionCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  Reducible.fundamental_optionCode_of_payload
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      elementCodeIsTypeCode)

/-- Identity-substitution identity-code endpoint from named carrier-code
and endpoint SN evidence. -/
theorem Reducible.fundamental_identity_idCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode typeCodeRaw)
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.idCode (context := sourceCtx)
                  outerLevel levelLe
                  typeCodeRaw leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_idCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      typeCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing leftCodeIsSN)
    (RawTerm.subst_identity_isStronglyNormalizing rightCodeIsSN)

/-- Direct identity-M04 SN case for universe code. -/
theorem Term.identity_universeCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.universeCode (context := sourceCtx)
      innerLevel outerLevel cumulOk levelLe)
    (Reducible.fundamental_universeCode
      (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
      (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
      innerLevel outerLevel cumulOk levelLe)

/-- Direct identity-M04 SN case for arrow type code. -/
theorem Term.identity_arrowCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.arrowCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw)
    (Reducible.fundamental_identity_arrowCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      domainCodeIsTypeCode codomainCodeIsTypeCode)

/-- Direct identity-M04 SN case for Pi type code. -/
theorem Term.identity_piTyCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.piTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw)
    (Reducible.fundamental_identity_piTyCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      domainCodeIsTypeCode codomainCodeIsTypeCode)

/-- Direct identity-M04 SN case for Sigma type code. -/
theorem Term.identity_sigmaTyCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw : RawTerm scope}
    {secondCodeRaw : RawTerm (scope + 1)}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.sigmaTyCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw)
    (Reducible.fundamental_identity_sigmaTyCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      firstCodeIsTypeCode secondCodeIsTypeCode)

/-- Direct identity-M04 SN case for product type code. -/
theorem Term.identity_productCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.productCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw)
    (Reducible.fundamental_identity_productCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      firstCodeIsTypeCode secondCodeIsTypeCode)

/-- Direct identity-M04 SN case for sum type code. -/
theorem Term.identity_sumCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.sumCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_sumCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftCodeIsTypeCode rightCodeIsTypeCode)

/-- Direct identity-M04 SN case for either type code. -/
theorem Term.identity_eitherCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.eitherCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_eitherCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftCodeIsTypeCode rightCodeIsTypeCode)

/-- Direct identity-M04 SN case for equivalence type code. -/
theorem Term.identity_equivCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCodeRaw)
    (rightTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.equivCode (context := sourceCtx)
      outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)
    (Reducible.fundamental_identity_equivCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftTypeCodeIsTypeCode rightTypeCodeIsTypeCode)

/-- Direct identity-M04 SN case for list type code. -/
theorem Term.identity_listCode_isStronglyNormalizing_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.listCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw)
    (Reducible.fundamental_identity_listCode_of_typeCode_payload
      (sourceCtx := sourceCtx) outerLevel levelLe elementCodeIsTypeCode)

/-- Direct identity-M04 SN case for option type code. -/
theorem Term.identity_optionCode_isStronglyNormalizing_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.optionCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw)
    (Reducible.fundamental_identity_optionCode_of_typeCode_payload
      (sourceCtx := sourceCtx) outerLevel levelLe elementCodeIsTypeCode)

/-- Direct identity-M04 SN case for identity type code. -/
theorem Term.identity_idCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode typeCodeRaw)
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.idCode (context := sourceCtx)
      outerLevel levelLe typeCodeRaw leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_idCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      typeCodeIsTypeCode leftCodeIsSN rightCodeIsSN)

/-- **K12.20.BB.1 cumulUpMarker SN preservation** — CUMUL-2.6 cong
helper at the raw layer.  Sister to `subsume_isStronglyNormalizing`
(K12.20.AB) and `modIntro_isStronglyNormalizing` (K12.20.Y) — unary
cong-only ctor; `RawStep.par.cumulUpMarkerCong` is the only non-refl
rule with `cumulUpMarker _` as source.  Powers `fundamental_cumulUp`
at the typed cross-universe cumulativity ctor. -/
theorem RawTerm.cumulUpMarker_isStronglyNormalizing {scope : Nat}
    {innerCodeRaw : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerCodeRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.cumulUpMarker innerCodeRaw) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.cumulUpMarker currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.cumulUpMarker_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.cumulUpMarker innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.20.BB.2 cumulUp fundamental case** — REAL cross-universe
cumulativity at the typed Term level (Phase CUMUL-2.6 Design D).
Source `Ty.universe lowerLevel levelLeLow` is SN-direct; output
`Ty.universe higherLevel levelLeHigh` is also SN-direct (per
`Reducibility.lean:330`).  `Term.subst` on `Term.cumulUp` reconstructs
the cumulUp ctor at the target scope with the recursively-substituted
inner typeCode (per `LeanFX2/Term/Subst.lean:388-393`); the typed
raw form is `RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw)`.
The `innerIH` is SN of the substituted inner; the K12.20.BB.1
cumulUpMarker SN helper closes the proof. -/
theorem Reducible.fundamental_cumulUp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (innerIH :
        Reducible ((Ty.universe lowerLevel levelLeLow).subst sigma)
                  (Term.subst termSubst typeCode)) :
    Reducible ((Ty.universe higherLevel levelLeHigh).subst sigma)
              (Term.subst termSubst
                (Term.cumulUp lowerLevel higherLevel
                              cumulMonotone levelLeLow levelLeHigh
                              typeCode)) :=
  RawTerm.cumulUpMarker_isStronglyNormalizing innerIH

/-- Cumulativity markers preserve fundamental stability. -/
theorem Reducible.fundamental_cumulUp_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (innerIsStable :
        IsRenamingStableReducible
          ((Ty.universe lowerLevel levelLeLow).subst sigma)
          (Term.subst termSubst typeCode)) :
    IsRenamingStableReducible
      ((Ty.universe higherLevel levelLeHigh).subst sigma)
      (Term.subst termSubst
        (Term.cumulUp lowerLevel higherLevel
                      cumulMonotone levelLeLow levelLeHigh
                      typeCode)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.cumulUpMarker_isStronglyNormalizing
    (innerIsStable rhoIsInjective termRenaming)


end LeanFX2
