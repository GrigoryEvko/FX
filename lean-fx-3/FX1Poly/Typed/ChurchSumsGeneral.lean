import FX1Poly.Typed.ChurchSums
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ChurchSumsGeneral — Church-sum case selection for an ARBITRARY symbolic payload

`ChurchSums` (#1019) proved the case selections `case (inl I) l r ↝* l I` and `case (inr I) l r ↝* r I` at the
CONCRETE stored value `I = combinatorI`.  The restriction to a concrete payload was forced by the double-weaken:
`leftInjection payload = λl.λr. l payload` stores its payload UNDER TWO binders (`l`, `r`), so the payload is
weakened TWICE, and applying the handlers needs `subst (lift σ) (weaken² payload) = weaken payload` — which does
not hold by `rfl` for a symbolic `payload` (only for a concrete closed one).  That double-weaken cancellation is
now the shipped lemma `RawTerm.subst_lift_singleton_weaken_weaken` (#1023), so the case selections hold for ANY
stored payload:

  * **`caseLeft_selectsLeftHandler_general` (★)** — `case (inl payload) l r ↝* l payload` for every closed
    `payload`, `l`, `r`: the LEFT injection's `case` applies the LEFT handler to the (now arbitrary) stored value.
  * **`caseRight_selectsRightHandler_general`** — the dual, `case (inr payload) l r ↝* r payload`.
  * **`caseSelectsByTag_general`** — the round-trip bundle for an arbitrary payload.

These SUBSUME `ChurchSums`' concrete theorems (each is this one at `payload = combinatorI`).  The only change from
the concrete proof is the first β-step's contractum reshape (`leftInjection_subst_handlerL` /
`rightInjection_subst_handlerL`): substituting the left handler pushes the lifted singleton through the doubly-
weakened payload, and `subst_lift_singleton_weaken_weaken` (#1023) collapses `weaken² payload` to `weaken payload`
— exactly the step a concrete payload got for free by `rfl`.  The remaining β-step uses the single-weaken
cancellation (`weaken_subst_singleton`) on both the handler and the payload, identically to #1019.

With these, the Church-sum coproduct encoding is faithful for ARBITRARY stored data, not just a fixed witness —
completing the symbolic story the de Bruijn substrate (single-weaken #1009 / double-weaken #1023) was built for.

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

The two β1 reshapes are the `show`-push (re-express the contractum with `subst` distributed through
`appCell`/`lamCell` — definitional — exposing the doubly-weakened payload) + `rw
[subst_lift_singleton_weaken_weaken]` + `rfl` idiom.  The case selections then mirror #1019: a function-position
congruence (`Step.cong .gen_app ()` + `StepChildren.here`) lifting the reshaped β1, then a β-step whose contractum
is rewritten by named `weaken_subst_singleton` cancellations, composed by `StepStar.trans`.  No `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **β1 contractum reshape (left injection).**  Substituting the left handler into `leftInjection payload`'s
body discards nothing of the payload: the doubly-weakened payload collapses one level
(`subst_lift_singleton_weaken_weaken`, #1023) to `weaken payload`, and the left-handler variable becomes
`weaken handlerL`.  The reshape a concrete payload got by `rfl`. -/
theorem leftInjection_subst_handlerL (payload handlerL : RawTerm 0) :
    RawTerm.subst0
        (lamCell churchSumDomainAnn (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (RawTerm.weaken (RawTerm.weaken payload)))) handlerL
      = lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload)) := by
  dsimp only [RawTerm.subst0, churchSumDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (appCell _ (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerL))
      (RawTerm.weaken (RawTerm.weaken payload)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken payload handlerL]
  rfl

/-- **β1 contractum reshape (right injection).**  The dual: substituting the (discarded) left handler leaves the
inner `r`-variable in place and collapses `weaken² payload` to `weaken payload`. -/
theorem rightInjection_subst_handlerL (payload handlerL : RawTerm 0) :
    RawTerm.subst0
        (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
          (RawTerm.weaken (RawTerm.weaken payload)))) handlerL
      = lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload)) := by
  dsimp only [RawTerm.subst0, churchSumDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (appCell _ (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerL))
      (RawTerm.weaken (RawTerm.weaken payload)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken payload handlerL]
  rfl

/-- ★ **`case (inl payload) l r ↝* l payload`** for EVERY closed payload (not just `combinatorI`).  The left
injection's `case` selects the left handler and applies it to the arbitrary stored value.  Subsumes the concrete
`caseLeft_selectsLeftHandler` (#1019) — the symbolic generalization unblocked by the #1023 double-weaken
cancellation. -/
theorem caseLeft_selectsLeftHandler_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection payload) handlerL) handlerR)
      (appCell handlerL payload) := by
  have functionBeta : Step (appCell (leftInjection payload) handlerL)
      (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) := by
    rw [← leftInjection_subst_handlerL payload handlerL]; exact HeadStep.beta.toStep
  have congStep : Step (appCell (appCell (leftInjection payload) handlerL) handlerR)
      (appCell (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) handlerR)
      (appCell (RawTerm.subst0 (RawTerm.weaken handlerL) handlerR)
        (RawTerm.subst0 (RawTerm.weaken payload) handlerR)) := HeadStep.beta.toStep
  have cancelHandler : RawTerm.subst0 (RawTerm.weaken handlerL) handlerR = handlerL :=
    RawTerm.weaken_subst_singleton handlerL handlerR
  have cancelValue : RawTerm.subst0 (RawTerm.weaken payload) handlerR = payload :=
    RawTerm.weaken_subst_singleton payload handlerR
  rw [cancelHandler, cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- **`case (inr payload) l r ↝* r payload`** for every closed payload — the dual of
`caseLeft_selectsLeftHandler_general`.  Subsumes the concrete `caseRight_selectsRightHandler` (#1019). -/
theorem caseRight_selectsRightHandler_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (rightInjection payload) handlerL) handlerR)
      (appCell handlerR payload) := by
  have functionBeta : Step (appCell (rightInjection payload) handlerL)
      (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) := by
    rw [← rightInjection_subst_handlerL payload handlerL]; exact HeadStep.beta.toStep
  have congStep : Step (appCell (appCell (rightInjection payload) handlerL) handlerR)
      (appCell (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) handlerR)
      (appCell handlerR (RawTerm.subst0 (RawTerm.weaken payload) handlerR)) := HeadStep.beta.toStep
  have cancelValue : RawTerm.subst0 (RawTerm.weaken payload) handlerR = payload :=
    RawTerm.weaken_subst_singleton payload handlerR
  rw [cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- **The Church sum's tag selects the correct handler, for any stored payload.**  `case (inl payload) l r ↝*
l payload` AND `case (inr payload) l r ↝* r payload` — the coproduct encoding is faithful for ARBITRARY stored
data, completing the symbolic story (the #1019 `caseSelectsByTag` was at the concrete `combinatorI`). -/
theorem caseSelectsByTag_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection payload) handlerL) handlerR) (appCell handlerL payload)
    ∧ StepStar (appCell (appCell (rightInjection payload) handlerL) handlerR) (appCell handlerR payload) :=
  ⟨caseLeft_selectsLeftHandler_general payload handlerL handlerR,
   caseRight_selectsRightHandler_general payload handlerL handlerR⟩

end FX1Poly.Typed
