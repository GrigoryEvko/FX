import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ChurchSums — Church-encoded coproducts (Either) in the λ-fragment

The shipped Church encodings cover booleans (#981), numerals (#989), and PRODUCTS (#1017/#1018).  This file
adds the last classical data shape — COPRODUCTS (sums / `Either`) — via the Church encoding, demonstrating that
the Π-fragment encodes tagged-union data through polymorphism, exactly dual to the Church pair:

  `inl a = λl. λr. l a`,   `inr b = λl. λr. r b`,   `case s l r = s l r`

A Church sum value is its own eliminator: it stores a payload together with a TAG realized as *which of the two
handlers it applies*.  `leftInjection` ("`inl`") applies the LEFT handler to its payload and discards the right;
`rightInjection` ("`inr`") applies the RIGHT handler and discards the left.  Case analysis is therefore just
application of the value to the two handlers, and the value's tag selects which handler fires:

  * **`caseLeft_selectsLeftHandler`** — `case (inl I) l r ↝* l I`: applying `inl I` to handlers `l`, `r`
    β-reduces (discarding `r`) to `l I` — the left handler applied to the stored value.
  * **`caseRight_selectsRightHandler`** — `case (inr I) l r ↝* r I`: the dual — `inr I` selects the RIGHT
    handler, reducing to `r I` (discarding `l`).
  * **`caseSelectsByTag` (★)** — the round-trip bundle: for all handlers `l, r`, `case (inl I) l r ↝* l I` AND
    `case (inr I) l r ↝* r I`.  The two injections are distinguished operationally by which handler their
    `case` selects — coproducts realized in the pure Π-fragment, no primitive sum type needed.

The injections `leftInjection` / `rightInjection` are defined for an ARBITRARY stored payload, but the
case-selection reductions are proved at the CONCRETE closed stored value `combinatorI`: with a symbolic payload
`a` the pair's inner `subst (lift (singleton handler)) (weaken² a)` does not collapse to `weaken a` by `rfl` (it
needs a weaken/subst commutation lemma), whereas the concrete closed `I` makes every under-binder substitution
compute — exactly the situation in `CombinatoryCompleteness` (`SKK` works because the concrete closed `K` makes
the substitutions definitional).  The symbolic-payload generalization is therefore a deferred de Bruijn exercise,
tracked alongside the general S-rule.

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

Each `caseTag_selects…` chains a function-position congruence (`Step.cong .gen_app ()` + `StepChildren.here` with
explicitly-pinned `parentScope`/`headShift`/`restShifts`) lifting the FIRST β-step (the outer-binder
contraction, which discards the unselected handler) under the outer application, then a second `Step.beta` whose
symbolic-handler / concrete-value contractum is rewritten by a named `subst0`-typed cancellation `have`
(`RawTerm.weaken_subst_singleton`, stated at `subst0` so the `rw` matches the term), all composed by
`StepStar.trans`.  `caseSelectsByTag` bundles the two.  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- A closed, scope-polymorphic domain annotation for the Church-sum binders.  Under T2 every `lamCell` carries a
domain; for these pure-raw fixtures (no typing derivation) a closed `universeCodeCell` is invariant under
`subst0`/`weaken` and heads no redex, keeping the case-selection reductions computational. -/
def churchSumDomainAnn {scope : Nat} : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- `inl a = λl. λr. l a` — the LEFT injection of a Church sum: applies the left handler (`l`, the outer binder,
appearing as `var 1` under the two binders) to the stored payload `a`, discarding the right handler `r`. -/
def leftInjection (payload : RawTerm 0) : RawTerm 0 :=
  lamCell churchSumDomainAnn (lamCell churchSumDomainAnn
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      (RawTerm.weaken (RawTerm.weaken payload))))

/-- `inr b = λl. λr. r b` — the RIGHT injection of a Church sum: applies the right handler (`r`, the inner binder,
appearing as `var 0`) to the stored payload `b`, discarding the left handler `l`. -/
def rightInjection (payload : RawTerm 0) : RawTerm 0 :=
  lamCell churchSumDomainAnn (lamCell churchSumDomainAnn
    (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
      (RawTerm.weaken (RawTerm.weaken payload))))

/-- **`case (inl I) l r ↝* l I`** — case-analysing the LEFT injection selects the LEFT handler.  Applying
`inl I` to `handlerL` β-reduces (discarding the still-to-come right handler, since the left injection's body never
mentions the inner binder `r`) to `λr. (weaken handlerL) (weaken I)`; applying that to `handlerR` discards `r` and
selects `handlerL`, recovering the stored value via the `subst0 (weaken ·) handlerR = ·` cancellations. -/
theorem caseLeft_selectsLeftHandler (handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection combinatorI) handlerL) handlerR)
      (appCell handlerL combinatorI) := by
  have functionBeta : Step (appCell (leftInjection combinatorI) handlerL)
      (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) := HeadStep.beta.toStep
  have congStep : Step (appCell (appCell (leftInjection combinatorI) handlerL) handlerR)
      (appCell (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell churchSumDomainAnn (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) handlerR)
      (appCell (RawTerm.subst0 (RawTerm.weaken handlerL) handlerR)
        (RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR)) := HeadStep.beta.toStep
  have cancelHandler : RawTerm.subst0 (RawTerm.weaken handlerL) handlerR = handlerL :=
    RawTerm.weaken_subst_singleton handlerL handlerR
  have cancelValue : RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI handlerR
  rw [cancelHandler, cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- **`case (inr I) l r ↝* r I`** — the dual of `caseLeft_selectsLeftHandler`: case-analysing the RIGHT injection
selects the RIGHT handler.  Applying `inr I` to `handlerL` β-reduces (discarding `handlerL`, since the right
injection returns its inner binder `r`) to `λr. r (weaken I)`; applying that to `handlerR` selects `handlerR`,
recovering the stored value via the `subst0 (weaken I) handlerR = I` cancellation. -/
theorem caseRight_selectsRightHandler (handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (rightInjection combinatorI) handlerL) handlerR)
      (appCell handlerR combinatorI) := by
  have functionBeta : Step (appCell (rightInjection combinatorI) handlerL)
      (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) := HeadStep.beta.toStep
  have congStep : Step (appCell (appCell (rightInjection combinatorI) handlerL) handlerR)
      (appCell (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell churchSumDomainAnn (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) handlerR)
      (appCell handlerR (RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR)) := HeadStep.beta.toStep
  have cancelValue : RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI handlerR
  rw [cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

/-- ★ **The Church sum's tag selects the correct handler.**  For all handlers `l, r`, `case (inl I) l r ↝* l I`
AND `case (inr I) l r ↝* r I` — the two injections are distinguished operationally by which handler their `case`
fires, exactly as a coproduct's two constructors are distinguished by which branch the eliminator takes.
Coproducts are realized in the pure Π-fragment via polymorphism, dual to the Church pair (#1017), no primitive
sum type needed. -/
theorem caseSelectsByTag (handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection combinatorI) handlerL) handlerR) (appCell handlerL combinatorI)
    ∧ StepStar (appCell (appCell (rightInjection combinatorI) handlerL) handlerR) (appCell handlerR combinatorI) :=
  ⟨caseLeft_selectsLeftHandler handlerL handlerR, caseRight_selectsRightHandler handlerL handlerR⟩

end FX1Poly.Typed
