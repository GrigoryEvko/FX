import LeanFX2.Term.Subst

/-! # Term/Pointwise — substitution pointwise & commute lemmas

Lemmas about how `Term.subst` and `Term.rename` interact with
substitutions that are pointwise-equivalent or compose with each other.

## Approach

The Foundation layer (`Foundation/Subst.lean` + `Foundation/RawSubst.lean`)
proves Eq-shaped commute laws on `Ty` and `RawTerm` because their indices
are scope/level naturals — no dependency on contexts or term values.

At the Term layer, `Term someCtx someType raw` carries the *value* of
`someType` and `raw` as type-level indices, so Term-level commutes
generally come in two shapes:

* **Eq-shaped pointwise lemmas** — when both sides have the same
  `someType` and `raw` (e.g. `Term.subst_pointwise`: two TermSubsts
  over the same Subst).  These reduce to structural induction.
* **HEq-shaped commute lemmas** — when the subst/rename composition
  changes the index (e.g. `Term.subst_compose`: subst-then-subst vs
  subst-by-composed).  Both sides have types that are *propositionally*
  Eq via the Foundation lemmas, but not definitionally Eq, so HEq is
  the right tool.

Downstream consumers (Compat) lift HEq results to Eq via `▸` casts at
the use site, or absorb the index difference into the two-Ty signature
of Step / Step.par / StepStar / Conv.

## Dependencies

* `Term/Subst.lean`
* (transitively) `Foundation/Subst.lean`, `Foundation/RawSubst.lean`
-/

namespace LeanFX2

/-! ## Pointwise lemmas — TermSubsts agreeing on every position

When two TermSubsts over the *same* underlying `Subst` agree pointwise,
`Term.subst` produces equal results.  No HEq needed — both sides have
the same `someType.subst sigma` index.  Casts that appear in `Term.subst`
(e.g. via `Ty.weaken_subst_commute`) are identical between LHS and RHS
because they depend only on `sigma` and the type indices, not on the
TermSubst values themselves; rewriting with the IH passes through them
unchanged. -/

/-- Lift preserves pointwise equality of TermSubsts. -/
theorem TermSubst.lift_pointwise
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstTermSubst secondTermSubst : TermSubst sourceCtx targetCtx sigma}
    (pointwiseEq : ∀ position, firstTermSubst position = secondTermSubst position)
    (newSourceType : Ty level sourceScope) :
    ∀ position,
      firstTermSubst.lift newSourceType position =
        secondTermSubst.lift newSourceType position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show
        (Ty.weaken_subst_commute sigma
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
          Term.weaken (newSourceType.subst sigma)
            (firstTermSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩) =
        (Ty.weaken_subst_commute sigma
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
          Term.weaken (newSourceType.subst sigma)
            (secondTermSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      rw [pointwiseEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- Term.subst respects pointwise equality of TermSubsts.  If two
TermSubsts over the same Subst agree on every variable position, then
they substitute equally into every term.  29-case structural induction. -/
theorem Term.subst_pointwise
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    {firstTermSubst secondTermSubst : TermSubst sourceCtx targetCtx sigma}
    (pointwiseEq : ∀ position, firstTermSubst position = secondTermSubst position) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
      (someTerm : Term sourceCtx someType raw),
        Term.subst firstTermSubst someTerm = Term.subst secondTermSubst someTerm
  | _, _, .var position => pointwiseEq position
  | _, _, .unit => rfl
  | _, _, .lam body => by
      simp only [Term.subst]
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .app fnTerm argTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .lamPi body => by
      simp only [Term.subst]
      rw [Term.subst_pointwise (TermSubst.lift_pointwise pointwiseEq _) body]
  | _, _, .appPi fnTerm argTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq fnTerm,
          Term.subst_pointwise pointwiseEq argTerm]
  | _, _, .pair firstValue secondValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq firstValue,
          Term.subst_pointwise pointwiseEq secondValue]
  | _, _, .fst pairTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .snd pairTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pairTerm]
  | _, _, .boolTrue => rfl
  | _, _, .boolFalse => rfl
  | _, _, .boolElim scrutinee thenBranch elseBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq thenBranch,
          Term.subst_pointwise pointwiseEq elseBranch]
  | _, _, .natZero => rfl
  | _, _, .natSucc predecessor => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq predecessor]
  | _, _, .natElim scrutinee zeroBranch succBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .natRec scrutinee zeroBranch succBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq zeroBranch,
          Term.subst_pointwise pointwiseEq succBranch]
  | _, _, .listNil => rfl
  | _, _, .listCons headTerm tailTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq headTerm,
          Term.subst_pointwise pointwiseEq tailTerm]
  | _, _, .listElim scrutinee nilBranch consBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq nilBranch,
          Term.subst_pointwise pointwiseEq consBranch]
  | _, _, .optionNone => rfl
  | _, _, .optionSome valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .optionMatch scrutinee noneBranch someBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq noneBranch,
          Term.subst_pointwise pointwiseEq someBranch]
  | _, _, .eitherInl valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherInr valueTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq valueTerm]
  | _, _, .eitherMatch scrutinee leftBranch rightBranch => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq scrutinee,
          Term.subst_pointwise pointwiseEq leftBranch,
          Term.subst_pointwise pointwiseEq rightBranch]
  | _, _, .refl _ _ => rfl
  | _, _, .idJ baseCase witness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .idStrictRefl _ _ => rfl
  | _, _, .idStrictRec baseCase witness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseCase,
          Term.subst_pointwise pointwiseEq witness]
  | _, _, .modIntro innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .modElim innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .subsume innerTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerTerm]
  | _, _, .interval0 => rfl
  | _, _, .interval1 => rfl
  | _, _, .intervalOpp innerValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq innerValue]
  | _, _, .intervalMeet leftValue rightValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .intervalJoin leftValue rightValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq leftValue,
          Term.subst_pointwise pointwiseEq rightValue]
  | _, _, .pathLam _ _ _ body => by
      simp only [Term.subst]
      rw [Term.subst_pointwise
            (TermSubst.lift_pointwise pointwiseEq Ty.interval) body]
  | _, _, .pathApp pathTerm intervalTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq pathTerm,
          Term.subst_pointwise pointwiseEq intervalTerm]
  | _, _, .glueIntro _ _ baseValue partialValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq baseValue,
          Term.subst_pointwise pointwiseEq partialValue]
  | _, _, .glueElim gluedValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq gluedValue]
  | _, _, .transp _ _ _ _ _ _ typePath sourceValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq typePath,
          Term.subst_pointwise pointwiseEq sourceValue]
  | _, _, .hcomp sidesValue capValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq sidesValue,
          Term.subst_pointwise pointwiseEq capValue]
  | _, _, .recordIntro firstField => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq firstField]
  | _, _, .recordProj recordValue => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq recordValue]
  -- Universe-code: scope-polymorphic; both sides definitionally
  -- equal regardless of substitution (no var dependencies).
  | _, _, .universeCode _ _ _ _ => rfl
  -- Cumul-up — Phase CUMUL-2.6 Design D: subst arm recurses on
  -- inner typeCode, so pointwise propagates via Term.subst_pointwise
  -- on the typeCode.
  | _, _, .cumulUp _ _ _ _ _ typeCode => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq typeCode]
  -- HoTT canonical equivalence/funext refl-fragment witnesses: their
  -- subst arms in Term/Subst.lean depend ONLY on the underlying
  -- Subst (not on the TermSubst pointwise data), so both sides
  -- reduce to identical shapes.
  | _, _, .equivReflId _ => rfl
  | _, _, .funextRefl _ _ _ => rfl
  | _, _, .equivReflIdAtId _ _ _ _ => rfl
  | _, _, .funextReflAtId _ _ _ => rfl
  -- HoTT heterogeneous-carrier equivIntroHet (Phase 12.A.B8.5): the
  -- subst arm in Term/Subst.lean recurses on the two subterms via
  -- Term.subst (which respects pointwise hypothesis by structural
  -- IH).  Pointwise equality propagates through both forward and
  -- backward subterms, then the ctor reassembles identically.
  | _, _, .equivIntroHet forward backward => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq forward,
          Term.subst_pointwise pointwiseEq backward]
  | _, _, .equivApp equivTerm argumentTerm => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq equivTerm,
          Term.subst_pointwise pointwiseEq argumentTerm]
  -- HoTT heterogeneous-carrier path-from-equivalence (Phase 12.A.B8.5b):
  -- the subst arm in Term/Subst.lean recurses on the single subterm
  -- `equivWitness` via Term.subst.  Both TermSubsts share the SAME
  -- underlying `sigma`, so `carrierARaw.subst sigma.forRaw` and
  -- `carrierBRaw.subst sigma.forRaw` are identical on both sides
  -- (depending only on sigma, not on the TermSubst values).  Pointwise
  -- equality propagates through the equivWitness subterm via the
  -- structural IH and the ctor reassembles identically.
  | _, _, .uaIntroHet _ _ _ _ equivWitness => by
      simp only [Term.subst]
      rw [Term.subst_pointwise pointwiseEq equivWitness]
  -- HoTT heterogeneous-carrier funext-introduction at Id-of-arrow
  -- (Phase 12.A.B8.8): the subst arm in Term/Subst.lean has NO
  -- subterm to recurse on (funextIntroHet is a VALUE, like
  -- funextReflAtId).  Both TermSubsts share the SAME underlying
  -- `sigma`, so `domainType.subst sigma`, `codomainType.subst sigma`,
  -- `applyARaw.subst sigma.forRaw.lift`, and `applyBRaw.subst
  -- sigma.forRaw.lift` are all identical on both sides — they
  -- depend only on `sigma`, not on the TermSubst values.  rfl
  -- discharges the pointwise equality.
  | _, _, .funextIntroHet _ _ _ _ => rfl
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).  The subst
  -- arms in Term/Subst.lean for ALL ten ctors depend ONLY on the
  -- underlying `sigma` (specifically `sigma.forRaw`), NOT on the
  -- TermSubst pointwise data.  Both TermSubsts share the SAME
  -- `sigma`, so all schematic raw payloads substitute identically on
  -- both sides.  rfl discharges the pointwise equality.
  | _, _, .arrowCode _ _ _ _ => rfl
  | _, _, .piTyCode _ _ _ _ => rfl
  | _, _, .sigmaTyCode _ _ _ _ => rfl
  | _, _, .productCode _ _ _ _ => rfl
  | _, _, .sumCode _ _ _ _ => rfl
  | _, _, .listCode _ _ _ => rfl
  | _, _, .optionCode _ _ _ => rfl
  | _, _, .eitherCode _ _ _ _ => rfl
  | _, _, .idCode _ _ _ _ _ => rfl
  | _, _, .equivCode _ _ _ _ => rfl

/-! ## TermSubst composition

`TermSubst.compose` builds the typed companion of `Subst.compose`.
For each source position `position`, it produces a Term in the final
target whose type/raw match the composed substitution by post-substituting
the first TermSubst's value through the second TermSubst.  The Ty
alignment uses `Ty.subst_compose`; the raw alignment is definitional
(both `Subst.compose.forRaw` and `RawTermSubst.compose` are defined
pointwise as `(σ1.forRaw p).subst σ2.forRaw`). -/

/-- Compose two TermSubsts: post-substitute the first's image through
the second.  The Ty cast aligns `(varType src pos).subst σ1).subst σ2`
with `(varType src pos).subst (Subst.compose σ1 σ2)` via the typed
two-position cast helper `Term.castType`. -/
def TermSubst.compose
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst) :
    TermSubst sourceCtx targetCtx (Subst.compose firstSubst secondSubst) :=
  fun position =>
    cast
      (by rw [Ty.subst_compose firstSubst secondSubst (varType sourceCtx position)])
      (Term.subst secondTermSubst (firstTermSubst position))

/-- The cast in `TermSubst.compose` doesn't change the Term value
underneath — only the type index.  HEq witnesses this directly via
`cast_heq`. -/
theorem TermSubst.compose_position_HEq
    {mode : Mode} {level : Nat} {sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst)
    (position : Fin sourceScope) :
    HEq (TermSubst.compose firstTermSubst secondTermSubst position)
        (Term.subst secondTermSubst (firstTermSubst position)) :=
  cast_heq _ _

/-! ## Cast-aware HEq scaffolding for Term.subst_compose

The full `Term.subst_compose` (HEq, 29 cases) is a substantial cascade
because each `lam`/`lamPi`/`appPi`/`pair`/`snd` case has internal Ty
casts that must be aligned across the two formulations.  Following the
W7-analysis: HEq cascade hits a factorization limit at typed Term level.

We attempt the cascade incrementally.  Simple constructor families
(no internal cast on the recursive call) work cleanly; cast-bearing
families are handled with the HEq tactic helpers from
`Tools/Tactics/HEq`. -/

end LeanFX2
