import LeanFX2.Algo.Check
import LeanFX2.Algo.Infer
import LeanFX2.Algo.Eval
import LeanFX2.Term.Inversion

/-! # Algo/Soundness — algorithmic soundness theorems

The bidirectional checker is **type-sound by construction**: when
`Term.check` returns `some t`, Lean has already verified `t : Term
context expectedType raw` (the return type pins it).  Same for
`Term.infer` returning `some ⟨ty, t⟩`.

The **non-trivial** soundness statement is for `Term.eval`: every
fired reduction corresponds to a `Step` in the kernel relation.
This file ships per-case soundness theorems for each redex type
that `Term.headStep?` handles — each shows the head reduction
exists at the kernel level.

## Coverage

* `Term.headStep?_sound_boolElimTrue` — boolElim with true scrut
* `Term.headStep?_sound_boolElimFalse` — boolElim with false scrut
* `Term.headStep?_sound_natElimZero` — natElim with zero scrut
* `Term.headStep?_sound_natRecZero` — natRec with zero scrut
* `Term.headStep?_sound_listElimNil` — listElim with nil scrut
* `Term.headStep?_sound_optionMatchNone` — optionMatch with none scrut

Each derives the canonical scrutinee form from the headCtor bridge
(`Algo/WHNF.lean`) + uniqueness (`Term/Inversion.lean`), then
applies the corresponding `Step.iotaXY` constructor.

## Pattern

```lean
have rawEq := Term.headCtor_X_raw scrutinee headEq
cases rawEq
have scrutEq := eq_of_heq (Term.X_unique scrutinee Term.X)
rw [scrutEq]
exact Step.iotaYZ ...
```

All zero-axiom under strict policy.

## Future: full `Term.headStep?` soundness

Combining all 6 case theorems via case analysis on
`Term.headStep?`'s output gives:

```lean
theorem Term.headStep?_sound (someTerm : Term context someType raw)
    (h : someTerm.headStep? = some result) :
    Step someTerm result.snd
```

That closure is deferred — the per-case theorems give the same
information point-by-point.

## Dependencies

* `Algo/Check.lean`, `Algo/Infer.lean`, `Algo/Eval.lean`
* `Algo/WHNF.lean` — headCtor inversion bridges
* `Term/Inversion.lean` — Term ctor uniqueness lemmas
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Soundness for the boolElim-true case of `Term.headStep?`:
when the scrutinee's head is `boolTrue`, the result `thenBranch`
is reachable via `Step.iotaBoolElimTrue`. -/
theorem Term.headStep?_sound_boolElimTrue
    {motiveType : Ty level scope}
    {scrutRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.boolTrue) :
    Step (Term.boolElim scrutinee thenBranch elseBranch) thenBranch := by
  have rawEq : scrutRaw = RawTerm.boolTrue :=
    Term.headCtor_boolTrue_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.boolTrue :=
    eq_of_heq (Term.boolTrue_unique scrutinee Term.boolTrue)
  rw [scrutEq]
  exact Step.iotaBoolElimTrue thenBranch elseBranch

/-- Soundness for the boolElim-false case of `Term.headStep?`. -/
theorem Term.headStep?_sound_boolElimFalse
    {motiveType : Ty level scope}
    {scrutRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.boolFalse) :
    Step (Term.boolElim scrutinee thenBranch elseBranch) elseBranch := by
  have rawEq : scrutRaw = RawTerm.boolFalse :=
    Term.headCtor_boolFalse_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.boolFalse :=
    eq_of_heq (Term.boolFalse_unique scrutinee Term.boolFalse)
  rw [scrutEq]
  exact Step.iotaBoolElimFalse thenBranch elseBranch

/-- Soundness for the natElim-zero case of `Term.headStep?`. -/
theorem Term.headStep?_sound_natElimZero
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natZero) :
    Step (Term.natElim scrutinee zeroBranch succBranch) zeroBranch := by
  have rawEq : scrutRaw = RawTerm.natZero :=
    Term.headCtor_natZero_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.natZero :=
    eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
  rw [scrutEq]
  exact Step.iotaNatElimZero zeroBranch succBranch

/-- Soundness for the natRec-zero case of `Term.headStep?`. -/
theorem Term.headStep?_sound_natRecZero
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natZero) :
    Step (Term.natRec scrutinee zeroBranch succBranch) zeroBranch := by
  have rawEq : scrutRaw = RawTerm.natZero :=
    Term.headCtor_natZero_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.natZero :=
    eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
  rw [scrutEq]
  exact Step.iotaNatRecZero zeroBranch succBranch

/-- Strong listNil uniqueness when both terms are at the SAME element
type — the case the soundness theorem needs.  Proved by freeing the
type indices, casing on each, then using injectivity of `Ty.listType`
to align the implicit elementTypes. -/
theorem Term.listNil_unique_sameType
    {elementType : Ty level scope}
    (t1 t2 : Term context (Ty.listType elementType) RawTerm.listNil) :
    HEq t1 t2 := by
  suffices key : ∀ {ty1 ty2 : Ty level scope}
                  (s1 : Term context ty1 RawTerm.listNil)
                  (s2 : Term context ty2 RawTerm.listNil),
                  ty1 = Ty.listType elementType →
                  ty2 = Ty.listType elementType →
                  HEq s1 s2 by
    exact key t1 t2 rfl rfl
  intro ty1 ty2 s1 s2 ty1Eq ty2Eq
  cases s1
  cases s2
  rename_i elt1 elt2
  have elt1Eq : elt1 = elementType := Ty.listType.inj ty1Eq
  have elt2Eq : elt2 = elementType := Ty.listType.inj ty2Eq
  cases elt1Eq
  cases elt2Eq
  rfl

/-- Strong optionNone uniqueness at SAME element type. -/
theorem Term.optionNone_unique_sameType
    {elementType : Ty level scope}
    (t1 t2 : Term context (Ty.optionType elementType) RawTerm.optionNone) :
    HEq t1 t2 := by
  suffices key : ∀ {ty1 ty2 : Ty level scope}
                  (s1 : Term context ty1 RawTerm.optionNone)
                  (s2 : Term context ty2 RawTerm.optionNone),
                  ty1 = Ty.optionType elementType →
                  ty2 = Ty.optionType elementType →
                  HEq s1 s2 by
    exact key t1 t2 rfl rfl
  intro ty1 ty2 s1 s2 ty1Eq ty2Eq
  cases s1
  cases s2
  rename_i elt1 elt2
  have elt1Eq : elt1 = elementType := Ty.optionType.inj ty1Eq
  have elt2Eq : elt2 = elementType := Ty.optionType.inj ty2Eq
  cases elt1Eq
  cases elt2Eq
  rfl

/-- Soundness for the listElim-nil case of `Term.headStep?`. -/
theorem Term.headStep?_sound_listElimNil
    {elementType motiveType : Ty level scope}
    {scrutRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType)
                                            motiveType)) consRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.listNil) :
    Step (Term.listElim scrutinee nilBranch consBranch) nilBranch := by
  have rawEq : scrutRaw = RawTerm.listNil :=
    Term.headCtor_listNil_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.listNil :=
    eq_of_heq (Term.listNil_unique_sameType scrutinee Term.listNil)
  rw [scrutEq]
  exact Step.iotaListElimNil nilBranch consBranch

/-- Soundness for the optionMatch-none case of `Term.headStep?`. -/
theorem Term.headStep?_sound_optionMatchNone
    {elementType motiveType : Ty level scope}
    {scrutRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.optionNone) :
    Step (Term.optionMatch scrutinee noneBranch someBranch) noneBranch := by
  have rawEq : scrutRaw = RawTerm.optionNone :=
    Term.headCtor_optionNone_raw scrutinee headEq
  cases rawEq
  have scrutEq : scrutinee = Term.optionNone :=
    eq_of_heq (Term.optionNone_unique_sameType scrutinee Term.optionNone)
  rw [scrutEq]
  exact Step.iotaOptionMatchNone noneBranch someBranch

/-! ## Payload-bearing β/ι soundness

The five soundness theorems for `Term.headStep?` firings on
canonical-with-payload scrutinee shapes — natElim/natRec succ,
listElim cons, optionMatch some, eitherMatch inl/inr.

Each follows the pattern:
1. From `scrutinee.headCtor = .X`, derive raw shape via
   `Term.headCtor_X_raw` (existential over payload raw).
2. Cases the raw equation to make raw concrete.
3. Apply `Term.<ctor>Destruct` to extract the typed payload + HEq.
4. Use the HEq to substitute scrutinee with the canonical form.
5. Apply the matching `Step.iota<Rule>` ctor.

Returns: the firing produces a Step witness from source to
the β/ι-reduct.  Zero-axiom under strict policy via
match-with-witness pattern (`feedback_lean_match_witness_pattern.md`).

These are the building blocks for closing the M08 contract
(extending `Term.headStep?_sound` to handle payload-firings). -/

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Soundness for the natElim-succ case: when scrutinee's head
is `natSucc`, the firing produces `app succBranch predTerm`,
reachable via `Step.iotaNatElimSucc`. -/
theorem Term.headStep?_sound_natElimSucc
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw' : RawTerm scope) (predTerm : Term context Ty.nat predRaw'),
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.app succBranch predTerm) := by
  obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee headEq
  cases rawEq
  obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
  have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutHEq
  refine ⟨_, predTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaNatElimSucc predTerm zeroBranch succBranch

/-- Soundness for the natRec-succ case. -/
theorem Term.headStep?_sound_natRecSucc
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw' : RawTerm scope) (predTerm : Term context Ty.nat predRaw'),
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.app (Term.app succBranch predTerm)
                     (Term.natRec predTerm zeroBranch succBranch)) := by
  obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee headEq
  cases rawEq
  obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
  have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutHEq
  refine ⟨_, predTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaNatRecSucc predTerm zeroBranch succBranch

/-- Soundness for the listElim-cons case. -/
theorem Term.headStep?_sound_listElimCons
    {elementType motiveType : Ty level scope}
    {scrutRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context
                    (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.listCons) :
    ∃ (headRaw' tailRaw' : RawTerm scope)
      (headTerm : Term context elementType headRaw')
      (tailTerm : Term context (Ty.listType elementType) tailRaw'),
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.app (Term.app consBranch headTerm) tailTerm) := by
  obtain ⟨headRaw, tailRaw, rawEq⟩ := Term.headCtor_listCons_raw scrutinee headEq
  cases rawEq
  obtain ⟨headTerm, tailTerm, scrutHEq⟩ := Term.listConsDestruct scrutinee
  have scrutEq : scrutinee = Term.listCons headTerm tailTerm := eq_of_heq scrutHEq
  refine ⟨_, _, headTerm, tailTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaListElimCons headTerm tailTerm nilBranch consBranch

/-- Soundness for the optionMatch-some case. -/
theorem Term.headStep?_sound_optionMatchSome
    {elementType motiveType : Ty level scope}
    {scrutRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.optionSome) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context elementType valueRaw'),
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.app someBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_optionSome_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.optionSomeDestruct scrutinee
  have scrutEq : scrutinee = Term.optionSome valueTerm := eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaOptionMatchSome valueTerm noneBranch someBranch

/-- Soundness for the eitherMatch-inl case. -/
theorem Term.headStep?_sound_eitherMatchInl
    {leftType rightType motiveType : Ty level scope}
    {scrutRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightBranchRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.eitherInl) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context leftType valueRaw'),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.app leftBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInl_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInlDestruct scrutinee
  have scrutEq : scrutinee = Term.eitherInl (rightType := rightType) valueTerm :=
    eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaEitherMatchInl valueTerm leftBranch rightBranch

/-- Soundness for the eitherMatch-inr case. -/
theorem Term.headStep?_sound_eitherMatchInr
    {leftType rightType motiveType : Ty level scope}
    {scrutRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightBranchRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.eitherInr) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context rightType valueRaw'),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.app rightBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInr_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInrDestruct scrutinee
  have scrutEq : scrutinee = Term.eitherInr (leftType := leftType) valueTerm :=
    eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaEitherMatchInr valueTerm leftBranch rightBranch

/-! ## Closure soundness

`Term.headStep?_sound` combines the 6 per-case theorems above
into a single closed-over statement: whenever `headStep?` fires
(returns `some _`), the result is reachable via `Step` from the
source term.

This is the load-bearing soundness contract for `Algo/Eval`:
the typed evaluator never produces a result that disagrees with
the kernel's reduction relation.

The proof case-analyses on the source term's outer constructor:
* Value, neutral, and deferred redex ctors have `headStep? = none`
  definitionally; the
  `firedEq : none = some _` hypothesis is closed by `simp` /
  `nomatch`.
* 5 eliminator ctors (boolElim, natElim, natRec, listElim,
  optionMatch) require splitting on the scrutinee's `headCtor`
  to identify which ι-rule fired, then applying the corresponding
  per-case theorem.

Zero-axiom under strict policy. -/

theorem Term.headStep?_sound
    {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context someType raw)
    {result : Σ (resultRaw : RawTerm scope), Term context someType resultRaw}
    (firedEq : someTerm.headStep? = some result) :
    Step someTerm result.snd := by
  cases someTerm with
  | var _ => nomatch firedEq
  | unit => nomatch firedEq
  | lam _ => nomatch firedEq
  | lamPi _ => nomatch firedEq
  | pair _ _ => nomatch firedEq
  | boolTrue => nomatch firedEq
  | boolFalse => nomatch firedEq
  | natZero => nomatch firedEq
  | natSucc _ => nomatch firedEq
  | listNil => nomatch firedEq
  | listCons _ _ => nomatch firedEq
  | optionNone => nomatch firedEq
  | optionSome _ => nomatch firedEq
  | eitherInl _ => nomatch firedEq
  | eitherInr _ => nomatch firedEq
  | refl _ _ => nomatch firedEq
  | oeqRefl _ _ => nomatch firedEq
  | oeqJ _ _ => nomatch firedEq
  | oeqFunext _ _ _ _ _ => nomatch firedEq
  | modIntro _ => nomatch firedEq
  | subsume _ => nomatch firedEq
  | interval0 => nomatch firedEq
  | interval1 => nomatch firedEq
  | intervalOpp _ => nomatch firedEq
  | intervalMeet _ _ => nomatch firedEq
  | intervalJoin _ _ => nomatch firedEq
  | pathLam _ _ _ _ => nomatch firedEq
  | glueIntro _ _ _ _ => nomatch firedEq
  | transp _ _ _ _ _ _ _ _ => nomatch firedEq
  | hcomp _ _ => nomatch firedEq
  | recordIntro _ => nomatch firedEq
  | recordProj _ => nomatch firedEq
  | refineIntro _ _ _ => nomatch firedEq
  | refineElim _ => nomatch firedEq
  | codataUnfold _ _ => nomatch firedEq
  | codataDest _ => nomatch firedEq
  | sessionSend _ _ _ => nomatch firedEq
  | sessionRecv _ => nomatch firedEq
  | effectPerform _ _ _ => nomatch firedEq
  | universeCode _ _ _ _ => nomatch firedEq
  | cumulUp _ _ _ _ _ _ => nomatch firedEq
  | equivReflId _ => nomatch firedEq
  | funextRefl _ _ _ => nomatch firedEq
  | equivReflIdAtId _ _ _ _ => nomatch firedEq
  | funextReflAtId _ _ _ => nomatch firedEq
  | equivIntroHet _ _ => nomatch firedEq
  | equivApp _ _ => nomatch firedEq
  | uaIntroHet _ _ _ _ _ => nomatch firedEq
  | funextIntroHet _ _ _ _ => nomatch firedEq
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped, all return
  -- `none` from headStep?, so `firedEq : none = some _` is contradictory).
  | arrowCode _ _ _ _ => nomatch firedEq
  | piTyCode _ _ _ _ => nomatch firedEq
  | sigmaTyCode _ _ _ _ => nomatch firedEq
  | productCode _ _ _ _ => nomatch firedEq
  | sumCode _ _ _ _ => nomatch firedEq
  | listCode _ _ _ => nomatch firedEq
  | optionCode _ _ _ => nomatch firedEq
  | eitherCode _ _ _ _ => nomatch firedEq
  | idCode _ _ _ _ _ => nomatch firedEq
  | equivCode _ _ _ _ => nomatch firedEq
  -- Eliminators not yet handled by headStep? (return none)
  | app _ _ => nomatch firedEq
  | appPi _ _ => nomatch firedEq
  | pathApp _ _ => nomatch firedEq
  | glueElim _ => nomatch firedEq
  | fst _ => nomatch firedEq
  | snd _ => nomatch firedEq
  | idJ _ _ => nomatch firedEq
  | idStrictRefl _ _ => nomatch firedEq
  | idStrictRec _ _ => nomatch firedEq
  | modElim _ => nomatch firedEq
  -- Firing eliminators.  Each dispatches on the scrutinee's
  -- `headCtor` value; the firing ι-rule depends on which canonical
  -- ctor the scrutinee has reduced to.
  --
  -- Pattern (from feedback_lean_match_propext_recipe.md): use
  -- `match headEq : scrutinee.headCtor with`, then `rw [show ...
  -- from rfl, headEq]` to definitionally unfold `headStep?` and
  -- substitute the headCtor value.  Avoids `simp` and `by_cases`
  -- which both leak propext on this large dep-typed match.
  | boolElim scrutinee thenBranch elseBranch =>
    match headEq : scrutinee.headCtor with
    | .boolTrue =>
      rw [show (Term.boolElim scrutinee thenBranch elseBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .boolTrue then some ⟨_, thenBranch⟩
               else if scrutineeHead == .boolFalse then some ⟨_, elseBranch⟩
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_boolElimTrue scrutinee thenBranch elseBranch headEq
    | .boolFalse =>
      rw [show (Term.boolElim scrutinee thenBranch elseBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .boolTrue then some ⟨_, thenBranch⟩
               else if scrutineeHead == .boolFalse then some ⟨_, elseBranch⟩
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_boolElimFalse scrutinee thenBranch elseBranch headEq
    -- Other head values: headStep? returns none, contradiction
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.boolElim scrutinee thenBranch elseBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .boolTrue then some ⟨_, thenBranch⟩
               else if scrutineeHead == .boolFalse then some ⟨_, elseBranch⟩
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | natElim scrutinee zeroBranch succBranch =>
    match headEq : scrutinee.headCtor with
    | .natZero =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_natElimZero scrutinee zeroBranch succBranch headEq
    | .natSucc =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructNatSucc scrutinee with
      | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaNatElimSucc predTerm zeroBranch succBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | natRec scrutinee zeroBranch succBranch =>
    match headEq : scrutinee.headCtor with
    | .natZero =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_natRecZero scrutinee zeroBranch succBranch headEq
    | .natSucc =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructNatSucc scrutinee with
      | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaNatRecSucc predTerm zeroBranch succBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | listElim scrutinee nilBranch consBranch =>
    match headEq : scrutinee.headCtor with
    | .listNil =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_listElimNil scrutinee nilBranch consBranch headEq
    | .listCons =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructListCons scrutinee with
      | some ⟨_, _, headTerm, tailTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.listCons headTerm tailTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaListElimCons headTerm tailTerm nilBranch consBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | optionMatch scrutinee noneBranch someBranch =>
    match headEq : scrutinee.headCtor with
    | .optionNone =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_optionMatchNone scrutinee noneBranch someBranch headEq
    | .optionSome =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructOptionSome scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.optionSome valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaOptionMatchSome valueTerm noneBranch someBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | eitherMatch scrutinee leftBranch rightBranch =>
    match headEq : scrutinee.headCtor with
    | .eitherInl =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructEitherInl scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq :
            scrutinee = Term.eitherInl (rightType := _) valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaEitherMatchInl valueTerm leftBranch rightBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .eitherInr =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructEitherInr scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq :
            scrutinee = Term.eitherInr (leftType := _) valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaEitherMatchInr valueTerm leftBranch rightBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq

/-! ## Multi-step closure: `Term.eval_sound`

Lift `Term.headStep?_sound` through the fuel-bounded loop in
`Term.eval`.  Whenever `Term.eval fuel` produces a result, that
result is reachable from the source term via a `StepStar` chain
of length ≤ fuel.

This is the END-TO-END soundness contract for the typed
evaluator: `Term.eval` is a sound implementation of the kernel's
multi-step reduction (within the restricted ι-rule subset that
`headStep?` currently fires).

Proof: induction on fuel.
* `fuel = 0`: `eval 0 t = ⟨_, t⟩`, so `StepStar.refl t`.
* `fuel = n + 1`: case on `t.headStep?`:
  - `none`: `eval (n+1) t = ⟨_, t⟩`, `StepStar.refl t`.
  - `some ⟨_, reducedTerm⟩`: per `headStep?_sound`,
    `Step t reducedTerm`; per IH on `n`, `StepStar reducedTerm
    (eval n reducedTerm).snd`; compose via `StepStar.step`.

Zero-axiom under strict policy. -/

theorem Term.eval_sound
    {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope} :
    ∀ (fuel : Nat) (someTerm : Term context someType raw),
      StepStar someTerm (Term.eval fuel someTerm).snd
  | 0, someTerm => by
    -- `Term.eval 0 someTerm = ⟨_, someTerm⟩` by definition
    show StepStar someTerm someTerm
    exact StepStar.refl someTerm
  | fuel + 1, someTerm => by
    -- `Term.eval (fuel+1) someTerm = match someTerm.headStep? with ...`
    -- Case on the firing.
    match firedEq : someTerm.headStep? with
    | none =>
      -- eval returns ⟨_, someTerm⟩
      show StepStar someTerm (Term.eval (fuel + 1) someTerm).snd
      rw [show (Term.eval (fuel + 1) someTerm)
            = (match someTerm.headStep? with
               | some ⟨_, reducedTerm⟩ => Term.eval fuel reducedTerm
               | none => ⟨_, someTerm⟩) from rfl, firedEq]
      exact StepStar.refl someTerm
    | some ⟨reducedRaw, reducedTerm⟩ =>
      -- eval continues with reducedTerm
      have firstStep : Step someTerm reducedTerm :=
        Term.headStep?_sound someTerm firedEq
      have tailChain : StepStar reducedTerm (Term.eval fuel reducedTerm).snd :=
        Term.eval_sound fuel reducedTerm
      show StepStar someTerm (Term.eval (fuel + 1) someTerm).snd
      rw [show (Term.eval (fuel + 1) someTerm)
            = (match someTerm.headStep? with
               | some ⟨_, reducedTerm⟩ => Term.eval fuel reducedTerm
               | none => ⟨_, someTerm⟩) from rfl, firedEq]
      exact StepStar.step firstStep tailChain

end LeanFX2

namespace LeanFX2.Algo

end LeanFX2.Algo
