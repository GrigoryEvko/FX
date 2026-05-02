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

end LeanFX2

namespace LeanFX2.Algo

-- TODO Phase 9.G: closure theorem `Term.headStep?_sound` combining
-- all 6 per-case theorems via case analysis on the function output

end LeanFX2.Algo
