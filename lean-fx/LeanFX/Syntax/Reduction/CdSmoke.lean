import LeanFX.Syntax.CdDominates
import LeanFX.Syntax.Reduction.CdLemmaStar
import LeanFX.Syntax.Reduction.CdLemmaStarWithBi
import LeanFX.Syntax.Reduction.Diamond
import LeanFX.Syntax.TermExtraction

namespace LeanFX.Syntax
open LeanFX.Mode

/-! # Smoke tests for the typed cd cascade.

Compile-time exercises of `Term.cd`, `Step.par.cd_dominates`,
`Step.par.cd_lemma_star`, and `Step.par.diamond` on canonical
typed terms.  These regress the W8.1–W8.7 chain: any future change
that breaks the propext-free shape of `Term.cd`, the single-par
output of `cd_dominates`, the parStar output of `cd_lemma_star`,
or the diamond corollary will fail to elaborate here.

Each example exists to ensure:

  * The constructor signatures still align (no off-by-one on
    indices, no missing implicit arguments).
  * The cd cascade works end-to-end on representative terms.
  * Future refactors of the kernel preserve the public-facing
    confluence API.

Coverage focuses on canonical βι-witnessed cases.  Tests that
would require typed confluence (`Step.parStar.confluence`) are
deliberately omitted — that proof is deferred per #1079
investigation; see WS.2 for the structural blocker. -/

namespace CdSmokeTest

/-- Empty software-mode context at level 0, scope 0.  Same shape as
the `EmptyCtx` private abbreviation in `LeanFX.Syntax.Smoke`. -/
private abbrev EmptyCtx : Ctx Mode.software 0 0 := .nil Mode.software

/-! ### `Term.cd` on ground terms.

For terms with no redex inside, `cd` reduces to itself
(definitionally).  These smoke tests verify the match arms in
`Term.cd`'s 25-RawTerm-shape outer dispatch return the expected
identity-shaped result. -/

/-- `cd unit = unit`. -/
example : Term.cd (Term.unit (context := EmptyCtx)) = Term.unit :=
  rfl

/-- `cd boolTrue = boolTrue`. -/
example : Term.cd (Term.boolTrue (context := EmptyCtx)) = Term.boolTrue :=
  rfl

/-- `cd boolFalse = boolFalse`. -/
example : Term.cd (Term.boolFalse (context := EmptyCtx)) = Term.boolFalse :=
  rfl

/-- `cd natZero = natZero`. -/
example : Term.cd (Term.natZero (context := EmptyCtx)) = Term.natZero :=
  rfl

/-- `cd listNil = listNil`. -/
example :
    Term.cd (Term.listNil (context := EmptyCtx) (elementType := Ty.bool))
            = Term.listNil :=
  rfl

/-- `cd optionNone = optionNone`. -/
example :
    Term.cd (Term.optionNone (context := EmptyCtx) (elementType := Ty.bool))
            = Term.optionNone :=
  rfl

/-! ### `Step.par.cd_dominates` on ground terms.

Every term reduces to its own `cd` in one parallel step.  Smoke
tests verify the recursion bottoms out at the constant-shape
arms (`var`, `unit`, ground constructors). -/

/-- `unit ⟶par cd unit`.  The `cd unit` reduces to `unit`,
so this is just the reflexivity step. -/
example : Step.par (Term.unit (context := EmptyCtx))
            (Term.cd (Term.unit (context := EmptyCtx))) :=
  Step.par.cd_dominates Term.unit

/-- `boolTrue ⟶par cd boolTrue`. -/
example : Step.par (Term.boolTrue (context := EmptyCtx))
            (Term.cd (Term.boolTrue (context := EmptyCtx))) :=
  Step.par.cd_dominates Term.boolTrue

/-- `natZero ⟶par cd natZero`. -/
example : Step.par (Term.natZero (context := EmptyCtx))
            (Term.cd (Term.natZero (context := EmptyCtx))) :=
  Step.par.cd_dominates Term.natZero

/-- `natSucc natZero ⟶par cd (natSucc natZero)`. -/
example :
    Step.par (Term.natSucc (Term.natZero (context := EmptyCtx)))
      (Term.cd (Term.natSucc (Term.natZero (context := EmptyCtx)))) :=
  Step.par.cd_dominates _

/-! ### `Step.par.cd_lemma_star` on refl-only chains.

When the parallel step is `Step.par.refl term`, the cd lemma
specializes to `term ⟶par* cd term` — guaranteed by the refl
case of `parStarWithBi`. -/

/-- Refl step yields a parStar chain to `cd`. -/
example :
    Step.parStar (Term.unit (context := EmptyCtx))
      (Term.cd (Term.unit (context := EmptyCtx))) :=
  Step.par.cd_lemma_star (Step.par.isBi.refl Term.unit)

/-- Refl on `boolTrue`. -/
example :
    Step.parStar (Term.boolTrue (context := EmptyCtx))
      (Term.cd (Term.boolTrue (context := EmptyCtx))) :=
  Step.par.cd_lemma_star (Step.par.isBi.refl Term.boolTrue)

/-! ### `Step.par.diamond` on refl-only diverging steps.

Two `refl` steps from the same source both reduce (in `parStar`)
to `cd source`.  This is the simplest diamond witness — both
legs collapse to the canonical reduct. -/

/-- Two refl steps from `unit` join at `cd unit = unit`. -/
example :
    ∃ commonReduct,
      Step.parStar (Term.unit (context := EmptyCtx)) commonReduct ∧
      Step.parStar (Term.unit (context := EmptyCtx)) commonReduct :=
  Step.par.diamond
    (Step.par.isBi.refl Term.unit)
    (Step.par.isBi.refl Term.unit)

/-- Two refl steps from `boolTrue` join. -/
example :
    ∃ commonReduct,
      Step.parStar (Term.boolTrue (context := EmptyCtx)) commonReduct ∧
      Step.parStar (Term.boolTrue (context := EmptyCtx)) commonReduct :=
  Step.par.diamond
    (Step.par.isBi.refl Term.boolTrue)
    (Step.par.isBi.refl Term.boolTrue)

/-- Two refl steps from a structured nat term `succ zero` join. -/
example :
    ∃ commonReduct,
      Step.parStar
        (Term.natSucc (Term.natZero (context := EmptyCtx)))
        commonReduct ∧
      Step.parStar
        (Term.natSucc (Term.natZero (context := EmptyCtx)))
        commonReduct :=
  Step.par.diamond
    (Step.par.isBi.refl _)
    (Step.par.isBi.refl _)

/-! ### `Step.par.diamond_isBi` — diamond with chain-isBi witnesses.

Same diamond shape, but each leg's chain is annotated with the
`Step.parStar.isBi` predicate.  Used downstream when chain
confluence has to keep the recursive chain in the βι-restricted
regime. -/

/-- Refl-pair diamond on `unit` with chain-isBi witnesses. -/
example :
    ∃ commonReduct,
      ∃ leftLeg : Step.parStar (Term.unit (context := EmptyCtx))
                    commonReduct,
        Step.parStar.isBi leftLeg ∧
      ∃ rightLeg : Step.parStar (Term.unit (context := EmptyCtx))
                     commonReduct,
        Step.parStar.isBi rightLeg :=
  Step.par.diamond_isBi
    (Step.par.isBi.refl Term.unit)
    (Step.par.isBi.refl Term.unit)

/-! ### `cd_dominates` on structured constructors.

For ground-only structured terms (no β/ι redex), `cd_dominates`
recurses on subterms and rebuilds via the cong rules.  These
exercise the recursive arms in `Term.cd`'s definition. -/

/-- `optionSome boolTrue ⟶par cd (optionSome boolTrue)`. -/
example :
    Step.par
      (Term.optionSome (context := EmptyCtx) (elementType := Ty.bool)
                       Term.boolTrue)
      (Term.cd (Term.optionSome (context := EmptyCtx)
                                (elementType := Ty.bool) Term.boolTrue)) :=
  Step.par.cd_dominates _

/-- `eitherInl boolTrue ⟶par cd (eitherInl boolTrue)`. -/
example :
    Step.par
      (Term.eitherInl
        (context := EmptyCtx) (rightType := Ty.unit) Term.boolTrue)
      (Term.cd
        (Term.eitherInl
          (context := EmptyCtx) (rightType := Ty.unit) Term.boolTrue)) :=
  Step.par.cd_dominates _

/-- `listCons boolTrue listNil ⟶par cd (listCons boolTrue listNil)`. -/
example :
    Step.par
      (Term.listCons (context := EmptyCtx) (elementType := Ty.bool)
        Term.boolTrue Term.listNil)
      (Term.cd
        (Term.listCons (context := EmptyCtx) (elementType := Ty.bool)
          Term.boolTrue Term.listNil)) :=
  Step.par.cd_dominates _

/-! ### `cd_lemma_star` on structured refl chains.

When `Step.par.refl` is annotated with isBi (always available
via `Step.par.isBi.refl`), `cd_lemma_star` produces a parStar
chain landing at `cd source`.  Smoke tests on structured terms
verify the eliminator-cong arms in
`Step.par.cd_lemma_star_with_bi`. -/

/-- Refl on a structured option term yields a parStar chain. -/
example :
    Step.parStar
      (Term.optionSome (context := EmptyCtx) (elementType := Ty.bool)
                       Term.boolTrue)
      (Term.cd (Term.optionSome (context := EmptyCtx)
                                (elementType := Ty.bool) Term.boolTrue)) :=
  Step.par.cd_lemma_star (Step.par.isBi.refl _)

/-- Refl on a structured list term yields a parStar chain. -/
example :
    Step.parStar
      (Term.listCons (context := EmptyCtx) (elementType := Ty.bool)
        Term.boolTrue Term.listNil)
      (Term.cd
        (Term.listCons (context := EmptyCtx) (elementType := Ty.bool)
          Term.boolTrue Term.listNil)) :=
  Step.par.cd_lemma_star (Step.par.isBi.refl _)

/-! ### W8.7 typed-inversion exercises.

`Term.eq_<ctor>_of_toRaw_<ctor>` lemmas recover typed
constructor identity from a `Term.toRaw t = RawTerm.<ctor> ...`
witness.  These smoke tests confirm the inversions discharge the
boolean, nat, list, option, and either ground-constructor
cases. -/

/-- toRaw boolTrue = RawTerm.boolTrue (definitionally). -/
example :
    Term.toRaw (Term.boolTrue (context := EmptyCtx)) = RawTerm.boolTrue :=
  rfl

/-- A typed bool whose toRaw is RawTerm.boolTrue is provably boolTrue. -/
example
    (witness : Term EmptyCtx Ty.bool)
    (rawEq : Term.toRaw witness = RawTerm.boolTrue) :
    witness = Term.boolTrue :=
  Term.eq_boolTrue_of_toRaw_boolTrue witness rawEq

/-- A typed nat whose toRaw is RawTerm.natZero is provably natZero. -/
example
    (witness : Term EmptyCtx Ty.nat)
    (rawEq : Term.toRaw witness = RawTerm.natZero) :
    witness = Term.natZero :=
  Term.eq_natZero_of_toRaw_natZero witness rawEq

/-- A typed list-of-bool whose toRaw is RawTerm.listNil is provably listNil. -/
example
    (witness : Term EmptyCtx (Ty.list Ty.bool))
    (rawEq : Term.toRaw witness = RawTerm.listNil) :
    witness = Term.listNil :=
  Term.eq_listNil_of_toRaw_listNil witness rawEq

/-- A typed option-of-bool whose toRaw is RawTerm.optionNone is
provably optionNone. -/
example
    (witness : Term EmptyCtx (Ty.option Ty.bool))
    (rawEq : Term.toRaw witness = RawTerm.optionNone) :
    witness = Term.optionNone :=
  Term.eq_optionNone_of_toRaw_optionNone witness rawEq

end CdSmokeTest

end LeanFX.Syntax
