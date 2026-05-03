import LeanFX2.Algo.Infer

/-! # Phase 12.A.3 audit: Term.infer extensions for listCons + optionSome

The base `Term.infer` was extended (this commit) to cover two
parametric ctors whose payload determines the element type:

* `RawTerm.listCons headRaw tailRaw` — head's inferred type
  determines the listType element
* `RawTerm.optionSome valueRaw` — value's inferred type
  determines the option element

Both new cases preserve type-soundness-by-construction (no
additional theorem needed; Lean's return type pins the result).

This file exercises the new branches on concrete examples + audits
that `Term.infer` remains zero-axiom under the strict policy. -/

#print axioms LeanFX2.Term.infer

namespace LeanFX2.Smoke

open LeanFX2

/-- `optionSome natZero` infers `optionType nat`. -/
example :
    Term.infer (Ctx.empty (level := 0) (mode := Mode.software))
                (RawTerm.optionSome RawTerm.natZero)
      = some ⟨Ty.optionType Ty.nat, Term.optionSome Term.natZero⟩ := rfl

/-- `optionSome boolTrue` infers `optionType bool`. -/
example :
    Term.infer (Ctx.empty (level := 0) (mode := Mode.software))
                (RawTerm.optionSome RawTerm.boolTrue)
      = some ⟨Ty.optionType Ty.bool, Term.optionSome Term.boolTrue⟩ := rfl

/-- Nested `optionSome (optionSome unit)` infers
`optionType (optionType unit)`. -/
example :
    Term.infer (Ctx.empty (level := 0) (mode := Mode.software))
                (RawTerm.optionSome (RawTerm.optionSome RawTerm.unit))
      = some ⟨Ty.optionType (Ty.optionType Ty.unit),
              Term.optionSome (Term.optionSome Term.unit)⟩ := rfl

end LeanFX2.Smoke
