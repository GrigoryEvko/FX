import LeanFX2.Graded.Rules
import LeanFX2.Term.ToRaw

/-! # Graded/Term — shadow graded wrapper over typed Terms

This module starts the load-bearing bridge from the D5.4 graded rule
algebra to the real typed `Term` kernel without refactoring `Term`'s
indices.  A `GradedTerm` carries:

* a `GradedCtx`;
* the erased typed `Term` over that context's underlying `Ctx`;
* a `GradeAttribution` index recording the term's per-binding usage.

Constructors require the matching graded compatibility predicate, but the
underlying computational content remains the existing typed `Term`.
This is intentionally a shadow layer: it does not yet make all typed
`Term` constructors grade-indexed. -/

namespace LeanFX2.Graded

/-- Erase a graded context to the kernel's ordinary typed context. -/
def GradedCtx.toCtx :
    ∀ {mode : Mode} {level : Nat} {dimensions : List Dimension} {scope : Nat},
      GradedCtx mode level dimensions scope →
      Ctx mode level scope
  | mode, level, _, _, .empty => Ctx.empty (mode := mode) (level := level)
  | _, _, _, _, .cons rest binding =>
      Ctx.cons (GradedCtx.toCtx rest) binding.bindingTy

/-- A graded term shadows a real typed `Term` and pins a grade
attribution to it.  The grade attribution is an index, not a loose field,
so later rules can refine it by construction. -/
structure GradedTerm {mode : Mode} {level scope : Nat}
    {dimensions : List Dimension}
    (gradedCtx : GradedCtx mode level dimensions scope)
    (termTy : Ty level scope)
    (rawTerm : RawTerm scope)
    (attribution : GradeAttribution dimensions scope) where
  /-- The actual kernel term over the grade-erased context. -/
  underlying : Term (GradedCtx.toCtx gradedCtx) termTy rawTerm

namespace GradedTerm

variable {mode : Mode} {level scope : Nat} {dimensions : List Dimension}
variable {gradedCtx : GradedCtx mode level dimensions scope}

/-- Unit uses no bindings. -/
def unit :
    GradedTerm gradedCtx Ty.unit RawTerm.unit GradeAttribution.zero where
  underlying := Term.unit

/-- Boolean true uses no bindings. -/
def boolTrue :
    GradedTerm gradedCtx Ty.bool RawTerm.boolTrue GradeAttribution.zero where
  underlying := Term.boolTrue

/-- Boolean false uses no bindings. -/
def boolFalse :
    GradedTerm gradedCtx Ty.bool RawTerm.boolFalse GradeAttribution.zero where
  underlying := Term.boolFalse

/-- A variable has the singleton attribution at its de Bruijn position. -/
def var (position : Fin scope) :
    GradedTerm gradedCtx
      (varType (GradedCtx.toCtx gradedCtx) position)
      (RawTerm.var position)
      (GradeAttribution.singleton position) where
  underlying := Term.var position

/-- Lambda introduction, guarded by the corrected Wood/Atkey Lam rule.

The body is checked in the graded context extended by the parameter grade.
The result attribution is the `lamAttr` witness accepted by
`IsLamCompatible`. -/
def lam
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {paramGrade closureGrade : GradeVector dimensions}
    {bodyAttr : GradeAttribution dimensions (scope + 1)}
    {lamAttr : GradeAttribution dimensions scope}
    (body :
      GradedTerm
        (GradedCtx.cons gradedCtx
          { bindingTy := domainType, grade := paramGrade })
        codomainType.weaken
        bodyRaw
        bodyAttr)
    (_compat :
      IsLamCompatible paramGrade closureGrade bodyAttr lamAttr) :
    GradedTerm gradedCtx
      (Ty.arrow domainType codomainType)
      (RawTerm.lam bodyRaw)
      lamAttr where
  underlying := Term.lam body.underlying

/-- Application, guarded by the graded App rule. -/
def app
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionAttr argumentAttr resultAttr : GradeAttribution dimensions scope}
    (paramGrade : GradeVector dimensions)
    (functionTerm :
      GradedTerm gradedCtx
        (Ty.arrow domainType codomainType)
        functionRaw
        functionAttr)
    (argumentTerm :
      GradedTerm gradedCtx domainType argumentRaw argumentAttr)
    (_compat :
      IsAppCompatible paramGrade functionAttr argumentAttr resultAttr) :
    GradedTerm gradedCtx
      codomainType
      (RawTerm.app functionRaw argumentRaw)
      resultAttr where
  underlying := Term.app functionTerm.underlying argumentTerm.underlying

/-- Boolean eliminator, guarded by the If/Match grade rule. -/
def boolElim
    {motiveType : Ty level scope}
    {conditionRaw thenRaw elseRaw : RawTerm scope}
    {conditionAttr thenAttr elseAttr resultAttr :
      GradeAttribution dimensions scope}
    (conditionTerm :
      GradedTerm gradedCtx Ty.bool conditionRaw conditionAttr)
    (thenTerm :
      GradedTerm gradedCtx motiveType thenRaw thenAttr)
    (elseTerm :
      GradedTerm gradedCtx motiveType elseRaw elseAttr)
    (_compat :
      IsIfCompatible conditionAttr thenAttr elseAttr resultAttr) :
    GradedTerm gradedCtx
      motiveType
      (RawTerm.boolElim conditionRaw thenRaw elseRaw)
      resultAttr where
  underlying :=
    Term.boolElim
      conditionTerm.underlying
      thenTerm.underlying
      elseTerm.underlying

/-- Grade-only subsumption: widen a term's attribution without changing
the underlying typed term. -/
def subsumeGrade
    {termTy : Ty level scope}
    {rawTerm : RawTerm scope}
    {tightAttr looseAttr : GradeAttribution dimensions scope}
    (someTerm : GradedTerm gradedCtx termTy rawTerm tightAttr)
    (_compat : IsSubsumptionCompatible tightAttr looseAttr) :
    GradedTerm gradedCtx termTy rawTerm looseAttr where
  underlying := someTerm.underlying

/-- The underlying typed term erases to the same raw term carried by the
graded wrapper's index. -/
theorem underlying_toRaw
    {termTy : Ty level scope}
    {rawTerm : RawTerm scope}
    {attribution : GradeAttribution dimensions scope}
    (someTerm : GradedTerm gradedCtx termTy rawTerm attribution) :
    Term.toRaw someTerm.underlying = rawTerm := rfl

end GradedTerm

/-! ## Smoke samples -/

example {mode : Mode} {level : Nat} {dimensions : List Dimension} :
    GradedCtx.toCtx
      (GradedCtx.empty
        (mode := mode) (level := level) (dimensions := dimensions))
      = Ctx.empty (mode := mode) (level := level) := rfl

end LeanFX2.Graded
