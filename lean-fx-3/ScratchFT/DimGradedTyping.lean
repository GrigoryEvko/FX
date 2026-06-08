import FX1Poly.Modal.UsageDiscipline

/-! Scratch probe: the SOUND graded typing judgment (BGMZ / co-effect graded STLC).  The binder
grade lives in the arrow type; the App rule scales the argument's grades by it.  This is the typed
judgment that AVOIDS the naive occurrence check's subject-reduction failure (the `(λx. x x) g`
counterexample is untypable here — self-application needs an infinite type). -/

namespace FX1Poly.Modal

/-- Graded simple types: a base type and a graded arrow `dom -(binderGrade)-> cod`, where
`binderGrade` records how many times the function uses its argument (the §6.1 usage grade). -/
inductive GType where
  | base : GType
  | arrow : UsageGrade → GType → GType → GType
  deriving DecidableEq, Repr

/-- Look up a variable's type in the context (propext-free structural recursion — the `l[i]?`
notation's `getElem?` routes through `propext`). -/
def GType.lookup : List GType → Nat → Option GType
  | [], _ => none
  | headType :: _, 0 => some headType
  | _ :: restTypes, position + 1 => GType.lookup restTypes position

/-- The sound graded typing-and-usage judgment `Γ ⊢_p t : T`: in type context `Γ` (a list of
types), term `t` has type `T` and uses the bindings with grade vector `p`.  The grades track usage
EXACTLY because App scales the argument by the function's binder grade — this is what the naive
occurrence check omitted. -/
inductive HasUsage : List GType → GradeVector → GradedLambda → GType → Prop where
  | var (typeContext : List GType) (index : Nat) (varType : GType)
      (lookupOk : GType.lookup typeContext index = some varType) :
      HasUsage typeContext (GradeVector.single typeContext.length index UsageGrade.one)
        (.var index) varType
  | lam (typeContext : List GType) (binderGrade : UsageGrade) (domain codomain : GType)
      (outerGrades : GradeVector) (body : GradedLambda)
      (bodyTyped : HasUsage (domain :: typeContext) (GradeVector.cons binderGrade outerGrades)
        body codomain) :
      HasUsage typeContext outerGrades (.lam body) (.arrow binderGrade domain codomain)
  | app (typeContext : List GType) (binderGrade : UsageGrade) (domain codomain : GType)
      (functionGrades argumentGrades : GradeVector) (function argument : GradedLambda)
      (functionTyped : HasUsage typeContext functionGrades function
        (.arrow binderGrade domain codomain))
      (argumentTyped : HasUsage typeContext argumentGrades argument domain) :
      HasUsage typeContext
        (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades))
        (.app function argument) codomain

/-- **The linear identity types with arrow grade `1`.**  `λx. x : base -(1)-> base` in the empty
context, using no outer bindings (`nil`): `x` is used exactly once, so the arrow records grade `1`. -/
theorem linearIdentity_typed :
    HasUsage [] GradeVector.nil (.lam (.var 0)) (.arrow UsageGrade.one GType.base GType.base) :=
  HasUsage.lam [] UsageGrade.one GType.base GType.base GradeVector.nil (.var 0)
    (HasUsage.var [GType.base] 0 GType.base rfl)

/-- **The K combinator's grades exactly track usage.**  `λx. λy. x : base -(1)-> (base -(0)-> base)`:
`x` is used once (binder grade `1`), `y` is dropped (binder grade `0`).  The grade discipline reads
linearity and discarding straight off the arrow grades. -/
theorem kCombinator_typed :
    HasUsage [] GradeVector.nil (.lam (.lam (.var 1)))
      (.arrow UsageGrade.one GType.base (.arrow UsageGrade.zero GType.base GType.base)) :=
  HasUsage.lam [] UsageGrade.one GType.base (.arrow UsageGrade.zero GType.base GType.base)
    GradeVector.nil (.lam (.var 1))
    (HasUsage.lam [GType.base] UsageGrade.zero GType.base GType.base
      (GradeVector.cons UsageGrade.one GradeVector.nil) (.var 1)
      (HasUsage.var [GType.base, GType.base] 1 GType.base rfl))

#print axioms GType
#print axioms HasUsage
#print axioms linearIdentity_typed
#print axioms kCombinator_typed

end FX1Poly.Modal
