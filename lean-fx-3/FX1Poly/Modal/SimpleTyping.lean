import FX1Poly.Modal.GradedLambdaTerm

/-! # FX1Poly/Modal/SimpleTyping — the grade-free STLC typing over the shared GradedLambda carrier

`SimpleType` (grade-free simple types) and the simple-typing judgment `HasSimpleType` over the shared
`GradedLambda` carrier — the type dimension that the usage dimension (and every other graded dimension)
refines.  Carrying it in its own module keeps the STLC strong-normalization substrate free of any
usage-specific import: the grade-ERASURE bridge (`eraseType : GType → SimpleType`, `HasUsage.erase`)
stays in `GradeErasure.lean`, which imports this module.

## Zero-axiom verification

A grade-free inductive `SimpleType`, a structural-recursion context `lookup` (avoiding the `getElem?`
notation, which routes `propext`), and the three-rule simple-typing judgment `HasSimpleType` over
`GradedLambda`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Grade-free simple types: the type dimension underneath `GType` (the arrow drops its binder grade). -/
inductive SimpleType where
  | base : SimpleType
  | arrow : SimpleType → SimpleType → SimpleType
  deriving DecidableEq, Repr

/-- Context lookup for simple types (structural recursion, propext-free — same care as `GType.lookup`). -/
def SimpleType.lookup : List SimpleType → Nat → Option SimpleType
  | [], _ => none
  | headType :: _, 0 => some headType
  | _ :: restTypes, position + 1 => SimpleType.lookup restTypes position

/-- **The grade-free STLC judgment** over the same `GradedLambda` terms — the type dimension that the
usage dimension refines. -/
inductive HasSimpleType : List SimpleType → GradedLambda → SimpleType → Prop where
  | var (typeContext : List SimpleType) (index : Nat) (varType : SimpleType)
      (lookupOk : SimpleType.lookup typeContext index = some varType) :
      HasSimpleType typeContext (.var index) varType
  | lam (typeContext : List SimpleType) (domain codomain : SimpleType) (body : GradedLambda)
      (bodyTyped : HasSimpleType (domain :: typeContext) body codomain) :
      HasSimpleType typeContext (.lam body) (.arrow domain codomain)
  | app (typeContext : List SimpleType) (domain codomain : SimpleType) (function argument : GradedLambda)
      (functionTyped : HasSimpleType typeContext function (.arrow domain codomain))
      (argumentTyped : HasSimpleType typeContext argument domain) :
      HasSimpleType typeContext (.app function argument) codomain

end FX1Poly.Modal
