import FX1Poly.Modal.GradedTyping

/-! # FX1Poly/Modal/GradeErasure — grade erasure (DIM2-4)

The usage dimension is a CONSERVATIVE refinement of simple typing: forget every binder grade and a
well-graded term is just a well-typed term of the underlying simply-typed λ-calculus.  This is the
projection that carries the type dimension's metatheory up to the graded layer — and the bridge for
the orthogonal-composition thesis (DIM2-5 / SN-056): graded strong normalization will transfer from
STLC strong normalization through this erasure, with NO graded-reducibility re-proof, because the
TERM and the β-reduction are grade-AGNOSTIC (`GradedLambda` carries no grade annotations; the erased
term IS the same `GradedLambda`).

  * `SimpleType` — grade-free simple types (the type dimension beneath `GType`; the arrow drops its
    §6.1 binder grade).
  * `eraseType : GType → SimpleType` — forget every arrow's binder grade.
  * `HasSimpleType` — the grade-free STLC judgment over the same `GradedLambda` terms.
  * `HasUsage.erase` — **grade erasure preserves typing**: every `HasUsage`-typed term is
    `HasSimpleType`-typed after forgetting the grades (the grade vector is discarded).  Witnesses
    that the usage dimension never changes what is *typable*; it only adds usage constraints.

## Zero-axiom verification

`SimpleType` / `HasSimpleType` are plain inductives; `eraseType` / `SimpleType.lookup` are structural
recursion (NOT the `getElem?` notation, which routes `propext`); `HasUsage.erase` is a direct
induction on the derivation (`HasUsage` is indexed over the plain inductive `GradedLambda`, so cross-
constructor cases discharge via `GradedLambda.noConfusion`).  The var-case lookup uses the explicit
`Option.map`-reducing `rfl` after `rw`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Modal

/-- Grade-free simple types: the type dimension underneath `GType` (the arrow drops its binder grade). -/
inductive SimpleType where
  | base : SimpleType
  | arrow : SimpleType → SimpleType → SimpleType
  deriving DecidableEq, Repr

/-- Grade erasure on types: forget every arrow's binder grade. -/
def eraseType : GType → SimpleType
  | .base => .base
  | .arrow _ domain codomain => .arrow (eraseType domain) (eraseType codomain)

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

/-- Erasure commutes with context lookup. -/
theorem lookup_map_eraseType :
    ∀ (typeContext : List GType) (index : Nat),
      SimpleType.lookup (typeContext.map eraseType) index =
        (GType.lookup typeContext index).map eraseType
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: restTypes, index + 1 => lookup_map_eraseType restTypes index

/-- **Grade erasure preserves typing**: every `HasUsage`-typed term is `HasSimpleType`-typed after
forgetting the grades (the grade vector `grades` is discarded).  Witnesses that the usage dimension
is a conservative refinement — it adds usage constraints atop simple typing, never changes what is
typable.  This is the projection that carries STLC metatheory (SN, …) up to the graded layer
(DIM2-5 / SN-056). -/
theorem HasUsage.erase {typeContext : List GType} {grades : GradeVector} {term : GradedLambda}
    {resultType : GType} (typed : HasUsage typeContext grades term resultType) :
    HasSimpleType (typeContext.map eraseType) term (eraseType resultType) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      exact HasSimpleType.var (typeContext.map eraseType) index (eraseType varType)
        (by rw [lookup_map_eraseType typeContext index, lookupOk]; rfl)
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      exact HasSimpleType.lam (typeContext.map eraseType) (eraseType domain) (eraseType codomain)
        body bodyIH
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _ _ functionIH argumentIH =>
      exact HasSimpleType.app (typeContext.map eraseType) (eraseType domain) (eraseType codomain)
        function argument functionIH argumentIH

/-- The linear identity erases to the simply-typed identity (smoke witness). -/
theorem linearIdentity_erases :
    HasSimpleType [] (.lam (.var 0)) (.arrow SimpleType.base SimpleType.base) :=
  linearIdentity_typed.erase

end FX1Poly.Modal
