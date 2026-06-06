import FX1Poly.Modal.GradedTyping
import FX1Poly.Modal.SimpleTyping

/-! # FX1Poly/Modal/GradeErasure — grade erasure

The usage dimension is a CONSERVATIVE refinement of simple typing: forget every binder grade and a
well-graded term is just a well-typed term of the underlying simply-typed λ-calculus.  This is the
projection that carries the type dimension's metatheory up to the graded layer — and the bridge for
the orthogonal-composition thesis: graded strong normalization transfers from
STLC strong normalization through this erasure, with NO graded-reducibility re-proof, because the
TERM and the β-reduction are grade-AGNOSTIC (`GradedLambda` carries no grade annotations; the erased
term IS the same `GradedLambda`).

  (`SimpleType` and the grade-free STLC judgment `HasSimpleType` live in `SimpleTyping.lean`, imported
  here.)  This file is the `GType`→STLC erasure bridge:
  * `eraseType : GType → SimpleType` — forget every arrow's binder grade.
  * `HasUsage.erase` — **grade erasure preserves typing**: every `HasUsage`-typed term is
    `HasSimpleType`-typed after forgetting the grades (the grade vector is discarded).  Witnesses
    that the usage dimension PROJECTS onto simple typing — the grades only ADD usage constraints atop
    a well-typed term.  (This is the forward/erasure direction; the converse — that every simply-typed
    term lifts to some grade vector — is not claimed, and is not needed for the SN transfer.)

## Zero-axiom verification

`SimpleType` / `HasSimpleType` are plain inductives; `eraseType` / `SimpleType.lookup` are structural
recursion (NOT the `getElem?` notation, which routes `propext`); `HasUsage.erase` is a direct
induction on the derivation (`HasUsage` is indexed over the plain inductive `GradedLambda`, so cross-
constructor cases discharge via `GradedLambda.noConfusion`).  The var-case lookup uses the explicit
`Option.map`-reducing `rfl` after `rw`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Modal

/-- Grade erasure on types: forget every arrow's binder grade. -/
def eraseType : GType → SimpleType
  | .base => .base
  | .arrow _ domain codomain => .arrow (eraseType domain) (eraseType codomain)

/-- Erasure commutes with context lookup. -/
theorem lookup_map_eraseType :
    ∀ (typeContext : List GType) (index : Nat),
      SimpleType.lookup (typeContext.map eraseType) index =
        (GType.lookup typeContext index).map eraseType
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: restTypes, index + 1 => lookup_map_eraseType restTypes index

/-- **Grade erasure preserves typing**: every `HasUsage`-typed term is `HasSimpleType`-typed after
forgetting the grades (the grade vector `grades` is discarded).  This PROJECTS the graded layer onto
simple typing — the grades only ADD usage constraints atop a well-typed term (forward/erasure
direction only; the converse lift is neither claimed nor needed).  It is the projection that carries
STLC metatheory (SN, …) up to the graded layer. -/
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
