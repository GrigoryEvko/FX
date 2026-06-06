import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradedFundamentalTheorem

/-! # FX1Poly/Modal/GradeErasureGeneric — generic grade erasure + SN-transfer (DIM5-4 + dims 6–21)

The usage dimension's erasure (`GradeErasure.lean`, DIM2-4) is hardcoded to `GType` / `HasUsage`; the
SN-transfer (`GradedFundamentalTheorem.lean`, DIM2-5 / SN-056) is hardcoded to `HasUsage`.  But the
projection is the SAME for every dimension: forget the binder grades and a well-graded term is just a
well-typed term of the underlying grade-free STLC, whose strong normalization is already proved (the
Tait fundamental theorem, `HasSimpleType.stronglyNormalizing`).  This file ships that projection ONCE,
generic over any `OrderedGradeSemiring`, from the DIM5-3 generic judgment `HasGradeOver R`.

  * `eraseGTypeOver : GTypeOver R → SimpleType` — forget every arrow's binder grade.  The output type
    is grade-FREE (`SimpleType`, shared with DIM2-4), so it does not mention `R` — every dimension's
    graded types erase into the SAME simple-type system.
  * `HasGradeOver.erase` — grade erasure preserves typing: every `HasGradeOver R`-typed term is
    `HasSimpleType`-typed after forgetting the grades.  The generically-graded layer PROJECTS onto the
    SAME grade-free STLC that the usage dimension projects onto (`HasUsage.erase`); the grades only ADD
    constraints atop a well-typed term (forward/erasure direction only — the converse lift is neither
    claimed nor needed).
  * `HasGradeOver.stronglyNormalizing` — **THE headline.**  For ANY ordered semiring `R`, a well-graded
    term is β-strongly-normalizing, obtained by erasing to STLC and invoking the shipped
    `HasSimpleType.stronglyNormalizing` — NO graded-reducibility re-proof.  This is the
    orthogonal-composition thesis (DIM2-7 / SN-056) at the JUDGMENT layer, for ALL 21 dimensions at
    once: SN survives grade erasure regardless of which dimension `R` is, because the term and its
    β-reduction are grade-AGNOSTIC (the erased term IS the same `GradedLambda`).

The witnesses instantiate the SN-transfer at the usage dimension (generic, any `R`) and at the security
dimension (`fxSecuritySemiring`): the linear identity and the K combinator are β-SN as graded terms in a
SECOND dimension, with no per-dimension SN proof.

## Zero-axiom verification

`eraseGTypeOver` / `lookup_map_eraseGTypeOver` are structural recursion; `HasGradeOver.erase` is a direct
induction on the derivation (`HasGradeOver` is indexed over the plain inductive `GradedLambda`, so cross-
constructor cases discharge via `GradedLambda.noConfusion`); the var-case lookup uses the explicit
`Option.map`-reducing `rfl` after `rw`; the SN-transfer is a one-line composition.  No semiring law is
used — erasure drops grades and β-SN is grade-agnostic, so the brick is lawfulness-FREE.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (probed with `#print axioms`
before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Grade erasure on generic graded types: forget every arrow's binder grade.  The output `SimpleType`
is grade-FREE and `R`-independent — every dimension's graded types erase into the SAME simple types
(the shared `SimpleType` of DIM2-4). -/
def eraseGTypeOver {R : OrderedGradeSemiring} : GTypeOver R → SimpleType
  | .base => .base
  | .arrow _ domain codomain => .arrow (eraseGTypeOver domain) (eraseGTypeOver codomain)

/-- Erasure commutes with context lookup (generic over `R`; structural, propext-free). -/
theorem lookup_map_eraseGTypeOver {R : OrderedGradeSemiring} :
    ∀ (typeContext : List (GTypeOver R)) (index : Nat),
      SimpleType.lookup (typeContext.map eraseGTypeOver) index =
        (GTypeOver.lookup typeContext index).map eraseGTypeOver
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: restTypes, index + 1 => lookup_map_eraseGTypeOver restTypes index

/-- **Grade erasure preserves typing**: every `HasGradeOver R`-typed term is `HasSimpleType`-typed after
forgetting the grades (the grade vector is discarded).  The generically-graded layer PROJECTS onto the
SAME grade-free STLC the usage dimension projects onto — the grades only ADD constraints atop a
well-typed term (forward/erasure direction only; the converse lift is neither claimed nor needed).  It
is the projection that carries STLC strong normalization up to the graded layer for ANY dimension. -/
theorem HasGradeOver.erase {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) :
    HasSimpleType (typeContext.map eraseGTypeOver) term (eraseGTypeOver resultType) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      exact HasSimpleType.var (typeContext.map eraseGTypeOver) index (eraseGTypeOver varType)
        (by rw [lookup_map_eraseGTypeOver typeContext index, lookupOk]; rfl)
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      exact HasSimpleType.lam (typeContext.map eraseGTypeOver) (eraseGTypeOver domain)
        (eraseGTypeOver codomain) body bodyIH
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _ _ functionIH argumentIH =>
      exact HasSimpleType.app (typeContext.map eraseGTypeOver) (eraseGTypeOver domain)
        (eraseGTypeOver codomain) function argument functionIH argumentIH

/-- **The generic SN-transfer (DIM5-4 / generic SN-056).**  For ANY ordered semiring `R`, a well-graded
term (in the generic judgment `HasGradeOver R`) is β-strongly-normalizing — obtained by erasing to STLC
(`HasGradeOver.erase`) and invoking the shipped Tait SN (`HasSimpleType.stronglyNormalizing`), with NO
graded-reducibility re-proof.  The orthogonal-composition thesis at the JUDGMENT layer, for ALL 21
dimensions at once: SN survives grade erasure regardless of which dimension `R` is, because the term and
its β-reduction are grade-AGNOSTIC. -/
theorem HasGradeOver.stronglyNormalizing {R : OrderedGradeSemiring}
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R} {term : GradedLambda}
    {resultType : GTypeOver R} (typed : HasGradeOver R typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term :=
  typed.erase.stronglyNormalizing

/-! ## Witnesses — the SN-transfer fires in a SECOND dimension with no per-dimension proof -/

/-- The linear identity is β-SN as a graded term in ANY dimension (generic over `R`). -/
theorem linearIdentityOver_stronglyNormalizing (R : OrderedGradeSemiring) :
    GradedLambda.IsStronglyNormalizing (.lam (.var 0)) :=
  (linearIdentityOver_typed R).stronglyNormalizing

/-- **DIM5-4: the security dimension's identity is β-SN via the shared transfer.**  No security-specific
SN proof — `securityLinearIdentity_typedViaGeneric` (DIM5-3) fed through `HasGradeOver.stronglyNormalizing`. -/
theorem securityLinearIdentity_stronglyNormalizingViaGeneric :
    GradedLambda.IsStronglyNormalizing (.lam (.var 0)) :=
  securityLinearIdentity_typedViaGeneric.stronglyNormalizing

/-- DIM5-4: the security dimension's K combinator is β-SN via the shared transfer (a second
second-dimension SN witness, again with no per-dimension proof). -/
theorem securityKCombinator_stronglyNormalizingViaGeneric :
    GradedLambda.IsStronglyNormalizing (.lam (.lam (.var 1))) :=
  securityKCombinator_typedViaGeneric.stronglyNormalizing

end FX1Poly.Modal
