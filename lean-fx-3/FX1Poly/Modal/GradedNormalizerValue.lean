import FX1Poly.Modal.GradedEvaluation

/-! # FX1Poly/Modal/GradedNormalizerValue — the verified normalizer evaluates well-typed terms to values

The executable payoff of the graded type-safety story.  Firing-prior work established PRESERVATION
(`hasGradeOver_betaPreservation` + full-β `hasGradeOver_reducesPreservation`), PROGRESS / canonical forms
(`closedWellTypedProgress` / `closedNormalFormIsLam`), TERMINATION (`HasGradeOver.stronglyNormalizing`),
and the abstract EVALUATION theorem (`closedReducesToLam`: SOME reduction reaches a `.lam`).  This file
sharpens evaluation to the ACTUAL computed output of the verified `GradedLambda.normalize` function:

  **`normalize` maps every closed well-typed term to a `.lam` value** (`closedNormalizesToLam`).

`normalize` is the SN-driven β-normalizer (`GradedNormalization.lean`, total on strongly-normalizing
terms).  Its output is reached (`normalize_reducesStar`) and irreducible (`normalize_isNormalForm`);
full-β subject reduction retypes it (still closed and well-typed) and canonical forms makes it a `.lam`.
So the COMPUTER actually evaluates a closed well-typed program to a λ-value — not merely "some reduction
sequence would".

  * **`closedNormalizesToLam`** — `normalize term sn` is a `.lam` for any closed well-typed `term`.
  * **`closedConvertibleSameValue`** — typed evaluation DETERMINISM: a closed well-typed term and any SN
    term convertible to it normalize to the SAME `.lam` value.  Only one side needs typing — the value
    propagates through convertibility via `joinable_iff_normalize_eq` (convertible SN terms share a
    normal form).
  * **`usageClosedNormalizesToLam` / `securityClosedNormalizesToLam`** — the orthogonal-composition
    thesis at the evaluation layer: the SAME `normalize` evaluates the linear identity to a value in
    BOTH the usage and security dimensions, with no per-dimension proof (the generic theorem
    instantiated at `fxUsageSemiring` and `fxSecuritySemiring`).

## Zero-axiom verification

`closedNormalizesToLam` composes `normalize_reducesStar` / `normalize_isNormalForm` with the firing-prior
`hasGradeOver_reducesStarPreservation` (full-β SR) and `closedNormalFormIsLam` (canonical forms); the
determinism corollary adds `joinable_iff_normalize_eq`; the smokes are instantiations.  The
`IsNormalForm` value must be type-annotated to stop Lean eagerly instantiating its `∀ {reduct}` binder.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (every declaration
probed with `#print axioms` before landing).  Per-declaration audit-gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (Joinable)

/-- **The verified normalizer computes a value.**  `normalize` of a closed well-typed `HasGradeOver R`
term is a `.lam`.  (Firing-108 `closedReducesToLam` gave "SOME reduction reaches a λ"; this characterizes
the actual computed normal form of the executable `normalize`.)  `normalize_reducesStar` reaches the
output, full-β SR (`hasGradeOver_reducesStarPreservation`) retypes it, and canonical forms
(`closedNormalFormIsLam`) makes it a `.lam`. -/
theorem closedNormalizesToLam {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    ∃ body, GradedLambda.normalize term sn = .lam body := by
  have reachedStar := GradedLambda.normalize_reducesStar term sn
  have resultNormal : GradedLambda.IsNormalForm (GradedLambda.normalize term sn) :=
    GradedLambda.normalize_isNormalForm term sn
  have resultTyped := hasGradeOver_reducesStarPreservation lawful reachedStar typed
  exact closedNormalFormIsLam (GradedLambda.normalize term sn) resultTyped resultNormal

/-- **Typed evaluation determinism.**  A closed well-typed term and any SN term CONVERTIBLE to it
normalize to the SAME `.lam` value.  Only ONE side needs typing — the value-ness propagates through
convertibility: `closedNormalizesToLam` makes the left a λ, and `joinable_iff_normalize_eq` (convertible
SN terms have equal normal forms) carries it to the right. -/
theorem closedConvertibleSameValue {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {gradesLeft : GradeVectorOver R} {termLeft termRight : GradedLambda} {typeLeft : GTypeOver R}
    (typedLeft : HasGradeOver R [] gradesLeft termLeft typeLeft)
    (snLeft : GradedLambda.IsStronglyNormalizing termLeft)
    (snRight : GradedLambda.IsStronglyNormalizing termRight)
    (convertible : Joinable GradedLambda.Reduces termLeft termRight) :
    ∃ body, GradedLambda.normalize termLeft snLeft = .lam body ∧
      GradedLambda.normalize termRight snRight = .lam body := by
  obtain ⟨body, leftEq⟩ := closedNormalizesToLam lawful typedLeft snLeft
  refine ⟨body, leftEq, ?_⟩
  rw [← (GradedLambda.joinable_iff_normalize_eq snLeft snRight).mp convertible]
  exact leftEq

/-- Usage-dimension smoke: the normalizer evaluates the linear identity `λx.x` to a `.lam`. -/
theorem usageClosedNormalizesToLam :
    ∃ body, GradedLambda.normalize (.lam (.var 0))
      (linearIdentityOver_stronglyNormalizing fxUsageSemiring) = .lam body :=
  closedNormalizesToLam fxUsageSemiring_isLawful usageLinearIdentity_typedViaGeneric
    (linearIdentityOver_stronglyNormalizing fxUsageSemiring)

/-- Security-dimension smoke: the SAME normalizer evaluates the security-typed linear identity to a
`.lam` — the orthogonal-composition thesis at the evaluation layer, no per-dimension proof. -/
theorem securityClosedNormalizesToLam :
    ∃ body, GradedLambda.normalize (.lam (.var 0))
      (linearIdentityOver_stronglyNormalizing fxSecuritySemiring) = .lam body :=
  closedNormalizesToLam fxSecuritySemiring_isLawful securityLinearIdentity_typedViaGeneric
    (linearIdentityOver_stronglyNormalizing fxSecuritySemiring)

end FX1Poly.Modal
