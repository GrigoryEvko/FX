import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradeErasure

/-! # FX1Poly/Modal/GradedStrongNormalization — graded SN as the orthogonal-composition corollary

The bespoke usage-dimension strong-normalization corollary: every `HasUsage`-typed term is strongly
normalizing, obtained by GRADE ERASURE — `HasUsage.erase` projects onto the grade-free `HasSimpleType`,
whose STLC Tait result (`HasSimpleType.stronglyNormalizing`, in `GradedFundamentalTheorem`) gives SN
with NO graded-reducibility re-proof.  Kept separate from the shared STLC fundamental theorem so the
latter — and the generic `HasGradeOver R` chain that reuses its STLC-SN — carries no usage-specific
import.

## Zero-axiom verification

Each theorem is a one-line composition through `HasUsage.erase` then `HasSimpleType.stronglyNormalizing`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Graded strong normalization, the orthogonal-composition payoff**: every
`HasUsage`-typed term is strongly normalizing — graded-SN TRANSFERS from STLC-SN through grade erasure
(`HasUsage.erase`) with NO graded-reducibility re-proof, because the term and β-reduction are
grade-AGNOSTIC.  Adding the usage dimension does not require redoing the SN metatheory. -/
theorem HasUsage.stronglyNormalizing {typeContext : List GType} {grades : GradeVector}
    {term : GradedLambda} {resultType : GType}
    (typed : HasUsage typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term :=
  typed.erase.stronglyNormalizing

/-- Smoke: the linear identity `λx. x` is strongly normalizing via the graded transfer (non-vacuous). -/
theorem linearIdentity_stronglyNormalizing :
    GradedLambda.IsStronglyNormalizing (GradedLambda.lam (GradedLambda.var 0)) :=
  linearIdentity_typed.stronglyNormalizing

/-- Smoke: the K combinator `λx. λy. x` is strongly normalizing via the graded transfer. -/
theorem kCombinator_stronglyNormalizing :
    GradedLambda.IsStronglyNormalizing (GradedLambda.lam (GradedLambda.lam (GradedLambda.var 1))) :=
  kCombinator_typed.stronglyNormalizing

end FX1Poly.Modal
