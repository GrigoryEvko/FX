import FX1Poly.Modal.GradedTypingGeneric

/-! # FX1Poly/Modal/SelfApplicationUntypable — self-application is untypable in EVERY graded dimension

The classic occurs-check, mechanized generically: the self-application lambda `λx. x x` has NO typing
derivation in the generic graded engine `HasGradeOver R` (`GradedTypingGeneric.lean`), for ANY ordered
grade semiring `R`.  Typing `x x` would force the binder's type `D` to be its own arrow domain,
`D = (D -(grade)-> codomain)` — impossible, because `GTypeOver R` is a FINITE inductive (`base` /
graded `arrow`) and no term equals a proper subterm of itself.

## Why this is the metatheoretic keystone, not a footnote

The untyped graded λ-calculus diverges: `Ω = (λx. x x)(λx. x x)` is not strongly normalizing
(`UnboundedGrowthNotStronglyNormalizing` / the kernel `RawStepNotStronglyNormalizing`, and the typed
twin `TypedFragmentAcyclicity` #958).  Yet the generic graded TYPING judgment IS strongly normalizing —
that transfers from the type-dimension SN-043 through grade erasure with no SN re-proof
(`GradeErasureGeneric`, #878).  The bridge fact that makes these two consistent is exactly this file:
`λx. x x` is UNTYPABLE.  You never reach `Ω` in the typed calculus because its function part cannot be
typed in the first place — the divergence-enabling term is excluded at the typing layer, by the
occurs-check, BEFORE reduction is ever considered.  This is the graded analogue of "why the
simply-typed λ-calculus normalizes": the only terms that could break SN are precisely the ones the
type discipline rejects.

  * **`gTypeOver_ne_self_arrow`** — the occurs-check core: a graded type is never equal to an arrow
    carrying itself as the domain.  A 6-line structural induction on `GTypeOver R` — the `base` case is
    a constructor clash (`nomatch`), the `arrow` case feeds the domain's induction hypothesis the
    `injection` residual `innerDomain = .arrow … innerDomain …`.
  * **`selfApplicationLambda_untypableOver`** — `λx. x x` has no `HasGradeOver R` derivation in any
    context / grade vector / result type.  Inverts the λ (`invertLam`), the application
    (`invertApp`), and both variable occurrences (`invertVar`); the two `var 0` lookups pin the binder
    type `D` simultaneously to the function's arrow `(D' -> codomain)` and to the argument type `D'`,
    so `D = (D -> codomain)` — refuted by `gTypeOver_ne_self_arrow`.
  * **`omegaCombinator_untypableOver`** — `Ω = (λx. x x)(λx. x x)` is untypable, as a direct corollary:
    its function part is `λx. x x`, which `invertApp` would have to type.
  * **`usageSelfApp_untypable` / `securitySelfApp_untypable`** — instantiations at `fxUsageSemiring`
    and `fxSecuritySemiring`: the SAME occurs-check rejects self-application in the usage dimension and
    the security dimension with no per-dimension proof.  Because the headline is generic over `R`, the
    rejection holds in all twenty-one graded dimensions at once.

## Zero-axiom verification

Structural induction (`GTypeOver` is a plain inductive), `injection` on the arrow constructor,
`nomatch` for the `base`-vs-`arrow` clash, the three shipped inversions (`invertVar` / `invertLam` /
`invertApp`, themselves `cases` + `rfl`), and `Option.some.inj` to read the binder type off the
definitional context lookup `GTypeOver.lookup (D :: Γ) 0 = some D`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (every declaration probed with `#print axioms`
before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **The occurs-check core.**  A graded type is never equal to an arrow that carries the type itself
as its domain: `someType ≠ (someType -(binderGrade)-> codomain)`.  There are no infinite/recursive
graded types — `GTypeOver R` is a finite inductive, so a term cannot equal a proper subterm of itself.
This is the single fact that excludes self-application from the typed calculus. -/
theorem gTypeOver_ne_self_arrow {R : OrderedGradeSemiring} :
    ∀ (someType : GTypeOver R) (binderGrade : R.Carrier) (codomain : GTypeOver R),
      someType ≠ .arrow binderGrade someType codomain := by
  intro someType
  induction someType with
  | base => intro binderGrade codomain selfEq; nomatch selfEq
  | arrow innerGrade innerDomain innerCodomain innerDomainIH _ =>
      intro binderGrade codomain selfEq
      -- selfEq : (innerDomain -> innerCodomain) = (… -> (innerDomain -> innerCodomain) -> codomain);
      -- injection's domain residual is `innerDomain = (innerDomain -> …)`, the IH's self-arrow shape.
      injection selfEq with _ domainEq _
      exact innerDomainIH innerGrade innerCodomain domainEq

/-- **Self-application is untypable.**  `λx. x x` has no `HasGradeOver R` derivation in any context,
grade vector, or result type.  The body's two `x` occurrences force the binder type `D` to be both the
function's arrow `(argumentType -> codomain)` and the argument type `argumentType`; substituting gives
`D = (D -> codomain)`, refuted by `gTypeOver_ne_self_arrow`.  Generic over `R`, hence over every graded
dimension. -/
theorem selfApplicationLambda_untypableOver {R : OrderedGradeSemiring} :
    ¬ ∃ (typeContext : List (GTypeOver R)) (grades : GradeVectorOver R) (resultType : GTypeOver R),
        HasGradeOver R typeContext grades (.lam (.app (.var 0) (.var 0))) resultType := by
  rintro ⟨typeContext, grades, resultType, typed⟩
  obtain ⟨binderGrade, domain, codomain, _, bodyTyped⟩ := HasGradeOver.invertLam typed
  obtain ⟨functionBinderGrade, argumentType, functionGrades, argumentGrades,
    functionTyped, argumentTyped, _⟩ := HasGradeOver.invertApp bodyTyped
  obtain ⟨functionLookup, _⟩ := HasGradeOver.invertVar functionTyped
  obtain ⟨argumentLookup, _⟩ := HasGradeOver.invertVar argumentTyped
  -- `GTypeOver.lookup (domain :: typeContext) 0` is `some domain` definitionally.
  have functionEq : domain = .arrow functionBinderGrade argumentType codomain :=
    Option.some.inj functionLookup
  have argumentEq : domain = argumentType := Option.some.inj argumentLookup
  rw [← argumentEq] at functionEq
  exact gTypeOver_ne_self_arrow domain functionBinderGrade codomain functionEq

/-- **The omega combinator is untypable.**  `Ω = (λx. x x)(λx. x x)` — the canonical non-terminating
term — has no `HasGradeOver R` derivation: `invertApp` exposes a typing of its function part
`λx. x x`, which `selfApplicationLambda_untypableOver` refutes.  This is precisely why the typed graded
calculus stays strongly normalizing despite `Ω` diverging in the untyped one (#950/#960). -/
theorem omegaCombinator_untypableOver {R : OrderedGradeSemiring} :
    ¬ ∃ (typeContext : List (GTypeOver R)) (grades : GradeVectorOver R) (resultType : GTypeOver R),
        HasGradeOver R typeContext grades
          (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))) resultType := by
  rintro ⟨typeContext, grades, resultType, typed⟩
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, _, _⟩ :=
    HasGradeOver.invertApp typed
  exact selfApplicationLambda_untypableOver
    ⟨typeContext, functionGrades, .arrow binderGrade domain resultType, functionTyped⟩

/-- Usage-dimension instantiation: `λx. x x` is untypable at `fxUsageSemiring`.  The occurs-check is
dimension-blind — the generic headline specialized, no new proof. -/
theorem usageSelfApp_untypable :
    ¬ ∃ (typeContext : List (GTypeOver fxUsageSemiring)) (grades : GradeVectorOver fxUsageSemiring)
        (resultType : GTypeOver fxUsageSemiring),
        HasGradeOver fxUsageSemiring typeContext grades (.lam (.app (.var 0) (.var 0))) resultType :=
  selfApplicationLambda_untypableOver

/-- Security-dimension instantiation: `λx. x x` is untypable at `fxSecuritySemiring` — the SAME
occurs-check rejects self-application in a second graded dimension, with no per-dimension proof.  The
orthogonal-composition thesis at the untypability layer. -/
theorem securitySelfApp_untypable :
    ¬ ∃ (typeContext : List (GTypeOver fxSecuritySemiring))
        (grades : GradeVectorOver fxSecuritySemiring) (resultType : GTypeOver fxSecuritySemiring),
        HasGradeOver fxSecuritySemiring typeContext grades (.lam (.app (.var 0) (.var 0)))
          resultType :=
  selfApplicationLambda_untypableOver

end FX1Poly.Modal
