import FX1Poly.Modal.GradeSemiringProduct

/-! # FX1Poly/Modal/GradeSemiringFunctorial
    — `HasGradeOver` is FUNCTORIAL along grade-semiring homomorphisms; a multi-dimension derivation PROJECTS
      to each factor dimension (the §6 "dimensions are checked independently / compose pointwise" content)

DIM-PRODUCT (#1035) composes two grade dimensions into one `OrderedGradeSemiring.product`, and DIM-PRODUCT-
MONOIDAL (#1036) showed the product is symmetric monoidal.  This file supplies the OTHER half of §6's "the
dimensions compose pointwise on the grade vector": a graded typing derivation in the COMPOSITE dimension
DECOMPOSES into derivations in each FACTOR dimension — the formal statement that the dimensions are checked
INDEPENDENTLY.

The clean way to state it is functoriality.  A grade-semiring HOMOMORPHISM `f : R.Carrier → S.Carrier`
(preserving `zero`/`one`/`add`/`mul`) induces a map on graded types and grade vectors, and lifts the entire
typing judgment:

  * **`GTypeOver.mapGrade f` / `GradeVectorOver.mapGrade f`** — push every grade through `f` (structural
    recursion).  Commutation lemmas: `mapGrade f` commutes with `zero` / `single` (given `f` preserves
    `R.zero`), with `add` (given `f` is additive), and with `scale` (given `f` is multiplicative).
    `GTypeOver.lookup_map` commutes context lookup with the type map.

  * **`HasGradeOver.mapHom` (★, the functoriality theorem)** — given `f` preserves `zero`/`one`/`add`/`mul`,
    every derivation `HasGradeOver R Γ p t T` maps to `HasGradeOver S (Γ.map (mapGrade f)) (p.mapGrade f) t
    (mapGrade f T)`.  Induction on the derivation: the `var` arm uses the `single`-commutation + `f R.one =
    S.one` + `lookup_map`; the `lam` arm reassembles under the binder; the `app` arm uses the `add`- and
    `scale`-commutations on the App-rule grade `p1 + r·p2`.  `HasGradeOver` is a functor on the category of
    grade semirings.

  * **`HasGradeOver.projectFirst` / `projectSecond`** — the two product projections `Prod.fst` / `Prod.snd`
    are grade-semiring homomorphisms (every preservation law is `rfl`, since the product is componentwise),
    so a derivation in `product A B` projects to a derivation in `A` AND a derivation in `B`.  This is the
    "dimensions are checked independently" theorem: the usage and security (etc.) checks of a composite
    derivation are exactly the per-dimension checks.  `fxUsageTimesSecurity_variableProjectsToUsage` /
    `…ToSecurity` exhibit it concretely — the variable carrying `(usage 1, security classified)` projects
    to a usage-grade-1 variable and a security-classified variable.

## Zero-axiom verification

The commutation lemmas are structural inductions closing by the hom hypotheses + `rfl`; `mapHom` is the
3-arm derivation induction; the length-map step uses the propext-free local `listLengthMapGrade` (core's
`List.length_map` leaks `propext`).  The projections instantiate `mapHom` with `rfl` preservation proofs.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Push every arrow-grade of a graded type through `f`. -/
def GTypeOver.mapGrade {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier) :
    GTypeOver R → GTypeOver S
  | .base => .base
  | .arrow grade domain codomain =>
      .arrow (f grade) (GTypeOver.mapGrade f domain) (GTypeOver.mapGrade f codomain)

/-- Push every binding's grade through `f`. -/
def GradeVectorOver.mapGrade {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier) :
    GradeVectorOver R → GradeVectorOver S
  | .nil => .nil
  | .cons headGrade restGrades => .cons (f headGrade) (GradeVectorOver.mapGrade f restGrades)

/-- `mapGrade f` carries the all-zero vector to the all-zero vector (given `f` preserves `R.zero`). -/
theorem GradeVectorOver.mapGrade_zero {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (fZero : f R.zero = S.zero) (scope : Nat) :
    GradeVectorOver.mapGrade f (GradeVectorOver.zero R scope) = GradeVectorOver.zero S scope := by
  induction scope with
  | zero => rfl
  | succ scope restIH =>
      show GradeVectorOver.cons (f R.zero) (GradeVectorOver.mapGrade f (GradeVectorOver.zero R scope))
        = GradeVectorOver.cons S.zero (GradeVectorOver.zero S scope)
      rw [fZero, restIH]

/-- `mapGrade f` commutes with the singleton (var-rule) vector (given `f` preserves `R.zero`). -/
theorem GradeVectorOver.mapGrade_single {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (fZero : f R.zero = S.zero) (scope position : Nat) (grade : R.Carrier) :
    GradeVectorOver.mapGrade f (GradeVectorOver.single R scope position grade)
      = GradeVectorOver.single S scope position (f grade) := by
  induction scope generalizing position with
  | zero => rfl
  | succ scope restIH =>
      cases position with
      | zero =>
          show GradeVectorOver.cons (f grade) (GradeVectorOver.mapGrade f (GradeVectorOver.zero R scope))
            = GradeVectorOver.cons (f grade) (GradeVectorOver.zero S scope)
          rw [GradeVectorOver.mapGrade_zero f fZero]
      | succ position =>
          show GradeVectorOver.cons (f R.zero)
              (GradeVectorOver.mapGrade f (GradeVectorOver.single R scope position grade))
            = GradeVectorOver.cons S.zero (GradeVectorOver.single S scope position (f grade))
          rw [fZero, restIH]

/-- `mapGrade f` commutes with pointwise addition (given `f` is additive). -/
theorem GradeVectorOver.mapGrade_add {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (fAdd : ∀ firstGrade secondGrade, f (R.add firstGrade secondGrade) = S.add (f firstGrade) (f secondGrade))
    (firstVector secondVector : GradeVectorOver R) :
    GradeVectorOver.mapGrade f (GradeVectorOver.add firstVector secondVector)
      = GradeVectorOver.add (GradeVectorOver.mapGrade f firstVector)
          (GradeVectorOver.mapGrade f secondVector) := by
  induction firstVector generalizing secondVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          show GradeVectorOver.cons (f (R.add firstHead secondHead))
              (GradeVectorOver.mapGrade f (GradeVectorOver.add firstRest secondRest))
            = GradeVectorOver.cons (S.add (f firstHead) (f secondHead))
              (GradeVectorOver.add (GradeVectorOver.mapGrade f firstRest)
                (GradeVectorOver.mapGrade f secondRest))
          rw [fAdd, restIH]

/-- `mapGrade f` commutes with scalar multiplication (given `f` is multiplicative). -/
theorem GradeVectorOver.mapGrade_scale {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (fMul : ∀ firstGrade secondGrade, f (R.mul firstGrade secondGrade) = S.mul (f firstGrade) (f secondGrade))
    (scaleGrade : R.Carrier) (vector : GradeVectorOver R) :
    GradeVectorOver.mapGrade f (GradeVectorOver.scale scaleGrade vector)
      = GradeVectorOver.scale (f scaleGrade) (GradeVectorOver.mapGrade f vector) := by
  induction vector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show GradeVectorOver.cons (f (R.mul scaleGrade headGrade))
          (GradeVectorOver.mapGrade f (GradeVectorOver.scale scaleGrade restGrades))
        = GradeVectorOver.cons (S.mul (f scaleGrade) (f headGrade))
          (GradeVectorOver.scale (f scaleGrade) (GradeVectorOver.mapGrade f restGrades))
      rw [fMul, restIH]

/-- Context lookup commutes with the type map. -/
theorem GTypeOver.lookup_map {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (typeContext : List (GTypeOver R)) (index : Nat) :
    GTypeOver.lookup (typeContext.map (GTypeOver.mapGrade f)) index
      = (GTypeOver.lookup typeContext index).map (GTypeOver.mapGrade f) := by
  induction typeContext generalizing index with
  | nil => rfl
  | cons _headType restTypes restIH =>
      cases index with
      | zero => rfl
      | succ index => exact restIH index

/-- The length of a mapped context, propext-free (core's `List.length_map` leaks `propext`). -/
private theorem listLengthMapGrade {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (typeContext : List (GTypeOver R)) :
    (typeContext.map (GTypeOver.mapGrade f)).length = typeContext.length := by
  induction typeContext with
  | nil => rfl
  | cons _headType restTypes restIH =>
      show (restTypes.map (GTypeOver.mapGrade f)).length + 1 = restTypes.length + 1
      rw [restIH]

/-- ★ **`HasGradeOver` is functorial along a grade-semiring homomorphism.**  A map `f : R.Carrier → S.Carrier`
preserving `zero`/`one`/`add`/`mul` lifts every graded derivation: `HasGradeOver R Γ p t T` becomes
`HasGradeOver S (Γ.map (mapGrade f)) (p.mapGrade f) t (mapGrade f T)`.  Induction on the derivation —
`var` via the `single`-commutation + `f R.one = S.one` + `lookup_map`; `lam` reassembles under the binder;
`app` via the `add`/`scale`-commutations on the App-rule grade `p1 + r·p2`. -/
theorem HasGradeOver.mapHom {R S : OrderedGradeSemiring} (f : R.Carrier → S.Carrier)
    (fZero : f R.zero = S.zero) (fOne : f R.one = S.one)
    (fAdd : ∀ firstGrade secondGrade, f (R.add firstGrade secondGrade) = S.add (f firstGrade) (f secondGrade))
    (fMul : ∀ firstGrade secondGrade, f (R.mul firstGrade secondGrade) = S.mul (f firstGrade) (f secondGrade))
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R} {term : GradedLambda}
    {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) :
    HasGradeOver S (typeContext.map (GTypeOver.mapGrade f)) (grades.mapGrade f) term
      (GTypeOver.mapGrade f resultType) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      rw [GradeVectorOver.mapGrade_single f fZero, fOne]
      have lookupMapped : GTypeOver.lookup (typeContext.map (GTypeOver.mapGrade f)) index
          = some (GTypeOver.mapGrade f varType) := by
        rw [GTypeOver.lookup_map f typeContext index, lookupOk]; rfl
      have varDeriv := HasGradeOver.var (typeContext.map (GTypeOver.mapGrade f)) index
        (GTypeOver.mapGrade f varType) lookupMapped
      rw [listLengthMapGrade] at varDeriv
      exact varDeriv
  | lam typeContext binderGrade domain codomain outerGrades body _bodyTyped bodyIH =>
      exact HasGradeOver.lam (typeContext.map (GTypeOver.mapGrade f)) (f binderGrade)
        (GTypeOver.mapGrade f domain) (GTypeOver.mapGrade f codomain)
        (outerGrades.mapGrade f) body bodyIH
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _functionTyped _argumentTyped functionIH argumentIH =>
      rw [GradeVectorOver.mapGrade_add f fAdd, GradeVectorOver.mapGrade_scale f fMul]
      exact HasGradeOver.app (typeContext.map (GTypeOver.mapGrade f)) (f binderGrade)
        (GTypeOver.mapGrade f domain) (GTypeOver.mapGrade f codomain)
        (functionGrades.mapGrade f) (argumentGrades.mapGrade f) function argument functionIH argumentIH

/-- **Projection to the first dimension.**  `Prod.fst` is a grade-semiring homomorphism `product A B → A`
(every preservation law is `rfl`), so a composite derivation projects to a derivation in the first factor —
the first dimension is checked independently of the second. -/
theorem HasGradeOver.projectFirst {factorA factorB : OrderedGradeSemiring}
    {typeContext : List (GTypeOver (OrderedGradeSemiring.product factorA factorB))}
    {grades : GradeVectorOver (OrderedGradeSemiring.product factorA factorB)} {term : GradedLambda}
    {resultType : GTypeOver (OrderedGradeSemiring.product factorA factorB)}
    (typed : HasGradeOver (OrderedGradeSemiring.product factorA factorB)
      typeContext grades term resultType) :
    HasGradeOver factorA (typeContext.map (GTypeOver.mapGrade Prod.fst)) (grades.mapGrade Prod.fst) term
      (GTypeOver.mapGrade Prod.fst resultType) :=
  HasGradeOver.mapHom Prod.fst rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) typed

/-- **Projection to the second dimension** — the `Prod.snd` twin of `projectFirst`. -/
theorem HasGradeOver.projectSecond {factorA factorB : OrderedGradeSemiring}
    {typeContext : List (GTypeOver (OrderedGradeSemiring.product factorA factorB))}
    {grades : GradeVectorOver (OrderedGradeSemiring.product factorA factorB)} {term : GradedLambda}
    {resultType : GTypeOver (OrderedGradeSemiring.product factorA factorB)}
    (typed : HasGradeOver (OrderedGradeSemiring.product factorA factorB)
      typeContext grades term resultType) :
    HasGradeOver factorB (typeContext.map (GTypeOver.mapGrade Prod.snd)) (grades.mapGrade Prod.snd) term
      (GTypeOver.mapGrade Prod.snd resultType) :=
  HasGradeOver.mapHom Prod.snd rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) typed

/-- The 2-dimension variable carrying `(usage 1, security classified)` projects to a usage-grade-1 variable —
the usage check, in isolation. -/
theorem fxUsageTimesSecurity_variableProjectsToUsage :
    HasGradeOver fxUsageSemiring [GTypeOver.base]
      (GradeVectorOver.single fxUsageSemiring 1 0 UsageGrade.one) (.var 0) GTypeOver.base :=
  HasGradeOver.projectFirst fxUsageTimesSecurity_variableCarriesBothGrades

/-- The same variable projects to a security-classified variable — the security check, in isolation. -/
theorem fxUsageTimesSecurity_variableProjectsToSecurity :
    HasGradeOver fxSecuritySemiring [GTypeOver.base]
      (GradeVectorOver.single fxSecuritySemiring 1 0 SecurityGrade.classified) (.var 0) GTypeOver.base :=
  HasGradeOver.projectSecond fxUsageTimesSecurity_variableCarriesBothGrades

end FX1Poly.Modal
