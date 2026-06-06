import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline

/-! # FX1Poly/Modal/GradedTypingGeneric — the GENERIC graded-typing judgment (DIM5-3 + dims 6–21)

The usage dimension's grade-checking judgment `HasUsage` (`GradedTyping.lean`, DIM2-3) is hardcoded to
the usage carrier (`UsageGrade` arrows, `GradeVector` usage vectors).  But the §6.2 grade-checking rules
— the corrected Wood/Atkey Lam (the lambda records its binder grade in the arrow type) and the App
SCALING (`functionGrades + binderGrade · argumentGrades`) — are the SAME for every dimension: they depend
only on the ordered semiring `R = (Carrier, 0, 1, +, *, ≤)`, never on WHICH dimension it is.  This file
ships that judgment ONCE, generic over any `OrderedGradeSemiring`, on top of the DIM5-2 generic vector
(`GradeVectorOver R`, `GradeVectorGeneric.lean`).  The usage and security dimensions (and the remaining
17) instantiate it for free — no per-dimension re-proof of the judgment or its structural metatheory.

  * `GTypeOver R` — graded simple types over `R`: a base type and a graded arrow
    `dom -(binderGrade)-> cod`, where `binderGrade : R.Carrier` is the grade at which the function
    consumes its argument (the usage `arrow UsageGrade …`, generic).

  * `GTypeOver.lookup` — context lookup by de Bruijn index (structural recursion; the `l[i]?` /
    `getElem?` notation routes through `propext`, so it is avoided, exactly as `GType.lookup`).

  * `HasGradeOver R Γ p t T` — the typing-and-grade judgment: in type context `Γ`, term `t` has type
    `T` and uses the bindings with grade vector `p`.  The three rules mirror DIM2-3 generically: VAR
    uses its variable at grade `R.one` (`single … R.one`); LAM records the body's head grade as the
    arrow's binder grade and passes the body's outer grades out (the co-effect Lam rule); APP combines
    `functionGrades + binderGrade · argumentGrades` (the App SCALING via `GradeVectorOver.add` +
    `scale`).

  * **Structural metatheory** (everything provable WITHOUT reduction): the three inversions
    (`invertVar` / `invertLam` / `invertApp`, read the premises back off a derivation) and the
    length-coherence invariant (`hasGradeOver_length`: a derivation's grade vector is exactly as long
    as its context — the §6.2 alignment every rule maintains, which is why the App rule's two operands
    share a length).  These transfer verbatim from the usage dimension; they are arithmetic on the
    vector, blind to which semiring `R` is.

The orthogonal-composition payoff: `linearIdentityOver_typed` / `kCombinatorOver_typed` are proved ONCE
generically, then instantiated at BOTH `fxUsageSemiring` (arrow grades `ω`/`1`/`0`) AND
`fxSecuritySemiring` (arrow grades `classified`/`unclassified`).  The SAME judgment types the linear
identity and the K combinator in two different dimensions with no per-dimension proof — the
orthogonal-composition thesis (DIM2-7) lifted from the semiring/vector layers (DIM5-1/DIM5-2) to the
JUDGMENT layer.  The reduction-based metatheory (weakening / substitution / subject reduction) is the
next brick; the usage dimension's `GradedTypingMetatheory` / `GradedSubjectReduction` are its concrete
template.

## Zero-axiom verification

`GTypeOver` / `HasGradeOver` are plain inductives over the structure-field carrier `R.Carrier`; the
context `lookup` is structural recursion; the inversions are `cases` with `rfl` index reconstruction;
the length invariant is `induction` over the judgment with `add_length_eq` (proved by structural
recursion, `Nat.noConfusion` on the impossible length-mismatch arm); the witnesses are constructor
terms (`R` is the inductive's implicit parameter, supplied by `(R := …)`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (every declaration probed with
`#print axioms` before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Graded simple types over the ordered semiring `R`: a base type and a graded arrow
`dom -(binderGrade)-> cod`, where `binderGrade : R.Carrier` records how many times (at which §6.1
grade) the function uses its argument.  The generic analogue of `GType`; `DecidableEq` is not derived
because the carrier's `DecidableEq` is a structure field (`R.carrierDecEq`), not an instance — the
`GradeVectorOver` gotcha — and the judgment does not need it. -/
inductive GTypeOver (R : OrderedGradeSemiring) where
  | base : GTypeOver R
  | arrow : R.Carrier → GTypeOver R → GTypeOver R → GTypeOver R

/-- Look up a variable's type in the context by de Bruijn index.  Structural recursion — the `l[i]?`
(`getElem?`) `List` instance routes through `propext`, so it is avoided, exactly as `GType.lookup`. -/
def GTypeOver.lookup {R : OrderedGradeSemiring} : List (GTypeOver R) → Nat → Option (GTypeOver R)
  | [], _ => none
  | headType :: _, 0 => some headType
  | _ :: restTypes, position + 1 => GTypeOver.lookup restTypes position

/-- **The generic graded typing-and-grade judgment** `Γ ⊢_p t : T` over the ordered semiring `R`: in
type context `Γ` (a list of `GTypeOver R`), term `t` has type `T` and uses the bindings with grade
vector `p : GradeVectorOver R`.  The three rules are DIM2-3's, generic over `R`:

  * VAR uses its variable at grade `R.one` (`GradeVectorOver.single … R.one`);
  * LAM records the body's head grade as the arrow's binder grade and passes the body's outer grades
    out (the co-effect Lam rule);
  * APP combines `functionGrades + binderGrade · argumentGrades` — the App SCALING (`add` of the
    function grades and the `scale`-by-binder-grade argument grades), the accounting that makes the
    judgment subject-reduction-sound (DIM2-3). -/
inductive HasGradeOver (R : OrderedGradeSemiring) :
    List (GTypeOver R) → GradeVectorOver R → GradedLambda → GTypeOver R → Prop where
  | var (typeContext : List (GTypeOver R)) (index : Nat) (varType : GTypeOver R)
      (lookupOk : GTypeOver.lookup typeContext index = some varType) :
      HasGradeOver R typeContext (GradeVectorOver.single R typeContext.length index R.one)
        (.var index) varType
  | lam (typeContext : List (GTypeOver R)) (binderGrade : R.Carrier) (domain codomain : GTypeOver R)
      (outerGrades : GradeVectorOver R) (body : GradedLambda)
      (bodyTyped : HasGradeOver R (domain :: typeContext)
        (GradeVectorOver.cons binderGrade outerGrades) body codomain) :
      HasGradeOver R typeContext outerGrades (.lam body) (.arrow binderGrade domain codomain)
  | app (typeContext : List (GTypeOver R)) (binderGrade : R.Carrier) (domain codomain : GTypeOver R)
      (functionGrades argumentGrades : GradeVectorOver R) (function argument : GradedLambda)
      (functionTyped : HasGradeOver R typeContext functionGrades function
        (.arrow binderGrade domain codomain))
      (argumentTyped : HasGradeOver R typeContext argumentGrades argument domain) :
      HasGradeOver R typeContext
        (GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades))
        (.app function argument) codomain

/-! ## Pointwise-add length coherence (the generic vector helper the length invariant needs) -/

/-- Pointwise add of EQUAL-length vectors keeps that length (it does not truncate).  The generic twin
of `GradedTypingMetatheory.add_length_eq`; the impossible length-mismatch arm is refuted by
`Nat.noConfusion` (avoiding `Nat.succ_ne_zero`, which pulls `propext`). -/
theorem GradeVectorOver.add_length_eq {R : OrderedGradeSemiring} :
    ∀ (firstVector secondVector : GradeVectorOver R), firstVector.length = secondVector.length →
      (GradeVectorOver.add firstVector secondVector).length = firstVector.length
  | .nil, _, _ => rfl
  | .cons _ firstRest, .nil, lengthEq => by
      have contra : firstRest.length + 1 = 0 := lengthEq
      exact Nat.noConfusion contra
  | .cons _ firstRest, .cons _ secondRest, lengthEq => by
      show (GradeVectorOver.add firstRest secondRest).length + 1 = firstRest.length + 1
      rw [GradeVectorOver.add_length_eq firstRest secondRest (Nat.succ.inj lengthEq)]

/-! ## Inversion — reading the premises back off a derivation -/

/-- Inversion for a variable: its type is the context lookup, its grades the var-rule singleton. -/
theorem HasGradeOver.invertVar {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {index : Nat} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.var index) resultType) :
    GTypeOver.lookup typeContext index = some resultType ∧
      grades = GradeVectorOver.single R typeContext.length index R.one := by
  cases typed with
  | var _ _ _ lookupOk => exact ⟨lookupOk, rfl⟩

/-- Inversion for a lambda: the type is a graded arrow, the body typed in the extended context with
the binder grade pushed onto the grade vector. -/
theorem HasGradeOver.invertLam {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {body : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.lam body) resultType) :
    ∃ (binderGrade : R.Carrier) (domain codomain : GTypeOver R),
      resultType = .arrow binderGrade domain codomain ∧
        HasGradeOver R (domain :: typeContext) (GradeVectorOver.cons binderGrade grades)
          body codomain := by
  cases typed with
  | lam _ binderGrade domain codomain _ _ bodyTyped =>
      exact ⟨binderGrade, domain, codomain, rfl, bodyTyped⟩

/-- Inversion for an application: function and argument typed, grades the App-scaled sum
`functionGrades + binderGrade · argumentGrades`. -/
theorem HasGradeOver.invertApp {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {function argument : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.app function argument) resultType) :
    ∃ (binderGrade : R.Carrier) (domain : GTypeOver R)
      (functionGrades argumentGrades : GradeVectorOver R),
      HasGradeOver R typeContext functionGrades function (.arrow binderGrade domain resultType) ∧
        HasGradeOver R typeContext argumentGrades argument domain ∧
          grades = GradeVectorOver.add functionGrades
            (GradeVectorOver.scale binderGrade argumentGrades) := by
  cases typed with
  | app _ binderGrade domain codomain functionGrades argumentGrades _ _ functionTyped argumentTyped =>
      exact ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, rfl⟩

/-! ## The length invariant -/

/-- **The length invariant**: a derivation's grade vector is exactly as long as its context.  Every
rule keeps grades length-aligned to the scope (VAR: a `single` of the context length; LAM: pops one;
APP: `add` of two equal-length operands, via `add_length_eq`).  This is the §6.2 coherence that lets
the App rule's two operands share a length — the structural twin of `hasUsage_length`, generic over
`R`. -/
theorem hasGradeOver_length {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) :
    grades.length = typeContext.length := by
  induction typed with
  | var typeContext index varType _ => exact GradeVectorOver.single_length R _ _ _
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      have step : outerGrades.length + 1 = typeContext.length + 1 := bodyIH
      exact Nat.succ.inj step
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _ _ functionIH argumentIH =>
      have lenScale : (GradeVectorOver.scale binderGrade argumentGrades).length =
          typeContext.length := by
        rw [GradeVectorOver.scale_length]; exact argumentIH
      rw [GradeVectorOver.add_length_eq functionGrades
            (GradeVectorOver.scale binderGrade argumentGrades) (by rw [functionIH, lenScale])]
      exact functionIH

/-! ## Generic witnesses — grades track usage exactly, in ANY dimension -/

/-- **The linear identity types at arrow grade `R.one`, in any dimension.**  `λx. x :
base -(R.one)-> base` in the empty context, using no outer bindings (`nil`): `x` is used once, so the
binder grade is `R.one`.  Proved ONCE generically; the dimension reads its own "used once" grade off
the arrow. -/
theorem linearIdentityOver_typed (R : OrderedGradeSemiring) :
    HasGradeOver R [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow R.one GTypeOver.base GTypeOver.base) :=
  HasGradeOver.lam (R := R) [] R.one GTypeOver.base GTypeOver.base GradeVectorOver.nil (.var 0)
    (HasGradeOver.var (R := R) [GTypeOver.base] 0 GTypeOver.base rfl)

/-- **The K combinator's grades track usage exactly, in any dimension.**
`λx. λy. x : base -(R.one)-> (base -(R.zero)-> base)`: `x` is used once (binder grade `R.one`), `y` is
dropped (binder grade `R.zero`).  Proved ONCE generically; the discipline reads "used" vs "discarded"
straight off the nested arrow grades. -/
theorem kCombinatorOver_typed (R : OrderedGradeSemiring) :
    HasGradeOver R [] GradeVectorOver.nil (.lam (.lam (.var 1)))
      (.arrow R.one GTypeOver.base (.arrow R.zero GTypeOver.base GTypeOver.base)) :=
  HasGradeOver.lam (R := R) [] R.one GTypeOver.base (.arrow R.zero GTypeOver.base GTypeOver.base)
    GradeVectorOver.nil (.lam (.var 1))
    (HasGradeOver.lam (R := R) [GTypeOver.base] R.zero GTypeOver.base GTypeOver.base
      (GradeVectorOver.cons R.one GradeVectorOver.nil) (.var 1)
      (HasGradeOver.var (R := R) [GTypeOver.base, GTypeOver.base] 1 GTypeOver.base rfl))

/-! ## Per-dimension instantiation smokes — the SAME judgment, two dimensions (DIM5-3) -/

/-- Usage-dimension instantiation: the generic judgment types the linear identity at `fxUsageSemiring`
with arrow grade `UsageGrade.one`. -/
theorem usageLinearIdentity_typedViaGeneric :
    HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow fxUsageSemiring.one GTypeOver.base GTypeOver.base) :=
  linearIdentityOver_typed fxUsageSemiring

/-- **DIM5-3: the security-dimension graded judgment.**  The SAME `HasGradeOver` types the linear
identity at `fxSecuritySemiring` (DIM5-1) — arrow grade `SecurityGrade.classified` (= `R.one`).  No
per-dimension proof: the generic `linearIdentityOver_typed` instantiated at a second semiring.  The
orthogonal-composition thesis (DIM2-7) at the JUDGMENT layer — a second dimension grade-checked by the
shared judgment with no change to it. -/
theorem securityLinearIdentity_typedViaGeneric :
    HasGradeOver fxSecuritySemiring [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow fxSecuritySemiring.one GTypeOver.base GTypeOver.base) :=
  linearIdentityOver_typed fxSecuritySemiring

/-- DIM5-3: the security dimension's K combinator via the shared judgment — `λx.λy.x` typed at
`fxSecuritySemiring` with the discard binder grade `SecurityGrade.unclassified` (= `R.zero`) on `y`.
A second witness that the generic judgment carries the full grade discipline (use AND discard) into the
security dimension unchanged. -/
theorem securityKCombinator_typedViaGeneric :
    HasGradeOver fxSecuritySemiring [] GradeVectorOver.nil (.lam (.lam (.var 1)))
      (.arrow fxSecuritySemiring.one GTypeOver.base
        (.arrow fxSecuritySemiring.zero GTypeOver.base GTypeOver.base)) :=
  kCombinatorOver_typed fxSecuritySemiring

end FX1Poly.Modal
