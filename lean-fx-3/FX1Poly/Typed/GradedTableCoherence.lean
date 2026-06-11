import FX1Poly.Typed.GradedIntroPremiseSpike
import FX1Poly.Modal.GradedLinearTime
import FX1Poly.Modal.GradedGradeExactness

/-! # FX1Poly/Typed/GradedTableCoherence — NATIVE-26: table binderUsage ↔ HasGradeOver
    (the single-binder projection, with the exact correspondence AND both directional gaps pinned)

THE QUESTION: the table-graded discipline (`GradedIntroRule.binderUsage`, interpreted by
`gradedBinderChecks` as a syntactic occurrence bound at binder position 0 — load-bearing in
`HasTypeNativeUnion.gradedBinderIntro`) versus the generic semiring discipline `HasGradeOver` at
`fxUsageSemiring` (the corrected Wood/Atkey judgment, where grades are SYNTHESIZED by the rules
with App SCALING `functionGrades + binderGrade · argumentGrades`).  How do they relate?

## The exact correspondence (the keystone)

  * **`natToUsageGrade`** — the count→grade abstraction (`0 ↦ zero`, `1 ↦ one`, `≥2 ↦ omega`),
    an ADDITIVE MONOID HOMOMORPHISM `(Nat, +, 0) → (UsageGrade, add, zero)`
    (`natToUsageGrade_addHom`, nine-case `rfl` — `one + one = omega` is exactly why the table
    never hides two uses behind a `one`).
  * **★ `gradedBinderChecks_iff_gradeSubsumption`** — THE single-binder projection: the table
    check `gradedBinderChecks usage body` holds IFF
    `natToUsageGrade (occurrenceCountAt body 0) ≤ usage` in the usage ORDER (the affine chain
    `zero ≤ one ≤ omega`).  The table's binderUsage discipline IS grade subsumption of the
    syntactic count's semiring image — a bona fide graded reading, not an ad-hoc side condition.

## Where the two disciplines agree, and the two PRECISE gaps

  * **★ `strictLinearLam_meetsAffineDiscipline`** — on the STRICT-linear fragment (every binder
    grade `one`, App scaling = identity), a lambda derivation SATISFIES the table's affine
    discipline at the shared interpreter `boundsCount` (via the shipped
    `HasStrictLinearGrade.lamBodyCountBound`).  The two syntaxes (`RawTerm` vs `GradedLambda`)
    meet in the interpreter, which is the same `UsageGrade.boundsCount` on both sides.
  * **★ `fullJudgmentLamGrade_doesNotMeetDiscipline`** — the FORWARD gap: beyond the strict
    fragment, a full-`HasGradeOver` lam binder grade does NOT imply the table check at that
    grade.  Witness: the shipped 0-scaling leak (`affineDuplicatorLam_typedAtGradeZero`) — the
    judgment grades the binder ZERO while the body uses it TWICE, because App scaling by `zero`
    annihilates the argument's grades while the syntax keeps the occurrences.  The semiring is
    β-AWARE (a discarded argument's occurrences vanish under reduction); the table is SYNTACTIC.
  * **★ `identityNotGradeableAtOmega` (+ `identityMeetsDisciplineAtOmega`)** — the BACKWARD gap:
    the table check at grade `g` does NOT imply a judgment derivation at binder grade `g`,
    because the Wood/Atkey rules SYNTHESIZE grades with no subsumption rule.  Witness: `λx.x`
    passes the table at `omega` (`boundsCount omega` is unconstrained) but is NOT gradeable at
    binder `omega` — the #1000 grade-exactness forces `one` (`identityBinderGradeForcedOne`),
    so an `omega` derivation would force `omega = one`, refuted by constructor no-confusion.

## The verdict (the NATIVE-59 input)

The table check is the SUBSUMPTION-form usage discipline on the syntactic count's grade image —
exactly `natToUsageGrade count ≤ binderUsage`.  The synthesized Wood/Atkey judgment agrees on
the strict-linear fragment and diverges beyond it in BOTH directions for two DIFFERENT,
precisely-pinned reasons: App 0/ω-scaling makes the semiring β-aware where the table is
syntactic (forward), and synthesis-without-subsumption pins exact grades where the table
accepts any upper bound (backward).  For NATIVE-59 (the affine premise's semantic role): the
pathLam `.one` row is the subsumption reading `natToUsageGrade count ≤ one`, i.e. count ≤ 1 —
the AFFINE (at-most-once) discipline, matching the strict fragment's guarantee, NOT the full
judgment's β-aware grade.

## Zero-axiom

`natToUsageGrade` is a three-arm Nat match; the hom and the order-iff are full finite case
enumerations (`rfl` / `Nat.noConfusion` / `Bool.noConfusion` / `Nat.zero_le` /
`Nat.le_of_succ_le_succ` + `Nat.not_succ_le_zero`); the agreement and gaps are direct citations
of the shipped COST-2a / #1000 witnesses.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-! ## The count→grade abstraction and its algebra -/

/-- The count→grade abstraction: `0 ↦ zero`, `1 ↦ one`, everything else `omega`.  The semiring
image of a syntactic occurrence count. -/
def natToUsageGrade : Nat → UsageGrade
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .omega

/-- The abstraction maps the empty count to the zero grade. -/
theorem natToUsageGrade_ofZero : natToUsageGrade 0 = UsageGrade.zero := rfl

/-- **The abstraction is an additive monoid homomorphism** `(Nat, +, 0) → (UsageGrade, add,
zero)` — nine-case `rfl`.  The load-bearing diagonal is `1 + 1 ↦ omega = add one one`: the
usage `add` table never compresses two uses into a `one`, which is exactly what makes the
count-reading of grades sound under context splitting. -/
theorem natToUsageGrade_addHom : ∀ (firstCount secondCount : Nat),
    natToUsageGrade (firstCount + secondCount)
      = UsageGrade.add (natToUsageGrade firstCount) (natToUsageGrade secondCount)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, _ + 2 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 1, _ + 2 => rfl
  | _ + 2, 0 => rfl
  | _ + 2, 1 => rfl
  | _ + 2, _ + 2 => rfl

/-! ## The order-form reading of `boundsCount` -/

/-- **`boundsCount` IS grade subsumption of the count's image**: a usage grade bounds a count
iff the count's `natToUsageGrade` image is `≤` the grade in the affine usage chain
`zero ≤ one ≤ omega`.  Full 3×3 enumeration (grade × count shape). -/
theorem usageBoundsCount_iff_gradeLe (usage : UsageGrade) (count : Nat) :
    usage.boundsCount count ↔ UsageGrade.le (natToUsageGrade count) usage = true := by
  cases usage with
  | zero =>
      cases count with
      | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | succ priorCount =>
          cases priorCount with
          | zero => exact ⟨fun oneIsZero => Nat.noConfusion oneIsZero,
              fun falseIsTrue => Bool.noConfusion falseIsTrue⟩
          | succ _ => exact ⟨fun succIsZero => Nat.noConfusion succIsZero,
              fun falseIsTrue => Bool.noConfusion falseIsTrue⟩
  | one =>
      cases count with
      | zero => exact ⟨fun _ => rfl, fun _ => Nat.zero_le 1⟩
      | succ priorCount =>
          cases priorCount with
          | zero => exact ⟨fun _ => rfl, fun _ => Nat.le_refl 1⟩
          | succ deeperCount =>
              exact ⟨fun twoLeOne => absurd (Nat.le_of_succ_le_succ twoLeOne)
                  (Nat.not_succ_le_zero deeperCount),
                fun falseIsTrue => Bool.noConfusion falseIsTrue⟩
  | omega =>
      cases count with
      | zero => exact ⟨fun _ => rfl, fun _ => trivial⟩
      | succ priorCount =>
          cases priorCount with
          | zero => exact ⟨fun _ => rfl, fun _ => trivial⟩
          | succ _ => exact ⟨fun _ => rfl, fun _ => trivial⟩

/-! ## ★ The single-binder projection: the table check IS grade subsumption -/

/-- **★ THE NATIVE-26 KEYSTONE.**  The table-graded intro check (`gradedBinderChecks`, the
premise `HasTypeNativeUnion.gradedBinderIntro` enforces) holds IFF the binder's syntactic
occurrence count maps under `natToUsageGrade` to a grade `≤ binderUsage` in the usage order.
The table's `binderUsage` field is a bona fide GRADED discipline: subsumption against the
syntactic count's semiring image — not an ad-hoc side condition. -/
theorem gradedBinderChecks_iff_gradeSubsumption (usage : UsageGrade) {scope : Nat}
    (body : RawTerm (scope + 1)) :
    gradedBinderChecks usage body
      ↔ UsageGrade.le
          (natToUsageGrade (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩)) usage
          = true :=
  usageBoundsCount_iff_gradeLe usage
    (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩)

/-! ## ★ Agreement on the strict-linear fragment (the shared interpreter) -/

/-- **★ The strict-linear lam rule SATISFIES the table's affine discipline.**  A strict-linear
lambda derivation (`HasStrictLinearGrade`, every binder grade `one`) guarantees its body's
binder-position occurrence count meets `boundsCount one` — the SAME interpreter the table's
`.one` row reads (`gradedBinderChecks UsageGrade.one` is `boundsCount one` at the RawTerm
count).  The two syntaxes meet in the interpreter: the semiring's strict lam discipline and the
table's affine row enforce the SAME occurrence bound. -/
theorem strictLinearLam_meetsAffineDiscipline
    {typeContext : List (GTypeOver fxUsageSemiring)}
    {outerGrades : GradeVectorOver fxUsageSemiring} {body : GradedLambda}
    {domain codomain : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext outerGrades (.lam body)
      (.arrow fxUsageSemiring.one domain codomain)) :
    UsageGrade.boundsCount UsageGrade.one (GradedLambda.countOccurrencesAt 0 body) :=
  typed.lamBodyCountBound

/-! ## ★ The FORWARD gap: full-judgment grades are β-aware, the table is syntactic -/

/-- **★ Beyond the strict fragment, a `HasGradeOver` lam binder grade does NOT imply the table
discipline at that grade** — the shipped 0-scaling leak as a coherence refutation: the judgment
grades the `affineDuplicatorBody` binder at ZERO (App scaling by `zero` annihilates the
argument's grades) while the binder occurs TWICE syntactically.  The semiring tracks usage up
to β (the discarded occurrences vanish under reduction); the table counts the present syntax. -/
theorem fullJudgmentLamGrade_doesNotMeetDiscipline :
    ∃ (typeContext : List (GTypeOver fxUsageSemiring))
      (outerGrades : GradeVectorOver fxUsageSemiring) (body : GradedLambda)
      (domain codomain : GTypeOver fxUsageSemiring) (binderGrade : UsageGrade),
      HasGradeOver fxUsageSemiring typeContext outerGrades (.lam body)
        (.arrow binderGrade domain codomain) ∧
      ¬ UsageGrade.boundsCount binderGrade (GradedLambda.countOccurrencesAt 0 body) :=
  ⟨[zeroScalingFunctionType, .base],
    GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
      GradeVectorOver.nil),
    affineDuplicatorBody, .base, .base, UsageGrade.zero,
    affineDuplicatorLam_typedAtGradeZero, affineGradeZero_doesNotBoundCount⟩

/-! ## ★ The BACKWARD gap: the table accepts upper bounds, the judgment synthesizes exactly -/

/-- The identity body passes the table discipline at `omega` (the unconstrained row accepts any
count — `boundsCount omega` is `True`). -/
theorem identityMeetsDisciplineAtOmega :
    UsageGrade.boundsCount UsageGrade.omega
      (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)) :=
  trivial

/-- **★ The identity is NOT gradeable at binder `omega`** — the Wood/Atkey rules synthesize
grades with no subsumption rule, so the #1000 grade-exactness (`identityBinderGradeForcedOne`)
forces the binder to `one`; a derivation at `omega` would force `omega = one`, refuted by
constructor no-confusion.  Together with `identityMeetsDisciplineAtOmega`: the table check at a
grade does NOT imply a judgment derivation at that grade — the table reads grades as UPPER
BOUNDS (subsumption), the judgment as EXACT synthesis. -/
theorem identityNotGradeableAtOmega :
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow UsageGrade.omega GTypeOver.base GTypeOver.base) :=
  fun typed => UsageGrade.noConfusion (identityBinderGradeForcedOne typed)

/-! ## The coherence verdict gate -/

/-- **The NATIVE-26 coherence record.**  Each field is one leg of the verdict: the table check
is EXACTLY grade subsumption of the syntactic count's semiring image (the additive-hom
abstraction `natToUsageGrade`); the strict-linear judgment agrees with the table through the
shared interpreter; and the two disciplines diverge beyond that fragment in BOTH directions —
App 0-scaling forward (β-aware vs syntactic), synthesis-without-subsumption backward (exact vs
upper-bound). -/
structure GradeTableCoherenceVerdict : Prop where
  /-- The table check is grade subsumption of the count image (the keystone iff). -/
  tableCheckIsGradeSubsumption : ∀ (usage : UsageGrade) {scope : Nat}
    (body : RawTerm (scope + 1)),
    gradedBinderChecks usage body
      ↔ UsageGrade.le
          (natToUsageGrade (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩)) usage
          = true
  /-- The count→grade abstraction is an additive monoid homomorphism. -/
  countImageIsAdditive : ∀ (firstCount secondCount : Nat),
    natToUsageGrade (firstCount + secondCount)
      = UsageGrade.add (natToUsageGrade firstCount) (natToUsageGrade secondCount)
  /-- The strict-linear lam rule satisfies the table's affine discipline. -/
  strictFragmentAgrees : ∀ {typeContext : List (GTypeOver fxUsageSemiring)}
    {outerGrades : GradeVectorOver fxUsageSemiring} {body : GradedLambda}
    {domain codomain : GTypeOver fxUsageSemiring},
    HasStrictLinearGrade typeContext outerGrades (.lam body)
      (.arrow fxUsageSemiring.one domain codomain) →
    UsageGrade.boundsCount UsageGrade.one (GradedLambda.countOccurrencesAt 0 body)
  /-- The forward gap: a full-judgment binder grade does not imply the table check. -/
  scalingGapForward : ∃ (typeContext : List (GTypeOver fxUsageSemiring))
    (outerGrades : GradeVectorOver fxUsageSemiring) (body : GradedLambda)
    (domain codomain : GTypeOver fxUsageSemiring) (binderGrade : UsageGrade),
    HasGradeOver fxUsageSemiring typeContext outerGrades (.lam body)
      (.arrow binderGrade domain codomain) ∧
    ¬ UsageGrade.boundsCount binderGrade (GradedLambda.countOccurrencesAt 0 body)
  /-- The backward gap: the table check does not imply a judgment derivation at that grade. -/
  synthesisGapBackward :
    UsageGrade.boundsCount UsageGrade.omega
      (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)) ∧
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow UsageGrade.omega GTypeOver.base GTypeOver.base)

/-- **★ The NATIVE-26 verdict** — inhabited by the shipped witnesses. -/
theorem gradeTableCoherenceVerdict : GradeTableCoherenceVerdict where
  tableCheckIsGradeSubsumption := gradedBinderChecks_iff_gradeSubsumption
  countImageIsAdditive := natToUsageGrade_addHom
  strictFragmentAgrees := fun typed => strictLinearLam_meetsAffineDiscipline typed
  scalingGapForward := fullJudgmentLamGrade_doesNotMeetDiscipline
  synthesisGapBackward := ⟨identityMeetsDisciplineAtOmega, identityNotGradeableAtOmega⟩

end FX1Poly.Typed
