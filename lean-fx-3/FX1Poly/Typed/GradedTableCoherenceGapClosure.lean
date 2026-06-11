import FX1Poly.Typed.GradedTableCoherence

/-! # FX1Poly/Typed/GradedTableCoherenceGapClosure — closing the two pinned directional gaps

`GradedTableCoherence` proves the keystone iff `gradedBinderChecks_iff_gradeSubsumption` (the table's
`binderUsage` field IS grade subsumption of the syntactic count's semiring image,
`natToUsageGrade count ≤ binderUsage`) and then PINS two directional residuals as bare witnesses:

  * the FORWARD residual `scalingGapForward` (a full `HasGradeOver` lam binder grade does NOT imply the
    table check at that grade — App 0-scaling makes the judgment β-aware while the table is syntactic);
  * the BACKWARD residual `synthesisGapBackward` (the table check at a grade does NOT imply a judgment
    derivation at that grade — the Wood/Atkey rules synthesise grades with no subsumption rule).

This module CLOSES both: the backward residual is closed as a STRENGTHENED IFF that exactly
characterises the residual as subsumption SLACK, and the forward residual is PROVEN TIGHT by a sharpened
witness that places the judgment grade STRICTLY BELOW the count's semiring image (so the gap is genuine
and the keystone iff cannot be strengthened to a two-way equivalence on the full fragment).

## The backward gap — CLOSED as a strengthened iff (the residual is exactly subsumption slack)

  * **`identityGradeableIffBinderGradeOne`** — the full characterisation: the identity `λx.x` is
    `HasGradeOver`-derivable at binder grade `g` IFF `g = one`.  Forward arrow is the shipped #1000
    exactness (`identityBinderGradeForcedOne`); backward arrow is `linearIdentityOver_typed`.  This
    strengthens the bare negation `identityNotGradeableAtOmega` into the COMPLETE set of admissible
    binder grades — exactly the singleton `{one}`.
  * **`identityCountImageIsOne`** — the identity body's count image is `natToUsageGrade 1 = one`, so the
    unique admissible binder grade IS the count's semiring image.
  * **`tableCheckAtExactImage_derivesIdentity`** — the CLOSURE: when the table grade equals the EXACT
    count image (`g = natToUsageGrade count`, the subsumption taken with EQUALITY rather than `≤`), the
    judgment derivation EXISTS.  The backward bridge holds at the exact image; the residual is precisely
    the slack between the table's `natToUsageGrade count ≤ g` (upper bound) and the judgment's
    `g = natToUsageGrade count` (exact synthesis).
  * **`backwardResidualIsStrictSlack`** — the tightness pin: at `g = omega` the table accepts
    (`natToUsageGrade 1 = one ≤ omega`, the slack `one < omega`) but the judgment refuses
    (`identityNotGradeableAtOmega`).  The residual lives EXACTLY where the count image is STRICTLY below
    the table grade.

## The forward gap — PROVEN TIGHT (the judgment grade is strictly below the count image)

  * **`affineDuplicatorViolatesGradeSubsumption`** — the sharpened forward witness via the keystone iff:
    the duplicator `λx.(f x) x` is judgment-derivable at binder grade `zero`, yet
    `UsageGrade.le (natToUsageGrade count) zero = false` — the count's image `omega` is STRICTLY ABOVE
    the judgment grade `zero`, so grade subsumption (= the table check, by the keystone iff) FAILS.  The
    judgment synthesises a binder grade BELOW the count's semiring image (β-aware 0-scaling), which the
    monotone count-reading can never bound.  This is sharper than the shipped
    `affineGradeZero_doesNotBoundCount`: it places the violation on the SUBSUMPTION ORDER, the exact
    object the keystone iff equates the table check to.
  * **`forwardGapIsGenuine`** — the tightness conclusion: there is a judgment derivation whose binder
    grade `g` admits a count whose image is NOT `≤ g`; hence no strengthening of the keystone iff to
    `HasGradeOver-at-g ⟹ table-check-at-g` can hold.  The forward direction is irreparably one-way off
    the strict fragment.

## The boundary the two closures pin

The keystone iff `gradedBinderChecks usage body ↔ natToUsageGrade count ≤ usage` is the STRONGEST true
statement: forward, the judgment grade can sit STRICTLY BELOW the count image (β-aware scaling), so
"judgment ⟹ table" fails; backward, the judgment grade is pinned EXACTLY to the count image (no
subsumption rule), so "table ⟹ judgment" fails for any STRICTLY larger table grade.  Both residuals are
the SAME object — the strict part of the subsumption order — read from the two opposite sides.

## Zero-axiom

The strengthened iff is a pair of shipped citations (`identityBinderGradeForcedOne` /
`linearIdentityOver_typed`); the exact-image closure is `rfl`-reduction of `natToUsageGrade 1` plus the
identity witness; the forward tightness routes the shipped 0-scaling leak through the keystone iff
(`usageBoundsCount_iff_gradeLe`) and discriminates the resulting `le`-Bool by `rfl` + `Bool.noConfusion`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditGradedTableCoherenceGapClosure.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-! ## The backward gap — CLOSED as a strengthened iff -/

/-- **★ The complete admissible-grade characterisation for the identity.**  `λx.x` is
`HasGradeOver`-derivable at binder grade `g` IFF `g = one`.  The forward arrow is the shipped #1000
grade-exactness (`identityBinderGradeForcedOne`: the Wood/Atkey rules synthesise the binder grade
exactly, with no subsumption); the backward arrow is `linearIdentityOver_typed` (the linear identity
IS derivable at `one`).  This strengthens the pinned bare negation `identityNotGradeableAtOmega` from
"not at `omega`" to "at PRECISELY the singleton `{one}`" — the residual of the backward bridge is the
whole complement of that singleton. -/
theorem identityGradeableIffBinderGradeOne {binderGrade : UsageGrade} :
    HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow binderGrade GTypeOver.base GTypeOver.base)
      ↔ binderGrade = UsageGrade.one :=
  ⟨fun typed => identityBinderGradeForcedOne typed,
    fun gradeIsOne => gradeIsOne ▸ linearIdentityOver_typed fxUsageSemiring⟩

/-- The identity body's syntactic occurrence count maps to `one` under `natToUsageGrade`: `var 0`
occurs once at position `0`, and `natToUsageGrade 1 = one`.  So the UNIQUE admissible binder grade
(`identityGradeableIffBinderGradeOne`) IS the count's semiring image. -/
theorem identityCountImageIsOne :
    natToUsageGrade (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)) = UsageGrade.one :=
  rfl

/-- **★ THE BACKWARD CLOSURE.**  When the table grade equals the EXACT count image
(`g = natToUsageGrade count` — the keystone subsumption taken with EQUALITY rather than the loose `≤`),
the identity's `HasGradeOver` derivation EXISTS at that grade.  The backward bridge holds at the exact
image; the pinned residual is therefore PRECISELY the subsumption slack between the table's upper bound
`natToUsageGrade count ≤ g` and the judgment's exact synthesis `g = natToUsageGrade count`. -/
theorem tableCheckAtExactImage_derivesIdentity (binderGrade : UsageGrade)
    (atExactImage : binderGrade
      = natToUsageGrade (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0))) :
    HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow binderGrade GTypeOver.base GTypeOver.base) :=
  identityGradeableIffBinderGradeOne.mpr (atExactImage.trans identityCountImageIsOne)

/-- **★ The backward residual lives exactly at the STRICT subsumption slack.**  At `g = omega` the
table check accepts (the count image `one` IS `≤ omega` — the proper inequality `one < omega`), yet the
identity is NOT judgment-derivable at `omega`.  Pairs the table-acceptance (as a grade-subsumption
`le` fact) with the shipped non-derivability: the residual is non-empty PRECISELY where the count image
sits strictly below the table grade. -/
theorem backwardResidualIsStrictSlack :
    UsageGrade.le
        (natToUsageGrade (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)))
        UsageGrade.omega = true ∧
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow UsageGrade.omega GTypeOver.base GTypeOver.base) :=
  ⟨rfl, identityNotGradeableAtOmega⟩

/-! ## The forward gap — PROVEN TIGHT (judgment grade strictly below the count image) -/

/-- **★ THE SHARPENED FORWARD WITNESS, via the keystone iff.**  The duplicator `λx.(f x) x` is
judgment-derivable at binder grade `zero`, yet the table check at `zero` FAILS — and via the keystone
`usageBoundsCount_iff_gradeLe` the failure is placed on the SUBSUMPTION ORDER:
`UsageGrade.le (natToUsageGrade count) zero = false`, i.e. the count's image `omega` is STRICTLY ABOVE
the judgment grade `zero`.  The semiring synthesises a binder grade BELOW the syntactic count's image
(β-aware 0-scaling annihilates the discarded occurrences); no monotone count-reading can bound that.
Sharper than `affineGradeZero_doesNotBoundCount`: it pins the violation on the exact object the keystone
iff equates the table check to. -/
theorem affineDuplicatorViolatesGradeSubsumption :
    HasGradeOver fxUsageSemiring [zeroScalingFunctionType, .base]
        (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
          GradeVectorOver.nil))
        (.lam affineDuplicatorBody) (.arrow UsageGrade.zero .base .base) ∧
    UsageGrade.le
        (natToUsageGrade (GradedLambda.countOccurrencesAt 0 affineDuplicatorBody))
        UsageGrade.zero = false :=
  ⟨affineDuplicatorLam_typedAtGradeZero, rfl⟩

/-- **★ THE FORWARD TIGHTNESS CONCLUSION.**  There is a `HasGradeOver` derivation of a lambda whose
binder grade `g` is NOT an upper bound for its body's count image (`UsageGrade.le (natToUsageGrade
count) g = false`).  By the keystone iff, the table check `gradedBinderChecks`-style bound (here the
`GradedLambda` interpreter `boundsCount`) is exactly `natToUsageGrade count ≤ g`, so this derivation
fails the table check at its own binder grade.  No strengthening of the keystone iff to a two-way
implication "judgment-at-`g` ⟹ table-at-`g`" can hold — the forward direction is irreparably one-way
off the strict-linear fragment. -/
theorem forwardGapIsGenuine :
    ∃ (typeContext : List (GTypeOver fxUsageSemiring))
      (outerGrades : GradeVectorOver fxUsageSemiring) (body : GradedLambda)
      (domain codomain : GTypeOver fxUsageSemiring) (binderGrade : UsageGrade),
      HasGradeOver fxUsageSemiring typeContext outerGrades (.lam body)
        (.arrow binderGrade domain codomain) ∧
      UsageGrade.le
          (natToUsageGrade (GradedLambda.countOccurrencesAt 0 body)) binderGrade = false ∧
      ¬ UsageGrade.boundsCount binderGrade (GradedLambda.countOccurrencesAt 0 body) :=
  ⟨[zeroScalingFunctionType, .base],
    GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
      GradeVectorOver.nil),
    affineDuplicatorBody, .base, .base, UsageGrade.zero,
    affineDuplicatorLam_typedAtGradeZero, rfl,
    fun bounds =>
      Bool.noConfusion
        (((usageBoundsCount_iff_gradeLe UsageGrade.zero
            (GradedLambda.countOccurrencesAt 0 affineDuplicatorBody)).mp bounds))⟩

/-! ## The combined gap-closure verdict gate -/

/-- **The gap-closure verdict.**  Each field is one closed leg: the backward residual is the
strengthened admissible-grade iff (closed at the exact count image, residual = strict subsumption
slack); the forward residual is the sharpened keystone-iff witness (the judgment grade is strictly below
the count image, so the table check fails at the judgment's own binder grade — proven tight). -/
structure GradedTableCoherenceGapClosureVerdict : Prop where
  /-- Backward, closed: the identity is derivable at binder grade `g` IFF `g = one`. -/
  backwardAdmissibleGradeIsExactlyOne : ∀ {binderGrade : UsageGrade},
    HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow binderGrade GTypeOver.base GTypeOver.base)
      ↔ binderGrade = UsageGrade.one
  /-- Backward, closed at the exact image: the table check at `g = natToUsageGrade count` derives. -/
  backwardExactImageDerives : ∀ (binderGrade : UsageGrade),
    binderGrade = natToUsageGrade (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)) →
    HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow binderGrade GTypeOver.base GTypeOver.base)
  /-- Backward, tight: the residual lives exactly at the strict subsumption slack `one < omega`. -/
  backwardResidualIsStrictSlack :
    UsageGrade.le
        (natToUsageGrade (GradedLambda.countOccurrencesAt 0 (GradedLambda.var 0)))
        UsageGrade.omega = true ∧
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow UsageGrade.omega GTypeOver.base GTypeOver.base)
  /-- Forward, tight: a derivation whose binder grade is strictly below its body's count image. -/
  forwardGradeStrictlyBelowCountImage : ∃ (typeContext : List (GTypeOver fxUsageSemiring))
    (outerGrades : GradeVectorOver fxUsageSemiring) (body : GradedLambda)
    (domain codomain : GTypeOver fxUsageSemiring) (binderGrade : UsageGrade),
    HasGradeOver fxUsageSemiring typeContext outerGrades (.lam body)
      (.arrow binderGrade domain codomain) ∧
    UsageGrade.le
        (natToUsageGrade (GradedLambda.countOccurrencesAt 0 body)) binderGrade = false ∧
    ¬ UsageGrade.boundsCount binderGrade (GradedLambda.countOccurrencesAt 0 body)

/-- **★ The gap-closure verdict** — inhabited by the closures above. -/
theorem gradedTableCoherenceGapClosureVerdict : GradedTableCoherenceGapClosureVerdict where
  backwardAdmissibleGradeIsExactlyOne := identityGradeableIffBinderGradeOne
  backwardExactImageDerives := tableCheckAtExactImage_derivesIdentity
  backwardResidualIsStrictSlack := backwardResidualIsStrictSlack
  forwardGradeStrictlyBelowCountImage := forwardGapIsGenuine

end FX1Poly.Typed
