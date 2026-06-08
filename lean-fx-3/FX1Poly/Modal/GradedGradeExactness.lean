import FX1Poly.Modal.GradedTypingGeneric

/-! # FX1Poly/Modal/GradedGradeExactness — the graded type system forces the EXACT binder grade

`GradedTypingGeneric` ships the POSITIVE witnesses: the linear identity types AT arrow grade `R.one`
(`linearIdentityOver_typed`) and the K combinator types with the dropped binder AT grade `R.zero`
(`kCombinatorOver_typed`).  This file ships the CONVERSE — the grades are not merely *achievable* but
*forced*: a derivation of those terms at ANY binder grade pins that grade EXACTLY.  Since the judgment
has no subsumption rule (the three rules synthesise grades exactly — §6.2), the grade vector is
computed, not chosen; so "uses its argument" is recorded as precisely `R.one` and "discards its
argument" as precisely `R.zero`, with no slack.  This is grade HONESTY: the type system cannot be made
to under- or over-count a binding's usage.

  * **`identityBinderGradeForcedOne`** — `λx.x : base -(g)-> base` forces `g = R.one`.  `invertLam`
    sends the body `x = var 0` to the singleton var-grade `single … R.one = cons R.one nil`, while the
    lambda carries the binder grade as `cons g nil`; `cons`-injectivity then forces `g = R.one`.  The
    identity GENUINELY uses its argument — its binder grade cannot be anything else.

  * **`kSecondBinderGradeForcedZero`** — `λx.λy.x : base -(g₁)-> (base -(g₂)-> base)` forces
    `g₂ = R.zero`.  The body `var 1` skips the innermost binder, so its var-grade is
    `single … (at index 1) R.one = cons R.zero (cons R.one nil)`; the `R.zero` head pins the dropped
    binder's grade.  The discard is recorded EXACTLY — `y` is provably unused (grade `0`), not merely
    "at most used".

  * **`usageIdentityNotDiscardable` / `securityIdentityNotDiscardable`** — the concrete payoff in two
    dimensions: the identity CANNOT be typed as a discard (binder grade `R.zero`), because that would
    force `R.zero = R.one`, refuted by `UsageGrade`/`SecurityGrade` constructor no-confusion (`0 ≠ 1`,
    `unclassified ≠ classified`).  Grade forgery — passing off a using function as a discarding one — is
    structurally rejected, in every dimension where `0 ≠ 1`.

## Zero-axiom verification

`HasGradeOver.invertLam` / `invertVar` (shipped, `cases` + `rfl`), `injection` on the arrow and on the
`GradeVectorOver.cons` equalities (plain-inductive constructor discrimination), `dsimp only` on the
structural `single`/`zero`/`List.length` defs to reduce the singleton var-grade, `Eq.trans` to chain,
`subst` of the existential codomain (so the inner `invertLam` sees a constructor head), and
`UsageGrade.noConfusion` / `SecurityGrade.noConfusion` for `0 ≠ 1`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (every declaration probed with `#print axioms`
before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **The identity's binder grade is forced to `R.one`.**  A derivation of `λx.x` at type
`base -(binderGrade)-> base` pins `binderGrade = R.one`: `invertVar` on the body `var 0` yields the
singleton var-grade `cons R.one nil`, while `invertLam` carries the binder as `cons binderGrade nil`, so
`cons`-injectivity forces equality.  No subsumption rule means the grade is synthesised exactly — the
identity provably USES its argument. -/
theorem identityBinderGradeForcedOne {R : OrderedGradeSemiring} {binderGrade : R.Carrier}
    (typed : HasGradeOver R [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow binderGrade GTypeOver.base GTypeOver.base)) :
    binderGrade = R.one := by
  obtain ⟨_bg, _dom, _cod, arrowEq, bodyTyped⟩ := HasGradeOver.invertLam typed
  obtain ⟨_lookupOk, gradesEq⟩ := HasGradeOver.invertVar bodyTyped
  injection arrowEq with bgEq
  dsimp only [List.length, GradeVectorOver.single, GradeVectorOver.zero] at gradesEq
  injection gradesEq with bgOneEq
  exact bgEq.trans bgOneEq

/-- **The K combinator's dropped binder is forced to `R.zero`.**  A derivation of `λx.λy.x` at
`base -(g₁)-> (base -(g₂)-> base)` pins `g₂ = R.zero`: the body `var 1` skips the innermost binder, so
`invertVar` yields the var-grade `cons R.zero (cons R.one nil)`, whose `R.zero` head fixes the dropped
binder's grade.  The discard is recorded EXACTLY — `y` is provably unused. -/
theorem kSecondBinderGradeForcedZero {R : OrderedGradeSemiring}
    {firstBinderGrade secondBinderGrade : R.Carrier}
    (typed : HasGradeOver R [] GradeVectorOver.nil (.lam (.lam (.var 1)))
      (.arrow firstBinderGrade GTypeOver.base
        (.arrow secondBinderGrade GTypeOver.base GTypeOver.base))) :
    secondBinderGrade = R.zero := by
  obtain ⟨_outerBg, _outerDom, outerCod, outerArrowEq, innerBodyTyped⟩ := HasGradeOver.invertLam typed
  injection outerArrowEq with _outerBgEq _outerDomEq outerCodEq
  subst outerCod
  obtain ⟨_innerBg, _innerDom, _innerCod, innerArrowEq, varTyped⟩ := HasGradeOver.invertLam innerBodyTyped
  injection innerArrowEq with innerBgEq
  obtain ⟨_lookupOk, gradesEq⟩ := HasGradeOver.invertVar varTyped
  dsimp only [List.length, GradeVectorOver.single, GradeVectorOver.zero] at gradesEq
  injection gradesEq with innerZeroEq
  exact innerBgEq.trans innerZeroEq

/-- **Usage dimension: the identity is not discardable.**  `λx.x` cannot be typed at binder grade
`UsageGrade.zero` (a discard), since `identityBinderGradeForcedOne` would force `zero = one`, refuted by
`UsageGrade` no-confusion.  The linear discipline rejects passing off a using function as a discarding
one. -/
theorem usageIdentityNotDiscardable :
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow fxUsageSemiring.zero GTypeOver.base GTypeOver.base) := by
  intro typed
  have gradeEq : fxUsageSemiring.zero = fxUsageSemiring.one := identityBinderGradeForcedOne typed
  exact UsageGrade.noConfusion gradeEq

/-- **Security dimension: the identity is not discardable.**  The same forcing fires at
`fxSecuritySemiring`: `λx.x` cannot be typed at binder grade `SecurityGrade.unclassified` (= `R.zero`),
since that forces `unclassified = classified`, refuted by `SecurityGrade` no-confusion.  Grade honesty
holds in every dimension where `0 ≠ 1`. -/
theorem securityIdentityNotDiscardable :
    ¬ HasGradeOver fxSecuritySemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow fxSecuritySemiring.zero GTypeOver.base GTypeOver.base) := by
  intro typed
  have gradeEq : fxSecuritySemiring.zero = fxSecuritySemiring.one := identityBinderGradeForcedOne typed
  exact SecurityGrade.noConfusion gradeEq

end FX1Poly.Modal
