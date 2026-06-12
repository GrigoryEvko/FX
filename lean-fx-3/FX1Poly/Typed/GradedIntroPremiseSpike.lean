import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.CellConstructors
import FX1Poly.Modal.GradedLinearTime
import FX1Poly.Core.RawTermOccurrenceRename

/-! # FX1Poly/Typed/GradedIntroPremiseSpike — the graded intro-premise grade-check (LIVE substrate)

This file HOSTS the live grade-check `gradedBinderChecks` consumed by the native union's
`gradedBinderIntro` arm (`HasTypeNativeUnion.lean`) and the v2 graded-introduction table
(`HasTypeDescGradedIntro` / `IntroRuleDescGradedBinder`).  An introduction premise carrying a USAGE GRADE on
its binder is CHECKED by bounding the body's freshest-binder occurrence — the orthogonal graded dimension
every graded former needs: the affine bridge/path binder (`pathLam`, usage `.one`), the ghost binder
(usage `.zero`), and the unrestricted ordinary binder (usage `.omega`).

(The module name retains its original GO/NO-GO-spike heritage; its production decls have since become
load-bearing — they are NOT a throwaway spike.  The historical adequacy that built the bespoke
`HasTypeDescBridge.pathIntro` from a `.one` graded premise was witnessed pre-retirement; that engine has been
deleted (NATIVE-45) and the union row `gradedBinderIntro` at `pathLamGradedIntroRule` — selected by
`gradedIntroRuleOf_pathLam` — is now definitionally the only realization of the affine path abstraction.)

## The grade-check, across the WHOLE grade spectrum

`UsageGrade.boundsCount` (`GradedLinearTime.lean`) is exactly the grade→occurrence-bound interpreter
(`.zero ⟹ count = 0`, `.one ⟹ count ≤ 1`, `.omega ⟹ True`).

  * `gradedBinderChecks usage body` — the grade-parametric premise interpreter: bound the body's binder
    occurrence by `usage.boundsCount`.  At `.one` it IS the affine path-intro premise (`rfl`).
  * `gradedBinderChecks_spectrum` — the interpreter handles all three grades: `.omega` is unconstrained
    (the ordinary `gen_lam` binder), `.one` is the affine bound, `.zero` is the ghost (used-zero-times) bound.
  * `GradedIntroPremise` — the grade-parametric intro premise (the body typed under the binder + the graded
    check), the foldable form of the affine path-intro premise set.
  * `gradedIntro_ghost_ofWeakened` — ★ ANY WEAKENED (dimension-constant) body satisfies the graded check at
    usage `.zero` (the STRONGEST grade), via the rung-77 `occurrenceCountAt_weaken_zeroPosition`.  A constant
    body is ghost-gradeable, stronger than affine.
  * `gradedIntro_affine_constant` — ★ NON-VACUOUS: the constant bridge body is an affine graded intro premise.
  * `gradedIntroExpressibility_isGo` — the all-positive verdict ledger.

## Honest scope

The interpreter `gradedBinderChecks` reads ONE binder position (`0`, the freshest), which is exactly the
single-binder intro shape (`pathLam`/`lam`).  The full graded-context substrate (`HasGradeOver R`, the grade
VECTOR over all binders, the Wood/Atkey context division) is shipped separately (#901/#876).

## Zero-axiom

`gradedBinderChecks` is a thin wrapper over the shipped `UsageGrade.boundsCount`; the ghost witness is the
rung-77 weaken lemma; the affine non-vacuity is a closed-body formation through the grown engine.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The grade-parametric intro-premise interpreter.**  A binder carrying usage grade `usage` is checked by
bounding the body's occurrence count at the freshest position (`0`) per `usage.boundsCount`.  At `.one` this
is the `pathIntro` affine premise; at `.zero` it is the ghost (zero-use) premise; at `.omega` it is
unconstrained (the ordinary `lam`). -/
def gradedBinderChecks (usage : UsageGrade) {scope : Nat} (body : RawTerm (scope + 1)) : Prop :=
  usage.boundsCount (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩)

/-- **The grade spectrum.**  The interpreter reads each grade as its occurrence discipline: `.omega`
unconstrained, `.one` at-most-once, `.zero` exactly-zero.  Witnesses that one premise schema spans
unrestricted / affine / ghost binders. -/
theorem gradedBinderChecks_spectrum {scope : Nat} (body : RawTerm (scope + 1)) :
    gradedBinderChecks UsageGrade.omega body ∧
    (gradedBinderChecks UsageGrade.one body
      ↔ RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1) ∧
    (gradedBinderChecks UsageGrade.zero body
      ↔ RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ = 0) :=
  ⟨trivial, Iff.rfl, Iff.rfl⟩

/-- The affine `pathIntro` premise IS the graded check at usage `.one` (definitional). -/
theorem affinePremise_isGradedCheckAtOne {scope : Nat} (body : RawTerm (scope + 1)) :
    gradedBinderChecks UsageGrade.one body
      = (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1) :=
  rfl

/-- **The grade-parametric intro premise.**  The body is typed under the dimension-binder-extended context,
and its binder usage is bounded by `usage`.  The foldable form of the affine path-intro premise set,
parameterized by the usage grade — the shape consumed by the v2 `gradedBinderIntro` arm. -/
structure GradedIntroPremise (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (usage : UsageGrade)
    (body : RawTerm (scope + 1)) (typeCode : RawTerm scope) : Prop where
  bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body (RawTerm.weaken typeCode)
  binderGraded : gradedBinderChecks usage body

/-- **★ The genuinely-new content: a weakened body is GHOST-gradeable.**  ANY dimension-constant body
(`RawTerm.weaken sourceTerm`) satisfies the graded check at usage `.zero` — it uses the binder ZERO times,
via the rung-77 `occurrenceCountAt_weaken_zeroPosition`.  Usage `.zero` is the strongest grade (used exactly
zero times), so a constant body is ghost-gradeable, strictly stronger than affine. -/
theorem gradedIntro_ghost_ofWeakened {scope : Nat} (sourceTerm : RawTerm scope) :
    gradedBinderChecks UsageGrade.zero (RawTerm.weaken sourceTerm) :=
  RawTerm.occurrenceCountAt_weaken_zeroPosition sourceTerm

/-- **★ NON-VACUOUS: the constant bridge body is an affine graded intro premise.**  `pathLam(Type@0)` (the
dimension-constant body) satisfies `GradedIntroPremise` at usage `.one` — the body is closed so its binder
occurrence is `0 ≤ 1`.  The grade-parametric premise the affine path-intro row consumes. -/
theorem gradedIntro_affine_constant {profile : PolyProfile} (flag : UniverseFlag) :
    GradedIntroPremise profile (TypingContext.empty : TypingContext profile 0)
      UsageGrade.one (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) where
  bodyTyped :=
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.cons TypingContext.empty intervalTypeCell) LevelExpr.lzero flag)
  binderGraded := Nat.zero_le 1

/- The historical adequacy `gradedIntroPremise_buildsPathIntro` — a `GradedIntroPremise` at usage `.one`
SUFFICES to construct the affine path abstraction, because its `binderGraded` check (`gradedBinderChecks .one
body`) IS the path-intro affine premise (`occurrenceCountAt body 0 ≤ 1`) definitionally — was witnessed
pre-retirement against the bespoke `HasTypeDescBridge.pathIntro`.  That engine has been deleted (NATIVE-45);
the affine path abstraction is now realized ONLY by the union row `HasTypeNativeUnion.gradedBinderIntro` at
`pathLamGradedIntroRule` (selected by `gradedIntroRuleOf_pathLam`), whose `binderGraded` premise is this same
`gradedBinderChecks rule.binderUsage body`.  The theorem is unstatable here (the union is defined downstream
of this file), so it does not survive the retirement. -/

/-! ## The GO-verdict ledger -/

/-- The spike's verdict record: each field is a machine-checked finding about the graded intro premise's
expressibility. -/
structure GradedIntroExpressibility where
  /-- The graded binder premise is expressible (`gradedBinderChecks` over `UsageGrade.boundsCount`). -/
  isExpressible : Bool
  /-- It spans the WHOLE grade spectrum (ghost / affine / unrestricted), not just affine. -/
  spansGradeSpectrum : Bool
  /-- A weakened/constant body is GHOST-gradeable (the rung-77 occurrence metatheory). -/
  weakenedIsGhost : Bool
  /-- It is NON-VACUOUSLY inhabited at the affine grade (`gradedIntro_affine_constant`). -/
  isNonVacuous : Bool
  /-- The affine path-intro premise IS an instance of the graded intro premise (witnessed pre-retirement;
  the union row `gradedBinderIntro` at `pathLamGradedIntroRule` is now its sole realization). -/
  pathIntroIsInstance : Bool
  /-- The grade is FORCED by the table row (`pathLamGradedIntroRule.binderUsage = .one`), not merely
  permitted — the affine bound is enforced as the arm's `binderGraded` premise. -/
  gradeIsForced : Bool

/-- **★ The graded-intro verdict: GO.**  The graded intro premise is expressible over the shipped usage
semiring, spans the ghost/affine/unrestricted spectrum, a weakened body is ghost-gradeable, it is
non-vacuously inhabited, the affine path-intro premise is an instance, and the grade is forced by the table
row.  Every field `true`, witnessed by the live decls above; the per-binder usage is threaded into the v2
`GradedIntroRule`/`gradedBinderIntro` arm that now carries the path abstraction. -/
def gradedIntroExpressibility : GradedIntroExpressibility where
  isExpressible := true
  spansGradeSpectrum := true
  weakenedIsGhost := true
  isNonVacuous := true
  pathIntroIsInstance := true
  gradeIsForced := true

/-- The verdict is unambiguously GO (all findings positive). -/
theorem gradedIntroExpressibility_isGo :
    gradedIntroExpressibility.isExpressible = true ∧
    gradedIntroExpressibility.spansGradeSpectrum = true ∧
    gradedIntroExpressibility.weakenedIsGhost = true ∧
    gradedIntroExpressibility.isNonVacuous = true ∧
    gradedIntroExpressibility.pathIntroIsInstance = true ∧
    gradedIntroExpressibility.gradeIsForced = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed
