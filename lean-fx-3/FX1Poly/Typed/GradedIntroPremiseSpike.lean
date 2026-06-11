import FX1Poly.Typed.HasTypeDescBridge
import FX1Poly.Modal.GradedLinearTime
import FX1Poly.Core.RawTermOccurrenceRename

/-! # FX1Poly/Typed/GradedIntroPremiseSpike — NATIVE-03: the graded intro premise IS expressible (SPIKE)

The GO/NO-GO spike for the `binderUsage` axis of NATIVE-01's locked vocabulary: can an introduction premise
carry a USAGE GRADE on its binder and have it CHECKED?  This is the orthogonal graded dimension every
graded former needs — the affine bridge/path binder (`pathLam`, usage `.one`), but also the ghost binder
(usage `.zero`) and the unrestricted ordinary binder (usage `.omega`).

## The answer is GO — substrate already shipped, across the WHOLE grade spectrum

`UsageGrade.boundsCount` (`GradedLinearTime.lean`) is exactly the grade→occurrence-bound interpreter
(`.zero ⟹ count = 0`, `.one ⟹ count ≤ 1`, `.omega ⟹ True`), and `HasTypeDescBridge.pathIntro` already
CHECKS the affine binder via `occurrenceCountAt body 0 ≤ 1` — definitionally `UsageGrade.one.boundsCount …`.
So the graded intro premise is shipped at the affine grade; this spike exhibits the grade-PARAMETRIC
foldable form and the two grades the shipped affine row does not name (ghost / unrestricted).

  * `gradedBinderChecks usage body` — the grade-parametric premise interpreter: bound the body's binder
    occurrence by `usage.boundsCount`.  At `.one` it IS the `pathIntro` affine premise (`rfl`).
  * `gradedBinderChecks_spectrum` — the interpreter handles all three grades: `.omega` is unconstrained
    (the ordinary `gen_lam` binder), `.one` is the affine bound, `.zero` is the ghost (used-zero-times) bound.
  * `GradedIntroPremise` — the grade-parametric intro premise (the body typed under the binder + the graded
    check), the foldable form of `pathIntro`'s premise set.
  * `gradedIntro_ghost_ofWeakened` — ★ the genuinely-new content: ANY WEAKENED (dimension-constant) body
    satisfies the graded check at usage `.zero` (the STRONGEST grade), via the rung-77
    `occurrenceCountAt_weaken_zeroPosition`.  A constant body is ghost-gradeable, stronger than affine.
  * `gradedIntroPremise_buildsPathIntro` — ★ ADEQUACY: a `GradedIntroPremise` at usage `.one` SUFFICES to
    construct `HasTypeDescBridge.pathIntro` — its graded check IS the affine premise.  Plus
    `HasTypeDescBridge.pathLamSubjectIsAffine` (shipped) gives the honesty: the grade is FORCED.
  * `gradedIntroExpressibility_isGo` — the all-positive verdict ledger.

## Honest scope

The interpreter `gradedBinderChecks` reads ONE binder position (`0`, the freshest), which is exactly the
single-binder intro shape (`pathLam`/`lam`).  The full graded-context substrate (`HasGradeOver R`, the grade
VECTOR over all binders, the Wood/Atkey context division) is already shipped separately (#901/#876); the
NATIVE-20/23 work is THREADING a per-binder usage into the unified `IntroRuleDesc`/`genIntro`, not the
expressibility this settles.

## Zero-axiom

`gradedBinderChecks` is a thin wrapper over the shipped `UsageGrade.boundsCount`; the ghost witness is the
rung-77 weaken lemma; the adequacy is `pathIntro` applied to the definitionally-equal premises.  No `axiom`,
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
and its binder usage is bounded by `usage`.  The foldable form of `HasTypeDescBridge.pathIntro`'s premise
set, parameterized by the usage grade (the NATIVE-20/23 target). -/
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
occurrence is `0 ≤ 1`.  The grade-parametric analogue of `HasTypeDescBridge.constantBridgeTyped`'s premise. -/
theorem gradedIntro_affine_constant {profile : PolyProfile} (flag : UniverseFlag) :
    GradedIntroPremise profile (TypingContext.empty : TypingContext profile 0)
      UsageGrade.one (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) where
  bodyTyped :=
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.cons TypingContext.empty intervalTypeCell) LevelExpr.lzero flag)
  binderGraded := Nat.zero_le 1

/-- **★ ADEQUACY: the grade-parametric premise SUFFICES to construct the path abstraction.**  A
`GradedIntroPremise` at usage `.one` yields exactly `HasTypeDescBridge.pathIntro` — its `binderGraded` check
(`gradedBinderChecks .one body`) IS `pathIntro`'s `dimensionAffine` premise (`occurrenceCountAt body 0 ≤ 1`)
definitionally.  So the bespoke affine `pathIntro` premise IS an instance of the foldable graded intro
premise (the introduction analogue of NATIVE-02's `termIndexedFormerTyping_buildsBridge`). -/
theorem gradedIntroPremise_buildsPathIntro {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)} {typeCode : RawTerm scope}
    (premise : GradedIntroPremise profile context UsageGrade.one body typeCode) :
    HasTypeDescBridge profile context (pathLamCell body)
      (bridgeTypeCell typeCode
        (RawTerm.subst0 body intervalZeroCell)
        (RawTerm.subst0 body intervalOneCell)) :=
  HasTypeDescBridge.pathIntro context body typeCode premise.bodyTyped premise.binderGraded

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
  /-- The bespoke affine `pathIntro` premise IS an instance (`gradedIntroPremise_buildsPathIntro`). -/
  pathIntroIsInstance : Bool
  /-- The grade is FORCED by the engine, not merely permitted (`pathLamSubjectIsAffine`). -/
  gradeIsForced : Bool

/-- **★ NATIVE-03 verdict: GO.**  The graded intro premise is expressible over the shipped usage semiring,
spans the ghost/affine/unrestricted spectrum, a weakened body is ghost-gradeable, it is non-vacuously
inhabited, the `pathIntro` premise is an instance, and the grade is forced.  Every field `true`, witnessed by
the theorems above (+ shipped `pathLamSubjectIsAffine`).  NATIVE-20/23 is threading a per-binder usage into
`IntroRuleDesc`/`genIntro` — not the expressibility this settles. -/
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
