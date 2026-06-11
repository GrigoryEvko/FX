import FX1Poly.Typed.IntroRuleDesc
import FX1Poly.Typed.GradedIntroPremiseSpike

/-! # FX1Poly/Typed/IntroRuleDescGradedBinder — NATIVE-20: genIntro interprets the binder-usage grade

NATIVE-12..19 made the Id/Bridge FORMERS table-driven.  NATIVE-20 pivots to the GRADED INTRO layer.
The `IntroRuleDesc` table now carries a per-binder usage grade (`binderUsage`, NATIVE-20 half 1, in
`IntroRuleDesc.lean`), and the generic introduction dispatcher INTERPRETS it — it reads
`rule.binderUsage` from the table and demands the body satisfy the corresponding occurrence discipline
(`gradedBinderChecks rule.binderUsage body`, the NATIVE-03 grade→occurrence-bound interpreter over
`UsageGrade.boundsCount`).  This is the seam the cubical `pathLam` (affine dimension binder, NATIVE-23)
rows into: the SAME arm that leaves the ordinary `gen_lam` binder unconstrained (`.omega`) enforces
affinity (`.one`) — and ghost discipline (`.zero`) — once a non-`.omega` row lands, with ZERO change.

  * `gradedBinderChecks_omega` — the unrestricted grade imposes no constraint (`.omega.boundsCount _ =
    True`); the discharge for the ordinary λ binder.
  * `gradedBinderChecks_ofGenLamRow` — for the only current intro row (`gen_lam`), the graded premise is
    FREE (`rule.binderUsage = .omega` via `introRuleDescOf_binderUsageIsOmega`).
  * `hasTypeDescPi_gradedGenIntro_dispatchViaTable` — ★ THE graded dispatcher: routes an arbitrary
    intro-carrying generator through the table, demanding `gradedBinderChecks rule.binderUsage body` as
    a usage SIDE-CONDITION on top of the type premises.  The grade is read from the table (interpreted),
    not hardwired; usage is erased of the runtime type (§1.5), so the conclusion is the same typed term
    — the grade GATES admission.  A non-`.omega` row is enforced here with no change.
  * `hasTypeDescPi_gradedGenIntro_genLamConservative` — CONSERVATIVITY: for the current table the graded
    premise discharges for free, so the graded arm types EXACTLY the λ-terms the ungraded arm did — the
    binder-usage field is a conservative extension (no currently-typed λ is rejected).
  * `closedConstantLambdaGradedTyped` — NON-VACUOUS: a concrete closed λ `λ(x:Type@0).Type@0 :
    Π(x:Type@0).Type@1` typed through the graded conservative arm (the field is genuinely read +
    discharged on a real derivation).
  * `gradedBinder_var_passesAffine` / `gradedBinder_var_rejectsGhost` — the interpreter DISCRIMINATES:
    the identity body `var 0` (occurrence exactly 1, `RawTerm.occurrenceCountAt_var_self`) satisfies the
    affine `.one` check (`1 ≤ 1`) but the ghost `.zero` check REJECTS it (`1 ≠ 0`).  The non-vacuity
    that makes "interprets" real — the grade actually constrains; the check is not always-`True`.
  * `GradedIntroDispatchCoverage` + `gradedIntroDispatchCoverageWitness` — the coverage gate (table
    carries the grade / conservative typing / affine-accepts / ghost-rejects), inhabited by the shipped
    witnesses so the exercised property set can NOT silently shrink.

## Zero-axiom

The dispatcher routes through the shipped ungraded `hasTypeDescPi_genIntro_dispatchViaTable`; the grade
discharge is `introRuleDescOf_binderUsageIsOmega` + the definitional `.omega ⟹ True`; the discrimination
is `RawTerm.occurrenceCountAt_var_self` (a variable counts itself once) + `Nat.le_of_eq` /
`Nat.one_ne_zero`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The unrestricted grade imposes no occurrence constraint.**  `gradedBinderChecks .omega body`
unfolds to `UsageGrade.omega.boundsCount _ = True` — the ordinary `gen_lam` binder is unconstrained.
The discharge every `.omega` intro row uses. -/
theorem gradedBinderChecks_omega {scope : Nat} (body : RawTerm (scope + 1)) :
    gradedBinderChecks UsageGrade.omega body :=
  trivial

/-- **For the only current intro row, the graded premise is free.**  `gen_lam` carries
`rule.binderUsage = .omega` (`introRuleDescOf_binderUsageIsOmega`), so its graded check holds for ANY
body — the ordinary λ binder is unconstrained.  The conservativity ingredient. -/
theorem gradedBinderChecks_ofGenLamRow {scope : Nat} {rule : IntroRuleDesc}
    (body : RawTerm (scope + 1))
    (isIntro : introRuleDescOf Generator.gen_lam = some rule) :
    gradedBinderChecks rule.binderUsage body := by
  rw [introRuleDescOf_binderUsageIsOmega isIntro]
  exact gradedBinderChecks_omega body

/-- **★ The graded introduction dispatcher.**  For ANY generator carrying an introduction rule, the
Church-style member `lamCell domainCode body` types at the rule-DATA output, PROVIDED the body satisfies
the table's binder-usage discipline `gradedBinderChecks rule.binderUsage body`.  The usage grade is read
from the table (`rule.binderUsage`) and interpreted as the body's occurrence bound — a SIDE-CONDITION on
top of the ungraded type premises (the type is erased of the grade per §1.5, so the conclusion is the
same typed term; the grade gates admission).  A future non-`.omega` row (the affine `pathLam`,
NATIVE-23) is enforced here with NO change — the cascade-death graded consumer shape. -/
theorem hasTypeDescPi_gradedGenIntro_dispatchViaTable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator} {rule : IntroRuleDesc}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleDescOf generator = some rule)
    (_binderGraded : gradedBinderChecks rule.binderUsage body)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyTyped :
      HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
    HasTypeDescPi profile context (lamCell domainCode body)
      (rule.outputType scope domainCode codomainCode) :=
  -- `_binderGraded` is the usage SIDE-CONDITION read from the table (`rule.binderUsage`); it gates
  -- admission and is erased of the runtime type (§1.5), so the typed term is produced by the ungraded
  -- reconstruction below.  A `.one`/`.zero` row makes `binderGraded` a genuine occurrence bound.
  hasTypeDescPi_genIntro_dispatchViaTable domainLevel codomainLevel flag isIntro
    domainTyped codomainTyped bodyTyped

/-- **Conservativity over the current table.**  For the only current intro row (`gen_lam`) the graded
premise discharges for free (`gradedBinderChecks_ofGenLamRow`), so the graded dispatcher types EXACTLY
the λ-terms the ungraded `hasTypeDescPi_piIntro_viaIntroDesc` did — adding `binderUsage` rejects NO
currently-typed λ.  The graded check is a conservative extension. -/
theorem hasTypeDescPi_gradedGenIntro_genLamConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {rule : IntroRuleDesc}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleDescOf Generator.gen_lam = some rule)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyTyped :
      HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
    HasTypeDescPi profile context (lamCell domainCode body)
      (rule.outputType scope domainCode codomainCode) :=
  hasTypeDescPi_gradedGenIntro_dispatchViaTable domainLevel codomainLevel flag isIntro
    (gradedBinderChecks_ofGenLamRow body isIntro) domainTyped codomainTyped bodyTyped

/-- **★ Non-vacuous: a closed λ typed through the graded arm.**  `λ(x:Type@0).Type@0 :
Π(x:Type@0).Type@1` types via the graded conservative dispatcher — the `binderUsage` field is genuinely
read and discharged (`.omega`, free) on a real derivation.  The constant body `Type@0` ignores the
binder, so it would pass the affine and even the ghost grade too; here the table-supplied grade is
`.omega`. -/
theorem closedConstantLambdaGradedTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  hasTypeDescPi_gradedGenIntro_genLamConservative
    (LevelExpr.lsucc LevelExpr.lzero) (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    introRuleDescOf_lam
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        (LevelExpr.lsucc LevelExpr.lzero) flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation
        (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
        LevelExpr.lzero flag))

/-- **★ The interpreter discriminates (affine accepts).**  The identity body `var 0` occurs exactly once
at the freshest binder (`occurrenceCountAt_var_self`), so it SATISFIES the affine `.one` graded check
(`1 ≤ 1`).  Half of the non-vacuity: the affine row WILL accept a binder-using body. -/
theorem gradedBinder_var_passesAffine {scope : Nat} :
    gradedBinderChecks UsageGrade.one
      (variableCell (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1))) :=
  Nat.le_of_eq (RawTerm.occurrenceCountAt_var_self ⟨0, Nat.succ_pos scope⟩)

/-- **★ The interpreter discriminates (ghost rejects).**  The identity body `var 0` occurs once, so it
FAILS the ghost `.zero` graded check (which demands occurrence `= 0`): `1 ≠ 0`.  The other half of the
non-vacuity — the grade genuinely constrains; `genIntro` does NOT merely demand a vacuous `True`. -/
theorem gradedBinder_var_rejectsGhost {scope : Nat} :
    ¬ gradedBinderChecks UsageGrade.zero
      (variableCell (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1))) :=
  -- `hcheck` defeq `occurrenceCountAt (var 0) 0 = 0`; the variable counts itself once
  -- (`occurrenceCountAt_var_self`, defeq through `variableCell`), so `1 = 0` — `Nat.noConfusion`.
  -- Pure term-mode (no `rw at`/`dsimp at`) keeps it propext-free.
  fun hcheck =>
    Nat.noConfusion
      ((RawTerm.occurrenceCountAt_var_self
        (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1))).symm.trans hcheck)

/-- **The graded intro-dispatch coverage record.**  Each field is a distinct live property of the
binder-usage threading; an inhabitant certifies NATIVE-20 is exercised (the table carries the grade, the
arm interprets it conservatively + non-vacuously, and the interpretation discriminates by grade). -/
structure GradedIntroDispatchCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The table carries the binder usage: the `gen_lam` row's grade is `.omega` (unrestricted). -/
  tableCarriesUsage : ∀ (rule : IntroRuleDesc),
    introRuleDescOf Generator.gen_lam = some rule → rule.binderUsage = UsageGrade.omega
  /-- A closed λ types through the graded arm (non-vacuous, grade read + discharged). -/
  closedLambdaTyped : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
    (lamCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
  /-- The affine grade ACCEPTS the identity body `var 0`. -/
  affineAcceptsIdentity : gradedBinderChecks UsageGrade.one
    (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  /-- The ghost grade REJECTS the identity body `var 0` (the grade-discrimination). -/
  ghostRejectsIdentity : ¬ gradedBinderChecks UsageGrade.zero
    (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))

/-- **★ The coverage gate.**  Inhabits `GradedIntroDispatchCoverage` from the shipped NATIVE-20
witnesses — deleting or renaming any breaks this `def`, so the binder-usage threading's exercised
property set can NOT silently shrink. -/
theorem gradedIntroDispatchCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    GradedIntroDispatchCoverage profile flag where
  tableCarriesUsage := fun _rule h => introRuleDescOf_binderUsageIsOmega h
  closedLambdaTyped := closedConstantLambdaGradedTyped flag
  affineAcceptsIdentity := gradedBinder_var_passesAffine
  ghostRejectsIdentity := gradedBinder_var_rejectsGhost

end FX1Poly.Typed
