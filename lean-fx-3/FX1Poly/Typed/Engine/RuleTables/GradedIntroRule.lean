import FX1Poly.Typed.Cell.CellShorthands
import FX1Poly.Tier0.Mode.GradeAlgebra.ResourceGraded
import FX1Poly.Tier0.Term.Core.RawTermFreeVars

/-! # FX1Poly/Typed/Engine/RuleTables/GradedIntroRule — the v2 graded-introduction table (live rule-data)

The pure-syntax introduction-rule descriptor `GradedIntroRule`, its two rows (`lamGradedIntroRule` /
`pathLamGradedIntroRule`), the dispatch table `gradedIntroRuleOf`, and its metadata lemmas — extracted
out of the (deprecated) graded-intro engine module `HasTypeDescGradedIntro` so the native union and the
RuleTables bundle read the rule DATA without importing a dead typing engine.  The description-driven
introduction JUDGMENT that once consumed this table lives (dead) in the old engine module; the live
substrate reads only the table below.

  * `GradedIntroRule` — the v2 schema: per-row `domainCell`, `bodyClassifier`, `memberCell`, the
    BODY-DEPENDENT `outputType`, the `binderUsage` grade, and two premise-selection `Bool` gates.
  * `lamGradedIntroRule` — the unrestricted λ row (`.omega`).
  * `pathLamGradedIntroRule` — the affine pathLam row (`.one`), the first non-`.omega` introduction row.
  * `gradedIntroRuleOf` — the two-row dispatch table (`gen_lam` / `gen_pathLam`).
  * `gradedIntroRuleOf_lam` / `gradedIntroRuleOf_pathLam` / `gradedIntroRuleOf_pathLamUsageIsOne` /
    `gradedIntroRuleOf_isLamOrPathLam` — the table-metadata lemmas every dispatch consumer routes through.
  * `doubleDimensionUseBody` + `doubleDimensionUseBody_occurrenceIsTwo` — the canonical AFFINE-REJECTION
    witness vector for the pathLam row (the dimension-duplicating body every grade-rejection theorem
    tests against; consumed by the native union inversion and the engine-side rejection alike).

## Zero-axiom

The table is pure syntax; the metadata collapses by `rfl` / `by_cases` + `Option.some.inj` + `if_neg`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/Typed/Engine/RuleTables/GradedIntroRule.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-- **The v2 introduction-rule description (the keystone schema).**  Everything the generic graded
introduction arm needs, as rule DATA: the binder's domain, the body's classifier, the member shape, the
BODY-DEPENDENT output, the usage grade, and the premise-selection gates.  `typeParamA : RawTerm scope`
is the row's scope-level type parameter (λ: the domain; pathLam: the carrier); `typeParamB :
RawTerm (scope+1)` is the row's extended-scope type parameter (λ: the codomain; pathLam: unused).
Pure syntax — strictly positive. -/
structure GradedIntroRule where
  /-- The binder's domain: what the bound variable inhabits.  λ: the parameter itself.
  pathLam: PINNED to `intervalTypeCell` (the parameter is ignored). -/
  domainCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The body's classifier under the domain-extended context.  λ: the codomain parameter.
  pathLam: `weaken` of the carrier parameter. -/
  bodyClassifier : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm (scope + 1)
  /-- The introduced member's shape — rule data, NOT hardwired to `lamCell`.
  λ: `lamCell domain body`.  pathLam: `pathLamCell body` (no domain annotation). -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm scope
  /-- The introduced TYPE — BODY-DEPENDENT (the v1 schema's gap).  λ: `piTyCodeCell domain codomain`
  (ignores the body).  pathLam: `bridgeTypeCell carrier (subst0 body 0) (subst0 body 1)`. -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm (scope + 1) →
    RawTerm scope
  /-- The binder's usage grade (NATIVE-20 axis).  λ: `.omega`.  pathLam: `.one` (affine). -/
  binderUsage : UsageGrade := UsageGrade.omega
  /-- Does the row demand the domain be a well-formed type?  λ: yes (`piIntro` parity).
  pathLam: no (`pathIntro` parity — premise parity is the delete-safety requirement). -/
  demandsDomainFormation : Bool := true
  /-- Does the row demand the body's classifier be a well-formed type?  λ: yes.  pathLam: no. -/
  demandsClassifierFormation : Bool := true

/-- The λ row: domain is the parameter, classifier is the codomain parameter, member is the annotated
`lamCell`, output is the (body-independent) Π code, binder unrestricted, both formation premises
demanded — exactly `HasTypeDescPi.piIntro`. -/
def lamGradedIntroRule : GradedIntroRule where
  domainCell := fun _ domainCode => domainCode
  bodyClassifier := fun _ _ codomainCode => codomainCode
  memberCell := fun _ domainCode body => lamCell domainCode body
  outputType := fun _ domainCode codomainCode _ => piTyCodeCell domainCode codomainCode
  binderUsage := UsageGrade.omega
  demandsDomainFormation := true
  demandsClassifierFormation := true

/-- The pathLam row — the FIRST affine introduction row.  Domain PINNED to the interval, classifier is
the weakened carrier, member is the annotation-free `pathLamCell`, output is the BODY-DEPENDENT bridge
code at the body's endpoint substitutions, binder AFFINE (`.one`), no formation premises — the affine path
abstraction (formerly the bespoke `HasTypeDescBridge.pathIntro`, retired NATIVE-45; this row is now its
realization, fed to the downstream uniform `HasTypeUnion.intro` builder). -/
def pathLamGradedIntroRule : GradedIntroRule where
  domainCell := fun _ _ => intervalTypeCell
  bodyClassifier := fun _ carrierCode _ => RawTerm.weaken carrierCode
  memberCell := fun _ _ body => pathLamCell body
  outputType := fun _ carrierCode _ body =>
    bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
      (RawTerm.subst0 body intervalOneCell)
  binderUsage := UsageGrade.one
  demandsDomainFormation := false
  demandsClassifierFormation := false

/-- **The v2 graded introduction table.**  Two rows: the unrestricted λ and the affine pathLam.  A new
introduction former (the data-constructor family, NATIVE-34) is one more row here — never a new arm. -/
def gradedIntroRuleOf (generator : Generator) : Option GradedIntroRule :=
  if generator = .gen_lam then some lamGradedIntroRule
  else if generator = .gen_pathLam then some pathLamGradedIntroRule
  else none

/-! ## Table metadata (cascade-death lemmas) -/

/-- `gen_lam`'s v2 row is the λ rule. -/
theorem gradedIntroRuleOf_lam :
    gradedIntroRuleOf .gen_lam = some lamGradedIntroRule := rfl

/-- `gen_pathLam`'s v2 row is the affine pathLam rule. -/
theorem gradedIntroRuleOf_pathLam :
    gradedIntroRuleOf .gen_pathLam = some pathLamGradedIntroRule := rfl

/-- The pathLam row carries the AFFINE grade — the first non-`.omega` introduction row (the NATIVE-20
graded check stops being inert at this row). -/
theorem gradedIntroRuleOf_pathLamUsageIsOne :
    (gradedIntroRuleOf .gen_pathLam).map (·.binderUsage) = some UsageGrade.one := rfl

/-- **The current v2 introduction table is exactly `{gen_lam, gen_pathLam}`.**  The enumeration lemma
every dispatch consumer routes through (one more disjunct per future row, no per-consumer cascade). -/
theorem gradedIntroRuleOf_isLamOrPathLam {generator : Generator} {rule : GradedIntroRule}
    (isIntro : gradedIntroRuleOf generator = some rule) :
    generator = Generator.gen_lam ∨ generator = Generator.gen_pathLam := by
  by_cases hLam : generator = .gen_lam
  · exact Or.inl hLam
  · by_cases hPath : generator = .gen_pathLam
    · exact Or.inr hPath
    · exfalso
      dsimp only [gradedIntroRuleOf] at isIntro
      rw [if_neg hLam, if_neg hPath] at isIntro
      contradiction

/-! ## The affine-rejection witness vector (the pathLam row's grade test term) -/

/-- The dimension-duplicating body: `pair(var 0, var 0)` uses the freshest binder TWICE. -/
def doubleDimensionUseBody (scope : Nat) : RawTerm (scope + 1) :=
  pairCell (variableCell ⟨0, Nat.succ_pos scope⟩) (variableCell ⟨0, Nat.succ_pos scope⟩)

/-- The dimension-duplicating body's occurrence count at the binder is exactly `2`. -/
theorem doubleDimensionUseBody_occurrenceIsTwo (scope : Nat) :
    RawTerm.occurrenceCountAt (doubleDimensionUseBody scope) ⟨0, Nat.succ_pos scope⟩ = 2 := rfl

end FX1Poly.Typed
