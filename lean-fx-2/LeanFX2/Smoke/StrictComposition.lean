import LeanFX2.Term
import LeanFX2.Reduction.Step
import LeanFX2.Graded.Rules
import LeanFX2.Graded.Dimensions21
import LeanFX2.Graded.Instances.Usage
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext
import LeanFX2.Tools.StrictHarness

/-! # Smoke/StrictComposition — end-to-end strict-discipline smoke

A small composition that touches multiple kernel layers and verifies
the strict harness cleanly accepts all of them.  If any layer
regresses (axiom leak, noncomputable creep, raw/typed parity drift),
this composition smoke turns red even when isolated audits pass.

Layers exercised:

* `Term` — typed kernel terms over the empty context
* `Graded.Rules` — Wood/Atkey 2022 corrected Lam compatibility predicate
* `Graded.GradeAttribution` — recursive-Type attribution carrier

Every shipped declaration in this file must pass `#assert_no_axioms`,
demonstrating that gluing real kernel pieces together still avoids
axioms / classical references / noncomputable creep. -/

namespace LeanFX2.Smoke.StrictComposition

open LeanFX2

/-! ## Layer 1: Term — typed kernel construction over empty context. -/

/-- The unit term in the empty observational context, level 1. -/
def termOfUnitInEmptyObservationalCtx :
    Term (Ctx.empty (mode := Mode.observational) (level := 1))
      (Ty.unit : Ty 1 0)
      RawTerm.unit :=
  Term.unit

/-- Boolean true in the same context. -/
def termOfBoolTrueInEmptyObservationalCtx :
    Term (Ctx.empty (mode := Mode.observational) (level := 1))
      (Ty.bool : Ty 1 0)
      RawTerm.boolTrue :=
  Term.boolTrue

/-! ## Layer 2: Graded — empty grade attribution at scope 0.

The empty grade attribution is the load-bearing base case for the
Wood/Atkey 2022 grade machinery: every kernel decl that does not use
any binding has the empty attribution.  Building it explicitly here
exercises the recursive-Type encoding (`Unit` at scope 0). -/

/-- Empty grade attribution at scope 0 over the empty dimension list. -/
def emptyGradeAttribution :
    LeanFX2.Graded.GradeAttribution (dims := []) 0 :=
  ()

/-- Empty grade attribution at scope 1 — represents a lambda body that
references its single binder at zero grade.  This pair shape is the
target of Wood/Atkey's context-division rule. -/
def emptyGradeAttributionAtScopeOne :
    LeanFX2.Graded.GradeAttribution (dims := []) 1 :=
  ((), ())

/-! ## Layer 3: Wood/Atkey Lam compatibility witness.

A trivial `IsLamCompatible` instance over the empty dimension list:
the body's empty attribution decomposes as the empty pair.  This
exercises the predicate's body shape without committing to any
specific grade structure. -/

/-- Trivial Lam-compatibility witness at the empty dimensions. -/
theorem trivialLamCompatibilityWitness :
    LeanFX2.Graded.IsLamCompatible
      (dims := []) (scope := 0)
      (paramGrade := LeanFX2.Graded.GradeVector.zero)
      (closureGrade := LeanFX2.Graded.GradeVector.zero)
      (bodyAttr := emptyGradeAttributionAtScopeOne)
      (lamAttr := emptyGradeAttribution) :=
  rfl

/-! ## Strict-discipline gates over this composition. -/

#assert_no_axioms LeanFX2.Smoke.StrictComposition.termOfUnitInEmptyObservationalCtx
#assert_no_axioms LeanFX2.Smoke.StrictComposition.termOfBoolTrueInEmptyObservationalCtx
#assert_no_axioms LeanFX2.Smoke.StrictComposition.emptyGradeAttribution
#assert_no_axioms LeanFX2.Smoke.StrictComposition.emptyGradeAttributionAtScopeOne
#assert_no_axioms LeanFX2.Smoke.StrictComposition.trivialLamCompatibilityWitness

end LeanFX2.Smoke.StrictComposition
