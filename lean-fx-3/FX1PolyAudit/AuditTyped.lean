import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TypingContext
import FX1Poly.Typed.HasType
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing
import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.HasTypeDecidableConv
import FX1Poly.Typed.HasTypeSubjectReduction
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.IsTypeDecidable
import FX1Poly.Typed.HasTypeDecidable

/-! # Tools/AuditAll/AuditTyped
   — persistent per-declaration zero-axiom gate for the typed layer

The typed layer (polycell.md §11.8.5) is the dim-0 soundness stratum: the
`.context` / `.type` / `.term` cells that classify each other.  Its first
brick is the native `TypingContext` de Bruijn telescope (TY-CTX, the
lean-fx-3 re-port of lean-fx-2's M31/M32) — the `.context`-sort spine the
`HasType` engine consumes via the variable rule.

Every declaration here must elaborate without `propext`, `Classical.choice`,
`Quot.sound`, or `sorryAx` — so any future edit that introduces an axiom
dependency fails `lake build FX1PolyAudit` immediately.  The `lookup`
de Bruijn destructuring and `length_eq_scope` induction are the two places
a careless rewrite could pull `propext` through the match compiler; these
gates pin them shut.
-/

/-! ### TY-CTX #467 — native TypingContext telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### TY-ENGINE #282 first slice — HasType var + conv core + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.HasType
#assert_no_axioms FX1Poly.Typed.IsType

/-! ### TY-honesty #470 first slice — 0-false-positive probe (ill-typed cell has no derivation) -/

#assert_no_axioms FX1Poly.Typed.unitCell
#assert_no_axioms FX1Poly.Typed.appUnitUnit
#assert_no_axioms FX1Poly.Typed.RawTerm.headGenerator
#assert_no_axioms FX1Poly.Typed.HasType.typedSubjectIsVariableOrUniverseCode
#assert_no_axioms FX1Poly.Typed.appUnitUnit_hasNoTyping

/-! ### TY-WF #468 — WfContext predicate + inversions + non-vacuity witness -/

#assert_no_axioms FX1Poly.Typed.WfContext
#assert_no_axioms FX1Poly.Typed.WfContext.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.headIsType
#assert_no_axioms FX1Poly.Typed.wfContext_universeBinding

/-! ### TY-SR-cong #456 — typed renaming + weakening (structural cartesian lift) -/

#assert_no_axioms FX1Poly.Typed.rename_variableCell
#assert_no_axioms FX1Poly.Typed.rename_universeCodeCell
#assert_no_axioms FX1Poly.Typed.HasType.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.weakenUnderBinding

/-! ### TY-SR-beta engine #457 — typed single-substitution (subst0 preserves typing) -/

#assert_no_axioms FX1Poly.Typed.subst_variableCell
#assert_no_axioms FX1Poly.Typed.subst_universeCodeCell
#assert_no_axioms FX1Poly.Typed.subst_singleton_renameWeaken_cancel
#assert_no_axioms FX1Poly.Typed.HasType.substRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.substituteUnderBinding

/-! ### TY-VALIDITY (P3) #468 — IsType stability + lookup-is-type + classifier-is-a-type -/

#assert_no_axioms FX1Poly.Typed.IsType.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.IsType.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContext.lookupIsType
#assert_no_axioms FX1Poly.Typed.HasType.classifierIsType

/-! ### FUNDAMENTAL THEOREM (M10, current fragment) + typed Conv.trans payoff -/

#assert_no_axioms FX1Poly.Typed.HasType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_typedMiddle

/-! ### INVERSION (#454, current fragment) — per-shape classifier characterization -/

#assert_no_axioms FX1Poly.Typed.HasType.inversionVariable
#assert_no_axioms FX1Poly.Typed.HasType.inversionUniverseCode

/-! ### UNIQUENESS OF TYPING (#469, current fragment) -/

#assert_no_axioms FX1Poly.Typed.HasType.uniqueness

/-! ### DECIDABLE TYPE CONVERSION (current fragment) — normal-form rigidity →
    decidable Conv.  Core rigidity (`StepStar.eq_of_noStep`, `Conv.eq_of_noStep`,
    `Conv.iff_eq_of_noStep`) is swept by `#audit_namespace FX1Poly.Core` in
    `AuditCoreSubstrate.lean`; the typed payoff is pinned per-decl here. -/

#assert_no_axioms FX1Poly.Typed.IsType.hasNoStep
#assert_no_axioms FX1Poly.Typed.Conv.eq_of_isType
#assert_no_axioms FX1Poly.Typed.Conv.iff_eq_of_isType
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfIsType

/-! ### TYPED SUBJECT REDUCTION (P4 #458, current fragment) — `subjectHasNoStep`
    is the real structural invariant (well-typed subjects are normal leaves);
    SR itself holds vacuously over the leaf-only fragment until app/iota arms
    land (#444), then routes through the substitution lemma (#457). -/

#assert_no_axioms FX1Poly.Typed.HasType.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasType.subjectReduction

/-! ### UNIVERSE-CODE CELL DESTRUCTOR (#303 groundwork) — recovers
    `universeCodeCell e flag` from `headGenerator = gen_universeCode` via the
    `RawTermChildren.eq_childNil` brick; the raw destructor `Decidable IsType`
    needs to apply `HasType.universeFormation`. -/

#assert_no_axioms FX1Poly.Typed.eq_universeCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.eq_variableCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.headGenerator_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headGenerator_variableCell

/-! ### IsType CHARACTERIZATION (#303 heart) — the decidable trichotomy on the
    head generator that `Decidable IsType` assembles: universe codes are always
    types; a variable is a type iff its looked-up classifier is a universe code
    (forward by `inversionVariable` + rigidity); any other head is never a type
    (`typedSubjectIsVariableOrUniverseCode`). -/

#assert_no_axioms FX1Poly.Typed.IsType.ofUniverseCodeCell
#assert_no_axioms FX1Poly.Typed.IsType.variableCell_iff_lookupIsUniverseCode
#assert_no_axioms FX1Poly.Typed.IsType.not_of_headGenerator

/-! ### DECIDABLE IsType (#303, current fragment) — the decision procedure
    assembled over the trichotomy: case on the cell (payload = index as data),
    `dite` on the head generator (`DecidableEq Generator`, no `Classical`). -/

#assert_no_axioms FX1Poly.Typed.IsType.decidableOfWellFormed

/-! ### HasType CHARACTERIZATION (#461 heart) — typed checking collapses to
    classifier equality: validity makes the classifier normal, so the inversions
    + rigidity turn `HasType Γ subject T` into `T = (the unique classifier)`.
    No `Conv` decision / normalizer needed for this fragment. -/

#assert_no_axioms FX1Poly.Typed.HasType.variableCell_iff_classifierEqLookup
#assert_no_axioms FX1Poly.Typed.HasType.universeCodeCell_iff_classifierEqSucc
#assert_no_axioms FX1Poly.Typed.HasType.not_of_headGenerator

/-! ### DECIDABLE HasType (#461/#302, current fragment) — typed checking decision
    procedure assembled over the classifier-equality characterization; mirror of
    `IsType.decidableOfWellFormed`, deciding via `DecidableEq RawTerm`. -/

#assert_no_axioms FX1Poly.Typed.HasType.decidableOfWellFormed
