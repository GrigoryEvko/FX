import FX1Poly.Typed.Engine.RuleTables.TypingRowDispatch

/-! # FX1Poly/Typed/TypingRoleOrthogonality — TYTAB-1 brick 2.5: the static-side `WfIotaTable`

Brick 1 (`TypingTableBundle`) gathered the nineteen typing dispatchers; brick 2
(`TypingRowDispatch`) collapsed them into ONE lookup, `typingRowsOf`, returning the list of rows a
generator fires.  Brick 2 deliberately returned a LIST and not an `Option`, deferring the soundness
of "exactly one row fires" — role-orthogonality — to a separate certificate.  This module is that
certificate: the static-side analogue of the reduction table's `WfIotaTable` (whose
`elimRootsAvoidHeads` field certifies a redex head double-classifies no rule).

**The right invariant is per role CLASS, not per table.**  The nineteen tables group into three
typing role classes — FORMATION (a generator forms a type), INTRODUCTION (constructs a term),
ELIMINATION (eliminates a term).  The soundness-relevant fact is that no generator inhabits two
DIFFERENT classes: a head is a type-former XOR a constructor XOR an eliminator, so inversion /
canonical-forms know unambiguously which kind of term a `g`-headed cell is.  This holds for ALL 208
generators (`roleClassesAreOrthogonal`, proved by full enumeration, zero-axiom).

**The one within-class duplicate, documented honestly.**  Naive per-table orthogonality
("`typingRowsOf` has length ≤ 1") is FALSE for exactly one generator: `gen_unitCode` fires both
`typingRuleDescOf` (cumulative formation) and `baseTypeRuleDescOf` (base-type) — two tables of the
SAME formation class, both outputting the unit type's classifier `Type@0`.  That is a benign
same-classifier redundancy (`unitCode_overlapsWithinFormationClassOnly`), not a cross-class conflict,
so it never threatens inversion.  Every OTHER generator fires at most one row
(`typingRowsAreUnique_of_ne_unitCode`), which is the unique-row precondition the arm-rebasing brick
consumes.

Zero-axiom: Boolean role predicates, a full-enumeration `cases <;> rfl`, and `List.head?` projection.
Audit-gated in `FX1PolyAudit/AuditTypingRoleOrthogonality.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core (Generator)

/-! ## The three typing role classes -/

/-- A generator plays a FORMATION role (it forms a type) when any formation-class table fires:
the cumulative formers, the flat formers, the nullary base types, or the term-indexed formers. -/
def firesFormationRole (bundle : TypingTableBundle) (generator : Generator) : Bool :=
  (bundle.formation generator).isSome || (bundle.flatFormation generator).isSome
    || (bundle.baseType generator).isSome || (bundle.termIndexedFormer generator).isSome

/-- A generator plays an INTRODUCTION role (it constructs a term) when any intro-class table fires:
the graded binder intro or any of the eight data-constructor tables. -/
def firesIntroRole (bundle : TypingTableBundle) (generator : Generator) : Bool :=
  (bundle.gradedIntro generator).isSome || (bundle.dataIntroNullary generator).isSome
    || (bundle.recursiveDataIntro generator).isSome
    || (bundle.grownDataIntro generator).isSome

/-- A generator plays an ELIMINATION role (it eliminates a term) when any elim-class table fires:
general application or any of the five data-eliminator tables. -/
def firesElimRole (bundle : TypingTableBundle) (generator : Generator) : Bool :=
  (bundle.generalElim generator).isSome || (bundle.recursiveElim generator).isSome
    || (bundle.twoBranchMatch generator).isSome || (bundle.pathInduction generator).isSome
    || (bundle.projection generator).isSome || (bundle.listElim generator).isSome

/-- At most one of the three role classes fires for this generator — no two classes are jointly
active.  This is the per-generator orthogonality predicate; its universal closure is the certificate. -/
def firesAtMostOneRoleClass (bundle : TypingTableBundle) (generator : Generator) : Bool :=
  !(firesFormationRole bundle generator && firesIntroRole bundle generator)
    && !(firesFormationRole bundle generator && firesElimRole bundle generator)
    && !(firesIntroRole bundle generator && firesElimRole bundle generator)

/-! ## The certificate -/

/-- ★ **The typing roles are well-formed** — the static-side `WfIotaTable`.  Its single field
certifies cross-class orthogonality: no generator simultaneously forms a type and constructs or
eliminates a term.  A generic theorem (the arm-rebasing brick) quantifies over
`certificate : TypingRolesWellFormed bundle` and instantiates at `fxTypingRolesWellFormed`. -/
structure TypingRolesWellFormed (bundle : TypingTableBundle) : Prop where
  /-- Every generator inhabits at most one typing role class. -/
  roleClassesAreOrthogonal : ∀ generator, firesAtMostOneRoleClass bundle generator = true

/-- ★ **The canonical FX typing tables are role-orthogonal.**  Proved by full enumeration over the
208 generators — each computes its three role-class Booleans and the at-most-one check to `true` by
`rfl`.  Zero-axiom (no `decide`, no `propext`). -/
theorem fxTypingRolesWellFormed : TypingRolesWellFormed fxTypingBundle where
  roleClassesAreOrthogonal generator := by cases generator <;> rfl

/-- The headline as a bare universal — every generator is a type-former XOR a constructor XOR an
eliminator. -/
theorem typingRoleClassesOrthogonal (generator : Generator) :
    firesAtMostOneRoleClass fxTypingBundle generator = true :=
  fxTypingRolesWellFormed.roleClassesAreOrthogonal generator

/-! ## The single within-class duplicate — `gen_unitCode`, documented

The unit type code is registered both as a cumulative former and as a nullary base type.  Both rows
are FORMATION-class and emit the same `Type@0` classifier, so the duplicate is a benign redundancy:
it keeps `gen_unitCode` purely formation-class (no intro, no elim), preserving cross-class
orthogonality. -/

/-- `gen_unitCode` is the within-class duplicate: it fires two FORMATION-class tables (cumulative
formation and base-type) and NO introduction or elimination table.  So its two-row `typingRowsOf` is
two formation rows for the one unit classifier — orthogonal at the class level, the one exception to
per-table uniqueness. -/
theorem unitCode_overlapsWithinFormationClassOnly :
    (fxTypingBundle.formation .gen_unitCode).isSome = true
      ∧ (fxTypingBundle.baseType .gen_unitCode).isSome = true
      ∧ firesIntroRole fxTypingBundle .gen_unitCode = false
      ∧ firesElimRole fxTypingBundle .gen_unitCode = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two rows `gen_unitCode` fires are exactly the cumulative-formation row and the base-type row
— concretely, `typingRowsOf` has length two for the unit code. -/
theorem unitCode_firesTwoFormationRows :
    (typingRowsOf fxTypingBundle .gen_unitCode).length = 2 := rfl

/-! ## Per-table uniqueness away from the duplicate — the brick-3 precondition -/

/-- Whether a generator fires at most one typing ROW (as a Bool, via `Nat.ble`). -/
def firesAtMostOneRow (bundle : TypingTableBundle) (generator : Generator) : Bool :=
  (typingRowsOf bundle generator).length.ble 1

/-- ★ **Every generator except `gen_unitCode` fires at most one typing row.**  The unit code's
within-formation duplicate is the SOLE counterexample to per-table uniqueness; with it excluded the
single lookup returns a unique row, the precondition the arm-rebasing brick reads.  Proved by
enumeration: each non-unit arm computes `≤ 1` by `rfl`, and the unit arm is discharged by the
hypothesis.  Building green re-certifies that `gen_unitCode` is the only exception. -/
theorem typingRowsAreUnique_of_ne_unitCode (generator : Generator)
    (isNotUnitCode : generator ≠ .gen_unitCode) :
    firesAtMostOneRow fxTypingBundle generator = true := by
  cases generator <;> first | rfl | exact absurd rfl isNotUnitCode

/-! ## The unique-row `Option` view — the orthogonality corollary promised by brick 2

`typingRowOf` returns the FIRST firing row in role order.  By `typingRowsAreUnique_of_ne_unitCode`
this is THE unique row for every generator but `gen_unitCode`, and for `gen_unitCode` it is the
primary (cumulative-formation) row of the two same-classifier formation rows. -/

/-- The unique typing row of a generator: the head of its `typingRowsOf` list. -/
def typingRowOf (bundle : TypingTableBundle) (generator : Generator) : Option TypingRow :=
  (typingRowsOf bundle generator).head?

/-- The λ generator's unique row is its graded-introduction rule. -/
theorem typingRowOf_lam :
    typingRowOf fxTypingBundle .gen_lam = some (TypingRow.gradedIntro lamGradedIntroRule) := rfl

/-- The application generator's unique row is its general-elimination rule. -/
theorem typingRowOf_app :
    typingRowOf fxTypingBundle .gen_app = some (TypingRow.generalElim appGeneralElimRule) := rfl

/-- The Π-former generator's unique row is its formation rule. -/
theorem typingRowOf_piTyCode :
    typingRowOf fxTypingBundle .gen_piTyCode
      = some (TypingRow.formation { outputType := universeFormerOutput }) := rfl

/-- A generator with no typing rule has no unique row. -/
theorem typingRowOf_var_none : typingRowOf fxTypingBundle .gen_var = none := rfl

/-! ## Class-membership of the canonical heads — each plays exactly one role -/

/-- The λ generator is purely an INTRODUCTION-class head. -/
theorem lam_isIntroClassOnly :
    firesIntroRole fxTypingBundle .gen_lam = true
      ∧ firesFormationRole fxTypingBundle .gen_lam = false
      ∧ firesElimRole fxTypingBundle .gen_lam = false :=
  ⟨rfl, rfl, rfl⟩

/-- The application generator is purely an ELIMINATION-class head. -/
theorem app_isElimClassOnly :
    firesElimRole fxTypingBundle .gen_app = true
      ∧ firesFormationRole fxTypingBundle .gen_app = false
      ∧ firesIntroRole fxTypingBundle .gen_app = false :=
  ⟨rfl, rfl, rfl⟩

/-- The Π-former generator is purely a FORMATION-class head. -/
theorem piTyCode_isFormationClassOnly :
    firesFormationRole fxTypingBundle .gen_piTyCode = true
      ∧ firesIntroRole fxTypingBundle .gen_piTyCode = false
      ∧ firesElimRole fxTypingBundle .gen_piTyCode = false :=
  ⟨rfl, rfl, rfl⟩

end FX1Poly.Typed
