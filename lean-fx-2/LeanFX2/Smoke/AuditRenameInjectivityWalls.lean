import LeanFX2.Term.RenameInjective.InductiveArms

/-! # Smoke audit: raw-shape collisions for `Term.rename_injective`

This file records the raw-index multi-inhabitancy cases that originally
looked like kernel-design walls for `Term.rename_injective`.  The witnesses
below are still useful, but their meaning is narrower: they show that a proof
which cases only on outer `Ty` plus `RawTerm` shape is insufficient.

They are **not** counterexamples to T2.  T2 assumes equality of the renamed
typed terms, and that premise is false for the distinct witnesses below.  The
completed proof closes the cases by inverting typed renamed constructor
equality, where `Term.noConfusion` exposes the implicit constructor fields
that the raw index alone forgot.

## The collision families

* **toNat raw collapse** (`universeCode`):
  `UniverseLevel.toNat` is non-injective (see
  `Foundation/Universe.lean:toNat_not_injective`).  `Term.universeCode`'s
  raw `RawTerm.universeCode innerLevel.toNat` shares a raw shape between
  `UniverseLevel.max 0 0` and `UniverseLevel.imax 0 0` even though those
  are distinct constructors.

* **Effect-row free parameter** (`effectPerform`):
  `Term.effectPerform`'s `effectRow` data appears in neither the outer
  type `Ty.effect resultCarrier effectTag` nor the raw
  `RawTerm.effectPerform operationRaw argumentsRaw`.  A read operation
  is permitted by `[read]` row (via `.direct`) AND by `[write]` row
  (via `.readViaWrite`), yielding two `Term` inhabitants at the same
  outer type + raw with distinct rows.

* **eta-family raw collisions** (`equivReflId`,
  `equivReflIdAtId`, `funextReflAtId`, `equivIntroHet`, `uaIntroHet`,
  `funextIntroHet`):
  Specialized identity-equivalence/funext ctors share raw shape
  `RawTerm.equivIntro id id` or `RawTerm.lam (RawTerm.refl _)` with the
  general heterogeneous-carrier ctors (`equivIntroHet`, `uaIntroHet`).
  The kernel admits distinct typed inhabitants at the same outer-Ty +
  raw.

## Consequences for downstream tasks

* `strength-T2: Term.rename_injective` is closed at 78 of 78 arm-helper level,
  with the public wrapper exported from
  `Term/RenameInjective/InductiveArms.lean`.

* The witnesses below are regression checks against the old raw-only proof
  plan.  They explain why the final proof must invert equality of renamed
  typed constructors rather than infer source equality from raw shape alone.

* `strength-T1: Term.strengthenTyped?_rename_eq` — composable
  separately from T2.  T1's theorem (strengthening function returns
  the right thing under renaming) is a different statement.

All witnesses below are tagged with explicit `#print axioms` reporting
"does not depend on any axioms"; the final `Term.rename_injective` audit is
printed here as well.
-/

namespace LeanFX2.RenameInjectivityWalls

/-! ## Collision 1: `universeCode` — toNat non-injectivity. -/

/-- Raw-collision witness #1A: `universeCode` with inner level
`UniverseLevel.max 0 0`. -/
def universeCodeMaxInhabitant
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (cumulOk :
      (UniverseLevel.max UniverseLevel.zero UniverseLevel.zero).toNat ≤
        outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term context (Ty.universe outerLevel levelLe)
      (RawTerm.universeCode
        (UniverseLevel.max UniverseLevel.zero UniverseLevel.zero).toNat) :=
  Term.universeCode
    (UniverseLevel.max UniverseLevel.zero UniverseLevel.zero)
    outerLevel cumulOk levelLe

/-- Raw-collision witness #1B: `universeCode` with inner level
`UniverseLevel.imax 0 0` — same outer type, same raw, distinct ctor. -/
def universeCodeImaxInhabitant
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope)
    (outerLevel : UniverseLevel)
    (cumulOk :
      (UniverseLevel.imax UniverseLevel.zero UniverseLevel.zero).toNat ≤
        outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term context (Ty.universe outerLevel levelLe)
      (RawTerm.universeCode
        (UniverseLevel.max UniverseLevel.zero UniverseLevel.zero).toNat) :=
  -- (max 0 0).toNat = (imax 0 0).toNat = 0, so the raw shape matches.
  Term.universeCode
    (UniverseLevel.imax UniverseLevel.zero UniverseLevel.zero)
    outerLevel cumulOk levelLe

/-! ## Collision 2: eta-family raw shape — `equivReflId` vs `equivIntroHet`. -/

/-- Raw-collision witness #2A: `Term.equivReflId carrier` inhabits
`Ty.equiv carrier carrier` at raw `RawTerm.equivIntro (lam (var 0))
(lam (var 0))`. -/
def equivReflIdInhabitant
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (carrier : Ty level scope) :
    Term context (Ty.equiv carrier carrier)
      (RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) :=
  Term.equivReflId carrier

/-- Raw-collision witness #2B: `Term.equivIntroHet` with identity
lambdas as forward/backward inhabits the SAME outer type + raw as
`equivReflId carrier` — distinct ctor, distinct typed term. -/
def equivIntroHetInhabitant
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (carrier : Ty level scope)
    (leftInvTerm :
      Term context
        (equivIntroHetLeftInverseType carrier
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
    (rightInvTerm :
      Term context
        (equivIntroHetRightInverseType carrier
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) :
    Term context (Ty.equiv carrier carrier)
      (RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))) :=
  Term.equivIntroHet
    (carrierA := carrier) (carrierB := carrier)
    (Term.lam (domainType := carrier) (codomainType := carrier)
      (Term.var ⟨0, Nat.zero_lt_succ scope⟩))
    (Term.lam (domainType := carrier) (codomainType := carrier)
      (Term.var ⟨0, Nat.zero_lt_succ scope⟩))
    leftInvTerm rightInvTerm

end LeanFX2.RenameInjectivityWalls

/-! ## Axiom audit — the collision witnesses and final wrapper are zero-axiom. -/

#print axioms LeanFX2.RenameInjectivityWalls.universeCodeMaxInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.universeCodeImaxInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.equivReflIdInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.equivIntroHetInhabitant
#print axioms LeanFX2.Term.rename_injective
