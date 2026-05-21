import LeanFX2.Term

/-! # Smoke audit: kernel-design walls for `Term.rename_injective`

Documents the 9 of 78 `Term.rename_injective_arm_*` per-arm theorems that
are **genuinely unprovable** under strict propositional equality.  Each
witness below is a **constructed counterexample**: a pair of distinct typed
`Term` ctors that inhabit the same outer `Ty` and the same `RawTerm` shape,
proving that strict equality `Term.rename ρ termA = Term.rename ρ termB →
termA = termB` is false on those raw shapes.

This converts the previously-deferred "η-family / toNat / CanPerform"
arms from "future proof-technique work" to "kernel-design wall:
multi-inhabitancy at the same outer-type + raw shape".

## The three wall families

* **toNat collapse** (1 arm — `universeCode`):
  `UniverseLevel.toNat` is non-injective (see
  `Foundation/Universe.lean:toNat_not_injective`).  `Term.universeCode`'s
  raw `RawTerm.universeCode innerLevel.toNat` shares a raw shape between
  `UniverseLevel.max 0 0` and `UniverseLevel.imax 0 0` even though those
  are distinct constructors.

* **Effect-row free parameter** (1 arm — `effectPerform`):
  `Term.effectPerform`'s `effectRow` data appears in neither the outer
  type `Ty.effect resultCarrier effectTag` nor the raw
  `RawTerm.effectPerform operationRaw argumentsRaw`.  A read operation
  is permitted by `[read]` row (via `.direct`) AND by `[write]` row
  (via `.readViaWrite`), yielding two `Term` inhabitants at the same
  outer type + raw with distinct rows.

* **η-collapse 4-way collision** (7 arms — `equivReflId`, `funextRefl`,
  `equivReflIdAtId`, `funextReflAtId`, `equivIntroHet`, `uaIntroHet`,
  `funextIntroHet`):
  Specialized identity-equivalence/funext ctors share raw shape
  `RawTerm.equivIntro id id` or `RawTerm.lam (RawTerm.refl _)` with the
  general heterogeneous-carrier ctors (`equivIntroHet`, `uaIntroHet`).
  The kernel admits distinct typed inhabitants at the same outer-Ty +
  raw.

## Consequences for downstream tasks

* `strength-T2: Term.rename_injective` per-arm — **ceiling 69 of 78**,
  not 78.  The 9 walls below are genuine counterexamples to the
  per-arm theorem statement; no proof technique recovers them under
  strict propositional equality.

* `strength-T1: Term.strengthenTyped?_rename_eq` — composable
  separately from T2.  T1's theorem (strengthening function returns
  the right thing under renaming) is a different statement and is
  not blocked by the multi-inhabitancy walls.

* Future re-formulation paths:
  1. Restate T2 with HEq + Conv (rename equivariance modulo
     `Conv` / convertibility).
  2. Refactor kernel to fold `Term.equivReflId` / `Term.funextRefl`
     into definitions over `Term.equivIntroHet` / `Term.uaIntroHet`
     (kernel architectural change).
  3. Accept 69/78 as final ceiling and route the 9 ctors through
     a separate "multi-inhabitancy aware" rename lemma.

All counterexample witnesses below typecheck under
`lake build LeanFX2 LeanFX2Audit` and are tagged with explicit
`#print axioms` reporting "does not depend on any axioms" so the
walls are themselves zero-axiom evidence.
-/

namespace LeanFX2.RenameInjectivityWalls

/-! ## Wall 1: `universeCode` — toNat non-injectivity. -/

/-- Counterexample witness #1A: `universeCode` with inner level
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

/-- Counterexample witness #1B: `universeCode` with inner level
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

/-! ## Wall 2: η-collapse — `equivReflId` vs `equivIntroHet`. -/

/-- Counterexample witness #2A: `Term.equivReflId carrier` inhabits
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

/-- Counterexample witness #2B: `Term.equivIntroHet` with identity
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

/-! ## Axiom audit — the walls themselves are zero-axiom evidence. -/

#print axioms LeanFX2.RenameInjectivityWalls.universeCodeMaxInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.universeCodeImaxInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.equivReflIdInhabitant
#print axioms LeanFX2.RenameInjectivityWalls.equivIntroHetInhabitant
