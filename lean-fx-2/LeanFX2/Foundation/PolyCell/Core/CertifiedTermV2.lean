import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralV2

/-! # Foundation/PolyCell/Core/CertifiedTermV2 — the `Certified` predicate for SR

V2-L3.1 phase C step 6 prep (2026-05-27).  Ships the `Certified`
predicate that the Subject Reduction theorem states about.

## What this file ships

* `Certified` predicate: term-level wrapper around the existential
  certifier `inferRawCellGeneralV2?`.  A raw term is Certified if
  wrapping it as a dim-0 cell (`RawCellV2.termBase`) yields an
  accepted certification.

* `Certified.intro` / `Certified.elim` helpers: trivial constructors
  for the existential.  Provide a stable API for consumers
  (especially SR's structural induction) rather than requiring them
  to deal with the underlying `∃` directly.

* `Certified.ofExistentialOk`: bridge from the certifier's `.ok`
  return to a Certified proof.  Used wherever the certifier is
  invoked operationally and the result needs to be lifted to the
  proof-level predicate.

## What the predicate captures

The SR theorem (V2-L3.1 phase C step 6) statement:

  ∀ {profile scope} {source target : RawTermV2 scope},
      Step source target → Certified source → Certified target

The predicate is term-level (not cell-level) because Step is on
terms.  The bridge to the certifier (which operates on cells)
goes through `RawCellV2.termBase` -- wrapping a term as a dim-0
cell.

## Profile-parametric

`Certified` is parametric in the profile.  Different profiles
admit different generator subsets:
* The FX profile admits standard MLTT iotas + value ctors.
* A modal-enabled profile additionally admits modal generators.

SR is naturally profile-parametric too: for profile P, the
theorem proves preservation of P's certification.  The proof
arms organized by Step constructor; the cong arm handles all
generators uniformly (regardless of profile admissibility);
iota arms are specific to the Step inductive's iota
constructors.

## Zero-axiom verification

All declarations pass `#assert_no_axioms`.  The predicate is
`def`-equal to an existential, so the elaboration is trivial.
Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- A raw term is **Certified** at the given profile and scope
when the existential certifier accepts the term wrapped as a dim-0
cell (`RawCellV2.termBase`).

This is the load-bearing predicate for the Subject Reduction
theorem: SR proves `Step source target → Certified source →
Certified target`.

Profile-parametric: different profiles admit different generator
subsets, and `Certified` inherits the profile's admissibility
constraints from the underlying certifier. -/
def Certified {profile : PolyProfile} {scope : Nat}
    (raw : RawTermV2 scope) : Prop :=
  ∃ (result : CertifiedRawCellResultV2 profile scope),
    inferRawCellGeneralV2? scope (RawCellV2.termBase raw) = Except.ok result

/-- **Constructor for `Certified`.**

Bridge from "the certifier accepted this term as a dim-0 cell"
to "this term is Certified".  Trivial -- just `Exists.intro` with
the result and the acceptance witness.

Provides a stable API: consumers needn't know `Certified` is
defined as an existential. -/
theorem Certified.intro
    {profile : PolyProfile} {scope : Nat} {raw : RawTermV2 scope}
    (result : CertifiedRawCellResultV2 profile scope)
    (accepted :
      inferRawCellGeneralV2? scope (RawCellV2.termBase raw) =
      Except.ok result) :
    Certified (profile := profile) raw :=
  ⟨result, accepted⟩

/-- **Destructor for `Certified`.**

Extracts the underlying certifier-result witness from a Certified
proof.  Trivial -- the existential's elimination.

Used by downstream SR-related lemmas that need to inspect the
certifier's result (the sort, boundary, certified cell, etc.). -/
theorem Certified.exists_result
    {profile : PolyProfile} {scope : Nat} {raw : RawTermV2 scope}
    (certified : Certified (profile := profile) raw) :
    ∃ (result : CertifiedRawCellResultV2 profile scope),
      inferRawCellGeneralV2? scope (RawCellV2.termBase raw) =
      Except.ok result :=
  certified

/-- **Bridge from operational certifier result to Certified.**

When the existential certifier is invoked operationally (returning
a concrete `.ok` value), this bridge lifts the result to a
`Certified` proof.  Trivial -- direct constructor application.

This is the natural way to PRODUCE Certified proofs from
verifier-style code that runs the certifier as a function. -/
theorem Certified.ofExistentialOk
    {profile : PolyProfile} {scope : Nat} {raw : RawTermV2 scope}
    {result : CertifiedRawCellResultV2 profile scope}
    (h : inferRawCellGeneralV2? scope (RawCellV2.termBase raw) =
         Except.ok result) :
    Certified (profile := profile) raw :=
  Certified.intro result h

/-! ## Inhabitation smokes

Concrete fixtures demonstrating that `Certified` is non-vacuous.
The certifier reduces transparently on basic fixtures (per V2-L1cert.15's
coverage suite), so `Certified.intro _ rfl` works -- Lean's elaborator
infers the existential witness from the rfl proof.

These smokes are profile-parametric: every profile admits the basic
fixtures (unit at scope 0, var at scope 1) because they don't depend
on the profile's excluded-generator list. -/

/-- **Smoke: the unit term at scope 0 is Certified.**

The simplest concrete inhabitant of `Certified`.  Reduces by
`rfl` because the certifier evaluates transparently on `unit` --
admission + payload-evidence + nil-spine + packaging all reduce
definitionally.

Witnesses that `Certified` is non-vacuous and the API helpers
(intro/exists_result/ofExistentialOk) work correctly. -/
theorem Certified.unit_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_unit () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: variable zero at scope 1 is Certified.**

Exercises a different payload path than `unit`: `gen_var` has
`Fin scope` payload (not Unit), so this smoke confirms the
certifier handles non-trivial payloads transparently too.

Same `⟨_, rfl⟩` closing pattern -- the certifier reduces on
var-shaped fixtures as well. -/
theorem Certified.varZero_at_scope_one {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
        : RawTermV2 1) :=
  ⟨_, rfl⟩

/-! ## Inhabitation smokes for the standard inductive-type ctors

Building on the unit/var fixtures: the standard 0-arity ctors
across bool/nat/list/option families all certify by rfl.  These
smokes establish a Certified-fixture catalog SR proofs can
reference -- particularly useful as building blocks when proving
iota arms (where the iota's target is a specific composite). -/

/-- **Smoke: boolTrue is Certified at scope 0.** -/
theorem Certified.boolTrue_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_boolTrue () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: boolFalse is Certified at scope 0.** -/
theorem Certified.boolFalse_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_boolFalse () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: natZero is Certified at scope 0.** -/
theorem Certified.natZero_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_natZero () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: listNil is Certified at scope 0.** -/
theorem Certified.listNil_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_listNil () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: optionNone is Certified at scope 0.** -/
theorem Certified.optionNone_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_optionNone () .childNil : RawTermV2 0) :=
  ⟨_, rfl⟩

/-! ## Inhabitation smokes for composite (arity 1+) fixtures

Building further: composite fixtures with non-trivial spines.
Each lifts a V2-L1cert.15 coverage fixture to the Certified
level.  Spine recursion through arity-1 (natSucc, optionSome,
eitherInl) and arity-2 (pair, listCons) generators. -/

/-- **Smoke: `natSucc natZero` = 1 is Certified at scope 0.**
Exercises arity-1 spine through one recursion level. -/
theorem Certified.natSuccZero_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_natSucc ()
        (.childCons (.mkGen .gen_natZero () .childNil) .childNil)
        : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: `optionSome unit` is Certified at scope 0.** -/
theorem Certified.optionSomeUnit_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_optionSome ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil)
        : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: `eitherInl unit` is Certified at scope 0.** -/
theorem Certified.eitherInlUnit_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_eitherInl ()
        (.childCons (.mkGen .gen_unit () .childNil) .childNil)
        : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: `pair unit unit` is Certified at scope 0.**
Exercises arity-2 spine through two adjacent same-scope children. -/
theorem Certified.pairUnits_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))
        : RawTermV2 0) :=
  ⟨_, rfl⟩

/-- **Smoke: `listCons unit listNil` is Certified at scope 0.**
Exercises a heterogeneous spine: arbitrary head + list-typed tail. -/
theorem Certified.listConsUnit_at_scope_zero {profile : PolyProfile} :
    Certified (profile := profile)
      (.mkGen .gen_listCons ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_listNil () .childNil) .childNil))
        : RawTermV2 0) :=
  ⟨_, rfl⟩

end LeanFX2.Foundation.PolyCell.Core
