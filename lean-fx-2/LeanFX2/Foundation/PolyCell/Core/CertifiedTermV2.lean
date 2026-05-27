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

end LeanFX2.Foundation.PolyCell.Core
