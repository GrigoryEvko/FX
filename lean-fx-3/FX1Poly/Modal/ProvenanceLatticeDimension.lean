import FX1Poly.Modal.ClockDomainLatticeDimension

/-! # FX1Poly/Modal/ProvenanceLatticeDimension
    — the PROVENANCE dimension (§6.3 Dim 8 / §1.1) as the kernel's FIRST INFINITE FULL LATTICE (M_omega:
      join AND meet over an infinite antichain), and the first lattice dimension whose top is a LEGITIMATE
      value rather than a type error

`OverflowLatticeDimension.lean` shipped the FINITE diamond M3 as the first FULL bounded lattice (join + meet +
absorption + non-distributivity + modularity).  `ClockDomainLatticeDimension.lean` shipped the first INFINITE
carrier — but only as a JOIN-semilattice (the `sync clockId` atoms with the `crossDomainError` top), with no
meet.  This file combines both advances: the PROVENANCE dimension is the first lattice that is BOTH infinite
AND full (it carries the meet), so it is the kernel's first concrete M_omega — the infinite generalization of
the diamond M3 (infinitely many atoms, all joining to one top and meeting to one bottom).

## The provenance lattice (§6.3 Dim 8 / §1.1)

§6.3 Dim 8: "lattice of origin labels `Source(name)`, `Derived`, `Aggregated`, `Unknown`.  Addition merges
chains.  `Source('x') <= Unknown`.  Functions requiring known provenance reject untracked data."  §1.1:
provenance is "opaque default, granted via `source('x')`".  We model the core FLAT fragment:

  * `opaqueOrigin` — the BOTTOM (the deny-by-default state: no origin granted; combining it with anything
    contributes no origin constraint, so it is the join identity).
  * `source originId` — one element per known origin (`originId : Nat`), an INFINITE ANTICHAIN: two distinct
    known sources are pairwise incomparable.
  * `unknown` — the TOP, the join of any two distinct sources: "addition merges chains" toward the
    least-informative label.  `Source('x') <= Unknown` is exactly the induced order.

`join` is the supremum (origins MERGE, losing precision toward `unknown`); `meet` is the infimum (the common
sub-origin, falling to `opaqueOrigin` when the sources differ).  The composite is M_omega.

## The distinctive content — the top is a value, not an error

This is the FIRST lattice dimension whose top is NOT a type error.  Overflow's `conflictGrade`, clock's
`crossDomainError`, and the §6.4 permission `CONFLICT` are all REJECTED states: reaching the top is a
compile error.  Provenance's `unknown` is a LEGITIMATE value — "this datum's origin is no longer known" — and
the §6.3 rejection ("functions requiring known provenance reject untracked data") is a POLICY on a sink, not a
structural impossibility.  We mechanize this contrast: `isKnownSource` (the provenance-requiring sink's
guard) ACCEPTS every `source _` and REJECTS `unknown` / `opaqueOrigin`; and crucially `isKnownSource`
of a join of two DISTINCT sources is `false` — combining distinct origins LOSES the known-origin property
(the supply-chain / §25.5 provenance-tracking guarantee), yet the merged value is a well-formed lattice
element, reachable and inspectable, NOT a stuck error.

## What lands here (all zero-axiom)

  * `ProvenanceGrade` (3-ctor inductive, one ctor carrying a `Nat`) + `join` / `meet` (dual flat operations,
    the `source`-`source` arms guarded by `Nat.beq`, propext-free `bif`).
  * `provenanceLattice` + `provenanceIsLawfulBoundedJoinSemilattice` — a verified bounded join-semilattice;
    comm/assoc route through the clock `Nat.beq` facts (reused, not re-derived).
  * The MEET half — `provenanceMeet_comm` / `_assoc` / `_idempotent` + identity (`unknown`) + absorber
    (`opaqueOrigin`) + the two absorption laws — upgrading the join-semilattice to a FULL infinite lattice.
  * **`provenanceSourceIncomparableOfDistinct`** — distinct sources are pairwise incomparable: an INFINITE
    antichain (as clock, but now in a FULL lattice).
  * **`provenanceIsNonDistributive`** — the canonical M3-sublattice failure on three concrete sources,
    pinning M_omega as a genuine non-distributive lattice (it contains M3).
  * **`isKnownSource` + `knownSourceLostOnDistinctMerge`** — the genuinely-new provenance SEMANTICS: a
    provenance-requiring sink accepts `source _`, rejects `unknown` / `opaqueOrigin`, and the known-origin
    property is LOST when two distinct origins merge — yet `unknown` is a legitimate value (`joinDistinct
    SourcesIsUnknown`), the first lattice top that is not a type error.
  * `provenanceClockProductLattice` + `_IsLawful` — the FIRST composition of TWO infinite-antichain lattice
    dimensions (provenance and clock), via the shipped `productIsLawful`, with no per-product re-proof.

## Honest scope boundary

Only the core FLAT fragment (`opaqueOrigin` / `source` / `unknown`) is modeled; the compositional origin labels
`Derived(parent, transform)` and `Aggregated(list)` of §6.3 (recursive origin trees) are a richer fragment
deferred — the flat M_omega is the lattice skeleton.  Like overflow / clock, this models only the COMBINE
algebra (the lattice); the runtime provenance-tracking instrumentation is separate.  General symbolic
modularity (M_omega is modular) is deferred: the concrete M3-sublattice non-distributivity here already pins it
as a genuine non-distributive lattice.  It does not fold `provenance` into the closed `GradedDimensionName`
classification enum (a deferred purely-additive cross-file edit); the lawfulness + antichain + meet theorems
here ARE the classification evidence.

## Zero-axiom verification

`ProvenanceGrade` is a plain inductive with derived `DecidableEq` (the `Nat` field routes through `Nat.decEq`).
The parameterized `source`-`source` join/meet laws reuse the clock file's hand-rolled propext-clean `Nat.beq`
facts (`natBeqReflexive` / `natEqOfBeqTrue` / `natBeqCommutes`); identity/absorber sub-cases use small
`cases <;> rfl` helpers (a stuck `source`-`source` guard blocks a direct `rfl`, so it is rewritten away);
incomparability and the known-source-loss facts are the defeq route (`ProvenanceGrade.noConfusion` / `Bool`
reduction after rewriting the guard); non-distributivity is a concrete `decide`; composition reuses
`productIsLawful`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The provenance grade (§6.3 Dim 8 / §1.1): `opaqueOrigin` (the deny-by-default no-origin state — the
bottom), a known origin `source originId` (one element per origin identifier — an infinite antichain), and
`unknown` (the top — origin lost through merging; a legitimate "origin unknown" value, NOT a type error). -/
inductive ProvenanceGrade where
  | opaqueOrigin
  | source (originId : Nat)
  | unknown
  deriving DecidableEq

/-- Provenance join — the lattice supremum (origins MERGE, losing precision).  `opaqueOrigin` is the identity;
two equal origins join to themselves; two DISTINCT origins join to `unknown` (the §6.3 "addition merges chains"
toward the least-informative label); `unknown` absorbs.  The `source`-`source` arm is `Nat.beq`-guarded
(propext-free `bif`); the rest is a full 3x3 enumeration. -/
def ProvenanceGrade.join : ProvenanceGrade → ProvenanceGrade → ProvenanceGrade
  | .opaqueOrigin, grade        => grade
  | .source first, .opaqueOrigin => .source first
  | .source first, .source second => bif Nat.beq first second then .source first else .unknown
  | .source _,     .unknown     => .unknown
  | .unknown,      _            => .unknown

/-- Provenance meet — the lattice infimum (the common sub-origin), dual to `join` under the bottom/top swap.
`unknown` is the identity; two equal origins meet to themselves; two DISTINCT origins meet DOWN to
`opaqueOrigin` (no shared origin survives); `opaqueOrigin` absorbs.  Full 3x3 enumeration, propext-free. -/
def ProvenanceGrade.meet : ProvenanceGrade → ProvenanceGrade → ProvenanceGrade
  | .unknown,      grade        => grade
  | .source first, .unknown     => .source first
  | .source first, .source second => bif Nat.beq first second then .source first else .opaqueOrigin
  | .source _,     .opaqueOrigin => .opaqueOrigin
  | .opaqueOrigin, _            => .opaqueOrigin

/-! ## Join identity / absorber helpers (the bottom feeds, the top absorbs) -/

/-- `opaqueOrigin` is the left identity for the join. -/
theorem provenanceJoinOpaqueLeft (grade : ProvenanceGrade) :
    ProvenanceGrade.join .opaqueOrigin grade = grade := by cases grade <;> rfl

/-- `opaqueOrigin` is the right identity for the join. -/
theorem provenanceJoinOpaqueRight (grade : ProvenanceGrade) :
    ProvenanceGrade.join grade .opaqueOrigin = grade := by cases grade <;> rfl

/-- `unknown` absorbs on the left under join. -/
theorem provenanceJoinUnknownLeft (grade : ProvenanceGrade) :
    ProvenanceGrade.join .unknown grade = .unknown := by cases grade <;> rfl

/-- `unknown` absorbs on the right under join. -/
theorem provenanceJoinUnknownRight (grade : ProvenanceGrade) :
    ProvenanceGrade.join grade .unknown = .unknown := by cases grade <;> rfl

/-- An origin joined with itself is itself (join idempotence at a `source` element — via `natBeqReflexive`). -/
theorem provenanceJoinSourceWithSelf (originId : Nat) :
    ProvenanceGrade.join (.source originId) (.source originId) = .source originId := by
  show (bif Nat.beq originId originId then ProvenanceGrade.source originId else ProvenanceGrade.unknown)
     = ProvenanceGrade.source originId
  rw [natBeqReflexive originId, Bool.cond_true]

/-! ## The bounded join-semilattice -/

/-- The provenance bounded join-semilattice: carrier `ProvenanceGrade`, bottom `opaqueOrigin`, the merge join. -/
def provenanceLattice : BoundedJoinSemilattice where
  Carrier := ProvenanceGrade
  bottom := .opaqueOrigin
  join := ProvenanceGrade.join
  carrierDecEq := instDecidableEqProvenanceGrade

/-- **Merging origins is commutative** — the `source`-`source` arm via `natBeqCommutes` (symmetric guard) +
`natEqOfBeqTrue` (when the guard fires the origins are equal). -/
theorem provenanceJoinCommutes (first second : ProvenanceGrade) :
    ProvenanceGrade.join first second = ProvenanceGrade.join second first := by
  cases first with
  | opaqueOrigin => cases second <;> rfl
  | source firstId =>
      cases second with
      | opaqueOrigin => rfl
      | source secondId =>
          show (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId else ProvenanceGrade.unknown)
             = (bif Nat.beq secondId firstId then ProvenanceGrade.source secondId else ProvenanceGrade.unknown)
          rw [natBeqCommutes firstId secondId]
          cases guard : Nat.beq secondId firstId with
          | false => rfl
          | true => exact congrArg ProvenanceGrade.source (natEqOfBeqTrue secondId firstId guard).symm
      | unknown => rfl
  | unknown => cases second <;> rfl

/-- **Merging origins is associative** — only the `source`-`source`-`source` arm is non-trivial: any pairwise
distinct-origin merge forces the whole to `unknown`, and three equal origins keep that origin in both
association orders.  The mixed `opaqueOrigin` / `unknown` arms use the identity/absorber helpers (a stuck
`source`-`source` guard blocks a direct `rfl`). -/
theorem provenanceJoinAssociates (first second third : ProvenanceGrade) :
    ProvenanceGrade.join (ProvenanceGrade.join first second) third
      = ProvenanceGrade.join first (ProvenanceGrade.join second third) := by
  cases first with
  | opaqueOrigin =>
      rw [provenanceJoinOpaqueLeft second, provenanceJoinOpaqueLeft (ProvenanceGrade.join second third)]
  | unknown =>
      rw [provenanceJoinUnknownLeft second, provenanceJoinUnknownLeft third,
        provenanceJoinUnknownLeft (ProvenanceGrade.join second third)]
  | source firstId =>
      cases second with
      | opaqueOrigin =>
          rw [provenanceJoinOpaqueRight (ProvenanceGrade.source firstId), provenanceJoinOpaqueLeft third]
      | unknown =>
          rw [provenanceJoinUnknownRight (ProvenanceGrade.source firstId)]
          cases third <;> rfl
      | source secondId =>
          cases third with
          | opaqueOrigin =>
              rw [provenanceJoinOpaqueRight
                    (ProvenanceGrade.join (ProvenanceGrade.source firstId) (ProvenanceGrade.source secondId)),
                provenanceJoinOpaqueRight (ProvenanceGrade.source secondId)]
          | unknown =>
              rw [provenanceJoinUnknownRight
                    (ProvenanceGrade.join (ProvenanceGrade.source firstId) (ProvenanceGrade.source secondId)),
                provenanceJoinUnknownRight (ProvenanceGrade.source secondId),
                provenanceJoinUnknownRight (ProvenanceGrade.source firstId)]
          | source thirdId =>
              show ProvenanceGrade.join
                     (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                        else ProvenanceGrade.unknown)
                     (ProvenanceGrade.source thirdId)
                 = ProvenanceGrade.join (ProvenanceGrade.source firstId)
                     (bif Nat.beq secondId thirdId then ProvenanceGrade.source secondId
                        else ProvenanceGrade.unknown)
              cases firstSecond : Nat.beq firstId secondId with
              | false =>
                  cases secondThird : Nat.beq secondId thirdId with
                  | false => rfl
                  | true =>
                      show ProvenanceGrade.unknown
                         = bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                             else ProvenanceGrade.unknown
                      rw [firstSecond, Bool.cond_false]
              | true =>
                  have originsAgree : firstId = secondId := natEqOfBeqTrue firstId secondId firstSecond
                  subst originsAgree
                  show (bif Nat.beq firstId thirdId then ProvenanceGrade.source firstId
                          else ProvenanceGrade.unknown)
                     = ProvenanceGrade.join (ProvenanceGrade.source firstId)
                         (bif Nat.beq firstId thirdId then ProvenanceGrade.source firstId
                            else ProvenanceGrade.unknown)
                  cases firstThird : Nat.beq firstId thirdId with
                  | false => rfl
                  | true =>
                      show ProvenanceGrade.source firstId
                         = bif Nat.beq firstId firstId then ProvenanceGrade.source firstId
                             else ProvenanceGrade.unknown
                      rw [natBeqReflexive firstId, Bool.cond_true]

/-- **Provenance IS a verified bounded join-semilattice.**  Like clock, its carrier is INFINITE; comm/assoc
route through the `Nat.beq` case analysis. -/
theorem provenanceIsLawfulBoundedJoinSemilattice : IsLawfulBoundedJoinSemilattice provenanceLattice where
  join_comm := provenanceJoinCommutes
  join_assoc := provenanceJoinAssociates
  join_idempotent := fun grade => by
    cases grade with
    | opaqueOrigin => rfl
    | source originId => exact provenanceJoinSourceWithSelf originId
    | unknown => rfl
  bottom_join := fun grade => by cases grade <;> rfl
  join_bottom := fun grade => by cases grade <;> rfl

/-! ## The infinite antichain — distinct origins are incomparable -/

/-- **Distinct origins are incomparable.**  For any two distinct origin identifiers, `source a` and `source b`
are pairwise incomparable in the induced order — an INFINITE antichain (now inside a FULL lattice).  Each
`¬ le` reduces (by the join + the distinctness guard) to refuting `unknown = source _`. -/
theorem provenanceSourceIncomparableOfDistinct (firstId secondId : Nat)
    (distinct : Nat.beq firstId secondId = false) :
    ¬ provenanceLattice.le (ProvenanceGrade.source firstId) (ProvenanceGrade.source secondId) ∧
    ¬ provenanceLattice.le (ProvenanceGrade.source secondId) (ProvenanceGrade.source firstId) := by
  refine ⟨fun leEq => ?_, fun leEq => ?_⟩
  · change (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId else ProvenanceGrade.unknown)
        = ProvenanceGrade.source secondId at leEq
    rw [distinct] at leEq
    exact ProvenanceGrade.noConfusion leEq
  · change (bif Nat.beq secondId firstId then ProvenanceGrade.source secondId else ProvenanceGrade.unknown)
        = ProvenanceGrade.source firstId at leEq
    rw [natBeqCommutes secondId firstId, distinct] at leEq
    exact ProvenanceGrade.noConfusion leEq

/-- Concrete non-vacuity: origins `0` and `1` are incomparable (the infinite antichain is inhabited). -/
theorem provenanceSource01Incomparable :
    ¬ provenanceLattice.le (ProvenanceGrade.source 0) (ProvenanceGrade.source 1) ∧
    ¬ provenanceLattice.le (ProvenanceGrade.source 1) (ProvenanceGrade.source 0) :=
  provenanceSourceIncomparableOfDistinct 0 1 rfl

/-! ## Bounds — opaqueOrigin is the bottom, unknown the top -/

/-- `opaqueOrigin` is the least element (via the generic `bottom_le`). -/
theorem provenanceOpaqueIsLeast (grade : ProvenanceGrade) :
    provenanceLattice.le ProvenanceGrade.opaqueOrigin grade :=
  BoundedJoinSemilattice.bottom_le provenanceIsLawfulBoundedJoinSemilattice grade

/-- `unknown` is the greatest element: every grade is below it (so `Source('x') <= Unknown`, §6.3). -/
theorem provenanceUnknownIsGreatest (grade : ProvenanceGrade) :
    provenanceLattice.le grade ProvenanceGrade.unknown := by cases grade <;> rfl

/-! ## The MEET — completing M_omega to the kernel's FIRST INFINITE FULL LATTICE

The join half above makes provenance a bounded join-semilattice (matching clock).  The meet built here adds the
infimum, upgrading it to a FULL lattice: provenance is the first lattice that is BOTH infinite (clock) AND full
(overflow's M3 was finite).  The meet mirrors the join dualized; its laws reuse the same `Nat.beq` idiom. -/

/-- `unknown` (the top) is the left identity for the meet (dual of `opaqueOrigin` being the join identity). -/
theorem provenanceMeetUnknownLeft (grade : ProvenanceGrade) :
    ProvenanceGrade.meet .unknown grade = grade := by cases grade <;> rfl

/-- `unknown` is the right identity for the meet. -/
theorem provenanceMeetUnknownRight (grade : ProvenanceGrade) :
    ProvenanceGrade.meet grade .unknown = grade := by cases grade <;> rfl

/-- `opaqueOrigin` (the bottom) absorbs on the left under meet (dual of `unknown` absorbing under join). -/
theorem provenanceMeetOpaqueLeft (grade : ProvenanceGrade) :
    ProvenanceGrade.meet .opaqueOrigin grade = .opaqueOrigin := by cases grade <;> rfl

/-- `opaqueOrigin` absorbs on the right under meet. -/
theorem provenanceMeetOpaqueRight (grade : ProvenanceGrade) :
    ProvenanceGrade.meet grade .opaqueOrigin = .opaqueOrigin := by cases grade <;> rfl

/-- An origin met with itself is itself (meet idempotence at a `source` element). -/
theorem provenanceMeetSourceWithSelf (originId : Nat) :
    ProvenanceGrade.meet (.source originId) (.source originId) = .source originId := by
  show (bif Nat.beq originId originId then ProvenanceGrade.source originId else ProvenanceGrade.opaqueOrigin)
     = ProvenanceGrade.source originId
  rw [natBeqReflexive originId, Bool.cond_true]

/-- Meet is commutative (the meet mirror of `provenanceJoinCommutes`). -/
theorem provenanceMeet_comm (first second : ProvenanceGrade) :
    ProvenanceGrade.meet first second = ProvenanceGrade.meet second first := by
  cases first with
  | unknown => cases second <;> rfl
  | source firstId =>
      cases second with
      | unknown => rfl
      | source secondId =>
          show (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                  else ProvenanceGrade.opaqueOrigin)
             = (bif Nat.beq secondId firstId then ProvenanceGrade.source secondId
                  else ProvenanceGrade.opaqueOrigin)
          rw [natBeqCommutes firstId secondId]
          cases guard : Nat.beq secondId firstId with
          | false => rfl
          | true => exact congrArg ProvenanceGrade.source (natEqOfBeqTrue secondId firstId guard).symm
      | opaqueOrigin => rfl
  | opaqueOrigin => cases second <;> rfl

/-- Meet is associative (the meet mirror of `provenanceJoinAssociates`). -/
theorem provenanceMeet_assoc (first second third : ProvenanceGrade) :
    ProvenanceGrade.meet (ProvenanceGrade.meet first second) third
      = ProvenanceGrade.meet first (ProvenanceGrade.meet second third) := by
  cases first with
  | unknown =>
      rw [provenanceMeetUnknownLeft second, provenanceMeetUnknownLeft (ProvenanceGrade.meet second third)]
  | opaqueOrigin =>
      rw [provenanceMeetOpaqueLeft second, provenanceMeetOpaqueLeft third,
        provenanceMeetOpaqueLeft (ProvenanceGrade.meet second third)]
  | source firstId =>
      cases second with
      | unknown =>
          rw [provenanceMeetUnknownRight (ProvenanceGrade.source firstId), provenanceMeetUnknownLeft third]
      | opaqueOrigin =>
          rw [provenanceMeetOpaqueRight (ProvenanceGrade.source firstId)]
          cases third <;> rfl
      | source secondId =>
          cases third with
          | unknown =>
              rw [provenanceMeetUnknownRight
                    (ProvenanceGrade.meet (ProvenanceGrade.source firstId) (ProvenanceGrade.source secondId)),
                provenanceMeetUnknownRight (ProvenanceGrade.source secondId)]
          | opaqueOrigin =>
              rw [provenanceMeetOpaqueRight
                    (ProvenanceGrade.meet (ProvenanceGrade.source firstId) (ProvenanceGrade.source secondId)),
                provenanceMeetOpaqueRight (ProvenanceGrade.source secondId),
                provenanceMeetOpaqueRight (ProvenanceGrade.source firstId)]
          | source thirdId =>
              show ProvenanceGrade.meet
                     (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                        else ProvenanceGrade.opaqueOrigin)
                     (ProvenanceGrade.source thirdId)
                 = ProvenanceGrade.meet (ProvenanceGrade.source firstId)
                     (bif Nat.beq secondId thirdId then ProvenanceGrade.source secondId
                        else ProvenanceGrade.opaqueOrigin)
              cases firstSecond : Nat.beq firstId secondId with
              | false =>
                  cases secondThird : Nat.beq secondId thirdId with
                  | false => rfl
                  | true =>
                      show ProvenanceGrade.opaqueOrigin
                         = bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                             else ProvenanceGrade.opaqueOrigin
                      rw [firstSecond, Bool.cond_false]
              | true =>
                  have originsAgree : firstId = secondId := natEqOfBeqTrue firstId secondId firstSecond
                  subst originsAgree
                  show (bif Nat.beq firstId thirdId then ProvenanceGrade.source firstId
                          else ProvenanceGrade.opaqueOrigin)
                     = ProvenanceGrade.meet (ProvenanceGrade.source firstId)
                         (bif Nat.beq firstId thirdId then ProvenanceGrade.source firstId
                            else ProvenanceGrade.opaqueOrigin)
                  cases firstThird : Nat.beq firstId thirdId with
                  | false => rfl
                  | true =>
                      show ProvenanceGrade.source firstId
                         = bif Nat.beq firstId firstId then ProvenanceGrade.source firstId
                             else ProvenanceGrade.opaqueOrigin
                      rw [natBeqReflexive firstId, Bool.cond_true]

/-! ### Absorption — the laws that fuse join + meet into a genuine lattice -/

/-- **Absorption (join over meet): `a ∨ (a ∧ b) = a`.**  One of the two laws that make join + meet a genuine
bounded LATTICE rather than two unrelated semilattices. -/
theorem provenanceJoinMeetAbsorb (first second : ProvenanceGrade) :
    ProvenanceGrade.join first (ProvenanceGrade.meet first second) = first := by
  cases first with
  | opaqueOrigin => rw [provenanceMeetOpaqueLeft second, provenanceJoinOpaqueLeft]
  | unknown => rw [provenanceMeetUnknownLeft second, provenanceJoinUnknownLeft]
  | source firstId =>
      cases second with
      | opaqueOrigin =>
          rw [provenanceMeetOpaqueRight (ProvenanceGrade.source firstId),
            provenanceJoinOpaqueRight (ProvenanceGrade.source firstId)]
      | unknown =>
          rw [provenanceMeetUnknownRight (ProvenanceGrade.source firstId)]
          exact provenanceJoinSourceWithSelf firstId
      | source secondId =>
          show ProvenanceGrade.join (ProvenanceGrade.source firstId)
                 (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                    else ProvenanceGrade.opaqueOrigin)
             = ProvenanceGrade.source firstId
          cases firstSecond : Nat.beq firstId secondId with
          | false =>
              rw [Bool.cond_false, provenanceJoinOpaqueRight (ProvenanceGrade.source firstId)]
          | true =>
              rw [Bool.cond_true]
              exact provenanceJoinSourceWithSelf firstId

/-- **Absorption (meet over join): `a ∧ (a ∨ b) = a`.**  The second lattice-absorption law. -/
theorem provenanceMeetJoinAbsorb (first second : ProvenanceGrade) :
    ProvenanceGrade.meet first (ProvenanceGrade.join first second) = first := by
  cases first with
  | opaqueOrigin => rw [provenanceJoinOpaqueLeft second, provenanceMeetOpaqueLeft]
  | unknown => rw [provenanceJoinUnknownLeft second, provenanceMeetUnknownRight]
  | source firstId =>
      cases second with
      | opaqueOrigin =>
          rw [provenanceJoinOpaqueRight (ProvenanceGrade.source firstId),
            provenanceMeetSourceWithSelf firstId]
      | unknown =>
          rw [provenanceJoinUnknownRight (ProvenanceGrade.source firstId),
            provenanceMeetUnknownRight (ProvenanceGrade.source firstId)]
      | source secondId =>
          show ProvenanceGrade.meet (ProvenanceGrade.source firstId)
                 (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId
                    else ProvenanceGrade.unknown)
             = ProvenanceGrade.source firstId
          cases firstSecond : Nat.beq firstId secondId with
          | false =>
              rw [Bool.cond_false, provenanceMeetUnknownRight (ProvenanceGrade.source firstId)]
          | true =>
              rw [Bool.cond_true]
              exact provenanceMeetSourceWithSelf firstId

/-! ### Distinct origins MEET to the opaque bottom (dual of join-to-unknown) -/

/-- `source a ∧ source b = opaqueOrigin` for distinct origins: meeting distinct origins loses all shared origin
information (dual of distinct origins joining to `unknown`). -/
theorem provenanceMeetDistinctIsOpaque (firstId secondId : Nat)
    (distinct : Nat.beq firstId secondId = false) :
    ProvenanceGrade.meet (.source firstId) (.source secondId) = .opaqueOrigin := by
  show (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId else ProvenanceGrade.opaqueOrigin)
     = ProvenanceGrade.opaqueOrigin
  rw [distinct, Bool.cond_false]

/-- ★ **M_omega is NON-DISTRIBUTIVE** — the canonical M3-sublattice witness on three concrete origins:
`s0 ∧ (s1 ∨ s2) = s0 ∧ unknown = s0` but `(s0 ∧ s1) ∨ (s0 ∧ s2) = opaqueOrigin ∨ opaqueOrigin = opaqueOrigin`,
and `s0 ≠ opaqueOrigin`.  Provenance contains M3 as a sublattice, so the infinite provenance lattice is
genuinely non-distributive (richer than the distributive chains). -/
theorem provenanceIsNonDistributive :
    ∃ first second third : ProvenanceGrade,
      ProvenanceGrade.meet first (ProvenanceGrade.join second third) ≠
        ProvenanceGrade.join (ProvenanceGrade.meet first second) (ProvenanceGrade.meet first third) :=
  ⟨.source 0, .source 1, .source 2, by decide⟩

/-! ## The distinctive provenance semantics — the top is a value a sink rejects, NOT a type error

§6.3: "functions requiring known provenance reject untracked data."  `isKnownSource` is that sink's guard.
The genuinely-new content: unlike clock's `crossDomainError` (a structural type error), provenance's `unknown`
is a LEGITIMATE value — reachable by merging two legitimate origins and freely inspectable — that the guard
merely REJECTS.  And combining two distinct origins LOSES the known-origin property: provenance tracking is the
statement that merged data carries no single known origin. -/

/-- The provenance-requiring sink's guard: a datum has known provenance iff its label is a concrete `source`.
`opaqueOrigin` (origin never granted) and `unknown` (origin lost through merging) are rejected. -/
def ProvenanceGrade.isKnownSource : ProvenanceGrade → Bool
  | .source _ => true
  | .opaqueOrigin => false
  | .unknown => false

/-- A concrete known origin passes the provenance guard. -/
theorem provenanceKnownSourceAccepts (originId : Nat) :
    ProvenanceGrade.isKnownSource (.source originId) = true := rfl

/-- `unknown` (the merged-away top) is REJECTED by the provenance guard — yet it is a well-formed value, not a
type error (the contrast with clock's `crossDomainError`). -/
theorem provenanceUnknownRejected :
    ProvenanceGrade.isKnownSource .unknown = false := rfl

/-- `opaqueOrigin` (the deny-by-default bottom) is REJECTED — provenance must be explicitly granted (§1.1). -/
theorem provenanceOpaqueRejected :
    ProvenanceGrade.isKnownSource .opaqueOrigin = false := rfl

/-- Two distinct origins MERGE to `unknown` — origins lose precision under combination (§6.3 "addition merges
chains"); the merged value is a legitimate `unknown`, reachable and inspectable. -/
theorem provenanceJoinDistinctSourcesIsUnknown (firstId secondId : Nat)
    (distinct : Nat.beq firstId secondId = false) :
    ProvenanceGrade.join (.source firstId) (.source secondId) = .unknown := by
  show (bif Nat.beq firstId secondId then ProvenanceGrade.source firstId else ProvenanceGrade.unknown)
     = ProvenanceGrade.unknown
  rw [distinct, Bool.cond_false]

/-- ★ **The provenance-tracking guarantee: merging two DISTINCT known origins LOSES the known-origin
property.**  Both inputs pass the guard (`isKnownSource (source _) = true`), but their merge does NOT
(`isKnownSource (join (source a) (source b)) = false` for `a ≠ b`) — combined-origin data carries no single
known provenance, so a provenance-requiring sink rejects it (the §25.5 supply-chain story).  Crucially the
merged value is `unknown`, a legitimate lattice element, not a stuck error. -/
theorem provenanceKnownSourceLostOnDistinctMerge (firstId secondId : Nat)
    (distinct : Nat.beq firstId secondId = false) :
    ProvenanceGrade.isKnownSource (.source firstId) = true ∧
    ProvenanceGrade.isKnownSource (.source secondId) = true ∧
    ProvenanceGrade.isKnownSource (ProvenanceGrade.join (.source firstId) (.source secondId)) = false :=
  ⟨rfl, rfl,
   (congrArg ProvenanceGrade.isKnownSource
     (provenanceJoinDistinctSourcesIsUnknown firstId secondId distinct)).trans provenanceUnknownRejected⟩

/-! ## Cross-family composition — two infinite-antichain lattice dimensions compose -/

/-- The `provenance × clock` composite lattice — the FIRST composition of TWO infinite-antichain dimensions
(provenance's origins and clock's domains). -/
def provenanceClockProductLattice : BoundedJoinSemilattice :=
  provenanceLattice.product clockLattice

/-- **Provenance × clock IS a lawful bounded join-semilattice** — TWO infinite-antichain dimensions compose
into one lawful lattice dimension via the shipped `productIsLawful`, with NO per-product re-proof.  Concrete
evidence that the §6.8 lattice-family composition is cardinality-agnostic even when BOTH factors are infinite
(prior compositions paired an infinite factor with a finite one). -/
theorem provenanceClockProductIsLawful :
    IsLawfulBoundedJoinSemilattice provenanceClockProductLattice :=
  BoundedJoinSemilattice.productIsLawful provenanceIsLawfulBoundedJoinSemilattice
    clockIsLawfulBoundedJoinSemilattice

end FX1Poly.Modal
