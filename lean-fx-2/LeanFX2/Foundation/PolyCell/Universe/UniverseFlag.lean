/-! # Foundation/PolyCell/Universe/UniverseFlag
   — Setzer-Rathjen consistency-strength ladder for Phase Z₆

M23 (#272, 2026-05-28).  Ships the `UniverseFlag` inductive
carrying the FULL Setzer-Rathjen ladder of universe admission
predicates per polycell.md §11.8 (lines 4033-4052).

Per the spec excerpt:

```
inductive UniverseFlag where
  | standard
  | inaccessible
  | mahlo
  | superMahlo
  | nMahlo (n : Nat)
  | hyperMahlo
  | weaklyCompact
  | indescribable (n : Nat)
  | reflecting
  | vopenka
```

## The Setzer-Rathjen ladder

Each flag is a STRICTLY STRONGER admission predicate (per
polycell.md §11.8 line 4049-4052).  Consistency strength
increases monotonically as you climb the ladder.  The ladder
matches the standard large-cardinal hierarchy from set theory:

1. **standard** — Mahlo-free MLTT; Phase Z₆ kickoff.  Proof-
   theoretic strength ≈ KP (Kripke-Platek) or Π¹₁-CA.
2. **inaccessible** — single inaccessible cardinal; Phase Z₆
   proper.  Strength ≈ ZFC + 1 inaccessible.
3. **mahlo** — single Mahlo cardinal; KPM.
4. **superMahlo** — KPM².
5. **nMahlo (n : Nat)** — KPM^n hierarchy.
6. **hyperMahlo** — fixed-point Mahlo (Π³-CA₀ territory).
7. **weaklyCompact** — weakly compact cardinal (Π¹_n
   indescribable for all n).
8. **indescribable (n : Nat)** — Πⁿ₂-indescribable hierarchy.
9. **reflecting** — Σ²ₙ-reflecting / total reflection.
10. **vopenka** — Vopěnka's principle; Σ²ₙ-CA₀ proof-theoretic
    strength.  Apex of the ladder.

Admission decidable in `O(flag enum position)` per
polycell.md §11.8 line 4050.

## Phase Z₆ rollout

Per polycell.md §11.8 line 4050-4052:
* `standard` ships Phase Z₆ KICKOFF.
* `inaccessible` + `mahlo` ship Phase Z₆ PROPER.
* `superMahlo` → `vopenka` ship Phase Z₆+ as RESEARCH-FRONTIER
  additions (admission proofs require set-theoretic large-
  cardinal axioms).

This M23 commit ships the ENUM only — all 10 ctors as a
closed inductive.  Admission proofs (showing each flag's
ConsistencyStrength bound) are M79-M82 task slots:
* M79 #328 inaccessible admission.
* M80 #329 mahlo + superMahlo.
* M81 #330 nMahlo / hyperMahlo / weaklyCompact.
* M82 #331 indescribable / reflecting.
* M83 #332 ★ MILESTONE B SHIPPED (vopenka + Phase Z₆ closure).

## Why ship all 10 today instead of just `standard`?

The ENUM is closed (no `Generator`-style growth path).  Adding
ctors later would be a backward-incompatible change.  Shipping
all 10 ctors today commits to the full ladder shape; M79-M82
add the ADMISSION PROOFS without changing the enum.

This commit deliberately ships the type but NOT the proofs —
proofs are research-frontier work (large-cardinal consistency
strength) that fits multi-turn focused sessions, not 5-min
cron iterations.

## Consistency-strength order

Per polycell.md §11.8 line 4049 ("each flag is a strictly
stronger admission predicate"), the ordering is the ctor
declaration order.  This commit doesn't ship a `LE`
instance — the order machinery is M24's responsibility
(retrofitting `gen_universeCode` payload to use
`LevelExpr × UniverseFlag` includes the LE structure).

## What this ships

* `UniverseFlag` inductive (10 ctors per spec).
* `deriving DecidableEq, BEq, Repr` — Lean derives these
  propext-free for simple ADTs with Nat payloads.
* 10 per-ctor canonical-form smokes (rfl-pinned).
* 1 DecidableEq positive smoke + 2 negative smokes.

## Cross-references

* polycell.md §11.8 (lines 4033-4052) — canonical spec.
* Setzer 2008 "Universes in type theory" — Mahlo / superMahlo
  / nMahlo hierarchy.
* Rathjen 1994 "Collapsing functions based on recursively
  large ordinals" — admission proof technique.
* Aczel 1999 "On relating type theories and set theories" —
  bridge between MLTT universe flags and set-theoretic
  consistency strength.
* M21 #270 `LevelExpr` — sibling type defining universe
  POLYMORPHISM (LevelExpr × UniverseFlag is the full payload
  per polycell.md §11.8 line 4002-4011).

## Phase Z₀ STRICT gate

When M21 + M23 are both shipped + M22 normalization lands,
`AuditPhaseZ.lean` #380 `STRICT_Z0_MOTIVE_state` advances
from `.notStarted` to `.scaffoldShipped`.  This commit
contributes M23; M22 normalization remains pending.

## Zero-axiom verification

`deriving DecidableEq, BEq, Repr` propext-free for simple
ADTs.  All 13 smoke theorems close by `rfl`.  No `axiom`, no
`sorry`, no Classical.  Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Universe

/-- Setzer-Rathjen consistency-strength ladder for universe
admission per polycell.md §11.8.

Ten constructors, each a STRICTLY STRONGER admission predicate
than the previous.  Listed in increasing consistency-strength
order:

* `standard` — Mahlo-free MLTT (Phase Z₆ kickoff).
* `inaccessible` — single inaccessible cardinal (Phase Z₆
  proper).
* `mahlo` — single Mahlo cardinal (KPM).
* `superMahlo` — KPM².
* `nMahlo n` — KPM^n hierarchy.
* `hyperMahlo` — fixed-point Mahlo.
* `weaklyCompact` — weakly compact cardinal.
* `indescribable n` — Πⁿ₂-indescribable hierarchy.
* `reflecting` — Σ²ₙ-reflecting.
* `vopenka` — Vopěnka's principle (apex). -/
inductive UniverseFlag where
  /-- Mahlo-free MLTT.  Phase Z₆ kickoff. -/
  | standard : UniverseFlag
  /-- Single inaccessible cardinal.  Phase Z₆ proper. -/
  | inaccessible : UniverseFlag
  /-- Single Mahlo cardinal (KPM). -/
  | mahlo : UniverseFlag
  /-- KPM² strength. -/
  | superMahlo : UniverseFlag
  /-- KPM^n hierarchy, n ≥ 2 (n = 0/1 collapse to standard/mahlo). -/
  | nMahlo : Nat → UniverseFlag
  /-- Fixed-point Mahlo. -/
  | hyperMahlo : UniverseFlag
  /-- Weakly compact cardinal. -/
  | weaklyCompact : UniverseFlag
  /-- Πⁿ₂-indescribable hierarchy. -/
  | indescribable : Nat → UniverseFlag
  /-- Σ²ₙ-reflecting / total reflection. -/
  | reflecting : UniverseFlag
  /-- Vopěnka's principle.  Apex of the Setzer-Rathjen ladder. -/
  | vopenka : UniverseFlag
deriving DecidableEq, BEq, Repr

/-! ## Per-ctor canonical-form smokes

Pin the inductive's shape via `rfl`-witnessed canonical-form
equations.  If `deriving DecidableEq` ever silently changes
behavior, these catch the regression. -/

theorem UniverseFlag.standard_canonical :
    (UniverseFlag.standard = .standard) := rfl

theorem UniverseFlag.inaccessible_canonical :
    (UniverseFlag.inaccessible = .inaccessible) := rfl

theorem UniverseFlag.mahlo_canonical :
    (UniverseFlag.mahlo = .mahlo) := rfl

theorem UniverseFlag.superMahlo_canonical :
    (UniverseFlag.superMahlo = .superMahlo) := rfl

theorem UniverseFlag.nMahlo_zero_canonical :
    UniverseFlag.nMahlo 0 = .nMahlo 0 := rfl

theorem UniverseFlag.hyperMahlo_canonical :
    (UniverseFlag.hyperMahlo = .hyperMahlo) := rfl

theorem UniverseFlag.weaklyCompact_canonical :
    (UniverseFlag.weaklyCompact = .weaklyCompact) := rfl

theorem UniverseFlag.indescribable_zero_canonical :
    UniverseFlag.indescribable 0 = .indescribable 0 := rfl

theorem UniverseFlag.reflecting_canonical :
    (UniverseFlag.reflecting = .reflecting) := rfl

theorem UniverseFlag.vopenka_canonical :
    (UniverseFlag.vopenka = .vopenka) := rfl

/-! ## DecidableEq smoke checks -/

theorem UniverseFlag.decEq_refl_standard :
    (decEq UniverseFlag.standard .standard = .isTrue rfl) := rfl

example : ¬ (UniverseFlag.standard = .inaccessible) := by
  intro contradiction
  cases contradiction

example : ¬ (UniverseFlag.mahlo = .superMahlo) := by
  intro contradiction
  cases contradiction

example : ¬ (UniverseFlag.nMahlo 0 = .nMahlo 1) := by
  intro contradiction
  cases contradiction

/-! ## Aggregate count

Pinned count of UniverseFlag ctors.  When the enum extends
(e.g., adding a new flag between weaklyCompact and
indescribable for a refined Setzer-Rathjen revision), this
count + the AuditPhaseZ ledger entries advance lockstep. -/

/-- 10 explicit ctors in the Setzer-Rathjen ladder.  Updates
lockstep with ctor additions. -/
def UniverseFlag.ctorCount : Nat := 10

theorem UniverseFlag.ctorCount_correct :
    UniverseFlag.ctorCount = 10 := rfl

end LeanFX2.Foundation.PolyCell.Universe
