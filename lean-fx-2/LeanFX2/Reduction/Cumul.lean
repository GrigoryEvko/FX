import LeanFX2.Reduction.Conv
import LeanFX2.Foundation.Universe

/-! # Reduction/Cumul — universe-cumulativity Conv rules

**STATUS: SHIPPED (Phase 12.A.2 / kernel-sprint A2 deliverable).**

This file ships the load-bearing `Conv.cumul`-flavored theorems for FX's
universe hierarchy.  All theorems are real bodies (no `axiom`,
`sorry`, `admit`, `noncomputable`, hypothesis-as-postulate).  Each is
gated by `#print axioms` in `Smoke/AuditPhase12A2Cumul.lean` and must
report "does not depend on any axioms".

## What cumulativity says

In MTT, "cumulativity" is the rule that a term whose type lives at
universe `outerLevel.toNat + 1` is also definitionally at any larger
universe — the inner level `innerLevel` may be ANY level satisfying
`innerLevel.toNat ≤ outerLevel.toNat`.  The same raw form
`RawTerm.universeCode innerLevel.toNat` thus inhabits multiple typed
contexts, all the cumulativity witnesses are mutually convertible.

## What we ship

### Same-level cumul (`Conv.cumul_refl`)

Two universe-codes at the same `outerLevel`, same `innerLevel`,
same `cumulOk` proof, same `levelEq` proof are Conv-equal
(directly via `Conv.refl`).

### Proof-irrelevance cumul (`Conv.cumul_proof_irrel`)

Two universe-codes at the same `outerLevel` and same `innerLevel`
but with possibly different `cumulOk` witnesses are Conv-equal.
This is the substantive zero-axiom theorem: it relies on the
fact that `Nat.le` is a Prop, so the two `cumulOk` proofs are
definitionally equal (`Nat.le_refl` on Nat hits this); hence
the two Term values are definitionally equal at the level of
the Term inductive (proof irrelevance via Subsingleton-of-Prop),
and `Conv.refl` discharges.

### Cross-level cumul `Conv.cumul_raw` (cross-level via shared raw)

Two universe-codes at DIFFERENT outer levels but the same inner
level project to the same raw form `RawTerm.universeCode
innerLevel.toNat` regardless of outer level.  This theorem
states that fact at the `Term.toRaw` level — provable by `rfl`
because `Term.toRaw_universeCode` is definitional.  Cross-level
`Conv` itself is not directly expressible (the relation requires
matched `level` indices), so we expose the raw-form equality as
the cross-level cumulativity bridge.

## Why a Conv rule, not a Term coercion

If `cumul` were a term-level ctor `Term.cumul ▸`, every reduction
lemma would need a cumul case, blowing up `cd_lemma` across all 53+
Step ctors.  Treating it as a Conv rule means the typechecker silently
accepts cumul-related convertibility without rewriting the term.  This
matches the standard MTT formulation.

## Audit gates

`Smoke/AuditPhase12A2Cumul.lean` runs `#print axioms` on every theorem
in this file and the supporting `Term.universeCode` ctor.  All must
report "does not depend on any axioms".

## Dependencies

* `Reduction/Conv.lean` — base `Conv` definition + `Conv.refl` etc.
* `Foundation/Universe.lean` — `UniverseLevel` + preorder
* `Term` (root file) — `Term.universeCode` ctor

## Phase rollout

* **Phase 12.A.2 (HERE)**: ship `Conv.cumul_refl`,
  `Conv.cumul_proof_irrel`, and `Conv.cumul_raw_shared`.  Algorithmic
  insertion of cumul coercions during elaboration is deferred to a
  later phase (Algo/Check changes touch the bidirectional checker).
-/

namespace LeanFX2

/-- **Same-level cumul (the trivial case)**: two universe-codes at the
same outer level with the same inner level, same cumul witness, same
level-equation are Conv-equal.  Body is `Conv.refl`. -/
theorem Conv.cumul_refl
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelEq : level = outerLevel.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelEq)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelEq) :=
  Conv.refl _

/-- **Cumulativity-witness equivalence**: two universe-codes at the
same outer level with the same inner level but POSSIBLY DIFFERENT
cumul witnesses are Conv-equal.  Body uses Subsingleton-on-`Nat.le`
(decidable Prop with proof irrelevance) to collapse the two proofs to
the same Term value, then discharges with `Conv.refl`. -/
theorem Conv.cumul_proof_irrel
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk1 cumulOk2 : innerLevel.toNat ≤ outerLevel.toNat)
    (levelEq : level = outerLevel.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk1 levelEq)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk2 levelEq) := by
  -- `Nat.le` is a Subsingleton: any two proofs are propositionally
  -- equal.  We extract this via `Subsingleton.elim`, then cast both
  -- terms into a common shape and discharge with `Conv.refl`.
  have proofIrrel : cumulOk1 = cumulOk2 := Subsingleton.elim cumulOk1 cumulOk2
  cases proofIrrel
  exact Conv.refl _

/-- **Raw-form sharing** (cross-level cumul bridge): two universe-codes
at different outer levels with the same inner level project to the
same `RawTerm.universeCode innerLevel.toNat`.

This is the cross-level cumulativity statement at the level the
ambient `Conv` relation can express.  `Conv` itself requires source
and target to share `level scope` indices in their `context : Ctx mode
level scope`, so cross-level Conv between `Ty.universe outerLow` (at
`outerLow.toNat + 1`) and `Ty.universe outerHigh` (at `outerHigh.toNat
+ 1`) is not directly expressible.  Instead, this theorem expresses
the underlying invariant: both cumulativity witnesses produce the same
underlying raw term.  Body: `rfl`, because `Term.toRaw` on
`Term.universeCode` is definitionally `RawTerm.universeCode
innerLevel.toNat` regardless of outer level. -/
theorem Conv.cumul_raw_shared
    {mode : Mode} {scope levelLow levelHigh : Nat}
    {contextLow : Ctx mode levelLow scope}
    {contextHigh : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelEqLow : levelLow = outerLow.toNat + 1)
    (levelEqHigh : levelHigh = outerHigh.toNat + 1) :
    Term.toRaw (Term.universeCode (context := contextLow) innerLevel
                                  outerLow cumulOkLow levelEqLow)
      = Term.toRaw (Term.universeCode (context := contextHigh) innerLevel
                                      outerHigh cumulOkHigh levelEqHigh) :=
  rfl

/-- **Same-context cumul across distinct outer levels**: when both
universe-codes happen to live in the same context (same `level`), the
outer-level alignment forces `outerLow.toNat + 1 = outerHigh.toNat +
1`, hence `outerLow.toNat = outerHigh.toNat` (`Nat.succ.inj`).  When
additionally the outer `UniverseLevel` constructors are equal, the two
universe-codes coincide as Term values and `Conv.refl` discharges.

This is the closest one can get to a same-level Conv-cumul rule
between distinct UniverseLevel-witnesses without expanding the Conv
relation itself.  Body: cumulOk-proof-irrelevance via Subsingleton, then
`Conv.refl`. -/
theorem Conv.cumul_outer_eq
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevelA outerLevelB : UniverseLevel)
    (outerEq : outerLevelA = outerLevelB)
    (cumulOkA : innerLevel.toNat ≤ outerLevelA.toNat)
    (cumulOkB : innerLevel.toNat ≤ outerLevelB.toNat)
    (levelEqA : level = outerLevelA.toNat + 1)
    (levelEqB : level = outerLevelB.toNat + 1) :
    Conv (Term.universeCode (context := context) innerLevel outerLevelA
                            cumulOkA levelEqA)
         (Term.universeCode (context := context) innerLevel outerLevelB
                            cumulOkB levelEqB) := by
  -- Align outerLevelB to outerLevelA via `outerEq`.  Once aligned,
  -- the only remaining variation is the cumul witness, which collapses
  -- to a single value via Subsingleton; the levelEq proofs then
  -- become identical, and `Conv.refl` discharges.
  cases outerEq
  -- Now `outerLevelA = outerLevelB` (same UniverseLevel value).
  -- The two cumul witnesses are equal by Subsingleton on Nat.le.
  have proofIrrelCumul : cumulOkA = cumulOkB :=
    Subsingleton.elim cumulOkA cumulOkB
  cases proofIrrelCumul
  -- Now the two levelEq proofs (equality at Nat) are also Subsingleton-
  -- equal; collapse them similarly.
  have proofIrrelLevel : levelEqA = levelEqB :=
    Subsingleton.elim levelEqA levelEqB
  cases proofIrrelLevel
  exact Conv.refl _

end LeanFX2
