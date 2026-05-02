import LeanFX2.Reduction.Conv
import LeanFX2.Foundation.Universe

/-! # Reduction/Cumul — cumulativity Conv rule (structural scaffold)

**STATUS: Structural scaffold for FUTURE integration.**

When `Ty.universe (level : Nat) : Ty (level+1) scope` is added to the
Ty inductive (per `Foundation/Universe.lean`'s phased rollout), this
file will host the `Conv.cumul` rule — a definitional-conversion rule
that says "a Ty at lower universe level is convertible to the same Ty
viewed at a higher universe level".

## Planned rule shape

```lean
theorem Conv.cumul {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {lowerLevel upperLevel : Nat}
    (levelLe : Ty.universeLe lowerLevel upperLevel)
    (sourceTerm : Term context (Ty.universe lowerLevel) sourceRaw)
    (targetTerm : Term context (Ty.universe upperLevel) targetRaw)
    -- Both terms project to the same RawTerm
    (rawsEqual : sourceRaw = targetRaw) :
    Conv sourceTerm targetTerm
```

The rule says: a term whose type is `Ty.universe lowerLevel` (a small
universe) and another whose type is `Ty.universe upperLevel` (a larger
universe) — IF their raw projections are equal AND the level
relationship is `lowerLevel ≤ upperLevel` — are definitionally
convertible.

## Why definitional, not propositional

In MTT (Martin-Löf Type Theory), cumulativity is part of the
**definitional equality**, not a separate coercion.  Every term-level
reduction respects the level relation; the only place levels enter
is at the universe-of-types ctor.  Treating cumulativity as `Conv`
preserves the canonical form / Church-Rosser argument because:
* Reduction doesn't change `Ty.universe N`'s level
* The `Conv.cumul` rule is **bidirectional** in the sense that
  `Conv (Ty.universe u) (Ty.universe v)` holds when `u ≤ v` OR
  `v ≤ u`; we use whichever direction we need

## Why a Conv rule, not a Term coercion

If `Ty.universe` were a term-level coercion ctor like `Term.cumul ▸`,
then every type-checking step would need to insert/remove these
coercions explicitly.  Treating it as a Conv rule means the typechecker
silently accepts `cumul`-related convertibility without rewriting the
term.  This is the standard MTT formulation.

Alternative (rejected): `Term.cumul level1 level2 (term : Term ... (Ty.universe level1) raw) :
  Term ... (Ty.universe level2) raw`.  Adding this would force every
reduction lemma to handle the cumul case explicitly, blowing up cd_lemma
across all 53+ Step ctors.  REJECTED per `feedback_lean_cumul_subst_mismatch.md`
(lean-fx attempted this and reverted at v1.29).

## Phased rollout

* **Now (Phase 1.G structural)**: this file; only documentation.  No
  Conv.cumul declared yet because Ty.universe doesn't exist yet.
* **Phase X.Y**: `Ty.universe` ctor lands in Foundation/Ty.lean.
  All Ty.rename / Ty.subst / Ty.subst_pointwise arms gain `.universe`
  case.
* **Phase X.Y+1**: `Conv.cumul` rule added here.  Decidable instance
  via `Ty.universeLe_decidable`.  cd_lemma cumul case is
  `Conv.refl`-via-`Conv.cumul`-projection.
* **Phase X.Y+2**: Algo/Check inserts cumul coercions automatically
  during elaboration.  Surface-syntax types at unannotated levels
  default to `level := 0` and elaborate-up via cumul as needed.

## Conv.cumul interaction with cd_lemma (planned)

For confluence, the cumul rule preserves canonical form: if
`Conv.cumul levelLe t t'`, then `Term.cd t' = Term.cd t` (canonical
forms are invariant under cumulativity, since they project the same
raw).  The diamond property holds trivially because cumul is a
"horizontal" Conv rule (not a reduction step).

## Audit gates

When Conv.cumul lands, smoke `AuditPhase3Cumul` will gate:
* `Conv.cumul` zero-axiom
* `Conv.cumul`-decidability via `Ty.universeLe_decidable`
* `Term.cd` cumul case zero-axiom
* `Step.parStar.confluence` still zero-axiom after cumul lands

## Dependencies

* `Reduction/Conv.lean` — base Conv structure
* `Foundation/Universe.lean` — preorder + decidability

## Downstream consumers (after rollout)

* `Algo/Check.lean` — inserts cumul coercions during type-checking
* `Confluence/CdLemma.lean` — cumul case (trivial — Term.cd unaffected)
-/

namespace LeanFX2

end LeanFX2
