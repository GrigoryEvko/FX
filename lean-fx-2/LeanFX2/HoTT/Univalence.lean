import LeanFX2.HoTT.NTypes

/-! # HoTT/Univalence — Univalence as a derivable theorem (NEVER an axiom)

Univalence is the principle that **type equivalence equals type
equality**:

```
Univalence : (A B : Ty.universe lvl) → Conv (Ty.id (Ty.universe lvl) A B) (Ty.equiv A B)
```

(Voevodsky's formulation: the canonical map
`Id Type A B → Equiv A B` is itself an equivalence; equivalently, the
kernel sees the two types as definitionally interchangeable.)

## Zero-axiom commitment — NO EXCEPTIONS

Per `/root/iprit/FX/lean-fx-2/CLAUDE.md` "Zero-axiom commitment —
ABSOLUTE, NO EXCEPTIONS" and `AXIOMS.md` "NO documented exceptions":

* **No `axiom Univalence`.**  Period.
* **No `@[univalence_postulate]` attribute.**  The attribute itself
  was a deception scaffold and is forbidden.
* **No hypothesis-as-postulate.**  Theorems do NOT take `Univalence`
  as an input.  That pattern is the same lie as `axiom Univalence`,
  just with extra parameters.
* **No `IsUnivalent : Sort N` placeholder.**  A predicate that
  pretends to ship a result is not shipping a result.

Univalence is not provable in standard MLTT.  It enters lean-fx-2 as
a **`Step` reduction** — a constructor of an inductive relation, not
an axiom — and the result becomes a theorem with a real proof body.

## Plan: definitional univalence via `Step.eqType`

When `Reduction/Step.lean` ships the rule

```
Step.eqType {scope levelTy : Nat}
  (innerLevel : Nat) (innerLevelLt : innerLevel < levelTy)
  {leftTy rightTy : Ty innerLevel scope} :
  Step (Ty.id (Ty.universe (level := levelTy) (scope := scope) innerLevel innerLevelLt)
                leftTy rightTy)
       (Ty.equiv leftTy rightTy)
```

(or similar — exact shape determined when `Ty.universe` lands per
`kernel-sprint.md` D1.2 and the HOTT eqType rule lands per D2.6),
this file ships:

```lean
theorem Univalence
    {scope levelTy : Nat} (innerLevel : Nat) (innerLevelLt : innerLevel < levelTy)
    (leftTy rightTy : Ty innerLevel scope) :
    Conv (Ty.id (Ty.universe (level := levelTy) (scope := scope) innerLevel innerLevelLt)
                  leftTy rightTy)
         (Ty.equiv leftTy rightTy) :=
  Conv.fromStep (Step.eqType innerLevel innerLevelLt)
```

`#print axioms Univalence` then reports "does not depend on any axioms".

## Funext from `Step.eqArrow`

Same pattern.  When `Reduction/Step.lean` ships

```
Step.eqArrow {scope level : Nat} {domainTy codomainTy : Ty level scope}
    {leftFn rightFn : Term ... (Ty.arrow domainTy codomainTy) ...} :
  Step (Ty.id (Ty.arrow domainTy codomainTy) leftFn rightFn)
       (Ty.piTy domainTy (Ty.id codomainTy ...))
```

this file ships `theorem funext := Conv.fromStep Step.eqArrow`.

## Status (as of `kernel-sprint.md` cycle)

* `Step.eqType` / `Step.eqArrow` not yet shipped — see D2.6.
* `Univalence` / `funext` theorems land in this file the moment
  D2.6 lands.
* This file currently exposes NO declarations.  Empty namespace is
  fine; the file documents the commitment until the dependency
  resolves.

## Dependencies

* `Foundation/Ty.lean` — `Ty.universe` (D1.2), `Ty.id`, `Ty.equiv`,
  `Ty.arrow`, `Ty.piTy`
* `Reduction/Step.lean` — `Step.eqType` (D2.6), `Step.eqArrow` (D2.6)
* `Reduction/Conv.lean` — `Conv.fromStep`
* `HoTT/NTypes.lean` — n-type stratification (orthogonal but useful)

## Downstream consumers

* `HoTT/HIT/*` — HITs use the same `Step`-reduction pattern for their
  eliminators.  Zero axioms.
* `Cubical/Bridge.lean` — Path ↔ Id equivalence (D3.11) lives at
  set level and uses `Step.eqArrow`-style reductions for cubical
  funext.

## What this file MUST NOT do

* Declare `axiom Univalence` (banned).
* Declare `@[univalence_postulate]` attribute (banned).
* Declare `theorem foo (h : Univalence) : ...` taking univalence as
  a hypothesis (banned — hypothesis-as-postulate).
* Declare `def Univalence : Sort N := ...` as a placeholder
  predicate without a real proof (banned).
* Use `propext`, `Quot.sound`, `Classical.choice`, `funext`,
  `noncomputable`, `Inhabited` of unconstructible types, or any
  axiom-equivalent (banned).

If `Step.eqType` cannot be shipped, this file stays empty and the
`Univalence` theorem does not enter the project.  Better to lack
the result than to ship the deception.
-/

namespace LeanFX2

end LeanFX2
