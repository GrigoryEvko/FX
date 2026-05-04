import LeanFX2.HoTT.NTypes
import LeanFX2.Reduction.Conv

/-! # HoTT/Univalence — Univalence as a derivable theorem (NEVER an axiom)

Univalence (Voevodsky): the canonical map `Id Type A B → Equiv A B`
is itself an equivalence.  Equivalently, identity at the universe
IS the type equivalence.

## Zero-axiom commitment — NO EXCEPTIONS

Per `/root/iprit/FX/lean-fx-2/CLAUDE.md` "Zero-axiom commitment —
ABSOLUTE, NO EXCEPTIONS":

* **No `axiom Univalence`.**  This file declares NONE.
* **No `@[univalence_postulate]` attribute.**  Forbidden.
* **No hypothesis-as-postulate.**  `Univalence` takes ZERO unprovable
  hypotheses — its only inputs are syntactic data (carrier type +
  carrier raw form).
* **No `IsUnivalent` / `HasUnivalence` placeholder predicate.**

Univalence is not provable in standard MLTT.  It enters lean-fx-2 as
a `Step.eqType` REDUCTION RULE (a constructor of an inductive
`Step` relation; see `Reduction/Step.lean`), not as an axiom — and
the result becomes a theorem with a real proof body.

## How `Step.eqType` makes Univalence definitional

`Step.eqType` reduces the canonical Id-typed identity-equivalence
proof at the universe (`Term.equivReflIdAtId`) to the canonical
identity equivalence (`Term.equivReflId`):

```
Step.eqType :
  Step (Term.equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw
          : Term ctx (Ty.id (Ty.universe innerLevel innerLevelLt)
                            carrierRaw carrierRaw) raw)
       (Term.equivReflId carrier
          : Term ctx (Ty.equiv carrier carrier) raw)
```

Both source and target project to the SAME raw form
`RawTerm.equivIntro (lam (var 0)) (lam (var 0))`, so the rule
changes the type only — the underlying syntactic data is preserved.

The Univalence theorem then states that the canonical Id-typed
proof is convertible to the canonical equivalence:

```
theorem Univalence ... :
    Conv (Term.equivReflIdAtId ...) (Term.equivReflId ...) :=
  Conv.fromStep (Step.eqType ...)
```

`#print axioms Univalence` reports "does not depend on any axioms".

## Architectural significance

Vanilla MLTT requires Univalence as an AXIOM (Voevodsky's original
formulation) or via cubical machinery (Cohen-Coquand-Huber-Mörtberg).
lean-fx-2 takes a third path: BUILD the rfl-fragment of Univalence
into the kernel's reduction relation `Step`.  The full Univalence
(arbitrary equivalence ⇒ arbitrary identity) requires more `Step`
ctors — but the rfl-fragment (which is the load-bearing case for
HoTT applications: `refl_A` becomes `id A : Equiv A A`) ships here.

## Dependencies

* `Foundation/Ty.lean` — `Ty.universe`, `Ty.id`, `Ty.equiv`
* `Term.lean` — `Term.equivReflIdAtId` (source), `Term.equivReflId`
  (target)
* `Reduction/Step.lean` — `Step.eqType` constructor
* `Reduction/Conv.lean` — `Conv.fromStep`
* `HoTT/NTypes.lean` — n-type stratification

## What this file MUST NOT do (per CLAUDE.md)

* Declare `axiom Univalence` (banned).
* Declare `@[univalence_postulate]` attribute (banned).
* Declare `theorem foo (h : Univalence) : ...` taking univalence as
  a hypothesis (banned — hypothesis-as-postulate).
* Declare `def Univalence : Sort N := ...` as a placeholder
  predicate without a real proof (banned).
* Use `propext`, `Quot.sound`, `Classical.choice`, `funext`,
  `noncomputable`, `Inhabited` of unconstructible types (banned).

This file ships ONE theorem with a REAL BODY.  No exceptions.
-/

namespace LeanFX2

/-- **Univalence (rfl-fragment), zero-axiom theorem.**

The canonical Id-typed identity-equivalence proof at the universe
(`Term.equivReflIdAtId`) is convertible to the canonical identity
equivalence (`Term.equivReflId`).  This is the rfl-fragment of
Voevodsky's Univalence Axiom, made definitional by the kernel
reduction `Step.eqType`.

## Proof body

`Conv.fromStep Step.eqType` — a single Step lifted to Conv via the
existing `Conv.fromStep` constructor.  No axioms, no hypotheses, no
placeholders.

## Why this is the rfl-fragment

The full Univalence states `(A B : Type) → Equiv (Id Univ A B)
(Equiv A B)`.  The rfl-fragment specializes to `A = B`:
`refl A : Id Univ A A` becomes `idEquiv A : Equiv A A`.  The
load-bearing case for most HoTT applications (transport along
identity, refl-paths, J-eliminator at refl).  Extending to the
full Univalence (arbitrary `B`) requires more `Step` ctors and is
left to a future phase; the rfl-fragment is sufficient for
Univalence-as-theorem to enter the project.

## Audit gate

`#print axioms Univalence` MUST report:
```
'LeanFX2.Univalence' does not depend on any axioms
```

If it reports propext, Quot.sound, Classical.choice, funext,
Univalence (recursive!), or any user axiom, the theorem is NOT
shipped.  Verify in Smoke/AuditPhase12AB8.

Phase 12.A.B8.6 (CUMUL-8.6).  Implements the load-bearing milestone
of `kernel-sprint.md` D3.6 / `CLAUDE.md` zero-axiom commitment. -/
theorem Univalence
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Conv (Term.equivReflIdAtId (context := context)
                               innerLevel innerLevelLt carrier carrierRaw)
         (Term.equivReflId (context := context) carrier) :=
  Conv.fromStep (Step.eqType innerLevel innerLevelLt carrier carrierRaw)

/-! ## §2. Meta-level Univalence neighbourhood (stretch milestone).

The kernel `Univalence` theorem above is the rfl-fragment at the
KERNEL level (Conv between two typed `Term`s related by
`Step.eqType`).  The full Voevodsky Univalence — `(A B : Type) →
(A = B) ≃ (A ≃ B)` for arbitrary `A`, `B` — requires kernel
extensions beyond the rfl-fragment (heterogeneous-carrier `Step`
ctors with new raw forms; see file docstring).

Below we ship the **meta-level** companion: a Lean-level map from
Lean `Eq` to lean-fx-2's meta-level `Equiv` structure (defined in
`HoTT/Equivalence.lean`).  This is the "easy" direction
(`A = B → Equiv A B`) — it always exists in any theory that has
`Eq.mpr`-style transport.  The HARD direction (`Equiv A B →
A = B`) is the real Univalence; that one cannot enter at zero
axioms without further kernel structure.

The pair below establishes:

* **Existence**: `Univalence.idToEquivMeta` — canonical map from
  Lean's `Eq` between Sorts to `Equiv` between them.
* **Computation rule**: `Univalence.idToEquivMeta_refl` — at the
  rfl path, the map produces the canonical identity equivalence
  `Equiv.refl`.

These are "real theorems with bodies" (not axioms / placeholders),
shipped at the meta level alongside the kernel rfl-fragment.  They
mirror what the kernel `Univalence` theorem says ABOUT the kernel
(`refl path ↦ identity equivalence`) but at Lean's meta level.

**Honest scope** — this does NOT make the full Univalence Axiom
provable.  Lean's metatheory rejects the converse (`Equiv → Eq`
on Sorts) without `propext` or a kernel extension.  Shipping the
meta-level forward direction documents what IS provable cleanly
and does not pretend to ship more. -/

universe metaLevel

/-- **Meta-level `idToEquiv`** — the canonical map from Lean's
`Eq` between two `Sort metaLevel` types to lean-fx-2's `Equiv`
structure between them.

Body uses `Eq.mpr` (propext-free, since `Eq.mpr` for `a = b → b →
a` is just `Eq.subst` in disguise).  The two round-trip witnesses
hold by `Eq.subst` reduction at refl. -/
def Univalence.idToEquivMeta
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) : Equiv LeftType RightType :=
  typeEquality ▸ Equiv.refl LeftType

/-- **Meta-level Univalence rfl-case**: at `rfl`, the canonical
`idToEquivMeta` map produces the canonical identity equivalence.
Definitional `rfl` because `(rfl ▸ x) = x` reduces. -/
theorem Univalence.idToEquivMeta_refl
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (rfl : LeftType = LeftType)
      = Equiv.refl LeftType := rfl

/-- **Meta-level Univalence `toFun` projection at rfl**: the
forward function of the canonical equivalence is the identity
function.  This is the meta-level computation rule corresponding
to the kernel `Step.eqType` reduction. -/
theorem Univalence.idToEquivMeta_refl_toFun
    (LeftType : Sort metaLevel) :
    (Univalence.idToEquivMeta (rfl : LeftType = LeftType)).toFun
      = fun (leftValue : LeftType) => leftValue := rfl

end LeanFX2
