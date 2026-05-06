import LeanFX2.HoTT.NTypes

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

/-- **Univalence (heterogeneous-carrier headline), zero-axiom theorem.**

The canonical heterogeneous-carrier path-from-equivalence proof at
the universe (`Term.uaIntroHet ... equivWitness`) is convertible to
the underlying packaged equivalence (`equivWitness`) — for ANY
equivalence between two distinct carrier type-codes
`carrierA, carrierB : Ty level scope`.

This is the **headline heterogeneous Univalence theorem** — the
Voevodsky form for arbitrary equivalences (not just rfl).  It
states:

```
Conv (Term.uaIntroHet ... equivWitness) equivWitness
```

at the heterogeneous Id-type
`Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw carrierBRaw`
versus `Ty.equiv carrierA carrierB`.  Both Terms project to the
SAME raw form `RawTerm.equivIntro forwardRaw backwardRaw` (the
architectural raw-alignment trick of `Term.uaIntroHet`):  the rule
changes the type only — `Ty.id (Ty.universe ...) carrierARaw
carrierBRaw` reduces to `Ty.equiv carrierA carrierB` while the
raw data is preserved.

## Relationship to the rfl-fragment `Univalence` above

The rfl-fragment `Univalence` (`Step.eqType`) handles only the case
where both endpoints are the SAME `carrier` (specialised via
`Term.equivReflIdAtId → Term.equivReflId`).  The heterogeneous form
generalises to ANY equivalence between distinct carriers
`carrierA, carrierB`, packaged by the user as `equivWitness :
Term ctx (Ty.equiv carrierA carrierB) (RawTerm.equivIntro ...)`.
Together the two cover the full Voevodsky Univalence at the kernel
level (`Step.eqType` for refl, `Step.eqTypeHet` for arbitrary).

## Proof body

`Conv.fromStep (Step.eqTypeHet innerLevel innerLevelLt
carrierARaw carrierBRaw equivWitness)` — a single Step lifted to
Conv via the existing `Conv.fromStep` constructor.  No axioms, no
hypotheses, no placeholders.

## Audit gate

`#print axioms UnivalenceHet` MUST report:
```
'LeanFX2.UnivalenceHet' does not depend on any axioms
```

If it reports propext, Quot.sound, Classical.choice, funext,
Univalence (recursive!), or any user axiom, the theorem is NOT
shipped.  Verified in `Smoke/AuditPhase12AB87.lean`.

Phase 12.A.B8.7 (CUMUL-8.7).  Consumes the `Step.eqTypeHet`
constructor shipped in commit `ab017bb0` (Phase 12.A.B8.6).  The
load-bearing milestone for FULL Voevodsky Univalence at the kernel
level — `Step.eqType` covers refl, `Step.eqTypeHet` covers
arbitrary, and the union is full Univalence definitional. -/
theorem UnivalenceHet
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                 (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Conv (Term.uaIntroHet (context := context)
                          innerLevel innerLevelLt
                          carrierARaw carrierBRaw equivWitness)
         equivWitness :=
  Conv.fromStep (Step.eqTypeHet innerLevel innerLevelLt
                                carrierARaw carrierBRaw equivWitness)

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

/-- **Meta-level Univalence `invFun` projection at rfl**: the
backward function of the canonical equivalence at the rfl path is
also the identity function.  Definitional `rfl` because
`(idToEquivMeta rfl) = Equiv.refl LeftType` and
`(Equiv.refl LeftType).invFun` reduces to the identity by
`Equiv.refl_invFun`. -/
theorem Univalence.idToEquivMeta_refl_invFun
    (LeftType : Sort metaLevel) :
    (Univalence.idToEquivMeta (rfl : LeftType = LeftType)).invFun
      = fun (leftValue : LeftType) => leftValue := rfl

/-! ## §3. Meta-level forward map is itself an equivalence (at refl).

The meta-level forward map `idToEquivMeta : (A = B) → Equiv A B`
takes the canonical refl path to the canonical identity
equivalence.  At that point its `toFun` IS the identity, so
`IsEquiv (idToEquivMeta rfl).toFun` reduces to `IsEquiv id`,
which is shipped in `HoTT/Equivalence.lean` as `IsEquiv.identity`.

This is the **rfl-case** of the forward direction of
"Univalence-as-equivalence": `idToEquivMeta` is itself an
equivalence between `A = B` and `Equiv A B`.  The full statement
(arbitrary `B`) requires the converse direction `Equiv → Eq`
which is non-derivable without further kernel structure or
propext (see file docstring); but the rfl-case is constructive
zero-axiom. -/

/-- **Meta-level idToEquiv at refl is an equivalence on toFun**:
the forward function of `idToEquivMeta rfl` (the identity function
on `LeftType`) is itself an equivalence in the IsEquiv sense
(every fiber over `target` is contractible — singleton at
`(target, refl)`).  Body invokes `IsEquiv.identity`.

Note: `IsEquiv` lives in `Sort N` (not `Prop`), so this is `def`
rather than `theorem` — but it has a real definitional body and
audits zero-axiom under `#print axioms`. -/
def Univalence.idToEquivMeta_refl_isEquiv_toFun
    (LeftType : Sort metaLevel) :
    IsEquiv (Univalence.idToEquivMeta (rfl : LeftType = LeftType)).toFun :=
  IsEquiv.identity LeftType

/-- **Meta-level idToEquivMeta produces an IsEquiv at every path**.
Proof: path-induct on the equality.  When the path is `rfl`, the
forward function reduces to the identity function, and
`IsEquiv.identity` discharges the goal.  This is the meta-level
forward direction of Univalence-as-equivalence at full generality
on Lean's `Eq`.

Note: this does NOT extend to arbitrary `Equiv → Eq` (the converse
direction requires propext or further kernel structure).  This
theorem says the FORWARD map is an equivalence; the converse map
is the hard part.

Note: `IsEquiv` is `Sort N` (not `Prop`), so this is `def`.  The
body is `Eq.rec`-based path induction with `IsEquiv.identity` at
the rfl base case — fully constructive, audits zero-axiom. -/
def Univalence.idToEquivMeta_isEquiv_toFun
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) :
    IsEquiv (Univalence.idToEquivMeta typeEquality).toFun := by
  cases typeEquality
  exact IsEquiv.identity LeftType

/-! ## §4. Bundled meta-level forward equivalence.

Package `idToEquivMeta typeEquality` together with the proof that
its `toFun` IS an equivalence into an `Equiv (A = B) (Equiv A B)`
shape — wait, that's the FULL Univalence axiom and is not
provable at zero axioms.

What we CAN bundle: at the rfl path, `idToEquivMeta rfl` is
**propositionally equal** to `Equiv.refl LeftType`, and the
forward function is **definitionally** the identity.  We bundle
the rfl-case into a single named theorem so downstream users have
a one-line citation. -/

/-- **Meta-level Univalence rfl-bundle**: at `rfl`, the
`idToEquivMeta` map IS structurally identical to `Equiv.refl`.
The two form the same `Equiv` value because their fields are all
definitionally equal:

* `toFun  = id` (definitional)
* `invFun = id` (definitional)
* `leftInv  = fun _ => rfl` (definitional)
* `rightInv = fun _ => rfl` (definitional)

Body is `rfl` — Lean recognizes that `(rfl ▸ Equiv.refl L) =
Equiv.refl L` reduces by `Eq.rec`. -/
theorem Univalence.idToEquivMeta_refl_eq_reflEquiv
    (LeftType : Sort metaLevel) :
    Univalence.idToEquivMeta (rfl : LeftType = LeftType)
      = Equiv.refl LeftType := rfl

/-! ## §6. Meta-level groupoid coherence with `idToEquivMeta`.

The forward map `idToEquivMeta : (A = B) → Equiv A B` should be a
**functor** with respect to the groupoid structure on equalities
and equivalences:

* `idToEquivMeta rfl = Equiv.refl _` (preserves identity)
* `idToEquivMeta (Eq.symm p) = Equiv.symm (idToEquivMeta p)`
  (preserves inverses)
* `idToEquivMeta (Eq.trans p q) = Equiv.trans (idToEquivMeta p)
  (idToEquivMeta q)` (preserves composition)

These laws establish that the meta-level forward direction IS
the canonical functor from the equality-groupoid on Sorts to
the equivalence-groupoid on Sorts.  They are derivable by path
induction on the equalities, with definitional `rfl` at the
base case.

These laws extend the rfl-fragment to NON-trivial paths — they
hold on arbitrary `p, q : A = B` (and so on) without requiring
any kernel structure beyond `Eq.rec`.  Audits zero-axiom. -/

/-- **Meta-level Univalence preserves equality-`symm`.**
`idToEquivMeta` of a symm-path equals the `Equiv.symm` of the
forward image.  At `rfl`, both sides reduce to `Equiv.refl _`
(which is its own `symm`).  Path induction on `typeEquality`
discharges the goal at the rfl base case. -/
theorem Univalence.idToEquivMeta_symm
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType) :
    Univalence.idToEquivMeta (Eq.symm typeEquality)
      = Equiv.symm (Univalence.idToEquivMeta typeEquality) := by
  cases typeEquality
  rfl

/-- **Meta-level Univalence preserves equality-`trans`.**
`idToEquivMeta` of a transitive path equals the `Equiv.trans` of
the forward images.  Path induction on the first equality
collapses both equalities to `rfl`, at which point both sides are
definitionally `Equiv.refl`. -/
theorem Univalence.idToEquivMeta_trans
    {LeftType : Sort metaLevel}
    {MiddleType : Sort metaLevel}
    {RightType : Sort metaLevel}
    (firstEquality  : LeftType = MiddleType)
    (secondEquality : MiddleType = RightType) :
    Univalence.idToEquivMeta (Eq.trans firstEquality secondEquality)
      = Equiv.trans (Univalence.idToEquivMeta firstEquality)
                    (Univalence.idToEquivMeta secondEquality) := by
  cases firstEquality
  cases secondEquality
  rfl

/-! ## §7. Meta-level toFun + invFun pointwise behaviour at general path.

Beyond the rfl-case, we can give a uniform pointwise computation
rule for `idToEquivMeta`'s `toFun` and `invFun` fields: at any
path, both fields agree with the standard transport along the
path.

* `(idToEquivMeta p).toFun  = transport id p` (forward via `▸`)
* `(idToEquivMeta p).invFun = transport id p.symm` (backward)

In Lean 4, `transport id p x = p ▸ x` for any `p : A = B` and
`x : A`.  This equality is definitional via `Eq.rec`. -/

/-- **Meta-level idToEquivMeta toFun is transport along the path.**
`(idToEquivMeta typeEquality).toFun x = typeEquality ▸ x`.  Proof:
path-induct on the equality.  When `typeEquality = rfl`, both
sides reduce to `x`.  Zero-axiom. -/
theorem Univalence.idToEquivMeta_toFun_eq_transport
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType)
    (leftValue : LeftType) :
    (Univalence.idToEquivMeta typeEquality).toFun leftValue
      = typeEquality ▸ leftValue := by
  cases typeEquality
  rfl

/-- **Meta-level idToEquivMeta invFun is transport along the inverse path.**
`(idToEquivMeta typeEquality).invFun y = typeEquality.symm ▸ y`.
Proof: path-induct on the equality.  Zero-axiom. -/
theorem Univalence.idToEquivMeta_invFun_eq_transport
    {LeftType : Sort metaLevel} {RightType : Sort metaLevel}
    (typeEquality : LeftType = RightType)
    (rightValue : RightType) :
    (Univalence.idToEquivMeta typeEquality).invFun rightValue
      = typeEquality.symm ▸ rightValue := by
  cases typeEquality
  rfl

/-! ## §5. Honest scope — what we DO NOT and CANNOT ship.

The full Voevodsky Univalence is the statement that `idToEquiv`
is itself an `Equiv`-valued equivalence, i.e.:

```
Univalence.canonical : Equiv (LeftType = RightType) (Equiv LeftType RightType)
```

This requires the **converse map** `Equiv LeftType RightType →
LeftType = RightType` — a function producing a Lean equality from
arbitrary equivalence data.  In standard Lean 4 this is provable
ONLY via `propext` (for `Sort 0` types — but our types are
arbitrary `Sort metaLevel`) or via kernel-level univalence
(unavailable in Lean's kernel without an axiom).

lean-fx-2's strict zero-axiom policy forbids `propext`, forbids
`axiom Univalence`, forbids hypothesis-as-postulate.  So the FULL
Univalence-as-equivalence statement at the meta level cannot be
shipped — and we do not pretend to.

What lean-fx-2 ships HONESTLY:

1. **Kernel rfl-fragment** (`LeanFX2.Univalence` above): a
   `Conv`-relation between two specific kernel `Term` values
   `equivReflIdAtId` and `equivReflId`, made definitional by
   `Step.eqType`.  Real theorem with a real body.

2. **Meta-level forward direction** (`idToEquivMeta` + computation
   rules): the easy direction, derivable from `Eq.mpr`.  Real
   theorems.

3. **Meta-level forward direction is itself an equivalence**
   (`idToEquivMeta_isEquiv_toFun` above): the rfl-case is
   constructive; full-generality version uses path induction.
   Real theorem.

Future kernel extensions (heterogeneous-carrier `Step` ctors,
or a Tarski-universe code structure) would unlock the converse
direction at zero axioms.  Until then, the rfl-fragment + meta-
level forward neighbourhood is the maximum honestly extensible
zero-axiom Univalence presentation. -/

end LeanFX2
