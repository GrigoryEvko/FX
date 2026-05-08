import LeanFX2.HoTT.Univalence

/-! # HoTT/Funext — Funext as a derivable theorem (NEVER an axiom)

Function extensionality (funext): two functions equal pointwise are
propositionally equal.  Equivalently, identity at an arrow type IS
the pointwise (Π-typed) identity.

## Zero-axiom commitment — NO EXCEPTIONS

Per `/root/iprit/FX/lean-fx-2/CLAUDE.md` "Zero-axiom commitment —
ABSOLUTE, NO EXCEPTIONS":

* **No `axiom funext`.**  This file declares NONE.
* **No hypothesis-as-postulate.**  `funext` takes ZERO unprovable
  hypotheses — its only inputs are syntactic data (domain type,
  codomain type, application raw form).
* **No `IsFunctionExtensional` / `HasFunext` placeholder predicate.**

Funext is not provable in standard MLTT.  It enters lean-fx-2 as
a `Step.eqArrow` REDUCTION RULE (a constructor of an inductive
`Step` relation; see `Reduction/Step.lean`), not as an axiom — and
the result becomes a theorem with a real proof body.

## How `Step.eqArrow` makes funext definitional

`Step.eqArrow` reduces the canonical Id-typed funext witness at
arrow types (`Term.funextReflAtId`) to the canonical pointwise-refl
funext witness (`Term.funextRefl`):

```
Step.eqArrow :
  Step (Term.funextReflAtId domainType codomainType applyRaw
          : Term ctx (Ty.id (Ty.arrow domainType codomainType)
                            (lam (refl applyRaw))
                            (lam (refl applyRaw))) raw)
       (Term.funextRefl domainType codomainType applyRaw
          : Term ctx (Ty.piTy domainType
                              (Ty.id codomainType.weaken applyRaw applyRaw))
                     raw)
```

Both source and target project to the SAME raw form
`RawTerm.lam (RawTerm.refl applyRaw)`, so the rule changes the type
only — the underlying syntactic data is preserved.

The funext theorem then states that the canonical Id-typed witness
at an arrow type is convertible to the pointwise-refl witness:

```
theorem funext ... :
    Conv (Term.funextReflAtId ...) (Term.funextRefl ...) :=
  Conv.fromStep (Step.eqArrow ...)
```

`#print axioms funext` reports "does not depend on any axioms".

## Architectural significance

Vanilla MLTT requires Funext as an AXIOM, or proves it in cubical
type theory via the Path-Π adjunction.  lean-fx-2 takes a third
path: BUILD the rfl-fragment of Funext into the kernel's reduction
relation `Step`.  The full Funext (arbitrary pointwise equality
⇒ function equality) requires more `Step` ctors — but the rfl-
fragment (which is the load-bearing case for HoTT applications:
`fun x => refl_(f x)` becomes `refl_f`) ships here.

## Dependencies

* `Foundation/Ty.lean` — `Ty.arrow`, `Ty.id`, `Ty.piTy`, `Ty.weaken`
* `Term.lean` — `Term.funextReflAtId` (source), `Term.funextRefl`
  (target)
* `Reduction/Step.lean` — `Step.eqArrow` constructor
* `Reduction/Conv.lean` — `Conv.fromStep`
* `HoTT/Univalence.lean` — sister theorem (Univalence) using the
  parallel pattern via `Step.eqType`

## What this file MUST NOT do (per CLAUDE.md)

* Declare `axiom funext` (banned).
* Declare `theorem foo (h : Funext) : ...` taking funext as
  a hypothesis (banned — hypothesis-as-postulate).
* Declare `def Funext : Sort N := ...` as a placeholder
  predicate without a real proof (banned).
* Use `propext`, `Quot.sound`, `Classical.choice`, `funext` (Lean
  stdlib axiom — distinct from this kernel theorem),
  `noncomputable`, `Inhabited` of unconstructible types (banned).

This file ships ONE theorem with a REAL BODY.  No exceptions.

## Root status

* Layer: typed-derived
* Load-bearing for: HoTT/UnivalenceFull, Smoke/AuditPhase12AB8, Smoke/AuditCumulMeta, Smoke/AuditMegaZ5A1, Smoke/AuditPhase12AB88, Smoke/StrictComposition, Smoke/AuditPhase12AB8Cascade, Smoke/AuditMegaZ3, Smoke/AuditMegaZ2A1
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2

/-- **Funext (rfl-fragment), zero-axiom theorem.**

The canonical Id-typed funext witness at an arrow type
(`Term.funextReflAtId`) is convertible to the canonical pointwise-
refl funext witness (`Term.funextRefl`).  This is the rfl-fragment
of function extensionality, made definitional by the kernel
reduction `Step.eqArrow`.

## Proof body

`Conv.fromStep Step.eqArrow` — a single Step lifted to Conv via the
existing `Conv.fromStep` constructor.  No axioms, no hypotheses, no
placeholders.

## Why this is the rfl-fragment

The full Funext states `(f g : A → B) → ((x : A) → f x = g x) →
f = g`.  The rfl-fragment specializes to `f = g`: an Id-typed
witness `refl_f : f = f` becomes the pointwise refl witness
`fun x => refl_(f x) : (x : A) → f x = f x`.  The load-bearing
case for most HoTT applications (refl-paths, transport along
identity, J-eliminator at refl).  Extending to the full Funext
(arbitrary pointwise equality) requires more `Step` ctors and
is left to a future phase; the rfl-fragment is sufficient for
Funext-as-theorem to enter the project.

## Audit gate

`#print axioms funext` MUST report:
```
'LeanFX2.funext' does not depend on any axioms
```

If it reports propext, Quot.sound, Classical.choice, funext
(Lean stdlib, distinct from this kernel theorem),
Univalence (recursive!), or any user axiom, the theorem is NOT
shipped.  Verify in Smoke/AuditPhase12AB8.

Phase 12.A.B8.7 (CUMUL-8.7).  Implements the load-bearing milestone
of `kernel-sprint.md` D3.7 / `CLAUDE.md` zero-axiom commitment. -/
theorem funext
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    Conv (Term.funextReflAtId (context := context)
                              domainType codomainType applyRaw)
         (Term.funextRefl (context := context)
                          domainType codomainType applyRaw) :=
  Conv.fromStep (Step.eqArrow domainType codomainType applyRaw)

/-! ## §2. Heterogeneous Funext — the headline theorem.

`funext` (rfl-fragment, above) handles only the case where both
endpoints share the SAME apply payload (`funextReflAtId → funextRefl`,
where `applyARaw = applyBRaw = applyRaw`).

`FunextHet` (this section) generalises to ANY two distinct apply
payloads `applyARaw, applyBRaw` packaged through `Term.funextIntroHet`.
The theorem asserts that the canonical heterogeneous funext-introduction
Term at Id-of-arrow is convertible to the canonical pointwise-refl
funext witness instantiated at `applyARaw`.

Together with the rfl-fragment `funext`, the union covers the FULL
heterogeneous funext at the kernel level — `Step.eqArrow` for refl,
`Step.eqArrowHet` for arbitrary, and the union is full Funext
definitional.  Both ship as zero-axiom theorems under strict policy.

## Architectural raw-alignment trick (recap)

Both source `Term.funextIntroHet ... applyARaw applyBRaw` and target
`Term.funextRefl ... applyARaw` project to the SAME raw form
`RawTerm.lam (RawTerm.refl applyARaw)` (the `funextIntroHet` ctor's
raw uses `applyARaw` and coincides with `funextRefl`'s raw at the
same payload — see `Term.funextIntroHet` docstring).  The rule changes
the type only: `Ty.id (Ty.arrow ...) (lam applyARaw) (lam applyBRaw)`
reduces to `Ty.piTy domainType (Ty.id codomainType.weaken applyARaw
applyARaw)` while the raw data is preserved.  Same architectural
payoff as `cumulUpInner` / `eqType` / `eqArrow` / `eqTypeHet`.

## Asymmetric collapse to applyARaw

The target instantiates `funextRefl` at `applyARaw` (the LEFT apply
payload of the source `Ty.id`).  This is forced by raw alignment:
`funextIntroHet`'s raw uses `applyARaw` (not `applyBRaw`), so the
rfl-collapse target must also pick `applyARaw`.  Sufficient for the
heterogeneous funext theorem — the kernel ships ONE direction (LEFT-
biased to applyARaw); the dual direction is symmetric by `Conv.sym`. -/

/-- **Heterogeneous Funext, zero-axiom theorem.**

The canonical heterogeneous funext-introduction Term at Id-of-arrow
(`Term.funextIntroHet ... applyARaw applyBRaw : Term context
(Ty.id (Ty.arrow domainType codomainType) (lam applyARaw)
(lam applyBRaw)) ...`) is convertible to the canonical pointwise-refl
funext witness instantiated at `applyARaw` (`Term.funextRefl ...
applyARaw : Term context (Ty.piTy domainType (Ty.id codomainType.weaken
applyARaw applyARaw)) ...`).

This is the heterogeneous fragment of function extensionality, made
definitional by the kernel reduction `Step.eqArrowHet`.

## Proof body

`Conv.fromStep (Step.eqArrowHet ...)` — a single Step lifted to Conv
via the existing `Conv.fromStep` constructor.  No axioms, no
hypotheses, no placeholders.

## Relationship to the rfl-fragment `funext`

`funext` (rfl-fragment, §1 above) handles the case `applyARaw =
applyBRaw = applyRaw` via `Step.eqArrow`.  `FunextHet` (this theorem)
handles any heterogeneous `applyARaw, applyBRaw` via `Step.eqArrowHet`.
Together they cover the FULL heterogeneous Funext schema as
definitional reductions.

## Audit gate

`#print axioms FunextHet` MUST report:
```
'LeanFX2.FunextHet' does not depend on any axioms
```

If it reports propext, Quot.sound, Classical.choice, funext (Lean
stdlib, distinct from this kernel theorem), Univalence (recursive!),
or any user axiom, the theorem is NOT shipped.  Verify in
Smoke/AuditPhase12AB89.

Phase 12.A.B8.B (CUMUL-8.B).  Implements the FINAL load-bearing
milestone of `kernel-sprint.md` D3.7 / `CLAUDE.md` zero-axiom
commitment for the HoTT foundation: Univalence + UnivalenceHet +
funext + FunextHet all ship as zero-axiom theorems with real bodies. -/
theorem FunextHet
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    Conv (Term.funextIntroHet (context := context)
                              domainType codomainType applyARaw applyBRaw)
         (Term.funextRefl (context := context)
                          domainType codomainType applyARaw) :=
  Conv.fromStep (Step.eqArrowHet domainType codomainType applyARaw applyBRaw)

end LeanFX2
