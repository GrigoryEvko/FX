import FX1Poly.Typed.Fib.ModedLockContext
import FX1Poly.Typed.Fib.ModeLockPath
import FX1Poly.Typed.Metatheory.HostAdmissibility.OfGrownArmReflection

/-! # FX1Poly/Typed/Fib/ModedLockFreePredicate — #7B: the DECIDABLE lock-free predicate over the
mode-indexed lock telescope, and the REAL discharge of the retirement Tier E `ofGrownReflected` side condition

The retired-`ofGrown` capstone `HasTypeDescPi.ofGrownReflected` (Retirement Brick 1) carries a single side
condition `context.isLockFreeContext = true` — the Fitch A1-RESTRICT lock-accessibility discharge.  On the
kernel telescope that predicate is already shipped structurally (`DimensionLockAccessibility.isLockFreeContext`:
`empty ↦ true`, `cons ↦ recurse`, `lockCons ↦ false`), but two things were missing to make the side condition a
GENUINE, computed, mode-theoretically-meaningful discharge rather than an opaque assumption:

  1. the SAME structural lock-free predicate over the GENERAL mode-indexed lock telescope `ModedContext`
     (fib-3 #3), so lock-freeness is stated over the carrier whose `locks(Δ)` composes real `ModalityPath`s;
  2. the BRIDGE that upgrades the opaque `Bool` flag to the mode-theoretic statement
     `locks(Δ) = id` — the total lock modality of the context's mode-shape is the IDENTITY 1-cell.

This file ships all of that, additively:

  * `ModedContext.isLockFree` — the byte-mirror of `TypingContext.isLockFreeContext` over the mode-indexed
    telescope (a context is lock-free iff no `lockCons` appears), with three `rfl` unfolders and a
    `Decidable` instance (`Bool`-reflection);
  * `ModedContext.lockFreeImpliesLocksLengthZero` — over ANY mode graph, a lock-free context's total lock
    modality has LENGTH 0 (the identity 1-cell, propext-free `Nat` statement, no dependent transport);
  * `ModedContext.affineLockFreeImpliesLocksIdentity` — over the affine dimension graph, a lock-free
    context's `locks(Δ)` is exactly `obligationModalityToPath .fibrant` (the shipped affine identity 1-cell),
    with the converse witness `affineSingleLockContextNotLockFree` (a genuine lock is NOT lock-free and its
    `locks` has length one);
  * `TypingContext.toModedShape` + `isLockFreeContext_eq_toModedShape_isLockFree` — the REFLECTION: the
    kernel's `Bool` lock-free predicate EQUALS the mode-indexed predicate on the forgotten lock-shape (all
    `rfl` arms — same structural recursion);
  * `TypingContext.lockFreeImpliesShapeLocksIdentity` — the mode-theoretic MEANING of the Tier E side
    condition: `isLockFreeContext = true` says the mode-shape's `locks(Δ)` is the identity 1-cell;
  * `HasTypeDescPi.ofGrownReflectedDecidably` — the DECIDED discharge: `ofGrownReflected` re-exposed with the
    side condition supplied by the decidable check (`decide (…) = true`), so a caller at any concretely
    lock-free context discharges it by computation (`by decide` / `rfl`), not by a hand-supplied assumption.

HONESTY: the lock-free ⟹ `locks = id` implication is ONE direction — `isLockFree` detects the STRUCTURAL
presence of a `lockCons`, which is STRICTLY STRONGER than `locks(Δ) = id` (a `lockCons` carrying an identity
path would have trivial `locks` yet not be structurally lock-free).  Over the kernel's `toModedShape` image
the two coincide (every reflected `lockCons` carries the length-one affine generator), so on kernel contexts
lock-freeness is exactly `locks(shape) = id` (`isLockFreeContext_eq_toModedShape_isLockFree` +
`affineLockFreeImpliesLocksIdentity`).  This does NOT flip the fib-3 dimension-2 keystone
(`fxMode_hasDecidableTwoCellEquality`), which stays walled: dimension-1 (1-cell length) only.

## Zero-axiom

`Bool`-valued structural recursions over the two telescopes, `rfl` unfolders, `Nat` length arithmetic, a
`Bool.noConfusion` on the impossible `lockCons` arm, and `of_decide_eq_true` (Init) for the decided capstone.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/Typed/Fib/ModedLockFreePredicate.lean`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Polygraph

namespace ModedContext

/-- ★ **#7B: the mode-indexed lock-free predicate.**  Decide whether a mode-indexed context is free of
dimension locks: `true` iff no `lockCons` appears anywhere in the telescope (a plain `cons` — CX/EXTEND — adds
none).  The byte-mirror of the kernel's `TypingContext.isLockFreeContext`, lifted from the mono-modality
telescope to the general mode axis.  A context is lock-free iff no `lockCons`. -/
def isLockFree {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode} :
    ModedContext graph Binding ambientMode → Bool
  | .empty _ => true
  | .cons restContext _binding => restContext.isLockFree
  | .lockCons _restContext _lockModality => false

/-- Unfolder: the empty context is lock-free. -/
theorem isLockFree_empty {graph : ModeGraph} {Binding : graph.Mode → Type} (mode : graph.Mode) :
    (ModedContext.empty (Binding := Binding) mode).isLockFree = true :=
  rfl

/-- Unfolder: a `cons` (CX/EXTEND) is lock-free exactly when its prefix is. -/
theorem isLockFree_cons {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode}
    (restContext : ModedContext graph Binding ambientMode) (binding : Binding ambientMode) :
    (restContext.cons binding).isLockFree = restContext.isLockFree :=
  rfl

/-- Unfolder: a `lockCons` (CX/LOCK) is never lock-free (it IS a lock). -/
theorem isLockFree_lockCons {graph : ModeGraph} {Binding : graph.Mode → Type}
    {ambientMode newAmbientMode : graph.Mode}
    (restContext : ModedContext graph Binding ambientMode)
    (lockModality : ModalityPath graph newAmbientMode ambientMode) :
    (restContext.lockCons lockModality).isLockFree = false :=
  rfl

/-- The lock-free predicate is DECIDABLE (a `Bool`-reflection): `isLockFree` returns a `Bool`, so
`isLockFree = true` is decided by `Bool` equality.  This is what makes the retirement Tier E side condition a
COMPUTED discharge rather than a hand-supplied assumption. -/
instance decidableIsLockFree {graph : ModeGraph} {Binding : graph.Mode → Type}
    {ambientMode : graph.Mode} (context : ModedContext graph Binding ambientMode) :
    Decidable (context.isLockFree = true) :=
  inferInstanceAs (Decidable (context.isLockFree = true))

/-- ★ **The general rigorous bridge (any mode graph).**  A lock-free context's total lock modality
`locks(Δ)` has LENGTH 0 — it is the identity 1-cell.  Stated on the `Nat` length (no dependent transport
across `baseModeOf`), so it is propext-free and holds over an arbitrary `ModeGraph`.  Structural recursion:
`empty ↦ 0`, `cons` transparently recurses, `lockCons` is impossible (`isLockFree = false`). -/
theorem lockFreeImpliesLocksLengthZero {graph : ModeGraph} {Binding : graph.Mode → Type} :
    ∀ {ambientMode : graph.Mode} (context : ModedContext graph Binding ambientMode),
      context.isLockFree = true → context.locksOf.length = 0
  | _, .empty _, _ => rfl
  | _, .cons restContext _binding, isLockFree =>
      lockFreeImpliesLocksLengthZero restContext isLockFree
  | _, .lockCons _restContext _lockModality, isLockFree => Bool.noConfusion isLockFree

/-- The affine-seal bridge over an ARBITRARY affine-graph mode (the ambient mode kept a variable so the
telescope index is a variable and structural recursion is inferred).  A lock-free affine context's `locks(Δ)`
is the IDENTITY 1-cell at its ambient mode.  The affine graph has a single (`Unit`) mode, so `baseModeOf` is
definitionally the ambient mode (`Unit` eta) and the equation typechecks with no transport. -/
theorem affineLockFreeImpliesLocksIdentityOverMode :
    ∀ {ambientMode : dimensionUsePositionModeGraph.Mode}
      (context : ModedContext dimensionUsePositionModeGraph (fun _ => Unit) ambientMode),
      context.isLockFree = true → context.locksOf = identityPath ambientMode
  | _, .empty _, _ => rfl
  | _, .cons restContext _binding, isLockFree =>
      affineLockFreeImpliesLocksIdentityOverMode restContext isLockFree
  | _, .lockCons _restContext _lockModality, isLockFree => Bool.noConfusion isLockFree

/-- ★ **The affine-seal bridge.**  Over the affine dimension graph a lock-free context's `locks(Δ)` is
exactly `obligationModalityToPath .fibrant` (the shipped `fibrant` identity 1-cell) — since
`obligationModalityToPath .fibrant` is definitionally `identityPath dimensionUsePositionMode`.  The affine identity
half of the mode-theoretic meaning of lock-freeness. -/
theorem affineLockFreeImpliesLocksIdentity
    (context : ModedContext dimensionUsePositionModeGraph (fun _ => Unit) dimensionUsePositionMode)
    (isLockFree : context.isLockFree = true) :
    context.locksOf = obligationModalityToPath .fibrant :=
  affineLockFreeImpliesLocksIdentityOverMode context isLockFree

/-- Converse witness: the shipped affine single-lock context is NOT lock-free (it carries a `lockCons`), so
the structural predicate genuinely detects the lock.  Its `locks(Δ)` is the length-one `dimensional` 1-cell
(`affineSingleLockContext_locks`), confirming a lock produces a non-identity total modality. -/
theorem affineSingleLockContextNotLockFree :
    affineSingleLockContext.isLockFree = false :=
  rfl

/-- Consistency with the shipped extend-context seal: the all-extend affine context IS lock-free, and
`affineLockFreeImpliesLocksIdentity` reproduces the shipped `affineExtendContext_locks` value. -/
theorem affineExtendContextIsLockFree :
    affineExtendContext.isLockFree = true :=
  rfl

end ModedContext

end FX1Poly.Core.Fib

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.Fib FX1Poly.Polygraph FX1Poly.Axis.Syntax

/-- The **lock-shape** of a kernel typing context as a mode-indexed telescope over the affine dimension graph:
forget the bindings and the dimension types, keep only the `empty` / `cons` / `lockCons` shape.  Each kernel
`lockCons` reflects to a mode-indexed `lockCons` carrying the length-one affine generator 1-cell
(`singletonModalityPath affineLockGenerator`), so the reflected total lock modality tracks the kernel's locks
exactly.  The shape functor whose lock-free predicate the kernel `Bool` reflects onto. -/
def TypingContext.toModedShape {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope →
      ModedContext dimensionUsePositionModeGraph (fun _ => Unit) dimensionUsePositionMode
  | _, .empty => ModedContext.empty dimensionUsePositionMode
  | _, .cons restContext _bindingType => (restContext.toModedShape).cons ()
  | _, .lockCons restContext _dimensionType =>
      (restContext.toModedShape).lockCons (singletonModalityPath affineLockGenerator)

/-- ★ **The reflection bridge.**  The kernel's `Bool` lock-free predicate EQUALS the mode-indexed
`ModedContext.isLockFree` on the forgotten lock-shape — the two are the SAME structural recursion.  Structural
induction, all arms `rfl`-closing (empty/lockCons directly, cons through the prefix IH). -/
theorem isLockFreeContext_eq_toModedShape_isLockFree {profile : PolyProfile} :
    ∀ {scope : Nat} (context : TypingContext profile scope),
      context.isLockFreeContext = (context.toModedShape).isLockFree
  | _, .empty => rfl
  | _, .cons restContext _bindingType => isLockFreeContext_eq_toModedShape_isLockFree restContext
  | _, .lockCons _restContext _dimensionType => rfl

/-- ★ **The mode-theoretic MEANING of the Tier E side condition.**  `context.isLockFreeContext = true` says
exactly that the total lock modality of the context's mode-shape is the IDENTITY 1-cell —
`locks(toModedShape) = obligationModalityToPath .fibrant`.  This upgrades the opaque `Bool` discharge threaded
through `ofGrownReflected` to a genuine mode-axis statement, via the reflection bridge and the affine-seal
`locks`-triviality lemma. -/
theorem TypingContext.lockFreeImpliesShapeLocksIdentity {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (isLockFree : context.isLockFreeContext = true) :
    (context.toModedShape).locksOf = obligationModalityToPath .fibrant :=
  ModedContext.affineLockFreeImpliesLocksIdentity context.toModedShape
    ((isLockFreeContext_eq_toModedShape_isLockFree context).symm.trans isLockFree)

/-- ★ **The DECIDED Tier E discharge.**  The retired-`ofGrown` capstone `HasTypeDescPi.ofGrownReflected`
re-exposed with its lock-free side condition supplied by the DECIDABLE check: `decide
(context.isLockFreeContext = true) = true`.  At any concretely lock-free context this is discharged by
computation (`by decide` / `rfl`), so the retirement side condition is a REAL computed discharge rather than a
hand-supplied assumption — and, by `lockFreeImpliesShapeLocksIdentity`, it MEANS the context's total lock
modality is the identity 1-cell.  Purely additive over the retirement brick (uses `ofGrownReflected`, does not
touch it). -/
theorem HasTypeDescPi.ofGrownReflectedDecidably {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier)
    (contextLockFreeDecides : decide (context.isLockFreeContext = true) = true) :
    HasTypeUnion profile context subject classifier :=
  derivation.ofGrownReflected (of_decide_eq_true contextLockFreeDecides)

end FX1Poly.Typed
