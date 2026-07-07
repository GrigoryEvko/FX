import FX1Poly.Typed.Fib.ContextDisplayPi

/-! # FX1Poly/Typed/Fib/FibredDisplayPiAdjunction — the honest WEAK bundle of the shipped `weaken ⊣ Π`
(the correct bounded stand-in for a non-existent `ContextLock` promotion of `fxWeakeningLock`)

## Why this is NOT a `ContextLock`

`Tier0/Context/ModalLock.lean` ships `fxWeakeningLock K : RawEndofunctor fxBaseSubstCategory` (`A ↦ A + K`) as
a lock CARRIER ONLY, by explicit design (its docstring, `:959-964`): `(− + K)` has NO endo-right-adjoint in
the bare context category, so it is deliberately NOT bundled into a `ContextLock`.  A `ContextLock` demands an
`IsEndoAdjunction lock dra` — a STRICT, on-the-nose natural bijection of the BASE category's morphisms
(`fxBaseSubstCategory.Morphism = SubstVec`).

The shipped `weaken ⊣ Π` (`ContextDisplayPi.lean`) is a DIFFERENT object on four independent counts:

  * it bijects TYPED TERM hom-sets `HasTypeUnion` in the display fibration over `Core/`, not `SubstVec`;
  * its right adjoint `Π_A` is fibrewise (a functor between slices), NOT an endofunctor of the base;
  * its round-trips hold only WEAKLY, up to `Conv` / `StepOver fxBundle` (the same `funext` ceiling as fib-5),
    where `IsEndoAdjunction` needs definitional round-trips;
  * it is one dependent display map (`Γ.A`), not the base coproduct `+K`.

So "promote `fxWeakeningLock` to a `ContextLock` via `weaken ⊣ Π`" would FABRICATE an adjoint the kernel does
not have (a strict base-`SubstVec` endo-adjunction where only a weak fibrational one exists).  The genuine
base-level DRA of weakening is the multiplier/transpension adjoint string whose triangle-saturation is
DEFERRED (`fxMode_hasAdjunctionTriangleSaturation = false`) — deep research, NOT bounded.

## What this file DOES ship (fully bounded)

The honest, precise structure the shipped `weaken ⊣ Π` really inhabits: a `Prop`-bundle
`FibredDisplayPiAdjunction context domainCode` collecting exactly the four shipped ContextDisplayPi theorems —
the forward transpose (currying, `lam`), the backward co-transpose (uncurrying, `app` to the fresh variable),
and the two triangle identities (β up-to-`Conv`, η in `StepOver fxBundle`) — over a lock-free context.  It is
the WEAK, fibrational, term-level analogue of `ContextLock`, and it explicitly does NOT fill the
`ContextAxis.lockOn` DRA slot.  Its witness `fibredDisplayPiAdjunctionWitness` inhabits every field from the
shipped theorems, so the bundle is exercised (constructed, not declared).

## Zero-axiom

Field-by-field application of the four shipped ContextDisplayPi theorems.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Fib/FibredDisplayPiAdjunction.lean`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Tier0.Syntax FX1Poly.Typed FX1Poly.Universe

/-- ★ **The honest WEAK fibred-Π adjunction bundle.**  Over a lock-free context `Γ` and a display domain
`A = domainCode`, the four shipped facts that make the kernel's `lam`/`app` the fibred-Π right adjoint to
display-map reindexing `Tm(Γ.A, B) ≅ Tm(Γ, Π_A B)`:

  * `forwardTranspose` — currying: `lam A body : Π_A B` over `Γ` (`lamRealizesFibredPiTranspose`);
  * `backwardCotranspose` — uncurrying: `app (weaken f) (var 0) : B` over `Γ.A`
    (`appRealizesFibredPiCotranspose`);
  * `betaTriangle` — backward ∘ forward = id up to `Conv` (`fibredPiBetaTriangle`);
  * `etaTriangle` — forward ∘ backward = id in `StepOver fxBundle` (`fibredPiEtaTriangle`).

This is the WEAK, up-to-`Conv` analogue of `Tier0/Context/ModalLock.ContextLock`; it does NOT provide an
`IsEndoAdjunction` over `fxBaseSubstCategory` and hence does NOT promote `fxWeakeningLock` to a `ContextLock`
(see the file header). -/
structure FibredDisplayPiAdjunction {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (domainCode : RawTerm scope) : Prop where
  /-- The ordinary (non-modal) fibred Π rides a lock-free context (the A1-CONJUNCT-WIRE side condition). -/
  isLockFree : context.isLockFreeContext = true
  /-- FORWARD transpose (currying): `lam A body` is typed `Π_A B` over `Γ`. -/
  forwardTranspose : ∀ (codomainCode body : RawTerm (scope + 1)) (level0 level1 : LevelExpr)
      (flag : UniverseFlag),
    HasTypeUnion profile context domainCode (universeCodeCell level0 flag) →
    HasTypeUnion profile (context.cons domainCode) codomainCode (universeCodeCell level1 flag) →
    HasTypeUnion profile (context.cons domainCode) body codomainCode →
    HasTypeUnion profile context (lamCell domainCode body) (piTyCodeCell domainCode codomainCode)
  /-- BACKWARD co-transpose (uncurrying): `app (weaken f) (var 0)` is typed `B` over `Γ.A`. -/
  backwardCotranspose : ∀ (codomainCode : RawTerm (scope + 1)) (functionTerm : RawTerm scope),
    HasTypeUnion profile context functionTerm (piTyCodeCell domainCode codomainCode) →
    HasTypeUnion profile (context.cons domainCode)
      (appCell (RawTerm.rename RawRenaming.weaken functionTerm) RawTerm.newestVar) codomainCode
  /-- β-triangle (backward ∘ forward = id up to `Conv`). -/
  betaTriangle : ∀ (body : RawTerm (scope + 1)),
    Conv (appCell (RawTerm.weaken (lamCell domainCode body)) RawTerm.newestVar) body
  /-- η-triangle (forward ∘ backward = id in the unified `StepOver fxBundle` relation). -/
  etaTriangle : ∀ (functionTerm : RawTerm scope),
    StepOver fxBundle
      (lamCell domainCode (appCell (RawTerm.weaken functionTerm) RawTerm.newestVar)) functionTerm

/-- ★ **The bundle is inhabited by the shipped `weaken ⊣ Π`.**  Every field is discharged by the corresponding
ContextDisplayPi theorem, so the weak fibred-Π adjunction is exercised (constructed) over any lock-free context
and display domain.  This is the honest bounded deliverable that stands in for the impossible `ContextLock`
promotion of `fxWeakeningLock`. -/
theorem fibredDisplayPiAdjunctionWitness {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (domainCode : RawTerm scope)
    (isLockFree : context.isLockFreeContext = true) :
    FibredDisplayPiAdjunction context domainCode where
  isLockFree := isLockFree
  forwardTranspose := fun codomainCode body level0 level1 flag domainTyped codomainTyped bodyTyped =>
    lamRealizesFibredPiTranspose context domainCode codomainCode body level0 level1 flag
      domainTyped codomainTyped bodyTyped isLockFree
  backwardCotranspose := fun codomainCode functionTerm functionTyped =>
    appRealizesFibredPiCotranspose context domainCode codomainCode functionTerm functionTyped isLockFree
  betaTriangle := fun body => fibredPiBetaTriangle domainCode body
  etaTriangle := fun functionTerm => fibredPiEtaTriangle domainCode functionTerm

end FX1Poly.Core.Fib
