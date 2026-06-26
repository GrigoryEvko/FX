import FX1Poly.Core.Fib.ContextComprehension
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Dimensions.Graded.GradedIntroPremiseSpike

/-! # FX1Poly/Core/Fib/ContextDisplayPi — fib-1d (i): the kernel's `lam` IS the fibred-Π right adjoint's forward transpose

`context-16` ships the CARTESIAN skeleton of local cartesian closure (finite products = context concatenation,
`fxContextCartesianClosed`) but HONESTLY DEFERS the locally-CLOSED half — the fibred-Π RIGHT ADJOINT to
reindexing along a display map (`democracyLCC_hasLocalExponentials := false`,
`fxComprehensionCategory_hasFibredPiRightAdjoint := false`) — as the `×type` core, "deferred to fib-1".  That
deferred right adjoint is NOT missing from the kernel: the kernel's Π-former (`piTyCodeCell` + `lam`/`app` with
β/η) IS it.  fib-1d performs the genuine `Core → Tier0/Context` REWIRE that realizes the deferred core: it
exhibits the kernel's typed Π-introduction as the fibred-Π right adjoint's CURRYING transpose over the
comprehension `Γ.A` that fib-1c identified with `TypingContext.cons`.

## The adjunction (what this file's increment delivers)

The fibred-Π right adjoint to context-extension reindexing is the currying bijection at the term level

  `Tm(Γ.A, B)  ≅  Tm(Γ, Π_A B)`        (the right adjoint `Π_A ⊣` weakening, fibrewise)

whose FORWARD transpose (the right-adjoint unit / λ-abstraction) sends a term `body` typed `B` over the
comprehension `Γ.A` to `lam A body` typed `Π_A B = piTyCodeCell A B` over `Γ`.  This increment (fib-1d (i))
discharges exactly that forward transpose over the SHIPPED kernel judgment `HasTypeUnion`, via the native
`gen_lam` intro arm — so the kernel's Π-introduction REALIZES the right adjoint's universal map.  The backward
co-transpose (`app` to the fresh variable) and the β/η triangle identities are the fib-1d (ii)/(iii)
increments; the on-the-nose strictness of the bijection meets the same `funext` ceiling as fib-5 (so the
realized adjunction is the WEAK, up-to-`Conv` one).

The source context `Γ.A` is `context.cons domainCode`, whose `comprehensionObject` is `scope + 1` (fib-1c) and
whose substitutions decompose by `fxComprehensionCategory.representability = SubstVec.comprehensionIso` — so the
transpose genuinely lands over the context axis's comprehension, making Core depend on the (now non-deferred)
fibred-Π core.

## Zero-axiom

The native `HasTypeUnion.intro` at `gen_lam lamIntroRule`, its `gradedBinderChecks omega` side condition
discharged by `(gradedBinderChecks_spectrum body).1` (unconstrained at `omega`), and the three formation/body
obligations supplied by `List.Mem` head/tail decomposition (no `mem_cons` iff, propext-free).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Typed FX1Poly.Universe

/-- **★ fib-1d (i): `lam` realizes the fibred-Π right adjoint's forward transpose (currying).**  Given the
display fibre's domain `A : Type@level0` over `Γ`, a codomain `B : Type@level1` over the comprehension `Γ.A`
(`context.cons domainCode`), and a `body : B` over `Γ.A`, the kernel's `lam A body` is typed at `Π_A B =
piTyCodeCell A B` over `Γ` by the native `gen_lam` introducer.  This is the right-adjoint UNIT / the currying
map `Tm(Γ.A, B) → Tm(Γ, Π_A B)` — the kernel's Π-introduction IS the deferred fibred-Π right adjoint's
universal transpose, over the comprehension fib-1c pinned. -/
theorem lamRealizesFibredPiTranspose {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode body : RawTerm (scope + 1))
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (domainTyped : HasTypeUnion profile context domainCode (universeCodeCell level0 flag))
    (codomainTyped : HasTypeUnion profile (context.cons domainCode) codomainCode
      (universeCodeCell level1 flag))
    (bodyTyped : HasTypeUnion profile (context.cons domainCode) body codomainCode) :
    HasTypeUnion profile context (lamCell domainCode body) (piTyCodeCell domainCode codomainCode) := by
  refine HasTypeUnion.intro context .gen_lam lamIntroRule
    (.childCons domainCode (.childCons body .childNil))
    (.childCons codomainCode .childNil)
    level0 level1 flag rfl (gradedBinderChecks_spectrum body).1 ?_
  intro obligation hmem
  cases hmem with
  | head => exact domainTyped
  | tail _ hmem => cases hmem with
    | head => exact codomainTyped
    | tail _ hmem => cases hmem with
      | head => exact bodyTyped
      | tail _ hmem => cases hmem

/-- The forward transpose lands over the context axis's comprehension: its source context `Γ.A =
context.cons domainCode` realizes the comprehension object `scope + 1` (fib-1c) AND its substitutions decompose
by the context axis's representability `= SubstVec.comprehensionIso` — so `lamRealizesFibredPiTranspose` curries
a term over the genuine comprehension `Γ.A` down to `Γ`, the fibred-Π right adjoint over the (previously
deferred) context-axis local-closure core. -/
theorem fibredPiTranspose_overComprehension {profile : PolyProfile} {scope target : Nat}
    (context : TypingContext profile scope) (domainCode : RawTerm scope) :
    (context.cons domainCode).comprehensionObject = scope + 1
    ∧ fxComprehensionCategory.representability (target := target) (source := scope)
        = SubstVec.comprehensionIso :=
  ⟨rfl, rfl⟩

end FX1Poly.Core.Fib
