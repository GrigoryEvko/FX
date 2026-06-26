import FX1Poly.Core.Fib.ContextComprehension
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Engine.HasTypeDescPi.Eta.HasTypeDescPiEtaCoherence
import FX1Poly.Typed.Dimensions.Graded.GradedIntroPremiseSpike
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepOverBundle
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStep

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

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Tier0.Syntax FX1Poly.Typed FX1Poly.Universe

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

/-- **★ fib-1d (ii): `app` to the fresh variable realizes the fibred-Π right adjoint's backward co-transpose
(uncurrying).**  Given `f : Π_A B = piTyCodeCell A B` over `Γ`, the kernel weakens it into the comprehension
`Γ.A = context.cons A` and applies it to the fresh variable: `app (weaken f) (var 0) : B` over `Γ.A`.  This is
the right-adjoint CO-UNIT / the uncurrying map `Tm(Γ, Π_A B) → Tm(Γ.A, B)` — the de Bruijn inner term of the
η-redex `etaLamSource f`, typed over the SHIPPED kernel judgment by `HasTypeUnion.weakenUnderBinding` (weaken
`f` into `Γ.A`) + the native `gen_app` eliminator applied to `HasTypeUnion.var` (the comprehension's fresh
variable), with the dependent output type `subst0 (weakenUnder B) (var 0)` collapsing to `B` through the de
Bruijn η identity `subst0_iterateLiftWeaken_newestVar`.  Together with `lamRealizesFibredPiTranspose` (the
forward currying), this exhibits BOTH directions of the fibred-Π adjunction `Tm(Γ.A, B) ≅ Tm(Γ, Π_A B)` over
the SHIPPED kernel — the previously-deferred fibred-Π right adjoint, realized.  (The β/η triangle identities
that make the pair a genuine bijection up to `Conv` are the fib-1d (iii) increment; on-the-nose strictness meets
the fib-5 `funext` ceiling.) -/
theorem appRealizesFibredPiCotranspose {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (functionTerm : RawTerm scope)
    (functionTyped :
      HasTypeUnion profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeUnion profile (context.cons domainCode)
      (appCell (RawTerm.rename RawRenaming.weaken functionTerm) RawTerm.newestVar)
      codomainCode := by
  have functionWeakened :
      HasTypeUnion profile (context.cons domainCode)
        (RawTerm.rename RawRenaming.weaken functionTerm)
        (piTyCodeCell (RawTerm.rename RawRenaming.weaken domainCode)
          (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomainCode)) := by
    have hWeak := functionTyped.weakenUnderBinding domainCode
    rw [rename_piTyCodeCell] at hWeak
    exact hWeak
  have newestVarTyped :
      HasTypeUnion profile (context.cons domainCode) RawTerm.newestVar
        (RawTerm.rename RawRenaming.weaken domainCode) := by
    have hVar := HasTypeUnion.var (context.cons domainCode) ⟨0, Nat.zero_lt_succ scope⟩
    rw [TypingContext.lookup_cons_zero] at hVar
    exact hVar
  have appTyped :
      HasTypeUnion profile (context.cons domainCode)
        (appCell (RawTerm.rename RawRenaming.weaken functionTerm) RawTerm.newestVar)
        (RawTerm.subst0 (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomainCode)
          RawTerm.newestVar) := by
    refine HasTypeUnion.elim (context.cons domainCode) .gen_app appElimRule
      (.childCons (RawTerm.rename RawRenaming.weaken functionTerm)
        (.childCons RawTerm.newestVar .childNil))
      (.childCons (RawTerm.rename RawRenaming.weaken domainCode)
        (.childCons (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomainCode) .childNil))
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl ?_
    intro obligation hmem
    cases hmem with
    | head => exact functionWeakened
    | tail _ hmem => cases hmem with
      | head => exact newestVarTyped
      | tail _ hmem => cases hmem
  rw [RawTerm.subst0_iterateLiftWeaken_newestVar] at appTyped
  exact appTyped

/-- **★ fib-1d (iii), β-triangle: backward ∘ forward = id (up to `Conv`).**  Currying a `body` then
uncurrying — `app (weaken (lam A body)) (var 0)` — converts back to `body`.  This is the right-adjoint
adjunction's β-triangle: one function-β contraction (`HeadStep.beta`: `app (lam A body') arg ↝ subst0 body'
arg`, here with `body' = weakenUnder body`, `arg = var 0`) whose contractum `subst0 (weakenUnder body) (var 0)`
collapses to `body` by the de Bruijn η identity.  The `weaken` of `lam` is `lam` of `weaken` definitionally
(`lamCell` shares `piTyCodeCell`'s `[0,1]` child shape).  Realizes the round-trip
`appRealizesFibredPiCotranspose ∘ lamRealizesFibredPiTranspose = id` at the TERM level, up to raw conversion. -/
theorem fibredPiBetaTriangle {scope : Nat}
    (domainCode : RawTerm scope) (body : RawTerm (scope + 1)) :
    Conv (appCell (RawTerm.weaken (lamCell domainCode body)) RawTerm.newestVar) body := by
  have betaStep :
      Step (appCell (RawTerm.weaken (lamCell domainCode body)) RawTerm.newestVar)
        (RawTerm.subst0 (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) body)
          RawTerm.newestVar) :=
    HeadStep.beta.toStep
  rw [RawTerm.subst0_iterateLiftWeaken_newestVar] at betaStep
  exact Conv.fromStep betaStep

/-- **★ fib-1d (iii), η-triangle: forward ∘ backward = id (the shipped function-η).**  Uncurrying an `f` then
currying — `lam A (app (weaken f) (var 0))` — reduces back to `f` by the kernel's shipped FUNCTION-η rule in the
unified βιη relation `StepOver fxBundle` (`StepOver.fxBundleEtaLamFires`, the `etaRedex` arm; the source IS
`RawTerm.etaLamSource A f = lam A (app (weaken f) (var 0))` definitionally).  This is the right-adjoint
adjunction's η-triangle: the round-trip `lamRealizesFibredPiTranspose ∘ appRealizesFibredPiCotranspose = id` at
the TERM level.  Stated in `StepOver fxBundle` because the kernel's η lives in the unified table relation (not
the bespoke `Step`/`Conv`, which is β+ι only) — the genuine shipped η that makes Π a right adjoint. -/
theorem fibredPiEtaTriangle {scope : Nat}
    (domainCode functionTerm : RawTerm scope) :
    StepOver fxBundle
      (lamCell domainCode (appCell (RawTerm.weaken functionTerm) RawTerm.newestVar))
      functionTerm :=
  StepOver.fxBundleEtaLamFires domainCode functionTerm

end FX1Poly.Core.Fib
