import FX1Poly.Typed.HasTypeDescPiEtaCoherence
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiWeakening

/-! # FX1Poly/Typed/HasTypeDescPiEtaExpansionGrown
    — forward η-expansion preserves typing for ARBITRARY GROWN functions (generalizes the
      formation-only η-coherence)

`HasTypeDescPi.etaCoherence_formationFunction` (`HasTypeDescPiEtaCoherence.lean`) ships the η counterpart
to β-coherence, but ONLY for functions whose `f : Π D C` typing lives in the FORMATION engine
(`HasTypeDesc`).  The formation engine types neither `λ` (grown `piIntro`) nor application (grown
`piElim`), so that version effectively covers only `f` = a VARIABLE of function type.

This file removes that restriction: the function `f` may be ANY grown-typed term — a `λ`-abstraction, an
application, a Church numeral, the polymorphic identity — and the η-redex `etaLamSource f = λ. (weaken f
@ var 0)` still types at the SAME `Π D C` as `f`.  This is the genuine forward half of GROWN η subject
reduction (the η direction of #477), applicable to the real functions the kernel builds.

  * **`HasTypeDescPi.etaExpansionPreservesTypingGrown` (★)** — given the grown context is well-formed
    (`WfContextDescPi`, the standard validity premise) and `f : piTyCodeCell D C` in the grown engine,
    `etaLamSource f : piTyCodeCell D C` in the grown engine.  Forward construction (no inversion of the
    function, no grown strengthening): validity (`classifierIsTypeDescPi`) + `invertPiTyCode` extract the
    grown typings of `D` and `C`; `weakenUnderBinding` (the GROWN weakening, not just formation) +
    `rename_piTyCodeCell` weaken `f` under the binder; `var 0` types at `weaken D`; the application's
    result classifier collapses to `C` by the shipped η identity `subst0_iterateLiftWeaken_newestVar`;
    `piIntro` reassembles.  The ONLY change from the formation version is grown components throughout —
    the de Bruijn substrate (η identity, `rename_piTyCodeCell`, the `var`/`piElim`/`piIntro` shapes) is
    identical, exhibiting that the formation η-coherence template is engine-agnostic.
  * `HasTypeDescPi.etaCoherenceGrown` — the η-coherence PAIR (the grown mirror of
    `etaCoherence_formationFunction`): BOTH the η-redex `etaLamSource f` and its η-reduct `f` type at the
    same `Π D C`.  The reduct half is `f` itself.

## Honest scope boundary

This is the FORWARD direction (η-EXPANSION preserves typing), the half that needs no strengthening.  The
fully-general INVERTED η subject reduction (an arbitrary grown derivation η-CONTRACTING `etaLamSource f ↝
f`, possibly under `conv`) additionally needs grown-engine STRENGTHENING (the inverse of
`weakenUnderBinding`), which does not yet exist — that is the remaining residual of #477's λ case.  The
forward direction here is exactly what the η-long readback / NbE quote tasks (#360–363) consume.

## Zero-axiom verification

The proof threads only shipped zero-axiom pieces: `classifierIsTypeDescPi`, `invertPiTyCode`,
`weakenUnderBinding`, `rename_piTyCodeCell` (defeq), `HasTypeDesc.var`,
`RawTerm.subst0_iterateLiftWeaken_newestVar`, `HasTypeDescPi.piIntro`/`piElim`/`ofFormation`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- ★ **Forward η-expansion preserves typing for an arbitrary grown function.**  Given a well-formed
grown context and `f : piTyCodeCell D C` in the grown engine, the η-redex `etaLamSource f = λ. (weaken f
@ var 0)` types at the SAME `piTyCodeCell D C`.  Generalizes `etaCoherence_formationFunction` from
formation-typed `f` (effectively only variables of function type) to ANY grown-typed `f` — `λ`-terms,
applications, Church numerals.  Forward construction: validity + `invertPiTyCode` give the grown domain
and codomain typings; `weakenUnderBinding` (grown) + `rename_piTyCodeCell` weaken `f` under the binder;
`var 0` types at `weaken D`; the application result classifier collapses to `C` by the η identity;
`piIntro` reassembles. -/
theorem HasTypeDescPi.etaExpansionPreservesTypingGrown {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (wellFormed : WfContextDescPi context)
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeDescPi profile context (RawTerm.etaLamSource domainCode functionTerm)
      (piTyCodeCell domainCode codomainCode) := by
  obtain ⟨_classLevel, _classFlag, piTyped⟩ := functionTyped.classifierIsTypeDescPi wellFormed
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped, _convCode⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  have functionWeakened :
      HasTypeDescPi profile (context.cons domainCode)
        (RawTerm.rename RawRenaming.weaken functionTerm)
        (piTyCodeCell (RawTerm.rename RawRenaming.weaken domainCode)
          (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomainCode)) := by
    have hWeak := HasTypeDescPi.weakenUnderBinding domainCode functionTyped
    rw [rename_piTyCodeCell] at hWeak
    exact hWeak
  have newestVarTyped :
      HasTypeDescPi profile (context.cons domainCode) RawTerm.newestVar
        (RawTerm.rename RawRenaming.weaken domainCode) :=
    HasTypeDescPi.ofFormation
      (HasTypeDesc.var (context.cons domainCode) ⟨0, Nat.zero_lt_succ scope⟩)
  have bodyTyped :
      HasTypeDescPi profile (context.cons domainCode)
        (appCell (RawTerm.rename RawRenaming.weaken functionTerm) RawTerm.newestVar)
        codomainCode := by
    have hElim := HasTypeDescPi.piElim functionWeakened newestVarTyped
    rw [RawTerm.subst0_iterateLiftWeaken_newestVar] at hElim
    exact hElim
  exact HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped

/-- **η-coherence for grown functions** (the grown mirror of `etaCoherence_formationFunction`).  BOTH the
η-redex `etaLamSource f` and its η-reduct `f` type in the grown engine at the same `piTyCodeCell D C` —
the redex half is `etaExpansionPreservesTypingGrown`, the reduct half is `f` itself. -/
theorem HasTypeDescPi.etaCoherenceGrown {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (wellFormed : WfContextDescPi context)
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeDescPi profile context (RawTerm.etaLamSource domainCode functionTerm)
        (piTyCodeCell domainCode codomainCode)
      ∧ HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) :=
  ⟨HasTypeDescPi.etaExpansionPreservesTypingGrown wellFormed functionTyped, functionTyped⟩

end FX1Poly.Typed
