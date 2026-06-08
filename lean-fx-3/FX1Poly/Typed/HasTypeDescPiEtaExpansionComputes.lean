import FX1Poly.Core.StepEta
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Typed.TypedChurchNumeralComputeGeneral
import FX1Poly.Typed.TypedChurchNumeralTyping
import FX1Poly.Typed.HasTypeDescPiEtaExpansionGrown

/-! # FX1Poly/Typed/HasTypeDescPiEtaExpansionComputes
    — the OPERATIONAL content of η on top of forward η-expansion typing (#1033)

`HasTypeDescPi.etaExpansionPreservesTypingGrown` (`HasTypeDescPiEtaExpansionGrown.lean`) showed the forward η
direction is TYPE-preserving: for any grown `f : Π D C`, the η-redex `etaLamSource f = λ. (weaken f @ var 0)`
types at the same `Π D C`.  That is the static half.  This file adds the DYNAMIC half — what η-expansion does
to a function when you actually APPLY it — and joins the two into a coherence statement, then exhibits both on
the kernel's flagship grown functions (the Church numerals).

  * **`Step.etaLamSourceApplication` (★, the operational core)** — for ANY scope and ANY `f`, `a`:

        (etaLamSource f) a  ↝β  f a

    Applying an η-expansion β-steps in ONE step to applying the original.  This is the operational justification
    of η: an η-expansion is interchangeable with the original under application, modulo a single administrative
    β-step.  No typing is consulted — it is the raw `Step.beta` whose contractum reshapes via the de Bruijn
    cancellations `subst0 (weaken f) a = f` (`weaken_subst_singleton`) and `subst0 (var 0) a = a` (`rfl`),
    packaged as `subst0_etaLamSource_body`.  General over scope, so it lifts under binders and inside spines.

  * **`HasTypeDescPi.etaExpansionTypedAndOperational`** — the η-coherence bundle: for any grown `f : Π D C`
    over a well-formed context, the η-redex `etaLamSource f` BOTH types at the same `Π D C` (the static half,
    `etaExpansionPreservesTypingGrown`) AND, applied to any argument, β-steps to `f` applied to that argument
    (the dynamic half, `Step.etaLamSourceApplication`).  η-expansion is invisible to the typed equational theory
    in both senses at once — types preserved, behaviour preserved.

  * **`etaExpandedChurchNumeral_hasTypeDescPi`** — non-vacuity (static): the η-expansion of `churchNumeralLambda
    n` types at the SAME Church Nat type `Π(A:Type@0). Π(f:A→A). Π(x:A). A` (via `etaExpansionPreservesTypingGrown
    ∘ churchNumeralLambda_hasTypeDescPi`).  This exercises the forward η rule on a genuine grown λ-term — a Church
    numeral, not the bare variable-of-function-type that the formation-only η-coherence (`etaCoherence_formation
    Function`) covered.

  * **`etaExpandedChurchNumeral_appliedReducesToIterate` (★)** — non-vacuity (dynamic): the η-expanded numeral
    still COMPUTES correctly.  Applied to `(typeA, handlerF, baseX)` it reduces to `iteratedApplication n
    handlerF baseX = f^n x` — exactly the iterate the bare numeral computes (`churchNumeral_appliedReducesTo
    Iterate_general`, #1009), the only difference being the one leading administrative β-step that
    `Step.etaLamSourceApplication` contributes, lifted through the two outer application layers.  η-expansion
    preserves the term model's arithmetic, not just its typing.

Together the two witnesses make the coherence bundle concrete on a real function family: η-expanding a Church
numeral changes neither its type nor its computed value.

## Zero-axiom verification

`Step.etaLamSourceApplication` is `rw [← subst0_etaLamSource_body]; exact Step.beta`; `subst0_etaLamSource_body`
is `unfold`/`show` + `weaken_subst_singleton` + the innermost-`var` `rfl`.  The Church witnesses thread the
shipped `etaExpansionPreservesTypingGrown` / `churchNumeralLambda_hasTypeDescPi` / `churchNumeral_appliedReduces
ToIterate_general` and the function-position congruence idiom (`Step.cong .gen_app () + StepChildren.here`,
scopes pinned).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The η-redex body's β-contractum collapses to the application: `subst0 ((weaken f) @ var 0) a = f @ a`.  The
two de Bruijn cancellations — `subst0 (weaken f) a = f` (`weaken_subst_singleton`, the lifted singleton fixes
the weakened term) and `subst0 (var 0) a = a` (innermost-variable rule, `rfl`) — fire under the definitional
push of `subst0` through the application cell. -/
theorem subst0_etaLamSource_body {scope : Nat} (innerFunction argument : RawTerm scope) :
    RawTerm.subst0 (appCell (RawTerm.weaken innerFunction) RawTerm.newestVar) argument
      = appCell innerFunction argument := by
  unfold RawTerm.subst0
  show appCell (RawTerm.subst (RawTermSubst.singleton argument) (RawTerm.weaken innerFunction))
       (RawTerm.subst (RawTermSubst.singleton argument) RawTerm.newestVar) = appCell innerFunction argument
  rw [RawTerm.weaken_subst_singleton innerFunction argument,
      show RawTerm.subst (RawTermSubst.singleton argument) RawTerm.newestVar = argument from rfl]

/-- ★ **The operational core of η.**  Applying an η-expansion β-steps in one step to applying the original:
`(etaLamSource f) a ↝β f a`.  `etaLamSource f = λ. (weaken f @ var 0)`, so the application is a β-redex whose
contractum reshapes to `f @ a` by `subst0_etaLamSource_body`.  Purely raw (no typing) and general over scope, so
it lifts under binders / inside application spines; it is the operational justification that an η-expansion is
interchangeable with the original under application. -/
theorem Step.etaLamSourceApplication {scope : Nat} (innerFunction argument : RawTerm scope) :
    Step (appCell (RawTerm.etaLamSource innerFunction) argument) (appCell innerFunction argument) := by
  rw [← subst0_etaLamSource_body innerFunction argument]
  exact Step.beta

/-- **η-coherence bundle (typed + operational).**  For any grown `f : Π D C` over a well-formed context, the
η-redex `etaLamSource f` BOTH types at the same `Π D C` (static, `etaExpansionPreservesTypingGrown`) AND, applied
to any argument, β-steps to `f` applied to that argument (dynamic, `Step.etaLamSourceApplication`).  η-expansion
preserves both the type and the application behaviour of every grown function. -/
theorem HasTypeDescPi.etaExpansionTypedAndOperational {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (wellFormed : WfContextDescPi context)
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeDescPi profile context (RawTerm.etaLamSource functionTerm) (piTyCodeCell domainCode codomainCode)
      ∧ ∀ argument : RawTerm scope,
          Step (appCell (RawTerm.etaLamSource functionTerm) argument) (appCell functionTerm argument) :=
  ⟨HasTypeDescPi.etaExpansionPreservesTypingGrown wellFormed functionTyped,
   fun argument => Step.etaLamSourceApplication functionTerm argument⟩

/-- **η-expansion preserves typing on a Church numeral** (non-vacuity, static).  The η-expansion of
`churchNumeralLambda n` types at the SAME Church Nat type — the forward η rule applied to a genuine grown λ-term
(not the bare variable-of-function-type the formation-only η-coherence covered). -/
theorem etaExpandedChurchNumeral_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) (depth : Nat) :
    HasTypeDescPi profile TypingContext.empty
      (RawTerm.etaLamSource (churchNumeralLambda depth))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) :=
  HasTypeDescPi.etaExpansionPreservesTypingGrown
    WfContextDescPi.emptyIsWellFormed
    (churchNumeralLambda_hasTypeDescPi flag depth)

/-- ★ **η-expansion preserves computation on a Church numeral** (non-vacuity, dynamic).  The η-expanded numeral
applied to `(typeA, handlerF, baseX)` still reduces to `iteratedApplication n handlerF baseX = f^n x` — the same
iterate the bare numeral computes, modulo the one leading administrative β-step that `Step.etaLamSourceApplication`
contributes (lifted through the two outer application layers via the function-position congruence idiom), after
which `churchNumeral_appliedReducesToIterate_general` finishes.  η-expansion preserves the term model's
arithmetic. -/
theorem etaExpandedChurchNumeral_appliedReducesToIterate (depth : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (RawTerm.etaLamSource (churchNumeralLambda depth)) typeA) handlerF) baseX)
      (iteratedApplication depth handlerF baseX) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons baseX .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons handlerF .childNil)
            (Step.etaLamSourceApplication (churchNumeralLambda depth) typeA)))))
    (churchNumeral_appliedReducesToIterate_general depth typeA handlerF baseX)

end FX1Poly.Typed
