import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB3aPiSigmaBeta — CONVTRANS-B.3a Π/Σ β-rule lifts

Strict gate plus reviewer-facing audit for the **Π/Σ β-rule lift**
family of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.3a, ticket #1729).  First B.3.* β-rule sub-ticket
after the B.2.* cong family closed at B.2g (#1728).

## Scope of B.3a

Three `RawStep.par.lift_full_*` β-rule lift theorems carrying both
the cong arm AND the deep-β arm (where the eliminand develops via
`RawStep.par` *to* the matching canonical introducer).  Each uses
the two-Ty existential pattern documented in
`Term/PreservesTerm/BetaCastWallDemolition.lean`:

```
∃ (targetTy : Ty level scope) (targetTerm : Term context targetTy
    targetRaw),
  Step.par sourceTerm targetTerm
```

absorbing the cast wall between the cong-arm target Ty and the
β-arm target Ty (the latter arises from `Term.subst0` for `app`,
projection-from-pair for `fst`/`snd`).

| Lift | Host file | β-arm |
| --- | --- | --- |
| `lift_full_app` | `BetaCastWallDemolition.lean` | `betaAppDeep` (Term.lam destructor) |
| `lift_full_fst` | `HeterogeneousElim.lean` | `betaFstPairDeep` (Term.pair destructor) |
| `lift_full_snd` | `HeterogeneousElim.lean` | `betaSndPairDeep` (Term.pair destructor) |

These three lifts cover the typed β-rules `betaApp` /
`betaAppDeep`, `betaFstPair` / `betaFstPairDeep`, `betaSndPair` /
`betaSndPairDeep`.  (The shallow `beta<X>` rules are
specializations of the deep `beta<X>Deep` rules via
`RawStep.par.lam`/`pair` cong wrappers — the deep destructor
proof absorbs both.)

## What this audit does NOT include — the `lift_full_appPi` gap

`lift_full_appPi` (the dependent Π β-rule lift mirroring
`lift_full_app` for `Term.app`) is NOT shipped under B.3a.  The
blocker is **structural at the kernel level**: when an `appPi`
node's function position `functionTerm : Term context
(Ty.piTy domainType codomainType) functionRaw` raw-reduces to
`(RawTerm.lam bodyTargetRaw)` (the β-deep arm of
`RawStep.par.app_inv`), the function IH produces a typed canonical

```
functionCanonical : Term context (Ty.piTy domainType codomainType)
                                 (RawTerm.lam bodyTargetRaw)
```

This canonical is ambiguous between TWO typed Term constructors:

1. **`Term.lamPi body`** — the standard dependent lambda at
   `Ty.piTy domainType codomainType` with `bodyRaw = body's raw`.
2. **`Term.funextRefl domain' codomain' applyRaw'`** — the
   canonical funext reflexivity witness at type
   `funextReflType domain' codomain' applyRaw' = Ty.piTy domain'
   (Ty.id codomain'.weaken applyRaw' applyRaw')`, which IS a
   `Ty.piTy ...` propositionally, and whose raw is
   `RawTerm.lam (RawTerm.refl applyRaw')`.

When the (`Ty.piTy`-typed) function reduces to a `funextRefl`
canonical, the typed β rule `Step.par.betaAppPiDeep`
(`Reduction/ParRed/ParInductive.lean:1304`) does NOT fire — its
signature explicitly demands

```
Step.par functionTermSource (Term.lamPi (domainType := domainType)
                                        bodyTarget)
```

so the `funextRefl`-shaped target falls outside its coverage.
There is no `Step.par.betaAppPiFunextRefl` kernel rule.  Sketch
of the failing attempt:

```lean
-- in lift_full_appPi β-deep arm:
obtain ⟨functionCanonical, functionStepTyped⟩ := functionLift functionToLam
-- functionCanonical : Term ctx (Ty.piTy A B) (RawTerm.lam bodyTargetRaw)
-- needs a destructor returning
--   Sum (∃ body, fc = Term.lamPi body)
--       (∃ ... applyRaw, fc = Term.funextRefl ...)
-- For the Term.lamPi arm: Step.par.betaAppPiDeep fires cleanly.
-- For the Term.funextRefl arm: NO typed β rule produces a Step.par
--   (Term.appPi (Term.funextRefl ...) argument) targetTerm.
sorry
```

## Coupling to Goal #1 typed-eta redesign

This blocker is documented in
`feedback_d255_eta_typed_kernel_correction_2026_05_16.md`
(memory) as "the constant-Pi-path case" for cubical β rules.  The
correct kernel design adds a typed `Step.par.piEta` rule that
bridges `Term.funextRefl` with `Term.lamPi (Term.refl _.weaken)`
via η-equivalence, enabling the funextRefl-shaped canonical to
collapse to a `Term.lamPi`-shaped one through the typed
parallel-reduction relation.  With `piEta` in the kernel:

1. funextRefl-shaped canonical → η-reduces to `Term.lamPi
   (Term.refl applyRaw.weaken)`-shaped canonical.
2. Standard `Step.par.betaAppPiDeep` fires from that canonical.

That kernel extension (≈ 400 LoC across `RawPar.lean`,
`Reduction/ParRed/ParInductive.lean`, the `Bridge.lean`
dispatcher, and the cd cascade in `Reduction/ParRed/CdLemma.lean`)
is tracked separately as Goal #1.  The funextRefl portion of
`lift_full_appPi` is deferred to that batch, OR to a smaller
kernel-extension batch adding only `Step.par.betaAppPiFunextRefl`
(the eta-redesign memo recommends the broader piEta + arrowEta
introduction for maximum cascade leverage).

## Investigation: structured-source pattern viability

`EliminatorFunextFamily.lean` (commit 48dc4f8) demonstrated the
**structured-source pattern** for the four HoTT-special
cong-only lifts (`lift_funextRefl`, `lift_funextReflAtId`,
`lift_funextIntroHet`, `lift_uaToEquiv`): pre-commit the source
to a specific Term constructor, sidestepping the `cases
genericTerm` multi-ctor dispatch trap.

For `lift_full_appPi`, the structured-source split would be:

* **`lift_full_appPi_lamPi`**: source pre-committed to
  `Term.appPi (Term.lamPi body) argTerm`.  This collapses to a
  thin wrapper around the shallow `Step.par.betaAppPi` rule plus
  the cong arm — essentially equivalent to `lift_appPi_cong`
  extended with shallow β.  Structurally weaker than the
  headline-form `lift_full_appPi` because the source's function
  position must already be `Term.lamPi`-shaped at the type level,
  which the headline walker does NOT guarantee (functions are
  introduced as generic `Term ctx (Ty.piTy ...) fRaw` parameters).
* **`lift_full_appPi_funextRefl`**: source pre-committed to
  `Term.appPi (Term.funextRefl ...) argTerm`.  Blocked by the
  same kernel-rule absence — no `Step.par` constructor produces a
  target from this source's β-firing.

Neither half advances the headline walker's needs.  The cleanest
shipping strategy is therefore:

* Ship audit gates for the three existing β-rule lifts under
  B.3a (this audit).
* Acknowledge the `lift_full_appPi` gap concretely with a
  cross-reference to the eta-redesign memo.
* Defer the gap closure to the kernel-extension follow-up
  (Goal #1 / typed-eta redesign batch), which IS shipping work
  by the same warrior cohort, not v1.1 deferral.

## What about `lift_full_pathApp`, `lift_full_idJ`,
`lift_full_idStrictRec`, `lift_full_boolElim`?

These are full β/ι-rule lifts already shipped in
`BetaCastWallDemolition.lean` and `HeterogeneousElim.lean`.
They cover their respective β/ι-rule families through their own
destructors:

| Lift | β/ι-rule | Destructor |
| --- | --- | --- |
| `lift_full_pathApp` | `betaPathAppDeep` | `Term.pathLamDestruct` |
| `lift_full_idJ` | `iotaIdJReflDeep` | `Term.idReflDestruct` |
| `lift_full_idStrictRec` | `iotaIdStrictRecReflDeep` | `Term.idStrictReflDestruct` |
| `lift_full_boolElim` | `iotaBoolElim{True,False}Deep` | `Term.boolTrue/False_unique` |

`lift_full_pathApp` works because the canonical inhabitants of
`Ty.path carrierType leftEndpoint rightEndpoint` with raw
`RawTerm.pathLam bodyRaw` are uniquely produced by
`Term.pathLam` — no funextRefl-style ambiguity.  Similarly the
identity-eliminator lifts disambiguate via the `Ty.id` / `Ty.idStrict`
typings.

These four lifts are NOT in B.3a scope (B.3a focuses on Π/Σ β
rules); they are audit-gated under follow-up B.3.* tickets
(B.3b for ι rules of `boolElim`/`natElim`/`listElim`/etc., B.3c
for cubical β/ι, B.3d for identity ι, etc.).

## Cascade role

B.3a is the first β-rule lift audit, completing the Π/Σ
β-coverage modulo the documented appPi blocker.  Subsequent
B.3.* tickets handle ι rules for closed-type eliminators
(boolElim, natElim, natRec, listElim, optionMatch, eitherMatch
— #1730 B.3b), cubical β/ι rules (#1731 B.3c), identity ι rules
(#1732 B.3d), modal/HoTT-special β/ι rules (#1733 B.3e), and
the appPi-funextRefl closure once the kernel eta-redesign lands
(coupled to Goal #1).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2gTypeCodeHottCong.lean` and
the prior B.2.* audits: `Term.PreservesTerm` is reachable as a
production module only through its smoke audits.  Co-location of
`#print axioms` with the strict gates keeps the reviewer-facing
log adjacent.

The `#assert_no_axioms` strict gates fire under the
`LeanFX2Audit` target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB2gTypeCodeHottCong.lean`: pre-existing typed β-rule
lifts with one `#assert_no_axioms` strict gate per lift, one
`#print axioms` reviewer log per lift.  No new theorem bodies
shipped in this commit — the three β-rule lifts existed prior
under B.2a's wake.  The new B.3a banner certifies the existing
β-rule coverage as a coherent audit family. -/

namespace LeanFX2.SmokeConvTransB3aPiSigmaBeta

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the three Π/Σ
β-rule lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_app
#assert_no_axioms LeanFX2.RawStep.par.lift_full_fst
#assert_no_axioms LeanFX2.RawStep.par.lift_full_snd

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside
the strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_full_app
#print axioms LeanFX2.RawStep.par.lift_full_fst
#print axioms LeanFX2.RawStep.par.lift_full_snd

end LeanFX2.SmokeConvTransB3aPiSigmaBeta
