import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.PinnedPiRenameImage

/-! Probe (T2 post-migration target): discharge the lambda-reduct residual of the pinned
reflection — `PinnedReflectionPiElimLamReductResidual` — against the ANNOTATED engine.

STATUS: written DURING the T2 grind (tree red); signatures below are the intended
post-migration shapes.  Do not expect this file to compile until the fleet finishes; the
value is the locked-in proof design.  Verify each helper's actual post-migration signature
before shipping (especially `invertLam` from agent 6's corner).

## Why T2 makes this dischargeable (the design, locked)

The pre-T2 obstruction: a Curry lambda's domain was invisible, so the source function's
Pi classifier had no pin derivable from the OUTPUT pin alone (the function-Pi float), and
every reconstruction route died on lambda typing non-uniqueness (six fenced refutations +
the eta-extraction cycle; see the firing log 2026-06-09/10).  Under T2 the lambda CARRIES
its domain: `lamCell annotation body`, and `piIntro` forces classifier domain = annotation.

## The discharge, step by step

Premises (the residual's): `functionTyped : HasTypeDescPi profile targetContext functionTerm
(piTyCodeCell domainCode codomainCode)`, `argumentTyped`, `functionTerm ↝* lamCell lamDomain
lamBody` (whnf, normal), the function/argument IH reflections, and the conclusion's inputs:
target-wf, `rho` injective, the (flag-coherent) context condition, source-wf, the subject
in-image equation `appCell functionTerm argument = rename rho sourceSubject`, the OUTPUT pin
`Conv (subst0 codomainCode argument) (rename rho pinBase)`, pinBase valid.

1. IN-IMAGE SPLIT.  `renameEqAppCellInversion` (PinnedPiRenameImage, [0,0] spine drilling):
   `sourceSubject = appCell sourceFunction sourceArgument` with
   `functionTerm = rename rho sourceFunction`, `argument = rename rho sourceArgument`.

2. REDUCT IN-IMAGE.  `StepStar.reflectRename` on `functionTerm ↝* lamCell lamDomain lamBody`
   (function IS in-image by step 1): a SOURCE chain `sourceFunction ↝* sourceReduct` with
   `rename rho sourceReduct = lamCell lamDomain lamBody`.  The drilling lemma ALREADY SHIPPED
   in the migration: `RawTerm.rename_eq_lam` (HeadStepRenameReflect.lean, agent-2 corner) was
   re-stated under T2 to expose BOTH components — a renamed term equal to an annotated lambda
   is an annotated lambda with `rename rho sourceDomain = lamDomain` and
   `rename (RawRenaming.lift rho) sourceBody = lamBody`.  Consume it directly; no new lemma.

3. REDUCT TYPING + THE T2 PIN.  `subjectReductionStar` keeps
   `lamCell lamDomain lamBody : piTyCodeCell domainCode codomainCode` in the target.  The
   ANNOTATED `invertLam` now yields `Conv (piTyCodeCell domainCode codomainCode)
   (piTyCodeCell lamDomain bodyClassifier)` with the classifier domain pinned to the
   SYNTACTIC annotation `lamDomain = rename rho sourceDomain` — so the function's Pi
   classifier is pinned to a renamed source term ON THE DOMAIN COMPONENT, definitionally:
   `Conv lamDomain (rename rho sourceDomain) = Conv.refl`.  THE FLOAT IS DEAD.

4. DOMAIN/CODOMAIN COMPONENT PINS.  `Conv.piTyCode_injective` on step 3's Conv:
   `Conv domainCode lamDomain` and `Conv codomainCode bodyClassifier` — composing,
   `Conv domainCode (rename rho sourceDomain)`: the DOMAIN pin the argument IH needs.

5. ARGUMENT REFLECTION.  Fire the argument IH at pin base `sourceDomain` (step 4's pin) +
   `sourceDomain`'s validity (from invertLam's reflected domain premise — its classifier is
   a universe code, rename-invariant, so its own pin is free; reflect it with the
   leaf/formation machinery or `pinBaseValidAtCallerPair`):
   `∃ reflectedDomain, Conv domainCode (rename rho reflectedDomain) ∧
   HasTypeDescPi profile sourceContext sourceArgument reflectedDomain`.

6. BODY REFLECTION UNDER THE BINDER.  The body typing lives in
   `targetContext.cons lamDomain`; the binder pin is `Conv lamDomain (rename rho
   sourceDomain)` — under T2 the SYNTACTIC equality makes the Kripke extension
   (`ContextReflectsRename(FlagCoherent).consConv`) fire with `Conv.refl`-strength data and
   image = target DEFINITIONALLY (`rename_lift_weaken_commute`).  The body's
   pinned-reflection (the shipped piIntro-arm machinery over the lifted renaming, which is
   injective by `RawRenaming.lift_injective`) gives
   `HasTypeDescPi profile (sourceContext.cons sourceDomain) sourceBody reflectedCodomain`
   with `Conv bodyClassifier (rename (lift rho) reflectedCodomain)`.

7. SOURCE REASSEMBLY.  `piIntro` in the source: domain validity (step 5's premise leg),
   codomain validity (step 6's reflected validity leg at the shared flag — the
   flag-coherent condition's triple supplies the shared (level, flag); this is exactly what
   E1/E3 shipped), body typing (step 6) give
   `HasTypeDescPi profile sourceContext (lamCell sourceDomain sourceBody) (piTyCodeCell
   sourceDomain reflectedCodomain)`.  Then EITHER (a) head-expand: `sourceFunction ↝*
   lamCell sourceDomain sourceBody` + strengthening-free re-typing of the CHAIN is not
   available — so instead (b) type the REDUCT application: `appCell (lamCell sourceDomain
   sourceBody) sourceArgument` via `piElim` (argument re-pinned to `sourceDomain` through
   step 4+5's Conv composition and the source `conv` rule), and reflect the ORIGINAL
   subject through the residual conclusion's freedom: the conclusion asks for SOME
   reflectedClassifier for `appCell sourceFunction sourceArgument` — use the source SR-star
   inverse direction... NO: use the source typing of the original application directly:
   `sourceFunction` itself gets typed at `piTyCodeCell sourceDomain reflectedCodomain` by
   the residual's FUNCTION IH fired at pin base `piTyCodeCell sourceDomain
   reflectedCodomain` — its pin is `Conv (piTyCodeCell domainCode codomainCode)
   (rename rho (piTyCodeCell sourceDomain reflectedCodomain))` assembled componentwise from
   steps 4+6 via `Conv.ofChildren` (THE COMPONENT-WISE ASSEMBLY THAT USED TO HIT THE FLAG
   WALL — closed by E3's pinBaseValidAtCallerPair), and its validity is the source
   Pi-formation over steps 5/6's validity legs.  Then `piElim` + `conv`.

8. OUTPUT CLASSIFIER.  `RawTerm.rename_subst0_commute`:
   `rename rho (subst0 reflectedCodomain sourceArgument) = subst0 (rename (lift rho)
   reflectedCodomain) (rename rho sourceArgument)`; compose with steps 4/6's Convs +
   `Conv.subst` to land the required
   `Conv (subst0 codomainCode argument) (rename rho (subst0 reflectedCodomain
   sourceArgument))`.  Conclusion: `reflectedClassifier := subst0 reflectedCodomain
   sourceArgument`.

## Dependency checklist (post-grind signature confirmations)

- [x] `invertLam` (agent 6 DONE): domain existential DROPPED — the Pi classifier's domain IS
      the syntactic annotation; 8-tuple output; subject equation carries {domainAnn}.
      Step 3 consumes exactly this.
- [x] `RawTerm.rename_eq_lam` (agent 2 DONE): step 2's drilling, exposes (domainAnn, body).
- [x] `eq_lamCell_of_headGenerator` (agent 6 DONE): `∃ domainAnn body, ...` — for any
      whnf-head dispatch the discharge shares with the dispatcher.
- [ ] `Conv.piTyCode_injective` — LOCATION CORRECTED: lives in
      FX1Poly/Typed/HasTypeDescPiContextConversion.lean (NOT Core); agent-12 sweep corner,
      confirm after the fleet lands.
- [ ] `renameEqAppCellInversion` (brick A, PinnedPiRenameImage) — agent 8 reshaped; its twin
      `renameEqLamCellInversion` was STRENGTHENED to expose (sourceDomain, sourceBody) with
      `domainAnn = rename rho sourceDomain` — exactly step 2's alternative entry; confirm.
- [x] `Step.reflectRename` (Core/StepRenameReflectAssembly.lean:68, GREEN post agent 10):
      `(rho) {sourceTerm}{targetReduct} : Step (rename rho sourceTerm) targetReduct →
      ∃ sourceReduct, Step sourceTerm sourceReduct ∧ rename rho sourceReduct = targetReduct`.
      NOTE: this is the ONE-STEP form; step 2 needs the star lift — either a shipped
      StepStar wrapper or a 5-line chain induction over it (injectivity-free, rho fixed).
- [x] `ContextReflectsRename.consConv` / flag-coherent `consConv` (shipped, E1).
- [x] `pinBaseValidAtCallerPair` + `renameAlongFlagCoherent` (shipped, E3; agent 9 owns the
      RenameAlongFlagCoherent re-thread).
- [x] `Conv.subst` + `Conv.subst0` (Core/ConvSubstRename.lean:119/174, GREEN);
      `Conv.ofChildren` (Core/ConvCongruence.lean, GREEN, signature confirmed).
- [ ] `RawTerm.rename_subst0_commute` — exact name unconfirmed; the commutation EXISTS in the
      subst/rename substrate (rename-subst commute family in Core, green); pin the name at
      ship time.
- [x] `RawRenaming.lift_injective` (shipped pre-campaign).

POST-FLEET GROUND-TRUTH NOTES (wave-3, agent 11 CONFIRMED):
- Agent 10's domainAnnSN convention applies to REDUCIBILITY abstraction lemmas only; the
  `piIntro` TYPING rule (step 7's reassembly) is unaffected — no SN premise enters the
  discharge.
- Agent 11 RESOLVED the PinnedReflectionPiIntro gap the principled way; step 6 inherits
  TWO confirmed structures:
  (a) `pinnedReflectionPiIntroArm` now takes `domainIH : PinnedReflectionConclusion ...
      domainCode (universeCodeCell domainLevel flag)` — the domain is a universe-typed
      sub-derivation carrying its OWN reflection IH (replacing the old
      `targetDomainIsType : IsTypeDescPi` premise).  `ClassifierRespectsConvRefuted`
      makes Conv-based domain re-typing IMPOSSIBLE — the domain-IH route is THE pattern;
      the discharge's step 5/6 should fire the domain IH the same way.
  (b) `flagUnique : SourceUniverseFlagUnique profile` — domain reflected at the rule's
      flag, codomain at the inverted Π-code's flag, `piIntro` demands one shared flag;
      their equality is `convUniverseClassificationUnique`, architecturally DOWNSTREAM
      (import cycle through NormalAppNeutral → PiElimDispatcher → PinnedReflectionPiIntro).
      The discharge theorem inherits `flagUnique` as a premise; the ASSEMBLY (which sits
      above the cycle) discharges it with `convUniverseClassificationUnique`.
  New bricks available: `ConvContextWithOldValid.ofHeadConv` (head-Conv context step),
  `RawTerm.size_lt_lamCell_domain`, `lamNormal_domainNormal`.
- ★ THE RESIDUAL IS PLAUSIBLY TRUE OUTRIGHT (agent 11): T2 flipped
  `ConvExistentialStrengtheningRefutation` — `weakenedIdentityTypedAtVariableDomainPi`
  is unprovable (the annotation pins the Π-domain to an in-image term), so
  `pinnedReflectionLamClassifierResidual_isFalse` cannot be re-proven.  The discharge
  this probe designs is the honest POSITIVE replacement.  AUDIT IMPACT: the two stale
  gates at FX1PolyAudit/AuditTyped.lean:8466 (`weakenedIdentityTypedAtVariableDomainPi`)
  and :8619 (`pinnedReflectionLamClassifierResidual_isFalse`) + the import at :555 and
  comment at :8459 must be retired/replaced WITH the discharge (names assert falsity —
  cannot be content-swapped honestly; needs the user-sanctioned cleanup pass).

No new lemmas needed: every ingredient exists post-migration.  The ship firing states the
discharge theorem against `PinnedReflectionPiElimLamReductResidual(FlagCoherent)` and walks
steps 1-8 with the confirmed signatures.
-/
