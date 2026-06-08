import FX1Poly.Typed.LevelingBridge
import FX1Poly.Typed.ValidTypingRefinedMotive

/-! SCRATCH probe for #662 totalBridge assembly (NEVER committed; persists across loop fires).

PROBE FINDINGS (2026-06-05, fire N):

1. `induction typed` FAILS — HasTypeDescPi is MUTUAL with DescTelescopePi. Must use
   `HasTypeDescPi.rec (motive_1 := …) (motive_2 := <telescope motive>) ?ofFormation ?conv
   ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope typed` — 7 minor premises,
   exactly the shape of `HasTypeDescPi.fundamentalVectorFromFormation`
   (HasTypeDescPiFundamentalVectorFromFormation.lean) — MIRROR THAT FILE'S STRUCTURE.

2. motive_1 := fun context subject classifier _ => ∀ contextLevels, TotalBridgeConclusion …
   does NOT close at conv-to-type-VARIABLE: validTypingBridgeConvPinnedReclassifier needs
   `contextLevels j = subjectLevel + 1` (var j pinned), but ∀-quantified contextLevels is
   arbitrary. ⇒ motive needs a STRATIFICATION precondition (type-binding one level above the
   terms it classifies). This crux is PERVASIVE — it also arises in the formation sub-engine
   (a term-variable x:X whose type X is itself a type-variable var j), so even the ofFormation
   arm's formation-leveling-bridge hits it. NOT avoided by restricting to formation.

3. The ofFormation arm needs a FORMATION-engine totalBridge (HasTypeDesc → ∀cl, TBC) as a
   sub-assembly (the formation arms var/conv/universeFormation/genFormation). #674 gives
   HasTypeDesc → reducibility, NOT → ValidTyping/TBC — so the formation leveling bridge is a
   DISTINCT sub-assembly to build (also conv-var-crux-blocked per (2)).

DECOMPOSITION for the multi-fire effort:
  (a) Define ConsistentStratification cl context (the type-binding-one-above invariant) + its
      empty-context base + binder-extension preservation (levelCons predLevel+1 stays consistent).
  (b) Formation leveling bridge: HasTypeDesc → ∀cl, Consistent cl context → TBC … (mutual w/ DescTelescope).
  (c) Grown arms (piIntro/piElim) over the same motive; piElim-align via the shared cl.
  (d) Assemble via HasTypeDescPi.rec; conv-var via validTypingBridgeConvPinnedReclassifier + the invariant.
  (e) Top: stratification EXISTENCE (the inference) discharges the precondition ⇒ totalBridge.
  ALL funext-free: build levelCons FORWARD into binders, never reconstruct (shiftLevels is funext-trapped).

NEXT FIRE: start at (a) — define ConsistentStratification + prove empty-base + binder-preservation
(a self-contained, committable LIBRARY brick that does NOT need the full induction). That is the
first GREEN piece of the multi-fire #662 effort.

==== UPDATE (sub-goal (a) COMPLETE + conv-arm dispatch precisely understood) ====

(a) IS DONE — shipped + gated + zero-axiom:
  - ConsistentStratification def + empty base + strictlyBelowType + noSelfType (174b4c6c)
  - rename_eq_variableCell_inversion (79393dde) — the binder-extension key lemma
  - ConsistentStratification.cons (8530d3a9) — binder-extension preservation (uses the inversion +
    rfl-closed levelCons_weaken over the propext-free Fin split; domainConstraint = the local edge)
  - convVariableReclassifierOfStratified (721b4aae, in ValidTypingConvArm.lean) — the conv-arm PAYOFF

CONV-ARM DISPATCH — the precise picture (do NOT re-derive, it cost a scare):
  validTypingBridgeConvPinnedReclassifier (LevelingBridge.lean:468) keys on
  `reclassifierIsUniverse : context.lookup index = universeCodeCell …` (the reclassifier VARIABLE's own
  looked-up type is a UNIVERSE) + `levelMatch : contextLevels index = subjectLevel + 1`. The conv-VARIABLE
  arm thus splits THREE ways by who/what supplies levelMatch:
    1. convNonVariableReclassifier — reclassifier is a universe-code/Π-Σ former (LEVEL-FLEXIBLE, no eq).
    2. convBoundVariableReclassifier — reclassifier is the FRESH ⟨0,_⟩ var (levelMatch = rfl by levelCons).
    3. convVariableReclassifierOfStratified — DEEPER tower: SUBJECT is `var termIndex`, its looked-up type
       IS the reclassifier var (lookup termIndex = variableCell index, the `x:A:Type` tower). levelMatch
       = `consistent termIndex index (that lookup eq)` — THIS is where ConsistentStratification pays off.
  KEY INSIGHT: `reclassifierIsUniverse` is about the RECLASSIFIER index; ConsistentStratification is about
  the SUBJECT's index whose lookup = variableCell(reclassifier). Different indices, both needed. The
  invariant `lookup termIndex = variableCell index ⟹ contextLevels index = contextLevels termIndex + 1`
  is EXACTLY the tower edge `A↦k+1, x↦k`.

==== UPDATE 2 (conv-rigidity dispatch fact shipped) ====
variableCell_inj_of_conv (e5b41913, UniverseCodeConversion.lean): Conv (var a) (var b) -> a = b, via the
normal-form collapse (Conv.iff_normalForms_eq_of_confluence + mkGen injectivity). Twin of
universeCodeCell_inj_of_conv. This is the conv-arm dispatch alignment fact: at a formation conv node whose
reclassifier is var index and whose subject's classifier is a convertible variable, the indices coincide.

CONV-ARM DISPATCHER (the next sub-brick toward b) — SCOPING NOTE:
  The formation engine HasTypeDesc subjects are var / universe-code / former (NO lam/app). At a conv node
  (subject : classifier, classifier Conv reclassifier, reclassifier : universe), routing to a TBC arm needs
  isVariableOrNot on the RECLASSIFIER:
    - reclassifier NON-variable → convNonVariableReclassifier (needs the reclassifier IH = level-flexibility).
    - reclassifier = var index → need lookup index = universeCode (reclassifier is a valid type) + the level.
      The subject is var/universe-code/former:
        * subject = var termIndex: classifier (= lookup termIndex via var-arm coherence) Conv var index.
          If lookup termIndex = var j: var j Conv var index → j = index (variableCell_inj_of_conv) → lookup
          termIndex = var index → convVariableReclassifierOfStratified (needs ConsistentStratification).
          If lookup termIndex = universe/former: universe/former Conv var index is FALSE → vacuous
          (variableCell_not_conv_universeCodeCell + a former-not-conv-variable twin, may need building).
        * subject = universe-code/former: classifier = universe/Type → classifier Conv var index FALSE → vacuous.
  OPEN QUESTION to resolve next fire: does the assembly's conv-node IH hand us the subject in a form where we
  can read "subject = var termIndex with classifier = lookup termIndex"? In HasTypeDesc.rec the conv arm's
  subject is the recursor variable (general). Likely need to INVERT the inner derivation (the subject's own
  HasTypeDesc) to learn its shape — OR carry a stronger motive. CHECK how the GROWN refined-motive conv arm
  (#673 UB-TB-conv) + ofTermValidity structure the dispatch; mirror it.

==== UPDATE 3 (CONV-RIGIDITY TOOLKIT NOW COMPLETE — vacuous cases all dischargeable) ====
Shipped d41bb5af: Conv.piTyCode_not_variableCell + Conv.sigmaTyCode_not_variableCell (ConvCodeInjectivity.lean)
— a former never Conv a variable (shapeStable + noStep_var + noConfusion). With these + the earlier facts the
full conv-rigidity toolkit is COMPLETE:
  variableCell_inj_of_conv (var a Conv var b -> a=b), variableCell_not_conv_universeCodeCell,
  piTyCode_not_variableCell, sigmaTyCode_not_variableCell, piTyCode_not_universeCode,
  sigmaTyCode_not_universeCode, universeCodeCell_inj_of_conv, piTyCode_not_sigmaTyCode, +Empty twins.

CONV-VARIABLE ARM DISPATCH — now traced END TO END (reclassifier = var index, formation engine):
  Subject is var / universe-code / former (formation engine has no lam/app).
   - subject = former: classifier = universeCodeCell; classifier Conv var index -> VACUOUS by
     variableCell_not_conv_universeCodeCell (symmetric). KILLED.
   - subject = universe-code: same, VACUOUS. KILLED.
   - subject = var termIndex: classifier = lookup termIndex (var rule); lookup termIndex Conv var index:
       * lookup termIndex = var j  -> j=index (variableCell_inj_of_conv) -> lookup termIndex = var index ->
         LIVE: convVariableReclassifierOfStratified (needs ConsistentStratification, SHIPPED).
       * lookup termIndex = former  -> VACUOUS by piTyCode/sigmaTyCode_not_variableCell. KILLED.
       * lookup termIndex = universe -> VACUOUS by variableCell_not_conv_universeCodeCell. KILLED.
  => EXACTLY ONE LIVE CASE (subject=var, type=var=reclassifier), all else vacuous via the toolkit.

REMAINING for the conv-arm dispatcher brick (next fire): (1) get reclassifierIsUniverse (lookup index =
universeCodeCell) from the reclassifier's typing at a universe — may need "lookup index Conv universeCodeCell
=> reduces to a universe code" + the rigidity facts; (2) invert the subject into var/universe/former (a
formation-subject shape classification — or read it off the recursor's conv-arm structure); (3) the
stratification precondition. THEN assemble var/universeFormation/conv-dispatch/genFormation via HasTypeDesc.rec.

NEXT FIRE = brick (b): the FORMATION leveling-bridge induction
  `HasTypeDesc Γ t T → ∀ contextLevels, ConsistentStratification contextLevels Γ → TotalBridgeConclusion …`
  (mutual w/ DescTelescope). This is the HARD multi-arm assembly (per finding 1: must use HasTypeDescPi.rec
  / the formation HasTypeDesc.rec with the telescope motive_2; MIRROR fundamentalVectorFromFormation's shape).
  The conv arm now routes: isVariableOrNot → {convNonVariableReclassifier | the two variable arms}. The
  var/universeFormation/genFormation arms are leaves. The STRATIFICATION precondition must thread through
  binders via ConsistentStratification.cons (the domainConstraint discharged from the binder's IsType deriv).
  Then (c) grown piIntro/piElim arms, (d) assemble via the grown rec, (e) stratification EXISTENCE (the
  inference: synthesize contextLevels from the level-free context) discharges the precondition ⟹ totalBridge
  ⟹ SN-027 unconditional (route-A crosscheck; SN-043 already closed via BFT/OB-5, so this is SN-150 triangulation).
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- (skeleton intentionally omitted — see fundamentalVectorFromFormation for the rec shape)

end FX1Poly.Typed
