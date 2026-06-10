import FX1Poly.Core.StepEta
import FX1Poly.Core.RawTermStrengthen
import FX1Poly.Core.Normalize

/-! # FX1Poly/Core/FireRootEtaRedex
   — the computable root η-firer + the layered βη one-step reducer (ETA-2)

The ETA-1 census (`BetaEtaConvGapStatement`) reduced decidable `BetaEtaConv` on the wf-typed
fragment to ONE missing computable artifact: a sound+complete βη one-step reducer.  This file
ships it.  The load-bearing simplification is that `Step.eta` is ROOT-ONLY (five constructors,
no congruence arm), so the η side needs no traversal at all:

  * `RawTerm.fireRootEtaRedex?` — fire the root η-redex, exactly when one exists.  The five
    source shapes are matched by the `fireRootRedex` dite-and-transport idiom; the binder cases
    (`etaLam` / `etaPathLam`) detect `weaken f` via the shipped `RawTerm.strengthen` (occurs
    check), and the duplicate-child cases (`etaPair` / `etaGlueIntro`) compare copies with the
    propext-free `DecidableEq RawTerm`.
  * five computation equations (`fireRootEtaRedex?_etaXxxSource`) — every η-source fires, to the
    η-rule's contractum (the `strengthen_weaken` round-trip discharges the binder cases).
  * `fireRootEtaRedex?_sound` / `fireRootEtaRedex?_complete` — fires only real `Step.eta` steps,
    and halts exactly on η-inert terms (EXACT because `Step.eta` is root-only).
  * `RawTerm.reduceOnceBetaEta` — the layered βη reducer: β/ι first (the shipped
    leftmost-outermost `reduceOnce`), then the root η-firer on β/ι-normal terms, with
    `reduceOnceBetaEta_sound` / `reduceOnceBetaEta_complete` against the FULL union
    `Step.betaEta = Step ∨ Step.eta`.

With the metatheory bundle (`betaEtaDeciderMetatheoryPrerequisitesHold`: typed βη-SN + typed
βη-CR + unique βη-NF + star-rigidity) this completes the ingredient list for the βη normalizer
and decidable `BetaEtaConv` on the wf fragment — the assembly is the named follow-on.

## Zero-axiom verification

The firer follows the `fireRootRedex` propext-clean idiom (dite on generator equality + transport
cast + structural child matches); soundness/completeness are `split`-driven case analyses feeding
`strengthen_sound` / `strengthen_weaken` and the five `Step.eta` constructors; the βη layer
composes `reduceOnce_sound` / `reduceOnce_complete` / `isStepNormalForm_blocks_step`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Fire the root η-redex, exactly when one exists.**  Dispatches on the five η-source heads;
binder shapes recover the strengthened function via `RawTerm.strengthen`, duplicate-child shapes
compare the two stored copies. -/
def RawTerm.fireRootEtaRedex? {scope : Nat} (term : RawTerm scope) : Option (RawTerm scope) :=
  match term with
  | .mkGen generator _payload children =>
    if hLam : generator = .gen_lam then
      match (hLam ▸ children : RawTermChildren (Generator.gen_lam.binderShifts) scope) with
      | .childCons _domainAnn (.childCons body .childNil) =>
          match body with
          | .mkGen bodyGenerator _bodyPayload bodyChildren =>
              if hApp : bodyGenerator = .gen_app then
                match (hApp ▸ bodyChildren :
                    RawTermChildren (Generator.gen_app.binderShifts) (scope + 1)) with
                | .childCons functionChild (.childCons argumentChild .childNil) =>
                    match argumentChild with
                    | .mkGen argGenerator argPayload _argChildren =>
                        if hVar : argGenerator = .gen_var then
                          match (hVar ▸ argPayload : Generator.gen_var.payload (scope + 1)) with
                          | ⟨0, _⟩ => RawTerm.strengthen functionChild
                          | ⟨_ + 1, _⟩ => none
                        else none
              else none
    else if hPair : generator = .gen_pair then
      match (hPair ▸ children : RawTermChildren (Generator.gen_pair.binderShifts) scope) with
      | .childCons firstChild (.childCons secondChild .childNil) =>
          match firstChild, secondChild with
          | .mkGen firstGenerator _firstPayload firstChildren,
            .mkGen secondGenerator _secondPayload secondChildren =>
              if hFst : firstGenerator = .gen_fst then
                if hSnd : secondGenerator = .gen_snd then
                  match (hFst ▸ firstChildren :
                      RawTermChildren (Generator.gen_fst.binderShifts) scope) with
                  | .childCons fstPayloadTerm .childNil =>
                      match (hSnd ▸ secondChildren :
                          RawTermChildren (Generator.gen_snd.binderShifts) scope) with
                      | .childCons sndPayloadTerm .childNil =>
                          if fstPayloadTerm = sndPayloadTerm then some fstPayloadTerm else none
                else none
              else none
    else if hPathLam : generator = .gen_pathLam then
      match (hPathLam ▸ children :
          RawTermChildren (Generator.gen_pathLam.binderShifts) scope) with
      | .childCons body .childNil =>
          match body with
          | .mkGen bodyGenerator _bodyPayload bodyChildren =>
              if hPathApp : bodyGenerator = .gen_pathApp then
                match (hPathApp ▸ bodyChildren :
                    RawTermChildren (Generator.gen_pathApp.binderShifts) (scope + 1)) with
                | .childCons functionChild (.childCons argumentChild .childNil) =>
                    match argumentChild with
                    | .mkGen argGenerator argPayload _argChildren =>
                        if hVar : argGenerator = .gen_var then
                          match (hVar ▸ argPayload : Generator.gen_var.payload (scope + 1)) with
                          | ⟨0, _⟩ => RawTerm.strengthen functionChild
                          | ⟨_ + 1, _⟩ => none
                        else none
              else none
    else if hModIntro : generator = .gen_modIntro then
      match (hModIntro ▸ children :
          RawTermChildren (Generator.gen_modIntro.binderShifts) scope) with
      | .childCons innerChild .childNil =>
          match innerChild with
          | .mkGen innerGenerator _innerPayload innerChildren =>
              if hModElim : innerGenerator = .gen_modElim then
                match (hModElim ▸ innerChildren :
                    RawTermChildren (Generator.gen_modElim.binderShifts) scope) with
                | .childCons modalTerm .childNil => some modalTerm
              else none
    else if hGlueIntro : generator = .gen_glueIntro then
      match (hGlueIntro ▸ children :
          RawTermChildren (Generator.gen_glueIntro.binderShifts) scope) with
      | .childCons firstChild (.childCons secondChild .childNil) =>
          match firstChild with
          | .mkGen firstGenerator _firstPayload firstChildren =>
              if hGlueElim : firstGenerator = .gen_glueElim then
                match (hGlueElim ▸ firstChildren :
                    RawTermChildren (Generator.gen_glueElim.binderShifts) scope) with
                | .childCons gluedTerm .childNil =>
                    if gluedTerm = secondChild then some secondChild else none
              else none
    else none

/-! ## Computation equations — every η-source fires, to its contractum -/

/-- The function η-source fires to the strengthened inner function. -/
theorem RawTerm.fireRootEtaRedex?_etaLamSource {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) :
    (RawTerm.etaLamSource domainAnn innerFunction).fireRootEtaRedex? = some innerFunction := by
  show RawTerm.strengthen (RawTerm.weaken innerFunction) = some innerFunction
  exact RawTerm.strengthen_weaken innerFunction

/-- The pair η-source fires to the shared payload. -/
theorem RawTerm.fireRootEtaRedex?_etaPairSource {scope : Nat} (pairTerm : RawTerm scope) :
    (RawTerm.etaPairSource pairTerm).fireRootEtaRedex? = some pairTerm := by
  show (if pairTerm = pairTerm then some pairTerm else none) = some pairTerm
  rw [if_pos rfl]

/-- The path η-source fires to the strengthened inner path. -/
theorem RawTerm.fireRootEtaRedex?_etaPathLamSource {scope : Nat} (innerPath : RawTerm scope) :
    (RawTerm.etaPathLamSource innerPath).fireRootEtaRedex? = some innerPath := by
  show RawTerm.strengthen (RawTerm.weaken innerPath) = some innerPath
  exact RawTerm.strengthen_weaken innerPath

/-- The modal η-source fires to the boxed payload. -/
theorem RawTerm.fireRootEtaRedex?_etaModIntroSource {scope : Nat} (modalTerm : RawTerm scope) :
    (RawTerm.etaModIntroSource modalTerm).fireRootEtaRedex? = some modalTerm := rfl

/-- The Glue η-source fires to the glued payload. -/
theorem RawTerm.fireRootEtaRedex?_etaGlueIntroSource {scope : Nat} (gluedTerm : RawTerm scope) :
    (RawTerm.etaGlueIntroSource gluedTerm).fireRootEtaRedex? = some gluedTerm := by
  show (if gluedTerm = gluedTerm then some gluedTerm else none) = some gluedTerm
  rw [if_pos rfl]

/-! ## Completeness — the firer halts exactly on η-inert terms (Step.eta is root-only) -/

/-- **The firer halts only on η-inert terms.**  EXACT because `Step.eta` is root-only: a `cases`
on the step pins the subject to one of the five source shapes, whose computation equation
contradicts the `none` hypothesis. -/
theorem RawTerm.fireRootEtaRedex?_complete {scope : Nat} {term : RawTerm scope}
    (halted : term.fireRootEtaRedex? = none) :
    ∀ reduct : RawTerm scope, ¬ Step.eta term reduct := by
  intro reduct step
  cases step with
  | etaLam domainAnn innerFunction =>
      rw [RawTerm.fireRootEtaRedex?_etaLamSource] at halted; cases halted
  | etaPair pairTerm =>
      rw [RawTerm.fireRootEtaRedex?_etaPairSource] at halted; cases halted
  | etaPathLam innerPath =>
      rw [RawTerm.fireRootEtaRedex?_etaPathLamSource] at halted; cases halted
  | etaModIntro modalTerm =>
      rw [RawTerm.fireRootEtaRedex?_etaModIntroSource] at halted; cases halted
  | etaGlueIntro gluedTerm =>
      rw [RawTerm.fireRootEtaRedex?_etaGlueIntroSource] at halted; cases halted

/-! ## Soundness — the firer fires only real root η steps -/

/-- **The firer fires only real `Step.eta` steps.**  Split-cascade through the dite/match chain;
each success arm reassembles the matched structure into the corresponding `etaXxxSource` shape
(the binder arms rewrite the function child back to `weaken reduct` via `strengthen_sound`; the
duplicate-child arms substitute the equality test's proof). -/
theorem RawTerm.fireRootEtaRedex?_sound {scope : Nat} {term reduct : RawTerm scope}
    (success : term.fireRootEtaRedex? = some reduct) :
    Step.eta term reduct := by
  cases term with
  | mkGen generator payload children =>
      dsimp only [RawTerm.fireRootEtaRedex?] at success
      split at success
      · next hLam =>
          subst hLam
          split at success
          next domainAnn body hChildrenEq =>
          have hChildren :
              children = .childCons domainAnn (.childCons body .childNil) := hChildrenEq
          subst hChildren
          split at success
          next bodyGenerator bodyPayload bodyChildren =>
          split at success
          · next hApp =>
              subst hApp
              split at success
              next functionChild argumentChild hBodyChildrenEq =>
              have hBodyChildren :
                  bodyChildren =
                    .childCons functionChild (.childCons argumentChild .childNil) :=
                hBodyChildrenEq
              subst hBodyChildren
              split at success
              next argGenerator argPayload argChildren =>
              split at success
              · next hVar =>
                  subst hVar
                  split at success
                  · next boundProof hPayloadEq =>
                      have hPayload :
                          argPayload = (⟨0, boundProof⟩ : Fin (scope + 1)) := hPayloadEq
                      subst hPayload
                      cases argChildren
                      have hWeaken :=
                        RawTerm.strengthen_sound functionChild reduct success
                      subst hWeaken
                      exact Step.eta.etaLam domainAnn reduct
                  · next tailIndex boundProof hPayloadEq => cases success
              · cases success
          · cases success
      · split at success
        · next hPair =>
            subst hPair
            split at success
            next firstChild secondChild hChildrenEq =>
            have hChildren :
                children = .childCons firstChild (.childCons secondChild .childNil) :=
              hChildrenEq
            subst hChildren
            split at success
            next firstGenerator firstPayload firstChildren
              secondGenerator secondPayload secondChildren =>
            split at success
            · next hFst =>
                subst hFst
                split at success
                · next hSnd =>
                    subst hSnd
                    split at success
                    next fstPayloadTerm hFstChildrenEq =>
                    have hFstChildren :
                        firstChildren = .childCons fstPayloadTerm .childNil := hFstChildrenEq
                    subst hFstChildren
                    split at success
                    next sndPayloadTerm hSndChildrenEq =>
                    have hSndChildren :
                        secondChildren = .childCons sndPayloadTerm .childNil := hSndChildrenEq
                    subst hSndChildren
                    split at success
                    · next hSamePayload =>
                        subst hSamePayload
                        cases success
                        exact Step.eta.etaPair reduct
                    · cases success
                · cases success
            · cases success
        · split at success
          · next hPathLam =>
              subst hPathLam
              split at success
              next body hChildrenEq =>
              have hChildren : children = .childCons body .childNil := hChildrenEq
              subst hChildren
              split at success
              next bodyGenerator bodyPayload bodyChildren =>
              split at success
              · next hPathApp =>
                  subst hPathApp
                  split at success
                  next functionChild argumentChild hBodyChildrenEq =>
                  have hBodyChildren :
                      bodyChildren =
                        .childCons functionChild (.childCons argumentChild .childNil) :=
                    hBodyChildrenEq
                  subst hBodyChildren
                  split at success
                  next argGenerator argPayload argChildren =>
                  split at success
                  · next hVar =>
                      subst hVar
                      split at success
                      · next boundProof hPayloadEq =>
                          have hPayload :
                              argPayload = (⟨0, boundProof⟩ : Fin (scope + 1)) := hPayloadEq
                          subst hPayload
                          cases argChildren
                          have hWeaken :=
                            RawTerm.strengthen_sound functionChild reduct success
                          subst hWeaken
                          exact Step.eta.etaPathLam reduct
                      · next tailIndex boundProof hPayloadEq => cases success
                  · cases success
              · cases success
          · split at success
            · next hModIntro =>
                subst hModIntro
                split at success
                next innerChild hChildrenEq =>
                have hChildren : children = .childCons innerChild .childNil := hChildrenEq
                subst hChildren
                split at success
                next innerGenerator innerPayload innerChildren =>
                split at success
                · next hModElim =>
                    subst hModElim
                    split at success
                    next modalTerm hInnerChildrenEq =>
                    have hInnerChildren :
                        innerChildren = .childCons modalTerm .childNil := hInnerChildrenEq
                    subst hInnerChildren
                    cases success
                    exact Step.eta.etaModIntro reduct
                · cases success
            · split at success
              · next hGlueIntro =>
                  subst hGlueIntro
                  split at success
                  next firstChild secondChild hChildrenEq =>
                  have hChildren :
                      children = .childCons firstChild (.childCons secondChild .childNil) :=
                    hChildrenEq
                  subst hChildren
                  split at success
                  next firstGenerator firstPayload firstChildren =>
                  split at success
                  · next hGlueElim =>
                      subst hGlueElim
                      split at success
                      next gluedTerm hGlueChildrenEq =>
                      have hGlueChildren :
                          firstChildren = .childCons gluedTerm .childNil := hGlueChildrenEq
                      subst hGlueChildren
                      split at success
                      · next hSameGlued =>
                          subst hSameGlued
                          cases success
                          exact Step.eta.etaGlueIntro reduct
                      · cases success
                  · cases success
              · cases success

/-! ## The layered βη one-step reducer -/

/-- **The βη one-step reducer**: fire β/ι first (the shipped leftmost-outermost `reduceOnce`),
then the root η-firer on β/ι-normal terms. -/
def RawTerm.reduceOnceBetaEta {scope : Nat} (term : RawTerm scope) : Option (RawTerm scope) :=
  match RawTerm.reduceOnce term with
  | some reduct => some reduct
  | none => term.fireRootEtaRedex?

/-- **The βη reducer fires only real `Step.betaEta` steps** — β/ι firings through
`reduceOnce_sound`, η firings through `fireRootEtaRedex?_sound`. -/
theorem RawTerm.reduceOnceBetaEta_sound {scope : Nat} {term reduct : RawTerm scope}
    (success : term.reduceOnceBetaEta = some reduct) :
    Step.betaEta term reduct := by
  unfold RawTerm.reduceOnceBetaEta at success
  split at success
  · next betaReduct hBeta =>
      cases success
      exact Or.inl (RawTerm.reduceOnce_sound hBeta)
  · exact Or.inr (RawTerm.fireRootEtaRedex?_sound success)

/-- **The βη reducer halts exactly at βη-normal forms**: `none` means no β/ι step ANYWHERE
(`reduceOnce_complete` — normal forms block steps) and no η step (root-only, via
`fireRootEtaRedex?_complete`) — so no `Step.betaEta` step at all. -/
theorem RawTerm.reduceOnceBetaEta_complete {scope : Nat} {term : RawTerm scope}
    (halted : term.reduceOnceBetaEta = none) :
    ∀ reduct : RawTerm scope, ¬ Step.betaEta term reduct := by
  intro reduct step
  unfold RawTerm.reduceOnceBetaEta at halted
  split at halted
  · next betaReduct hBeta => cases halted
  · next hBetaNone =>
      cases step with
      | inl betaStep =>
          exact RawTerm.isStepNormalForm_blocks_step
            (RawTerm.reduceOnce_complete hBetaNone) reduct betaStep
      | inr etaStep =>
          exact RawTerm.fireRootEtaRedex?_complete halted reduct etaStep

end FX1Poly.Core
