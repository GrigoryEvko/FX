import FX1Poly.Core.EtaStrengthenEquivariance
import FX1Poly.Core.StepEtaTableBackward
import FX1Poly.Core.StepOverTable
import FX1Poly.Core.RawTermFoldNonVarCommute

/-! # EtaContractionNaturality — ETA-T2: the firing naturality

`contractsOn?` commutes with substitution: a contracting intro cell
keeps contracting after any substitution, to the substituted core.  The
pieces, each generic over the schema:

* `childAtShift?_subst` — the shift-checked lookup is natural (the fold
  engine lifts per-child by exactly the looked-up shift);
* `observerFreshVarsHold_subst` — fresh-variable patterns persist:
  binder-lifted substitutions fix the fresh block
  (`iterateLiftRaw_RawTermSubst_fixesFreshVar`), provided the spec's
  fresh indices stay within the binder depth — the `IsScopeSafe`
  obligation a row certifies once;
* `extractCoreFrom?_subst` — one observation's extraction is natural:
  the observer head persists (substitution preserves non-var heads),
  the fresh test persists, and the core strengthens by the ETA-T2 crux
  `strengthenBy?_subst`;
* `contractsOn?_subst` — the full firing is natural: the primary
  observation transports, and DecEq-equal cores STAY equal because
  substitution is a function (`congrArg`).

The non-var observer-head and fresh-bound hypotheses are bundled as
`EtaObservationSpec.IsScopeSafe` / `EtaRuleDesc.IsScopeSafe`; the five
canonical rows certify them by `rfl`-decidable pins (in the relation
closure file).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaContractionNaturality.lean`. -/

namespace FX1Poly.Core

/-! ## The scope-safety obligations -/

/-- One observation's scope-safety: a non-variable observer head (so
substitution preserves it) and fresh indices within the binder depth
(so lifted substitutions fix them). -/
structure EtaObservationSpec.IsScopeSafe
    (spec : EtaObservationSpec) : Prop where
  observerIsNotVar : spec.observerHead ≠ .gen_var
  freshVarsWithinDepth : spec.freshVarSlots.length ≤ spec.binderDepth

/-- A rule's scope-safety: a non-variable intro head and scope-safe
observations. -/
structure EtaRuleDesc.IsScopeSafe (rule : EtaRuleDesc) : Prop where
  introIsNotVar : rule.introGenerator ≠ .gen_var
  observationsAreScopeSafe :
    ∀ spec, spec ∈ rule.observations → spec.IsScopeSafe

/-! ## Lookup naturality -/

/-- The shift-checked lookup is natural in substitution: the fold
engine lifts per-child by the child's own shift, which the successful
lookup pins to the expected shift. -/
theorem RawTermChildren.childAtShift?_subst
    {parentSourceScope parentTargetScope : Nat}
    (someSubstitution : RawTermSubst parentSourceScope parentTargetScope) :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentSourceScope) →
    (slot expectedShift : Nat) →
    {found : RawTerm (parentSourceScope + expectedShift)} →
    RawTermChildren.childAtShift? children slot expectedShift = some found →
    RawTermChildren.childAtShift?
        (children.subst someSubstitution) slot expectedShift
      = some (RawTerm.subst (iterateLiftRaw someSubstitution expectedShift)
          found)
  | _, .childNil, _, _, _, lookupEq => nomatch lookupEq
  | headShift :: _restShifts, .childCons head rest, 0, expectedShift,
      found, lookupEq => by
      by_cases shiftMatches : headShift = expectedShift
      case pos =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_pos shiftMatches] at lookupEq
          have headIsFound : shiftMatches ▸ head = found :=
            Option.some.inj lookupEq
          subst headIsFound
          cases shiftMatches
          have computedSubst :
              RawTermChildren.childAtShift?
                ((RawTermChildren.childCons head rest).subst
                  someSubstitution) 0 headShift
              = (if shiftEq : headShift = headShift then
                  some (shiftEq ▸
                    RawTerm.subst (iterateLiftRaw someSubstitution headShift)
                      head)
                else none) := rfl
          rw [computedSubst, dif_pos rfl]
      case neg =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_neg shiftMatches] at lookupEq
          exact nomatch lookupEq
  | _headShift :: _restShifts, .childCons _head rest, nextSlot + 1,
      expectedShift, found, lookupEq =>
      RawTermChildren.childAtShift?_subst someSubstitution rest nextSlot
        expectedShift lookupEq

/-! ## Fresh-pattern persistence -/

/-- Fresh-variable patterns persist under a binder-lifted substitution:
each observed `var index` with `index` inside the fresh block is fixed
by the lift. -/
theorem observerFreshVarsHold_subst {sourceScope targetScope : Nat}
    {binderDepth : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    {observerShifts : List Nat}
    (observedChildren :
      RawTermChildren observerShifts (sourceScope + binderDepth)) :
    (varSlots : List Nat) → (nextVarIndex : Nat) →
    nextVarIndex + varSlots.length ≤ binderDepth →
    observerFreshVarsHold observedChildren varSlots nextVarIndex = true →
    observerFreshVarsHold
        (observedChildren.subst
          (iterateLiftRaw someSubstitution binderDepth))
        varSlots nextVarIndex
      = true
  | [], _nextVarIndex, _withinDepth, _holds => rfl
  | slot :: restSlots, varIndex, withinDepth, holds => by
      have isFresh : varIndex < binderDepth :=
        Nat.le_trans
          (Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.zero_le restSlots.length)) varIndex)
          withinDepth
      dsimp only [observerFreshVarsHold] at holds
      match lookupEq : observedChildren.childAtShift? slot 0 with
      | none =>
          rw [lookupEq] at holds
          exact nomatch holds
      | some child =>
          rw [lookupEq] at holds
          have sourceBound : varIndex < sourceScope + binderDepth :=
            Nat.lt_of_lt_of_le isFresh (Nat.le_add_left _ _)
          have holdsReduced :
              ((if isInBounds : varIndex < sourceScope + binderDepth then
                  if child
                      = RawTerm.mkGen .gen_var ⟨varIndex, isInBounds⟩
                          .childNil then true
                  else false
                else false)
                && observerFreshVarsHold observedChildren restSlots
                    (varIndex + 1))
              = true := holds
          rw [dif_pos sourceBound] at holdsReduced
          by_cases childEq :
              child = RawTerm.mkGen .gen_var ⟨varIndex, sourceBound⟩
                .childNil
          case neg =>
              rw [if_neg childEq] at holdsReduced
              exact nomatch holdsReduced
          case pos =>
              obtain ⟨_headHolds, restHolds⟩ := andEqTrueSplit holdsReduced
              subst childEq
              -- assemble the substituted check
              have substLookup :=
                RawTermChildren.childAtShift?_subst
                  (iterateLiftRaw someSubstitution binderDepth)
                  observedChildren slot 0 lookupEq
              have targetBound : varIndex < targetScope + binderDepth :=
                Nat.lt_of_lt_of_le isFresh (Nat.le_add_left _ _)
              have substitutedVarIsFixed :
                  RawTerm.subst
                      (iterateLiftRaw
                        (iterateLiftRaw someSubstitution binderDepth) 0)
                      (RawTerm.mkGen .gen_var ⟨varIndex, sourceBound⟩
                        .childNil)
                    = RawTerm.mkGen .gen_var ⟨varIndex, targetBound⟩
                        .childNil :=
                iterateLiftRaw_RawTermSubst_fixesFreshVar someSubstitution
                  binderDepth varIndex sourceBound targetBound isFresh
              dsimp only [observerFreshVarsHold]
              rw [substLookup, substitutedVarIsFixed]
              show ((if isInBounds : varIndex < targetScope + binderDepth then
                  if RawTerm.mkGen .gen_var ⟨varIndex, targetBound⟩
                        .childNil
                      = RawTerm.mkGen .gen_var ⟨varIndex, isInBounds⟩
                          .childNil then true
                  else false
                else false)
                && observerFreshVarsHold
                    (observedChildren.subst
                      (iterateLiftRaw someSubstitution binderDepth))
                    restSlots (varIndex + 1))
                = true
              rw [dif_pos targetBound, if_pos rfl]
              have restWithinDepth :
                  (varIndex + 1) + restSlots.length ≤ binderDepth := by
                rw [Nat.add_assoc, Nat.add_comm 1 restSlots.length]
                exact withinDepth
              show observerFreshVarsHold
                  (observedChildren.subst
                    (iterateLiftRaw someSubstitution binderDepth))
                  restSlots (varIndex + 1)
                = true
              exact observerFreshVarsHold_subst someSubstitution
                observedChildren restSlots (varIndex + 1) restWithinDepth
                restHolds

/-! ## Observation naturality -/

/-- One observation's core extraction is natural in substitution. -/
theorem EtaObservationSpec.extractCoreFrom?_subst
    (spec : EtaObservationSpec) (isScopeSafe : spec.IsScopeSafe)
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts sourceScope}
    {core : RawTerm sourceScope}
    (success : spec.extractCoreFrom? introChildren = some core) :
    spec.extractCoreFrom? (introChildren.subst someSubstitution)
      = some (RawTerm.subst someSubstitution core) := by
  obtain ⟨observedPayload, observedChildren, lookupEq, freshHolds,
    coreExtract⟩ :=
    EtaObservationSpec.extractCoreFrom?_someInversion spec success
  have substLookup :=
    RawTermChildren.childAtShift?_subst someSubstitution introChildren
      spec.introChildSlot spec.binderDepth lookupEq
  -- the substituted observer cell keeps its head (non-var)
  rw [RawTerm.subst_mkGen_of_ne_var
    (iterateLiftRaw someSubstitution spec.binderDepth)
    isScopeSafe.observerIsNotVar observedPayload observedChildren]
    at substLookup
  -- core lookup naturality inside the observer
  match coreLookupEq :
      observedChildren.childAtShift? spec.coreSlot 0 with
  | none =>
      rw [coreLookupEq] at coreExtract
      exact nomatch coreExtract
  | some rawCore =>
      rw [coreLookupEq] at coreExtract
      have strengthenedRaw :
          RawTerm.strengthenBy? spec.binderDepth rawCore = some core :=
        coreExtract
      have substCoreLookup :=
        RawTermChildren.childAtShift?_subst
          (iterateLiftRaw someSubstitution spec.binderDepth)
          observedChildren spec.coreSlot 0 coreLookupEq
      have substStrengthened :=
        RawTerm.strengthenBy?_subst someSubstitution spec.binderDepth
          rawCore core strengthenedRaw
      -- assemble the substituted walk
      dsimp only [EtaObservationSpec.extractCoreFrom?]
      rw [substLookup]
      show (if spec.observerHead = spec.observerHead then
          (if observerFreshVarsHold
              (observedChildren.subst
                (iterateLiftRaw someSubstitution spec.binderDepth))
              spec.freshVarSlots 0 = true then
            ((observedChildren.subst
                (iterateLiftRaw someSubstitution spec.binderDepth))
              |>.childAtShift? spec.coreSlot 0).bind
              (fun rawCoreTerm =>
                RawTerm.strengthenBy? spec.binderDepth rawCoreTerm)
          else none)
        else none)
        = some (RawTerm.subst someSubstitution core)
      rw [if_pos rfl,
        if_pos (observerFreshVarsHold_subst someSubstitution
          observedChildren spec.freshVarSlots 0
          (by rw [Nat.zero_add]; exact isScopeSafe.freshVarsWithinDepth)
          freshHolds),
        substCoreLookup]
      show RawTerm.strengthenBy? spec.binderDepth
          (RawTerm.subst
            (iterateLiftRaw
              (iterateLiftRaw someSubstitution spec.binderDepth) 0)
            rawCore)
        = some (RawTerm.subst someSubstitution core)
      exact substStrengthened

/-! ## Firing naturality -/

/-- The agreement gate is natural: each remaining observation keeps
extracting, to the SUBSTITUTED shared core (substitution is a function,
so decidably-equal cores stay equal). -/
theorem etaObservationsAgree_subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts sourceScope}
    {core : RawTerm sourceScope} :
    (specs : List EtaObservationSpec) →
    (specsAreScopeSafe : ∀ spec, spec ∈ specs → spec.IsScopeSafe) →
    etaObservationsAgree introChildren core specs = true →
    etaObservationsAgree (introChildren.subst someSubstitution)
        (RawTerm.subst someSubstitution core) specs
      = true
  | [], _, _ => rfl
  | spec :: restSpecs, specsAreScopeSafe, agree => by
      dsimp only [etaObservationsAgree] at agree
      match extractEq : spec.extractCoreFrom? introChildren with
      | none =>
          rw [extractEq] at agree
          exact nomatch agree
      | some otherCore =>
          rw [extractEq] at agree
          have agreeReduced :
              ((if otherCore = core then true else false)
                && etaObservationsAgree introChildren core restSpecs)
              = true := agree
          by_cases otherEq : otherCore = core
          case neg =>
              rw [if_neg otherEq] at agreeReduced
              exact nomatch agreeReduced
          case pos =>
              obtain ⟨_headAgree, restAgree⟩ := andEqTrueSplit agreeReduced
              subst otherEq
              have substExtract :=
                spec.extractCoreFrom?_subst
                  (specsAreScopeSafe spec (.head _)) someSubstitution
                  extractEq
              dsimp only [etaObservationsAgree]
              rw [substExtract]
              show ((if RawTerm.subst someSubstitution otherCore
                    = RawTerm.subst someSubstitution otherCore then true
                  else false)
                && etaObservationsAgree
                    (introChildren.subst someSubstitution)
                    (RawTerm.subst someSubstitution otherCore) restSpecs)
                = true
              rw [if_pos rfl]
              show etaObservationsAgree
                  (introChildren.subst someSubstitution)
                  (RawTerm.subst someSubstitution otherCore) restSpecs
                = true
              exact etaObservationsAgree_subst someSubstitution restSpecs
                (fun innerSpec isMember =>
                  specsAreScopeSafe innerSpec (.tail _ isMember))
                restAgree

/-- **★ The firing naturality**: a contracting intro cell keeps
contracting after ANY substitution, to the substituted core — the eta
twin of the iota `firesOn?` naturality, generic over every scope-safe
rule. -/
theorem EtaRuleDesc.contractsOn?_subst (rule : EtaRuleDesc)
    (isScopeSafe : rule.IsScopeSafe)
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts sourceScope}
    {core : RawTerm sourceScope}
    (contracts : rule.contractsOn? introChildren = some core) :
    rule.contractsOn? (introChildren.subst someSubstitution)
      = some (RawTerm.subst someSubstitution core) := by
  dsimp only [EtaRuleDesc.contractsOn?] at contracts ⊢
  match specsEq : rule.observations with
  | [] =>
      rw [specsEq] at contracts
      exact nomatch contracts
  | primarySpec :: restSpecs =>
      rw [specsEq] at contracts
      have primaryIsSafe : primarySpec.IsScopeSafe :=
        isScopeSafe.observationsAreScopeSafe primarySpec
          (by rw [specsEq]; exact List.Mem.head _)
      have restAreSafe :
          ∀ spec, spec ∈ restSpecs → spec.IsScopeSafe :=
        fun spec isMember =>
          isScopeSafe.observationsAreScopeSafe spec
            (by rw [specsEq]; exact List.Mem.tail _ isMember)
      have contractsReduced :
          (primarySpec.extractCoreFrom? introChildren).bind
              (fun sharedCore =>
                if etaObservationsAgree introChildren sharedCore
                    restSpecs then some sharedCore
                else none)
            = some core := contracts
      match extractEq : primarySpec.extractCoreFrom? introChildren with
      | none =>
          rw [extractEq] at contractsReduced
          exact nomatch contractsReduced
      | some extractedCore =>
          rw [extractEq] at contractsReduced
          have gateReduced :
              (if etaObservationsAgree introChildren extractedCore
                  restSpecs then some extractedCore
              else none)
                = some core := contractsReduced
          by_cases agreeHolds :
              etaObservationsAgree introChildren extractedCore restSpecs
                = true
          case neg =>
              rw [if_neg agreeHolds] at gateReduced
              exact nomatch gateReduced
          case pos =>
              rw [if_pos agreeHolds] at gateReduced
              have coreIsExtracted : extractedCore = core :=
                Option.some.inj gateReduced
              rw [← coreIsExtracted]
              show (primarySpec.extractCoreFrom?
                  (introChildren.subst someSubstitution)).bind
                  (fun sharedCore =>
                    if etaObservationsAgree
                        (introChildren.subst someSubstitution) sharedCore
                        restSpecs then some sharedCore
                    else none)
                = some (RawTerm.subst someSubstitution extractedCore)
              rw [primarySpec.extractCoreFrom?_subst primaryIsSafe
                someSubstitution extractEq]
              show (if etaObservationsAgree
                  (introChildren.subst someSubstitution)
                  (RawTerm.subst someSubstitution extractedCore)
                  restSpecs then
                some (RawTerm.subst someSubstitution extractedCore)
              else none)
                = some (RawTerm.subst someSubstitution extractedCore)
              rw [if_pos (etaObservationsAgree_subst someSubstitution
                restSpecs restAreSafe agreeHolds)]
