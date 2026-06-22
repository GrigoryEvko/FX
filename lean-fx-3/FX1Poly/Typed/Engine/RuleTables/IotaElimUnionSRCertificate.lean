import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionBetaRedexSubjectReduction
import FX1Poly.Typed.Engine.RuleTables.IotaElimTypedLink

/-! # FX1Poly/Typed/IotaElimUnionSRCertificate — TYTAB-2 capstone: the decidable bundle ι-subject-reduction
    certificate.

This file is the capstone of the TYTAB-2 arc: it pairs the DECIDABLE static<->operational coherence of
the unified `elimRuleOf` / `introRuleOf` bundle with the unified bundle ι-subject-reduction soundness over
the native union judgment `HasTypeUnion`, and records exactly which rows discharge unconditionally and
which route to their named residual.  Three deliverables:

  1. **The decidable coherence certificate** `WfIotaElimSRTable` — a `Prop` structure whose every field is a
     `<Bool check> = true` fold over `iotaRuleTable`, re-based onto the UNIFIED bundle (`elimRuleOf` /
     `introRuleOf`, NOT the legacy `elimRuleDescOf` / `generalElimRuleOf` / `introRuleDescOf` /
     `gradedIntroRuleOf`).  Each field closes by `rfl`; the certificate RE-DECIDES whenever either table
     grows.  This is the DECIDABLE half — the static typing tables and the operational ι table name the
     SAME generators in the SAME slots.

  2. **The unified bundle soundness theorem** `HasTypeUnion.bundleIotaRowSubjectReduction` — the IOTA-T7
     generalization onto the union judgment.  Quantified over an arbitrary ι row `rule ∈ iotaRuleTable`
     whose `elimRuleOf rule.elimGenerator = some elimRule` and a firing on a union-typed redex cell, it
     concludes the reduct is union-typed at a Conv-equal classifier — OBLIGATION-FREE (the per-row deferred
     reduct-typing parameter is RETIRED; the redex typing plus `WfContextUnion` suffice).  Proved by
     `cases`-dispatch on which ι row it is, routing EACH row to its shipped `unionSubjectReduction*` theorem.
     The four reserved-head rows (`gen_idStrictRec` / `gen_quotRec` / `gen_quotElim` / `gen_truncRec` /
     `gen_ungel`) have NO `elimRuleOf` entry and are excluded by the `some` hypothesis.

  3. **The coverage / witness record** `WfIotaElimSRCoverage` — enumerates that the certificate holds
     (`rfl`) and that the soundness theorem types every routed reduct; an inhabitant certifies the certified
     set cannot silently shrink.

## HONESTY — ALL seventeen reducing rows are now UNCONDITIONAL (TYTAB-2 SRINV)

The nine branch-selection / projection rows ARE unconditional.  The four app-chain selectors
(optionMatchSome, eitherMatchInl/Inr, listElimCons) are unconditional over `WfContextUnion` (W5): the former
`UnionElementReclassifies` oracle is RETIRED, because the element-type universe witness the `conv` arm needs
is DERIVED from the scrutinee's data-code validity (the now-unconditional `HasTypeUnion.classifierIsType`
over `WfContextUnion`, Route A, plus the element-leg head inversions `invertAtOptionCodeHeadElement` /
`invertAtListCodeHeadElement` / `eitherComponents_ofValidity`).  The four binder-substituting rows (β,
endpoint-β, natElimSucc, natRecSucc) are NOW discharged in place too (SRINV): the union REDEX inversions
`invertAtAppHead` / `invertAtPathAppHead` / `invertAtNatElim{,Rec}HeadAllPremises` are SHIPPED, so the
`unionSubjectReduction{Beta,EndpointBeta,NatElimSucc,NatRecSucc}FromRedex` closers feed the shipped per-row
theorems (binder descent `subst0WithUnionImage` / `substPairNonDependentUnionImages`, cumulative former
`unionCumulativeFormerCloses`, wave U3) from the redex typing ALONE.  So the per-row
`SubjectReductionObligation` — and the `UnionClassifierRespectsConv` (VAL-2) `Prop` it routed through — are
BOTH retired: there is no residual.  The sole remaining hypothesis is the `WfContextUnion` presupposition
(tracked under TYTAB-2-WFCTX #1696).

## Zero-axiom

The `= true := rfl` gates are propext-clean Bool folds; the dispatch is `cases` on `List.Mem` +
`Generator.noConfusion` (the `iotaRowAtAppIsBeta` recipe) routed to shipped theorems.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditIotaElimUnionSRCertificate.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## (1) The decidable static<->operational coherence certificate (the UNIFIED bundle)

NOTE — an honest divergence from the legacy `iotaRowCoheresWith` "slot 0" check.  The legacy gates
`typedElimIotaRowsCohere` / `gradedElimIotaRowsCohere` pinned the eliminated child to slot 0 because their
typed-eliminator tables covered ONLY `gen_app` / `gen_pathApp`, whose eliminated child IS slot 0.  The
UNIFIED `elimRuleOf` covers all eleven eliminators, and the recursive / match eliminators scrutinize at the
LAST child (slot 3 for the 4-ary `boolElim` / `natElim` / `natRec` / `listElim` / `optionMatch` /
`eitherMatch`, slot 2 for `idJ`), NOT slot 0.  So the literal slot-0 check FAILS on the unified bundle.  The
correct unified coherence is slot-AGNOSTIC: every ι row whose eliminator carries an `elimRuleOf` row
scrutinizes a SINGLE constructor head that carries an `introRuleOf` row — the eliminated child is a typed
introducer, wherever it sits.  This is what `iotaRowCoheresWithBundle` checks, and it closes by `rfl`. -/

/-- Does ONE ι row cohere with the UNIFIED eliminator / introducer bundle?  If the row's eliminator carries
an `elimRuleOf` row, the row must have a SINGLE scrutinee whose head carries an `introRuleOf` row (the
eliminated child is a typed introducer — at whatever slot the row declares).  Rows at untyped (reserved)
eliminators are unconstrained.  The slot-agnostic adaptation of `iotaRowCoheresWith` to the unified bundle
(the slot-0 hardcoding the legacy gate could afford with only `gen_app` typed no longer holds). -/
def iotaRowCoheresWithBundle (rule : IotaRuleDesc) : Bool :=
  if (elimRuleOf rule.elimGenerator).isSome then
    match rule.scrutinees with
    | [] => false
    | spec :: [] => (introRuleOf spec.head).isSome
    | _ :: _ :: _ => false
  else true

/-- **★ The decidable well-formed-ι-elim-SR-table predicate (the UNIFIED bundle).**  Two fields, each a
`<Bool check> = true` fold over `iotaRuleTable`:

  * `elimIntroCohere` — every ι row whose eliminator carries an `elimRuleOf` row scrutinizes an
    `introRuleOf`-carrying introducer (the static typing tables and the operational ι table name the same
    generators; the eliminated child is the corresponding constructor);
  * `elimDomainCovered` — every ι row whose `elimGenerator` carries an `elimRuleOf` row is exactly a row
    whose `elimRuleOf` is present (the `elimRuleOf` domain is the typed eliminator heads, so no reducing
    row at a typed eliminator escapes the SR dispatch).

Both close by `rfl`; the certificate RE-DECIDES whenever either table grows — the permanent audit guard for
the static<->operational link onto the unified bundle. -/
structure WfIotaElimSRTable : Prop where
  /-- Every ι row coheres with the unified elim/intro bundle (typed-eliminator rows scrutinize typed
  introducers). -/
  elimIntroCohere : listForall iotaRowCoheresWithBundle iotaRuleTable = true
  /-- Every ι row at a unified-eliminator head names that head's `elimRuleOf` row (the operational table's
  eliminator heads are a SUBSET of the static typing table's — no reducing row at a typed eliminator
  escapes the SR dispatch). -/
  elimDomainCovered :
    listForall
      (fun rule =>
        match elimRuleOf rule.elimGenerator with
        | some _ => (elimRuleOf rule.elimGenerator).isSome
        | none => true)
      iotaRuleTable = true

/-- **★ The canonical certificate.**  Every field closes by `rfl`-decidable enumeration over the 22-row ι
table — the decidable half of the TYTAB-2 capstone. -/
theorem iotaRuleTable_elimSRCertified : WfIotaElimSRTable :=
  { elimIntroCohere := rfl
    elimDomainCovered := rfl }

/-! ## (2) The unified bundle soundness theorem — OBLIGATION-FREE (TYTAB-2 SRINV)

The per-row `SubjectReductionObligation` is RETIRED.  Every one of the seventeen reducing rows now
discharges from the redex typing plus `WfContextUnion` ALONE — the soundness theorem takes NO deferred
reduct-typing parameter.  The bridge is burned in three steps, all shipped:

  * the NINE branch-selection / projection rows (boolElim true/false, natElimZero, natRecZero, listElimNil,
    optionMatchNone, idJRefl, fstPair, sndPair) discharge from the redex typing alone;
  * the FOUR select-then-apply rows (optionMatchSome, eitherMatchInl/Inr, listElimCons) are unconditional
    over `WfContextUnion` (TYTAB-2 W5 — the element-type universe witness is derived from the scrutinee's
    data-code validity via the parameter-free `HasTypeUnion.classifierIsType`, retiring the former
    `UnionElementReclassifies` oracle);
  * the FOUR genuinely-substituting rows (β `gen_app`, endpoint-β `gen_pathApp`, natElimSucc, natRecSucc)
    are now discharged IN PLACE by their union REDEX inversions (TYTAB-2 SRINV — `invertAtAppHead` /
    `invertAtPathAppHead` / `invertAtNatElim{,Rec}HeadAllPremises` + the `unionSubjectReduction*FromRedex`
    closers; the binder descent `subst0WithUnionImage` / `substPairNonDependentUnionImages` and the
    cumulative former `unionCumulativeFormerCloses` were already shipped in wave U3).

So every reducing row's subject reduction is derivable from its elim row alone, decidably — there is no
residual.  The `WfContextUnion` presupposition is the only remaining hypothesis (tracked under #1696). -/

/-- **★ The unified bundle ι-subject-reduction soundness theorem (IOTA-T7 over the native union) — fully
unconditional (TYTAB-2 SRINV).**

For an arbitrary ι row `rule ∈ iotaRuleTable` whose `elimGenerator` carries an `elimRuleOf` row (so the row
is one of the seventeen reducing rows at a typed eliminator — the reserved heads are excluded), a firing on
a union-typed redex cell, and the union well-formedness `WfContextUnion`, the reduct is union-typed at a
Conv-equal classifier.  NO per-row obligation — the deferred reduct-typing parameter is RETIRED; every
reducing row discharges from `typed` plus `wellFormed` alone.

Proved by `cases`-dispatch on the 22-row membership (the `iotaRowAtAppIsBeta` recipe): each reducing row's
firing inversion (`*RowFiringToIotaHead` / `betaRowFiringToHeadStep` / `*RowFiringPinsRedex`) pins the redex
cell shape, after which `typed` matches the shipped `unionSubjectReduction*` theorem.  The nine
branch-selection / projection rows discharge from the redex typing alone; the FOUR app-chain selectors
(optionMatchSome / eitherMatchInl/Inr / listElimCons) discharge over `wellFormed` (TYTAB-2 W5 — the shipped
row theorems derive the element-type universe witness from the scrutinee's data-code validity); and the FOUR
substituting rows (β `gen_app`, endpoint-β `gen_pathApp`, natElimSucc, natRecSucc) discharge through their
union REDEX inversions (TYTAB-2 SRINV — `unionSubjectReduction{Beta,EndpointBeta,NatElimSucc,NatRecSucc}`
`FromRedex`).  The reserved-head rows die on `elimRuleOf … = none` vs the `some` hypothesis. -/
theorem HasTypeUnion.bundleIotaRowSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    {elimRule : ElimRule}
    (isTypedElim : elimRuleOf rule.elimGenerator = some elimRule)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (.mkGen rule.elimGenerator elimPayload spine) classifier)
    (wellFormed : WfContextUnion context) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  -- dispatch on the 22 rows; reserved heads die on `elimRuleOf … = none`
  cases isRow with
  | head =>
      -- betaIotaRow (gen_app): UNCONDITIONAL — the app-head inversion (TYTAB-2 SRINV) pins the redex shape,
      -- then `unionSubjectReductionBetaFromRedex` types the β reduct.  No obligation consumed.
      obtain ⟨betaDomain, betaBody, betaArgument, redexShape, reductShape⟩ :=
        betaRowFiringPinsRedex elimPayload fires
      rw [redexShape] at typed
      rw [reductShape]
      exact unionSubjectReductionBetaFromRedex typed
  | tail _ isRow => cases isRow with
    | head =>
        -- boolTrueIotaRow (gen_boolElim): unconditional then-branch
        cases boolTrueRowFiringToIotaHead elimPayload fires with
        | iotaBoolTrue =>
            exact ⟨_, (unionSubjectReductionBoolElimTrue typed).2.1,
              (unionSubjectReductionBoolElimTrue typed).2.2⟩
        | iotaBoolFalse =>
            exact ⟨_, (unionSubjectReductionBoolElimFalse typed).2.1,
              (unionSubjectReductionBoolElimFalse typed).2.2⟩
    | tail _ isRow => cases isRow with
      | head =>
          -- boolFalseIotaRow (gen_boolElim)
          cases boolFalseRowFiringToIotaHead elimPayload fires with
          | iotaBoolTrue =>
              exact ⟨_, (unionSubjectReductionBoolElimTrue typed).2.1,
                (unionSubjectReductionBoolElimTrue typed).2.2⟩
          | iotaBoolFalse =>
              exact ⟨_, (unionSubjectReductionBoolElimFalse typed).2.1,
                (unionSubjectReductionBoolElimFalse typed).2.2⟩
      | tail _ isRow => cases isRow with
        | head =>
            -- fstPairIotaRow (gen_fst): unconditional projection
            cases fstPairRowFiringToIotaHead elimPayload fires with
            | iotaFstPair => exact unionSubjectReductionFstPair typed |>.2
        | tail _ isRow => cases isRow with
          | head =>
              -- sndPairIotaRow (gen_snd)
              cases sndPairRowFiringToIotaHead elimPayload fires with
              | iotaSndPair => exact unionSubjectReductionSndPair typed |>.2
          | tail _ isRow => cases isRow with
            | head =>
                -- natElimZeroIotaRow (gen_natElim): zero (unconditional) | succ (deferred)
                cases natElimZeroRowFiringToIotaHead elimPayload fires with
                | iotaNatElimZero =>
                    exact ⟨classifier, (unionSubjectReductionNatElimZero typed).2, Conv.refl classifier⟩
                | iotaNatElimSucc =>
                    exact unionSubjectReductionNatElimSuccFromRedex typed
            | tail _ isRow => cases isRow with
              | head =>
                  -- natRecZeroIotaRow (gen_natRec)
                  cases natRecZeroRowFiringToIotaHead elimPayload fires with
                  | iotaNatRecZero =>
                      exact ⟨classifier, (unionSubjectReductionNatRecZero typed).2, Conv.refl classifier⟩
                  | iotaNatRecSucc =>
                      exact unionSubjectReductionNatRecSuccFromRedex typed
              | tail _ isRow => cases isRow with
                | head =>
                    -- natElimSuccIotaRow (gen_natElim)
                    cases natElimSuccRowFiringToIotaHead elimPayload fires with
                    | iotaNatElimZero =>
                        exact ⟨classifier, (unionSubjectReductionNatElimZero typed).2,
                          Conv.refl classifier⟩
                    | iotaNatElimSucc =>
                        exact unionSubjectReductionNatElimSuccFromRedex typed
                | tail _ isRow => cases isRow with
                  | head =>
                      -- natRecSuccIotaRow (gen_natRec)
                      cases natRecSuccRowFiringToIotaHead elimPayload fires with
                      | iotaNatRecZero =>
                          exact ⟨classifier, (unionSubjectReductionNatRecZero typed).2,
                            Conv.refl classifier⟩
                      | iotaNatRecSucc =>
                          exact unionSubjectReductionNatRecSuccFromRedex typed
                  | tail _ isRow => cases isRow with
                    | head =>
                        -- listElimNilIotaRow (gen_listElim): nil (unconditional) | cons (reclassify)
                        cases listElimNilRowFiringToIotaHead elimPayload fires with
                        | iotaListElimNil => exact (unionSubjectReductionListElimNil typed).2
                        | iotaListElimCons =>
                            exact (unionSubjectReductionListElimCons typed wellFormed).2
                    | tail _ isRow => cases isRow with
                      | head =>
                          -- listElimConsIotaRow (gen_listElim)
                          cases listElimConsRowFiringToIotaHead elimPayload fires with
                          | iotaListElimNil => exact (unionSubjectReductionListElimNil typed).2
                          | iotaListElimCons =>
                              exact (unionSubjectReductionListElimCons typed wellFormed).2
                      | tail _ isRow => cases isRow with
                        | head =>
                            -- optionMatchNoneIotaRow (gen_optionMatch): none | some (reclassify)
                            cases optionMatchNoneRowFiringToIotaHead elimPayload fires with
                            | iotaOptionMatchNone => exact (unionSubjectReductionOptionMatchNone typed).2
                            | iotaOptionMatchSome =>
                                exact (unionSubjectReductionOptionMatchSome typed wellFormed).2
                        | tail _ isRow => cases isRow with
                          | head =>
                              -- optionMatchSomeIotaRow (gen_optionMatch)
                              cases optionMatchSomeRowFiringToIotaHead elimPayload fires with
                              | iotaOptionMatchNone =>
                                  exact (unionSubjectReductionOptionMatchNone typed).2
                              | iotaOptionMatchSome =>
                                  exact (unionSubjectReductionOptionMatchSome typed wellFormed).2
                          | tail _ isRow => cases isRow with
                            | head =>
                                -- eitherMatchInlIotaRow (gen_eitherMatch): inl | inr (reclassify)
                                cases eitherMatchInlRowFiringToIotaHead elimPayload fires with
                                | iotaEitherMatchInl =>
                                    exact (unionSubjectReductionEitherMatchInl typed wellFormed).2
                                | iotaEitherMatchInr =>
                                    exact (unionSubjectReductionEitherMatchInr typed wellFormed).2
                            | tail _ isRow => cases isRow with
                              | head =>
                                  -- eitherMatchInrIotaRow (gen_eitherMatch)
                                  cases eitherMatchInrRowFiringToIotaHead elimPayload fires with
                                  | iotaEitherMatchInl =>
                                      exact (unionSubjectReductionEitherMatchInl typed wellFormed).2
                                  | iotaEitherMatchInr =>
                                      exact (unionSubjectReductionEitherMatchInr typed wellFormed).2
                              | tail _ isRow => cases isRow with
                                | head =>
                                    -- idJReflIotaRow (gen_idJ): unconditional
                                    cases idJReflRowFiringToIotaHead elimPayload fires with
                                    | iotaIdJRefl =>
                                        exact ⟨classifier, (unionSubjectReductionIdJRefl typed).2,
                                          Conv.refl classifier⟩
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      -- idStrictRecReflIotaRow (gen_idStrictRec): reserved, no elimRuleOf
                                      exact absurd isTypedElim (by intro hit; cases hit)
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        -- pathBetaIotaRow (gen_pathApp): UNCONDITIONAL — the pathApp-head
                                        -- inversion (TYTAB-2 SRINV) pins the redex shape, then
                                        -- `unionSubjectReductionEndpointBetaFromRedex` types the reduct.
                                        obtain ⟨pathBetaBody, pathBetaEndpoint, redexShape, reductShape⟩ :=
                                          pathBetaRowFiringPinsRedex elimPayload fires
                                        rw [redexShape] at typed
                                        rw [reductShape]
                                        exact unionSubjectReductionEndpointBetaFromRedex typed
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          -- quotRecMkIotaRow (gen_quotRec): reserved
                                          exact absurd isTypedElim (by intro hit; cases hit)
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            -- quotElimMkIotaRow (gen_quotElim): reserved
                                            exact absurd isTypedElim (by intro hit; cases hit)
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              -- truncRecIntroIotaRow (gen_truncRec): reserved
                                              exact absurd isTypedElim (by intro hit; cases hit)
                                          | tail _ isRow => cases isRow with
                                            | head =>
                                                -- gelBetaIotaRow (gen_ungel): reserved
                                                exact absurd isTypedElim (by intro hit; cases hit)
                                            | tail _ isRow => cases isRow

/-- **★ The single bundle subject-reduction interface (TYTAB-2 SRINV deliverable) — OBLIGATION-FREE.**  THE
one entry point the kernel uses for ι-subject-reduction over the native union: given a union typing of an
ι-redex cell, the firing, and the union well-formedness `WfContextUnion`, the reduct is union-typed at a
Conv-equal classifier.  Thin delegate of `bundleIotaRowSubjectReduction`; carries NO reclassification oracle
and NO per-row obligation — all seventeen reducing rows are unconditional.  The four app-chain selectors
discharge over `wellFormed` (W5); the four substituting rows (β / endpoint-β / natElimSucc / natRecSucc)
discharge through their now-shipped union REDEX inversions (`invertAtAppHead` / `invertAtPathAppHead` /
`invertAtNatElim{,Rec}HeadAllPremises`, SRINV).  The decidable static<->operational companion is
`iotaRuleTable_elimSRCertified : WfIotaElimSRTable` (re-checked by `rfl`); the two are paired in
`WfIotaElimSRCoverage`.  The only remaining hypothesis is the `WfContextUnion` presupposition (#1696). -/
theorem HasTypeUnion.subjectReductionOnIotaRedex {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    {elimRule : ElimRule}
    (isTypedElim : elimRuleOf rule.elimGenerator = some elimRule)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (.mkGen rule.elimGenerator elimPayload spine) classifier)
    (wellFormed : WfContextUnion context) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧
      Conv pinnedClassifier classifier :=
  HasTypeUnion.bundleIotaRowSubjectReduction isRow isTypedElim fires typed wellFormed

/-! ## (3) The coverage / witness record -/

/-- **★ The coverage / witness record (OBLIGATION-FREE).**  An inhabitant certifies: the decidable coherence
certificate holds (`certified`); and the soundness theorem types every routed reduct (`reductTyped`) from
the redex typing plus `WfContextUnion` alone — no per-row obligation, since the deferred-typing parameter is
retired.  Because every field is inhabited by a shipped object, the certified set can NOT silently shrink. -/
structure WfIotaElimSRCoverage (profile : PolyProfile) : Prop where
  /-- The decidable coherence certificate holds. -/
  certified : WfIotaElimSRTable
  /-- The soundness theorem types every routed reduct from `typed` + `wellFormed` alone (no obligation). -/
  reductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    {elimRule : ElimRule} (isTypedElim : elimRuleOf rule.elimGenerator = some elimRule)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (.mkGen rule.elimGenerator elimPayload spine) classifier)
    (wellFormed : WfContextUnion context),
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier

/-- **★ The coverage witness** — inhabited by the shipped certificate + soundness theorem, so the certified
set cannot silently shrink.  The `reductTyped` field IS the (now obligation-free) soundness theorem. -/
theorem wfIotaElimSRCoverageWitness {profile : PolyProfile} : WfIotaElimSRCoverage profile where
  certified := iotaRuleTable_elimSRCertified
  reductTyped := by
    intro _scope _context _rule isRow _elimRule isTypedElim _elimPayload _spine _reduct fires
      _classifier typed wellFormed
    exact HasTypeUnion.bundleIotaRowSubjectReduction isRow isTypedElim fires typed wellFormed

end FX1Poly.Typed
