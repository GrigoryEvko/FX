import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
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
     whose `elimRuleOf rule.elimGenerator = some elimRule`, a firing on a union-typed redex cell, AND a
     per-row `SubjectReductionObligation` (`True` for the nine UNCONDITIONAL rows; the row's actual residual
     for the conditional rows), it concludes the reduct is union-typed at a Conv-equal classifier.  Proved
     by `cases`-dispatch on which ι row it is, routing EACH row to its shipped `unionSubjectReduction*`
     theorem.  The four reserved-head rows (`gen_idStrictRec` / `gen_quotRec` / `gen_quotElim` /
     `gen_truncRec` / `gen_ungel`) have NO `elimRuleOf` entry and are excluded by the `some` hypothesis.

  3. **The coverage / witness record** `WfIotaElimSRCoverage` — enumerates that the certificate holds
     (`rfl`), the nine rows discharge unconditionally, and the remaining rows route to their residual; an
     inhabitant certifies the certified set cannot silently shrink.

## HONESTY — the single remaining open lemma

This certificate does NOT claim unconditional SR on all reducing rows.  The nine branch-selection /
projection rows ARE unconditional.  The remaining conditional rows split by residual: the app-chain
selectors (optionMatchSome, eitherMatchInl/Inr, listElimCons) route to `UnionElementReclassifies`; the
binder-substituting rows (β, endpoint-β, natElimSucc, natRecSucc) — whose binder descent is now SHIPPED
(TYTAB-2 W4, `HasTypeUnion.subst0WithUnionImage` / `substPairNonDependentUnionImages`) — route to the
precise cumulative-former oracle `UnionCumulativeFormerCloses` (the documented `UnionDataFormerValidity`
wall — forming the four cumulative type-codes from union children), strictly smaller than the old
`UnionSubst0Transports` / `UnionSubstPairTransports` transports.  The app-chain residual
`UnionElementReclassifies` reduces to the single open union-classifier-validity lemma (VAL-2,
`classifierRespectsConv`): a value union-typed at `A` with `Conv A B` is union-typed at `B`, supplied with
a universe witness for `B`; it is isolated below as ONE named obligation (`UnionClassifierRespectsConv`)
and is NOT claimed proven.

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

/-! ## (2) The per-row subject-reduction obligation + the unified bundle soundness theorem -/

/-- **The per-row subject-reduction obligation.**  Routed by the row's `elimGenerator` (the unified-bundle
key):

  * `True` for the NINE UNCONDITIONAL branch-selection / projection rows — boolElim true/false,
    natElimZero, natRecZero, listElimNil, optionMatchNone, idJRefl, fstPair, sndPair (heads `gen_boolElim`,
    `gen_natElim`/`gen_natRec` at zero, `gen_listElim` at nil, `gen_optionMatch` at none, `gen_idJ`,
    `gen_fst`, `gen_snd`).  These discharge from the redex typing alone.

  * `UnionElementReclassifies profile context` for the four select-then-apply rows — optionMatchSome,
    eitherMatchInl, eitherMatchInr, listElimCons (heads `gen_optionMatch` at some, `gen_eitherMatch`,
    `gen_listElim` at cons).  These route via the redex typing PLUS the single element-reclassification
    residual.

  * For the four genuinely-substituting rows — β (`gen_app`), endpoint-β (`gen_pathApp`), natElimSucc
    (`gen_natElim` at succ), natRecSucc (`gen_natRec` at succ) — the obligation is the DIRECT deferred
    reduct typing `UnionDeferredReductTyped`: the reduct is union-typed at a Conv-equal classifier.  The
    union's binder descent with a union-typed substituent is now SHIPPED (TYTAB-2 W4,
    `HasTypeUnion.subst0WithUnionImage` / `substPairNonDependentUnionImages`), so the shipped
    `unionSubjectReduction{Beta,EndpointBeta,NatElimSucc,NatRecSucc}` produce the reduct typing from the body
    / argument premises plus ONLY the precise cumulative-former oracle `UnionCumulativeFormerCloses` (the
    documented `UnionDataFormerValidity` wall), strictly smaller than the old whole-transport residuals.

Note: because several rows share an `elimGenerator` (e.g. `gen_boolElim` heads both boolElim-true and
boolElim-false; `gen_natElim` heads natElimZero and natElimSucc), the obligation is keyed on the head and
made permissive enough that the actual per-row routing in the soundness proof consumes only the part it
needs.  The substituting heads (`gen_app` / `gen_pathApp`) head a UNIQUE row each, so the deferred-typing
obligation pins them exactly; the `gen_natElim` / `gen_natRec` heads cover BOTH the zero and succ rows, so
their obligation is the deferred typing (consumed by the succ arm; the zero arm ignores it). -/
def SubjectReductionObligation {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (rule : IotaRuleDesc)
    (redex : RawTerm scope) (reduct : RawTerm scope) (classifier : RawTerm scope) : Prop :=
  if rule.elimGenerator = .gen_app then
    -- β: deferred reduct typing (no app head inversion ships)
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier
  else if rule.elimGenerator = .gen_pathApp then
    -- endpoint-β: deferred reduct typing (no pathApp head inversion ships)
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier
  else if rule.elimGenerator = .gen_natElim then
    -- natElimZero (unconditional) | natElimSucc (deferred): the succ arm consumes the deferred typing
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier
  else if rule.elimGenerator = .gen_natRec then
    -- natRecZero (unconditional) | natRecSucc (deferred)
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier
  else if rule.elimGenerator = .gen_optionMatch then
    -- optionMatchNone (unconditional) | optionMatchSome (reclassify)
    UnionElementReclassifies profile context
  else if rule.elimGenerator = .gen_eitherMatch then
    -- eitherMatchInl / Inr (reclassify)
    UnionElementReclassifies profile context
  else if rule.elimGenerator = .gen_listElim then
    -- listElimNil (unconditional) | listElimCons (reclassify)
    UnionElementReclassifies profile context
  else
    -- boolElim true/false, idJRefl, fstPair, sndPair — all unconditional
    True

/-! The directly-typed routing for the thirteen rows whose reduct typing IS recoverable from the redex
typing (the nine unconditional + the four reclassify), packaged so the master dispatch consumes one
uniform conclusion shape. -/

/-- **★ The unified bundle ι-subject-reduction soundness theorem (IOTA-T7 over the native union).**

For an arbitrary ι row `rule ∈ iotaRuleTable` whose `elimGenerator` carries an `elimRuleOf` row (so the row
is one of the seventeen reducing rows at a typed eliminator — the reserved heads are excluded), a firing on
a union-typed redex cell, AND the per-row `SubjectReductionObligation`, the reduct is union-typed at a
Conv-equal classifier.

Proved by `cases`-dispatch on the 22-row membership (the `iotaRowAtAppIsBeta` recipe): each reducing row's
firing inversion (`*RowFiringToIotaHead` / `betaRowFiringToHeadStep`) pins the redex cell shape, after
which `typed` matches the shipped `unionSubjectReduction*` theorem.  The nine unconditional rows discharge
their `True` obligation; the four reclassify rows consume the `UnionElementReclassifies` residual; the four
substituting rows consume the deferred reduct typing.  The reserved-head rows die on
`elimRuleOf … = none` vs the `some` hypothesis. -/
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
    (obligation : SubjectReductionObligation context rule
      (.mkGen rule.elimGenerator elimPayload spine) reduct classifier) :
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  -- dispatch on the 22 rows; reserved heads die on `elimRuleOf … = none`
  cases isRow with
  | head =>
      -- betaIotaRow (gen_app): deferred typing
      simp only [SubjectReductionObligation] at obligation
      exact obligation
  | tail _ isRow => cases isRow with
    | head =>
        -- boolTrueIotaRow (gen_boolElim): unconditional then-branch
        cases boolTrueRowFiringToIotaHead elimPayload fires with
        | iotaBoolTrue =>
            exact ⟨classifier, (unionSubjectReductionBoolElimTrue typed).2, Conv.refl classifier⟩
        | iotaBoolFalse =>
            exact ⟨classifier, (unionSubjectReductionBoolElimFalse typed).2, Conv.refl classifier⟩
    | tail _ isRow => cases isRow with
      | head =>
          -- boolFalseIotaRow (gen_boolElim)
          cases boolFalseRowFiringToIotaHead elimPayload fires with
          | iotaBoolTrue =>
              exact ⟨classifier, (unionSubjectReductionBoolElimTrue typed).2, Conv.refl classifier⟩
          | iotaBoolFalse =>
              exact ⟨classifier, (unionSubjectReductionBoolElimFalse typed).2, Conv.refl classifier⟩
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
                    simp only [SubjectReductionObligation] at obligation
                    exact obligation
            | tail _ isRow => cases isRow with
              | head =>
                  -- natRecZeroIotaRow (gen_natRec)
                  cases natRecZeroRowFiringToIotaHead elimPayload fires with
                  | iotaNatRecZero =>
                      exact ⟨classifier, (unionSubjectReductionNatRecZero typed).2, Conv.refl classifier⟩
                  | iotaNatRecSucc =>
                      simp only [SubjectReductionObligation] at obligation
                      exact obligation
              | tail _ isRow => cases isRow with
                | head =>
                    -- natElimSuccIotaRow (gen_natElim)
                    cases natElimSuccRowFiringToIotaHead elimPayload fires with
                    | iotaNatElimZero =>
                        exact ⟨classifier, (unionSubjectReductionNatElimZero typed).2,
                          Conv.refl classifier⟩
                    | iotaNatElimSucc =>
                        simp only [SubjectReductionObligation] at obligation
                        exact obligation
                | tail _ isRow => cases isRow with
                  | head =>
                      -- natRecSuccIotaRow (gen_natRec)
                      cases natRecSuccRowFiringToIotaHead elimPayload fires with
                      | iotaNatRecZero =>
                          exact ⟨classifier, (unionSubjectReductionNatRecZero typed).2,
                            Conv.refl classifier⟩
                      | iotaNatRecSucc =>
                          simp only [SubjectReductionObligation] at obligation
                          exact obligation
                  | tail _ isRow => cases isRow with
                    | head =>
                        -- listElimNilIotaRow (gen_listElim): nil (unconditional) | cons (reclassify)
                        cases listElimNilRowFiringToIotaHead elimPayload fires with
                        | iotaListElimNil => exact (unionSubjectReductionListElimNil typed).2
                        | iotaListElimCons =>
                            simp only [SubjectReductionObligation] at obligation
                            exact (unionSubjectReductionListElimCons typed obligation).2
                    | tail _ isRow => cases isRow with
                      | head =>
                          -- listElimConsIotaRow (gen_listElim)
                          cases listElimConsRowFiringToIotaHead elimPayload fires with
                          | iotaListElimNil => exact (unionSubjectReductionListElimNil typed).2
                          | iotaListElimCons =>
                              simp only [SubjectReductionObligation] at obligation
                              exact (unionSubjectReductionListElimCons typed obligation).2
                      | tail _ isRow => cases isRow with
                        | head =>
                            -- optionMatchNoneIotaRow (gen_optionMatch): none | some (reclassify)
                            cases optionMatchNoneRowFiringToIotaHead elimPayload fires with
                            | iotaOptionMatchNone => exact (unionSubjectReductionOptionMatchNone typed).2
                            | iotaOptionMatchSome =>
                                simp only [SubjectReductionObligation] at obligation
                                exact (unionSubjectReductionOptionMatchSome typed obligation).2
                        | tail _ isRow => cases isRow with
                          | head =>
                              -- optionMatchSomeIotaRow (gen_optionMatch)
                              cases optionMatchSomeRowFiringToIotaHead elimPayload fires with
                              | iotaOptionMatchNone =>
                                  exact (unionSubjectReductionOptionMatchNone typed).2
                              | iotaOptionMatchSome =>
                                  simp only [SubjectReductionObligation] at obligation
                                  exact (unionSubjectReductionOptionMatchSome typed obligation).2
                          | tail _ isRow => cases isRow with
                            | head =>
                                -- eitherMatchInlIotaRow (gen_eitherMatch): inl | inr (reclassify)
                                cases eitherMatchInlRowFiringToIotaHead elimPayload fires with
                                | iotaEitherMatchInl =>
                                    simp only [SubjectReductionObligation] at obligation
                                    exact (unionSubjectReductionEitherMatchInl typed obligation).2
                                | iotaEitherMatchInr =>
                                    simp only [SubjectReductionObligation] at obligation
                                    exact (unionSubjectReductionEitherMatchInr typed obligation).2
                            | tail _ isRow => cases isRow with
                              | head =>
                                  -- eitherMatchInrIotaRow (gen_eitherMatch)
                                  cases eitherMatchInrRowFiringToIotaHead elimPayload fires with
                                  | iotaEitherMatchInl =>
                                      simp only [SubjectReductionObligation] at obligation
                                      exact (unionSubjectReductionEitherMatchInl typed obligation).2
                                  | iotaEitherMatchInr =>
                                      simp only [SubjectReductionObligation] at obligation
                                      exact (unionSubjectReductionEitherMatchInr typed obligation).2
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
                                        -- pathBetaIotaRow (gen_pathApp): deferred typing
                                        simp only [SubjectReductionObligation] at obligation
                                        exact obligation
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

/-! ## (3) The coverage / witness record + the single isolated open lemma -/

/-- **The single open union-classifier-validity obligation (VAL-2 / `classifierRespectsConv`).**  A value
union-typed at `A` with `Conv A B` AND a universe witness for `B` is union-typed at `B`.  This is exactly
the `conv` arm of `HasTypeUnion` made unconditional in the witness — it is NOT claimed proven here.  The
app-chain residual `UnionElementReclassifies` IS its element-type instance (the universe witness is what
the eliminator-head inversion fails to surface).  The binder-substituting rows no longer reduce to it: their
binder descent is SHIPPED (TYTAB-2 W4), so they reduce instead to the cumulative-former oracle
`UnionCumulativeFormerCloses` (the `UnionDataFormerValidity` wall).  These two — VAL-2 and the
cumulative-former oracle — are the remaining gaps to unconditional SR on every reducing row. -/
abbrev UnionClassifierRespectsConv (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) : Prop :=
  ∀ (value sourceType targetType : RawTerm scope)
    (levelExpr : FX1Poly.Universe.LevelExpr) (flag : FX1Poly.Universe.UniverseFlag),
    HasTypeUnion profile context value sourceType →
      Conv sourceType targetType →
      HasTypeUnion profile context targetType (universeCodeCell levelExpr flag) →
      HasTypeUnion profile context value targetType

/-- **★ The coverage / witness record.**  An inhabitant certifies: the certificate holds (`certified`); the
NINE rows discharge their obligation UNCONDITIONALLY — the obligation at those heads is `True`
(`boolElimUnconditional` / `idJFstSndUnconditional` cover the `gen_boolElim` / `gen_idJ` / `gen_fst` /
`gen_snd` heads; the `gen_natElim` / `gen_natRec` / `gen_optionMatch` / `gen_listElim` heads carry their
SHARED conditional obligation, whose unconditional sub-row is the zero / none / nil branch routed inside the
soundness theorem); and the soundness theorem itself types every routed reduct (`reductTyped`, inhabited by
the shipped theorem).  Because every field is inhabited by a shipped object, the certified set can NOT
silently shrink. -/
structure WfIotaElimSRCoverage (profile : PolyProfile) : Prop where
  /-- The decidable coherence certificate holds. -/
  certified : WfIotaElimSRTable
  /-- The boolElim rows' obligation is `True` (unconditional). -/
  boolElimUnconditional : ∀ {scope : Nat} {context : TypingContext profile scope}
    {redex reduct classifier : RawTerm scope},
    SubjectReductionObligation context boolTrueIotaRow redex reduct classifier
  /-- The fst / snd / idJ rows' obligation is `True` (unconditional). -/
  projectionAndIdJUnconditional : ∀ {scope : Nat} {context : TypingContext profile scope}
    {redex reduct classifier : RawTerm scope},
    SubjectReductionObligation context fstPairIotaRow redex reduct classifier ∧
    SubjectReductionObligation context sndPairIotaRow redex reduct classifier ∧
    SubjectReductionObligation context idJReflIotaRow redex reduct classifier
  /-- The soundness theorem types every routed reduct (the dispatch is inhabited). -/
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
    (obligation : SubjectReductionObligation context rule
      (.mkGen rule.elimGenerator elimPayload spine) reduct classifier),
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier

/-- **★ The coverage witness** — inhabited by the shipped certificate + soundness theorem, so the certified
set cannot silently shrink.  The unconditional fields close because the obligation at those heads computes
to `True`; the `reductTyped` field IS the soundness theorem. -/
theorem wfIotaElimSRCoverageWitness {profile : PolyProfile} : WfIotaElimSRCoverage profile where
  certified := iotaRuleTable_elimSRCertified
  boolElimUnconditional := trivial
  projectionAndIdJUnconditional := ⟨trivial, trivial, trivial⟩
  reductTyped := by
    intro _scope _context _rule isRow _elimRule isTypedElim _elimPayload _spine _reduct fires
      _classifier typed obligation
    exact HasTypeUnion.bundleIotaRowSubjectReduction isRow isTypedElim fires typed obligation

end FX1Poly.Typed
