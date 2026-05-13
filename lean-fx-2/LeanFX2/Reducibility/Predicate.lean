import LeanFX2.Reducibility.Basic
import LeanFX2.Reducibility.Neutral

/-! # LeanFX2.Reducibility.Predicate — the Tait reducibility candidate

`def Reducible` is the load-bearing definition for the kernel SN
theorem.  It is a Prop-valued recursive function on `Ty` covering
all 25 Ty constructors (K12.1–K12.16):

* Closed-leaf arms (`unit`, `bool`, `nat`, `empty`, `interval`,
  `universe`, `session`, `effect`, `modal`) — plain strong
  normalization.
* Compound arms — Tait's specialized closure per type former
  (arrow / piTy / sigmaTy / id / oeq / idStrict / equiv / refine
  / record / codata / listType / optionType / eitherType / path
  / glue / tyVar).

The pivot from inductive Prop to `def`-by-recursion is forced by
Lean 4 v4.29.1's strict-positivity rejection of the arrow closure
clause (K12.5).  Documented in `feedback_lean_reducible_arrow_blocker.md`.

## Termination

Reducible recurses on structurally-smaller Ty sub-components.
Lean accepts this via the auto-generated `Ty.rec` recursor
(no `Acc`, no `WellFounded` — pure structural recursion).

## Root status

Layer 3 metatheory leaf.  Foundational for the K12.20.U4
fundamental-theorem cascade and the M04 strong-normalization
corollary (#1273 / K12.27). -/

namespace LeanFX2



/-- The Tait reducibility-candidate predicate, defined by
structural recursion on Ty.

Closed-leaf arms (unit / bool / nat / empty / interval /
universe / tyVar) use plain SN per Tait's base-type clause.
The arrow arm bundles SN with the closure under application
per Wood/Atkey 2022's corrected Lam rule.  Remaining arms
(piTy / sigmaTy / id / list / option / either / path / glue /
oeq / idStrict / equiv / refine / record / codata / session /
effect / modal) ship the SN-fallback closure; K12.6-K12.16
tighten each to its type-former-specific shape. -/
def Reducible {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : ∀ (ty : Ty level scope) {raw : RawTerm scope},
        Term context ty raw → Prop
  -- Closed leaves (K12.2-K12.4): SN base-type clause
  | Ty.unit, _, term => Term.isStronglyNormalizing term
  | Ty.bool, _, term => Term.isStronglyNormalizing term
  | Ty.nat, _, term => Term.isStronglyNormalizing term
  | Ty.empty, _, term => Term.isStronglyNormalizing term
  | Ty.interval, _, term => Term.isStronglyNormalizing term
  | Ty.universe _ _, _, term => Term.isStronglyNormalizing term
  | Ty.tyVar _, _, term => Term.isStronglyNormalizing term
  -- Function type (K12.5): SN + closure under application
  | Ty.arrow domainType codomainType, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Reducible codomainType (Term.app functionTerm argumentTerm)
  -- Dependent Π type (K12.6, SN-output closure): SN + SN-after-app.
  -- The full Tait dep-Π closure (`Reducible (B.subst0 A arg)
  -- (Term.appPi f arg)`) recurses on the substituted codomain
  -- `B.subst0 domainType argumentRaw` — NOT a structural
  -- sub-term of `Ty.piTy A B`, so the structural-recursion
  -- checker rejects it (probed 2026-05-11: "Please use
  -- `termination_by` to specify a decreasing measure",
  -- requires WellFounded.fix → Acc, banned by GatesCore
  -- line 51).  The current closure recurses only on `domainType`
  -- (strict sub-term) and records the M04 endpoint: reducible
  -- arguments produce SN applications.  A full substituted-codomain
  -- Reducible witness belongs to later motive-rich beta-eta / NbE
  -- infrastructure (reserve K12.6.full for that).
  | Ty.piTy domainType _, _, functionTerm =>
      Term.isStronglyNormalizing functionTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm)
  -- Dependent Σ type (K12.7, asymmetric closure): SN + full
  -- Reducible on fst projection (firstType IS a strict sub-term
  -- of `Ty.sigmaTy firstType secondType`, so structural recursion
  -- works) + SN on snd projection (its type is
  -- `secondType.subst0 firstType (RawTerm.fst pairRaw)` — same
  -- substituted-sub-term wall as K12.6's piTy codomain).
  | Ty.sigmaTy firstType _, _, pairTerm =>
      Term.isStronglyNormalizing pairTerm ∧
      Reducible firstType (Term.fst pairTerm) ∧
      Term.isStronglyNormalizing (Term.snd pairTerm)
  -- Remaining type formers (K12.11-K12.16 TODO): SN-fallback
  -- HoTT propositional identity type (K12.9, SN-output idJ closure).
  -- The id-eliminator `Term.idJ` consumes a witness at
  -- `Ty.id carrier leftEndpoint rightEndpoint` and a baseCase at an
  -- arbitrary motiveType, producing `motiveType`.  motiveType is NOT
  -- a structural sub-Ty of `Ty.id _ _ _` (eliminator-output types
  -- never are), so Reducible at motiveType is banned by the
  -- structural-recursion-on-Ty checker.  Carrier IS a strict sub-Ty,
  -- but doesn't appear in idJ's argument signature directly — only in
  -- the id-type's own structure.  The closure records SN(witness) +
  -- (baseCase SN → SN(idJ baseCase witness)), mirroring K12.6's
  -- SN-output pattern.  Full Reducible-motive closure belongs to
  -- later motive-rich infrastructure.
  | Ty.id _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing (Term.idJ baseCase witness)
  -- Parametric inductive: list (K12.8, SN-output elim closure).
  -- Mirrors K12.6 piTy's "Reducible-arg → SN result" pattern.
  -- The eliminator `Term.listElim` returns at an arbitrary motiveType
  -- (NOT a strict sub-Ty of `Ty.listType elementType`), so the
  -- structural-recursion-on-Ty checker rejects a full
  -- Reducible-at-motiveType conclusion (would need same-or-arbitrary-Ty
  -- recursion).  The closure recurses on `elementType` only
  -- (strict sub-Ty, full Reducible works) for the head-element witness,
  -- demotes the tail to SN (its type is `Ty.listType elementType` —
  -- SAME Ty, recursion banned), demands SN of branches and SN of the
  -- elim result.  The explicit branch-SN premises are load-bearing:
  -- raw congruence reduces branches even when the scrutinee is stuck,
  -- so neutral/list-variable CR3 cannot be sound without them.
  | Ty.listType elementType, _, listTerm =>
      Term.isStronglyNormalizing listTerm ∧
      ∀ {motiveType : Ty level scope}
        {nilRaw consRaw : RawTerm scope}
        (nilBranch : Term context motiveType nilRaw)
        (consBranch : Term context (Ty.arrow elementType
                                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw),
        Term.isStronglyNormalizing nilBranch →
        Term.isStronglyNormalizing consBranch →
        (∀ {headRaw tailRaw : RawTerm scope}
           (headTerm : Term context elementType headRaw)
           (tailTerm : Term context (Ty.listType elementType) tailRaw),
           Reducible elementType headTerm →
           Term.isStronglyNormalizing tailTerm →
           Term.isStronglyNormalizing
             (Term.app (Term.app consBranch headTerm) tailTerm)) →
        Term.isStronglyNormalizing (Term.listElim listTerm nilBranch consBranch)
  -- Parametric inductive: option (K12.8, SN-output elim closure).  Cleanest
  -- of the three K12.8 arms: someBranch's type `Ty.arrow elementType
  -- motiveType` matches K12.6 piTy SN-output closure shape exactly when
  -- restricted to elementType (strict sub-Ty).  Demands SN of both
  -- branches and Reducible-arg → SN-applied of someBranch, yielding SN
  -- of the optionMatch result.  The some-branch SN premise is necessary
  -- because optionMatch congruence can reduce it even under a stuck
  -- neutral scrutinee.
  | Ty.optionType elementType, _, optionTerm =>
      Term.isStronglyNormalizing optionTerm ∧
      ∀ {motiveType : Ty level scope}
        {noneRaw someRaw : RawTerm scope}
        (noneBranch : Term context motiveType noneRaw)
        (someBranch : Term context (Ty.arrow elementType motiveType) someRaw),
        Term.isStronglyNormalizing noneBranch →
        Term.isStronglyNormalizing someBranch →
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context elementType valueRaw),
           Reducible elementType valueTerm →
           Term.isStronglyNormalizing (Term.app someBranch valueTerm)) →
        Term.isStronglyNormalizing
          (Term.optionMatch optionTerm noneBranch someBranch)
  -- Parametric inductive: either (K12.8, symmetric SN-output elim closure).
  -- Symmetric in leftType / rightType (both strict sub-Ty of
  -- `Ty.eitherType leftType rightType`); each branch is
  -- `Ty.arrow leftType motiveType` / `Ty.arrow rightType motiveType`
  -- matching the K12.6 piTy SN-output shape per branch.  Demands branch SN
  -- plus Reducible-arg → SN-applied on each side, yielding SN of the
  -- eitherMatch result.  Branch SN is required for neutral scrutinees
  -- because eitherMatch congruence reduces both branches independently
  -- of which ι-rule may later fire.
  | Ty.eitherType leftType rightType, _, eitherTerm =>
      Term.isStronglyNormalizing eitherTerm ∧
      ∀ {motiveType : Ty level scope}
        {leftRaw rightRaw : RawTerm scope}
        (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
        (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw),
        Term.isStronglyNormalizing leftBranch →
        Term.isStronglyNormalizing rightBranch →
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context leftType valueRaw),
           Reducible leftType valueTerm →
           Term.isStronglyNormalizing (Term.app leftBranch valueTerm)) →
        (∀ {valueRaw : RawTerm scope}
           (valueTerm : Term context rightType valueRaw),
           Reducible rightType valueTerm →
           Term.isStronglyNormalizing (Term.app rightBranch valueTerm)) →
        Term.isStronglyNormalizing
          (Term.eitherMatch eitherTerm leftBranch rightBranch)
  -- Cubical path (K12.12, full-output pathApp closure).
  -- `Ty.path carrier left right` has carrier as strict sub-Ty and
  -- endpoints as RawTerm.  The eliminator `Term.pathApp` consumes
  -- the path + an interval term, produces a result at carrier
  -- (strict sub-Ty).  The closure recurses Reducible on carrier
  -- (strict sub-Ty ✓), but demands only SN on intervalTerm rather
  -- than Reducible at Ty.interval — Ty.interval is a sibling
  -- constructor of Ty, NOT a structural sub-Ty of Ty.path, so the
  -- structural-recursion-on-Ty checker rejects a `Reducible
  -- Ty.interval` call here.  Per K12.4's closed-leaf arm,
  -- `Reducible Ty.interval _ = Term.isStronglyNormalizing _`, so the
  -- SN demotion is propositionally equivalent to the full Tait
  -- form.  `modeIsUnivalent : mode = Mode.univalent` is universally
  -- quantified — vacuous in non-univalent modes.
  | Ty.path carrier _ _, _, pathTerm =>
      Term.isStronglyNormalizing pathTerm ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent)
        {intervalRaw : RawTerm scope}
        (intervalTerm : Term context Ty.interval intervalRaw),
        Term.isStronglyNormalizing intervalTerm →
        Reducible carrier
          (Term.pathApp modeIsUnivalent pathTerm intervalTerm)
  -- CCHM Glue (K12.12, full glueElim closure).  `Ty.glue baseType
  -- boundaryWitness` has baseType as strict sub-Ty.  The eliminator
  -- `Term.glueElim` is a simple projection: consumes the glued value,
  -- produces a result at baseType.  Even simpler closure than path
  -- (no quantifier over argument): SN(gluedValue) + Reducible at
  -- baseType for the projection result.  Mode-univalent constraint
  -- universally quantified per the K12.10 idStrict pattern.
  | Ty.glue baseType _, _, gluedValue =>
      Term.isStronglyNormalizing gluedValue ∧
      ∀ (modeIsUnivalent : mode = Mode.univalent),
        Reducible baseType
          (Term.glueElim modeIsUnivalent gluedValue)
  -- HoTT observational equality (K12.10, SN-output oeqJ closure).
  -- Ty.oeq mirrors Ty.id's shape exactly: carrier (strict sub-Ty) +
  -- two RawTerm endpoints.  The oeq-eliminator `Term.oeqJ` has the
  -- same shape as `Term.idJ` — consumes a witness and a baseCase at
  -- an arbitrary motiveType, produces motiveType.  Same K12.6 / K12.9
  -- SN-output pattern: SN(witness) + (SN baseCase → SN(oeqJ
  -- baseCase witness)).
  | Ty.oeq _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing (Term.oeqJ baseCase witness)
  -- Strict identity type (K12.10, SN-output idStrictRec closure).
  -- Ty.idStrict mirrors Ty.id's shape but the eliminator
  -- `Term.idStrictRec` requires a `mode = Mode.strict` witness.  The
  -- closure quantifies that witness universally — when the ambient
  -- mode ≠ Mode.strict, the equation is uninhabited and the inner
  -- ∀ is vacuous (closure reduces to SN(witness) alone).  Same
  -- K12.6 / K12.9 SN-output pattern in the strict-mode branch.
  | Ty.idStrict _ _ _, _, witness =>
      Term.isStronglyNormalizing witness ∧
      ∀ (modeIsStrict : mode = Mode.strict)
        {motiveType : Ty level scope}
        {baseRaw : RawTerm scope}
        (baseCase : Term context motiveType baseRaw),
        Term.isStronglyNormalizing baseCase →
        Term.isStronglyNormalizing
          (Term.idStrictRec modeIsStrict baseCase witness)
  -- Type equivalence (K12.11, full Reducible closure via equivApp).
  -- `Ty.equiv carrierA carrierB` has BOTH carrierA and carrierB as
  -- strict sub-Ty, and `Term.equivApp` mirrors `Term.app` exactly:
  -- takes the equivalence + an argument at carrierA, produces a
  -- result at carrierB.  Both Reducible recursions descend on strict
  -- sub-Ty, so the closure can demand FULL Reducible on both sides
  -- (no SN-fallback needed — same shape as K12.5 RC.arrow).
  -- Heterogeneous equivalence laws (left/right inverse) live INSIDE
  -- equivIntroHet's construction and are not exposed as eliminators;
  -- so the equivApp-driven closure captures the full computational
  -- content available at the kernel layer.
  | Ty.equiv carrierA carrierB, _, equivTerm =>
      Term.isStronglyNormalizing equivTerm ∧
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context carrierA argumentRaw),
        Reducible carrierA argumentTerm →
        Reducible carrierB (Term.equivApp equivTerm argumentTerm)
  -- Refinement type (K12.14, full refineElim closure).
  -- `Ty.refine baseType predicate` has baseType as strict sub-Ty
  -- and predicate as a RawTerm-binder (no typed dependency at the
  -- Reducible layer).  `Term.refineElim` is a pure projection from
  -- `Ty.refine _ _` to baseType — no mode constraint, no
  -- quantifier overhead.  Structurally identical to K12.12
  -- Ty.glue's full-output closure: SN(refinedValue) + Reducible
  -- baseType (Term.refineElim refinedValue).  The "Decidable
  -- predicate discharge" aspect of K12.14 lives at Layer 5 SMT-
  -- recheck (#1342 D5.6, #1344 D5.8 SMTCert) — orthogonal to the
  -- Reducibility-candidate closure shipped here.
  | Ty.refine baseType _, _, refinedValue =>
      Term.isStronglyNormalizing refinedValue ∧
      Reducible baseType (Term.refineElim refinedValue)
  -- Single-field record (K12.15, full recordProj closure).
  -- `Ty.record singleFieldType` has singleFieldType as strict sub-Ty.
  -- `Term.recordProj` projects to singleFieldType — same structure
  -- as K12.14 refine / K12.12 glue.  Multi-field records compose
  -- via nested single-field records (per Term.lean docstring),
  -- preserving this closure shape under nesting.
  | Ty.record singleFieldType, _, recordValue =>
      Term.isStronglyNormalizing recordValue ∧
      Reducible singleFieldType (Term.recordProj recordValue)
  -- Codata (K12.15, full codataDest closure).  `Ty.codata stateType
  -- outputType` has BOTH stateType and outputType as strict sub-Ty.
  -- `Term.codataDest` projects to outputType (the observation type).
  -- The stateType doesn't appear in any current eliminator (it's
  -- packed into the unfold/initial-state), so the closure recurses
  -- only on outputType.  Productivity-checking at higher
  -- observation depths lives at the codata-corecursion Layer
  -- (#1267 K08), orthogonal to this RC closure.
  | Ty.codata _ outputType, _, codataValue =>
      Term.isStronglyNormalizing codataValue ∧
      Reducible outputType (Term.codataDest codataValue)
  -- Session protocol (K12.15, Layer-1 documented SN-fallback).
  -- `Ty.session protocolStep` has protocolStep as a RawTerm — no
  -- typed sub-Ty exposed at the Ty layer.  Layer 1 ships
  -- `Term.sessionSend` / `Term.sessionRecv` as type-PRESERVING
  -- congruence-only ctors: both produce `Term ctx (Ty.session
  -- protocolStep) _` from inputs at the same session type, not a
  -- strict sub-Ty.  No projection eliminator at Layer 1 — the
  -- session protocol-state advancement (send → recv → end via
  -- duality) lives at the Sessions layer (#1268 K09 - implement
  -- session types at kernel).  K12.15.layer-sessions will then
  -- ship per-step closures via the Sessions.advance eliminator.
  | Ty.session _, _, sessionTerm =>
      Term.isStronglyNormalizing sessionTerm
  -- Effectful type (K12.15, Layer-1 documented SN-fallback).
  -- `Ty.effect carrierType effectTag` has carrierType as a strict
  -- sub-Ty in principle, but Layer 1 ships ONLY the
  -- `Term.effectPerform` introducer — no `Term.effectHandle`
  -- destructor projecting to carrierType exists yet.  The effect-
  -- handler / row-discharge semantics belong to the Effects layer
  -- (#1345 D5.9 Effects/Foundation.lean Op+EffectRow+effectPerform+
  -- effectHandle infrastructure, #1346 D5.10 Effects/Step.lean
  -- handler reduction theorems).  When Layer 5 Effects lands,
  -- K12.15.layer-effects will tighten this arm to
  -- `SN(term) ∧ ∀ handlerImpl, Reducible carrierType
  -- (Term.effectHandle term handlerImpl)`.
  | Ty.effect _ _, _, effectTerm =>
      Term.isStronglyNormalizing effectTerm
  -- Modal type (K12.13, Layer-1 SN-fallback with Layer-6 deferral).
  -- `Ty.modal modalityTag carrierType` has carrierType as a strict
  -- sub-Ty, so structural recursion would admit a `Reducible
  -- carrierType _` call in principle.  HOWEVER, the current kernel
  -- (Layer 1) ships modal ctors as RAW-SIDE SCAFFOLDING ONLY:
  -- `Term.modIntro innerTerm : Term ctx innerType (RawTerm.modIntro
  -- innerRaw)` preserves innerType rather than producing
  -- `Ty.modal _ innerType`.  Consequently, NO Term ctor at the
  -- typed layer currently inhabits `Ty.modal _ _` — the type
  -- former exists, but the typed kernel has zero inhabitants of
  -- modal type.  Any putative `Reducible Ty.modal _ _ term`
  -- application is therefore vacuous at Layer 1, and SN-fallback
  -- is the maximally-meaningful closure available without new
  -- ctors.  Layer 6 (#1716 Modal/Foundation.lean +
  -- CUMUL-7.1.{1,2,3} #1689-1691) will add typed
  -- `Term.modIntroCross` / `Term.modElimCross` producing
  -- `Ty.modal modality carrierType`-typed values plus the
  -- 8-modality dispatch (♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain + ghost/cap/
  -- later/clock).  K12.13.layer6 will then tighten this arm to
  -- the per-modality Tait closure (e.g. `Reducible (modal ◇ A)
  -- term := SN(term) ∧ Reducible A (Term.modElimCross term)` for
  -- positive modalities, with mode-quantified eliminators per the
  -- K12.10 idStrict pattern).
  | Ty.modal _ _, _, term => Term.isStronglyNormalizing term

/-- **K12.17 universal extraction**: every reducible term is
strongly normalizing.  Holds uniformly across all 25 Ty arms —
every Reducible body either IS `Term.isStronglyNormalizing` (for
closed-leaf arms K12.2-K12.4, SN-fallback arms K12.13/15-modal-
session-effect) or starts with it as the first conjunct (for all
type-former-specific arms K12.5-K12.15).

This is the foundational extraction lemma the fundamental-lemma
cascade (K12.18-K12.26) will invoke on every Term typing
derivation to conclude SN from the Reducible witness. -/
theorem Reducible.isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    : ∀ {ty : Ty level scope} {raw : RawTerm scope}
        {term : Term context ty raw},
        Reducible ty term → Term.isStronglyNormalizing term
  | Ty.unit, _, _, witness => witness
  | Ty.bool, _, _, witness => witness
  | Ty.nat, _, _, witness => witness
  | Ty.empty, _, _, witness => witness
  | Ty.interval, _, _, witness => witness
  | Ty.universe _ _, _, _, witness => witness
  | Ty.tyVar _, _, _, witness => witness
  | Ty.arrow _ _, _, _, witness => witness.1
  | Ty.piTy _ _, _, _, witness => witness.1
  | Ty.sigmaTy _ _, _, _, witness => witness.1
  | Ty.id _ _ _, _, _, witness => witness.1
  | Ty.listType _, _, _, witness => witness.1
  | Ty.optionType _, _, _, witness => witness.1
  | Ty.eitherType _ _, _, _, witness => witness.1
  | Ty.path _ _ _, _, _, witness => witness.1
  | Ty.glue _ _, _, _, witness => witness.1
  | Ty.oeq _ _ _, _, _, witness => witness.1
  | Ty.idStrict _ _ _, _, _, witness => witness.1
  | Ty.equiv _ _, _, _, witness => witness.1
  | Ty.refine _ _, _, _, witness => witness.1
  | Ty.record _, _, _, witness => witness.1
  | Ty.codata _ _, _, _, witness => witness.1
  | Ty.session _, _, _, witness => witness
  | Ty.effect _ _, _, _, witness => witness
  | Ty.modal _ _, _, _, witness => witness


end LeanFX2
