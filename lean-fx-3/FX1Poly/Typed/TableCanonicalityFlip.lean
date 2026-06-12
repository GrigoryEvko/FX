import FX1Poly.Core.TableNormalize
import FX1Poly.Core.TableOneStepReducts
import FX1Poly.Core.TableRewriteRuleMap
import FX1Poly.Core.IotaTableOrientedSN
import FX1Poly.Core.IotaTableHeadExpansion
import FX1Poly.Typed.IotaElimTypedLink
import FX1Poly.Typed.TypedFragmentTableAdequacy

/-! # TableCanonicalityFlip — IOTA-T9 ★: StepTable/ConvTable are the
kernel's OFFICIAL relations

**THE FLIP.**  From this module on, the kernel's canonical one-step
reduction relation is `StepTable` (= `StepOverTable iotaRuleTable`) and
its canonical conversion is `ConvTable` — rules as DATA, metatheorems
generic over rows.  The bespoke `Step` survives as a DERIVED VIEW of the
legacy 17-row fragment (the embeddings below; its retirement is
IOTA-T11, user-gated), and the table-native endpoint-β is live in the
canonical semantics with no bespoke constructor anywhere.

## The headline ledger (what the canonical relations carry)

Every entry below is shipped, zero-axiom, and either proven generically
over any well-formed scope-uniform table or discharged at the canonical
18 rows by `rfl`-decided certificates:

* **Subject reduction** — `StepTable.subjectReduction` /
  `.subjectReductionStar` (this file; aliases of the IOTA-T7 master):
  Pi-fragment typing is preserved by every canonical step.
* **Confluence** — `StepTable.confluent` (IOTA-T6): the Takahashi
  triangle over the table; future rows inherit by re-deciding two
  certificates.
* **Conversion** — `ConvTable` with `refl`/`sym`/`trans`, transitivity
  needing NO per-term hypotheses (global confluence), and
  `ConvTable.decidableOfStronglyNormalizing` on the SN fragment.
* **Normalization** — `StepTable.reduceOnce` (sound + halting exactly
  at table normal forms, endpoint-β live) and `StepTable.normalize`
  (reaches a normal form by a genuine chain).
* **Exact reduct enumeration** — `StepTable.oneStepReducts`, sound AND
  complete (the completeness half the bespoke enumeration deferred).
* **SN tier** — `stepOverOrientedTable_wellFounded` (IOTA-T8): the
  classifier-passing 14-row sub-table is strongly normalizing by one
  RPO; the substituting rows honestly refuse the promise.
* **Head expansion** — `StepTable.tableRedexHeadExpansion` (IOTA-T8):
  the Tait arm at the SN candidate, generic over rows.
* **Honesty** — `Generator.hasReductionRule` derived from the table;
  `gen_fixedPoint` pinned rule-free.
* **The generated rewrite system** — `fxTableSystem`, containing the
  bespoke `fxStepSystem` strictly.

## Honest exclusions (NOT yet table-driven)

* η stays the bespoke `Step.eta` SIBLING inductive — the ETA-TABLE arc
  (`EtaRuleDesc`, #1387–#1396) is filed and gated behind this flip;
* `LevelExpr` normalization is a different carrier (the universe
  payload engine, M22);
* the typing rules of `HasTypeDescPi` (piIntro/piElim) await the TYTAB
  arc — this flip is the OPERATIONAL semantics only.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableCanonicalityFlip.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The legacy relation as a derived view -/

/-- Every bespoke chain is a canonical chain (the one-step view
`Step.toStepTable` shipped with the T1 adequacy; this lifts it along
chains). -/
theorem _root_.FX1Poly.Core.StepStar.toStepTableClosure {scope : Nat}
    {source target : RawTerm scope} (chain : StepStar source target) :
    ReflTransClosure (StepTable (scope := scope)) source target := by
  induction chain with
  | refl term => exact ReflTransClosure.refl term
  | trans headStep _tailChain tailClosure =>
      exact ReflTransClosure.head headStep.toStepTable tailClosure

/-- **Every bespoke conversion is a canonical conversion** — the join
components map chain-for-chain. -/
theorem _root_.FX1Poly.Core.Conv.toConvTable {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (convertible : Conv sourceTerm targetTerm) :
    ConvTable sourceTerm targetTerm := by
  obtain ⟨commonReduct, sourceChain, targetChain⟩ := convertible
  exact ⟨commonReduct, sourceChain.toStepTableClosure,
    targetChain.toStepTableClosure⟩

/-! ## The re-pointed typed subject reduction -/

/-- **★★ Subject reduction for the CANONICAL relation** — the kernel's
official one-step preservation theorem, re-pointed from the IOTA-T7
master: Pi-fragment typing survives every `StepTable` step. -/
theorem _root_.FX1Poly.Core.StepTable.subjectReduction
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context)
    {reduct : RawTerm scope} (tableStep : StepTable subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReductionTable typed wellFormed tableStep

/-- **★★ Many-step subject reduction for the canonical relation.** -/
theorem _root_.FX1Poly.Core.StepTable.subjectReductionStar
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context)
    {reduct : RawTerm scope}
    (chain : ReflTransClosure (StepTable (scope := scope)) subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReductionTableStar wellFormed typed chain

/-! ## Typed conversion transport along the legacy view -/

/-- Typed subjects converted by the BESPOKE conversion are convertible
canonically — the conversion side of the derived view, for consumers
holding legacy `Conv` facts across the flip. -/
theorem _root_.FX1Poly.Core.ConvTable.ofLegacyConv {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (convertible : Conv sourceTerm targetTerm) :
    ConvTable sourceTerm targetTerm :=
  convertible.toConvTable

end FX1Poly.Typed
