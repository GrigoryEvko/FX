import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality
import FX1Poly.Core.Rewriting.Confluence.RawConfluence
import FX1Poly.Tier0.Term.Generator.GeneratorSignatureValue

/-! # type-5 — quotient inductive-inductive types (QIITs) as a presented schema

The QIIT rung of the type axis.  A QIIT bundles three ingredients: (II) induction-induction — already
backed at `type-4` (the well-scoped `RawTerm`/`RawTermChildren` mutual + the `HasTypeDesc`/`DescTelescope`
description-driven mutual judgment); (Q) a quotient by equations; and (presentation) a SCHEMA — a signature
plus oriented equations — whose models the QIIT is initial among.  Lean 4 cannot DECLARE the intrinsic
inductive-inductive datatype, and the quotient half would need `Quot.sound` (an axiom we ban), so the QIIT
cannot be a native Lean inductive.  But it CAN be PRESENTED — and this rung backs the genuinely-shipped
presented-schema substrate (the new content beyond `type-4`'s II): the kernel's computation rules ARE a
well-formed table of oriented equations, the quotient recursor/eliminator DO compute as table rows, raw
terms ARE quotiented by computation (`Conv`, an unconditional equivalence), and the signature IS a
first-order value.  Like `type-1`..`type-4`, a NON-DUPLICATIVE ledger ABOVE Typed: markers + `_isBacked`
referencing named shipped theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasQuotientComputationRows`** — the quotient LIFT (recursor) and dependent ELIMINATOR compute
    on the constructor, as TABLE ROWS (the QIIT computation equation oriented as a rewrite):
    `quotRec(f, resp, quotMk(v)) ↝ app(f, v)` (`quotRecMkIotaRow_interpretsTarget`) and
    `quotElim(motive, kernel, quotMk(v)) ↝ app(kernel, v)` (`quotElimMkIotaRow_interpretsTarget`), both `rfl`.
  * **`fxType_hasWellFormedPresentation`** — the presented theory is a WELL-FORMED ORTHOGONAL rewrite system:
    the canonical iota rule table (the kernel's oriented computation equations, the quotient rows among them)
    satisfies the decidable orthogonality certificate (`iotaRuleTable_isWf : WfIotaTable iotaRuleTable`) —
    distinct keys, eliminator-determines-slot, elim/scrutinee head disjointness, primary scrutinee present.
    A presented theory whose rules are coherent.
  * **`fxType_hasComputationalQuotient`** — raw terms quotiented by COMPUTATION: `Conv` (join under the
    rewrite system) is an UNCONDITIONAL equivalence relation (`Conv.equivalence`, via raw confluence — no SN
    hypothesis, no `Quot.sound`).  The kernel's native quotient — the Q of QIIT realized computationally
    rather than by a propositional equality axiom.
  * **`fxType_hasSignatureValue`** — the kernel is PRESENTED as a signature: the generator signature reifies
    to a first-order data value (`fxSignature : List GeneratorDescriptor`) with a FAITHFUL enum↔descriptor
    round-trip (`Generator.descriptor_toGenerator_roundTrip`) — the signature half of the presented schema.

## What is deferred (the genuine object-level QIIT frontier)

  * `fxType_hasQuotientTypeFormer` — the object-level quotient TYPE former with FORMATION + typing.  The
    quotient lift COMPUTES (backed above) but `typingRuleDescOf` returns `none` for every quotient generator,
    the reducibility model has no quotient member, and subject reduction records "`gen_quotRec`/`gen_quotElim`
    carries no union typing rule".  Route: EXT-2 (quotient types as rows, WITH the typing rule).  `= false`.
  * `fxType_hasQuotientEquality` — the quotient EQUALITY law (`quotMk a ≡ quotMk b` when `a ~ b`).  The
    constructor `gen_quotEqAxiom` is an INERT reserved tag (Unit payload, no iota / redex head / typing /
    reducibility), held inert PRECISELY because it is the `Quot.sound` analogue and `Quot.sound` is banned
    under zero-axiom.  The kernel ships the recursor/computational side, not the propositional path-equality
    side.  `= false`.
  * `fxType_hasQuotientInductiveInductive` — the genuine QIIT FORMER.  `gen_qiitIntro` / `gen_qiitElim` are
    pure reserved tags (Unit payload, no iota / redex head / typing / reducibility).  Lean 4 rejects the
    intrinsic inductive-inductive datatype and the quotient needs `Quot.sound`, so the QIIT cannot be
    DECLARED — only PRESENTED as a bi-initial model over (signature, rule tables, `Conv`), the
    megaapex / SIG-5 / `fib-12` roadmap.  `= false`.

## Zero-axiom verification

Four `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems:
`quotRecMkIotaRow_interpretsTarget` / `quotElimMkIotaRow_interpretsTarget`; `iotaRuleTable_isWf`;
`Conv.equivalence`; `Generator.descriptor_toGenerator_roundTrip`) and three `:= false` deferral markers.
All cited substrate is `FX1Poly.Core`, funext-free, and CRUCIALLY `Quot.sound`-free (the kernel ships the
quotient COMPUTATIONALLY, never via the equality axiom).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TypeFive.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The quotient computation rows (the Q equation oriented as a rewrite) -/

/-- **Honesty marker** — `type-5` (quotient computation rows).  The quotient lift and dependent eliminator
compute on the constructor as table rows — the QIIT computation equation oriented as a rewrite.  Backed in
`fxType_quotientComputationRows_isBacked`.  `= true`. -/
def fxType_hasQuotientComputationRows : Bool := true

/-- ★ **Backed flip (quotient computation rows).**  The marker is `true` AND (i) the quotient lift fires:
`quotRec(f, resp, quotMk(v)) ↝ app(f, v)` (`quotRecMkIotaRow_interpretsTarget`); (ii) the dependent quotient
eliminator fires: `quotElim(motive, kernel, quotMk(v)) ↝ app(kernel, v)`
(`quotElimMkIotaRow_interpretsTarget`). -/
theorem fxType_quotientComputationRows_isBacked :
    fxType_hasQuotientComputationRows = true
      ∧ (∀ {scope : Nat} (kernelFn respectsRel value : RawTerm scope),
          quotRecMkIotaRow.interpretTarget? ()
            (.childCons kernelFn
              (.childCons respectsRel
                (.childCons (.mkGen .gen_quotMk () (.childCons value .childNil)) .childNil)))
            = some (.mkGen .gen_app () (.childCons kernelFn (.childCons value .childNil))))
      ∧ (∀ {scope : Nat} (depMotive depKernel value : RawTerm scope),
          quotElimMkIotaRow.interpretTarget? ()
            (.childCons depMotive
              (.childCons depKernel
                (.childCons (.mkGen .gen_quotMk () (.childCons value .childNil)) .childNil)))
            = some (.mkGen .gen_app () (.childCons depKernel (.childCons value .childNil)))) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro scope kernelFn respectsRel value
    exact quotRecMkIotaRow_interpretsTarget kernelFn respectsRel value
  · intro scope depMotive depKernel value
    exact quotElimMkIotaRow_interpretsTarget depMotive depKernel value

/-! ## The well-formed presentation (the schema is an orthogonal rewrite system) -/

/-- **Honesty marker** — `type-5` (well-formed presentation).  The presented theory — the canonical iota
rule table of oriented computation equations — is a well-formed ORTHOGONAL rewrite system.  Backed in
`fxType_wellFormedPresentation_isBacked`.  `= true`. -/
def fxType_hasWellFormedPresentation : Bool := true

/-- ★ **Backed flip (well-formed presentation).**  The marker is `true` AND the canonical iota rule table
satisfies the decidable orthogonality certificate (`iotaRuleTable_isWf`): distinct root keys,
eliminator-determines-slot coherence, elim/scrutinee head disjointness, and a primary scrutinee per row. -/
theorem fxType_wellFormedPresentation_isBacked :
    fxType_hasWellFormedPresentation = true ∧ WfIotaTable iotaRuleTable :=
  ⟨rfl, iotaRuleTable_isWf⟩

/-! ## The computational quotient (Conv = quotient of raw terms by computation) -/

/-- **Honesty marker** — `type-5` (computational quotient).  Raw terms quotiented by computation: `Conv` is
an unconditional equivalence relation (the Q of QIIT realized computationally, `Quot.sound`-free).  Backed in
`fxType_computationalQuotient_isBacked`.  `= true`. -/
def fxType_hasComputationalQuotient : Bool := true

/-- ★ **Backed flip (computational quotient).**  The marker is `true` AND `Conv` is an equivalence relation
at every scope — unconditionally, via raw confluence with no SN hypothesis and no `Quot.sound`
(`Conv.equivalence`). -/
theorem fxType_computationalQuotient_isBacked :
    fxType_hasComputationalQuotient = true ∧ (∀ {scope : Nat}, Equivalence (@Conv scope)) := by
  refine ⟨rfl, ?_⟩
  intro scope
  exact Conv.equivalence

/-! ## The signature value (the presented schema's signature half) -/

/-- **Honesty marker** — `type-5` (signature value).  The kernel is presented as a signature: the generator
signature reifies to a first-order data value (`fxSignature`) with a faithful enum↔descriptor round-trip.
Backed in `fxType_signatureValue_isBacked`.  `= true`. -/
def fxType_hasSignatureValue : Bool := true

/-- ★ **Backed flip (signature value).**  The marker is `true` AND every generator is recovered from its own
descriptor's tag — `toGenerator` is a left inverse of `descriptor`
(`Generator.descriptor_toGenerator_roundTrip`), the faithfulness of the reified signature `fxSignature`. -/
theorem fxType_signatureValue_isBacked :
    fxType_hasSignatureValue = true
      ∧ (∀ generator : Generator, (Generator.descriptor generator).toGenerator = some generator) :=
  ⟨rfl, Generator.descriptor_toGenerator_roundTrip⟩

/-! ## Honesty markers (the deferred object-level QIIT frontier) -/

/-- **Honesty marker.**  The object-level quotient TYPE former with FORMATION + typing — the quotient lift
computes (backed above) but `typingRuleDescOf` is `none` for every quotient generator, the reducibility model
has no quotient member, and subject reduction records "`gen_quotRec`/`gen_quotElim` carries no union typing
rule".  Route: EXT-2 (quotient types as rows, with the typing rule).  Deferred.  `= false`. -/
def fxType_hasQuotientTypeFormer : Bool := false

/-- **Honesty marker.**  The quotient EQUALITY law (`quotMk a ≡ quotMk b` when `a ~ b`) — `gen_quotEqAxiom`
is an INERT reserved tag, held inert precisely because it is the `Quot.sound` analogue and `Quot.sound` is
banned under zero-axiom.  The kernel ships the recursor/computational side, not the propositional
path-equality side.  Deferred.  `= false`. -/
def fxType_hasQuotientEquality : Bool := false

/-- **Honesty marker.**  The genuine QIIT FORMER — `gen_qiitIntro` / `gen_qiitElim` are pure reserved tags
(no iota / redex head / typing / reducibility).  Lean 4 rejects the intrinsic inductive-inductive datatype
and the quotient needs `Quot.sound`, so the QIIT cannot be DECLARED — only PRESENTED as a bi-initial model
over (signature, rule tables, `Conv`), the megaapex / SIG-5 / `fib-12` roadmap.  Deferred.  `= false`. -/
def fxType_hasQuotientInductiveInductive : Bool := false

end FX1Poly.Tier0
