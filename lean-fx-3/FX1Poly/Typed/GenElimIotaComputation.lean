import FX1Poly.Typed.ElimRuleDesc
import FX1Poly.Typed.HasTypeDescPiBetaSR

/-! # FX1Poly/Typed/GenElimIotaComputation — the generic ι-computation typing rule (GTL-18)

`ElimRuleDesc` (GTL-17) shipped the elimination-rule TABLE and the *reconstruction*
(`hasTypeDescPi_piElim_viaElimDesc`): the shipped `HasTypeDescPi.piElim` output IS the rule-DATA
output (`appCell functionTerm argument : rule.outputType scope codomainCode argument =
subst0 codomainCode argument`).  That is the INTRODUCTION half of the elimination story — the
eliminator application TYPES at the table-driven output.  This file is GTL-18's genuinely-new piece: the
COMPUTATION half — the eliminator's ι-reduction PRESERVES the rule-DATA output.

For the sole current eliminator (`gen_app` / Π-elimination) the ι-rule is β: `appCell (lamCell body)
argument` ι-contracts to `RawTerm.subst0 body argument`.  The shipped fully-general β subject reduction
(`HasTypeDescPi.betaSubjectReduction`, TY-SR-β / #474) carries the contractum to the SAME classifier the
redex was typed at; composed with the GTL-17 reconstruction that classifier IS the rule-DATA output.  So:

  * `hasTypeDescPi_genElimIota_viaElimDesc` — **the generic ι-computation typing rule.**  The
    ι-contractum `subst0 body argument` of an eliminator application types at the rule-DATA output
    `rule.outputType scope codomainCode argument`, table-DRIVEN (the `rule` comes from
    `elimRuleDescOf .gen_app`).  The elimination twin of the formation-engine's
    `subjectReductionAtFormer` (the former family's ι-side type-stability), but read off the elim TABLE.
  * `hasTypeDescPi_genElim_computesTypeStably` — **the bundle the GTL-20 mutual fundamental-metatheory
    bundle consumes for its elimination arm**: BOTH the redex (`appCell (lamCell body) argument`, via the
    GTL-17 reconstruction) AND its ι-contractum (`subst0 body argument`, via the ι-rule) type at the one
    rule-DATA output — i.e. the eliminator computes TYPE-STABLY.  This is precisely the elimination-side
    ingredient the mutual bundle pairs against the introduction reconstruction (GTL-16) and the formation
    `genFormationPi` arm to discharge the grown context-conversion piElim residual (GrownCtxConv-5 / #842 via
    GTL-21 / #835).

ADDITIVE — it does NOT modify `HasTypeDescPi`.  Like `ElimRuleDesc`/`IntroRuleDesc` it reads the
existing engine arms (`piElim`, `betaSubjectReduction`) through the table; the abstract-generic `genElim`
ARM with a fully-generic elimination-premise spine remains the deliberate engine-level fold (the
arity-entangled residual the GTL-20 mutual bundle states).  Here every eliminator-family ι-rule that
lands in `elimRuleDescOf` reuses this theorem by the same `Option.some.inj` table read.

## Zero-axiom verification

`Option.some.inj` on the `gen_app` table row + `HasTypeDescPi.piElim` (the reconstruction) +
`HasTypeDescPi.betaSubjectReduction` (the shipped TY-SR-β).  The rule-DATA output reduces to
`RawTerm.subst0 codomainCode argument` by `rfl` after `subst hRule`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The generic ι-computation typing rule (GTL-18).**  An eliminator application whose function is a
`lamCell body` and whose `rule` is read from the table (`elimRuleDescOf .gen_app = some rule`) has its
ι-contractum `RawTerm.subst0 body argument` typed at the rule-DATA output
`rule.outputType scope codomainCode argument` (= `RawTerm.subst0 codomainCode argument` by `rfl`).  The
COMPUTATION half of the elimination story (the GTL-17 reconstruction is the introduction half): the
eliminator's ι-reduction preserves the table-driven output type.  Built by typing the redex at the
rule-DATA output (`HasTypeDescPi.piElim`, the reconstruction) and carrying its contractum to the same
output by the shipped fully-general β subject reduction (`HasTypeDescPi.betaSubjectReduction`, #474).
NON-VACUOUS (a genuine β/ι-redex's contractum types at the table output), table-DRIVEN, and the
elimination-side ingredient the GTL-20 mutual fundamental-metatheory bundle pairs against the formation
and introduction reconstructions to discharge the GrownCtxConv-5 piElim residual. -/
theorem hasTypeDescPi_genElimIota_viaElimDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (rule : ElimRuleDesc) (isElim : elimRuleDescOf .gen_app = some rule)
    (functionTyped :
      HasTypeDescPi profile context (lamCell domainCode body) (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context (RawTerm.subst0 body argument)
      (rule.outputType scope codomainCode argument) := by
  have hRule : rule = { outputType := piElimOutput } :=
    Option.some.inj (isElim.symm.trans elimRuleDescOf_app)
  subst hRule
  have redexTyped :
      HasTypeDescPi profile context (appCell (lamCell domainCode body) argument)
        (RawTerm.subst0 codomainCode argument) :=
    HasTypeDescPi.piElim functionTyped argumentTyped
  exact HasTypeDescPi.betaSubjectReduction redexTyped wellFormed

/-- **Type-stable elimination computation (GTL-18, the GTL-20-bundle ingredient).**  For a `lamCell`
function and a table-read `rule`, BOTH the eliminator redex `appCell (lamCell body) argument` (via the
GTL-17 reconstruction `HasTypeDescPi.piElim`) AND its ι-contractum `RawTerm.subst0 body argument` (via
the generic ι-computation rule) type at the SAME rule-DATA output `rule.outputType scope codomainCode
argument`.  This is the elimination arm in the exact shape the GTL-20 mutual fundamental-metatheory
bundle consumes: the eliminator both forms and computes at one table-driven type, so its ι-step is
type-preserving by construction of the table — the structural counterpart, on the elimination side, to
the formation engine's `subjectReductionAtFormer` and the introduction reconstruction (GTL-16).
Zero-axiom (the reconstruction + the generic ι-rule, both shipped above). -/
theorem hasTypeDescPi_genElim_computesTypeStably {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (rule : ElimRuleDesc) (isElim : elimRuleDescOf .gen_app = some rule)
    (functionTyped :
      HasTypeDescPi profile context (lamCell domainCode body) (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context (appCell (lamCell domainCode body) argument)
        (rule.outputType scope codomainCode argument)
      ∧ HasTypeDescPi profile context (RawTerm.subst0 body argument)
        (rule.outputType scope codomainCode argument) := by
  refine ⟨hasTypeDescPi_piElim_viaElimDesc rule isElim functionTyped argumentTyped, ?_⟩
  exact hasTypeDescPi_genElimIota_viaElimDesc rule isElim functionTyped argumentTyped wellFormed

end FX1Poly.Typed
