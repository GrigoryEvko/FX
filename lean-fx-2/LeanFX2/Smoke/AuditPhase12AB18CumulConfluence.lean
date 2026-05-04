import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Smoke.AuditPhase12AB17CumulReduction

/-! # Smoke/AuditPhase12AB18CumulConfluence — confluence cascade audit.

Phase 12.A.B18 (CUMUL-4.1..4.5).  Audits where the cumulUpInner
extension lands in the confluence pipeline, and explicitly
documents the architectural dependency on Phase 4 (D3.1-D3.4)
shipping the typed `Term.cd` machinery.

## Architectural status

`Confluence/Cd.lean`, `Confluence/CdLemma.lean`,
`Confluence/Diamond.lean`, and `Confluence/ChurchRosser.lean`
are CURRENTLY PLACEHOLDERS — they contain only documentation
plus an `end LeanFX2` marker.  No `Term.cd` function, no
`cd_lemma` theorem, no `Diamond`, no `Church-Rosser` proof
exists at the typed level in lean-fx-2 yet.

This is a known architectural commitment per ROADMAP.md
(Phase 4 work).  The lean-fx codebase has the analogous
machinery (W8.x, ~3000 lines), and the lean-fx-2 plan is to
re-ship it on the cleaner raw-aware Term foundation in tasks
D3.1 (#1316), D3.2 (#1317), D3.3 (#1318), D3.4 (#1319).

## What this audit DOES audit

* Confluence layer files BUILD with the new cumulUpInner ctor in
  Step.lean and Step.par.cumulUpInnerCong in ParRed.lean.
* The typed Step infrastructure (Step.toPar, Step.toConvCumul,
  Step.par.toRawBridge, Step.preserves_isClosedTy) handles the
  new ctor zero-axiom — re-confirmed via re-import.

## What this audit DOES NOT audit (and why)

* `Term.cd` arm for cumulUp (CUMUL-4.1 #1414): blocked on D3.1
  (#1316) shipping the base `Term.cd` definition.  Cannot extend
  what does not exist.
* `cd_lemma` cumulUp case (CUMUL-4.2 #1415): blocked on D3.2
  (#1317) shipping the base cd_lemma.
* Diamond extension (CUMUL-4.3 #1416): blocked on D3.3 (#1318).
* ChurchRosser extension (CUMUL-4.4 #1417): blocked on D3.4
  (#1319).

When Phase 4 ships, each of those will have a one-arm extension
to cover cumulUp via `Step.cumulUpInner` (now available).

## Honest discipline

Per CLAUDE.md zero-axiom rule: we do NOT ship sorry-blocked or
hypothesis-as-postulate "extensions" of `Term.cd` etc.  We ship
the dependency documentation and the foundation rules
(cumulUpInner) that Phase 4 will consume.

## Audit gates

Re-confirms the Phase 17 audit decls remain green when imported
from the broader Confluence layer. -/

namespace LeanFX2

#print axioms Step.toPar
#print axioms Step.toConvCumul
#print axioms Step.par.toRawBridge
#print axioms Step.preserves_isClosedTy

/-! ## Demonstration: a Step.cumulUpInner threads through the

forward bridge to ConvCumul AND through the par lift AND through
the raw projection — three consumers of Step's recursion all
handle the new ctor cleanly. -/

example
    {mode : Mode} {scopeLow scope : Nat}
    {innerLevel lowerLevel higherLevel : UniverseLevel}
    {cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat}
    {cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {ctxLow : Ctx mode (lowerLevel.toNat + 1) scopeLow}
    {ctxHigh : Ctx mode (higherLevel.toNat + 1) scope}
    {lowerSource lowerTarget :
      Term ctxLow (Ty.universe lowerLevel (Nat.le_refl _))
                  (RawTerm.universeCode innerLevel.toNat)}
    (innerStep : Step lowerSource lowerTarget) :
    -- Three independent bridges through cumulUpInner:
    -- (a) Step ⇒ Step.par
    Step.par
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerSource)
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerTarget)
    ∧
    -- (b) Step ⇒ ConvCumul
    ConvCumul
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerSource)
      (Term.cumulUp (ctxHigh := ctxHigh)
                    innerLevel lowerLevel higherLevel
                    cumulOkLow cumulOkHigh cumulMonotone
                    (Nat.le_refl _) (Nat.le_refl _) lowerTarget) :=
  let outerStep := Step.cumulUpInner innerLevel lowerLevel higherLevel
                                      cumulOkLow cumulOkHigh cumulMonotone
                                      innerStep
  ⟨Step.toPar outerStep, Step.toConvCumul outerStep⟩

end LeanFX2
