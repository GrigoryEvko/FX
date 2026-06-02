import FX1Poly.Typed.ClassifierLevelSpike
import FX1Poly.Typed.RouteAObstruction

/-! # FX1Poly/Typed/SNStrategy
    — SN-005: the strong-normalization strategy decision gate (committed decision record)

The SN-001 → SN-004 spike arc asked one make-or-break question: can the syntactic strong-normalization
proof be carried by a *reducibility* (Tait/Kripke logical-relations) model whose level is the term's own
CLASSIFIER universe level `LevelExpr.denote`, rather than an external `Nat` "fuel"?  The arc:

* **SN-001** (`RouteAObstruction`) pinned *why the fuel model is dead at its base*: at fuel `0` the universe
  membership predicate is EMPTY, so a universe-DOMAIN Π type `Π(x:Type@e).C` is reducible at fuel `0` for
  EVERY codomain `C`, VACUOUSLY — its fuel-`0` candidate is the trivial `fun _ => True`.  The degenerate
  `0 ↔ 1` base of any level-irrelevance argument is therefore unbridgeable WITHIN the fuel model.
* **SN-002** (`ClassifierLevelDiagnosis`) found the denote-keyed setup COHERENT: `denote (lsucc e) = denote e + 1`
  aligns with the universe arm's `+1` discipline on the nose, and re-keying is an INSTANTIATION of the
  shipped level-polymorphic `FundamentalConclusionLevelIndexed`, not a rebuild.
* **SN-003** (`ClassifierLevelMeasure`) landed the predicative well-founded measure the denote-keyed recursion
  descends on: `denote e < denote (lsucc e)` (strict, at the universe-decode step), the non-increasing
  `lmax` former-component bounds, and the NON-degenerate neutral base (`variableCell_reducibleTypeAtZero`) —
  unlike the SN-001 universe-code vacuity, neutral types genuinely inhabit the base level.
* **SN-004** (`ClassifierLevelSpike`) closed the make-or-break: the universe-DOMAIN Π former CLOSES at
  classifier-level semantics.  The constant-codomain case is the shipped
  `universeDomainPi_reducibleAllLevels`; the dependent case reduces EXACTLY to domain member-extension
  (`piTypeOfDomainMemberExtension`), supplied by the SN-003 denote-WF induction hypothesis — the fuel-`0`
  empty-membership wall does NOT reappear.

## DECISION: **GO** (locked 2026-06-02)

The classifier-universe-level / validity-derivation-indexed reducibility model is VIABLE.  The premise that
the fuel model could not discharge — universe-DOMAIN Π-formation at the degenerate base — closes under the
denote-keyed predicative measure at the classifier level, with the neutral fragment as a genuinely inhabited
base.  No premise failed; the make-or-break premise closed at the universe-decode level via SN-003's strict
`denote` decrease.

## LOCKED STRATEGY (three legs; this fixes their roles, ending the historical Route-A/Route-B oscillation)

* **Leg 2 — PRIMARY syntactic SN path: the validity-relation route (Route B).**  Phase 1 (SN-007 .. SN-030)
  builds the leveled validity context `ValidTyping`, the classifier-level reducible environment, the
  level-indexed fundamental theorem, and the leveling bridge `HasTypeDescPi → ValidTyping → reducible`.  This
  is the critical path to `HasTypeDescPi Γ t T → IsStronglyNormalizing t` (SN-043) and onward to canonicity
  (SN-047 .. SN-049) and consistency (SN-050).  Route A (single-fuel all-levels/member-extension bootstrap)
  is the documented dead fragment SN-001 pins — KEPT, not deleted, as the negative witness justifying this
  choice.
* **Leg 1 — INDEPENDENT SECOND proof: BKS internal sconing (Phase 5, SN-083 .. SN-110).**  A reducibility
  candidate IS a sconing witness (`reducibilityScone`, SN-092), so the categorical SN obtained from the
  glued computability (SN-102) is a genuinely independent derivation of the SAME theorem — the
  "sconing-is-enough" thesis (SN-110), not a fallback-of-necessity.
* **Leg 3 — CROSS-CHECK: Makkai/Forest word equality (Phase 6, SN-111 .. SN-139).**  CONSUMES the typed SN
  (SN-131) to present the certified fragment as a convergent rewrite system; an independent decision of
  convertibility used to triangulate (SN-137 .. SN-139), per the corrected polycell.md §2.3 "Path A primary,
  Path B cross-check" reconciliation.

The NO-GO branch — promote sconing to primary, demote Route B to a documented dead fragment — is therefore
NOT taken.  Every subsequent SN-* task's relevance/priority is conditioned on this verdict: the Phase-1
validity-route tasks (SN-007 .. SN-054) are on the critical path; SN-006 (Adjedj derivation-indexed LogRel)
stays a fallback contingency, relevant only for the impredicative `limax` fragment where SN-003's predicative
`denote` decrease does not apply.

## The decision as a checked object

`lockedStrategyGoCertificate` is the GO verdict in typechecked form: for the SAME universe-domain Π former, it
exhibits BOTH (a) genuine reducibility at ALL classifier levels (the live model, SN-004) AND (b) only the
VACUOUS fuel-`0` reducibility with the trivial `fun _ => True` candidate (the dead model, SN-001).  Holding
both for one former is exactly the justification to lock the classifier-level (live) route over the fuel
(dead) route — the decision is anchored to shipped theorems, not left implicit in prose.

## Zero-axiom verification

The certificate is the `And.intro` of two shipped zero-axiom theorems (`universeDomainPi_reducibleAllLevels`
+ `universeDomainPiTrivialCandidateAtZero`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **SN-005 decision-gate certificate (GO, locked 2026-06-02).**  The strong-normalization strategy is
locked to the classifier-universe-level (denote-keyed) validity-relation route as the PRIMARY syntactic SN
path, with BKS sconing as the independent second proof and Makkai word-equality as the cross-check (see the
module docstring).  This theorem records the GO rationale as a checked object: for one and the same
universe-DOMAIN Π former `Π(x:Type@domainLevel).Type@codomainLevel`, BOTH hold —

* the LIVE classifier-level model makes it genuinely reducible at ALL levels
  (`universeDomainPi_reducibleAllLevels`, SN-004), while
* the DEAD fuel-`0` model makes it reducible only VACUOUSLY, with the trivial `fun _ => True` candidate
  (`universeDomainPiTrivialCandidateAtZero`, SN-001).

The same former being genuinely-all-levels-reducible yet only trivially-fuel-`0`-reducible is precisely why
Route B (classifier-level) is locked over the fuel route. -/
theorem lockedStrategyGoCertificate {scope : Nat}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllLevels
        (piTyCodeCell (universeCodeCell domainLevel flag)
          (RawTerm.weaken (universeCodeCell codomainLevel flag) : RawTerm (scope + 1)))
      ∧ ReducibleTypeAt 0
          (piTyCodeCell (universeCodeCell domainLevel flag)
            (RawTerm.weaken (universeCodeCell codomainLevel flag) : RawTerm (scope + 1)))
          (fun _functionTerm => True) :=
  ⟨universeDomainPi_reducibleAllLevels domainLevel codomainLevel flag,
   universeDomainPiTrivialCandidateAtZero domainLevel flag
     (RawTerm.weaken (universeCodeCell codomainLevel flag))⟩

/-! ## SN-021 design decision (the generic `genFormationPi` arm for `ValidTyping`) — pinned 2026-06-02

SN-021 adds the GENERIC table-driven former arm to `ValidTyping` (over `typingRuleDescOf`), so the leveled
relation matches `HasTypeDescPi`'s cascade-free former coverage (Π / Σ become instances of one arm). The
discharge target is the shipped `fundamentalGenFormationFormerLevelIndexed` (FundamentalLevelIndexed.lean),
whose key hypothesis is
`telescopeFundamental : ∀ σ (env : ReducibleEnvVec contextLevels context σ) shapeEq,
  TelescopeReducible flag 0 levels.length σ levels (shapeEq ▸ children)`.

OBSTRUCTION. The model `HasTypeDescPi.fundamentalVectorFromFormation` obtains that telescope IH FOR FREE from
the MUTUAL recursor `HasTypeDescPi.rec` (`motive_2 := IsTelescopeReducibleAtVector` over the mutual
`DescTelescopePi`). `ValidTyping` is a SINGLE (non-mutual) inductive, so `ValidTyping.rec` produces no
telescope IH — the genFormationPi arm cannot synthesize `telescopeFundamental`.

ADOPTED DESIGN (revised 2026-06-02 — option (b), the semantic-premise ctor; LANDED). The
`ValidTyping.genFormationPi` ctor carries exactly `fundamentalGenFormationFormerLevelIndexed`'s premises: the
structural `premises : DescTelescopePi …` PLUS the `telescopeFundamental` hypothesis (the children telescope is
reducible under every closing reducible environment). `ValidTyping.fundamental`'s new arm is then a one-liner
to `fundamentalGenFormationFormerLevelIndexed` — which still does the REAL former-membership work (dispatch
Π/Σ, invert the two-child spine, build the former's universe membership via `toPiMember`/`toSigmaMember`), so
the arm is non-vacuous. The reversal of last week's instinct is justified: `ValidTyping` is an Abel VALIDITY
relation (semantic — see its own docstring), so a former case that ASSUMES component reducibility and DERIVES
former reducibility is exactly standard logical-relations reasoning, not a wart. The ctor is NON-recursive in
`ValidTyping`, so it needed NO mutual refactor, is trivially strictly-positive, landed atomically, and the
shipped `ValidTyping` / `ValidTyping.fundamental` gates now cover it zero-axiom.

WHY NOT the mutual `ValidTelescope` (last tick's plan). It would keep every former arm syntactic (children as
`ValidTyping` sub-derivations lifted by a mutual recursor) — cleaner in principle, but a heavy core-inductive
change (mutual inductive + mutual fundamental, with the mutual-recursor propext/Quot.sound risks). Option (b)
achieves the SAME GOAL (cascade-free former coverage over `typingRuleDescOf`) atomically and zero-axiom, so the
mutual route is UNNECESSARY. The bridge SN-023 supplies `telescopeFundamental` for a constructed
genFormationPi from the children's own fundamentals (recursively bridge children → `ValidTyping`, then apply
`ValidTyping.fundamental`), so option (b) is bridge-compatible.

STILL REJECTED. Carrying the bare `DescTelescopePi` premise and deriving `telescopeFundamental` INSIDE the arm
— CIRCULAR: it needs the unconditional `HasTypeDescPi` fundamental, the very thing still under assembly.
-/

end FX1Poly.Typed
