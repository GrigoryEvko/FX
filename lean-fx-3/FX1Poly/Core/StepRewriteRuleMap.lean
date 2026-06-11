import FX1Poly.Core.Step
import FX1Poly.Core.RawCellCode

/-! # FX1Poly/Core/StepRewriteRuleMap
    — each FX reduction as a rewrite rule over the term-code word monoid

`RawCellWordEncoding` encodes the RawCell composite layer into the dim-1 rule-id free monoid (the derivation
word: WHICH rewrite rules a path applies).  This file encodes the complementary half of the Leg-3 bridge: each FX `Step`
(a single beta / iota / cong reduction on `RawTerm`, `Step.lean`) becomes a REWRITE RULE on the term-code word
monoid — the rule endpoints.  Together they describe a reduction fully: a derivation word `[r1, r2, ...]` taking
the term word `encode(a)` to `encode(b)`.

## The encoding is the shipped faithful serializer

The bridge `encode` is the SHIPPED `RawTerm.toCode` (`RawCellCode.lean`): `mkGen g p c` maps to
`g.toNat :: payloadToNat g p :: c.toCode` — head generator tag (the polygraph tag), the payload
(variable index / level), then the children's codes.  It is FAITHFUL (records tags AND payloads), unlike the
shape-only `encodeRuleWord`.  This file adds the two facts the rule map needs:

* `toCode_mkGen` — the encoder exposes its head tag (a `rfl` computation rule over the shipped mutual `toCode`).
* `toCode_ne_nil` — every term code is non-empty (it always begins with the head generator tag), so every
  induced rule has non-empty sides (a genuine, non-degenerate rule).

## The Step → rule map and its generated system

* `FxTermRewriteRule` — a rewrite rule over the term-code word alphabet (`List Nat`): the FX-faithful analogue
  of `OmegacEWord`'s `OmegacERewriteRule` (which is over the abstract 2-letter scaffold alphabet — the wrong
  target for the 203-generator kernel).
* `Step.inducedRewriteRule` — the map: a reduction `Step redex reduct` induces the rule
  `⟨redex.toCode, reduct.toCode⟩`.
* `Step.inducedRewriteRule_leftHandSide` / `_rightHandSide` (`rfl`) and `_leftHandSide_ne_nil` /
  `_rightHandSide_ne_nil` (non-degeneracy) — the rule faithfully records the reduction's endpoints.
* `fxStepSystem` — the rule SYSTEM the FX reductions generate: a rule is in it iff it is the code-pair of some
  FX reduction (at some scope).  This is the `fxSystem` that the bridge soundness (`Step a b ⟹
  RewritesOneStep fxSystem (encode a) (encode b)`) ranges over.
* `Step.inducedRewriteRule_mem_fxStepSystem` — every FX reduction's induced rule is a rule of the system (the
  map lands in the generated system by construction).

The soundness `Step a b ⟹ RewritesOneStep fxSystem a.toCode b.toCode`, the inversion, and the
`Conv ↔ ConvertibleModulo` bridge need a `RewritesOneStep` infrastructure over `List Nat` and the
substitution-tracking analysis; they remain gated on the typed-SN critical path per `core_raw_sn_false_natrec`
(raw `Step` is not globally terminating).  Here we build only the rule map and its generated system.

## Zero-axiom verification

`toCode_mkGen` is `rfl`; `toCode_ne_nil` is `cases term` + `List.cons_ne_nil` (the mkGen code is defeq to a cons);
the rule projections are `rfl`; the system membership is an existential intro with `rfl` witnesses.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The shipped term encoder exposes its head generator tag: `toCode` of a `mkGen` begins with the generator's
table tag, then the payload code, then the children's codes (a `rfl` computation rule over the mutual `toCode`). -/
theorem toCode_mkGen {scope : Nat} (generator : Generator)
    (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope) :
    (RawTerm.mkGen generator payload children).toCode
      = generator.toNat :: payloadToNat generator scope payload :: children.toCode := rfl

/-- **Every term code is non-empty**: it always begins with the head generator tag.  So every rule a reduction
induces has non-empty sides — a genuine, non-degenerate rewrite rule. -/
theorem toCode_ne_nil {scope : Nat} (term : RawTerm scope) : term.toCode ≠ [] := by
  cases term with
  | mkGen generator payload children => exact List.cons_ne_nil _ _

/-- A **rewrite rule over the term-code word alphabet** (`List Nat`): the FX-faithful analogue of the abstract
scaffold's `OmegacERewriteRule`.  The two sides are the codes of the reduction's redex and reduct. -/
structure FxTermRewriteRule where
  /-- The pattern replaced by the rewrite (the redex's term code). -/
  leftHandSide : List Nat
  /-- The replacement the rewrite installs (the reduct's term code). -/
  rightHandSide : List Nat

/-- **The Step → rule map**: an FX reduction `Step redex reduct` induces the rewrite rule
`⟨redex.toCode, reduct.toCode⟩` over the term-code word monoid. -/
def Step.inducedRewriteRule {scope : Nat} {redex reduct : RawTerm scope}
    (_step : Step redex reduct) : FxTermRewriteRule where
  leftHandSide := redex.toCode
  rightHandSide := reduct.toCode

/-- The induced rule's left side is the redex's code. -/
theorem Step.inducedRewriteRule_leftHandSide {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    step.inducedRewriteRule.leftHandSide = redex.toCode := rfl

/-- The induced rule's right side is the reduct's code. -/
theorem Step.inducedRewriteRule_rightHandSide {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    step.inducedRewriteRule.rightHandSide = reduct.toCode := rfl

/-- The induced rule's left side is non-empty (non-degenerate rule). -/
theorem Step.inducedRewriteRule_leftHandSide_ne_nil {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    step.inducedRewriteRule.leftHandSide ≠ [] :=
  toCode_ne_nil redex

/-- The induced rule's right side is non-empty (non-degenerate rule). -/
theorem Step.inducedRewriteRule_rightHandSide_ne_nil {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    step.inducedRewriteRule.rightHandSide ≠ [] :=
  toCode_ne_nil reduct

/-- **The FX rewriting system**: the set of rules the FX reductions generate.  A rule belongs to the system iff
it is the term-code pair of some FX reduction (at some scope).  This is the `fxSystem` over which the bridge
soundness `Step a b ⟹ RewritesOneStep fxStepSystem a.toCode b.toCode` ranges. -/
def fxStepSystem (rule : FxTermRewriteRule) : Prop :=
  ∃ (scope : Nat) (redex reduct : RawTerm scope),
    Step redex reduct
      ∧ rule.leftHandSide = redex.toCode
      ∧ rule.rightHandSide = reduct.toCode

/-- **Every FX reduction's induced rule is a rule of the system** — the Step → rule map lands in the generated
system by construction (the membership witness is the reduction itself). -/
theorem Step.inducedRewriteRule_mem_fxStepSystem {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) : fxStepSystem step.inducedRewriteRule :=
  ⟨scope, redex, reduct, step, rfl, rfl⟩

end FX1Poly.Core
