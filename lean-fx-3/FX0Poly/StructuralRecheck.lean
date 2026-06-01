import FX0Poly.Checker

/-!
# FX0Poly — per-node structural re-check rule (the trusted-core admission step)

The minimal external checker (`FX0Poly`) re-checks a certificate tree node-by-node.  This file ships the
single-node ADMISSION RULE — the building block the whole re-checker rests on — together with its
soundness-and-completeness characterisation.

The rule is deliberately NON-RECURSIVE: the recursive descent over a certificate tree is the driver's job;
`recheckNode` decides ONE node, given (a) the expected arity of the node's generator tag (looked up in the
checker's tag→arity model, `none` for an unknown/forbidden tag) and (b) the verdicts already computed for
the node's children.  Keeping the per-node rule recursion-free makes its soundness a closed, structural
equivalence — no fuel, no well-founded recursion, no termination obligation — and is exactly the
Metamath-Zero discipline: the trusted core is a tiny total decision, auditable at a glance.

## Zero-axiom verification

`recheckNode` is a total `match` + `if` on `Bool`; the soundness theorem is a direct computational equation
against the deciding Boolean — no `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Each declaration is gated by a per-declaration `#assert_no_axioms` in
`FX1PolyAudit/AuditFX0Poly.lean`; FX0Poly itself stays free of the audit macro, preserving its independence
from the FX1Poly stack (the trust point — FX0Poly is auditable without trusting FX1Poly).
-/

namespace FX0Poly

/-- The per-node structural admission rule.  A node re-checks as `accepted` exactly when its generator
tag has a known expected arity, the supplied child count matches that arity, and every child already
re-checked as `accepted`; otherwise the node is `malformed`.  `expectedArity = none` models an unknown or
forbidden generator tag (the checker's tag→arity model rejects it outright). -/
def recheckNode (expectedArity : Option Nat) (childVerdicts : List CheckVerdict) : CheckVerdict :=
  match expectedArity with
  | none => CheckVerdict.malformed
  | some arity =>
    if childVerdicts.length == arity && childVerdicts.all CheckVerdict.wasAccepted then
      CheckVerdict.accepted
    else
      CheckVerdict.malformed

/-- An unknown generator tag (`none` arity) is rejected as structurally malformed — never accepted. -/
theorem recheckNode_none_malformed (childVerdicts : List CheckVerdict) :
    recheckNode none childVerdicts = CheckVerdict.malformed := rfl

/-- The accepting verdict of an `accepted`/`malformed` branch select is exactly the deciding `Bool`:
`accepted.wasAccepted = true`, `malformed.wasAccepted = false`. -/
theorem wasAccepted_ite_accepted_malformed (condition : Bool) :
    (if condition then CheckVerdict.accepted else CheckVerdict.malformed).wasAccepted = condition := by
  cases condition <;> rfl

/-- **Soundness of the per-node admission rule (known tag), as a computational characterization.**  For a
known generator tag of expected arity `arity`, the node's acceptance `Bool` EQUALS the conjunction "the
child count matches the arity AND every child was accepted".  Stated as a `Bool` equality (not a `Prop`
`Iff`) so it stays `propext`-free — the natural form for a Metamath-Zero checker that computes verdicts as
`Bool`s: no false accepts (the right side is `false` on a mismatched arity or any non-accepted child) and no
false rejects (the right side is `true` on a well-formed node).  This single equation is the trusted core's
whole admission criterion at one node. -/
theorem recheckNode_some_wasAccepted_eq (arity : Nat) (childVerdicts : List CheckVerdict) :
    (recheckNode (some arity) childVerdicts).wasAccepted =
      (childVerdicts.length == arity && childVerdicts.all CheckVerdict.wasAccepted) := by
  show (if childVerdicts.length == arity && childVerdicts.all CheckVerdict.wasAccepted then
          CheckVerdict.accepted else CheckVerdict.malformed).wasAccepted =
    (childVerdicts.length == arity && childVerdicts.all CheckVerdict.wasAccepted)
  exact wasAccepted_ite_accepted_malformed _

/-- Non-vacuity: a well-formed node (arity 2, two accepted children) is accepted. -/
theorem recheckNode_smoke_accepted :
    recheckNode (some 2) [CheckVerdict.accepted, CheckVerdict.accepted] = CheckVerdict.accepted := rfl

/-- Non-vacuity: a wrong-arity node (arity 2, one child) is rejected as malformed. -/
theorem recheckNode_smoke_arityMismatch :
    recheckNode (some 2) [CheckVerdict.accepted] = CheckVerdict.malformed := rfl

/-- Non-vacuity: a node with a rejected child is rejected, even at matching arity. -/
theorem recheckNode_smoke_childRejected :
    recheckNode (some 2) [CheckVerdict.accepted, CheckVerdict.disagreed] = CheckVerdict.malformed := rfl

end FX0Poly
