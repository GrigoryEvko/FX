import FX1Poly.Typed.StaticTypingSoundness

/-! # FX1Poly/Typed/ClassifierRefinement — the union classifier STRICTLY refines the grown untypability decision (HON-8)

Two honest classifiers sit over the generator table:

  * `isUntypableHead g` (`UntypableHeadDecision`) — the GROWN-only untypability decision: `g` is roleless in the
    three grown rule tables (`typingRoleOf = none`) and neither bespoke typed head.  It sees ONLY the grown
    engine (`HasTypeDescPi`).
  * `hasSomeTypingRule g` (`TypedBySomeEngine`) — the FULL-UNION static-typing classifier: `g` is typed by SOME
    of the 17 engines, grown OR any of the standalone data intro/elim/flat/base engines.

HON-5 shipped the bridge `hasSomeTypingRule_false_imp_isUntypableHead`: a head the UNION reports reserved is
grown-untypable.  This file sharpens that into a STRICT REFINEMENT statement, answering "is the honest union
classifier just the grown decision in disguise, or does it genuinely see more?":

  * **`hasSomeTypingRule_refines_isUntypableHead`** — the refinement direction (cite HON-5): union-reserved
    (`hasSomeTypingRule = false`) ⟹ grown-untypable (`isUntypableHead = true`).
  * **`grownTypable_imp_unionTyped`** — the containment / contrapositive: grown-typable (`isUntypableHead =
    false`) ⟹ union-typed (`hasSomeTypingRule = true`).  Every head the grown decision rules in is also
    union-typed — the union's typed-set CONTAINS the grown-typable set.
  * **`boolTrue_grownUntypableButUnionTyped`** — the STRICT witness: `gen_boolTrue` is grown-untypable
    (`isUntypableHead = true` — no grown rule-table row) yet union-typed (`hasSomeTypingRule = true` — the
    standalone `HasTypeDescDataIntro` engine types it).  The containment is PROPER.
  * **`hasSomeTypingRuleStrictlyRefinesUntypableHead`** — ★ the bundle: refinement + containment + strict
    witness.  The union classifier strictly refines the grown decision — the standalone data engines genuinely
    EXTEND typability beyond the grown core; the honest classifier is not a re-skin of `isUntypableHead`.

This is the structural honesty fact that the 203-table's typability is the UNION of all engines, and that union is
non-trivially larger than any single engine's reach.

(The strict witness is currently `gen_boolTrue`; should a future folding of data-intro rows into the grown table
(`introRuleDescOf`) make it grown-roleful, the `rfl` here would fail the build, prompting a re-witness with a
head still typed only by a standalone engine — e.g. a flat-table former, disjoint from the grown table per the
shipped cross-table no-confusion.)

## Zero-axiom

The refinement is the shipped HON-5 bridge verbatim; the containment is `cases` on the union Bool + `rw` of the
bridge + `Bool.noConfusion` (propext-free); the strict witness is `⟨rfl, rfl⟩` (both classifiers compute on
`gen_boolTrue`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Refinement direction.**  A head the union classifier reports reserved (`hasSomeTypingRule = false`) is
grown-untypable (`isUntypableHead = true`).  This IS the shipped HON-5 bridge — the union's reserved-verdict
refines (entails) the grown untypability decision. -/
theorem hasSomeTypingRule_refines_isUntypableHead {g : Generator}
    (reserved : hasSomeTypingRule g = false) : isUntypableHead g = true :=
  hasSomeTypingRule_false_imp_isUntypableHead g reserved

/-- **Containment (contrapositive).**  A grown-typable head (`isUntypableHead = false`) is union-typed
(`hasSomeTypingRule = true`): the union's typed-set contains the grown-typable set.  Bool-contraposition of the
refinement — were the union to report it reserved, the bridge would force `isUntypableHead = true`, contradicting
the hypothesis. -/
theorem grownTypable_imp_unionTyped {g : Generator}
    (grownTypable : isUntypableHead g = false) : hasSomeTypingRule g = true := by
  cases hUnion : hasSomeTypingRule g with
  | true => rfl
  | false =>
      rw [hasSomeTypingRule_false_imp_isUntypableHead g hUnion] at grownTypable
      exact Bool.noConfusion grownTypable

/-- **The STRICT witness.**  `gen_boolTrue` is grown-untypable (`isUntypableHead = true` — it has no row in any
grown rule table, so it is roleless and non-bespoke) yet union-typed (`hasSomeTypingRule = true` — the standalone
`HasTypeDescDataIntro` engine types it as a bool constructor).  The refinement's converse therefore FAILS: being
grown-untypable does NOT entail union-reserved, because the standalone engines see what the grown decision
cannot. -/
theorem boolTrue_grownUntypableButUnionTyped :
    isUntypableHead .gen_boolTrue = true ∧ hasSomeTypingRule .gen_boolTrue = true :=
  ⟨rfl, rfl⟩

/-- **★ The union classifier STRICTLY refines the grown untypability decision.**  Three facts: (1) union-reserved
⟹ grown-untypable (refinement); (2) grown-typable ⟹ union-typed (containment); (3) a grown-untypable head the
union nonetheless types (`gen_boolTrue` — strictness).  Together: the union's typed-set strictly contains the
grown-typable set, so the standalone data engines genuinely EXTEND typability — the honest 203-table classifier is
not the grown decision in disguise. -/
theorem hasSomeTypingRuleStrictlyRefinesUntypableHead :
    (∀ g : Generator, hasSomeTypingRule g = false → isUntypableHead g = true) ∧
    (∀ g : Generator, isUntypableHead g = false → hasSomeTypingRule g = true) ∧
    (∃ g : Generator, isUntypableHead g = true ∧ hasSomeTypingRule g = true) :=
  ⟨fun g reserved => hasSomeTypingRule_false_imp_isUntypableHead g reserved,
   fun _ grownTypable => grownTypable_imp_unionTyped grownTypable,
   ⟨.gen_boolTrue, rfl, rfl⟩⟩

end FX1Poly.Typed
