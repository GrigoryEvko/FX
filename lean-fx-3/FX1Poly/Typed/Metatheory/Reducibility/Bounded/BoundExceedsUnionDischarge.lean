import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundExceedsUnion
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundExceedsPiDischarge

/-! # FX1Poly/Typed/BoundExceedsUnionDischarge
    — the discharge core for the NATIVE union budget: monotonicity (TYTAB-4 step 2a)

The native union analogue of `BoundExceedsPiDischarge.lean`.  Ships the upward-monotonicity of
`BoundExceedsUnion` in the bound — the structural fact the union fundamental-theorem discharge
(TYTAB-4 step 3, `HasTypeUnion.fundamentalAtBoundedSucc` via `BoundExceedsUnion.rec`) and the existence
builder (step 2b, `BoundExceedsUnion.existsBound`) consume to thread a SINGLE bound through every
`HasTypeUnionOver` derivation: combine sub-bounds by SUM, then lift each sub-budget up to the sum.

Mirror of `BoundExceedsPi.monotoneInBound` (the grown twin) in every arm, specialized to the union's
SINGLE-inductive shape:

  * `ofGrown` lifts its carried grown budget through the already-shipped `BoundExceedsPi.monotoneInBound`.
  * the obligation-list arms (`formationRule` / `intro` / `elim`) lift every per-obligation sub-budget
    pointwise (`fun obligation hmem => … (premisesBudget obligation hmem)`) — the union's analogue of the
    grown telescope's head/rest split, here a map over the `∀ obligation ∈ …` premise function.
  * the two per-term universe-level gates (`formationRule`'s `formationLevelsBelowBound` over the level
    sources `level :: levels`, the `universeFormation` leaf's `belowBound`) lift their `… < bound` leaf
    pointwise through `Nat.lt_of_lt_of_le … hle`.
  * `conv` lifts both sub-budgets; `var` is a pure leaf.

SINGLE (non-mutual) — no telescope twin, because the union reflects premises into `∀ obligation ∈ …`
lists rather than a sibling inductive.

## Zero-axiom verification

Term-mode structural `match` on the budget reusing `BoundExceedsPi.monotoneInBound` and
`Nat.lt_of_lt_of_le`.  The obligation-list arms recurse on `premisesBudget obligation hmem` — a
structural sub-budget reached through the infinitary (function-typed) recursive premise, accepted by the
budget inductive's structural recursion.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The native union budget is monotone in the bound.**  `BoundExceedsUnion env bound d →
BoundExceedsUnion env higherBound d` for `bound ≤ higherBound`, by term-mode structural `match` on the
budget: the `ofGrown` arm lifts its grown budget through `BoundExceedsPi.monotoneInBound`; the
obligation-list arms (`formationRule` / `intro` / `elim`) lift every per-obligation sub-budget; the two
universe-level gates lift their `… < bound` leaf via `Nat.lt_of_lt_of_le … hle`; the `conv` arm lifts
both sub-budgets; `var` / `universeFormation` are leaves.  The native analogue of
`BoundExceedsPi.monotoneInBound`; SINGLE because the union is a single inductive. -/
theorem BoundExceedsUnion.monotoneInBound {bundle : TypingTableBundle} {profile : PolyProfile}
    {env : Nat → Nat} {bound higherBound : Nat} (hle : bound ≤ higherBound) {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {d : HasTypeUnionOver bundle profile context subject classifier}
    (budget : BoundExceedsUnion env bound d) : BoundExceedsUnion env higherBound d :=
  match budget with
  | .ofGrown hostBudget => .ofGrown (BoundExceedsPi.monotoneInBound hle hostBudget)
  | .formationRule context generator payload children rule levels carrier level flag isFormationRule
      formationLevelsBelowBound premisesBudget =>
      .formationRule context generator payload children rule levels carrier level flag isFormationRule
        (fun levelExpr hmem =>
          Nat.lt_of_lt_of_le (formationLevelsBelowBound levelExpr hmem) hle)
        (fun obligation hmem => BoundExceedsUnion.monotoneInBound hle (premisesBudget obligation hmem))
  | .intro context generator rule args params level0 level1 flag isIntro sideHolds premisesBudget =>
      .intro context generator rule args params level0 level1 flag isIntro sideHolds
        (fun obligation hmem => BoundExceedsUnion.monotoneInBound hle (premisesBudget obligation hmem))
  | .elim context generator rule args params level0 level1 flag isElim premisesBudget =>
      .elim context generator rule args params level0 level1 flag isElim
        (fun obligation hmem => BoundExceedsUnion.monotoneInBound hle (premisesBudget obligation hmem))
  | .conv (converts := convertsProof) levelExpr flag subjectBudget reclassifierBudget =>
      .conv (converts := convertsProof) levelExpr flag
        (BoundExceedsUnion.monotoneInBound hle subjectBudget)
        (BoundExceedsUnion.monotoneInBound hle reclassifierBudget)
  | .var context index => .var context index
  | .universeFormation context levelExpr flag belowBound =>
      .universeFormation context levelExpr flag (Nat.lt_of_lt_of_le belowBound hle)

end FX1Poly.Typed
