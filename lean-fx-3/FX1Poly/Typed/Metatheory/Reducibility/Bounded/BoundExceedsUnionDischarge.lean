import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundExceedsUnion

/-! # FX1Poly/Typed/BoundExceedsUnionDischarge
    — the discharge core for the NATIVE union budget: monotonicity (TYTAB-4 step 2a)

The native union analogue of `BoundExceedsPiDischarge.lean`.  Ships the upward-monotonicity of
`BoundExceedsUnion` in the bound — the structural fact the union fundamental-theorem discharge
(TYTAB-4 step 3, `HasTypeUnion.fundamentalAtBoundedSucc` via `BoundExceedsUnion.rec`) and the existence
builder (step 2b, `BoundExceedsUnion.existsBound`) consume to thread a SINGLE bound through every
`HasTypeUnionOver` derivation: combine sub-bounds by SUM, then lift each sub-budget up to the sum.

Mirror of `BoundExceedsPi.monotoneInBound` (the grown twin) in every arm, specialized to the union's
SINGLE-inductive shape:

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
budget: the obligation-list arms (`formationRule` / `intro` / `elim`) lift every per-obligation sub-budget;
the two universe-level gates lift their `… < bound` leaf via `Nat.lt_of_lt_of_le … hle`; the `conv` arm lifts
both sub-budgets; `var` / `universeFormation` are leaves.  The native analogue of
`BoundExceedsPi.monotoneInBound`; SINGLE because the union is a single inductive. -/
theorem BoundExceedsUnion.monotoneInBound {bundle : TypingTableBundle} {profile : PolyProfile}
    {env : Nat → Nat} {bound higherBound : Nat} (hle : bound ≤ higherBound) {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {d : HasTypeUnionOver bundle profile context subject classifier}
    (budget : BoundExceedsUnion env bound d) : BoundExceedsUnion env higherBound d :=
  match budget with
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

/-- **A bound exceeding the denotation of every level in a list.**  `∃ bound, ∀ lv ∈ levels, denote lv env <
bound`, by structural recursion on the list: the nil case is vacuous (`0`); the cons case takes
`denote head env + tailBound + 1` and discharges each membership — the head via `Nat.lt_succ_of_le`, a tail
member by lifting the recursive bound through `Nat.lt_of_lt_of_le`.  `BoundExceedsUnion.existsBound`'s
`formationRule` arm instantiates this at `level :: levels` to produce the `formationLevelsBelowBound` gate.
Zero-axiom: SUM bounds (`Nat.le_add_left` / `Nat.le_add_right`) + `List.Mem` constructor `match` (no `mem_cons`
iff lemma), no `Nat.le_max`. -/
theorem existsLevelSourceBound (env : Nat → Nat) :
    (levels : List LevelExpr) →
    ∃ bound, ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound
  | [] => ⟨0, by intro levelExpr hmem; cases hmem⟩
  | head :: tail => by
      obtain ⟨tailBound, tailBelow⟩ := existsLevelSourceBound env tail
      refine ⟨LevelExpr.denote head env + tailBound + 1, fun levelExpr hmem => ?_⟩
      cases hmem with
      | head => exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
      | tail _ memTail =>
          exact Nat.lt_of_lt_of_le (tailBelow levelExpr memTail)
            (Nat.le_succ_of_le (Nat.le_add_left _ _))

/-- **A single bound exceeding the budget of every obligation in a list.**  Turns the per-obligation pointwise
existentials (the recursor's IH for a `∀ obligation ∈ list, HasTypeUnionOver …` premise) into ONE shared bound:
`∃ bound, ∀ ob hmem, BoundExceedsUnion env bound (premisesHold ob hmem)`, by structural recursion on the
obligation list.  The cons case sums the head's bound with the tail's shared bound and lifts each per-obligation
budget up to the sum through `BoundExceedsUnion.monotoneInBound`; `premisesHold` / `premisesExists` are rebuilt
for the tail by lifting `ob ∈ tail` to `ob ∈ head :: tail` via `List.Mem.tail`.  The union analogue of the grown
telescope's head/rest bound combination, here over the obligation `List`.  Zero-axiom: SUM bounds + `List.Mem`
constructor `match` + `monotoneInBound`, no `mem_cons` iff lemma, no `Nat.le_max`. -/
theorem existsSharedObligationBound {bundle : TypingTableBundle} {profile : PolyProfile} {env : Nat → Nat} :
    (obligations : List (ElimObligation profile)) →
    (premisesHold : ∀ obligation, obligation ∈ obligations →
        HasTypeUnionOver bundle profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation (hmem : obligation ∈ obligations),
        ∃ bound, BoundExceedsUnion env bound (premisesHold obligation hmem)) →
    ∃ bound, ∀ obligation (hmem : obligation ∈ obligations),
        BoundExceedsUnion env bound (premisesHold obligation hmem)
  | [], _, _ => ⟨0, by intro obligation hmem; cases hmem⟩
  | head :: tail, premisesHold, premisesExists => by
      obtain ⟨headBound, headBudget⟩ := premisesExists head List.mem_cons_self
      obtain ⟨tailBound, tailBudget⟩ := existsSharedObligationBound tail
        (fun obligation hmem => premisesHold obligation (List.mem_cons_of_mem head hmem))
        (fun obligation hmem => premisesExists obligation (List.mem_cons_of_mem head hmem))
      refine ⟨headBound + tailBound, fun obligation hmem => ?_⟩
      cases hmem with
      | head => exact BoundExceedsUnion.monotoneInBound (Nat.le_add_right _ _) headBudget
      | tail _ memTail =>
          exact BoundExceedsUnion.monotoneInBound (Nat.le_add_left _ _) (tailBudget obligation memTail)

/-- **Every native union derivation has a budget (TYTAB-4 step 2b).**  `∃ bound, BoundExceedsUnion env bound d`
by `induction d` over the six `HasTypeUnionOver` arms — the native analogue of `BoundExceedsPi.existsBound`:

  * `formationRule` combines the obligation-list shared bound (`existsSharedObligationBound`) with the level-source
    bound (`existsLevelSourceBound` at `level :: levels`) by SUM, lifting each per-obligation budget through
    `monotoneInBound` and discharging the `formationLevelsBelowBound` gate from the level bound — BUNDLE-GENERIC,
    reading `level` / `levels` straight off the node;
  * `intro` / `elim` take the obligation-list shared bound directly (no universe-level gate);
  * `conv` sums the subject + reclassifier IH bounds and lifts both;
  * `var` needs no fuel (bound `0`); `universeFormation` picks `denote (lsucc levelExpr) env + 1` and discharges
    its leaf gate by `Nat.lt_succ_self`.

Recursive arms take the SUM of sub-bounds (`Nat.le_add_left` / `Nat.le_add_right`, never `Nat.le_max`) and lift
each sub-budget through `BoundExceedsUnion.monotoneInBound`.  Zero-axiom: `induction` on the indexed inductive
with a clean recursive motive (free-variable indices, no index-unification equations), the two List helpers, and
SUM bounds.  Feeds the native FT dispatch (TYTAB-4 step 3, `HasTypeUnion.fundamentalAtBoundedSucc` via
`BoundExceedsUnion.rec`) toward the native-SN gate-1 keystone of TYTAB-2-FT (#1697). -/
theorem BoundExceedsUnion.existsBound {bundle : TypingTableBundle} {profile : PolyProfile}
    {env : Nat → Nat} {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (d : HasTypeUnionOver bundle profile context subject classifier) :
    ∃ bound, BoundExceedsUnion env bound d := by
  induction d with
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold premisesIH =>
      obtain ⟨obligationBound, obligationBudget⟩ :=
        existsSharedObligationBound _ premisesHold premisesIH
      obtain ⟨levelBound, levelBelow⟩ := existsLevelSourceBound env (level :: levels)
      exact ⟨obligationBound + levelBound,
        .formationRule context generator payload children rule levels carrier level flag isFormationRule
          (fun levelExpr hmem =>
            Nat.lt_of_lt_of_le (levelBelow levelExpr hmem) (Nat.le_add_left levelBound obligationBound))
          (fun obligation hmem =>
            BoundExceedsUnion.monotoneInBound (Nat.le_add_right obligationBound levelBound)
              (obligationBudget obligation hmem))⟩
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold premisesIH =>
      obtain ⟨obligationBound, obligationBudget⟩ :=
        existsSharedObligationBound _ premisesHold premisesIH
      exact ⟨obligationBound,
        .intro context generator rule args params level0 level1 flag isIntro sideHolds obligationBudget⟩
  | elim context generator rule args params level0 level1 flag isElim premisesHold premisesIH =>
      obtain ⟨obligationBound, obligationBudget⟩ :=
        existsSharedObligationBound _ premisesHold premisesIH
      exact ⟨obligationBound,
        .elim context generator rule args params level0 level1 flag isElim obligationBudget⟩
  | conv levelExpr flag typed converts reclassifierTyped subjectIH reclassifierIH =>
      obtain ⟨subjectBound, subjectBudget⟩ := subjectIH
      obtain ⟨reclassifierBound, reclassifierBudget⟩ := reclassifierIH
      exact ⟨subjectBound + reclassifierBound,
        .conv (converts := converts) levelExpr flag
          (BoundExceedsUnion.monotoneInBound (Nat.le_add_right subjectBound reclassifierBound) subjectBudget)
          (BoundExceedsUnion.monotoneInBound (Nat.le_add_left reclassifierBound subjectBound)
            reclassifierBudget)⟩
  | var context index => exact ⟨0, .var context index⟩
  | universeFormation context levelExpr flag =>
      exact ⟨LevelExpr.denote levelExpr.lsucc env + 1,
        .universeFormation context levelExpr flag (Nat.lt_succ_self _)⟩

end FX1Poly.Typed
