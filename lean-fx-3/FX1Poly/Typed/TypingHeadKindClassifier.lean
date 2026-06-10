import FX1Poly.Typed.UntypableHeadDecision

/-! # FX1Poly/Typed/TypingHeadKindClassifier — the complete decidable head-kind taxonomy (GTL-ROLE capstone)

The head-taxonomy trilogy: `TypingRoleClassifier` (#985) classified the THREE table-driven heads (formation /
intro / elim); `TypingRoleEngineBridge` (#986) proved every grown-typed head is role-bearing OR one of two
BESPOKE non-table typed heads (`gen_var`, `gen_universeCode`); `UntypableHeadDecision` (#987) gave the decidable
untypable/not split.  This file is the capstone: a SINGLE total decision procedure that partitions ALL 196
generators into their SIX typing-head kinds — the table-driven trio plus the two bespoke arms plus the
genuinely-untyped data heads.

  * **`TypingHeadKind`** — the six kinds: `formation` (genFormationPi), `introduction` (`gen_lam`/piIntro),
    `elimination` (`gen_app`/piElim), `bespokeVariable` (`gen_var`/var arm), `bespokeUniverse`
    (`gen_universeCode`/universeFormation arm), `untypable` (data constructors/eliminators).
  * **`typingHeadKindOf`** — the total classifier: check the two bespoke heads first (they are roleless yet
    typed, so must be split off before consulting `typingRoleOf`), then dispatch on `typingRoleOf`.  Every
    generator maps to EXACTLY ONE kind (it is a function); the six `headKind_*` rfl witnesses exhibit one head
    of each kind.
  * **`headKind_untypable_imp_isUntypableHead` / `headKind_untypable_of_isUntypableHead`** — the untypable kind
    is EXACTLY `isUntypableHead` (#987): both directions, a clean iff-characterization.
  * **`headKind_untypable_sound`** — the engine tie: `typingHeadKindOf g = untypable` ⟹ a cell rooted at `g`
    has no grown typing (routes the `→` through `isUntypableHead_sound`).
  * **`headKind_bespokeVariable_imp` / `headKind_bespokeUniverse_imp`** — the bespoke kinds pin their generator
    exactly (`bespokeVariable ⟹ g = gen_var`, `bespokeUniverse ⟹ g = gen_universeCode`): the two roleless-yet-
    typed heads are precisely classified, completing the taxonomy's soundness in every kind direction.

## Zero-axiom

The classifier is `if`-over-`DecidableEq Generator` + `match` on `typingRoleOf`; the corpus is `rfl`; the
untypable directions are `of_decide_eq_true` / `decide_eq_true` (both `Decidable`-cases, propext-free — NOT
`decide_eq_true_eq`) bridging `isUntypableHead`; the bespoke extractions are `by_cases` over the two head
guards plus `cases` on the `typingRoleOf` Option and the `TypingHeadKind` constructor mismatches.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The six typing-head kinds: the three table-driven roles, the two bespoke typed arms, and untypable. -/
inductive TypingHeadKind where
  | formation
  | introduction
  | elimination
  | bespokeVariable
  | bespokeUniverse
  | untypable
  deriving DecidableEq

/-- **The total head-kind classifier.**  Splits the two BESPOKE typed heads first (`gen_var`,
`gen_universeCode` — roleless yet typed, so they must be caught before the `typingRoleOf = none` ⟹ untypable
branch), then dispatches on `typingRoleOf`.  A total function: every generator gets exactly one kind. -/
def typingHeadKindOf (generator : Generator) : TypingHeadKind :=
  if generator = Generator.gen_var then .bespokeVariable
  else if generator = Generator.gen_universeCode then .bespokeUniverse
  else match typingRoleOf generator with
    | some .formation => .formation
    | some .intro => .introduction
    | some .elim => .elimination
    | none => .untypable

/-! ## The six-way partition — one head of each kind, by `rfl` -/

/-- `gen_piTyCode` (Π-FORMATION former) → `formation`. -/
theorem headKind_piTyCode : typingHeadKindOf .gen_piTyCode = .formation := rfl

/-- `gen_lam` (Π-INTRODUCTION / λ) → `introduction`. -/
theorem headKind_lam : typingHeadKindOf .gen_lam = .introduction := rfl

/-- `gen_app` (Π-ELIMINATION / application) → `elimination`. -/
theorem headKind_app : typingHeadKindOf .gen_app = .elimination := rfl

/-- `gen_var` (the bespoke `var`-arm head) → `bespokeVariable`. -/
theorem headKind_var : typingHeadKindOf .gen_var = .bespokeVariable := rfl

/-- `gen_universeCode` (the bespoke `universeFormation`-arm head) → `bespokeUniverse`. -/
theorem headKind_universeCode : typingHeadKindOf .gen_universeCode = .bespokeUniverse := rfl

/-- `gen_boolTrue` (a data constructor — proven untyped) → `untypable`. -/
theorem headKind_boolTrue : typingHeadKindOf .gen_boolTrue = .untypable := rfl

/-! ## The untypable kind is EXACTLY `isUntypableHead` (#987) -/

/-- The untypable kind implies the `isUntypableHead` decision: ruling out the two bespoke heads and the three
typed roles (the only branch yielding `untypable`) leaves precisely the `isUntypableHead` precondition. -/
theorem headKind_untypable_imp_isUntypableHead {generator : Generator}
    (kindUntypable : typingHeadKindOf generator = .untypable) :
    isUntypableHead generator = true := by
  dsimp only [typingHeadKindOf] at kindUntypable
  by_cases hVar : generator = Generator.gen_var
  · rw [if_pos hVar] at kindUntypable; cases kindUntypable
  · rw [if_neg hVar] at kindUntypable
    by_cases hUniverse : generator = Generator.gen_universeCode
    · rw [if_pos hUniverse] at kindUntypable; cases kindUntypable
    · rw [if_neg hUniverse] at kindUntypable
      cases hRole : typingRoleOf generator with
      | some role => rw [hRole] at kindUntypable; cases role <;> cases kindUntypable
      | none =>
          dsimp only [isUntypableHead]
          exact decide_eq_true ⟨hRole, hVar, hUniverse⟩

/-- The converse: an `isUntypableHead` head is classified `untypable`.  Together with the forward direction this
characterizes the untypable kind as EXACTLY the `isUntypableHead` heads. -/
theorem headKind_untypable_of_isUntypableHead {generator : Generator}
    (untypable : isUntypableHead generator = true) :
    typingHeadKindOf generator = .untypable := by
  obtain ⟨roleless, notVar, notUniverse⟩ := of_decide_eq_true untypable
  dsimp only [typingHeadKindOf]
  rw [if_neg notVar, if_neg notUniverse, roleless]

/-- ★ **The engine tie.**  A cell whose head is classified `untypable` has no grown typing — routes the
forward direction through `isUntypableHead_sound`.  The complete taxonomy's negative-soundness: the `untypable`
kind genuinely means untyped. -/
theorem headKind_untypable_sound {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (kindUntypable : typingHeadKindOf generator = .untypable)
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    False :=
  isUntypableHead_sound (headKind_untypable_imp_isUntypableHead kindUntypable) typed

/-! ## The bespoke kinds pin their generator exactly -/

/-- `bespokeVariable` is classified for EXACTLY `gen_var`. -/
theorem headKind_bespokeVariable_imp {generator : Generator}
    (kind : typingHeadKindOf generator = .bespokeVariable) : generator = Generator.gen_var := by
  by_cases hVar : generator = Generator.gen_var
  · exact hVar
  · exfalso
    dsimp only [typingHeadKindOf] at kind
    rw [if_neg hVar] at kind
    by_cases hUniverse : generator = Generator.gen_universeCode
    · rw [if_pos hUniverse] at kind; cases kind
    · rw [if_neg hUniverse] at kind
      cases hRole : typingRoleOf generator with
      | some role => rw [hRole] at kind; cases role <;> cases kind
      | none => rw [hRole] at kind; cases kind

/-- `bespokeUniverse` is classified for EXACTLY `gen_universeCode`. -/
theorem headKind_bespokeUniverse_imp {generator : Generator}
    (kind : typingHeadKindOf generator = .bespokeUniverse) :
    generator = Generator.gen_universeCode := by
  by_cases hUniverse : generator = Generator.gen_universeCode
  · exact hUniverse
  · exfalso
    dsimp only [typingHeadKindOf] at kind
    by_cases hVar : generator = Generator.gen_var
    · rw [if_pos hVar] at kind; cases kind
    · rw [if_neg hVar, if_neg hUniverse] at kind
      cases hRole : typingRoleOf generator with
      | some role => rw [hRole] at kind; cases role <;> cases kind
      | none => rw [hRole] at kind; cases kind

end FX1Poly.Typed
