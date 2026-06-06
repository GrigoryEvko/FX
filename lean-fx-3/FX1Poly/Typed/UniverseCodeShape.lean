import FX1Poly.Typed.RawTermHeadGenerator
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.RawTermChildrenUnique
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawSize

/-! # FX1Poly/Typed/UniverseCodeShape
    — raw-cell inversion for universe-code cells

`eq_universeCodeCell_of_headGenerator` recovers the full `universeCodeCell`
shape from the head generator alone: any cell whose head is `gen_universeCode`
*is* `universeCodeCell e flag` for the `e`, `flag` in its payload.  Two facts
collapse the cell: its nullary child-spine is `childNil`
(`RawTermChildren.eq_childNil`, since `gen_universeCode.binderShifts = []`), and
its payload is a `LevelExpr x UniverseFlag` pair (Prod-eta is definitional), so
once the spine is `childNil` the reconstruction is by reflexivity.

This is the raw destructor `Decidable (IsTypeDesc Γ T)` needs: to confirm a candidate type
is a universe code — and apply `HasTypeDesc.universeFormation` — the decision procedure
must turn `headGenerator = gen_universeCode` into a concrete `universeCodeCell e
flag`.

## Zero-axiom verification

`cases` on the single-constructor `RawTerm`, then `change` (defeq, NOT `simp`)
exposes `generator = gen_universeCode`, `subst`, and
`RawTermChildren.eq_childNil` collapses the spine.  No `propext` / `Quot.sound` /
`Classical`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A cell whose head generator is `gen_universeCode` is a `universeCodeCell`:
its nullary child-spine is `childNil` (`eq_childNil`) and its payload is the
`(level, flag)` pair. -/
theorem eq_universeCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsUniverseCode :
      RawTerm.headGenerator cell = Generator.gen_universeCode) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      cell = universeCodeCell levelExpr flag := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_universeCode at headIsUniverseCode
      subst headIsUniverseCode
      refine ⟨payload.1, payload.2, ?_⟩
      rw [RawTermChildren.eq_childNil children]
      rfl

/-- A cell whose head generator is `gen_var` is a `variableCell`: the same
nullary child-spine collapse (`RawTermChildren.eq_childNil`, since
`gen_var.binderShifts = []`) as the universe-code case, with the cell's payload
serving directly as the de Bruijn index.  This is the second raw destructor
`Decidable (IsTypeDesc Γ T)` needs — to case on a `gen_var` cell and recover its
index as data (`Exists` admits no large elimination, so the index must come from
destructuring the cell, not from an existential witness). -/
theorem eq_variableCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsVariable :
      RawTerm.headGenerator cell = Generator.gen_var) :
    ∃ index : Fin scope, cell = variableCell index := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_var at headIsVariable
      subst headIsVariable
      refine ⟨payload, ?_⟩
      rw [RawTermChildren.eq_childNil children]
      rfl

/-- The head generator of a universe-code cell is `gen_universeCode` (the cell
unfolds to `mkGen gen_universeCode _ _`, and the matcher reads the head field).
Stated with `scope` pinned so the defeq check does not stall on a metavariable.
The dual destructor `eq_universeCodeCell_of_headGenerator` is the converse. -/
theorem headGenerator_universeCodeCell {scope : Nat} (levelExpr : LevelExpr)
    (flag : UniverseFlag) :
    RawTerm.headGenerator (universeCodeCell levelExpr flag : RawTerm scope)
      = Generator.gen_universeCode := by
  rfl

/-- **The pure structural universe-code dichotomy.**  Every `RawTerm` either IS a universe code
(`∃ levelExpr flag, term = universeCodeCell …`) or provably is NOT one (`∀ levelExpr flag, ≠`).  Decided by
head-generator inspection (`DecidableEq Generator`, no Classical): head `= gen_universeCode` recovers the cell
via `eq_universeCodeCell_of_headGenerator`; otherwise any equality to a universe code would force the head to be
`gen_universeCode` (`headGenerator_universeCodeCell`), a contradiction.

This is the routing primitive the totalBridge assembly (SN-027/#662) needs: the term arms
`TotalBridgeConclusion.var` / `.piElim` carry a "classifier is not a universe code" hypothesis, and the
assembly discharges it for the TERM case while routing the neutral-TYPE case (a type variable whose looked-up
type IS a universe code, or a type-family application whose result IS a universe code — exactly the subjects
whose motive conjunct-2 level-flexibility is unsatisfiable) to the pinned reclassifier handler.  The
split is this dichotomy applied to `context.lookup index` resp. `subst0 codomainCode argument`. -/
theorem RawTerm.isUniverseCodeOrNot {scope : Nat} (term : RawTerm scope) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag), term = universeCodeCell levelExpr flag) ∨
    (∀ (levelExpr : LevelExpr) (flag : UniverseFlag), term ≠ universeCodeCell levelExpr flag) := by
  by_cases headIsUniverseCode : RawTerm.headGenerator term = Generator.gen_universeCode
  · exact Or.inl (eq_universeCodeCell_of_headGenerator headIsUniverseCode)
  · refine Or.inr (fun levelExpr flag termEqUniverseCode => headIsUniverseCode ?_)
    rw [termEqUniverseCode]
    exact headGenerator_universeCodeCell levelExpr flag

/-- The head generator of a variable cell is `gen_var`.  `scope` is pinned by the
index's `Fin scope` type. -/
theorem headGenerator_variableCell {scope : Nat} (index : Fin scope) :
    RawTerm.headGenerator (variableCell index) = Generator.gen_var := by
  rfl

/-- **The pure structural variable dichotomy.**  Every `RawTerm` either IS a variable cell
(`∃ index, term = variableCell index`) or provably is NOT one (`∀ index, ≠`).  Decided by head-generator
inspection (`DecidableEq Generator`, no Classical), exactly like `RawTerm.isUniverseCodeOrNot`.

The second routing primitive the totalBridge conv arm (SN-027/#662) needs.  A conv reclassifier is typed at a
universe code, so it is a TYPE; the conv consumer must produce it at `subjectLevel + 1`.  A NON-variable type
code (universe code / Π / Σ / generic former) is LEVEL-FLEXIBLE (valid at every positive level —
`universeFormation_isLevelFlexible` etc.), so it re-derives at `subjectLevel + 1` and routes through
`ValidTyping.convWithLevelFlexibleReclassifier`.  A VARIABLE reclassifier is PINNED to `contextLevels index`
(`ValidTyping.var`), so it routes through `validTypingBridgeConvPinnedReclassifier`, which needs the leveling
equation `contextLevels index = subjectLevel + 1`.  This dichotomy is what separates the two routes —
`isUniverseCodeOrNot` does not, because a Π/Σ former is "not a universe code" yet still flexible. -/
theorem RawTerm.isVariableOrNot {scope : Nat} (term : RawTerm scope) :
    (∃ index : Fin scope, term = variableCell index) ∨
    (∀ index : Fin scope, term ≠ variableCell index) := by
  by_cases headIsVariable : RawTerm.headGenerator term = Generator.gen_var
  · exact Or.inl (eq_variableCell_of_headGenerator headIsVariable)
  · refine Or.inr (fun index termEqVariable => headIsVariable ?_)
    rw [termEqVariable]
    exact headGenerator_variableCell index

/-- The head generator of a Π-type code cell is `gen_piTyCode`.  `scope` pinned by
the domain code. -/
theorem headGenerator_piTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) :
    RawTerm.headGenerator (piTyCodeCell domainCode codomainCode)
      = Generator.gen_piTyCode := by
  rfl

/-- A cell whose head generator is `gen_piTyCode` is a `piTyCodeCell`: unlike the
nullary universe/variable cells, its child-spine has TWO entries (domain at
`scope`, codomain at `scope + 1`), recovered by destructuring the `[0, 1]`-indexed
`RawTermChildren` and collapsing the `childNil` tail.  Decidable Π-formation typing
turns `headGenerator = gen_piTyCode` into a concrete `piTyCodeCell domain codomain`
with this. -/
theorem eq_piTyCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsPi : RawTerm.headGenerator cell = Generator.gen_piTyCode) :
    ∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      cell = piTyCodeCell domainCode codomainCode := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_piTyCode at headIsPi
      subst headIsPi
      change RawTermChildren [0, 1] scope at children
      cases children with
      | childCons domainCode restChildren =>
          cases restChildren with
          | childCons codomainCode tailChildren =>
              refine ⟨domainCode, codomainCode, ?_⟩
              rw [RawTermChildren.eq_childNil tailChildren]
              rfl

/-- `universeCodeCell` is injective: two equal universe-code cells have equal
levels and equal flags.  Proved by `cases` on the cell equality — the same
propext-free substrate tactic as `piTyCodeCell_inj`; here the children are
`childNil` (no dependent spine), so `cases` simply unifies the `gen_universeCode
(levelExpr, flag)` payloads.  Feeds the no-Type-in-Type honesty probe (#442): a
universe classified by itself would force `levelExpr = levelExpr.lsucc`, refuted
by `LevelExpr.ne_lsucc_self`. -/
theorem universeCodeCell_inj {scope : Nat}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (cellsEqual :
      (universeCodeCell firstLevel firstFlag : RawTerm scope)
        = universeCodeCell secondLevel secondFlag) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- `piTyCodeCell` is injective: two equal Π-type code cells have equal domains
and equal codomains.  Proved by `cases` on the cell equality — the propext-free
substrate tactic that `RawTermDecEq` uses to compare `mkGen` cells (raw
`injection` instead surfaces the dependent `scope` index of the `childCons`
spine).  `cases` unifies the two `childCons … childNil` spines, substituting the
second domain/codomain by the first, leaving `⟨rfl, rfl⟩`.

The component extractor the `piFormation` arm of `HasTypeDesc.inversionPiCode`
needs: it aligns the inducted arm's own `domainCode` / `codomainCode` with the
`piTyCodeCell` targeted by the inversion. -/
theorem piTyCodeCell_inj {scope : Nat}
    {firstDomain secondDomain : RawTerm scope}
    {firstCodomain secondCodomain : RawTerm (scope + 1)}
    (cellsEqual :
      piTyCodeCell firstDomain firstCodomain
        = piTyCodeCell secondDomain secondCodomain) :
    firstDomain = secondDomain ∧ firstCodomain = secondCodomain := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- A Π-type code cell with non-stepping children is itself non-stepping: Π-
formation is a pure type former (no head redex — `Step.from_piTyCode` has only the
congruence case), so any step of the cell descends into the domain or codomain,
each ruled out by hypothesis.

This is the inductive crux for the Π-case of subject-no-step reasoning
(`exact piTyCodeCell_noStep_of_childrenNoStep IH_domain IH_codomain`): the
load-bearing invariant is "typed subject is NORMAL", not "typed subject is a
non-stepping LEAF" — a piTyCodeCell is not a leaf but is still normal when its
(typed ⇒ normal) children are.  Stated at the raw `Step` layer. -/
theorem piTyCodeCell_noStep_of_childrenNoStep {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainNoStep : ∀ reduct, Step domainCode reduct → False)
    (codomainNoStep : ∀ reduct, Step codomainCode reduct → False) :
    ∀ reduct, Step (piTyCodeCell domainCode codomainCode) reduct → False := by
  intro reduct stepFromPi
  rcases Step.from_piTyCode stepFromPi with
    ⟨domainAfter, _, domainStep⟩ | ⟨codomainAfter, _, codomainStep⟩
  · exact domainNoStep domainAfter domainStep
  · exact codomainNoStep codomainAfter codomainStep

/-- The domain code is strictly smaller (by `RawTerm.size`) than the Π-type code
cell containing it.  The `decreasing_by` obligation a well-founded recursive
Π-formation decider discharges when it recurses into the domain.

Proved by composing the spine brick `RawTermChildren.size_lt_childCons_head`
(`domain.size < (childCons domain _).size`) with `Nat.lt_succ_self` (the cell's
size is the spine's size plus one), after `dsimp` unfolds `piTyCodeCell` and
`RawTerm.size` to the literal `childCons` spine.  A `RawTerm.size` Nat measure —
NOT structural recursion — to sidestep the `RawTerm`/`RawTermChildren` mutual
`termination_by` boundary gap (the same reason the certifier uses fuel). -/
theorem size_lt_piTyCodeCell_domain {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    domainCode.size < (piTyCodeCell domainCode codomainCode).size := by
  dsimp only [piTyCodeCell, RawTerm.size]
  exact Nat.lt_trans
    (RawTermChildren.size_lt_childCons_head (shift := 0) domainCode
      (.childCons codomainCode .childNil))
    (Nat.lt_succ_self _)

/-- The codomain code is strictly smaller (by `RawTerm.size`) than the Π-type
code cell containing it.  Companion to `size_lt_piTyCodeCell_domain`: the
`decreasing_by` obligation when the Π-formation decider recurses into the
codomain (at `scope + 1`).

The codomain sits one `childCons` deeper than the domain, so the chain is one
step longer: head-of-tail (`codomain.size < (childCons codomain childNil).size`)
then tail-of-head (`(childCons codomain _).size < (childCons domain _).size`)
then `Nat.lt_succ_self`. -/
theorem size_lt_piTyCodeCell_codomain {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    codomainCode.size < (piTyCodeCell domainCode codomainCode).size := by
  dsimp only [piTyCodeCell, RawTerm.size]
  exact Nat.lt_trans
    (Nat.lt_trans
      (RawTermChildren.size_lt_childCons_head (shift := 1) codomainCode .childNil)
      (RawTermChildren.size_lt_childCons_tail (shift := 0) domainCode
        (.childCons codomainCode .childNil)))
    (Nat.lt_succ_self _)

end FX1Poly.Typed
