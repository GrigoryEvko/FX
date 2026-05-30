import FX1Poly.Typed.HasTypeHonesty
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

This is the raw destructor that `Decidable IsType` (#303) needs: to confirm a
candidate type is a universe code — and apply `HasType.universeFormation` — the
decision procedure must turn `headGenerator = gen_universeCode` into a concrete
`universeCodeCell e flag`.

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
`Decidable IsType` (#303) needs — to case on a `gen_var` cell and recover its
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

/-- The head generator of a variable cell is `gen_var`.  `scope` is pinned by the
index's `Fin scope` type. -/
theorem headGenerator_variableCell {scope : Nat} (index : Fin scope) :
    RawTerm.headGenerator (variableCell index) = Generator.gen_var := by
  rfl

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
`RawTermChildren` and collapsing the `childNil` tail.  The destructor `Decidable`
typing of Π-formation (#443) needs to turn `headGenerator = gen_piTyCode` into a
concrete `piTyCodeCell domain codomain`. -/
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

/-- `piTyCodeCell` is injective: two equal Π-type code cells have equal domains
and equal codomains.  Proved by `cases` on the cell equality — the propext-free
substrate tactic that `RawTermDecEq` uses to compare `mkGen` cells (raw
`injection` instead surfaces the dependent `scope` index of the `childCons`
spine).  `cases` unifies the two `childCons … childNil` spines, substituting the
second domain/codomain by the first, leaving `⟨rfl, rfl⟩`.

The component extractor the `piFormation` arm of `HasType.inversionPiCode` (#443)
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

This is the inductive crux that #443 stage 2's `subjectHasNoStep` Π-case will call
directly (`exact piTyCodeCell_noStep_of_childrenNoStep IH_domain IH_codomain`),
turning the load-bearing invariant from "typed subject is a non-stepping LEAF"
into "typed subject is NORMAL" — a piTyCodeCell is not a leaf but is still normal
when its (typed ⇒ normal) children are.  Stated at the raw `Step` layer so it
lands non-breaking, before the `piFormation` arm cascades. -/
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
Π-formation decider (#443 stage 2) discharges when it recurses into the domain.

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
