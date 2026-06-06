import FX1Poly.Typed.RawTermHeadGenerator
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.RawTermChildrenUnique
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawSize

/-! # FX1Poly/Typed/SigmaCodeShape
    — raw-cell shape lemmas for Σ-type code cells

The dual of `UniverseCodeShape`'s Π section: every raw-layer shape brick a
Σ-formation typing arm needs, mirroring the Π-formation substrate.
`gen_sigmaTyCode` is structurally identical to `gen_piTyCode` (binder
shifts `[0, 1]`, `Unit` payload, two children with the codomain at `scope + 1`),
so each lemma here is the exact analog of its `piTyCodeCell` counterpart with
the head generator swapped.

Contents (all over `sigmaTyCodeCell`, the `gen_sigmaTyCode` cell defined in
`CellConstructors`):

* `headGenerator_sigmaTyCodeCell` — the head generator is `gen_sigmaTyCode`.
* `eq_sigmaTyCodeCell_of_headGenerator` — head `gen_sigmaTyCode` recovers the
  full `sigmaTyCodeCell domain codomain` shape (the destructor a `Decidable`
  Σ-formation arm needs: an `Exists` admits no large elimination, so the
  domain/codomain must come from destructuring the `[0, 1]` child spine).
* `sigmaTyCodeCell_inj` — injectivity (component extractor for the inversion's
  `sigmaFormation` arm), by `cases` on the cell equality (propext-free).
* `sigmaTyCodeCell_noStep_of_childrenNoStep` — a Σ cell with non-stepping
  children is non-stepping (the subject-no-step Σ-case crux; Σ-formation is
  a pure type former, every step descends into a child).
* `size_lt_sigmaTyCodeCell_domain` / `_codomain` — the `RawTerm.size`
  `decreasing_by` bricks a well-founded recursive Σ-formation decider needs,
  sidestepping the `RawTerm`/`RawTermChildren` mutual-`termination_by` boundary
  gap with a plain `Nat` measure (the same reason the Π decider uses it).

## Zero-axiom verification

Same tactics as the Π section: `cases` on the single-constructor `RawTerm`,
`change` (defeq, NOT `simp`), `subst`, `RawTermChildren.eq_childNil`, and the
`RawTermChildren.size_lt_childCons_*` size bricks.  No `propext` / `Quot.sound` /
`Classical`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The head generator of a Σ-type code cell is `gen_sigmaTyCode` (the cell
unfolds to `mkGen gen_sigmaTyCode _ _`, and the matcher reads the head field).
`scope` pinned by the domain code so the defeq check does not stall on a
metavariable.  Dual of `headGenerator_piTyCodeCell`. -/
theorem headGenerator_sigmaTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) :
    RawTerm.headGenerator (sigmaTyCodeCell domainCode codomainCode)
      = Generator.gen_sigmaTyCode := by
  rfl

/-- A cell whose head generator is `gen_sigmaTyCode` is a `sigmaTyCodeCell`: its
child-spine has TWO entries (domain at `scope`, codomain at `scope + 1`),
recovered by destructuring the `[0, 1]`-indexed `RawTermChildren` and collapsing
the `childNil` tail.  Dual of `eq_piTyCodeCell_of_headGenerator`. -/
theorem eq_sigmaTyCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsSigma : RawTerm.headGenerator cell = Generator.gen_sigmaTyCode) :
    ∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      cell = sigmaTyCodeCell domainCode codomainCode := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_sigmaTyCode at headIsSigma
      subst headIsSigma
      change RawTermChildren [0, 1] scope at children
      cases children with
      | childCons domainCode restChildren =>
          cases restChildren with
          | childCons codomainCode tailChildren =>
              refine ⟨domainCode, codomainCode, ?_⟩
              rw [RawTermChildren.eq_childNil tailChildren]
              rfl

/-- `sigmaTyCodeCell` is injective: two equal Σ-type code cells have equal
domains and equal codomains.  Proved by `cases` on the cell equality (the
propext-free substrate tactic `RawTermDecEq` uses to compare `mkGen` cells —
raw `injection` instead surfaces the dependent `scope` index of the `childCons`
spine).  The component extractor the `sigmaFormation` arm of the Σ inversion
needs.  Dual of `piTyCodeCell_inj`. -/
theorem sigmaTyCodeCell_inj {scope : Nat}
    {firstDomain secondDomain : RawTerm scope}
    {firstCodomain secondCodomain : RawTerm (scope + 1)}
    (cellsEqual :
      sigmaTyCodeCell firstDomain firstCodomain
        = sigmaTyCodeCell secondDomain secondCodomain) :
    firstDomain = secondDomain ∧ firstCodomain = secondCodomain := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- A Σ-type code cell with non-stepping children is itself non-stepping:
Σ-formation is a pure type former (no head redex — `Step.from_sigmaTyCode` has
only the congruence case), so any step of the cell descends into the domain or
codomain, each ruled out by hypothesis.  Dual of
`piTyCodeCell_noStep_of_childrenNoStep`; the inductive crux for the Σ-case of
subject-no-step reasoning over formation cells. -/
theorem sigmaTyCodeCell_noStep_of_childrenNoStep {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainNoStep : ∀ reduct, Step domainCode reduct → False)
    (codomainNoStep : ∀ reduct, Step codomainCode reduct → False) :
    ∀ reduct, Step (sigmaTyCodeCell domainCode codomainCode) reduct → False := by
  intro reduct stepFromSigma
  rcases Step.from_sigmaTyCode stepFromSigma with
    ⟨domainAfter, _, domainStep⟩ | ⟨codomainAfter, _, codomainStep⟩
  · exact domainNoStep domainAfter domainStep
  · exact codomainNoStep codomainAfter codomainStep

/-- The domain code is strictly smaller (by `RawTerm.size`) than the Σ-type code
cell containing it.  The `decreasing_by` obligation a well-founded recursive
Σ-formation decider discharges when it recurses into the domain.  Dual of
`size_lt_piTyCodeCell_domain`. -/
theorem size_lt_sigmaTyCodeCell_domain {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    domainCode.size < (sigmaTyCodeCell domainCode codomainCode).size := by
  dsimp only [sigmaTyCodeCell, RawTerm.size]
  exact Nat.lt_trans
    (RawTermChildren.size_lt_childCons_head (shift := 0) domainCode
      (.childCons codomainCode .childNil))
    (Nat.lt_succ_self _)

/-- The codomain code is strictly smaller (by `RawTerm.size`) than the Σ-type
code cell containing it.  Companion to `size_lt_sigmaTyCodeCell_domain`: the
codomain sits one `childCons` deeper than the domain, so the chain is one step
longer.  Dual of `size_lt_piTyCodeCell_codomain`. -/
theorem size_lt_sigmaTyCodeCell_codomain {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    codomainCode.size < (sigmaTyCodeCell domainCode codomainCode).size := by
  dsimp only [sigmaTyCodeCell, RawTerm.size]
  exact Nat.lt_trans
    (Nat.lt_trans
      (RawTermChildren.size_lt_childCons_head (shift := 1) codomainCode .childNil)
      (RawTermChildren.size_lt_childCons_tail (shift := 0) domainCode
        (.childCons codomainCode .childNil)))
    (Nat.lt_succ_self _)

end FX1Poly.Typed
