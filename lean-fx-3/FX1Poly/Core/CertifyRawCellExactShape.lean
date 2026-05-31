import FX1Poly.Core.CertifyRawCellExact

/-! # Foundation/PolyCell/Core/CertifyRawCellExactShape — behavioral shape lemmas

Ships **behavioral shape pin lemmas** for the exact certifier.

## Context: why `_sound` alone is insufficient

`certifyRawCellExact?_sound` at `CertifyRawCellExactSound.lean` is a
TYPE-LEVEL observation: it proves `cert.certifiedCell.raw = rawCell`
by `rfl`, because the certifier's raw-INDEXED return type
`Except _ (CertifiedRawCell profile scope rawCell)` pins the
rawCell at the type level — any inhabitant of that type satisfies
the equality, whether produced by the certifier or by any other
means.

That is structurally correct and useful (witnesses no laundering of
the input raw), but it does NOT exercise the certifier's actual
*behavioral dispatch*.  Its `_accepted` hypothesis is unused (the
proof is `rfl`, not a case analysis on the acceptance result).

A regression that breaks the certifier's dispatch logic —
e.g., the `.identityCell` arm erroneously returning the
`.generatingCell`-shaped output — could pass `_sound` unchanged,
because the type system still rejects malformed shapes.  The
soundness theorem observes the type-level guarantee without testing
the behavioral computation.

## This file: shape pin lemmas

This file ships behavioral shape pin lemmas that **DO inspect the
acceptance hypothesis** via case analysis on the recursive call's
result.  Each lemma pins a SPECIFIC VALUE (not a type-level
property) of the certified output, derived from the dispatcher's
match-arm body.

The pattern:

  1. State the lemma with the acceptance hypothesis.
  2. Use a `dispatcherEq` rewrite (a `rfl`-bridge that exposes the
     dispatcher's match body) to manually expose the inner match
     without using `unfold` on the mutual recursive definition
     (`unfold` on mutual would leak `Quot.sound` per
     `feedback_lean_unfold_mutual_quot_sound`).
  3. Case-analyze on the recursive call's result via
     `cases hRec : certifyRawCellExactFueled? ... base`.
  4. In the `.error` branch, derive contradiction (the dispatcher
     produces `.error _` but `accepted` says `.ok cert`).
  5. In the `.ok certBase` branch, inject the `accepted`'s `.ok`
     equality through `injection` to extract a `cert = ⟨...⟩`
     equation, then rewrite the goal.

The result: the lemma's proof crucially uses `accepted` (no
underscore prefix; the hypothesis is consumed), and a regression
that broke the dispatcher's identityCell arm would fail to
discharge the case split.

## Coverage

This file ships three behavioral shape lemmas:

  * `certifyRawCellExact?_identityCell_boundary` — pins
    `cert.boundary = (base, base)` for `.identityCell base` input.
  * `certifyRawCellExact?_verticalComposite_accepted_implies_inner_certs`
    — pins that an accepted `.verticalComposite first second` forces
    both inner recursive certifications to succeed.
  * `certifyRawCellExact?_generatingCell_accepted_implies_inner_certs`
    — the same "implies inner certs" pin for `.generatingCell`.

The shape lemma family complements:
  * `certifyRawCellExact?_sound` — type-level no-laundering.
  * `certifyRawCellExact?_compH_rejects` — horizontalComposite
    always rejects with `.unsupportedCompH` (behavioral shape pin
    for the reject branch).

Together they convert the soundness story from "type-level
observation" → "type-level + behavioral dispatch pins per
constructor".

## Zero-axiom verification

All shape lemmas pass `#print axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Pattern catalogued

The `rfl`-bridge technique used in `dispatcherEq` is reusable for
similar shape lemmas where direct `unfold` on a mutual recursive
def would leak axioms.  See
`feedback_lean_unfold_mutual_quot_sound.md` for the general
prohibition and `feedback_lean_curried_match_brecOn.md` for the
related match-form caveat.
-/

namespace FX1Poly.Core

/-- **Behavioral shape pin: identityCell boundary.**

If the certifier accepts an `identityCell base` input, the resulting
certified cell's boundary is exactly `(base, base)` — the pair of
endpoints produced by the dispatcher's identityCell arm:

```
| .identityCell base =>
    match certifyRawCellExactFueled? fuel' scope base with
    | .error rejection => .error rejection
    | .ok certBase =>
        .ok ⟨certBase.sort, CellBoundary.endpoints base base, ...⟩
```

The lemma is **substantively non-vacuous**: the proof inspects the
acceptance hypothesis via case analysis on the recursive call's
result.  In the `.error` branch the dispatcher returns `.error _`,
contradicting `accepted = .ok cert`.  In the `.ok certBase` branch
the dispatcher returns `.ok ⟨certBase.sort, .endpoints base base,
...⟩`, and injection through the Except.ok equality pins
`cert.boundary = .endpoints base base = (base, base)`.

A regression that broke the identityCell dispatch (e.g., by emitting
a different boundary value) would invalidate this lemma. -/
theorem certifyRawCellExact?_identityCell_boundary
    {profile : PolyProfile} {scope : Nat} (base : RawCell scope)
    {cert : CertifiedRawCell profile scope (.identityCell base)}
    (accepted :
      certifyRawCellExact? (profile := profile) scope (.identityCell base)
        = Except.ok cert) :
    cert.boundary = (base, base) := by
  -- `rfl`-bridge: rewrite the top-level wrapper into its expanded
  -- dispatcher form.  This avoids `unfold certifyRawCellExactFueled?`
  -- (mutual recursive def — would leak Quot.sound) while still
  -- exposing the inner match for case analysis.
  have dispatcherEq :
      certifyRawCellExact? (profile := profile) scope (.identityCell base)
      = (match certifyRawCellExactFueled? (base.size + 1) scope base with
         | .error rejection => .error rejection
         | .ok certBase =>
             .ok ⟨certBase.sort, CellBoundary.endpoints base base,
                  PolyCell.identityCell certBase.certifiedCell⟩) := rfl
  rw [dispatcherEq] at accepted
  -- Case-analyze on the recursive call's result.
  cases hRec : certifyRawCellExactFueled? (base.size + 1) scope base with
  | error rejection =>
    -- The dispatcher's identityCell arm returns `.error rejection`,
    -- contradicting `accepted = .ok cert`.
    rw [hRec] at accepted
    cases accepted
  | ok certBase =>
    -- The dispatcher returns `.ok ⟨certBase.sort, .endpoints base
    -- base, ...⟩`.  Inject through the Except.ok equality to extract
    -- the structural equation on cert.
    rw [hRec] at accepted
    injection accepted with eqCert
    rw [← eqCert]
    -- After rewrite, the goal becomes
    -- `⟨certBase.sort, .endpoints base base, ...⟩.boundary = (base, base)`,
    -- which reduces by structural-projection + `@[reducible]`
    -- expansion of `CellBoundary.endpoints` to
    -- `(base, base) = (base, base)`, closed automatically by the
    -- definitional unfolding through the rewrite.

/-- Concrete smoke for the identityCell shape lemma: at scope 0 with
a unit-termBase base, certification accepts the identityCell and the
boundary pin lemma derives the expected `(base, base)` equation.

This smoke witnesses that the lemma's statement is operationally
useful (a concrete acceptance instance + the boundary extraction
produces a concrete equality), not merely propositionally true. -/
example :
    let baseCell : RawCell 0 :=
      .termBase (.mkGen .gen_unit () .childNil)
    ∀ (cert :
        CertifiedRawCell fxProfile 0
          (.identityCell baseCell)),
      certifyRawCellExact?
          (profile := fxProfile)
          0 (.identityCell baseCell) = Except.ok cert →
      cert.boundary = (baseCell, baseCell) := by
  intro baseCell cert accepted
  exact certifyRawCellExact?_identityCell_boundary baseCell accepted

/-! ## "implies inner certs" shape pins

Beyond `_identityCell_boundary` (which pins a concrete boundary
value of the certified output), the dispatcher's two
**two-recursion** arms — `.verticalComposite` and `.generatingCell`
— get a different but equally substantive class of behavioral pin:
**"if accepted, both recursive sub-certifications must have
succeeded"**.

### Why not the boundary?

The natural follow-on pin would be `..._verticalComposite_boundary` —
pinning what the outer endpoints of an accepted vertical composite
are.  But the dispatcher's `.verticalComposite` arm delegates to
`buildVerticalCompositeExact?`, whose output's boundary depends on
the helper's internal sort reconciliation and `Eq.rec` transport.
Extracting a concrete boundary value would require either:

  * A sibling boundary shape pin for `buildVerticalCompositeExact?`
    itself (lifts the helper's output into a pinnable shape).
  * A direct unfold of the helper's body inside the proof (defeats
    the modularity of the helper as an externally-defined operation).

The same applies to `.generatingCell` via `buildGeneratingCellExact?`.

Phase B sidesteps that machinery by pinning a SHALLOWER but still
substantive behavioral property: **the outer dispatcher's two-stage
recursion is not short-circuited**.

### What "implies inner certs" pins

Given acceptance of the outer call, the proof inspects the dispatcher's
explicit `match certifyRawCellExactFueled? ... scope first/source` /
`match certifyRawCellExactFueled? ... scope second/target` cases.
Each `.error` branch causes the outer call to immediately return
`.error` (contradicting acceptance), so an accepting outer call
forces both inner calls to land on `.ok`.

The lemma extracts the inner cert witnesses as existentials and pins
their stored values.  Concretely it ships:

  * `∃ certFirst, certifyRawCellExactFueled? ... scope first
                  = Except.ok certFirst`
  * `∃ certSecond, certifyRawCellExactFueled? ... scope second
                   = Except.ok certSecond`

A regression that "short-circuited" the dispatcher — for instance, by
emitting `.ok` without performing the recursion — would falsify this
lemma because the witnesses would be unobtainable.

### Why the proofs close by `rfl`

Each `cases hRec : foo with | ok certCorrespondent => ...` arm
substitutes `foo` with `Except.ok certCorrespondent` in the goal.
The existential body `foo = Except.ok certCorrespondent` thus reduces
to `Except.ok certCorrespondent = Except.ok certCorrespondent`, closed
by `rfl`.  The `.error` arms close by `cases accepted` after
rewriting (the dispatcher's match arm returns `.error`, contradicting
`accepted`).

### Pattern reusability

This pattern applies to every dispatcher arm that performs N recursive
sub-certifications then delegates to a helper.  The dispatcher's
N+1 levels of match (one per recursion, plus the helper call) collapse
to N `cases hRec` + 1 `exact ⟨rfl, ..., rfl⟩` line after the recursion
phase. -/

/-- **Behavioral shape pin: verticalComposite implies inner certs.**

If the certifier accepts `.verticalComposite first second`, then the
dispatcher's recursive certifications of both `first` and `second`
must have succeeded.

A regression that short-circuited the recursion (returning `.ok` without
actually recursing) would invalidate this lemma. -/
theorem certifyRawCellExact?_verticalComposite_accepted_implies_inner_certs
    {profile : PolyProfile} {scope : Nat}
    (first second : RawCell scope)
    {cert : CertifiedRawCell profile scope (.verticalComposite first second)}
    (accepted :
      certifyRawCellExact? (profile := profile) scope
        (.verticalComposite first second) = Except.ok cert) :
    (∃ certFirst : CertifiedRawCell profile scope first,
      certifyRawCellExactFueled?
        (first.size + second.size + 1) scope first = Except.ok certFirst) ∧
    (∃ certSecond : CertifiedRawCell profile scope second,
      certifyRawCellExactFueled?
        (first.size + second.size + 1) scope second = Except.ok certSecond) := by
  have dispatcherEq :
      certifyRawCellExact? (profile := profile) scope
        (.verticalComposite first second)
      = (match certifyRawCellExactFueled?
              (first.size + second.size + 1) scope first with
         | .error rejection => .error rejection
         | .ok certFirst =>
           match certifyRawCellExactFueled?
                  (first.size + second.size + 1) scope second with
           | .error rejection => .error rejection
           | .ok certSecond =>
               match hFirstDim : first.dim with
               | 0 => .error .badVerticalBoundary
               | parentDim + 1 =>
                   if hDimEq : first.dim = second.dim then
                     let hSecondDim : second.dim = parentDim + 1 :=
                       hDimEq.symm.trans hFirstDim
                     buildVerticalCompositeExact? parentDim first second
                       hFirstDim hSecondDim certFirst certSecond
                   else
                     .error .badVerticalBoundary) := rfl
  rw [dispatcherEq] at accepted
  cases hRec1 : certifyRawCellExactFueled?
                  (first.size + second.size + 1) scope first with
  | error rejection =>
    rw [hRec1] at accepted
    cases accepted
  | ok certFirst =>
    rw [hRec1] at accepted
    dsimp only at accepted
    cases hRec2 : certifyRawCellExactFueled?
                    (first.size + second.size + 1) scope second with
    | error rejection =>
      rw [hRec2] at accepted
      cases accepted
    | ok certSecond =>
      exact ⟨⟨certFirst, rfl⟩, ⟨certSecond, rfl⟩⟩

/-- **Behavioral shape pin: generatingCell implies inner certs.**

If the certifier accepts `.generatingCell ruleId source target`, then
the dispatcher's recursive certifications of both `source` and
`target` must have succeeded.

Symmetric to `_verticalComposite_accepted_implies_inner_certs`.  The
two-stage recursion structure is identical (source then target,
delegating to `buildGeneratingCellExact?` for boundary
reconciliation), so the proof shape transfers verbatim. -/
theorem certifyRawCellExact?_generatingCell_accepted_implies_inner_certs
    {profile : PolyProfile} {scope : Nat}
    (ruleId : Nat) (source target : RawCell scope)
    {cert : CertifiedRawCell profile scope (.generatingCell ruleId source target)}
    (accepted :
      certifyRawCellExact? (profile := profile) scope
        (.generatingCell ruleId source target) = Except.ok cert) :
    (∃ certSource : CertifiedRawCell profile scope source,
      certifyRawCellExactFueled?
        (source.size + target.size + 1) scope source = Except.ok certSource) ∧
    (∃ certTarget : CertifiedRawCell profile scope target,
      certifyRawCellExactFueled?
        (source.size + target.size + 1) scope target = Except.ok certTarget) := by
  have dispatcherEq :
      certifyRawCellExact? (profile := profile) scope
        (.generatingCell ruleId source target)
      = (match certifyRawCellExactFueled?
              (source.size + target.size + 1) scope source with
         | .error rejection => .error rejection
         | .ok certSource =>
           match certifyRawCellExactFueled?
                  (source.size + target.size + 1) scope target with
           | .error rejection => .error rejection
           | .ok certTarget =>
               buildGeneratingCellExact? ruleId source target
                 certSource certTarget) := rfl
  rw [dispatcherEq] at accepted
  cases hRec1 : certifyRawCellExactFueled?
                  (source.size + target.size + 1) scope source with
  | error rejection =>
    rw [hRec1] at accepted
    cases accepted
  | ok certSource =>
    rw [hRec1] at accepted
    dsimp only at accepted
    cases hRec2 : certifyRawCellExactFueled?
                    (source.size + target.size + 1) scope target with
    | error rejection =>
      rw [hRec2] at accepted
      cases accepted
    | ok certTarget =>
      exact ⟨⟨certSource, rfl⟩, ⟨certTarget, rfl⟩⟩

end FX1Poly.Core
