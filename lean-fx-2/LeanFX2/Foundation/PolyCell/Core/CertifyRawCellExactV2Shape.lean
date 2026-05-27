import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2

/-! # Foundation/PolyCell/Core/CertifyRawCellExactV2Shape — behavioral shape lemmas

V2-fix-1 (2026-05-27).  Ships **behavioral shape pin lemmas** that
discharge Agent 3's H3.1 finding from the V2 falsification audit.

## Context: why `_sound` alone is insufficient

`certifyRawCellExactV2?_sound` (V2-L1cert.10, #165) at
`CertifyRawCellExactV2Sound.lean` is a TYPE-LEVEL observation: it
proves `cert.certifiedCell.raw = rawCell` by `rfl`, because the
certifier's raw-INDEXED return type
`Except _ (CertifiedRawCellV2 profile scope rawCell)` pins the
rawCell at the type level — any inhabitant of that type satisfies
the equality, whether produced by the certifier or by any other
means.

That is structurally correct and useful (witnesses no laundering of
the input raw), but it does NOT exercise the certifier's actual
*behavioral dispatch*.  The `_accepted` hypothesis is unused (the
proof is `rfl`, not a case analysis on the acceptance result).

A future regression that breaks the certifier's dispatch logic —
e.g., the `.identityCell` arm erroneously returning the
`.generatingCell`-shaped output — could ship past `_sound`
unchanged, because the type system still rejects malformed shapes.
The shipped soundness theorem observes the type-level guarantee
without testing the behavioral computation.

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
     `cases hRec : certifyRawCellExactV2Fueled? ... base`.
  4. In the `.error` branch, derive contradiction (the dispatcher
     produces `.error _` but `accepted` says `.ok cert`).
  5. In the `.ok certBase` branch, inject the `accepted`'s `.ok`
     equality through `injection` to extract a `cert = ⟨...⟩`
     equation, then rewrite the goal.

The result: the lemma's proof crucially uses `accepted` (no
underscore prefix; the hypothesis is consumed), and a regression
that broke the dispatcher's identityCell arm would fail to
discharge the case split.

## Coverage strategy (this commit + follow-ups)

This V2-fix-1 commit ships the FIRST behavioral shape lemma:

  * `certifyRawCellExactV2?_identityCell_boundary` — pins
    `cert.boundary = (base, base)` for `.identityCell base` input.

Follow-up V2-fix-1 commits will extend coverage to:

  * `..._verticalComposite_boundary` — pins the outer endpoints
    from the `buildVerticalCompositeExactV2?` dispatch (more
    complex: the helper's internals must be unfolded).
  * `..._generatingCell_boundary` — pins `(source, target)` from
    the `buildGeneratingCellExactV2?` dispatch.
  * `..._termBase_sort` — pins `cert.sort = generator.cellSort`
    via the gen-arm `.ok ⟨generator.cellSort, .trivial, ...⟩`
    construction.

The shape lemma family complements:
  * `certifyRawCellExactV2?_sound` (#165) — type-level no-laundering.
  * `certifyRawCellExactV2?_compH_rejects` (#166) — horizontalComposite
    always rejects with `.unsupportedCompH` (behavioral shape pin
    for the reject branch).
  * `_termBase_*`, `_generatingCell_*`, `_verticalComposite_*`
    (future V2-fix-1 commits) — behavioral shape pins for the ok
    branches.

Together they convert the soundness story from "type-level
observation" → "type-level + behavioral dispatch pins per
constructor" — exactly the labor that V2's cascade-deletion
deferred and that V2-fix-* incrementally pays down.

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

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Behavioral shape pin: identityCell boundary.**

If the certifier accepts an `identityCell base` input, the resulting
certified cell's boundary is exactly `(base, base)` — the pair of
endpoints produced by the dispatcher's identityCell arm:

```
| .identityCell base =>
    match certifyRawCellExactV2Fueled? fuel' scope base with
    | .error rejection => .error rejection
    | .ok certBase =>
        .ok ⟨certBase.sort, CellBoundaryV2.endpoints base base, ...⟩
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
theorem certifyRawCellExactV2?_identityCell_boundary
    {profile : PolyProfile} {scope : Nat} (base : RawCellV2 scope)
    {cert : CertifiedRawCellV2 profile scope (.identityCell base)}
    (accepted :
      certifyRawCellExactV2? (profile := profile) scope (.identityCell base)
        = Except.ok cert) :
    cert.boundary = (base, base) := by
  -- `rfl`-bridge: rewrite the top-level wrapper into its expanded
  -- dispatcher form.  This avoids `unfold certifyRawCellExactV2Fueled?`
  -- (mutual recursive def — would leak Quot.sound) while still
  -- exposing the inner match for case analysis.
  have dispatcherEq :
      certifyRawCellExactV2? (profile := profile) scope (.identityCell base)
      = (match certifyRawCellExactV2Fueled? (base.size + 1) scope base with
         | .error rejection => .error rejection
         | .ok certBase =>
             .ok ⟨certBase.sort, CellBoundaryV2.endpoints base base,
                  PolyCellV2.identityCell certBase.certifiedCell⟩) := rfl
  rw [dispatcherEq] at accepted
  -- Case-analyze on the recursive call's result.
  cases hRec : certifyRawCellExactV2Fueled? (base.size + 1) scope base with
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
    -- expansion of `CellBoundaryV2.endpoints` to
    -- `(base, base) = (base, base)`, closed automatically by the
    -- definitional unfolding through the rewrite.

/-- Concrete smoke for the identityCell shape lemma: at scope 0 with
a unit-termBase base, certification accepts the identityCell and the
boundary pin lemma derives the expected `(base, base)` equation.

This smoke witnesses that the lemma's statement is operationally
useful (a concrete acceptance instance + the boundary extraction
produces a concrete equality), not merely propositionally true. -/
example :
    let baseCell : RawCellV2 0 :=
      .termBase (.mkGen .gen_unit () .childNil)
    ∀ (cert :
        CertifiedRawCellV2 fxProfile 0
          (.identityCell baseCell)),
      certifyRawCellExactV2?
          (profile := fxProfile)
          0 (.identityCell baseCell) = Except.ok cert →
      cert.boundary = (baseCell, baseCell) := by
  intro baseCell cert accepted
  exact certifyRawCellExactV2?_identityCell_boundary baseCell accepted

end LeanFX2.Foundation.PolyCell.Core
