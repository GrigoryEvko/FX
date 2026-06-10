import FX1Poly.Typed.UnitNeutralSpineDetection

/-! # FX1Poly/Typed/UnitSpineDetectionBoundary
   — ★ the 5th refutation: spine detection misses λ-arguments (ULC-5 brick-2 verdict)

The mandated pre-construction re-analysis, machine-checked, AGAIN before building: the planned
brick 2 (detector-driven deep collapse — replacement predicate = `detectSpineType` positive at
`unitTypeCell`) cannot be complete, because the DETECTOR itself misses genuinely unit-typed
neutrals.  Witness, in the higher-order context `(g : Π(_:Π(_:Unit).Unit).Unit)`:

  * `app(g, λ(x:Unit).x)` is grown-typed at `unitTypeCell` — `piElim` of the variable `g` applied
    to the identity function, whose `piIntro` typing is wf-free over the #1205 unit-formation
    row.  So it is congruently unit-η-equal to `unitCell` by ONE `unitEta` leaf.
  * `detectSpineType` answers `none` on it at EVERY fuel: the spine grammar requires the
    ARGUMENT to synthesize, and `λ(x:Unit).x` is λ-headed — outside the variable-headed spine
    grammar entirely.

Any collapse whose replacement predicate is this detector leaves the term un-replaced at the
root, so the `unitEta` leaf above survives every such canonicalizer — incompleteness is forced
BEFORE the procedure is built.

## The verdict: the elimination chain is COMPLETE

Widening the detector to λ-arguments means SYNTHESIZING a λ — `piIntro` with formation typings
for the domain annotation and the synthesized codomain, i.e. bidirectional CHECKING with
formation obligations.  That is precisely the missing half of the #481 type-directed readback.
The unit campaign's five machine-checked refutations have now each forced one component of it:

  1. non-congruence of `DefEqUnitEta`        → congruent closure through children,
  2. β-surfacing                              → normalization interleaving,
  3. the binder fence                         → binder-crossing with context extension,
  4. compound neutrals                        → type detection at neutral replacement sites,
  5. λ-arguments (THIS module)                → check-mode synthesis of abstractions.

Nothing short of the full bidirectional type-directed traversal closes the relation; every
syntactic shortcut has been refuted by a concrete typed witness.  ULC-5's honest deliverable is
the sound detector (brick 1) plus THIS boundary; completeness transfers to #481 itself.

## Honest scope notes

(1) All soundness packages remain intact — the detector and both collapses stay sound
semi-decisions; positive answers certify.  (2) The witness typing is wf-free (`var` + `piIntro` +
`piElim` only), so the refutation survives any wf-restriction of the completeness statement.

## Zero-axiom verification

The typings are the `betaSurfacingRedexTyped` incantation one binder deeper; the detector
refusals are `rfl` per fuel shape (`0` / `1` / `_+2` — the fuel-structural definition reduces
with a FREE fuel tail under two successors).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The higher-order context `(g : Π(_:Π(_:Unit).Unit).Unit)` — a function CONSUMING a unit
function, so applying it needs a λ-headed argument. -/
def higherOrderUnitContext (profile : PolyProfile) : TypingContext profile 1 :=
  (TypingContext.empty : TypingContext profile 0).cons
    (piTyCodeCell (piTyCodeCell unitTypeCell unitTypeCell) unitTypeCell)

/-- The unit identity function `λ(x:Unit).x` at scope 1 — λ-headed, hence outside the
variable-headed spine grammar. -/
def unitIdentityFunction : RawTerm 1 :=
  lamCell unitTypeCell (variableCell ⟨0, Nat.le.step Nat.le.refl⟩)

/-- The λ-argument neutral `app(g, λ(x:Unit).x)` — genuinely unit-typed, undetectable. -/
def lambdaArgumentNeutral : RawTerm 1 :=
  appCell (variableCell ⟨0, Nat.zero_lt_one⟩) unitIdentityFunction

/-- The identity function is grown-typed at `Π(_:Unit).Unit` — `piIntro` over the #1205
unit-formation row, wf-free. -/
theorem unitIdentityFunctionTyped (profile : PolyProfile) :
    HasTypeDescPi profile (higherOrderUnitContext profile) unitIdentityFunction
      (piTyCodeCell unitTypeCell unitTypeCell) :=
  HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped (higherOrderUnitContext profile)))
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped
      ((higherOrderUnitContext profile).cons unitTypeCell)))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var ((higherOrderUnitContext profile).cons unitTypeCell)
        ⟨0, Nat.le.step Nat.le.refl⟩))

/-- **The λ-argument neutral is grown-typed at `unitTypeCell`** — `piElim` of the variable `g`
(its looked-up Π code computes by `rfl`) applied to the identity function; the codomain instance
computes to `unitTypeCell`.  No well-formedness needed. -/
theorem lambdaArgumentNeutralTyped (profile : PolyProfile) :
    HasTypeDescPi profile (higherOrderUnitContext profile) lambdaArgumentNeutral unitTypeCell :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (higherOrderUnitContext profile) ⟨0, Nat.zero_lt_one⟩))
    (unitIdentityFunctionTyped profile)

/-- **The pair IS congruently unit-η-equal**: one `unitEta` leaf — the neutral by the grown
typing, `unitCell` by the data-intro typing. -/
theorem lambdaArgument_congruentlyEqual_unitValue (profile : PolyProfile) :
    DefEqUnitEtaCong profile (higherOrderUnitContext profile)
      lambdaArgumentNeutral unitCell :=
  .ofDefEq (.unitEta (Or.inr (lambdaArgumentNeutralTyped profile))
    (Or.inl (HasTypeDescDataIntro.unitValueTyped (higherOrderUnitContext profile))))

/-- The λ itself is outside the spine grammar: `detectSpineType` refuses it at every fuel. -/
theorem detectSpineType_missesUnitIdentityFunction (profile : PolyProfile) :
    ∀ fuel : Nat,
      detectSpineType (higherOrderUnitContext profile) fuel unitIdentityFunction = none
  | 0 => rfl
  | _ + 1 => rfl

/-- **The detector misses the unit-typed neutral at EVERY fuel**: the app arm demands the
argument synthesize, and the λ-headed argument never does. -/
theorem detectSpineType_missesLambdaArgument (profile : PolyProfile) :
    ∀ fuel : Nat,
      detectSpineType (higherOrderUnitContext profile) fuel lambdaArgumentNeutral = none
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- **★ The 5th refutation — spine detection is incomplete at λ-arguments**: a term grown-typed
at `unitTypeCell` (wf-free), congruently unit-η-equal to `unitCell`, on which the detector
answers `none` at every fuel.  Any canonicalizer whose replacement predicate is this detector
leaves the `unitEta` leaf intact — detector-driven deep collapse is incomplete BEFORE being
built.  Widening the detector to λ-arguments is λ-SYNTHESIS (piIntro + formation obligations) —
bidirectional checking, the #481 readback itself.  The elimination chain is complete. -/
theorem spineDetection_isIncompleteAtLambdaArguments (profile : PolyProfile) :
    ∃ (neutralTerm : RawTerm 1),
      HasTypeDescPi profile (higherOrderUnitContext profile) neutralTerm unitTypeCell ∧
      DefEqUnitEtaCong profile (higherOrderUnitContext profile) neutralTerm unitCell ∧
      ∀ fuel : Nat,
        detectSpineType (higherOrderUnitContext profile) fuel neutralTerm = none :=
  ⟨lambdaArgumentNeutral, lambdaArgumentNeutralTyped profile,
    lambdaArgument_congruentlyEqual_unitValue profile,
    detectSpineType_missesLambdaArgument profile⟩

end FX1Poly.Typed
