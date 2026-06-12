import FX1Poly.Typed.UnitReadbackArgumentBoundary

/-! # FX1Poly/Typed/UnitReadbackFormerChildBoundary
   — ★ the 7th boundary: classifiers do not flow into FORMER children (#481 brick-5 verdict)

The mandated completeness re-analysis after the neutral-spine arm, machine-checked: the readback
still never descends into the children of TYPE-CODE formers.  Term positions inside type codes
exist — the identity code `Id(A, a, b)` carries two TERMS of the carrier type — and a unit
difference there is invisible to every shipped arm.  Witness, in
`(f : Π(_:Unit).Unit, x : Unit)`:

  * `Id(Unit, app(f,x), unit)` and `Id(Unit, unit, unit)` are congruently unit-η-equal — one
    `congGen` descent through `gen_idCode`, the left endpoints related by `unitEta` (the
    compound neutral is grown-typed at `unitTypeCell`, the value nullary-value-typed).
  * At the classifier `Type@0` the readback degrades to the deep collapse at EVERY fuel (an
    `idCode` head is not an application, so the spine arm cannot fire), and the collapses are
    distinct βη-normal forms that never join: the deep collapse rewrites the unit VARIABLE
    inside the neutral (`app(f,x) ↦ app(f,unit)`) but cannot see that the whole neutral is
    unit-typed — the compound-neutral phenomenon (the 4th boundary), recurring one level down,
    inside a former.

## The verdict (CORRECTED post-fact-check) — engine-gated, like Σ

The boundary is DOUBLE-gated on the engine, not on readback machinery: (a) `typingRuleDescOf`
has NO `gen_idCode` row today, and (b) the `DescTelescope` row schema classifies former children
at UNIVERSES only — a VALUE premise (endpoints at the CARRIER) is inexpressible in the current
schema.  Consequently the witness pair lies OUTSIDE the currently-typeable fragment (the same
engine-separation class as the Σ-η block), and within the TYPED fragment every former child is
a TYPE, so no unit-η leaf can sit at a former-child position TODAY.  The former-descent readback
arm is gated on a future value-premise row schema; the genuine IN-FRAGMENT frontier is
depth-2+ application spines (the next boundary).

## Honest scope notes

(1) The PAIR-level typings are not asserted — the right cell's `unit` children are
nullary-value-typed only (the standing layer separation), and `congGen` needs no endpoint typing;
the `unitEta` leaf carries the typings exactly where they are needed (the endpoint position).
(2) All shipped soundness packages remain intact; the procedure stays a sound semi-decision.

## Zero-axiom verification

The `congGen` witness composes shipped leaves; degradations are `rfl` per fuel shape; the
collapse computations are `rfl`; non-joinability is the `reduceOnceBetaEta_complete`-at-`rfl`
leaf discipline; inequalities are `decide` on concrete cells via the `show`-coercion.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The identity code `Id(Unit, app(f,x), unit)` — the compound unit-typed neutral sitting at a
FORMER-child (endpoint) position. -/
def identityCodeOverCompoundNeutral : RawTerm 2 :=
  .mkGen .gen_idCode ()
    (.childCons unitTypeCell
      (.childCons compoundUnitNeutral
        (.childCons unitCell .childNil)))

/-- The identity code `Id(Unit, unit, unit)` — the η-long target. -/
def identityCodeOverUnitValue : RawTerm 2 :=
  .mkGen .gen_idCode ()
    (.childCons unitTypeCell
      (.childCons unitCell
        (.childCons unitCell .childNil)))

/-- **The identity codes are congruently unit-η-equal**: one `congGen` descent through
`gen_idCode` — carrier and right endpoint shared, the left endpoints related by `unitEta`. -/
theorem identityCodePair_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      identityCodeOverCompoundNeutral identityCodeOverUnitValue :=
  DefEqUnitEtaCong.congGen (generator := Generator.gen_idCode) ()
    (.consEqualZero
      (.consZero
        (.ofDefEq (.unitEta (Or.inr (compoundUnitNeutralTyped profile))
          (Or.inl (NullaryDataValueTyped.unitValueTyped (unitFunctionContext profile)))))
        (.consEqualZero .nil)))

/-- At `Type@0` the readback degrades to the deep collapse on the neutral-endpoint code at EVERY
fuel — an `idCode` head is not an application, so neither the classifier-directed arms nor the
delegated spine readback fire (three fuel shapes: 0 collapses outright, 1 delegates into an
exhausted spine, ≥ 2 delegates into a spine whose app-destructuring refuses the former head). -/
theorem readback_identityCodeNeutral_isDeepCollapse (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (unitFunctionContext profile)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          identityCodeOverCompoundNeutral
        = collapseUnitVariablesDeep (unitFunctionContext profile)
            identityCodeOverCompoundNeutral
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem readback_identityCodeValue_isDeepCollapse (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (unitFunctionContext profile)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          identityCodeOverUnitValue
        = collapseUnitVariablesDeep (unitFunctionContext profile)
            identityCodeOverUnitValue
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The deep collapse of the neutral-endpoint code: the unit VARIABLE inside the neutral is
rewritten, but the neutral itself survives — the 4th-boundary phenomenon inside a former. -/
def collapsedIdentityCodeOverCompoundNeutral : RawTerm 2 :=
  .mkGen .gen_idCode ()
    (.childCons unitTypeCell
      (.childCons (appCell (variableCell ⟨1, Nat.le.refl⟩) unitCell)
        (.childCons unitCell .childNil)))

theorem deepCollapse_identityCodeNeutral (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitFunctionContext profile) identityCodeOverCompoundNeutral
      = collapsedIdentityCodeOverCompoundNeutral := rfl

theorem deepCollapse_identityCodeValue (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitFunctionContext profile) identityCodeOverUnitValue
      = identityCodeOverUnitValue := rfl

/-- **The collapsed identity codes never βη-join**: formers are operationally inert, the inner
application is a stuck neutral, and the cells are distinct. -/
theorem collapsedIdentityCodePair_notBetaEtaConv :
    ¬ BetaEtaConv collapsedIdentityCodeOverCompoundNeutral identityCodeOverUnitValue := by
  intro convertible
  obtain ⟨commonTerm, neutralChain, valueChain⟩ := convertible
  have neutralEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        collapsedIdentityCodeOverCompoundNeutral.reduceOnceBetaEta = none))
      neutralChain
  have valueEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        identityCodeOverUnitValue.reduceOnceBetaEta = none))
      valueChain
  exact absurd (neutralEq.trans valueEq.symm) (by decide)

/-- **★ The 7th boundary — the readback is incomplete at FORMER-CHILDREN positions**: a
congruently unit-η-equal pair of TYPE CODES (the unit difference at an identity-code endpoint)
whose readbacks at EVERY fuel are distinct βη-normal forms that never join.  Engine-gated (see
the corrected module verdict): the witness is outside the currently-typeable fragment; the
former-descent arm waits on a value-premise row schema. -/
theorem readback_isIncompleteAtFormerChildren (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 2),
      DefEqUnitEtaCong profile (unitFunctionContext profile) leftTerm rightTerm ∧
      (∀ leftFuel rightFuel : Nat,
        readbackAtClassifier leftFuel (unitFunctionContext profile)
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard) leftTerm
          ≠ readbackAtClassifier rightFuel (unitFunctionContext profile)
              (universeCodeCell LevelExpr.lzero UniverseFlag.standard) rightTerm) ∧
      ¬ BetaEtaConv
          (collapseUnitVariablesDeep (unitFunctionContext profile) leftTerm)
          (collapseUnitVariablesDeep (unitFunctionContext profile) rightTerm) :=
  ⟨identityCodeOverCompoundNeutral, identityCodeOverUnitValue,
    identityCodePair_congruentlyEqual profile,
    fun leftFuel rightFuel readbacksEqual =>
      absurd
        (show collapsedIdentityCodeOverCompoundNeutral = identityCodeOverUnitValue from
          (readback_identityCodeNeutral_isDeepCollapse profile leftFuel).symm.trans
            (readbacksEqual.trans
              (readback_identityCodeValue_isDeepCollapse profile rightFuel)))
        (by decide),
    fun convertible => collapsedIdentityCodePair_notBetaEtaConv
      (deepCollapse_identityCodeNeutral profile ▸
        deepCollapse_identityCodeValue profile ▸ convertible)⟩

end FX1Poly.Typed
