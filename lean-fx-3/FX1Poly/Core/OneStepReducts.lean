import FX1Poly.Core.TableOneStepReducts
import FX1Poly.Core.StepTable

/-! # FX1Poly/Core/OneStepReducts
    — the kernel one-step reduct enumeration, with SOUNDNESS (COST-3 brick 2), TABLE-BACKED

The reduct enumeration the worst-case cost bound (`costBound`) folds over.  A term's one-step
reducts are exactly: the root reduct when the term is a redex, plus every reassembly of the cell
with ONE child stepped (the congruence positions, mutual over the children spine).

Since the IOTA-T11 enumeration rebase, the ENGINE is the generic table enumeration
(`oneStepReductsOverTable`, TableOneStepReducts.lean) instantiated at the 17-row LEGACY table —
the rows that mirror the bespoke `Step` exactly — so the per-iota `fireRootRedex` dispatch is no
longer in this chain.  The spec surface is unchanged:

  * `RawTerm.oneStepReducts` / `RawTermChildren.oneStepChildrenReducts` — the enumeration;
  * ★ SOUNDNESS — every listed element is a genuine `Step`: the generic table soundness gives a
    `StepOverTable iotaRuleTable` step, and the IOTA-T1 backward adequacy
    (`StepOverTable.toStep`) maps it onto the bespoke relation;
  * non-vacuity: the identity-β fixture's enumeration computes to exactly the singleton β-reduct,
    by kernel evaluation through the table walk.

COMPLETENESS (every `Step` is listed — the direction the cost bound's soundness consumes) is
`OneStepReductsComplete.lean`, now one generic theorem instead of a 17-arm match.

The CANONICAL enumeration is `StepTable.oneStepReducts` (the full table, endpoint-β live); this
legacy-table instance exists for the surviving `Step`-stated cost lane and retires with the
bespoke relation.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## The enumeration -/

/-- **All one-step reducts of a kernel term**: the generic table enumeration at the legacy
table — the root reduct when some legacy row fires, plus every reassembly with one child
stepped. -/
def RawTerm.oneStepReducts {scope : Nat} (term : RawTerm scope) : List (RawTerm scope) :=
  oneStepReductsOverTable iotaRuleTable term

/-- All one-position-stepped variants of a children spine: step the head (tail fixed) or step
somewhere in the tail (head fixed). -/
def RawTermChildren.oneStepChildrenReducts {binderShifts : List Nat} {parentScope : Nat}
    (children : RawTermChildren binderShifts parentScope) :
    List (RawTermChildren binderShifts parentScope) :=
  oneStepChildrenReductsOverTable iotaRuleTable children

/-! ## ★ Soundness — every listed reduct is a genuine Step -/

/-- ★ **Enumeration soundness**: every member of `oneStepReducts` is a genuine `Step` — the
generic table soundness mapped back through the adequacy. -/
theorem RawTerm.oneStepReducts_sound {scope : Nat} (term : RawTerm scope)
    {reduct : RawTerm scope} (memReduct : reduct ∈ RawTerm.oneStepReducts term) :
    Step term reduct :=
  (oneStepReductsOverTable_sound (table := iotaRuleTable) term memReduct).toStep

/-- Spine soundness: every listed children variant is a genuine `StepChildren` — the spine
companion mapped back through the adequacy. -/
theorem RawTermChildren.oneStepChildrenReducts_sound {binderShifts : List Nat}
    {parentScope : Nat} (children : RawTermChildren binderShifts parentScope)
    {steppedSpine : RawTermChildren binderShifts parentScope}
    (memSpine : steppedSpine ∈ RawTermChildren.oneStepChildrenReducts children) :
    StepChildren children steppedSpine :=
  (oneStepChildrenReductsOverTable_sound (table := iotaRuleTable)
    children memSpine).toStepChildren

/-! ## Non-vacuity — the enumeration computes -/

/-- The identity-β fixture `(λ. var 0) unit` at scope 0. -/
def identityBetaFixture : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_lam ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons
            (.mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil)
            .childNil)))
      (.childCons (.mkGen .gen_unit () .childNil) .childNil))

/-- **The enumeration computes**: the identity-β fixture has EXACTLY one one-step reduct — the
β-reduct `unit` — by kernel evaluation through the table walk (the legacy β row fires; every
child is normal so the congruence half is empty). -/
theorem identityBetaFixture_oneStepReducts :
    RawTerm.oneStepReducts identityBetaFixture
      = [.mkGen .gen_unit () .childNil] := rfl

end FX1Poly.Core
