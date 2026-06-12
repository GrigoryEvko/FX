import FX1Poly.Typed.HasTypeUnionCanonicalForms
import FX1Poly.Typed.HasTypeUnionInversion
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Core.RawSize

/-! # FX1Poly/Typed/NatNumeralUnionCanonicity — DEEP Nat canonicity over the single union judgment

The NATIVE-38 lane master's nat corollary (`HasTypeUnion.closedNormalNatCanonicalForms`) is
deliberately SHALLOW: it pins only the HEAD of a closed normal union-typed term at `natTypeCell`
(`natZero`, or `natSucc` of an ARBITRARY predecessor) — exactly what an ι rule inspects.  The
Milestone-A Nat-canonicity pillar concludes the RECURSIVE `IsNatNumeral` family (the whole tower is
numeral-shaped).  This file closes that depth gap over the union:

  * **`HasTypeUnion.closedNormalNatNumeralBounded`** — the fuel-indexed worker: structural
    induction on a `RawTerm.size` bound (the [[feedback_lean_structural_fuel_decoder]] discipline —
    STRUCTURAL on the fuel `Nat`, never `WellFounded.fix`).  Each round: the shallow lane corollary
    pins the head; the `natZero` head closes by `IsNatNumeral.zero`; the `natSucc` head walks through
    the NATIVE-42-exact `invertAtNatSuccHead` (the predecessor child is union-typed at `Nat`), extracts
    the predecessor's normality / path-freeness with the children projections, shrinks the size bound
    (`size (natSucc p) = p.size + 2`, definitionally), and recurses.
  * **`HasTypeUnion.closedNormalNatNumeral` (★)** — the headline: a closed normal union-typed
    term at `natTypeCell` with no bridge-fragment occurrence IS a deep numeral.  Instantiates the
    worker at `fuel := subject.size`.

This is the union restatement of the retired zoo-level Nat-canonicity pillar (`closedNatCanonicalForms`
over `HasTypeDescNatIntro ∨ HasTypeDescPi`): the zoo statement's reduces-to-numeral content was
reflexive (intro-typed subjects ARE values), so the honest live content is exactly closed-NORMAL
deep-numeral shape — which this theorem states over the ONE judgment.  The reduces-to-numeral form
over the union returns with the deferred union SR/SN arc.

## Zero-axiom

Structural fuel induction (no `WellFounded.fix`, no `termination_by`), the shallow lane corollary, the
exact natSucc inversion, the Bool children projections, and `Nat.le` arithmetic
(`Nat.le_of_succ_le_succ` / `Nat.le_succ` / `Nat.le_trans` / `Nat.not_succ_le_zero`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditNatNumeralUnionCanonicity.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The fuel-indexed deep-numeral worker.**  Structural induction on the fuel bound: the shallow
lane corollary pins the head, the exact natSucc inversion recovers the predecessor's union typing,
the children projections recover its normality / path-freeness, and the size bound shrinks by two
per `natSucc` layer. -/
theorem HasTypeUnion.closedNormalNatNumeralBounded {profile : PolyProfile} :
    ∀ (fuel : Nat) (subject : RawTerm 0), RawTerm.size subject ≤ fuel →
      HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
        subject natTypeCell →
      RawTerm.isStepNormalForm subject →
      RawTerm.containsGeneratorBool .gen_pathApp subject = false →
      RawTerm.containsGeneratorBool .gen_pathLam subject = false →
      IsNatNumeral subject := by
  intro fuel
  induction fuel with
  | zero =>
      intro subject sizeBound _typed _normal _pathAppFree _pathLamFree
      cases subject with
      | mkGen generator payload children =>
          exact absurd sizeBound (Nat.not_succ_le_zero _)
  | succ fuelPrev fuelIH =>
      intro subject sizeBound typed normal pathAppFree pathLamFree
      rcases typed.closedNormalNatCanonicalForms normal pathAppFree pathLamFree with
          zeroShape | ⟨predecessor, succShape⟩
      · rw [zeroShape]
        exact IsNatNumeral.zero
      · subst succShape
        obtain ⟨_convNat, predecessorTyped⟩ := typed.invertAtNatSuccHead rfl
        have predecessorNormal := RawTermChildren.areStepNormalFormsBool_head
          (RawTerm.isStepNormalFormBool_children normal)
        have predecessorAppFree := RawTermChildren.containGeneratorBool_head
          (RawTerm.containsGeneratorBool_children pathAppFree)
        have predecessorLamFree := RawTermChildren.containGeneratorBool_head
          (RawTerm.containsGeneratorBool_children pathLamFree)
        have predecessorBelowChildren :=
          RawTermChildren.size_lt_childCons_head (shift := 0) (restShifts := [])
            predecessor RawTermChildren.childNil
        have childrenBelowFuel :
            RawTermChildren.size
                (RawTermChildren.childCons (shift := 0) (restShifts := [])
                  predecessor RawTermChildren.childNil) + 1
              ≤ fuelPrev + 1 :=
          sizeBound
        have predecessorBound : RawTerm.size predecessor ≤ fuelPrev :=
          Nat.le_of_succ_le
            (Nat.le_of_succ_le_succ
              (Nat.le_trans (Nat.succ_le_succ predecessorBelowChildren) childrenBelowFuel))
        exact IsNatNumeral.succ
          (fuelIH predecessor predecessorBound predecessorTyped predecessorNormal
            predecessorAppFree predecessorLamFree)

/-- **★ DEEP closed-normal Nat canonicity over the single union judgment** (core beta/iota fragment):
a closed normal union-typed term at `natCode` with no bridge-fragment occurrence is a deep numeral
(`IsNatNumeral` — the WHOLE tower, not just the head).  The Milestone-A Nat-canonicity pillar over the
ONE judgment. -/
theorem HasTypeUnion.closedNormalNatNumeral {profile : PolyProfile}
    {subject : RawTerm 0}
    (typed : HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
      subject natTypeCell)
    (normal : RawTerm.isStepNormalForm subject)
    (pathAppFree : RawTerm.containsGeneratorBool .gen_pathApp subject = false)
    (pathLamFree : RawTerm.containsGeneratorBool .gen_pathLam subject = false) :
    IsNatNumeral subject :=
  HasTypeUnion.closedNormalNatNumeralBounded (RawTerm.size subject) subject
    (Nat.le_refl _) typed normal pathAppFree pathLamFree

/-- **Non-vacuity**: the numeral `2` — union-typed through the recursive `natSucc` arm twice — is a
deep numeral by the headline (it is closed, normal, and bridge-free on the nose). -/
theorem HasTypeUnion.closedNormalNatNumeral.numeralTwo {profile : PolyProfile} :
    IsNatNumeral (natSuccCell (natSuccCell natZeroCell) : RawTerm 0) :=
  HasTypeUnion.closedNormalNatNumeral
    (numeralTwoTypedThroughUnionRecursiveIntroTwice (profile := profile)) rfl rfl rfl

end FX1Poly.Typed
