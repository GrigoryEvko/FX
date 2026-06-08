import FX1Poly.Core.ReducibleType
namespace FX1Poly.Core
def gateLevels {scope : Nat} (base : RawTerm scope → (RawTerm scope → Prop) → Prop) :
    Nat → RawTerm scope → (RawTerm scope → Prop) → Prop
  | level => fun tc cand => (∀ lvl, if _h : lvl < level then gateLevels base lvl tc cand else True) ∧ base tc cand
termination_by level => level
decreasing_by exact _h
end FX1Poly.Core
#print axioms WellFounded.fix_eq
#print axioms FX1Poly.Core.gateLevels
#print axioms FX1Poly.Core.gateLevels.eq_def
