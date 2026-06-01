import FX1Poly.Universe.UniverseFlag

/-! # FX1Poly/Universe/UniverseFlagStrength
    — the consistency-strength total order on the Setzer-Rathjen ladder

`UniverseFlag` (the 10-constructor Setzer-Rathjen large-cardinal-as-universe-admission ladder, §11.8.2)
ships as a closed enum with `DecidableEq` but NO order — its own docstring notes "the consistency-strength
order is the ctor declaration order" without realizing it.  This file realizes it: a decidable total order
on universe admission predicates, so the spec's two operational claims become theorems —

  * "Each flag is a strictly STRONGER admission predicate" (polycell.md §11.8.2 / §3.16.3) — the order is a
    genuine linear order (`le_refl` / `le_trans` / `le_antisymm` / `le_total`), and the ladder is strictly
    increasing (`standard ≤ … ≤ vopenka`, with `¬ vopenka ≤ standard`).
  * "Admission is decidable in O(flag enum position)" (§3.16.3) — `Decidable (f ≤ g)`, an O(1) comparison
    of the two flags' strength ranks.

## The lexicographic strength rank

The two payload constructors — `nMahlo n` (KPMⁿ) and `indescribable n` (Πⁿ₂-indescribable) — carry an
UNBOUNDED internal hierarchy that must sit between fixed neighbours (`superMahlo < nMahlo n < hyperMahlo`
for every `n`; `weaklyCompact < indescribable n < reflecting`).  A single-`Nat` rank cannot express this
(infinitely many `nMahlo` below one `hyperMahlo`).  So strength is a LEXICOGRAPHIC pair `(strengthBand,
strengthDegree)`: the band is the declaration-order position (payload constructors get one band each), the
degree is the payload (`0` for payload-free constructors).  `nMahlo_le_hyperMahlo` witnesses the headline
lex property — every `nMahlo n`, however large `n`, is below `hyperMahlo`.

This is the SYNTACTIC declaration-order strength; the `nMahlo 0 = standard` / `nMahlo 1 = mahlo` collapse
(a separate normal-form concern) is deliberately NOT folded in, which keeps the rank injective
(`eq_of_strengthRank`) and the order antisymmetric.  Per-flag ADMISSION proofs (that a given flag's
consistency strength is actually attained) require large-cardinal axioms and are out of scope — this file
orders the ladder, it does not discharge it.

## Zero-axiom verification

`strengthBand` / `strengthDegree` are plain matches; injectivity is via a `decodeStrengthRank` left inverse
(`cases <;> rfl`); the order laws reduce to `Init` `Nat` order lemmas (`Nat.lt_trans` / `Nat.le_antisymm` /
`Nat.lt_trichotomy` / `Nat.le_total`); decidability is `inferInstanceAs` over the decidable `Nat` formula;
the ladder smokes are `decide` over that formula.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- The declaration-order band of a universe flag's consistency strength (the major lexicographic
component).  Payload constructors (`nMahlo` / `indescribable`) each occupy one band; their internal
hierarchy is carried by `strengthDegree`. -/
def UniverseFlag.strengthBand : UniverseFlag → Nat
  | .standard => 0
  | .inaccessible => 1
  | .mahlo => 2
  | .superMahlo => 3
  | .nMahlo _ => 4
  | .hyperMahlo => 5
  | .weaklyCompact => 6
  | .indescribable _ => 7
  | .reflecting => 8
  | .vopenka => 9

/-- The internal degree of a payload universe flag (the minor lexicographic component): the `nMahlo` /
`indescribable` index, `0` for the payload-free constructors.  Written as a FULL enumeration (not a
wildcard fallthrough) — a wildcard `_ => 0` arm leaks `propext` through its equation lemmas. -/
def UniverseFlag.strengthDegree : UniverseFlag → Nat
  | .standard => 0
  | .inaccessible => 0
  | .mahlo => 0
  | .superMahlo => 0
  | .nMahlo n => n
  | .hyperMahlo => 0
  | .weaklyCompact => 0
  | .indescribable n => n
  | .reflecting => 0
  | .vopenka => 0

/-- A left inverse of `(strengthBand, strengthDegree)` — reconstructs the flag from its lexicographic
rank.  Witnesses that the rank is injective (`eq_of_strengthRank`). -/
def UniverseFlag.decodeStrengthRank (band degree : Nat) : Option UniverseFlag :=
  match band with
  | 0 => some .standard
  | 1 => some .inaccessible
  | 2 => some .mahlo
  | 3 => some .superMahlo
  | 4 => some (.nMahlo degree)
  | 5 => some .hyperMahlo
  | 6 => some .weaklyCompact
  | 7 => some (.indescribable degree)
  | 8 => some .reflecting
  | 9 => some .vopenka
  | _ + 10 => none

/-- The strength rank reconstructs its flag — the left-inverse equation. -/
theorem UniverseFlag.decodeStrengthRank_strength (flag : UniverseFlag) :
    UniverseFlag.decodeStrengthRank flag.strengthBand flag.strengthDegree = some flag := by
  cases flag <;> rfl

/-- The lexicographic strength rank is injective: equal band AND equal degree force equal flags.  Via the
`decodeStrengthRank` left inverse — no constructor case analysis on pairs. -/
theorem UniverseFlag.eq_of_strengthRank {leftFlag rightFlag : UniverseFlag}
    (bandEqual : leftFlag.strengthBand = rightFlag.strengthBand)
    (degreeEqual : leftFlag.strengthDegree = rightFlag.strengthDegree) :
    leftFlag = rightFlag := by
  have leftDecode := UniverseFlag.decodeStrengthRank_strength leftFlag
  rw [bandEqual, degreeEqual, UniverseFlag.decodeStrengthRank_strength rightFlag] at leftDecode
  exact (Option.some.inj leftDecode).symm

/-- **Consistency-strength order**: `leftFlag` admits no more than `rightFlag` when its strength rank is
lexicographically below — a strictly smaller band, or an equal band with no larger degree.  `standard` is
the bottom, `vopenka` the top. -/
def UniverseFlag.le (leftFlag rightFlag : UniverseFlag) : Prop :=
  leftFlag.strengthBand < rightFlag.strengthBand ∨
    (leftFlag.strengthBand = rightFlag.strengthBand ∧
      leftFlag.strengthDegree ≤ rightFlag.strengthDegree)

instance : LE UniverseFlag := ⟨UniverseFlag.le⟩

/-- Admission comparison is decidable (the §3.16.3 "decidable in O(flag enum position)" claim): the order
reduces to a decidable `Nat` formula. -/
instance (leftFlag rightFlag : UniverseFlag) : Decidable (leftFlag ≤ rightFlag) :=
  inferInstanceAs (Decidable
    (leftFlag.strengthBand < rightFlag.strengthBand ∨
      (leftFlag.strengthBand = rightFlag.strengthBand ∧
        leftFlag.strengthDegree ≤ rightFlag.strengthDegree)))

/-- The strength order is reflexive. -/
theorem UniverseFlag.le_refl (flag : UniverseFlag) : flag ≤ flag :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

/-- The strength order is transitive. -/
theorem UniverseFlag.le_trans {leftFlag midFlag rightFlag : UniverseFlag}
    (leftBelowMid : leftFlag ≤ midFlag) (midBelowRight : midFlag ≤ rightFlag) :
    leftFlag ≤ rightFlag := by
  rcases leftBelowMid with bandLt | ⟨bandEq, degreeLe⟩ <;>
    rcases midBelowRight with bandLt' | ⟨bandEq', degreeLe'⟩
  · exact Or.inl (Nat.lt_trans bandLt bandLt')
  · exact Or.inl (Nat.lt_of_lt_of_le bandLt (Nat.le_of_eq bandEq'))
  · exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_of_eq bandEq) bandLt')
  · exact Or.inr ⟨bandEq.trans bandEq', Nat.le_trans degreeLe degreeLe'⟩

/-- The strength order is antisymmetric — `leftFlag ≤ rightFlag ≤ leftFlag` forces flag equality (via the
injective strength rank). -/
theorem UniverseFlag.le_antisymm {leftFlag rightFlag : UniverseFlag}
    (leftBelowRight : leftFlag ≤ rightFlag) (rightBelowLeft : rightFlag ≤ leftFlag) :
    leftFlag = rightFlag := by
  rcases leftBelowRight with bandLt | ⟨bandEq, degreeLe⟩ <;>
    rcases rightBelowLeft with bandLt' | ⟨bandEq', degreeLe'⟩
  · exact absurd (Nat.lt_trans bandLt bandLt') (Nat.lt_irrefl _)
  · exact absurd (bandEq' ▸ bandLt) (Nat.lt_irrefl _)
  · exact absurd (bandEq ▸ bandLt') (Nat.lt_irrefl _)
  · exact UniverseFlag.eq_of_strengthRank bandEq (Nat.le_antisymm degreeLe degreeLe')

/-- The strength order is total — any two admission predicates are comparable. -/
theorem UniverseFlag.le_total (leftFlag rightFlag : UniverseFlag) :
    leftFlag ≤ rightFlag ∨ rightFlag ≤ leftFlag := by
  rcases Nat.lt_trichotomy leftFlag.strengthBand rightFlag.strengthBand with bandLt | bandEq | bandGt
  · exact Or.inl (Or.inl bandLt)
  · rcases Nat.le_total leftFlag.strengthDegree rightFlag.strengthDegree with degreeLe | degreeGe
    · exact Or.inl (Or.inr ⟨bandEq, degreeLe⟩)
    · exact Or.inr (Or.inr ⟨bandEq.symm, degreeGe⟩)
  · exact Or.inr (Or.inl bandGt)

/-! ## Ladder non-degeneracy smokes -/

/-- The ladder spans from the weakest admission (`standard`) to the committed categorical apex
(`vopenka`). -/
theorem UniverseFlag.standard_le_vopenka : UniverseFlag.standard ≤ .vopenka := by decide

/-- The apex is STRICTLY above the bottom — the ladder is non-degenerate. -/
theorem UniverseFlag.not_vopenka_le_standard : ¬ (UniverseFlag.vopenka ≤ .standard) := by decide

/-- **The headline lex property**: every `nMahlo n`, however large `n`, has strength strictly below
`hyperMahlo` — the unbounded KPMⁿ hierarchy sits entirely below fixed-point Mahlo, which a single-`Nat`
rank could not express. -/
theorem UniverseFlag.nMahlo_le_hyperMahlo (degree : Nat) :
    UniverseFlag.nMahlo degree ≤ .hyperMahlo :=
  Or.inl (show (4 : Nat) < 5 by decide)

/-- Internal `nMahlo` degree monotonicity (the KPMⁿ hierarchy is ordered by `n`). -/
theorem UniverseFlag.nMahlo_mono {lowerDegree higherDegree : Nat} (degreeLe : lowerDegree ≤ higherDegree) :
    UniverseFlag.nMahlo lowerDegree ≤ .nMahlo higherDegree :=
  Or.inr ⟨rfl, degreeLe⟩

end FX1Poly.Universe
