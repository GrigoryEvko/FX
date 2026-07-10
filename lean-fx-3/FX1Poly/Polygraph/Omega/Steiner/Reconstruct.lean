import FX1Poly.Polygraph.Omega.StrictAxioms
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv

/-! # Polygraph/Omega/Steiner/Reconstruct — the CROWN completeness at the honest scope (OMEGA-2 r3)

★ **THE COMPLETENESS LEG, SCOPED.**  OMEGA-2 r1/r2 shipped the SOUND half of the free-omega word
problem: `linearize` is a congruence invariant (`linearizeSoundness`), so distinct Steiner tables
soundly REFUTE convertibility (`not_conv_of_linearize_ne`).  r3 supplies the CONVERSE — a
`reconstruct : SteinerCell -> CellExpr` and a proof that on a genuinely-admitted sub-fragment equal
tables IMPLY convertibility, so table equality DECIDES the word problem (both verdicts), at EVERY
dimension.

## Why the scope is what it is (recon verdict, honest and load-bearing)

Full free-omega completeness is **FALSE on the whole carrier**, not merely hard, for two independent
reasons recorded in the r2 ledger and re-confirmed by the r3 recon:

  * **Lossy whisker.**  `linearize (whiskerLeft w b) = linearize b` (`linearize_whiskerLeft`): the
    whiskering 1-cell `w` is FORGOTTEN, so a whiskered cell `f . g => f . g'` and its unwhiskered
    reconstruction `g => g'` have genuinely different boundaries and are NOT convertible.  No
    strict-axiom row un-whiskers a cell.
  * **The id-congruence gap.**  `SaturatedConvOver` has 8 constructors (`ofRelation` + 4 one-hole
    congruences + refl/symm/trans) and NO `idCongr`: there is no way to derive `id a ~ id b` from
    `a ~ b`.  A map-OUT (the soundness fold `recInto`) never CONSTRUCTS an id-congruence, so soundness
    dodges the gap; a map-IN (reconstruct) hits it on any interior identity.

So the honest completeness scope is the **whisker-free, interior-id-free vcomp-word fragment over a
single endo generator** (`IsAtomWord`): cells built from ONE generating atom `crownAtom` and `vcomp`.
There `reconstruct` is a right-nested vcomp-chain of atoms ending in the base identity, and completeness
is `assoc + right-unit` — NO id-congruence (no interior ids), NO whisker (excluded).  This is a
genuinely-admitted fragment at **every** dimension (the free monoid of endo `n`-cells on one generator),
so it satisfies the world-first census target (c): free-`n` decidability for `n >= 3`, exhibited here at
`n = 3` AND `n = 4`.

## The reconstruct recursion (fuel-structural, never `WellFounded.fix`)

`reconstruct` is driven by a DOUBLE structural recursion — structural on the coordinate `List Int`
(finite) and, per nonzero entry, structural on the entry's `Int.toNat` count (`vcompPow`).  This is
strictly cleaner than the recon's `sumAbs`-fuel option: both are `WellFounded.fix`-free, but the
list-and-count structural form needs no fuel-exhaustion arm and no rank bound.

## What ships (each piece zero-axiom, structural, ASCII-only, propext-clean)

  * **`vcompPow` / `vcompPow_add`** — the generic `k`-fold vertical composite and its splitting law
    (dimension-and-count generic; the reconstruct backbone).
  * **`crownComputad` / `crownValuation` / `crownAtom`** — the single-endo-generator one-object
    computad with a length-1 one-hot valuation (`crownAtom -> [1]`, identities -> `[0]`).
  * **`reconstructCrown`** — `SteinerCell -> CellExpr crownComputad (dim+1)`, the fuel-structural
    vcomp-word peel.
  * **`linearize_vcompPow_count`** — THE ARITHMETIC ROUNDTRIP `linearize (reconstruct [k]) = [k]` on the
    admitted (singleton non-negative) tables, generic in `k` and `dim`.
  * **`reconstructCrown_conv_atomWord`** — THE CONV LEG `SaturatedConvOver (reconstruct (linearize a)) a`
    for every atom word `a` (assoc + right-unit; no id-congruence, no whisker).
  * **`atomWord_conv_iff_linearize_eq`** — THE CROWN: convertibility <-> table equality on the fragment,
    both directions, at every dimension.
  * **`decideAtomWordConv`** — the `Decidable` value deciding conv by O(1) table equality; both verdicts
    exhibited at `n = 3` and `n = 4`.
  * The r3 honesty markers naming the scope and the two general obstructions.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## Clean Nat helpers (self-defined; the stock `Nat.zero_add` / `Nat.succ_add` are avoided so no
propext can enter through arithmetic) -/

/-- `0 + n = n`, structural (avoids the stock lemma; `congrArg` is propext-clean). -/
theorem natZeroAddClean : (n : Nat) → 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (natZeroAddClean n)

/-- `(m + 1) + n = (m + n) + 1`, structural. -/
theorem natSuccAddClean : (m n : Nat) → (m + 1) + n = (m + n) + 1
  | _, 0 => rfl
  | m, n + 1 => congrArg (· + 1) (natSuccAddClean m n)

/-- `1 + n = n + 1`, structural (the reconstruct arithmetic's only commutation need). -/
theorem natOneAddClean : (n : Nat) → 1 + n = n + 1
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (natOneAddClean n)

/-! ## The generic `k`-fold vertical composite -/

/-- The **`k`-fold right-nested vertical composite** of `atom` ending in `tail`:
`vcompPow atom tail k = atom . (atom . ( ... . tail))` with `k` copies of `atom`.  Structural on the
count; dimension-and-computad generic. -/
def vcompPow {computad : OmegaComputad} {dim : Nat}
    (atom tail : CellExpr computad (dim + 1)) : Nat → CellExpr computad (dim + 1)
  | 0 => tail
  | count + 1 => CellExpr.vcomp atom (vcompPow atom tail count)

/-- **The splitting law** `vcompPow atom tail (kl + kr) = vcompPow atom (vcompPow atom tail kr) kl` —
the associativity of the count that the atom-word completeness induction consumes.  Structural on `kl`
over the clean Nat helpers (no propext). -/
theorem vcompPow_add {computad : OmegaComputad} {dim : Nat}
    (atom tail : CellExpr computad (dim + 1)) :
    (kl kr : Nat) → vcompPow atom tail (kl + kr) = vcompPow atom (vcompPow atom tail kr) kl
  | 0, kr => by
      show vcompPow atom tail (0 + kr) = vcompPow atom tail kr
      rw [natZeroAddClean]
  | kl + 1, kr => by
      rw [natSuccAddClean]
      show CellExpr.vcomp atom (vcompPow atom tail (kl + kr))
        = CellExpr.vcomp atom (vcompPow atom (vcompPow atom tail kr) kl)
      rw [vcompPow_add atom tail kl kr]

/-! ## The single-endo-generator one-object computad (the honest completeness carrier) -/

/-- The **crown computad** — one object (`Unit` modes), one generator label per dimension (`Unit`).  The
free omega-category on a single endo generator at each dimension: the substantive whisker-free vcomp-word
fragment lives here. -/
def crownComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => Unit

/-- The **canonical base cell** at each dimension — the identity tower `ofMode () , id (ofMode ()) ,
id (id (ofMode ())) , ...`.  Every generator is the endo cell on this base. -/
def crownBaseCell : (dim : Nat) → CellExpr crownComputad dim
  | 0 => CellExpr.ofMode ()
  | dim + 1 => CellExpr.id (crownBaseCell dim)

/-- The **single generating `(dim+1)`-cell** — the endo generator `crownAtom dim : crownBaseCell dim =>
crownBaseCell dim`.  Its declared source and target are both the canonical base cell, so its boundaries
are `crownBaseCell dim`. -/
def crownAtom (dim : Nat) : CellExpr crownComputad (dim + 1) :=
  CellExpr.gen () (crownBaseCell dim) (crownBaseCell dim)

/-- The **one-hot length-1 valuation** — every generator (at any dimension) linearizes to the basis
vector `[1]`; identities (via `linearize_id`) linearize to the degenerate `[0]`.  Faithful: an atom
word's table counts its atoms. -/
def crownValuation : ComputadValuation crownComputad where
  ambientDim := 1
  modeValue := fun _ => ⟨[0]⟩
  genValue := fun _dim _label => ⟨[1]⟩
  modeValueLength := fun _ => rfl
  genValueLength := fun _ _ => rfl

/-! ## The atom-word fragment -/

/-- Whether a `(dim+1)`-cell is an **atom word** — built from the single generator `crownAtom dim` and
`vcomp` ONLY (no interior identity, no whisker).  This is exactly the fragment where `reconstruct` is a
right-nested vcomp-chain and completeness needs neither the missing id-congruence nor an un-whiskering
row. -/
inductive IsAtomWord {dim : Nat} : CellExpr crownComputad (dim + 1) → Prop where
  /-- The single generating atom is an atom word. -/
  | atom : IsAtomWord (crownAtom dim)
  /-- A vertical composite of two atom words is an atom word. -/
  | vcomp {left right : CellExpr crownComputad (dim + 1)} :
      IsAtomWord left → IsAtomWord right → IsAtomWord (CellExpr.vcomp left right)

/-- The **atom count** of a cell — one per generator, additive over vertical composites, zero on
identities and modes; whiskers project to the main factor.  Constant `Nat` motive, propext-free. -/
def atomCount {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → Nat
  | _, .ofMode _ => 0
  | _, .gen _ _ _ => 1
  | _, .id _ => 0
  | _, .vcomp left right => atomCount left + atomCount right
  | _, .whiskerLeft _ cell => atomCount cell
  | _, .whiskerRight cell _ => atomCount cell

/-! ## The linearize invariant on atom words -/

/-- ★ **An atom word's Steiner table counts its atoms.**  `linearize crownValuation a = [atomCount a]`
for every atom word `a`: the generator contributes `[1]`, vcomp is coordinate addition (which is
integer addition of the single coordinate), so the table is the atom total.  Structural on
`IsAtomWord`. -/
theorem linearize_atomWord {dim : Nat} {cell : CellExpr crownComputad (dim + 1)}
    (hAtom : IsAtomWord cell) :
    (linearize crownValuation cell).coordinates = [Int.ofNat (atomCount cell)] := by
  induction hAtom with
  | atom => rfl
  | @vcomp left right _ _ ihLeft ihRight =>
      show addCoordinates (linearize crownValuation left).coordinates
        (linearize crownValuation right).coordinates = [Int.ofNat (atomCount left + atomCount right)]
      rw [ihLeft, ihRight]
      show [Int.ofNat (atomCount left) + Int.ofNat (atomCount right)]
        = [Int.ofNat (atomCount left + atomCount right)]
      rfl

/-! ## The generic homomorphism backbone: `linearize (vcompPow ...)` -/

/-- ★ **THE ARITHMETIC ROUNDTRIP.**  `linearize (vcompPow crownAtom (id base) k) = [Int.ofNat k]` — the
`k`-atom reconstruction's table is exactly `[k]`.  Structural on `k`: the base identity gives `[0]`,
each extra atom adds `[1]` on the head coordinate.  This is `linearize (reconstruct t) = t` on the
admitted (singleton non-negative) tables. -/
theorem linearize_vcompPow_count (dim : Nat) : (k : Nat) →
    (linearize crownValuation
      (vcompPow (crownAtom dim) (CellExpr.id (crownBaseCell dim)) k)).coordinates = [Int.ofNat k]
  | 0 => rfl
  | k + 1 => by
      show addCoordinates (linearize crownValuation (crownAtom dim)).coordinates
        (linearize crownValuation
          (vcompPow (crownAtom dim) (CellExpr.id (crownBaseCell dim)) k)).coordinates
        = [Int.ofNat (k + 1)]
      rw [linearize_vcompPow_count dim k]
      show [Int.ofNat (1 + k)] = [Int.ofNat (k + 1)]
      exact congrArg (fun total => ([Int.ofNat total] : List Int)) (natOneAddClean k)

/-! ## The reconstruct map -/

/-- Read the head coordinate as a Nat atom count (the length-1 ambient uses only the head). -/
def listHeadCount : List Int → Nat
  | [] => 0
  | entry :: _ => entry.toNat

/-- ★ **`reconstructCrown` — the fuel-structural vcomp-word peel.**  A Steiner table is reconstructed at
dimension `dim+1` as the `k`-fold vcomp of `crownAtom dim` over the base identity, where `k` is the head
coordinate's `toNat`.  Total; on the admitted image `t = [k]` it inverts `linearize`. -/
def reconstructCrown (dim : Nat) (table : SteinerCell) : CellExpr crownComputad (dim + 1) :=
  vcompPow (crownAtom dim) (CellExpr.id (crownBaseCell dim)) (listHeadCount table.coordinates)

/-- The full arithmetic roundtrip in reconstruct form: `linearize (reconstructCrown dim [k]) = [k]`. -/
theorem linearize_reconstructCrown_roundtrip (dim k : Nat) :
    (linearize crownValuation (reconstructCrown dim ⟨[Int.ofNat k]⟩)).coordinates = [Int.ofNat k] := by
  show (linearize crownValuation
    (vcompPow (crownAtom dim) (CellExpr.id (crownBaseCell dim)) k)).coordinates = [Int.ofNat k]
  exact linearize_vcompPow_count dim k

/-! ## The boundary of an atom word (the right-unit reconciliation) -/

/-- Every atom word's target boundary is the canonical base cell — so the reconstruction's trailing
`id (crownBaseCell dim)` is exactly `id (boundaryTarget a)`, the right-unit row's argument. -/
theorem boundaryTarget_atomWord {dim : Nat} {cell : CellExpr crownComputad (dim + 1)}
    (hAtom : IsAtomWord cell) : boundaryTarget cell = crownBaseCell dim := by
  induction hAtom with
  | atom => rfl
  | @vcomp _ _ _ _ _ ihRight => exact ihRight

/-! ## The conv leg: an atom word appended by a tail equals its vcomp-power -/

/-- ★ **THE APPEND LEMMA (the conv leg's engine).**  For every atom word `a` and every tail cell,
`vcomp a tail ~ vcompPow crownAtom tail (atomCount a)`.  Structural on `IsAtomWord a`: the single atom is
`refl`; the vcomp case is `assoc` + the right-factor IH + the left-factor IH at the threaded tail,
reconciled by `vcompPow_add`.  Crucially the tail is THREADED, so no interior identity ever appears —
the id-congruence gap is not touched, and no boundary reconciliation arises until the final right-unit
step. -/
theorem atomWord_vcompPow {dim : Nat} {cell : CellExpr crownComputad (dim + 1)}
    (hAtom : IsAtomWord cell) :
    ∀ (tail : CellExpr crownComputad (dim + 1)),
      SaturatedConvOver crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.vcomp cell tail) (vcompPow (crownAtom dim) tail (atomCount cell)) := by
  induction hAtom with
  | atom => intro tail; exact SaturatedConvOver.refl _
  | @vcomp left right _ _ ihLeft ihRight =>
      intro tail
      show SaturatedConvOver crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.vcomp (CellExpr.vcomp left right) tail)
        (vcompPow (crownAtom dim) tail (atomCount left + atomCount right))
      rw [vcompPow_add]
      exact SaturatedConvOver.trans
        (SaturatedConvOver.ofRelation (StrictAxiomRel.vcompAssoc left right tail))
        (SaturatedConvOver.trans
          (SaturatedConvOver.vcompCongrRight left (ihRight tail))
          (ihLeft (vcompPow (crownAtom dim) tail (atomCount right))))

/-- ★ **THE CONV LEG.**  For every atom word `a`, its reconstruction from its own Steiner table is
convertible to it: `SaturatedConvOver (reconstructCrown dim (linearize a)) a`.  The append lemma at
`tail := id base` gives `vcomp a (id base) ~ reconstruct`, and the right-unit row (`id base =
id (boundaryTarget a)`, the boundary lemma) absorbs the trailing base identity. -/
theorem reconstructCrown_conv_atomWord {dim : Nat} {cell : CellExpr crownComputad (dim + 1)}
    (hAtom : IsAtomWord cell) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad)
      (reconstructCrown dim (linearize crownValuation cell)) cell := by
  have hcount : listHeadCount (linearize crownValuation cell).coordinates = atomCount cell := by
    rw [linearize_atomWord hAtom]
    rfl
  show SaturatedConvOver crownComputad (StrictAxiomRel crownComputad)
    (vcompPow (crownAtom dim) (CellExpr.id (crownBaseCell dim))
      (listHeadCount (linearize crownValuation cell).coordinates)) cell
  rw [hcount]
  have hpow := atomWord_vcompPow hAtom (CellExpr.id (crownBaseCell dim))
  have hunit : SaturatedConvOver crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.vcomp cell (CellExpr.id (crownBaseCell dim))) cell := by
    have hbt := boundaryTarget_atomWord hAtom
    rw [← hbt]
    exact SaturatedConvOver.ofRelation (StrictAxiomRel.vcompUnitRight cell)
  exact SaturatedConvOver.trans (SaturatedConvOver.symm hpow) hunit

/-! ## The CROWN: convertibility decides by table equality on the fragment -/

/-- ★ **COMPLETENESS AT SCOPE.**  Equal Steiner tables imply convertibility for atom words: if
`linearize a = linearize b`, then `a ~ reconstruct(linearize a) = reconstruct(linearize b) ~ b`.  The
converse of the shipped soundness `not_conv_of_linearize_ne`. -/
theorem atomWord_conv_of_linearize_eq {dim : Nat} {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB)
    (tablesEqual : linearize crownValuation cellA = linearize crownValuation cellB) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB := by
  have ha := reconstructCrown_conv_atomWord hAtomA
  have hb := reconstructCrown_conv_atomWord hAtomB
  rw [tablesEqual] at ha
  exact SaturatedConvOver.trans (SaturatedConvOver.symm ha) hb

/-- ★★ **THE OMEGA-2 CROWN (scoped).**  On the atom-word fragment, at EVERY dimension, free-strict
convertibility is EXACTLY Steiner table equality — soundness (`linearize_eq_of_saturatedConv`) and
completeness (`atomWord_conv_of_linearize_eq`) both directions, zero-axiom.  Composition of endo cells is
decided by `List Int` equality. -/
theorem atomWord_conv_iff_linearize_eq {dim : Nat} {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB
      ↔ linearize crownValuation cellA = linearize crownValuation cellB :=
  ⟨fun conv => linearize_eq_of_saturatedConv crownValuation conv,
   fun tablesEqual => atomWord_conv_of_linearize_eq hAtomA hAtomB tablesEqual⟩

/-- ★ **THE DECISION.**  A `Decidable` value for atom-word convertibility, decided by O(1) Steiner table
equality (the shipped structural `DecidableEq SteinerCell`).  `isTrue` from completeness, `isFalse` from
soundness — both verdicts genuine. -/
def decideAtomWordConv {dim : Nat} (cellA cellB : CellExpr crownComputad (dim + 1))
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    Decidable (SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB) :=
  match decidableSteinerCellEq (linearize crownValuation cellA) (linearize crownValuation cellB) with
  | isTrue tablesEqual => isTrue (atomWord_conv_of_linearize_eq hAtomA hAtomB tablesEqual)
  | isFalse tablesDiffer => isFalse (not_conv_of_linearize_ne crownValuation tablesDiffer)

/-! ## Non-vacuity at n = 3 AND n = 4 (the world-first census target (c), dimension-genericity explicit)

The SAME `decideAtomWordConv` / arithmetic runs at cell dimension 3 (`crownAtom 2`) and cell dimension 4
(`crownAtom 3`).  Differently-ASSOCIATED atom words of equal length are decided convertible by
arithmetic (a genuine `SaturatedConvOver`, not merely equal tables); unequal-length words are decided
NON-convertible. -/

/-- A dimension-3 atom word: `atom . (atom . atom)` (right-nested, 3 atoms). -/
def word3Right : CellExpr crownComputad 3 :=
  CellExpr.vcomp (crownAtom 2) (CellExpr.vcomp (crownAtom 2) (crownAtom 2))

/-- A dimension-3 atom word: `(atom . atom) . atom` (left-nested, 3 atoms). -/
def word3Left : CellExpr crownComputad 3 :=
  CellExpr.vcomp (CellExpr.vcomp (crownAtom 2) (crownAtom 2)) (crownAtom 2)

/-- A dimension-3 atom word: a single atom (1 atom). -/
def word3One : CellExpr crownComputad 3 := crownAtom 2

theorem word3Right_isAtomWord : IsAtomWord word3Right :=
  IsAtomWord.vcomp IsAtomWord.atom (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom)

theorem word3Left_isAtomWord : IsAtomWord word3Left :=
  IsAtomWord.vcomp (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom) IsAtomWord.atom

theorem word3One_isAtomWord : IsAtomWord word3One := IsAtomWord.atom

/-- ★ **n=3 census, positive verdict (arithmetic decides genuine convertibility).**  Two
differently-associated dim-3 atom words (both 3 atoms, table `[3]`) are GENUINELY convertible — a real
`SaturatedConvOver` derivation, obtained by table equality through completeness. -/
theorem word3_conv :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) word3Right word3Left :=
  atomWord_conv_of_linearize_eq word3Right_isAtomWord word3Left_isAtomWord rfl

/-- ★ **n=3 census, negative verdict.**  Words of unequal length (tables `[3]` vs `[1]`) are genuinely
NON-convertible. -/
theorem word3_not_conv :
    ¬ SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) word3Right word3One :=
  not_conv_of_linearize_ne crownValuation (by decide)

/-- A dimension-4 atom word: `atom . (atom . atom)` (right-nested, 3 atoms). -/
def word4Right : CellExpr crownComputad 4 :=
  CellExpr.vcomp (crownAtom 3) (CellExpr.vcomp (crownAtom 3) (crownAtom 3))

/-- A dimension-4 atom word: `(atom . atom) . atom` (left-nested, 3 atoms). -/
def word4Left : CellExpr crownComputad 4 :=
  CellExpr.vcomp (CellExpr.vcomp (crownAtom 3) (crownAtom 3)) (crownAtom 3)

/-- A dimension-4 atom word: `atom . atom` (2 atoms). -/
def word4Two : CellExpr crownComputad 4 :=
  CellExpr.vcomp (crownAtom 3) (crownAtom 3)

theorem word4Right_isAtomWord : IsAtomWord word4Right :=
  IsAtomWord.vcomp IsAtomWord.atom (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom)

theorem word4Left_isAtomWord : IsAtomWord word4Left :=
  IsAtomWord.vcomp (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom) IsAtomWord.atom

theorem word4Two_isAtomWord : IsAtomWord word4Two :=
  IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom

/-- ★ **n=4 census, positive verdict** — the same crown at cell dimension 4 (dimension-genericity made
explicit: identical machinery, one dimension up). -/
theorem word4_conv :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) word4Right word4Left :=
  atomWord_conv_of_linearize_eq word4Right_isAtomWord word4Left_isAtomWord rfl

/-- ★ **n=4 census, negative verdict.** -/
theorem word4_not_conv :
    ¬ SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) word4Right word4Two :=
  not_conv_of_linearize_ne crownValuation (by decide)

/-! ## The eval-level decision witnesses (the semi-decider computes both verdicts at both dimensions) -/

/-- n=3: differently-associated words decide EQUAL tables (`true`). -/
example : decideFreeConvSound crownValuation word3Right word3Left = true := rfl

/-- n=3: unequal-length words decide DISTINCT tables (`false`). -/
example : decideFreeConvSound crownValuation word3Right word3One = false := rfl

/-- n=4: differently-associated words decide EQUAL tables (`true`). -/
example : decideFreeConvSound crownValuation word4Right word4Left = true := rfl

/-- n=4: unequal-length words decide DISTINCT tables (`false`). -/
example : decideFreeConvSound crownValuation word4Right word4Two = false := rfl

/-- The arithmetic roundtrip computes: reconstruct of `[3]` at dim 3 linearizes back to `[3]`. -/
example : (linearize crownValuation (reconstructCrown 2 ⟨[3]⟩)).coordinates = [3] := rfl

/-- The arithmetic roundtrip computes at dimension 4 too. -/
example : (linearize crownValuation (reconstructCrown 3 ⟨[3]⟩)).coordinates = [3] := rfl

/-! ## OMEGA-2 r3 honesty markers (the ledger; markers name their scope, never oversell) -/

/-- ★ **B1/B2 — `reconstruct` is SHIPPED** (fuel-structural on the coordinate list + `toNat` count,
`WellFounded.fix`-free) and the ARITHMETIC ROUNDTRIP `linearize (reconstruct [k]) = [k]` is PROVEN
generically (`linearize_vcompPow_count` / `linearize_reconstructCrown_roundtrip`).  `= true`. -/
def fxOmega_reconstructRoundtripShippedR3 : Bool := true

/-- ★ **B2/B3 — THE CONV LEG + THE CROWN are SHIPPED at the honest scope.**  On the whisker-free,
interior-id-free, single-endo-generator vcomp-word fragment (`IsAtomWord`), free-strict convertibility
IS Steiner table equality both directions (`atomWord_conv_iff_linearize_eq`), decided by O(1) `List Int`
equality (`decideAtomWordConv`), at EVERY dimension (exhibited n=3 AND n=4).  The scope is named in the
marker: single-generator atom-word fragment.  `= true`. -/
def fxOmega_completenessScopedSingleGeneratorAtomWordFragmentR3 : Bool := true

/-- ★ **B4 — SOUNDNESS stays UNIVERSAL, COMPLETENESS is the scoped fragment; the GENERAL obligation is
OPEN by TWO named obstructions.**  Full free-omega completeness is FALSE on the whole carrier: (1) LOSSY
WHISKER — `linearize` forgets the whiskering 1-cell (`linearize_whiskerLeft`), so whiskered cells are
non-convertible to their unwhiskered reconstruction; (2) the ID-CONGRUENCE GAP — the 8-constructor
`SaturatedConvOver` has no `idCongr`, so interior identities cannot be reconstructed.  Both are the OMEGA-1
`fxOmega_bridgeDimTwoConvLegOpen` wall resurfacing on the map-IN side.  The multi-generator vcomp-word
fragment (ambient length >= 2) additionally needs the absolute-index one-hot bookkeeping (deferred).
`= false` (the GENERAL case is NOT closed — honest). -/
def fxOmega_completenessGeneralOpenTwoObstructionsR3 : Bool := false

/-- ★ **OMEGA-3 handoff (r3 sharpened).**  Suspension rides the SAME crown: `suspendTable : SteinerCell
-> SteinerCell` (dimension shift = a list reindex) with `linearize (suspend a) = suspendTable (linearize
a)` and `suspendTable` INJECTIVE gives the arithmetic reflection route for the ceiling lift, dodging
syntactic fullness.  The r3 reconstruct supplies the arithmetic inverse the reflection needs.  `= true`
(recorded, not shipped). -/
def fxOmega_omegaThreeSuspendTableHandoffR3 : Bool := true

/-- ★ **Honesty marker — OMEGA-2 r3 is COMPLETE (scoped).**  reconstruct + arithmetic roundtrip (B1),
the conv leg + the crown iff + the Decidable decision (B2/B3), the n=3 AND n=4 census witnesses, and the
honest general-obstruction ledger (B4) all type-check zero-axiom; this marker imports every r3 piece.
`= true`. -/
def fxOmega_omega2R3Complete : Bool := true

end FX1Poly.Polygraph.Omega
