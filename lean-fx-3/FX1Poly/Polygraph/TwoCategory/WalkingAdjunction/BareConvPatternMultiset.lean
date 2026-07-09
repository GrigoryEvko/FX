import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvWordCodeCompleteness

/-! # mode-3 floor — the bare-`TwoCellConv` PER-GENERATOR PATTERN-MULTISET: the sound, NON-ADDITIVE invariant that
is the SUP of the entire additive scalar tower — machine-checked to SEPARATE the r4 `wordCode` collision (where
every additive scalar collided), yet NOT proven complete (the finer Cartier–Foata clique-SEQUENCE is)

`BareConvWordCodeCompleteness` (r4) machine-refuted the LAST additive scalar: `RawTwoCellExpr.wordCode`
(`Σ_gen code(pattern gen)`, the injective-per-pattern base-2 code) is INCOMPLETE on general cells — the
two-generator Godement pair `wordCodeCollisionLeft` / `wordCodeCollisionRight` has EQUAL `wordCode` (`5 = 5`, code
multisets `{4, 1}` vs `{2, 3}`) yet is not bare.  r4's own reading: since `code` is injective per pattern, NO
additive `Σ_gen φ(pattern)` word-code decides bare conv, and the genuinely complete bare invariant is strictly the
per-generator pattern MULTISET (the order-forgetting bag of per-generator whisker words).  This file BUILDS that
multiset and settles its exact status — the FINAL flip-reachable direction of the flag-B arc.

## The carrier and why it is the sup of the scalar tower

The per-generator "pattern" is the `{L, R}` whisker word wrapping one generator (`false = L = whiskerLeft`,
`true = R = whiskerRight`, outermost-first — the same reading as `frameWord` / `wordCode`).
`RawTwoCellExpr.patternMultiplicity a target` = the number of generators of `a` whose pattern is exactly `target`
— i.e. the coordinate-`target` value of the pattern MULTISET, as its count-function `List Bool → Nat`.  Each
single coordinate `patternMultiplicity · target` is itself an additive per-generator moment
`Σ_gen [pattern gen = target]` (so r4 refutes each single coordinate), but the WHOLE FAMILY
`{patternMultiplicity · target}_target` IS the multiset and does NOT collapse to any additive scalar shadow: every
shipped additive invariant (`whiskerSum`, `rSum`, `crossSum`, `leftCount`, `coCrossSum`, `nestedCrossSum`,
`wordCode`) is `Σ_gen φ(pattern gen)` and therefore FACTORS THROUGH this multiset.  The pattern-multiset is the
categorical SUP of the entire additive scalar tower.

## What this file ships (each piece zero-axiom)

  ★ **`RawTwoCellExpr.patternMultiplicity`** — the multiset carrier as a count-function `List Bool → Nat`.  Full
    five-case match, `target` threaded (peeled in the whisker cases), constant `Nat` motive — propext-free,
    structural on the expression (never on `target`).
  ★★ **`TwoCellStep.patternMultiplicity_eq` / `TwoCellConv.patternMultiplicity_eq`** — SOUNDNESS: bare conv
    preserves the multiset at EVERY coordinate, over all 12 bare `TwoCellStep` ctors INCLUDING `interchange`.
    This is why the carrier must be an order-FORGETTING multiset and not a list: `interchange` PERMUTES the
    generator order (moving generators across the vcomp boundary) while preserving each generator's pattern
    exactly — the Eckmann–Hilton order-collapse (nLab computad: `βα = αβ`, "no way to distinguish α from β").
    `Nat`-valued throughout, so every arm is a plain `Nat` identity (`zero_add` / `add_assoc` / `add_zero`-defeq /
    the inductive hypothesis at the peeled target); interchange is a 3-way `cases target` with `zero_add`, far
    cleaner than `wordCode`'s eight-atom shuffle — no `List.append` traps.
  ★ **`wcc_not_conv_viaMultiset`** — the r4 collision pair `wordCodeCollisionLeft` / `wordCodeCollisionRight` is
    machine-SEPARATED by the multiset: coordinate `[L]` scores `1` vs `0` (`wcc_left_patternMultiplicity_L` /
    `wcc_right_patternMultiplicity_L`), so the pair is NOT bare `TwoCellConv` — proven via the multiset ALONE,
    independent of `coCrossSum`.  The multiset DECIDES where every additive scalar collided: the SHARPEST bare
    invariant in the tower.  Cross-checks reproduce r1's `whiskerExchange` (`[L,R]` / `[R,L]`) and r2's composite
    (`[L,R,R,L]` / `[R,L,L,R]`) separations.
  ★ **`RawTwoCellExpr.sortedPatternMultiset` + `listListBoolDecEq`** — the multiset as a SORTED canonical
    `List (List Bool)` (insertion-sorted by `listBoolLe`, prepend-preserving), with a hand-rolled structural
    `DecidableEq` (cons-only, reusing `listBoolDecEq`, NEVER `Multiset` / `Quot` / `Quot.sound`).  So multiset
    equality is DECIDABLE zero-axiom — decidability is NOT the obstruction; the pair's sorted forms differ
    (`[[false],[true,false]]` vs `[[false,false],[true]]`, `wordCodeCollision_sortedPatternMultiset_differs`).

## The exact status — NEITHER a flip NOR a "no-invariant" wall (the honest terminal)

The multiset is SOUND (proven) and the RIGHT KIND (order-forgetting = exactly what the interchange Eckmann–Hilton
collapse demands) and SEPARATES every exhibited collision (proven, strictly beyond the whole additive tower).  It
is NOT proven COMPLETE, and completeness is deliberately NOT fabricated:

  * A FLIP (flat-multiset completeness `TwoCellConvFull a b → patternMultiplicity a = patternMultiplicity b →
    TwoCellConv a b`) would make `bareConvViaMultiset := TwoCellConvFull ∧ equal sorted multiset` a total
    `Decidable (bare TwoCellConv)` (the faithful full-conv decision × `listListBoolDecEq`).  But per the
    literature settlement the FLAT multiset is almost certainly INCOMPLETE: the complete invariant of a
    Mazurkiewicz trace monoid is the ordered Cartier–Foata clique-SEQUENCE (Diekert–Muscholl; two traces are
    equal IFF their clique-sequences are — sequences of pairwise-independent cliques with the `c → c'`
    admissibility), which retains the per-level / adjacency structure a single order-forgetting bag discards.  A
    flat multiset is the same SPECIES of shadow as the additive scalars, one level up.  Completeness within a
    full-conv class is exactly the interchange critical-pair coherence (Gratzer) — research-grade, NOT
    zero-axiom-reachable in one round.  We do NOT ship it.

  * A "no invariant of any structural class decides bare conv" WALL would be FALSE: the planar interchange word
    problem IS decidable via a STRUCTURAL invariant — Makkai's word-problem procedure for free strict
    ω-categories, and Delpeuch–Vicary's strongly-normalizing exchange-move rewriting (linear on connected /
    QUADRATIC in general), both deciding it via the string-diagram / clique-sequence normal form.  So bare conv
    is decidable IN PRINCIPLE, and the mechanised total decider needs strictly the FINER clique-sequence, not any
    flat bag.  The only GENUINELY research-open frontier is the dimension-3 braided / Gray lift (Delpeuch: the
    braided-monoidal word problem is unknotting-hard, decidability merely conjectured) — which the PLANAR bare
    2-cell structure never reaches.

Hence the honest terminal: the flat pattern-multiset is shipped as the machine-checked CEILING of the additive
scalar tower (the first non-additive, order-forgetting bare invariant, separating the r4 pair where every scalar
collided), and `fxMode_hasBareConvFlatPatternMultisetSoundAndSeparating := true` records exactly that, with the
completeness gap characterized precisely as the finer (still decidable, still structural) Cartier–Foata
clique-sequence.  `fxMode_hasModeRelativeConvDecision` (its terminal disposition in `ModeRelativeMetatheory`)
STAYS `false` — the general bare decision remains the open Gratzer coherence, re-openable and NOT
undecidability-walled.  r1 / r2 / r3 / r4 soundness and shipped statements are NOT weakened; the disposed trace /
nfCell carriers are NOT re-flipped; the saturated / faithful decisions are untouched.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
carrier is a constant-`Nat`-motive full-enum match; soundness is `induction` on the step with `Nat.zero_add` /
`Nat.add_assoc` / `cases target` + the inductive hypothesis — never `omega`/`simp`/`ac_rfl`; the sorted carrier is
a hand-rolled insertion sort + structural `listListBoolDecEq`, NEVER `Multiset`/`Quot`).  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-generator pattern-multiset carrier (count-function form) -/

/-- ★ The **per-generator pattern MULTISET** of a free 2-cell, as its count-function `List Bool → Nat`:
`patternMultiplicity a target` = the number of generators of `a` whose `{L, R}` whisker word (outermost-first,
`false = L`, `true = R`) is exactly `target`.  A generator scores `1` at `[]` (its pattern is the empty word), `0`
elsewhere; an identity scores `0`; a `vcomp` sums the factors' counts; a LEFT whisker prepends `L` to every
generator's pattern, so its count at `false :: rest` is the body's count at `rest` (and `0` at `true :: _` / `[]`);
a RIGHT whisker prepends `R` dually.  Structural on the EXPRESSION (`target` is a threaded parameter, peeled in the
whisker cases, never the recursion measure).  Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.patternMultiplicity {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → List Bool → Nat
  | _, _, _, _, .gen _, target => match target with | [] => 1 | _ :: _ => 0
  | _, _, _, _, .id _, _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta, target =>
      cellAlpha.patternMultiplicity target + cellBeta.patternMultiplicity target
  | _, _, _, _, .whiskerLeft _ body, target =>
      match target with
      | false :: rest => body.patternMultiplicity rest
      | true :: _ => 0
      | [] => 0
  | _, _, _, _, .whiskerRight _ body, target =>
      match target with
      | true :: rest => body.patternMultiplicity rest
      | false :: _ => 0
      | [] => 0

/-! ## Soundness: bare conv preserves the multiset at every coordinate (interchange included) -/

/-- ★★ **The pattern-multiset is invariant under one 3-cell rewrite — INCLUDING interchange, at every
coordinate.**  Identity removal drops a `0` factor (`Nat.zero_add` / `Nat.add_zero`-defeq); re-association is
`Nat.add_assoc`; whisker-over-vcomp distribution and the whisker-identity laws are `cases target` (each arm `rfl`);
the four congruences thread the inductive hypothesis at the peeled target.  The INTERCHANGE law is the crux and the
cleanest: `interchange` PERMUTES the generator order (moving generators across the vcomp boundary via the Godement
product) while preserving each generator's pattern EXACTLY — so at each coordinate the source and target sum the
SAME per-generator counts, split by the `target` head (`true` selects the R-side `α / α'`, `false` the L-side
`β / β'`, the other side `0`).  A 3-way `cases target` with `Nat.zero_add` closes it — no eight-atom reassociation
(the multiset never mixes generators across the L/R split).  This is why the carrier must be an order-forgetting
MULTISET, not a list: interchange scrambles the order, and the multiset is the interchange-invariant residual
(the Eckmann–Hilton order-collapse).  By induction on the step, with `target` universally quantified so the
whisker-congruence IHs apply at the peeled coordinate. -/
theorem TwoCellStep.patternMultiplicity_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) :
    ∀ target, expr.patternMultiplicity target = reduct.patternMultiplicity target := by
  induction step with
  | vcompIdLeft _ =>
      intro target; dsimp only [RawTwoCellExpr.patternMultiplicity]; exact Nat.zero_add _
  | vcompIdRight _ => intro target; rfl
  | vcompAssoc _ _ _ =>
      intro target; dsimp only [RawTwoCellExpr.patternMultiplicity]; exact Nat.add_assoc _ _ _
  | whiskerLeftId _ _ =>
      intro target; cases target with
      | nil => rfl
      | cons head _ => cases head with | false => rfl | true => rfl
  | whiskerRightId _ _ =>
      intro target; cases target with
      | nil => rfl
      | cons head _ => cases head with | false => rfl | true => rfl
  | whiskerLeftVcomp _ _ _ =>
      intro target; cases target with
      | nil => rfl
      | cons head _ => cases head with | false => rfl | true => rfl
  | whiskerRightVcomp _ _ _ =>
      intro target; cases target with
      | nil => rfl
      | cons head _ => cases head with | false => rfl | true => rfl
  | vcompCongrLeft _ _ ih =>
      intro target; dsimp only [RawTwoCellExpr.patternMultiplicity]; rw [ih target]
  | vcompCongrRight _ _ ih =>
      intro target; dsimp only [RawTwoCellExpr.patternMultiplicity]; rw [ih target]
  | whiskerLeftCongr _ _ ih =>
      intro target; cases target with
      | nil => rfl
      | cons head rest => cases head with | false => exact ih rest | true => rfl
  | whiskerRightCongr _ _ ih =>
      intro target; cases target with
      | nil => rfl
      | cons head rest => cases head with | false => rfl | true => exact ih rest
  | interchange _ _ _ _ =>
      intro target
      dsimp only [RawTwoCellExpr.hcomp, RawTwoCellExpr.patternMultiplicity]
      cases target with
      | nil => rfl
      | cons head _ =>
          cases head with
          | false => rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]
          | true => rfl

/-- **The pattern-multiset is invariant under 2-cell convertibility.**  A single step is `patternMultiplicity_eq`;
reflexivity is `rfl`; symmetry / transitivity chain through `Eq` at each coordinate.  A genuine BARE-conv invariant
surviving interchange, and the FIRST non-additive one — the sup of the whole additive scalar tower. -/
theorem TwoCellConv.patternMultiplicity_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) :
    ∀ target, expr.patternMultiplicity target = reduct.patternMultiplicity target := by
  induction conv with
  | ofStep step => exact step.patternMultiplicity_eq
  | refl _ => intro target; rfl
  | symm _ ih => intro target; exact (ih target).symm
  | trans _ _ ih1 ih2 => intro target; exact (ih1 target).trans (ih2 target)

/-! ## The multiset SEPARATES the r4 collision — where every additive scalar collided -/

/-- The LEFT r4 member scores `1` at coordinate `[L]` (`[false]`): its second Godement factor is the single
generator with pattern exactly `[L]`. -/
theorem wcc_left_patternMultiplicity_L :
    wordCodeCollisionLeft.patternMultiplicity [false] = 1 := rfl

/-- The RIGHT r4 member scores `0` at coordinate `[L]`: its generators have patterns `[R]` and `[L, L]`, neither
`[L]`. -/
theorem wcc_right_patternMultiplicity_L :
    wordCodeCollisionRight.patternMultiplicity [false] = 0 := rfl

/-- ★ **The multiset SEPARATES the r4 `wordCode` collision pair — the pair is NOT bare `TwoCellConv`, via the
multiset alone.**  `wordCodeCollisionLeft` / `wordCodeCollisionRight` are `TwoCellConvFull` with EQUAL `wordCode`
(`5 = 5`) yet DISTINCT pattern-multisets (coordinate `[L]` scores `1` vs `0`), and `patternMultiplicity` is a
bare-conv invariant (`TwoCellConv.patternMultiplicity_eq`), so they are not bare-convertible.  This DECIDES the
exact pair where the additive `wordCode` (and every additive `Σ_gen φ(pattern)` scalar) collided — the multiset is
the sharpest bare invariant of the tower.  (An independent proof of `wordCodeCollision_not_twoCellConv`, which r4
established via `coCrossSum`; here via the strictly sharper multiset.) -/
theorem wcc_not_conv_viaMultiset :
    ¬ TwoCellConv adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight := by
  intro conv
  have hCoordinate := conv.patternMultiplicity_eq [false]
  rw [wcc_left_patternMultiplicity_L, wcc_right_patternMultiplicity_L] at hCoordinate
  exact Nat.noConfusion hCoordinate

/-! ## Cross-checks: the multiset reproduces the r1 / r2 fragment separations -/

/-- Cross-check (r1): `whiskerExchange` `[L,R]` scores `1` at its own coordinate `[L,R]`, `[R,L]` scores `0` — the
multiset reproduces the r1 whiskerExchange refutation. -/
theorem whiskerExchange_patternMultiplicity_separates :
    whiskerExchangeLHS.patternMultiplicity [false, true] = 1
      ∧ whiskerExchangeRHS.patternMultiplicity [false, true] = 0 :=
  ⟨rfl, rfl⟩

/-- Cross-check (r2): the composite `[L,R,R,L]` scores `1` at its own coordinate, `[R,L,L,R]` scores `0` — the
multiset reproduces the r2 composite refutation. -/
theorem cellLRRL_patternMultiplicity_separates :
    cellLRRL.patternMultiplicity [false, true, true, false] = 1
      ∧ cellRLLR.patternMultiplicity [false, true, true, false] = 0 :=
  ⟨rfl, rfl⟩

/-! ## The sorted canonical carrier — decidable multiset equality, NEVER `Multiset` / `Quot` -/

/-- Lexicographic `≤` on `List Bool` (`false < true`), `Bool`-valued — full-enum head match, structural on the
first list, propext-free.  The sort key for the canonical multiset representative. -/
def listBoolLe : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | firstBit :: firstRest, secondBit :: secondRest =>
      match firstBit, secondBit with
      | false, true => true
      | true, false => false
      | false, false => listBoolLe firstRest secondRest
      | true, true => listBoolLe firstRest secondRest

/-- Insert a pattern into a `listBoolLe`-sorted list of patterns, keeping it sorted.  Full-enum `Bool` match on the
comparison (no `ite` — propext-clean), structural on the accumulator. -/
def insertPat : List Bool → List (List Bool) → List (List Bool)
  | pat, [] => [pat]
  | pat, head :: rest =>
      match listBoolLe pat head with
      | true => pat :: head :: rest
      | false => head :: insertPat pat rest

/-- Merge two sorted pattern-lists into one (insertion of each left element), structural on the first. -/
def mergePat : List (List Bool) → List (List Bool) → List (List Bool)
  | [], right => right
  | head :: rest, right => insertPat head (mergePat rest right)

/-- ★ The **per-generator pattern MULTISET as a SORTED canonical `List (List Bool)`** — the decidable carrier.  A
generator contributes its (empty, so far) pattern `[]`; an identity contributes nothing; a `vcomp` merges the
factors' multisets; a LEFT / RIGHT whisker prepends `L` / `R` to every pattern (prepend preserves lex-sortedness,
all patterns gaining the same head).  Insertion-sorted throughout, so it is a canonical representative of the
multiset — equal cells (same multiset) give the SAME sorted list.  Structural, constant-`List`-motive full-enum —
propext-free.  Its through-conv soundness (`TwoCellConv a b → sortedPatternMultiset a = sortedPatternMultiset b`)
reduces to the coordinate soundness (`patternMultiplicity_eq`) via multiset extensionality (the `mergePat`
commutative-monoid lemmas) — deferred, as the FLIP is not sought; the sorted carrier ships as the DECIDABLE
fingerprint. -/
def RawTwoCellExpr.sortedPatternMultiset {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → List (List Bool)
  | _, _, _, _, .gen _ => [[]]
  | _, _, _, _, .id _ => []
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      mergePat cellAlpha.sortedPatternMultiset cellBeta.sortedPatternMultiset
  | _, _, _, _, .whiskerLeft _ body => body.sortedPatternMultiset.map (fun pat => false :: pat)
  | _, _, _, _, .whiskerRight _ body => body.sortedPatternMultiset.map (fun pat => true :: pat)

/-- Hand-rolled structural `DecidableEq (List (List Bool))` — cons-only, reusing the inner `listBoolDecEq`
(`BareConvFragmentDecision`), `List.noConfusion`; NEVER `Multiset` / `Quot` / `Quot.sound`.  So multiset equality
is DECIDABLE zero-axiom: decidability is not the obstruction, completeness is. -/
def listListBoolDecEq : (leftList rightList : List (List Bool)) → Decidable (leftList = rightList)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by injection h)
  | _ :: _, [] => isFalse (fun h => by injection h)
  | headLeft :: tailLeft, headRight :: tailRight =>
      match listBoolDecEq headLeft headRight with
      | isFalse headDiffers => isFalse (fun h => by injection h with hHead _; exact headDiffers hHead)
      | isTrue headAgrees =>
          match listListBoolDecEq tailLeft tailRight with
          | isFalse tailDiffers => isFalse (fun h => by injection h with _ hTail; exact tailDiffers hTail)
          | isTrue tailAgrees => isTrue (by cases headAgrees; cases tailAgrees; rfl)

/-- The LEFT r4 member's sorted multiset is `[[L], [R,L]]` (`{[L], [R,L]}` canonicalized). -/
theorem wcc_left_sortedPatternMultiset :
    wordCodeCollisionLeft.sortedPatternMultiset = [[false], [true, false]] := rfl

/-- The RIGHT r4 member's sorted multiset is `[[L,L], [R]]` (`{[R], [L,L]}` canonicalized). -/
theorem wcc_right_sortedPatternMultiset :
    wordCodeCollisionRight.sortedPatternMultiset = [[false, false], [true]] := rfl

/-- ★ The r4 pair's SORTED multisets DIFFER — the decidable canonical carrier distinguishes them (equal `wordCode`
notwithstanding).  So `bareConvViaMultiset := TwoCellConvFull ∧ equal sorted multiset` would be DECIDABLE
(`listListBoolDecEq` × the faithful full-conv decision); it is COMPLETENESS, not decidability, that is unproven. -/
theorem wordCodeCollision_sortedPatternMultiset_differs :
    wordCodeCollisionLeft.sortedPatternMultiset ≠ wordCodeCollisionRight.sortedPatternMultiset := by
  rw [wcc_left_sortedPatternMultiset, wcc_right_sortedPatternMultiset]
  intro h; injection h with hHead _; injection hHead with _ hTail; injection hTail

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the per-generator pattern MULTISET is a machine-checked SOUND, NON-ADDITIVE bare-conv
invariant that SEPARATES the r4 `wordCode` collision (where every additive scalar collided), the ceiling of the
additive scalar tower — yet is NOT proven complete, and the complete decision is the strictly finer (still
decidable, still structural) Cartier–Foata clique-SEQUENCE.**

Delivered (each zero-axiom): the count-function carrier `RawTwoCellExpr.patternMultiplicity` with full bare-conv
SOUNDNESS through the interchange critical pair (`TwoCellStep.patternMultiplicity_eq` / `TwoCellConv.
patternMultiplicity_eq` — interchange PERMUTES generators while preserving each pattern, so the order-forgetting
multiset is the invariant residual); the r4-collision SEPARATION `wcc_not_conv_viaMultiset` (coordinate `[L]`:
`1` vs `0`) — the multiset DECIDES the exact pair the additive `wordCode` (and every `Σ_gen φ(pattern)` scalar)
collided on, reproducing r1's `whiskerExchange` and r2's composite separations
(`whiskerExchange_patternMultiplicity_separates`, `cellLRRL_patternMultiplicity_separates`); and the DECIDABLE
sorted canonical carrier `RawTwoCellExpr.sortedPatternMultiset` + `listListBoolDecEq` (SORTED `List (List Bool)`,
cons-only, NEVER `Multiset` / `Quot`), whose r4 forms differ (`wordCodeCollision_sortedPatternMultiset_differs`).

Reading (the exact terminal — NEITHER a flip NOR a "no-invariant" wall): the flat multiset is the SUP of the whole
additive scalar tower (`whiskerSum` / `rSum` / `crossSum` / `leftCount` / `coCrossSum` / `nestedCrossSum` /
`wordCode` each factor through it), the FIRST invariant to beat the additive tower on a concrete pair.  But it is
almost certainly INCOMPLETE: the complete invariant of the interchange (Mazurkiewicz) trace monoid is the ordered
Cartier–Foata clique-SEQUENCE (Diekert–Muscholl — two traces equal IFF clique-sequences equal), which keeps the
per-level / adjacency structure a flat order-forgetting bag discards; flat-multiset completeness within a full-conv
class is the interchange critical-pair coherence (Gratzer), NOT fabricated here.  Crucially this is NOT "beyond
structural methods": Makkai's free-strict-ω-category word-problem procedure and Delpeuch–Vicary's
strongly-normalizing exchange-move rewriting (quadratic in general) DECIDE the planar interchange word problem via
the string-diagram / clique-sequence normal form — so bare conv is decidable IN PRINCIPLE, its mechanised total
decider owing the strictly finer clique-sequence.  The only GENUINELY research-open frontier is the dimension-3
braided / Gray lift (Delpeuch: braided-monoidal word problem unknotting-hard, decidability conjectured), which the
PLANAR bare 2-cell never reaches.

Untouched / not weakened: `fxMode_hasModeRelativeConvDecision` STAYS `false` (its terminal disposition in
`ModeRelativeMetatheory` — the general bare decision remains the open Gratzer coherence, re-openable, NOT
undecidability-walled); r1 / r2 / r3 / r4 soundness and shipped statements are NOT weakened; the disposed
trace / nfCell carriers are NOT re-flipped; the saturated / faithful decisions are untouched.  This flag records
the multiset's exact status: sound, separating, the ceiling of the scalar tower — completeness deferred to the
finer clique-sequence.  `= true`. -/
def fxMode_hasBareConvFlatPatternMultisetSoundAndSeparating : Bool := true

end FX1Poly.Polygraph
