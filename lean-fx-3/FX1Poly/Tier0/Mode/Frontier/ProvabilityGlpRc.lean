import FX1Poly.Tier0.Mode.Provability

/-! # mode-23 frontier — the Reflection Calculus RC + GLP worms, over the `boxAt` semantics

This file extends `FX1Poly/Tier0/Mode/Provability.lean` (which ships GL soundness `boxOver` / `boxOver_loeb`
and the polymodal GLP layer `boxAt` / `boxAt_monotone_level` / `boxAt_loeb`) with the strictly-positive
**Reflection Calculus** RC of Dashkov–Beklemishev, its core derivability, several derived lemmas, a sound
bounded-fuel checker, and — the headline — its **soundness** against the diamond duals of the `boxAt` modalities.

RC is the strictly-positive polymodal fragment whose formulas are built from `top`, atoms, conjunction, and the
diamond operators `<n>` (the duals of the GLP boxes `[n]`):

    A, B  ::=  top  |  atom k  |  A ∧ B  |  <n> A          (n, k : Nat)

There is NO negation and NO implication.  Derivability is a sequent calculus `A ⊢ B` (`RCProves`) with the
Dashkov core: reflexivity / transitivity / `⊤`-top / conjunction intro+elim / diamond monotonicity / the
characteristic "4" `<n><n>A ⊢ <n>A` / the level-monotonicity `<n+1>A ⊢ <n>A` / the worm "J" rule
`<n+1>A ⊢ <n><n+1>A`.

## What this file ships (each piece zero-axiom)

  * `RCFormula` — the strictly-positive formula syntax (4 constructors);
  * `RCProves` — the RC derivability sequent relation (11 constructors: the Dashkov core, including the
    canonical conjunctive J rule `diamondJoin` `<n>A ∧ <m>B ⊢ <n>(A ∧ <m>B)` for `n < m`);
  * derived lemmas: `RCProves.topRefl`, `RCProves.andSwap` (conjunction commutativity),
    `RCProves.andAssocRight` / `RCProves.andAssocLeft` (conjunction associativity, both directions),
    `RCProves.andCongr` (congruence under ∧), `RCProves.diamondChain` (iterated diamond monotonicity),
    `RCProves.diamondCollapse` (the worm collapse `<n>…<n>A ⊢ <n>A`), `RCProves.diamondWorm_ofJoin` (the worm
    "J" form derived from the canonical conjunctive J — a coherence check the two presentations agree);
  * `rcCheck` + `rcCheck_sound` — a bounded-fuel, structurally-terminating, propext-clean SOUND checker
    (`rcCheck fuel a b = true → RCProves a b`): a decidable certificate for a syntactic sub-fragment (identity,
    conjunction intro/elim, same-level diamond monotonicity, the level drop) with worked non-vacuity witnesses
    (`rcCheck_certifies_levelDrop`, `rcCheck_certifies_diamondConjElim`);
  * the **soundness** half against the `boxAt` semantics:
      - `diamondAt` — the diamond dual of `Provability.boxAt`;
      - `RCInterpret` — the forcing of an `RCFormula` (diamonds ↦ `diamondAt`, atoms ↦ a valuation);
      - `GLPFrame` — the GLP frame conditions needed for RC soundness (per-level transitivity, nestedness
        `R_{n+1} ⊆ R_n`, the worm factorisation `jFactor`, and the J downward-sharing `jShareDown`);
      - ★★ `RCProves_sound` — if `RCProves A B` then on every `GLPFrame`, at every world,
        `RCInterpret A → RCInterpret B`.

## What is DEFERRED (still markers in `Provability.lean`)

  * RC *completeness* and Dashkov's polytime decidability of full RC — `rcCheck` is sound only, on a
    sub-fragment; the full normal-form / polytime decision procedure is not mechanized;
  * the ordinal analysis up to `Γ₀` (worm orderings → ordinal notations) — only the algebraic worm skeleton
    (`Worm`, `wormToFormula`, `wormDrop`, the well-founded length pre-order `wormPrecedes` +
    `wormPrecedes_wellFounded`) ships;
  * arithmetical completeness (Solovay) — needs an arithmetized PA provability predicate, out of scope here.

Zero external dependencies; raw Lean 4 + `Init` only.  Imports `FX1Poly.Tier0.Mode.Provability` for `boxAt`.
-/

namespace FX1Poly.Tier0

/-! ## The strictly-positive RC syntax -/

/-- The Reflection Calculus formula syntax: strictly positive — `top`, atoms, conjunction, and the diamond
operators `<n>`.  No negation, no implication. -/
inductive RCFormula where
  /-- The constant `⊤`. -/
  | top : RCFormula
  /-- A propositional atom, indexed by a `Nat`. -/
  | atom : Nat → RCFormula
  /-- Conjunction `A ∧ B`. -/
  | and : RCFormula → RCFormula → RCFormula
  /-- The level-`n` diamond `<n> A` (the dual of the GLP box `[n]`). -/
  | diamond : Nat → RCFormula → RCFormula
  deriving Repr

/-! ## RC derivability `A ⊢ B` -/

/-- RC derivability `A ⊢ B` (read "from `A`, `B` is reflection-derivable"), the Dashkov–Beklemishev core of
the strictly-positive Reflection Calculus.  The constructors:

  * `refl` — `A ⊢ A`;
  * `trans` — cut: `A ⊢ B` and `B ⊢ C` give `A ⊢ C`;
  * `topIntro` — `A ⊢ ⊤`;
  * `andElimLeft` / `andElimRight` — `A ∧ B ⊢ A`, `A ∧ B ⊢ B`;
  * `andIntro` — `A ⊢ B` and `A ⊢ C` give `A ⊢ B ∧ C`;
  * `diamondMono` — monotonicity: `A ⊢ B` gives `<n>A ⊢ <n>B`;
  * `diamondFour` — the characteristic "4": `<n><n>A ⊢ <n>A` (the strictly-positive Löb shadow);
  * `diamondLevel` — level monotonicity: `<n+1>A ⊢ <n>A`;
  * `diamondWorm` — the "J" / worm rule: `<n+1>A ⊢ <n><n+1>A`;
  * `diamondJoin` — the canonical Dashkov J rule: `<n>A ∧ <m>B ⊢ <n>(A ∧ <m>B)` for `n < m`. -/
inductive RCProves : RCFormula → RCFormula → Prop where
  /-- `A ⊢ A`. -/
  | refl (formula : RCFormula) : RCProves formula formula
  /-- Cut / transitivity: `A ⊢ B` and `B ⊢ C` give `A ⊢ C`. -/
  | trans {first second third : RCFormula} :
      RCProves first second → RCProves second third → RCProves first third
  /-- `A ⊢ ⊤`. -/
  | topIntro (formula : RCFormula) : RCProves formula RCFormula.top
  /-- `A ∧ B ⊢ A`. -/
  | andElimLeft (left right : RCFormula) : RCProves (RCFormula.and left right) left
  /-- `A ∧ B ⊢ B`. -/
  | andElimRight (left right : RCFormula) : RCProves (RCFormula.and left right) right
  /-- `A ⊢ B` and `A ⊢ C` give `A ⊢ B ∧ C`. -/
  | andIntro {source left right : RCFormula} :
      RCProves source left → RCProves source right → RCProves source (RCFormula.and left right)
  /-- Diamond monotonicity: `A ⊢ B` gives `<n>A ⊢ <n>B`. -/
  | diamondMono {inner outer : RCFormula} (level : Nat) :
      RCProves inner outer → RCProves (RCFormula.diamond level inner) (RCFormula.diamond level outer)
  /-- The "4" axiom in diamond form: `<n><n>A ⊢ <n>A`. -/
  | diamondFour (level : Nat) (formula : RCFormula) :
      RCProves (RCFormula.diamond level (RCFormula.diamond level formula))
        (RCFormula.diamond level formula)
  /-- Level monotonicity (dual of `boxAt_monotone_level`): `<n+1>A ⊢ <n>A`. -/
  | diamondLevel (level : Nat) (formula : RCFormula) :
      RCProves (RCFormula.diamond (level + 1) formula) (RCFormula.diamond level formula)
  /-- The "J" / worm rule: `<n+1>A ⊢ <n><n+1>A`. -/
  | diamondWorm (level : Nat) (formula : RCFormula) :
      RCProves (RCFormula.diamond (level + 1) formula)
        (RCFormula.diamond level (RCFormula.diamond (level + 1) formula))
  /-- The **canonical Dashkov J rule** (the characteristic RC rule): for `n < m`,
  `<n>A ∧ <m>B ⊢ <n>(A ∧ <m>B)` — a higher-level diamond can be absorbed under a lower-level one. -/
  | diamondJoin {lower upper : Nat} (isStrictlyLower : lower < upper) (left right : RCFormula) :
      RCProves (RCFormula.and (RCFormula.diamond lower left) (RCFormula.diamond upper right))
        (RCFormula.diamond lower (RCFormula.and left (RCFormula.diamond upper right)))

/-! ## Propext-clean Boolean splitters (local toolkit for the checker soundness) -/

/-- From `(a && b) = true`, the left conjunct holds.  Propext-clean (`cases` on `Bool` + `Bool.noConfusion`). -/
theorem rcBoolAndLeft {leftBool rightBool : Bool} (conjunctionTrue : (leftBool && rightBool) = true) :
    leftBool = true := by
  cases leftBool with
  | true => rfl
  | false => exact Bool.noConfusion conjunctionTrue

/-- From `(a && b) = true`, the right conjunct holds.  Propext-clean. -/
theorem rcBoolAndRight {leftBool rightBool : Bool} (conjunctionTrue : (leftBool && rightBool) = true) :
    rightBool = true := by
  cases leftBool with
  | true => exact conjunctionTrue
  | false => exact Bool.noConfusion conjunctionTrue

/-- Disjunction elimination on `(a || b) = true` into any goal.  Propext-clean. -/
theorem rcBoolOrElim {leftBool rightBool : Bool} (disjunctionTrue : (leftBool || rightBool) = true)
    {motive : Prop} (caseLeft : leftBool = true → motive) (caseRight : rightBool = true → motive) :
    motive := by
  cases leftBool with
  | true => exact caseLeft rfl
  | false => exact caseRight disjunctionTrue

/-! ## Derived RC lemmas -/

/-- `A ⊢ ⊤` (a renaming of `topIntro`, for the worm vocabulary). -/
theorem RCProves.topRefl (formula : RCFormula) : RCProves formula RCFormula.top :=
  RCProves.topIntro formula

/-- Conjunction commutativity: `A ∧ B ⊢ B ∧ A`. -/
theorem RCProves.andSwap (left right : RCFormula) :
    RCProves (RCFormula.and left right) (RCFormula.and right left) :=
  RCProves.andIntro (RCProves.andElimRight left right) (RCProves.andElimLeft left right)

/-- Conjunction congruence: from `A ⊢ A'` and `B ⊢ B'`, `A ∧ B ⊢ A' ∧ B'`. -/
theorem RCProves.andCongr {leftSource leftTarget rightSource rightTarget : RCFormula}
    (leftStep : RCProves leftSource leftTarget) (rightStep : RCProves rightSource rightTarget) :
    RCProves (RCFormula.and leftSource rightSource) (RCFormula.and leftTarget rightTarget) :=
  RCProves.andIntro
    (RCProves.trans (RCProves.andElimLeft leftSource rightSource) leftStep)
    (RCProves.trans (RCProves.andElimRight leftSource rightSource) rightStep)

/-- Conjunction associativity, right-nesting: `(A ∧ B) ∧ C ⊢ A ∧ (B ∧ C)`. -/
theorem RCProves.andAssocRight (alpha beta gamma : RCFormula) :
    RCProves (RCFormula.and (RCFormula.and alpha beta) gamma)
      (RCFormula.and alpha (RCFormula.and beta gamma)) :=
  RCProves.andIntro
    (RCProves.trans (RCProves.andElimLeft (RCFormula.and alpha beta) gamma)
      (RCProves.andElimLeft alpha beta))
    (RCProves.andIntro
      (RCProves.trans (RCProves.andElimLeft (RCFormula.and alpha beta) gamma)
        (RCProves.andElimRight alpha beta))
      (RCProves.andElimRight (RCFormula.and alpha beta) gamma))

/-- Conjunction associativity, left-nesting: `A ∧ (B ∧ C) ⊢ (A ∧ B) ∧ C`. -/
theorem RCProves.andAssocLeft (alpha beta gamma : RCFormula) :
    RCProves (RCFormula.and alpha (RCFormula.and beta gamma))
      (RCFormula.and (RCFormula.and alpha beta) gamma) :=
  RCProves.andIntro
    (RCProves.andIntro
      (RCProves.andElimLeft alpha (RCFormula.and beta gamma))
      (RCProves.trans (RCProves.andElimRight alpha (RCFormula.and beta gamma))
        (RCProves.andElimLeft beta gamma)))
    (RCProves.trans (RCProves.andElimRight alpha (RCFormula.and beta gamma))
      (RCProves.andElimRight beta gamma))

/-- The level-drop chained through a worm prefix: applying `diamondLevel` then re-wrapping. From `A ⊢ B`,
`<n+1>A ⊢ <n>B` (a single diamond at the dropped level). -/
theorem RCProves.diamondChain {inner outer : RCFormula} (level : Nat)
    (innerStep : RCProves inner outer) :
    RCProves (RCFormula.diamond (level + 1) inner) (RCFormula.diamond level outer) :=
  RCProves.trans (RCProves.diamondLevel level inner) (RCProves.diamondMono level innerStep)

/-- The worm collapse at a fixed level: `<n>(<n>(<n>A)) ⊢ <n>A` — the "4" applied through one extra layer. -/
theorem RCProves.diamondCollapse (level : Nat) (formula : RCFormula) :
    RCProves (RCFormula.diamond level (RCFormula.diamond level (RCFormula.diamond level formula)))
      (RCFormula.diamond level formula) :=
  RCProves.trans
    (RCProves.diamondMono level (RCProves.diamondFour level formula))
    (RCProves.diamondFour level formula)

/-- The worm form of the J rule (`<n+1>A ⊢ <n><n+1>A`) is DERIVABLE from the canonical conjunctive J rule
`diamondJoin` together with the level drop and conjunction calculus — a coherence check that the worm primitive
is subsumed by the canonical primitive (so the two presentations agree). -/
theorem RCProves.diamondWorm_ofJoin (level : Nat) (formula : RCFormula) :
    RCProves (RCFormula.diamond (level + 1) formula)
      (RCFormula.diamond level (RCFormula.diamond (level + 1) formula)) :=
  -- `<n+1>A ⊢ <n>⊤ ∧ <n+1>A` (level-drop-to-top on the left, reflexivity on the right)
  let toConjunction : RCProves (RCFormula.diamond (level + 1) formula)
      (RCFormula.and (RCFormula.diamond level RCFormula.top) (RCFormula.diamond (level + 1) formula)) :=
    RCProves.andIntro
      (RCProves.trans (RCProves.diamondLevel level formula)
        (RCProves.diamondMono level (RCProves.topIntro formula)))
      (RCProves.refl _)
  -- the canonical J rule absorbs the upper diamond: `<n>⊤ ∧ <n+1>A ⊢ <n>(⊤ ∧ <n+1>A)`
  let joinStep : RCProves
      (RCFormula.and (RCFormula.diamond level RCFormula.top) (RCFormula.diamond (level + 1) formula))
      (RCFormula.diamond level (RCFormula.and RCFormula.top (RCFormula.diamond (level + 1) formula))) :=
    RCProves.diamondJoin (Nat.lt_succ_of_le (Nat.le_refl level)) RCFormula.top formula
  -- drop the `⊤` conjunct under the lower diamond: `<n>(⊤ ∧ <n+1>A) ⊢ <n><n+1>A`
  let dropTop : RCProves
      (RCFormula.diamond level (RCFormula.and RCFormula.top (RCFormula.diamond (level + 1) formula)))
      (RCFormula.diamond level (RCFormula.diamond (level + 1) formula)) :=
    RCProves.diamondMono level (RCProves.andElimRight RCFormula.top (RCFormula.diamond (level + 1) formula))
  RCProves.trans toConjunction (RCProves.trans joinStep dropTop)

/-! ## A bounded-fuel SOUND checker (a decidable certificate on a sub-fragment) -/

/-- Structural-equality test on `RCFormula` (propext-clean: full enumeration, no wildcard arms, `Nat` equality
via `Nat.beq` decided structurally).  Returns `true` exactly on syntactically-identical formulas. -/
def rcFormulaBeq : RCFormula → RCFormula → Bool
  | RCFormula.top, RCFormula.top => true
  | RCFormula.top, RCFormula.atom _ => false
  | RCFormula.top, RCFormula.and _ _ => false
  | RCFormula.top, RCFormula.diamond _ _ => false
  | RCFormula.atom _, RCFormula.top => false
  | RCFormula.atom leftIndex, RCFormula.atom rightIndex => Nat.beq leftIndex rightIndex
  | RCFormula.atom _, RCFormula.and _ _ => false
  | RCFormula.atom _, RCFormula.diamond _ _ => false
  | RCFormula.and _ _, RCFormula.top => false
  | RCFormula.and _ _, RCFormula.atom _ => false
  | RCFormula.and leftFirst leftSecond, RCFormula.and rightFirst rightSecond =>
      rcFormulaBeq leftFirst rightFirst && rcFormulaBeq leftSecond rightSecond
  | RCFormula.and _ _, RCFormula.diamond _ _ => false
  | RCFormula.diamond _ _, RCFormula.top => false
  | RCFormula.diamond _ _, RCFormula.atom _ => false
  | RCFormula.diamond _ _, RCFormula.and _ _ => false
  | RCFormula.diamond leftLevel leftInner, RCFormula.diamond rightLevel rightInner =>
      Nat.beq leftLevel rightLevel && rcFormulaBeq leftInner rightInner

/-- `rcFormulaBeq` reflects propositional equality (the `true` direction): structurally equal ⇒ equal.
Propext-clean: structural recursion, `Nat.beq` reflection via `Nat.eq_of_beq_eq_true`, no wildcards. -/
theorem rcFormulaBeq_sound : ∀ (left right : RCFormula), rcFormulaBeq left right = true → left = right
  | RCFormula.top, RCFormula.top, _ => rfl
  | RCFormula.atom leftIndex, RCFormula.atom rightIndex, equalityProof => by
      have indicesEqual : leftIndex = rightIndex := Nat.eq_of_beq_eq_true equalityProof
      rw [indicesEqual]
  | RCFormula.and leftFirst leftSecond, RCFormula.and rightFirst rightSecond, equalityProof => by
      have rewriteConjunction :
          (rcFormulaBeq leftFirst rightFirst && rcFormulaBeq leftSecond rightSecond) = true := equalityProof
      have firstEqual : leftFirst = rightFirst :=
        rcFormulaBeq_sound leftFirst rightFirst (rcBoolAndLeft rewriteConjunction)
      have secondEqual : leftSecond = rightSecond :=
        rcFormulaBeq_sound leftSecond rightSecond (rcBoolAndRight rewriteConjunction)
      rw [firstEqual, secondEqual]
  | RCFormula.diamond leftLevel leftInner, RCFormula.diamond rightLevel rightInner, equalityProof => by
      have rewriteConjunction :
          (Nat.beq leftLevel rightLevel && rcFormulaBeq leftInner rightInner) = true := equalityProof
      have levelEqual : leftLevel = rightLevel := Nat.eq_of_beq_eq_true (rcBoolAndLeft rewriteConjunction)
      have innerEqual : leftInner = rightInner :=
        rcFormulaBeq_sound leftInner rightInner (rcBoolAndRight rewriteConjunction)
      rw [levelEqual, innerEqual]

/-- The conjunction-introduction contribution: when the target is a conjunction, check both halves from the
source.  A separate total function with a complete match (propext-clean, no wildcard). -/
def rcCheckConjIntro (recurse : RCFormula → RCFormula → Bool) (source : RCFormula) :
    RCFormula → Bool
  | RCFormula.top => false
  | RCFormula.atom _ => false
  | RCFormula.and targetLeft targetRight => recurse source targetLeft && recurse source targetRight
  | RCFormula.diamond _ _ => false

/-- The conjunction-elimination contribution: when the source is a conjunction, descend into either half. -/
def rcCheckConjElim (recurse : RCFormula → RCFormula → Bool) : RCFormula → RCFormula → Bool
  | RCFormula.top, _ => false
  | RCFormula.atom _, _ => false
  | RCFormula.and sourceLeft sourceRight, target => recurse sourceLeft target || recurse sourceRight target
  | RCFormula.diamond _ _, _ => false

/-- The diamond-rule contribution: when both source and target are diamonds, allow monotonicity at the same
level (`<n>A ⊢ <n>B` when `A ⊢ B` recursively) or the level drop (`<n+1>A ⊢ <n>A`). -/
def rcCheckDiamond (recurse : RCFormula → RCFormula → Bool) : RCFormula → RCFormula → Bool
  | RCFormula.top, _ => false
  | RCFormula.atom _, _ => false
  | RCFormula.and _ _, _ => false
  | RCFormula.diamond _ _, RCFormula.top => false
  | RCFormula.diamond _ _, RCFormula.atom _ => false
  | RCFormula.diamond _ _, RCFormula.and _ _ => false
  | RCFormula.diamond sourceLevel sourceInner, RCFormula.diamond targetLevel targetInner =>
      (Nat.beq sourceLevel targetLevel && recurse sourceInner targetInner) ||
        (Nat.beq sourceLevel (targetLevel + 1) && rcFormulaBeq sourceInner targetInner)

/-- A bounded-fuel SOUND checker for RC derivability.  `rcCheck fuel source target` searches for a derivation
`source ⊢ target` within `fuel` structural steps, combining: identity (`rcFormulaBeq`), conjunction
introduction (`rcCheckConjIntro`, keyed on the target), conjunction elimination (`rcCheckConjElim`, keyed on
the source), and the diamond rules (`rcCheckDiamond`: same-level monotonicity + the level drop).  It is SOUND
but NOT complete (it does not cover the diamond "4"/"J" or arbitrary cut chains — those remain in `RCProves`).
Structurally terminating on `fuel` (every recursive call decrements), so propext-clean. -/
def rcCheck : Nat → RCFormula → RCFormula → Bool
  | 0, _, _ => false
  | fuel + 1, source, target =>
      rcFormulaBeq source target ||
        rcCheckConjIntro (rcCheck fuel) source target ||
        rcCheckConjElim (rcCheck fuel) source target ||
        rcCheckDiamond (rcCheck fuel) source target

/-! ### Soundness of the checker's contributions -/

/-- `rcCheckConjIntro`-soundness: if the contribution fires, the target is a conjunction and both halves are
derivable from the source (given the recursive checker is sound). -/
theorem rcCheckConjIntro_sound (recurse : RCFormula → RCFormula → Bool) (source : RCFormula)
    (recurseSound : ∀ innerSource innerTarget, recurse innerSource innerTarget = true →
      RCProves innerSource innerTarget) :
    ∀ (target : RCFormula), rcCheckConjIntro recurse source target = true → RCProves source target
  | RCFormula.top, fires => by exact Bool.noConfusion fires
  | RCFormula.atom _, fires => by exact Bool.noConfusion fires
  | RCFormula.and targetLeft targetRight, fires => by
      have splitConjunction : (recurse source targetLeft && recurse source targetRight) = true := fires
      exact RCProves.andIntro
        (recurseSound source targetLeft (rcBoolAndLeft splitConjunction))
        (recurseSound source targetRight (rcBoolAndRight splitConjunction))
  | RCFormula.diamond _ _, fires => by exact Bool.noConfusion fires

/-- `rcCheckConjElim`-soundness: if the contribution fires, the source is a conjunction and the target follows
by descending into one half. -/
theorem rcCheckConjElim_sound (recurse : RCFormula → RCFormula → Bool)
    (recurseSound : ∀ innerSource innerTarget, recurse innerSource innerTarget = true →
      RCProves innerSource innerTarget) :
    ∀ (source target : RCFormula), rcCheckConjElim recurse source target = true → RCProves source target
  | RCFormula.top, _, fires => by exact Bool.noConfusion fires
  | RCFormula.atom _, _, fires => by exact Bool.noConfusion fires
  | RCFormula.and sourceLeft sourceRight, target, fires => by
      have splitDisjunction : (recurse sourceLeft target || recurse sourceRight target) = true := fires
      exact rcBoolOrElim splitDisjunction
        (fun leftFires => RCProves.trans (RCProves.andElimLeft sourceLeft sourceRight)
          (recurseSound sourceLeft target leftFires))
        (fun rightFires => RCProves.trans (RCProves.andElimRight sourceLeft sourceRight)
          (recurseSound sourceRight target rightFires))
  | RCFormula.diamond _ _, _, fires => by exact Bool.noConfusion fires

/-- `rcCheckDiamond`-soundness: if the contribution fires, both formulas are diamonds and the target follows by
same-level monotonicity or the level drop. -/
theorem rcCheckDiamond_sound (recurse : RCFormula → RCFormula → Bool)
    (recurseSound : ∀ innerSource innerTarget, recurse innerSource innerTarget = true →
      RCProves innerSource innerTarget) :
    ∀ (source target : RCFormula), rcCheckDiamond recurse source target = true → RCProves source target
  | RCFormula.top, _, fires => by exact Bool.noConfusion fires
  | RCFormula.atom _, _, fires => by exact Bool.noConfusion fires
  | RCFormula.and _ _, _, fires => by exact Bool.noConfusion fires
  | RCFormula.diamond _ _, RCFormula.top, fires => by exact Bool.noConfusion fires
  | RCFormula.diamond _ _, RCFormula.atom _, fires => by exact Bool.noConfusion fires
  | RCFormula.diamond _ _, RCFormula.and _ _, fires => by exact Bool.noConfusion fires
  | RCFormula.diamond sourceLevel sourceInner, RCFormula.diamond targetLevel targetInner, fires => by
      have splitDisjunction :
          ((Nat.beq sourceLevel targetLevel && recurse sourceInner targetInner) ||
            (Nat.beq sourceLevel (targetLevel + 1) && rcFormulaBeq sourceInner targetInner)) = true := fires
      refine rcBoolOrElim splitDisjunction (fun monoFires => ?_) (fun dropFires => ?_)
      · have levelEqual : sourceLevel = targetLevel := Nat.eq_of_beq_eq_true (rcBoolAndLeft monoFires)
        have innerProvable : RCProves sourceInner targetInner :=
          recurseSound sourceInner targetInner (rcBoolAndRight monoFires)
        rw [levelEqual]
        exact RCProves.diamondMono targetLevel innerProvable
      · have levelEqual : sourceLevel = targetLevel + 1 := Nat.eq_of_beq_eq_true (rcBoolAndLeft dropFires)
        have innerEqual : sourceInner = targetInner := rcFormulaBeq_sound _ _ (rcBoolAndRight dropFires)
        rw [levelEqual, innerEqual]
        exact RCProves.diamondLevel targetLevel targetInner

/-- The bounded-fuel checker is SOUND: `rcCheck fuel source target = true` yields a real RC derivation.
Propext-clean: structural induction on `fuel`, the four disjuncts split by `rcBoolOrElim`, each discharged by
the matching contribution-soundness lemma. -/
theorem rcCheck_sound : ∀ (fuel : Nat) (source target : RCFormula),
    rcCheck fuel source target = true → RCProves source target
  | 0, _, _, checkSucceeds => by exact Bool.noConfusion checkSucceeds
  | fuel + 1, source, target, checkSucceeds => by
      -- `rcCheck (fuel+1)` is `((reflexive || conjIntro) || conjElim) || diamond`; peel the three `||`.
      have expanded :
          (((rcFormulaBeq source target ||
              rcCheckConjIntro (rcCheck fuel) source target) ||
              rcCheckConjElim (rcCheck fuel) source target) ||
              rcCheckDiamond (rcCheck fuel) source target) = true := checkSucceeds
      have recurseSound : ∀ innerSource innerTarget, rcCheck fuel innerSource innerTarget = true →
          RCProves innerSource innerTarget := fun innerSource innerTarget =>
        rcCheck_sound fuel innerSource innerTarget
      refine rcBoolOrElim expanded (fun firstThree => ?_) (fun diamondFires => ?_)
      · refine rcBoolOrElim firstThree (fun reflOrIntro => ?_) (fun elimFires => ?_)
        · refine rcBoolOrElim reflOrIntro (fun reflexiveHit => ?_) (fun introFires => ?_)
          · have sourceEqual : source = target := rcFormulaBeq_sound _ _ reflexiveHit
            rw [sourceEqual]; exact RCProves.refl _
          · exact rcCheckConjIntro_sound (rcCheck fuel) source recurseSound target introFires
        · exact rcCheckConjElim_sound (rcCheck fuel) recurseSound source target elimFires
      · exact rcCheckDiamond_sound (rcCheck fuel) recurseSound source target diamondFires

/-! ## The diamond semantics over `Provability.boxAt`, and RC soundness -/

/-- The diamond dual of `Provability.boxAt`: `<n>φ` holds at a world iff `φ` holds at SOME level-`n`
successor. -/
def diamondAt {World : Type} (accessibleAt : Nat → World → World → Prop) (level : Nat)
    (proposition : World → Prop) : World → Prop :=
  fun world => ∃ successor, accessibleAt level world successor ∧ proposition successor

/-- The forcing of an RC formula: atoms via a valuation, `⊤` always, `∧` as conjunction, `<n>` as `diamondAt`.
Propext-clean: full 4-way structural recursion, no wildcard. -/
def RCInterpret {World : Type} (accessibleAt : Nat → World → World → Prop)
    (valuation : Nat → World → Prop) : RCFormula → World → Prop
  | RCFormula.top, _ => True
  | RCFormula.atom index, world => valuation index world
  | RCFormula.and left right, world =>
      RCInterpret accessibleAt valuation left world ∧ RCInterpret accessibleAt valuation right world
  | RCFormula.diamond level inner, world =>
      diamondAt accessibleAt level (RCInterpret accessibleAt valuation inner) world

/-- The GLP frame conditions sufficient for RC soundness:

  * `isTransitivePerLevel` — each `R_n` is transitive (validates the diamond "4" `<n><n>A ⊢ <n>A`);
  * `isNested` — `R_{n+1} ⊆ R_n` (validates the level drop `<n+1>A ⊢ <n>A`);
  * `jFactor` — every `R_{n+1}` edge factors as an `R_n`-step followed by an `R_{n+1}`-step (validates the worm
    "J" rule `<n+1>A ⊢ <n><n+1>A`);
  * `jShareDown` — for `n < m`, an `R_m` target reachable from a world is also `R_m`-reachable from any of that
    world's `R_n`-successors (validates the canonical Dashkov J rule `<n>A ∧ <m>B ⊢ <n>(A ∧ <m>B)`).

These are exactly the Beklemishev GLP frame conditions, packaged for the diamond fragment. -/
structure GLPFrame {World : Type} (accessibleAt : Nat → World → World → Prop) : Prop where
  /-- Each level's accessibility is transitive. -/
  isTransitivePerLevel : ∀ level, IsTransitiveFrame (accessibleAt level)
  /-- Higher levels see fewer successors: `R_{n+1} ⊆ R_n`. -/
  isNested : ∀ level world successor,
    accessibleAt (level + 1) world successor → accessibleAt level world successor
  /-- The worm factorisation: an `R_{n+1}` edge factors through an `R_n`-step then an `R_{n+1}`-step. -/
  jFactor : ∀ level world successor,
    accessibleAt (level + 1) world successor →
      ∃ intermediate, accessibleAt level world intermediate ∧
        accessibleAt (level + 1) intermediate successor
  /-- The downward-sharing condition for the canonical J rule: for `n < m`, if `w R_n u` and `w R_m v` then
  `u R_m v` (the `R_m`-target is shared down each `R_n`-step). -/
  jShareDown : ∀ lower upper, lower < upper → ∀ world lowerSuccessor upperSuccessor,
    accessibleAt lower world lowerSuccessor → accessibleAt upper world upperSuccessor →
      accessibleAt upper lowerSuccessor upperSuccessor

/-- ★★ **RC soundness** against the `boxAt`/`diamondAt` semantics.  If `RCProves source target`, then on every
`GLPFrame`, at every world, the forcing of `source` entails the forcing of `target`.  Proved by induction on
the RC derivation; each constructor is discharged from exactly one `GLPFrame` field (or none, for the
propositional core).  Propext-clean: `dsimp only [RCInterpret, diamondAt]` to unfold the forcing, then explicit
existential / conjunction manipulation. -/
theorem RCProves_sound {World : Type} (accessibleAt : Nat → World → World → Prop)
    (valuation : Nat → World → Prop) (frame : GLPFrame accessibleAt) :
    ∀ {source target : RCFormula}, RCProves source target →
      ∀ (world : World), RCInterpret accessibleAt valuation source world →
        RCInterpret accessibleAt valuation target world := by
  intro source target derivation
  induction derivation with
  | refl formula => intro world holds; exact holds
  | trans _ _ firstSound secondSound =>
      intro world holds; exact secondSound world (firstSound world holds)
  | topIntro formula => intro world _; exact True.intro
  | andElimLeft left right => intro world holds; exact holds.left
  | andElimRight left right => intro world holds; exact holds.right
  | andIntro _ _ leftSound rightSound =>
      intro world holds; exact And.intro (leftSound world holds) (rightSound world holds)
  | diamondMono level _ innerSound =>
      intro world holds
      dsimp only [RCInterpret, diamondAt] at holds ⊢
      match holds with
      | ⟨successor, accessibleSuccessor, innerHolds⟩ =>
          exact ⟨successor, accessibleSuccessor, innerSound successor innerHolds⟩
  | diamondFour level formula =>
      intro world holds
      dsimp only [RCInterpret, diamondAt] at holds ⊢
      match holds with
      | ⟨middle, accessibleMiddle, ⟨inner, accessibleInner, innerHolds⟩⟩ =>
          exact ⟨inner, frame.isTransitivePerLevel level world middle inner accessibleMiddle accessibleInner,
            innerHolds⟩
  | diamondLevel level formula =>
      intro world holds
      dsimp only [RCInterpret, diamondAt] at holds ⊢
      match holds with
      | ⟨successor, accessibleSuccessor, innerHolds⟩ =>
          exact ⟨successor, frame.isNested level world successor accessibleSuccessor, innerHolds⟩
  | diamondWorm level formula =>
      intro world holds
      dsimp only [RCInterpret, diamondAt] at holds ⊢
      match holds with
      | ⟨successor, accessibleSuccessor, innerHolds⟩ =>
          match frame.jFactor level world successor accessibleSuccessor with
          | ⟨intermediate, accessibleIntermediate, accessibleToSuccessor⟩ =>
              exact ⟨intermediate, accessibleIntermediate,
                ⟨successor, accessibleToSuccessor, innerHolds⟩⟩
  | diamondJoin isStrictlyLower left right =>
      intro world holds
      dsimp only [RCInterpret, diamondAt] at holds ⊢
      match holds with
      | ⟨⟨lowerSuccessor, accessibleLower, leftHolds⟩, ⟨upperSuccessor, accessibleUpper, rightHolds⟩⟩ =>
          -- the lower-successor reaches the upper target by `jShareDown`, so absorb the upper diamond under it
          have sharedDown := frame.jShareDown _ _ isStrictlyLower world lowerSuccessor upperSuccessor
            accessibleLower accessibleUpper
          exact ⟨lowerSuccessor, accessibleLower,
            ⟨leftHolds, ⟨upperSuccessor, sharedDown, rightHolds⟩⟩⟩

/-! ## The GLP worm algebraic skeleton (for the ordinal-analysis marker) -/

/-- A GLP **worm** is a list of modality levels, read as the iterated diamond `<n_1><n_2>…<n_k>⊤`.  This is the
algebraic carrier of Beklemishev's ordinal analysis; the ordinal notation itself (up to `Γ₀`) is deferred. -/
abbrev Worm : Type := List Nat

/-- Read a worm as the RC formula `<n_1><n_2>…<n_k>⊤`. -/
def wormToFormula : Worm → RCFormula
  | [] => RCFormula.top
  | level :: rest => RCFormula.diamond level (wormToFormula rest)

/-- The worm "lose a worm" decrement at the head: drop the leading modality.  (The full Beklemishev `h`/`w^n`
worm operations and their ordinal images are deferred.) -/
def wormDrop : Worm → Worm
  | [] => []
  | _ :: rest => rest

/-- Dropping the head of a non-empty worm is RC-derivable as a level-drop step is NOT what this says — rather,
the head diamond can be eliminated to `⊤` (`<n>A ⊢ <n>⊤ ⊢ … `).  We ship the basic monotone fact that the
worm's formula entails its head dropped to `⊤`: `<n>(rest) ⊢ <n>⊤`. -/
theorem wormToFormula_head_topMono (level : Nat) (rest : Worm) :
    RCProves (wormToFormula (level :: rest)) (RCFormula.diamond level RCFormula.top) := by
  dsimp only [wormToFormula]
  exact RCProves.diamondMono level (RCProves.topIntro (wormToFormula rest))

/-- The dropped worm is a structural sub-list (length strictly decreases on a non-empty worm), the well-founded
measure underlying the worm ordering. -/
theorem wormDrop_length_lt (level : Nat) (rest : Worm) :
    (wormDrop (level :: rest)).length < (level :: rest).length := by
  dsimp only [wormDrop, List.length]
  exact Nat.lt_succ_of_le (Nat.le_refl rest.length)

/-- The worm length ordering — the simplest order under which the worm operations descend.  `worm₁ ≺ worm₂` iff
`worm₁` is strictly shorter.  Beklemishev's ordinal-faithful ordering is finer (it is the very ordinal notation
we defer); this length pre-order is the well-founded skeleton on which the full analysis rests. -/
def wormPrecedes (smaller larger : Worm) : Prop := smaller.length < larger.length

/-- The worm length ordering is well-founded (every worm is accessible), via the well-foundedness of `<` on
`Nat` transported along the length measure.  Propext-clean: structural `Acc` over the `Nat` measure. -/
theorem wormPrecedes_wellFounded : ∀ (worm : Worm),
    Acc wormPrecedes worm := by
  have natAccessible : ∀ (bound : Nat) (worm : Worm), worm.length < bound → Acc wormPrecedes worm := by
    intro bound
    induction bound with
    | zero => intro worm lengthBelowZero; exact absurd lengthBelowZero (Nat.not_lt_zero worm.length)
    | succ predecessor inductiveHypothesis =>
        intro worm lengthBelowSucc
        refine Acc.intro worm (fun smaller smallerPrecedes => ?_)
        have smallerBelowPredecessor : smaller.length < predecessor :=
          Nat.lt_of_lt_of_le smallerPrecedes (Nat.le_of_lt_succ lengthBelowSucc)
        exact inductiveHypothesis smaller smallerBelowPredecessor
  intro worm
  exact natAccessible (worm.length + 1) worm (Nat.lt_succ_of_le (Nat.le_refl worm.length))

/-- The dropped worm precedes the original (a non-empty worm), the descending step of the worm operations. -/
theorem wormDrop_precedes (level : Nat) (rest : Worm) :
    wormPrecedes (wormDrop (level :: rest)) (level :: rest) :=
  wormDrop_length_lt level rest

/-- A worm with one extra leading diamond entails the worm with that diamond dropped to `⊤` then re-wrapped —
the basic monotone fact threading the worm head through the calculus: `<n>(rest) ⊢ <n>⊤`. -/
theorem wormCons_topMono (level : Nat) (rest : Worm) :
    RCProves (wormToFormula (level :: rest)) (RCFormula.diamond level RCFormula.top) :=
  wormToFormula_head_topMono level rest

/-! ## A non-vacuity witness for the checker -/

/-- The checker is non-vacuous: it certifies a genuine derivation — here the level drop `<1>p₀ ⊢ <0>p₀`.  The
`rcCheck` call evaluates to `true`, and `rcCheck_sound` turns that into an `RCProves` derivation. -/
theorem rcCheck_certifies_levelDrop :
    RCProves (RCFormula.diamond 1 (RCFormula.atom 0)) (RCFormula.diamond 0 (RCFormula.atom 0)) :=
  rcCheck_sound 1 (RCFormula.diamond 1 (RCFormula.atom 0)) (RCFormula.diamond 0 (RCFormula.atom 0)) rfl

/-- The checker also certifies same-level diamond monotonicity through a conjunction elimination:
`<0>(p₀ ∧ p₁) ⊢ <0>p₀` (it descends into the diamond, then eliminates the conjunction). -/
theorem rcCheck_certifies_diamondConjElim :
    RCProves (RCFormula.diamond 0 (RCFormula.and (RCFormula.atom 0) (RCFormula.atom 1)))
      (RCFormula.diamond 0 (RCFormula.atom 0)) :=
  rcCheck_sound 3 (RCFormula.diamond 0 (RCFormula.and (RCFormula.atom 0) (RCFormula.atom 1)))
    (RCFormula.diamond 0 (RCFormula.atom 0)) rfl

end FX1Poly.Tier0
