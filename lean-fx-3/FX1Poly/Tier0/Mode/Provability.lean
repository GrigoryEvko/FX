/-! # mode-23 — provability logic GL + polymodal GLP

The provability modality `□` ("it is provable that") as a mode instance, via Kripke frame semantics.  GL
(Gödel-Löb) is the modal logic of provability; its characteristic LÖB axiom `□(□φ → φ) → □φ` (the modal form of
Löb's theorem) is VALID exactly on TRANSITIVE + CONVERSE-WELL-FOUNDED frames.  This rung mechanizes that validity —
the semantic soundness of GL — and the polymodal `[n]` family of Japaridze's GLP (the setting of Beklemishev's
ordinal analysis).

A frame is `(World, accessible)`.  A semantic proposition is a forcing `World → Prop`; `□φ` holds at a world iff
`φ` holds at every accessible successor.

## What this file ships (each piece zero-axiom)

  * `boxOver` / `diamondOver` — the `□` / `◇` modalities over an accessibility relation; `IsTransitiveFrame` and
    `ConverseWellFounded` (the GL frame conditions, the latter via `Acc` of the converse relation).
  * the normal-modal-logic core (valid on ANY frame): ★ `boxOver_distrib` (the K axiom `□(φ→ψ) → □φ → □ψ`),
    `boxOver_necessitation`, `boxOver_monotone`, `diamondOver_not_boxOver_not` (the intuitionistic `◇`/`□` De Morgan).
  * ★ `boxOver_four` — the 4 axiom `□φ → □□φ`, valid on TRANSITIVE frames.
  * ★★ `boxOver_loeb` — the **Löb axiom** `□(□φ → φ) → □φ`, valid on transitive + converse-well-founded frames,
    proved by well-founded induction along the converse accessibility (the semantic heart of GL).
  * the polymodal `[n]` family: `boxAt` + ★ `boxAt_monotone_level` (the GLP axiom `[n]φ → [n+1]φ`, from the nested
    frame condition `R_{n+1} ⊆ R_n`) + `boxAt_loeb` (each level is itself a GL box).

## What is DEFERRED (markers)

  * the GLP ordinal analysis — Beklemishev's reduction, the reflection calculus RC / worms, ordinal notations up to
    `Γ₀` (`hasGlpOrdinalAnalysis`);
  * arithmetical completeness — Solovay's theorem that GL is EXACTLY the provability logic of PA (the bridge to a
    metamathematical provability predicate) (`hasArithmeticalCompleteness`);
  * Kripke COMPLETENESS — GL is complete w.r.t. finite transitive irreflexive trees (here only soundness/validity is
    shipped) (`hasKripkeCompleteness`);
  * the strictly-positive reflection calculus RC + its polytime decidability (Dashkov-Beklemishev)
    (`hasReflectionCalculus`);
  * the provability box fibred into the kernel doctrine (the trust / `axiom`-graded modality, cross-axis, `fib`)
    (`hasKernelProvabilityFibration`).

Zero external dependencies; raw Lean 4 + Init only (`Acc` from the prelude).
-/

namespace FX1Poly.Tier0

/-! ## Frames and the modalities -/

/-- The `□` modality over an accessibility relation: `□φ` holds at a world iff `φ` holds at every successor. -/
def boxOver {World : Type} (accessible : World → World → Prop) (proposition : World → Prop) : World → Prop :=
  fun world => ∀ successor, accessible world successor → proposition successor

/-- The `◇` modality: `◇φ` holds at a world iff `φ` holds at some successor. -/
def diamondOver {World : Type} (accessible : World → World → Prop) (proposition : World → Prop) : World → Prop :=
  fun world => ∃ successor, accessible world successor ∧ proposition successor

/-- A frame is transitive. -/
def IsTransitiveFrame {World : Type} (accessible : World → World → Prop) : Prop :=
  ∀ first second third, accessible first second → accessible second third → accessible first third

/-- A frame is converse-well-founded: there is no infinite forward chain `w₀ R w₁ R w₂ …` (the GL frame condition).
Encoded as accessibility of every world under the CONVERSE relation. -/
def ConverseWellFounded {World : Type} (accessible : World → World → Prop) : Prop :=
  ∀ world, Acc (fun laterWorld earlierWorld => accessible earlierWorld laterWorld) world

/-! ## The normal modal core (valid on any frame) -/

/-- ★ The **K axiom** `□(φ → ψ) → □φ → □ψ` — the box distributes over implication (any frame). -/
theorem boxOver_distrib {World : Type} (accessible : World → World → Prop)
    (premiseProp conclusionProp : World → Prop) (world : World) :
    boxOver accessible (fun inner => premiseProp inner → conclusionProp inner) world →
      boxOver accessible premiseProp world → boxOver accessible conclusionProp world :=
  fun boxedImplication boxedPremise successor accessibleSuccessor =>
    boxedImplication successor accessibleSuccessor (boxedPremise successor accessibleSuccessor)

/-- Necessitation: a proposition true everywhere is boxed at every world. -/
theorem boxOver_necessitation {World : Type} (accessible : World → World → Prop)
    (proposition : World → Prop) (world : World) :
    (∀ everyWorld, proposition everyWorld) → boxOver accessible proposition world :=
  fun trueEverywhere successor _ => trueEverywhere successor

/-- The box is monotone in its proposition. -/
theorem boxOver_monotone {World : Type} (accessible : World → World → Prop)
    (weakerProp strongerProp : World → Prop) (world : World) :
    (∀ everyWorld, weakerProp everyWorld → strongerProp everyWorld) →
      boxOver accessible weakerProp world → boxOver accessible strongerProp world :=
  fun pointwiseImplication boxedWeaker successor accessibleSuccessor =>
    pointwiseImplication successor (boxedWeaker successor accessibleSuccessor)

/-- The intuitionistic `◇`/`□` De Morgan: `◇φ → ¬□¬φ`. -/
theorem diamondOver_not_boxOver_not {World : Type} (accessible : World → World → Prop)
    (proposition : World → Prop) (world : World) :
    diamondOver accessible proposition world →
      ¬ boxOver accessible (fun inner => ¬ proposition inner) world :=
  fun witnessedDiamond boxedNegation =>
    match witnessedDiamond with
    | ⟨successor, accessibleSuccessor, holdsAtSuccessor⟩ =>
        boxedNegation successor accessibleSuccessor holdsAtSuccessor

/-! ## The 4 axiom (transitive frames) -/

/-- ★ The **4 axiom** `□φ → □□φ`, valid on transitive frames. -/
theorem boxOver_four {World : Type} (accessible : World → World → Prop)
    (isTransitive : IsTransitiveFrame accessible) (proposition : World → Prop) (world : World) :
    boxOver accessible proposition world → boxOver accessible (boxOver accessible proposition) world :=
  fun boxedProposition middleWorld accessibleToMiddle finalWorld accessibleMiddleFinal =>
    boxedProposition finalWorld (isTransitive world middleWorld finalWorld accessibleToMiddle accessibleMiddleFinal)

/-! ## The Löb axiom (the semantic heart of GL) -/

/-- ★★ The **Löb axiom** `□(□φ → φ) → □φ`, valid on transitive + converse-well-founded frames.  Proved by
well-founded induction along the converse accessibility: at each reachable world, the inductive hypothesis supplies
`□φ` (from transitivity gathering the forward successors), the premise turns `□φ → φ` into `φ`. -/
theorem boxOver_loeb {World : Type} (accessible : World → World → Prop)
    (isTransitive : IsTransitiveFrame accessible)
    (isConverseWellFounded : ConverseWellFounded accessible)
    (proposition : World → Prop) (world : World)
    (premise : boxOver accessible
      (fun inner => boxOver accessible proposition inner → proposition inner) world) :
    boxOver accessible proposition world := by
  intro candidate accessibleToCandidate
  suffices auxiliary : ∀ reachable,
      Acc (fun laterWorld earlierWorld => accessible earlierWorld laterWorld) reachable →
      accessible world reachable → proposition reachable by
    exact auxiliary candidate (isConverseWellFounded candidate) accessibleToCandidate
  intro reachable reachableAccessible
  induction reachableAccessible with
  | intro currentWorld _ inductiveHypothesis =>
    intro accessibleToCurrent
    have implicationAtCurrent := premise currentWorld accessibleToCurrent
    apply implicationAtCurrent
    intro furtherWorld accessibleCurrentFurther
    exact inductiveHypothesis furtherWorld accessibleCurrentFurther
      (isTransitive world currentWorld furtherWorld accessibleToCurrent accessibleCurrentFurther)

/-! ## The polymodal `[n]` family (GLP) -/

/-- The level-indexed `[n]` modality (Japaridze's GLP): the box over the level-`n` accessibility relation. -/
def boxAt {World : Type} (accessibleAt : Nat → World → World → Prop) (level : Nat)
    (proposition : World → Prop) : World → Prop :=
  fun world => ∀ successor, accessibleAt level world successor → proposition successor

/-- ★ The GLP axiom `[n]φ → [n+1]φ` — provability gets stronger with the level, from the nested frame condition
`R_{n+1} ⊆ R_n` (the higher level sees fewer successors, so its box demands less). -/
theorem boxAt_monotone_level {World : Type} (accessibleAt : Nat → World → World → Prop)
    (isNested : ∀ level world successor,
      accessibleAt (level + 1) world successor → accessibleAt level world successor)
    (level : Nat) (proposition : World → Prop) (world : World) :
    boxAt accessibleAt level proposition world → boxAt accessibleAt (level + 1) proposition world :=
  fun boxedLower successor accessibleHigher =>
    boxedLower successor (isNested level world successor accessibleHigher)

/-- Each GLP level is itself a GL box: the Löb axiom holds at every level (transitive + converse-well-founded). -/
theorem boxAt_loeb {World : Type} (accessibleAt : Nat → World → World → Prop) (level : Nat)
    (isTransitive : IsTransitiveFrame (accessibleAt level))
    (isConverseWellFounded : ConverseWellFounded (accessibleAt level))
    (proposition : World → Prop) (world : World)
    (premise : boxAt accessibleAt level
      (fun inner => boxAt accessibleAt level proposition inner → proposition inner) world) :
    boxAt accessibleAt level proposition world :=
  boxOver_loeb (accessibleAt level) isTransitive isConverseWellFounded proposition world premise

/-! ## Honesty markers -/

/-- **Honesty marker.**  The GLP ordinal analysis — Beklemishev's reduction, the reflection calculus RC / worms,
ordinal notations up to `Γ₀` — is deferred.  `= false`. -/
def fxMode_hasGlpOrdinalAnalysis : Bool := false

/-- **Honesty marker.**  Arithmetical completeness — Solovay's theorem that GL is EXACTLY the provability logic of
PA (the bridge to a metamathematical provability predicate) — is deferred.  `= false`. -/
def fxMode_hasArithmeticalCompleteness : Bool := false

/-- **Honesty marker.**  Kripke COMPLETENESS — GL is complete w.r.t. finite transitive irreflexive trees (here only
soundness / validity is shipped) — is deferred.  `= false`. -/
def fxMode_hasKripkeCompleteness : Bool := false

/-- **Honesty marker.**  The strictly-positive reflection calculus RC + its polytime decidability
(Dashkov-Beklemishev) is deferred.  `= false`. -/
def fxMode_hasReflectionCalculus : Bool := false

/-- **Honesty marker.**  The provability box fibred into the kernel doctrine (the trust / `axiom`-graded modality,
cross-axis, `fib`) is deferred.  `= false`. -/
def fxMode_hasKernelProvabilityFibration : Bool := false

end FX1Poly.Tier0
