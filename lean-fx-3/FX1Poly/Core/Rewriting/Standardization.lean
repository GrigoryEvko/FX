import FX1Poly.Core.Rewriting.Confluence.Newman

/-! # FX1Poly/Core — standardization + finite developments (term-12)

Two classical reordering theorems of higher rewriting, in their abstract-rewriting form.

**Finite developments** (Church-Rosser's foundational lemma): mark a SET of redexes in a term; a *development*
contracts only their residuals.  The FD theorem says every development is FINITE.  Its abstract core is that
the development carries a strictly-decreasing measure — de Vrijer's exact development bound counts the marked
residuals remaining, and each marked contraction drops it — so the marked sub-reduction is strongly
normalizing.

**Standardization** (Curry-Feys; Klop): every reduction can be reordered into a *standard* one, contracting
redexes outside-in / left-to-right.  Its key lemma (Mitschke; Takahashi via parallel reduction; Hindley's
postponement) is **head/internal FACTORIZATION**: a reduction `→head ∪ →internal` can always be reordered so
all head steps come first — `(head ∪ internal)* ⊆ head* ∘ internal*` — provided internal reduction
*postpones* past head reduction.

This file ships the genuine abstract cores (each zero-axiom):

  * **`developmentsAreFinite`** — a relation with a strictly-decreasing `Nat` measure is strongly
    normalizing (every point is `Acc`-essible); the `Acc` is built by structural recursion on a bound
    (`accessibleBelowMeasure`), NOT `WellFounded.fix`.  This is the FD finiteness theorem: the development
    measure terminates the development.
  * **`factorizationOfStrongPostponement`** — under STRONG postponement (one internal step then one head step
    reorders to head steps followed by AT MOST ONE internal step), every `(head ∪ internal)*` reduction
    factors as `head* ∘ internal*` (`pushOneInternalPastHeads` is the strip lemma).  This is the head/internal
    factorization that standardization is built from.
  * concrete witnesses (`exampleFiniteDevelopment`, `exampleFactorization`).

## Honest scope

The FD finiteness theorem (via the measure) + the head/internal factorization (via strong postponement).
DEFERRED: the full FD package (de Vrijer's EXACT development-length formula + confluence of developments via
the residual / zig-zag theory); GENERAL postponement (internal steps producing arbitrarily many trailing
internals — the blow-up case, needing the commutation double-induction); and the FULL standardization theorem
(standard sequences ordered by the redex partial order, Klop's reordering, and the leftmost-reduction
normalization corollary).

## Zero-axiom verification

`accessibleBelowMeasure` is structural recursion on the bound (`induction bound`, `Acc.intro`, clean `Nat`
order lemmas); the strip lemma and factorization are inductions on `ReflTransClosure` with the
universal-in-conclusion motive and `subst`, no `Nat.add_comm`, no indexed-match wildcards.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCoreStandardization.lean`.
-/

namespace FX1Poly.Core

/-! ## Finite developments — the development measure terminates -/

/-- Accessibility from a strictly-decreasing `Nat` measure, bounded and built by structural recursion on the
bound (so no `WellFounded.fix`).  Every point whose measure is below the bound is `Acc`-essible. -/
theorem accessibleBelowMeasure {Carrier : Type} (rel : Carrier → Carrier → Prop)
    (measure : Carrier → Nat)
    (measureStrictlyDecreases : ∀ earlier later, rel earlier later → measure later < measure earlier) :
    ∀ (bound : Nat) (point : Carrier), measure point < bound →
      Acc (fun later earlier => rel earlier later) point := by
  intro bound
  induction bound with
  | zero => intro point measureBelowZero; exact absurd measureBelowZero (Nat.not_lt_zero _)
  | succ smallerBound inductionHypothesis =>
      intro point measureBelowBound
      exact Acc.intro point (fun successor stepFromPoint =>
        inductionHypothesis successor
          (Nat.lt_of_lt_of_le (measureStrictlyDecreases point successor stepFromPoint)
            (Nat.le_of_lt_succ measureBelowBound)))

/-- ★ **Finite developments** (abstract).  A rewrite relation equipped with a strictly-decreasing `Nat`
measure is strongly normalizing — every point is accessible, so there is no infinite reduction.  A
development contracts only marked residuals, and de Vrijer's development measure strictly drops at each
marked contraction; hence every development is FINITE. -/
theorem developmentsAreFinite {Carrier : Type} (markedStep : Carrier → Carrier → Prop)
    (developmentMeasure : Carrier → Nat)
    (measureStrictlyDecreases : ∀ earlier later, markedStep earlier later →
      developmentMeasure later < developmentMeasure earlier) (point : Carrier) :
    Acc (fun later earlier => markedStep earlier later) point :=
  accessibleBelowMeasure markedStep developmentMeasure measureStrictlyDecreases
    (developmentMeasure point + 1) point (Nat.lt_succ_self _)

/-! ## Standardization — head/internal factorization via strong postponement -/

/-- **The strip lemma for strong postponement**: push ONE internal step past a sequence of head steps.
Given `internalStep origin midpoint` and `head* midpoint headTarget`, there is a landing reached from
`origin` by head steps with AT MOST ONE trailing internal step to `headTarget`.  By induction on the head
chain (universal-in-conclusion motive on the incoming internal). -/
theorem pushOneInternalPastHeads {Carrier : Type}
    (headStep internalStep : Carrier → Carrier → Prop)
    (strongPostponement : ∀ before middle after, internalStep before middle → headStep middle after →
      ∃ landing, ReflTransClosure headStep before landing ∧ (internalStep landing after ∨ landing = after)) :
    ∀ {midpoint headTarget : Carrier}, ReflTransClosure headStep midpoint headTarget →
      ∀ {origin : Carrier}, internalStep origin midpoint →
        ∃ landing, ReflTransClosure headStep origin landing ∧
          (internalStep landing headTarget ∨ landing = headTarget) := by
  intro midpoint headTarget headChain
  induction headChain with
  | refl point =>
      intro origin internalFirst
      exact ⟨origin, ReflTransClosure.refl origin, Or.inl internalFirst⟩
  | head firstHead restHeads inductionHypothesis =>
      intro origin internalFirst
      obtain ⟨landing, headsOriginToLanding, postponed⟩ :=
        strongPostponement origin _ _ internalFirst firstHead
      cases postponed with
      | inl internalLandingToNext =>
          obtain ⟨finalLanding, headsLandingToFinal, tailInternal⟩ :=
            inductionHypothesis internalLandingToNext
          exact ⟨finalLanding, headsOriginToLanding.trans headsLandingToFinal, tailInternal⟩
      | inr landingEqNext =>
          subst landingEqNext
          exact ⟨_, headsOriginToLanding.trans restHeads, Or.inr rfl⟩

/-- ★ **Head/internal factorization** (the standardization core).  When the step relation splits as
`head ∪ internal` and internal reduction STRONGLY POSTPONES past head reduction, every reduction reorders so
that all head steps come first: `(head ∪ internal)* ⊆ head* ∘ internal*`.  This is the key lemma of
standardization — head reduction can always be performed first.  By induction on the mixed reduction, using
the strip lemma to push each internal step past the head prefix produced so far. -/
theorem factorizationOfStrongPostponement {Carrier : Type}
    (headStep internalStep : Carrier → Carrier → Prop)
    (strongPostponement : ∀ before middle after, internalStep before middle → headStep middle after →
      ∃ landing, ReflTransClosure headStep before landing ∧ (internalStep landing after ∨ landing = after)) :
    ∀ {source target : Carrier},
      ReflTransClosure (fun first second => headStep first second ∨ internalStep first second) source target →
      ∃ middle, ReflTransClosure headStep source middle ∧ ReflTransClosure internalStep middle target := by
  intro source target mixedChain
  induction mixedChain with
  | refl point => exact ⟨point, ReflTransClosure.refl point, ReflTransClosure.refl point⟩
  | head firstStep _restSteps inductionHypothesis =>
      obtain ⟨middle, headsToMiddle, internalsToTarget⟩ := inductionHypothesis
      cases firstStep with
      | inl headFirst =>
          exact ⟨middle, ReflTransClosure.head headFirst headsToMiddle, internalsToTarget⟩
      | inr internalFirst =>
          obtain ⟨landing, headsSourceToLanding, postponed⟩ :=
            pushOneInternalPastHeads headStep internalStep strongPostponement headsToMiddle internalFirst
          cases postponed with
          | inl internalLandingToMiddle =>
              exact ⟨landing, headsSourceToLanding,
                ReflTransClosure.head internalLandingToMiddle internalsToTarget⟩
          | inr landingEqMiddle =>
              subst landingEqMiddle
              exact ⟨landing, headsSourceToLanding, internalsToTarget⟩

/-! ## Concrete witnesses -/

/-- The decreasing-`Nat` development terminates: with the identity measure, every strict decrease is
accessible — a non-vacuous instance of finite developments. -/
theorem exampleFiniteDevelopment (start : Nat) :
    Acc (fun later earlier => later < earlier) start :=
  developmentsAreFinite (fun earlier later => later < earlier) (fun value => value)
    (fun _earlier _later strictlyLess => strictlyLess) start

/-- Factorization fires when head and internal are the SAME relation (strong postponement holds one-for-one):
every `step*` factors trivially, exercising both branches of the strip lemma. -/
theorem exampleFactorization {Carrier : Type} (step : Carrier → Carrier → Prop)
    {source target : Carrier}
    (reduction : ReflTransClosure (fun first second => step first second ∨ step first second) source target) :
    ∃ middle, ReflTransClosure step source middle ∧ ReflTransClosure step middle target :=
  factorizationOfStrongPostponement step step
    (fun _before middle _after internalFirst headSecond =>
      ⟨middle, ReflTransClosure.single internalFirst, Or.inl headSecond⟩) reduction

end FX1Poly.Core
