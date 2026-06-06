import FX1Poly.OmegacE.TranspositionSystem

/-! # FX1Poly/OmegacE/AbsorptionSystem
    — the first TWO-rule presentation with GENUINE inter-rule critical pairs

The idempotent system (`[c,c] → [c]`) and the transposition system (`[a,b] → [b,a]`) are each SINGLE-rule:
idempotent has a SELF-overlap critical pair (`[c,c,c]`), transposition is ORTHOGONAL (its one-cell overlap is
vacuous, forcing `a = b`).  This file opens the next complexity level — TWO DISTINCT rules whose left-hand
sides OVERLAP, producing genuine INTER-rule critical pairs that need a real multi-step join (a Newman
demonstration).

The system: a `survivingCell` absorbs an adjacent `vanishingCell` on either side.

* `absorptionRuleVanishingLeft  v s` — `[v, s] → [s, s]` (vanishingCell on the left).
* `absorptionRuleVanishingRight v s` — `[s, v] → [s, s]` (vanishingCell on the right).
* `absorptionSystem v s` — the TWO-rule system, membership a DISJUNCTION
  `· = absorptionRuleVanishingLeft v s ∨ · = absorptionRuleVanishingRight v s`.  This disjunction is the
  genuinely new content: every `fire` inversion must `rcases` on which rule fired (contrast the singleton
  systems, whose membership is a single `rfl`-equality).

Both rules are LENGTH-PRESERVING (`|lhs| = 2 = |rhs|`), like the transposition system; the system is NOT
length-reducing, so length is no termination measure.  Termination is by the count of `vanishingCell`s: each
rule eliminates exactly one (the survivingCell absorbs it), so `countOccurrences vanishingCell` strictly
decreases — a simpler measure than the transposition inversion count (no cross term), reusing the shipped
`countOccurrences` + `countOccurrences_append`.  Distinctness `v ≠ s` is REQUIRED: at `v = s` both rules are
self-loops `[v,v] → [v,v]`.

## Honest scope

This ships the SYSTEM + length invariants + non-vacuity + TERMINATION.  The two deferred subsequent atoms:

  1. LOCAL CONFLUENCE — the genuine inter-rule critical pairs.  The two LHS `[v,s]` and `[s,v]` overlap by one
     cell in two words: `[v,s,v]` (rule-Left at front, rule-Right at back) and `[s,v,s]` (rule-Right at front,
     rule-Left at back).  Both are REAL critical pairs (NOT vacuous, unlike transposition) and join via a
     two-step rewrite to `[s,s,s]` — `[v,s,v]`: Left@0 → `[s,s,v]` → Right@1 → `[s,s,s]`; Right@1 → `[v,s,s]`
     → Left@0 → `[s,s,s]`.  (`[s,v,s]`: both one-step reducts already join.)  Disjoint redexes commute as
     usual; the prefix-split trichotomy reuses `listPrefixSplit` from `IdempotentConfluence`, but the
     one-cell-overlap case here is the load-bearing join, not an `absurd`.
  2. BOUNDED-SEARCH DECIDABILITY — with `newman` (local confluence + the termination here) giving confluence,
     a two-rule `WordReducer` + `decidableConvertibleModulo_ofConvergent` decides the word problem.

This is the natural predecessor of the braid / symmetric sorting system (the full sorting / symmetric-group
convergent presentation, a rule FAMILY over an ordered alphabet).

## Zero-axiom verification

`fire` witnesses use `Or.inl/Or.inr rfl` membership; `isLengthPreserving` is `rcases` + two `rfl`s; the length
invariants instantiate the shipped preservation lemmas; the termination measure decrease is by induction on
the step (`fire` `rcases`-es the rule disjunction, both branches give `0 < 1`; context cases split by
`countOccurrences_append` and lift the inner IH by `Nat.add_lt_add_left/right`); `isTerminating` is the
`Subrelation` into `InvImage (· < ·) measure`, mirroring `transpositionSystem_isTerminating`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in
scratch before landing; the one trap — `rw [if_pos rfl]` leaving `1 + countOccurrences _ [] = 1` — is closed
by an explicit default-transparency `rfl`).  Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- absorption rule, vanishing cell on the LEFT: `[v, s] → [s, s]`. -/
def absorptionRuleVanishingLeft {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension) :
    OmegacERewriteRule dimension where
  leftHandSide := { cells := [vanishingCell, survivingCell] }
  rightHandSide := { cells := [survivingCell, survivingCell] }

/-- absorption rule, vanishing cell on the RIGHT: `[s, v] → [s, s]`. -/
def absorptionRuleVanishingRight {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension) :
    OmegacERewriteRule dimension where
  leftHandSide := { cells := [survivingCell, vanishingCell] }
  rightHandSide := { cells := [survivingCell, survivingCell] }

/-- The **two-rule absorption system**: a `survivingCell` absorbs an adjacent `vanishingCell` (either side).
Membership is a DISJUNCTION — the genuinely new structure forcing `rcases` in every `fire` inversion. -/
def absorptionSystem {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension) :
    OmegacERewriteRule dimension → Prop :=
  fun rule => rule = absorptionRuleVanishingLeft vanishingCell survivingCell
            ∨ rule = absorptionRuleVanishingRight vanishingCell survivingCell

/-- **Non-vacuity (left rule)**: the system genuinely rewrites `[v,s] → [s,s]` (`fire`, membership `Or.inl rfl`). -/
theorem absorptionRuleVanishingLeft_fires {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      { cells := [vanishingCell, survivingCell] } { cells := [survivingCell, survivingCell] } :=
  OmegacEWord.RewritesOneStep.fire (absorptionRuleVanishingLeft vanishingCell survivingCell) (Or.inl rfl)

/-- **Non-vacuity (right rule)**: the system genuinely rewrites `[s,v] → [s,s]` (`fire`, membership `Or.inr rfl`). -/
theorem absorptionRuleVanishingRight_fires {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      { cells := [survivingCell, vanishingCell] } { cells := [survivingCell, survivingCell] } :=
  OmegacEWord.RewritesOneStep.fire (absorptionRuleVanishingRight vanishingCell survivingCell) (Or.inr rfl)

/-- **The absorption system is length-preserving**: both rules have `|lhs| = 2 = |rhs|`.  `rcases` the
membership disjunction, then each branch is `rfl`. -/
theorem absorptionSystem_isLengthPreserving {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    IsLengthPreservingSystem (absorptionSystem vanishingCell survivingCell) := by
  intro rule isInSystem
  rcases isInSystem with hLeft | hRight
  · subst hLeft; rfl
  · subst hRight; rfl

/-- One-step rewriting preserves length (instantiating the shipped `RewritesOneStep.length_preserved`). -/
theorem absorptionSystem_rewritesOneStep_length_preserved {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  step.length_preserved (absorptionSystem_isLengthPreserving vanishingCell survivingCell)

/-- Many-step rewriting preserves length. -/
theorem absorptionSystem_rewritesMany_length_preserved {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany (absorptionSystem vanishingCell survivingCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  many.length_preserved (absorptionSystem_isLengthPreserving vanishingCell survivingCell)

/-- Convertibility preserves length — the convertibility class of `w` lies in the finite same-length word set. -/
theorem absorptionSystem_convertibleModulo_length_preserved {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (conv : OmegacEWord.ConvertibleModulo (absorptionSystem vanishingCell survivingCell)
      sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  conv.length_preserved (absorptionSystem_isLengthPreserving vanishingCell survivingCell)

/-- **A step strictly decreases the vanishingCell count** (requires `vanishingCell ≠ survivingCell`).  The
termination measure: each rule absorbs exactly one vanishingCell, so the count drops by one.  `fire` `rcases`-es
the rule disjunction — both `[v,s] ↦ [s,s]` and `[s,v] ↦ [s,s]` give `0 < 1`; context cases split by
`countOccurrences_append` and lift the inner IH.  Simpler than the transposition inversion measure (no cross term). -/
theorem vanishingCount_decreases_by_step {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (distinct : vanishingCell ≠ survivingCell)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      sourceWord targetWord) :
    countOccurrences vanishingCell targetWord.cells
      < countOccurrences vanishingCell sourceWord.cells := by
  have notSV : survivingCell = vanishingCell → False := fun h => distinct h.symm
  have targetZero : countOccurrences vanishingCell [survivingCell, survivingCell] = 0 := by
    show (if survivingCell = vanishingCell then 1 else 0)
       + countOccurrences vanishingCell [survivingCell] = 0
    rw [if_neg notSV, Nat.zero_add]
    show (if survivingCell = vanishingCell then 1 else 0)
       + countOccurrences vanishingCell [] = 0
    rw [if_neg notSV]
    rfl
  have cntS : countOccurrences vanishingCell [survivingCell] = 0 := by
    show (if survivingCell = vanishingCell then 1 else 0)
       + countOccurrences vanishingCell [] = 0
    rw [if_neg notSV]
    rfl
  induction step with
  | fire rule isInSystem =>
      rcases isInSystem with hLeft | hRight
      · subst hLeft
        show countOccurrences vanishingCell [survivingCell, survivingCell]
           < countOccurrences vanishingCell [vanishingCell, survivingCell]
        have sourceOne : countOccurrences vanishingCell [vanishingCell, survivingCell] = 1 := by
          show (if vanishingCell = vanishingCell then 1 else 0)
             + countOccurrences vanishingCell [survivingCell] = 1
          rw [if_pos rfl, cntS]
        rw [targetZero, sourceOne]
        exact Nat.zero_lt_one
      · subst hRight
        show countOccurrences vanishingCell [survivingCell, survivingCell]
           < countOccurrences vanishingCell [survivingCell, vanishingCell]
        have sourceOne : countOccurrences vanishingCell [survivingCell, vanishingCell] = 1 := by
          show (if survivingCell = vanishingCell then 1 else 0)
             + countOccurrences vanishingCell [vanishingCell] = 1
          rw [if_neg notSV, Nat.zero_add]
          show (if vanishingCell = vanishingCell then 1 else 0)
             + countOccurrences vanishingCell [] = 1
          rw [if_pos rfl]
          rfl
        rw [targetZero, sourceOne]
        exact Nat.zero_lt_one
  | underLeftContext prefixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countOccurrences_append, countOccurrences_append]
      exact Nat.add_lt_add_left innerIH _
  | underRightContext suffixWord inner innerIH =>
      dsimp only [OmegacEWord.append]
      rw [countOccurrences_append, countOccurrences_append]
      exact Nat.add_lt_add_right innerIH _

/-- **The absorption system is terminating** (requires `vanishingCell ≠ survivingCell`).  The vanishingCell
count embeds reduction into `<` on `ℕ` (pulled back along the measure), which is well-founded, so every word
is accessible.  The NON-LENGTH termination certificate for this two-rule length-preserving system, discharging
the `IsTerminating` premise of `newman` / `decidableConvertibleModulo_ofConvergent`. -/
theorem absorptionSystem_isTerminating {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (distinct : vanishingCell ≠ survivingCell) :
    IsTerminating (absorptionSystem vanishingCell survivingCell) := by
  intro word
  have subrel :
      Subrelation
        (fun reduct source =>
          OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell) source reduct)
        (InvImage (· < ·)
          (fun candidate => countOccurrences vanishingCell candidate.cells)) := by
    intro smaller larger hStep
    exact vanishingCount_decreases_by_step vanishingCell survivingCell distinct hStep
  exact subrel.accessible
    ((InvImage.wf (fun candidate => countOccurrences vanishingCell candidate.cells)
      Nat.lt_wfRel.wf).apply word)

end FX1Poly.OmegacE
