import FX1Poly.OmegacE.Rewrite

/-! # FX1Poly/OmegacE/Confluence
    — confluence / Church-Rosser for word rewriting: the decidability enabler for the Makkai word problem

`Rewrite.lean` built directed rewriting (`RewritesOneStep`/`RewritesMany`) and the presented-monoid equality
(`ConvertibleModulo` = the reflexive-symmetric-transitive closure).  Convertibility is what the word problem
must decide, but as a symmetric-transitive closure it is not directly searchable.  Confluence collapses it to
JOINABILITY (`∃ a common reduct`), which a normalizer can decide.

This file is the confluence layer (the ωcE/Path-B twin of the term-layer `StepStarConfluence.lean`):

* `Joinable` — two words reduce to a common word; reflexive, symmetric, contains `RewritesMany`, embeds into
  `ConvertibleModulo` (`toConvertible`), and (under a length-preserving system) preserves length.
* `HasConfluence` — the diamond property: any two reducts of one source are joinable.
* `HasChurchRosser` — convertible words are joinable.
* `churchRosser_of_confluence` — the standard metatheorem: confluence ⟹ Church-Rosser (induction on the
  convertibility derivation; the `trans` case merges the two common reducts via confluence).
* `convertibleModulo_iff_joinable_of_churchRosser` — under Church-Rosser, convertibility IS joinability — the
  reduction that makes the word problem decidable once a normalizer exists.

## Honest scope

This is the confluence PROPERTY layer + its consequences.  It does NOT prove confluence for any concrete rule
system (that needs local confluence + termination via Newman's lemma, or critical-pair analysis — the next
Path-B atoms), nor decide the word problem (that additionally needs a terminating normalizer to make
`Joinable` checkable).  `HasConfluence`/`HasChurchRosser` are stated as properties exactly as the term layer
states `StepStar.HasConfluence` — discharged per concrete system later.

## Zero-axiom verification

Structural inductions over `ConvertibleModulo` + `RewritesMany.trans`/`.single`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Two words are **joinable** when they reduce to a common word.  Confluence's currency: the searchable
relation convertibility collapses to under Church-Rosser. -/
def OmegacEWord.Joinable {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop)
    (firstWord secondWord : OmegacEWord dimension) : Prop :=
  ∃ commonWord : OmegacEWord dimension,
    OmegacEWord.RewritesMany system firstWord commonWord ∧
      OmegacEWord.RewritesMany system secondWord commonWord

/-- Joinability is reflexive (a word joins itself at itself). -/
theorem OmegacEWord.Joinable.refl {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop} (word : OmegacEWord dimension) :
    OmegacEWord.Joinable system word word :=
  ⟨word, OmegacEWord.RewritesMany.refl word, OmegacEWord.RewritesMany.refl word⟩

/-- Joinability is symmetric. -/
theorem OmegacEWord.Joinable.symm {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {firstWord secondWord : OmegacEWord dimension}
    (joinable : OmegacEWord.Joinable system firstWord secondWord) :
    OmegacEWord.Joinable system secondWord firstWord :=
  Exists.elim joinable (fun commonWord reaches => ⟨commonWord, reaches.2, reaches.1⟩)

/-- A many-step reduction makes its endpoints joinable (join at the target). -/
theorem OmegacEWord.Joinable.ofRewritesMany {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany system sourceWord targetWord) :
    OmegacEWord.Joinable system sourceWord targetWord :=
  ⟨targetWord, many, OmegacEWord.RewritesMany.refl targetWord⟩

/-- Joinable words are convertible (`firstWord →* common ←* secondWord`, glued by `symm`/`trans`). -/
theorem OmegacEWord.Joinable.toConvertible {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {firstWord secondWord : OmegacEWord dimension}
    (joinable : OmegacEWord.Joinable system firstWord secondWord) :
    OmegacEWord.ConvertibleModulo system firstWord secondWord := by
  obtain ⟨commonWord, firstReaches, secondReaches⟩ := joinable
  exact OmegacEWord.ConvertibleModulo.trans
    (OmegacEWord.ConvertibleModulo.ofRewritesMany firstReaches)
    (OmegacEWord.ConvertibleModulo.symm (OmegacEWord.ConvertibleModulo.ofRewritesMany secondReaches))

/-- Joinable words have equal length under a length-preserving system (both reduce to the common word,
each preserving length). -/
theorem OmegacEWord.Joinable.length_preserved {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthPreserving : IsLengthPreservingSystem system)
    {firstWord secondWord : OmegacEWord dimension}
    (joinable : OmegacEWord.Joinable system firstWord secondWord) :
    firstWord.length = secondWord.length := by
  obtain ⟨commonWord, firstReaches, secondReaches⟩ := joinable
  exact (firstReaches.length_preserved lengthPreserving).trans
    (secondReaches.length_preserved lengthPreserving).symm

/-- **The confluence (diamond) property**: any two reducts of a common source are joinable. -/
def HasConfluence {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ {sourceWord firstReduct secondReduct : OmegacEWord dimension},
    OmegacEWord.RewritesMany system sourceWord firstReduct →
    OmegacEWord.RewritesMany system sourceWord secondReduct →
    OmegacEWord.Joinable system firstReduct secondReduct

/-- **The Church-Rosser property**: convertible words are joinable. -/
def HasChurchRosser {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ {firstWord secondWord : OmegacEWord dimension},
    OmegacEWord.ConvertibleModulo system firstWord secondWord →
    OmegacEWord.Joinable system firstWord secondWord

/-- **Confluence implies Church-Rosser** — the standard metatheorem.  By induction on the convertibility
derivation: `ofStep`/`refl`/`symm` are direct; the `trans` case merges the two inductively-obtained common
reducts (`leftCommon` for `first~middle`, `rightCommon` for `middle~last`) by applying confluence to the two
reductions OUT OF `middle`, then chaining with `RewritesMany.trans`. -/
theorem churchRosser_of_confluence {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (confluence : HasConfluence system) :
    HasChurchRosser system := by
  intro firstWord secondWord converts
  induction converts with
  | ofStep step => exact OmegacEWord.Joinable.ofRewritesMany (OmegacEWord.RewritesMany.single step)
  | refl word => exact OmegacEWord.Joinable.refl word
  | symm _converts convertsIH => exact convertsIH.symm
  | trans _firstToMiddle _middleToLast firstIH middleIH =>
      obtain ⟨leftCommon, firstReachesLeft, middleReachesLeft⟩ := firstIH
      obtain ⟨rightCommon, middleReachesRight, lastReachesRight⟩ := middleIH
      obtain ⟨mergedCommon, leftReachesMerged, rightReachesMerged⟩ :=
        confluence middleReachesLeft middleReachesRight
      exact ⟨mergedCommon,
        firstReachesLeft.trans leftReachesMerged,
        lastReachesRight.trans rightReachesMerged⟩

/-- **Under Church-Rosser, convertibility is exactly joinability.**  The decidability enabler: the symmetric-
transitive closure (`ConvertibleModulo`) reduces to `∃ a common reduct` (`Joinable`), which a terminating
normalizer can decide (normalize both, compare). -/
theorem convertibleModulo_iff_joinable_of_churchRosser {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (churchRosser : HasChurchRosser system)
    {firstWord secondWord : OmegacEWord dimension} :
    OmegacEWord.ConvertibleModulo system firstWord secondWord ↔
      OmegacEWord.Joinable system firstWord secondWord :=
  ⟨fun converts => churchRosser converts, fun joinable => joinable.toConvertible⟩

/-! ## Newman's lemma — confluence from the checkable local confluence

`HasConfluence` quantifies over arbitrary many-step reductions, so it is not directly checkable.  Newman's
lemma reduces it to LOCAL confluence (the peak of two SINGLE steps is joinable — checkable by critical-pair
analysis) plus TERMINATION (well-foundedness of the reduction relation).  This is THE tool for discharging
`HasConfluence` on a concrete system. -/

/-- **Local confluence**: the peak of two single rewrite steps out of one word is joinable.  Checkable in
practice (finitely many critical pairs); Newman lifts it to global confluence under termination. -/
def HasLocalConfluence {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ {sourceWord firstReduct secondReduct : OmegacEWord dimension},
    OmegacEWord.RewritesOneStep system sourceWord firstReduct →
    OmegacEWord.RewritesOneStep system sourceWord secondReduct →
    OmegacEWord.Joinable system firstReduct secondReduct

/-- **Termination**: every word is accessible under the reduction relation — there are no infinite reduction
sequences (the well-founded measure a concrete system supplies, e.g. strictly decreasing length). -/
def IsTerminating {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ word : OmegacEWord dimension,
    Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) word

/-- The well-founded core of Newman's lemma: from local confluence, confluence holds at every ACCESSIBLE word.
By Acc-recursion on the source — if either reduction is `refl` the joinability is immediate; otherwise the two
first steps' peak is joined by local confluence, and the two inductive hypotheses (at the two strictly-smaller
one-step reducts) tile the result together. -/
theorem confluenceFromAccessible {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (localConfluence : HasLocalConfluence system) :
    ∀ {sourceWord : OmegacEWord dimension},
      Acc (fun reduct source => OmegacEWord.RewritesOneStep system source reduct) sourceWord →
      ∀ {firstReduct secondReduct : OmegacEWord dimension},
        OmegacEWord.RewritesMany system sourceWord firstReduct →
        OmegacEWord.RewritesMany system sourceWord secondReduct →
        OmegacEWord.Joinable system firstReduct secondReduct := by
  intro sourceWord accessible
  induction accessible with
  | intro currentSource _accStep innerIH =>
    intro firstReduct secondReduct sourceToFirst sourceToSecond
    cases sourceToFirst with
    | refl _ => exact OmegacEWord.Joinable.ofRewritesMany sourceToSecond
    | step firstHead firstTail =>
      cases sourceToSecond with
      | refl _ =>
        exact (OmegacEWord.Joinable.ofRewritesMany
          (OmegacEWord.RewritesMany.step firstHead firstTail)).symm
      | step secondHead secondTail =>
        obtain ⟨peakMerge, firstMidToMerge, secondMidToMerge⟩ :=
          localConfluence firstHead secondHead
        obtain ⟨firstFinal, firstToFirstFinal, mergeToFirstFinal⟩ :=
          innerIH _ firstHead firstTail firstMidToMerge
        obtain ⟨secondFinal, secondToSecondFinal, firstFinalToSecondFinal⟩ :=
          innerIH _ secondHead secondTail (secondMidToMerge.trans mergeToFirstFinal)
        exact ⟨secondFinal, firstToFirstFinal.trans firstFinalToSecondFinal, secondToSecondFinal⟩

/-- **Newman's lemma for word rewriting**: a terminating, locally-confluent system is confluent.  Combined
with `churchRosser_of_confluence` + `WordProblem`'s decision, a terminating system with checkable local
confluence has a decidable word problem. -/
theorem newman {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (localConfluence : HasLocalConfluence system) (terminating : IsTerminating system) :
    HasConfluence system := by
  intro sourceWord firstReduct secondReduct sourceToFirst sourceToSecond
  exact confluenceFromAccessible localConfluence (terminating sourceWord) sourceToFirst sourceToSecond

/-! ## Termination from a length measure

`IsTerminating` (well-foundedness of reduction) is abstract; this discharges it from a CHECKABLE condition —
every rule strictly decreasing length — the simplest termination certificate a concrete system supplies. -/

/-- A rule system is length-reducing when every rule's right-hand side is strictly shorter than its left. -/
def IsLengthReducingSystem {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ rule : OmegacERewriteRule dimension, system rule →
    rule.rightHandSide.length < rule.leftHandSide.length

/-- A one-step rewrite under a length-reducing system strictly decreases length (the strict analogue of
`RewritesOneStep.length_preserved`): `fire` is the rule hypothesis, the context cases add `length_append` to
the inner strict inequality. -/
theorem OmegacEWord.RewritesOneStep.length_lt_of_lengthReducing {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthReducing : IsLengthReducingSystem system)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
    targetWord.length < sourceWord.length := by
  induction step with
  | fire rule isInSystem => exact lengthReducing rule isInSystem
  | underLeftContext prefixWord _inner innerIH =>
      rw [OmegacEWord.length_append, OmegacEWord.length_append]
      exact Nat.add_lt_add_left innerIH prefixWord.length
  | underRightContext suffixWord _inner innerIH =>
      rw [OmegacEWord.length_append, OmegacEWord.length_append]
      exact Nat.add_lt_add_right innerIH suffixWord.length

/-- **A length-reducing system is terminating.**  Reduction embeds (by strictly decreasing length) into `<` on
`ℕ` pulled back along `length`, which is well-founded — so every word is accessible.  Discharges the
`IsTerminating` hypothesis of the convergent-presentation decision (`decidableConvertibleModulo_ofConvergent`)
from a checkable length measure; combined with `newman` it leaves only local confluence + a reducer to supply
for a concrete length-reducing system. -/
theorem IsTerminating_of_lengthReducing {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthReducing : IsLengthReducingSystem system) :
    IsTerminating system := by
  intro word
  have subrel :
      Subrelation (fun reduct source => OmegacEWord.RewritesOneStep system source reduct)
        (InvImage (· < ·) (OmegacEWord.length (dimension := dimension))) := by
    intro smaller larger hStep
    exact OmegacEWord.RewritesOneStep.length_lt_of_lengthReducing lengthReducing hStep
  exact subrel.accessible
    ((InvImage.wf (OmegacEWord.length (dimension := dimension)) Nat.lt_wfRel.wf).apply word)

end FX1Poly.OmegacE
