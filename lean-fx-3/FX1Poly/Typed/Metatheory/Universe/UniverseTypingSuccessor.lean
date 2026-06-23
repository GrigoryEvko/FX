import FX1Poly.Typed.Metatheory.Canonicity.Consistency.GrownUniverseConsistency

/-! # FX1Poly/Typed/Metatheory/Universe/UniverseTypingSuccessor
    — universe typing is the successor function (the acyclicity inversion kernel of the Girard / Type:Type
      obstruction, §27.2 / §1.4)

These three results were the genuinely load-bearing kernel content of the §27.3 Layer-1 known-unsoundness
corpus.  They are carved out here into the metatheory tree so the kernel proof
`UniverseClassificationAcyclic` (the "no Girard cycle of any length" theorem) depends on a kernel module
rather than on the audit-flavoured corpus catalog.  All three are proved SN-free from one grown inversion
(`inversionUniverseCode`) feeding cell injectivity (`universeCodeCell_inj_of_conv`), then the size-free
predicativity guards `LevelExpr.ne_lsucc_self` / `ne_lsuccLsucc_self`:

  * `grownUniverseTypingForcesSuccessor` — `Type@a : Type@b` in ANY context forces `b = a+1` and flag
    agreement.  The universe-typing relation is the successor FUNCTION, not merely irreflexive.  Consumed by
    `UniverseClassificationAcyclic` and re-exported through the corpus catalog.
  * `grownUniverseTypingHasNoTwoCycle` — no pair of universes classifies each other.
  * `corpusRejectsTypeInType` — the classic no-`Type:Type` (1-cycle), unconditional (no well-formedness).

Zero-axiom: no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Universe typing is the successor function.**  If a universe code `Type@(subjectLevel, subjectFlag)` is
grown-typed at a universe code `Type@(classifierLevel, classifierFlag)` in ANY context (no well-formedness
needed — this is a pure inversion), then `classifierLevel = subjectLevel + 1` and the flags agree.  The
grown inversion `inversionUniverseCode` forces every classifier `Conv`-equal to the strict predicative
successor `Type@(subjectLevel+1, subjectFlag)`; `universeCodeCell_inj_of_conv` collapses that `Conv` to the
level + flag equalities.  Every level-strictness rejection (self / inflation / deflation) is a corollary. -/
theorem grownUniverseTypingForcesSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag}
    (typed : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag)
        (universeCodeCell classifierLevel classifierFlag)) :
    classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag :=
  universeCodeCell_inj_of_conv (HasTypeDescPi.inversionUniverseCode typed)

/-- **No Girard 2-cycle in universe typing.**  There is no pair of universes each classified by the other:
`Type@a : Type@b` forces `b = a+1`, and `Type@b : Type@a` forces `a = b+1`, so `a = a+2`, refuted by the
double-successor predicativity guard `LevelExpr.ne_lsuccLsucc_self`.  The first genuinely-new acyclicity
obstruction beyond the shipped length-1 no-`Type:Type`.  (The FULL "no Girard cycle of any length" guarantee —
length-3 and beyond — is `grownUniverseTypingHasNoCycleOfAnyLength` in `UniverseClassificationAcyclic.lean`,
which generalizes this finite obstruction via the transitive closure + a strictly-increasing size measure;
that file's `grownUniverseTypingHasNoTwoCycleViaChain` re-derives this 2-cycle as its length-2 instance.) -/
theorem grownUniverseTypingHasNoTwoCycle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelA levelB : LevelExpr} {flagA flagB : UniverseFlag}
    (typedUp : HasTypeDescPi profile context (universeCodeCell levelA flagA)
        (universeCodeCell levelB flagB))
    (typedDown : HasTypeDescPi profile context (universeCodeCell levelB flagB)
        (universeCodeCell levelA flagA)) :
    False := by
  obtain ⟨levelBeqSuccA, _⟩ := grownUniverseTypingForcesSuccessor typedUp
  obtain ⟨levelAeqSuccB, _⟩ := grownUniverseTypingForcesSuccessor typedDown
  rw [levelBeqSuccA] at levelAeqSuccB
  exact LevelExpr.ne_lsuccLsucc_self levelA levelAeqSuccB

/-- **Corpus entry — no `Type : Type` (the classic Girard 1-cycle, §27.2 / §1.4).**  `Type@(level, flag)`
is never grown-classified by itself, in ANY context.  A one-line corollary of the functional
characterization: self-classification forces `level = level + 1`, refuted by `LevelExpr.ne_lsucc_self`.
Unlike the shipped `grownUniverseCode_notTypedAtSelf`, this carries no well-formedness decoration — the
rejection is unconditional. -/
theorem corpusRejectsTypeInType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (level : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell level flag)
        (universeCodeCell level flag) := by
  intro typed
  exact LevelExpr.ne_lsucc_self level (grownUniverseTypingForcesSuccessor typed).1

end FX1Poly.Typed
