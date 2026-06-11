import FX1Poly.Typed.HasTypeNativeUnionInversion

/-! # FX1Poly/Typed/HasTypeNativeUnionTwoPathVerdict — NATIVE-37 part d: THE TWO-PATH EQUIVALENCE
    (closing fold 35's canonical-path decision for natSucc).

`natSucc` is union-typable via BOTH paths the seed/batch arms provide:

  * the EMBEDDING arm `ofNatIntro` (a standalone `HasTypeDescNatIntro` derivation whose subject is a
    `natSucc`), and
  * the recursive table ROW arm `recursiveUnaryIntro` at the `gen_natSucc` row (whose child premise is
    union-recursive at `Nat`).

`invertAtNatSuccHead` (shipped) surfaces exactly these two survivors.  This file decides which path is
canonical by proving the two are NOT interchangeable:

  1. **Embedding ⟹ row (trivial subsumption).**  A bespoke `HasTypeDescNatIntro` typing of `natSucc(c)`
     pins its predecessor `c` as itself NatIntro-typed at `Nat`; embedding that through `ofNatIntro`
     yields the ROW survivor's premise shape `HasTypeNativeUnion … c natTypeCell`.  So every embedding
     witness is reproducible on the row path.

  2. **Row ⟹ embedding is REFUTED (strict generality).**  A union-typed child at `natTypeCell` need NOT
     be a bespoke NatIntro derivation: a `natElim`-headed COMPUTED number is union-typed at `Nat` (the
     batch-1 nested witness, exhibited here through the `recursiveElim` arm) yet is NOT NatIntro-typed.
     For that child, the EMBEDDING path is DEAD — `HasTypeDescNatIntro … (natSucc(natElim …)) Nat` is
     FALSE (the bespoke `natSuccIntro` demands a NatIntro predecessor, and a `natElim`-head clashes with
     every NatIntro constructor head) — while the ROW path TYPES it.

VERDICT: the ROW path (`recursiveUnaryIntro`) is STRICTLY MORE GENERAL; the embedding is subsumed.  This
is the canonical-path decision feeding NATIVE-42's `ofNatIntro` delete-readiness — the embedding arm is
redundant for derivability of natSucc subjects, and the row's recursive premise is the one that admits the
computed-number tower.

## Zero-axiom

The bespoke natSucc predecessor inversion is a free-index single-arm `cases` with head no-confusion; the
subsumption is `ofNatIntro` of the recovered premise; the refutation is a free-index `cases` on the
bespoke engine with `subjectIsNatConstructor` head clashes.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeUnionReverseAdequacy.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## The bespoke natSucc predecessor inversion (the intro-head inversion deliverable 3 needs) -/

/-- **★ Inversion of a bespoke `natSucc` typing.**  A `HasTypeDescNatIntro` typing whose subject is
`natSucc(child)` pins the classifier to `Nat` and recovers the RECURSIVE predecessor premise: the child
is itself NatIntro-typed at `Nat`.  Free-index `cases` on the two-arm Nat-intro engine: the `natZero` arm
is refuted by head clash (`natZero` ≠ `natSucc`); the `natSucc` arm injects to recover the predecessor and
its typing. -/
theorem HasTypeDescNatIntro.invertNatSucc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier child : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier)
    (subjectShape : subject = natSuccCell child) :
    classifier = natTypeCell ∧ HasTypeDescNatIntro profile context child natTypeCell := by
  cases derivation with
  | natZeroIntro =>
      exact absurd (subjectShape.symm) (by intro headEq; cases headEq)
  | natSuccIntro predecessor predecessorTyped =>
      rcases subjectShape with ⟨⟩
      exact ⟨rfl, predecessorTyped⟩

/-! ## (1) Embedding ⟹ row: the trivial subsumption -/

/-- **★ Embedding ⟹ row.**  A bespoke `HasTypeDescNatIntro` typing of `natSucc(child)` reproduces the ROW
survivor's premise shape: the classifier is `Nat` and the child is union-typed at `Nat` (through
`ofNatIntro` of the recovered predecessor premise).  Every embedding witness lands on the row path — the
embedding is subsumed BY the row for derivability. -/
theorem HasTypeNativeUnion.natSuccEmbeddingSubsumedByRow {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier child : RawTerm scope}
    (embeddingTyped : HasTypeDescNatIntro profile context (natSuccCell child) classifier) :
    classifier = natTypeCell ∧ HasTypeNativeUnion profile context child natTypeCell := by
  obtain ⟨classifierEq, childIntro⟩ := embeddingTyped.invertNatSucc rfl
  exact ⟨classifierEq, HasTypeNativeUnion.ofNatIntro childIntro⟩

/-! ## The computed-number child: a union-typed `natElim`-headed term at `Nat` -/

/-- **★ A computed number types at `Nat` in the union through the recursive-eliminator arm.**
`natElim(motive, natZero, stepBranch, natZero) : Nat` — a `natElim`-HEADED term union-typed at `natTypeCell`
(scrutinee `natZero : Nat` via `ofNatIntro`, base branch `natZero : Nat` via `ofNatIntro`).  This is the
batch-1 nested witness: a union member at `Nat` whose HEAD is an eliminator, NOT a Nat constructor — so it
is NOT bespoke-NatIntro-typable, the exact surplus the row's recursive premise admits. -/
theorem HasTypeNativeUnion.computedNumberTypedAtNat {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (motive : RawTerm (scope + 1))
    (stepBranch : RawTerm (scope + 2))
    (stepBranchTyped : HasTypeNativeUnion profile
      ((context.cons natTypeCell).cons
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken natTypeCell))
      stepBranch
      (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken natTypeCell))) :
    HasTypeNativeUnion profile context
      (natElimCell motive natZeroCell stepBranch natZeroCell) natTypeCell :=
  HasTypeNativeUnion.recursiveElim context .gen_natElim natElimNativeRecursiveRule
    motive natZeroCell stepBranch natZeroCell natTypeCell rfl
    (HasTypeNativeUnion.ofNatIntro (HasTypeDescNatIntro.natZeroIntro context))
    (HasTypeNativeUnion.ofNatIntro (HasTypeDescNatIntro.natZeroIntro context))
    stepBranchTyped

/-! ## (2) Row ⟹ embedding is REFUTED: strict generality -/

/-- **★ The embedding path is DEAD on a `natElim`-headed child.**  The bespoke `HasTypeDescNatIntro` CANNOT
type `natSucc(natElim(…))` at any classifier: the `natSucc` predecessor inversion would force the
`natElim`-headed child to be NatIntro-typed, but every NatIntro-typed subject is `natZero` or `natSucc`
(by `subjectIsNatConstructor`), and `natElim` clashes with both heads.  So while the ROW path types
`natSucc` of this computed-number child, the EMBEDDING path does not — the row is strictly more
general. -/
theorem HasTypeDescNatIntro.natSuccOfComputedNumberHasNoEmbedding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {stepBranch : RawTerm (scope + 2)}
    (embeddingTyped : HasTypeDescNatIntro profile context
      (natSuccCell (natElimCell motive natZeroCell stepBranch natZeroCell)) classifier) :
    False := by
  obtain ⟨_, childIntro⟩ := embeddingTyped.invertNatSucc rfl
  rcases childIntro.subjectIsNatConstructor with isZero | ⟨_, isSucc⟩
  · exact absurd isZero.symm (by intro headEq; cases headEq)
  · exact absurd isSucc.symm (by intro headEq; cases headEq)

/-! ## ★ The two-path verdict, packaged -/

/-- **★ The two-path canonical decision (natSucc).**  For the computed-number child
`natElim(motive, natZero, stepBranch, natZero)`:

  * the ROW path TYPES `natSucc(child) : Nat` (through `recursiveUnaryIntro` over the union-typed child),
  * the EMBEDDING path is DEAD (`HasTypeDescNatIntro … (natSucc(child)) classifier → False` for every
    classifier).

So the ROW path is STRICTLY MORE GENERAL than the embedding; the embedding is subsumed (by
`natSuccEmbeddingSubsumedByRow`) but does not subsume.  VERDICT: the row is the canonical natSucc path —
the `ofNatIntro` embedding is redundant for derivability and is delete-ready (NATIVE-42). -/
theorem HasTypeNativeUnion.natSuccRowStrictlyMoreGeneralThanEmbedding {profile : PolyProfile}
    {scope : Nat} (context : TypingContext profile scope) (motive : RawTerm (scope + 1))
    (stepBranch : RawTerm (scope + 2))
    (stepBranchTyped : HasTypeNativeUnion profile
      ((context.cons natTypeCell).cons
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken natTypeCell))
      stepBranch
      (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken natTypeCell))) :
    HasTypeNativeUnion profile context
      (natSuccCell (natElimCell motive natZeroCell stepBranch natZeroCell)) natTypeCell ∧
    (∀ classifier : RawTerm scope,
      ¬ HasTypeDescNatIntro profile context
          (natSuccCell (natElimCell motive natZeroCell stepBranch natZeroCell)) classifier) := by
  refine ⟨?_, ?_⟩
  · exact HasTypeNativeUnion.recursiveUnaryIntro context .gen_natSucc
      natSuccNativeRecursiveUnaryRule (natElimCell motive natZeroCell stepBranch natZeroCell) rfl
      (HasTypeNativeUnion.computedNumberTypedAtNat context motive stepBranch stepBranchTyped)
  · intro classifier embeddingTyped
    exact embeddingTyped.natSuccOfComputedNumberHasNoEmbedding

end FX1Poly.Typed
