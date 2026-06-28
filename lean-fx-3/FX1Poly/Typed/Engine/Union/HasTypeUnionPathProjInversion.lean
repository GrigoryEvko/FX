import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion
import FX1Poly.Typed.Cell.IdJDependentMotiveType
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/HasTypeUnionPathProjInversion — NATIVE-37 part d: per-head inversions for the
    path-induction head (idJ) and the projection heads (fst / snd).

Two more eliminator shapes from the inversion substrate of `HasTypeUnionInversion`:

  * **idJ** — the survivor is the unified `elim` arm pinned to the `gen_idJ` row (the TYTAB-1 elim-collapse
    arm).  Surfaced premises: the witness union-typed at a reflexive identity code
    `Id(typeCode, endpoint, endpoint)`, the base case union-typed at the result classifier.
  * **fst / snd** — the survivor is the unified `elim` arm pinned to the `gen_fst` / `gen_snd` row.
    Surfaced premise: the pair term union-typed at `product(firstType, secondType)`; the classifier is
    forced to the selected component (`firstType` for fst, `secondType` for snd).

Both follow the established free-subject `induction` recipe with the three killer classes; the `idJCell`,
`fstCell`, `sndCell` heads are all untypable in the grown engine (host-head-untyped lemmas shipped), so
none carries an ofGrown disjunct.

## Zero-axiom

Free-subject `induction` + the shipped eleven-row inverter `elimRuleOf_cases` + the member-cell
head-projection `elimMemberCellRootGenerator` + head no-confusion + `rcases subjectShape with ⟨⟩`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## (1) Inversion at the idJ head -/

/-- **★ Inversion at the idJ head (GENUINE Paulin-Mohring).**  A union typing of an `idJCell`-headed subject
is EXACTLY a path-induction typing at the genuine `gen_idJ` row: for some carrier `A` and TWO endpoints
`left`, `right`, the witness is union-typed at the GENERAL identity code `Id(A, left, right)`, the base case
is union-typed at the diagonal motive instantiation `idJMotiveAt motive left (refl left) = C[left, refl left]`,
and the genuine dependent output `idJMotiveAt motive right witness = C[right, witness]` is `Conv`-equal to the
ambient classifier.  (The two-binder motive is stored, not premised; the right-endpoint typing premise is
likewise stored.)  Conv-modulo (like `invertAtFstHead`): the conv chain is surfaced, not applied — the
genuine-J iota SR consumer composes it with the JMAX-2 motive-instantiation transport.  No grown disjunct:
`idJCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtIdJHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode leftEndpoint rightEndpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context baseCase
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) ∧
      Conv (idJMotiveAt motive rightEndpoint witness) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `idJ` row (obligation order
  -- `[witness, rightEndpoint, baseCase, motive]`; `outputType = idJMotiveAt motive rightEndpoint witness`).
  -- The plain inversion surfaces the witness (obligation 0) + diagonal base-case (obligation 2) premises.
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := idJElimRule)
      (show elimRuleOf Generator.gen_idJ = some idJElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argWitness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeCode, leftEndpoint, rightEndpoint,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      outputConv⟩

/-- **★ Inversion at the idJ head, ALL FOUR premises (incl. the right-endpoint typing + the 2-extended-context
motive).**  The `invertAtIdJHead` companion that ADDITIONALLY surfaces the right-endpoint typing obligation
(`rightEndpoint : typeCode`) and the motive obligation (the two-binder motive union-typed at a universe over the
2-extended context `(context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)`, existential
in `level`/`flag`).  These are exactly the two premises the plain inversion drops but that rebuilding an `idJ`
cell — when one of its children steps — requires (the eliminator-congruence subject reduction, gate 2 of #1697:
the rebuilt cell's `elim` arm needs all four obligations).  Same recipe: induct the union derivation at a free
subject, refute every arm except the `gen_idJ` elim survivor, which surfaces all four obligations from
`premisesHold` (order `[witness, rightEndpoint, baseCase, motive]`); the `conv` arm threads them through and
composes its conversion onto the output leg. -/
theorem HasTypeUnion.invertAtIdJHeadAllPremises {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode leftEndpoint rightEndpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context rightEndpoint typeCode ∧
      HasTypeUnion profile context baseCase
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) ∧
      (∃ (motiveLevel : LevelExpr) (motiveFlag : UniverseFlag),
        HasTypeUnion profile
          ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
          (universeCodeCell motiveLevel motiveFlag)) ∧
      Conv (idJMotiveAt motive rightEndpoint witness) classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `idJ` row surfacing ALL four obligations
  -- (`[witness, rightEndpoint, baseCase, motive]`); the motive obligation's universe levels are the row's
  -- existential `level0`/`flag`, repackaged into the `∃ motiveLevel motiveFlag` conclusion.
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := idJElimRule)
      (show elimRuleOf Generator.gen_idJ = some idJElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argWitness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeCode, leftEndpoint, rightEndpoint,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      ⟨level0, flag, obligationsHold _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))⟩,
      outputConv⟩

/-! ## (1) Inversion at the fst head -/

/-- **★ Inversion at the fst head.**  A union typing of an `fstCell`-headed subject is EXACTLY a
projection typing at the `gen_fst` row: for some second-component type `B`, the pair term is union-typed
at `product(C, B)` where `C` is the classifier, and the projected type is the first component (the
classifier).  No grown disjunct: `fstCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtFstHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = fstCell pairTerm) :
    ∃ secondType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell pinnedClassifier secondType) ∧
      Conv pinnedClassifier classifier := by
  -- Thin specialization of the table-driven `invertAtElimHeadGeneric` at the `fst` row.  The generic
  -- hands back the row's children `args`, the type-index `params`, the cell-shape equation, the typed
  -- obligation list, and the output `Conv`; the `fst` wrapper destructures the one child / two params,
  -- recovers the pair term from `subjectShape` (cell injectivity), and surfaces the pair obligation
  -- (`outputType = firstType`, so the surfaced output `Conv` IS the pinned-classifier conv).
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := fstElimRule)
      (show elimRuleOf Generator.gen_fst = some fstElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argPair .childNil,
    .childCons firstType (.childCons secondType .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨secondType, firstType, obligationsHold _ (List.Mem.head _), outputConv⟩

/-! ## (1) Inversion at the snd head -/

/-- **★ Inversion at the snd head.**  A union typing of an `sndCell`-headed subject is EXACTLY a
projection typing at the `gen_snd` row: for some first-component type `A`, the pair term is union-typed
at `product(A, C)` where `C` is the classifier, and the projected type is the second component (the
classifier).  No grown disjunct: `sndCell` is untypable in the grown engine. -/
theorem HasTypeUnion.invertAtSndHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {pairTerm : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = sndCell pairTerm) :
    ∃ firstType pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context pairTerm
        (productTypeCell firstType pinnedClassifier) ∧
      Conv pinnedClassifier classifier := by
  -- Thin specialization of `invertAtElimHeadGeneric` at the `snd` row (`outputType = secondType`, so the
  -- surfaced output `Conv` IS the pinned-classifier conv); twin of `invertAtFstHead`.
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold, outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := sndElimRule)
      (show elimRuleOf Generator.gen_snd = some sndElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argPair .childNil,
    .childCons firstType (.childCons secondType .childNil),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨firstType, secondType, obligationsHold _ (List.Mem.head _), outputConv⟩

end FX1Poly.Typed
