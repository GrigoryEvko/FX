import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation

/-! # TraceCanonicalForm — the least-element canonical form (FREE-6c brick 5)

The Eckmann–Hilton falsification killed per-level minimal extraction: `normalizeSpine`
is not swap-invariant.  The corrected canonical form selects the LEAST element of the
saturated ~-class under a total key order — invariance holds BY CONSTRUCTION, because
equivalent seeds have the same saturated class as a set, and a total antisymmetric
order picks the same minimum from the same set.

  * `compareNatKeys` — self-contained `Ordering` on `Nat` by double structural
    recursion (no core order lemmas, hence no axiom risk);
  * `AtomKeying` — the choice data: an injective `Nat` key on spine atoms (the generic
    signature carries no enumeration, so the key is supplied per instance, like
    `GeneratorKeying`);
  * `compareTraces` — the lexicographic lift to traces, with reflexivity-as-`eq`,
    `eq`-implies-equal (antisymmetry's engine), swap symmetry (totality's engine), and
    `lt`-transitivity;
  * `selectSmallerTrace` / `selectLeastTraceFrom` — the fold computing the minimum,
    with membership and least-ness;
  * `canonicalTraceRepresentative` — the least element of the saturated class;
  * `canonicalTraceRepresentative_isEquivInvariant` ★ — gated on both frontiers
    exhausting, equivalent seeds produce THE SAME canonical trace.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The key order -/

/-- `Ordering` on `Nat` keys by double structural recursion — self-contained, so every
order fact below is a plain induction with no core order lemmas. -/
def compareNatKeys : Nat → Nat → Ordering
  | 0, 0 => Ordering.eq
  | 0, _ + 1 => Ordering.lt
  | _ + 1, 0 => Ordering.gt
  | firstPred + 1, secondPred + 1 => compareNatKeys firstPred secondPred

/-- Comparing a key with itself yields `eq`. -/
theorem compareNatKeys_selfIsEq : (key : Nat) → compareNatKeys key key = Ordering.eq
  | 0 => rfl
  | keyPred + 1 => compareNatKeys_selfIsEq keyPred

/-- The `eq` verdict means the keys are equal. -/
theorem compareNatKeys_eqImpliesEqual : {first second : Nat} →
    compareNatKeys first second = Ordering.eq → first = second
  | 0, 0, _ => rfl
  | 0, _ + 1, compared => nomatch compared
  | _ + 1, 0, compared => nomatch compared
  | _ + 1, _ + 1, compared =>
      congrArg Nat.succ (compareNatKeys_eqImpliesEqual compared)

/-- Swapping the arguments swaps the verdict. -/
theorem compareNatKeys_swapSymm : (first second : Nat) →
    compareNatKeys second first = (compareNatKeys first second).swap
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | firstPred + 1, secondPred + 1 => compareNatKeys_swapSymm firstPred secondPred

/-- The `lt` verdict is transitive. -/
theorem compareNatKeys_ltTrans : (first second third : Nat) →
    compareNatKeys first second = Ordering.lt →
    compareNatKeys second third = Ordering.lt →
    compareNatKeys first third = Ordering.lt
  | 0, 0, _, firstLt, _ => nomatch firstLt
  | _ + 1, 0, _, firstLt, _ => nomatch firstLt
  | 0, _ + 1, 0, _, secondLt => nomatch secondLt
  | _ + 1, _ + 1, 0, _, secondLt => nomatch secondLt
  | 0, _ + 1, _ + 1, _, _ => rfl
  | firstPred + 1, secondPred + 1, thirdPred + 1, firstLt, secondLt =>
      compareNatKeys_ltTrans firstPred secondPred thirdPred firstLt secondLt

/-! ## Atom keying and the trace order -/

/-- The choice data for the canonical form: an injective `Nat` key on spine atoms.
The generic signature carries no enumeration of its modes or generators, so a total
order cannot be derived — each instance supplies its key (the walking-adjunction and
bubble signatures both admit obvious ones). -/
structure AtomKeying (signature : ModeSignature)
    (overallSource overallTarget : signature.graph.Mode) : Type where
  /-- The key. -/
  keyOf : SpineAtom signature overallSource overallTarget → Nat
  /-- Injectivity — equal keys mean equal atoms. -/
  keyOf_isInjective : (firstAtom secondAtom : SpineAtom signature overallSource
      overallTarget) → keyOf firstAtom = keyOf secondAtom → firstAtom = secondAtom

/-- Lexicographic trace comparison over the atom keys: shorter-prefix first, then the
first differing key decides. -/
def compareTraces {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | firstAtom :: firstRest, secondAtom :: secondRest =>
      match compareNatKeys (keying.keyOf firstAtom) (keying.keyOf secondAtom) with
      | Ordering.lt => Ordering.lt
      | Ordering.gt => Ordering.gt
      | Ordering.eq => compareTraces keying firstRest secondRest

/-- Comparing a trace with itself yields `eq`. -/
theorem compareTraces_selfIsEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    (trace : List (SpineAtom signature overallSource overallTarget)) →
    compareTraces keying trace trace = Ordering.eq
  | [] => rfl
  | headAtom :: rest => by
      show (match compareNatKeys (keying.keyOf headAtom) (keying.keyOf headAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying rest rest) = Ordering.eq
      rw [compareNatKeys_selfIsEq]
      exact compareTraces_selfIsEq keying rest

/-- The `eq` verdict means the traces are equal — key injectivity pins each atom. -/
theorem compareTraces_eqImpliesEqual {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    {first second : List (SpineAtom signature overallSource overallTarget)} →
    compareTraces keying first second = Ordering.eq → first = second
  | [], [], _ => rfl
  | [], _ :: _, compared => nomatch compared
  | _ :: _, [], compared => nomatch compared
  | firstAtom :: firstRest, secondAtom :: secondRest, compared => by
      have comparedShaped : (match compareNatKeys (keying.keyOf firstAtom)
          (keying.keyOf secondAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying firstRest secondRest) = Ordering.eq :=
        compared
      cases keysCompared : compareNatKeys (keying.keyOf firstAtom)
          (keying.keyOf secondAtom) with
      | lt =>
          rw [keysCompared] at comparedShaped
          exact (nomatch comparedShaped)
      | gt =>
          rw [keysCompared] at comparedShaped
          exact (nomatch comparedShaped)
      | eq =>
          rw [keysCompared] at comparedShaped
          have atomsEqual : firstAtom = secondAtom :=
            keying.keyOf_isInjective firstAtom secondAtom
              (compareNatKeys_eqImpliesEqual keysCompared)
          have restsEqual : firstRest = secondRest :=
            compareTraces_eqImpliesEqual keying comparedShaped
          rw [atomsEqual, restsEqual]

/-- Swapping the traces swaps the verdict. -/
theorem compareTraces_swapSymm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    (first second : List (SpineAtom signature overallSource overallTarget)) →
    compareTraces keying second first = (compareTraces keying first second).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | firstAtom :: firstRest, secondAtom :: secondRest => by
      show (match compareNatKeys (keying.keyOf secondAtom) (keying.keyOf firstAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying secondRest firstRest)
        = (match compareNatKeys (keying.keyOf firstAtom) (keying.keyOf secondAtom) with
          | Ordering.lt => Ordering.lt
          | Ordering.gt => Ordering.gt
          | Ordering.eq => compareTraces keying firstRest secondRest).swap
      rw [compareNatKeys_swapSymm (keying.keyOf firstAtom) (keying.keyOf secondAtom)]
      cases compareNatKeys (keying.keyOf firstAtom) (keying.keyOf secondAtom) with
      | lt => rfl
      | gt => rfl
      | eq => exact compareTraces_swapSymm keying firstRest secondRest

/-- The `lt` verdict is transitive — the `eq` corners collapse by key injectivity. -/
theorem compareTraces_ltTrans {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    {first second third : List (SpineAtom signature overallSource overallTarget)} →
    compareTraces keying first second = Ordering.lt →
    compareTraces keying second third = Ordering.lt →
    compareTraces keying first third = Ordering.lt
  | [], [], _, firstLt, _ => nomatch firstLt
  | _ :: _, [], _, firstLt, _ => nomatch firstLt
  | [], _ :: _, [], _, secondLt => nomatch secondLt
  | _ :: _, _ :: _, [], _, secondLt => nomatch secondLt
  | [], _ :: _, _ :: _, _, _ => rfl
  | firstAtom :: firstRest, secondAtom :: secondRest, thirdAtom :: thirdRest,
      firstLt, secondLt => by
      have firstShaped : (match compareNatKeys (keying.keyOf firstAtom)
          (keying.keyOf secondAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying firstRest secondRest) = Ordering.lt :=
        firstLt
      have secondShaped : (match compareNatKeys (keying.keyOf secondAtom)
          (keying.keyOf thirdAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying secondRest thirdRest) = Ordering.lt :=
        secondLt
      show (match compareNatKeys (keying.keyOf firstAtom) (keying.keyOf thirdAtom) with
        | Ordering.lt => Ordering.lt
        | Ordering.gt => Ordering.gt
        | Ordering.eq => compareTraces keying firstRest thirdRest) = Ordering.lt
      cases firstKeys : compareNatKeys (keying.keyOf firstAtom)
          (keying.keyOf secondAtom) with
      | gt =>
          rw [firstKeys] at firstShaped
          exact (nomatch firstShaped)
      | lt =>
          cases secondKeys : compareNatKeys (keying.keyOf secondAtom)
              (keying.keyOf thirdAtom) with
          | lt => rw [compareNatKeys_ltTrans _ _ _ firstKeys secondKeys]
          | gt =>
              rw [secondKeys] at secondShaped
              exact (nomatch secondShaped)
          | eq =>
              have secondThirdEqual : secondAtom = thirdAtom :=
                keying.keyOf_isInjective secondAtom thirdAtom
                  (compareNatKeys_eqImpliesEqual secondKeys)
              rw [← secondThirdEqual, firstKeys]
      | eq =>
          have firstSecondEqual : firstAtom = secondAtom :=
            keying.keyOf_isInjective firstAtom secondAtom
              (compareNatKeys_eqImpliesEqual firstKeys)
          rw [firstKeys] at firstShaped
          cases secondKeys : compareNatKeys (keying.keyOf secondAtom)
              (keying.keyOf thirdAtom) with
          | lt => rw [firstSecondEqual, secondKeys]
          | gt =>
              rw [secondKeys] at secondShaped
              exact (nomatch secondShaped)
          | eq =>
              have secondThirdEqual : secondAtom = thirdAtom :=
                keying.keyOf_isInjective secondAtom thirdAtom
                  (compareNatKeys_eqImpliesEqual secondKeys)
              rw [secondKeys] at secondShaped
              rw [firstSecondEqual, secondThirdEqual, compareNatKeys_selfIsEq]
              exact compareTraces_ltTrans keying firstShaped secondShaped

/-! ## The non-strict order -/

/-- Non-strict trace order: the comparison does not say `gt`. -/
abbrev IsTraceLeq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (first second : List (SpineAtom signature overallSource overallTarget)) : Prop :=
  compareTraces keying first second ≠ Ordering.gt

/-- Every trace is `leq` itself. -/
theorem isTraceLeq_ofSelf {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (trace : List (SpineAtom signature overallSource overallTarget)) :
    IsTraceLeq keying trace trace := by
  intro isGt
  rw [compareTraces_selfIsEq keying trace] at isGt
  exact (nomatch isGt)

/-- The non-strict order is transitive — `eq` verdicts collapse to equalities, `lt`
verdicts chain through `lt`-transitivity. -/
theorem isTraceLeq_trans {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    {first second third : List (SpineAtom signature overallSource overallTarget)}
    (firstLeq : IsTraceLeq keying first second)
    (secondLeq : IsTraceLeq keying second third) :
    IsTraceLeq keying first third := by
  cases firstCompared : compareTraces keying first second with
  | gt => exact (firstLeq firstCompared).elim
  | eq =>
      have firstSecondEqual : first = second :=
        compareTraces_eqImpliesEqual keying firstCompared
      rw [firstSecondEqual]
      exact secondLeq
  | lt =>
      cases secondCompared : compareTraces keying second third with
      | gt => exact (secondLeq secondCompared).elim
      | eq =>
          have secondThirdEqual : second = third :=
            compareTraces_eqImpliesEqual keying secondCompared
          rw [← secondThirdEqual]
          intro isGt
          rw [firstCompared] at isGt
          exact (nomatch isGt)
      | lt =>
          intro isGt
          rw [compareTraces_ltTrans keying firstCompared secondCompared] at isGt
          exact (nomatch isGt)

/-! ## Least-element selection -/

/-- Keep the smaller of two traces (the first on ties). -/
def selectSmallerTrace {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (first second : List (SpineAtom signature overallSource overallTarget)) :
    List (SpineAtom signature overallSource overallTarget) :=
  match compareTraces keying first second with
  | Ordering.lt => first
  | Ordering.eq => first
  | Ordering.gt => second

/-- On a `gt` verdict the selection takes the second trace. -/
theorem selectSmallerTrace_ofGt {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    {first second : List (SpineAtom signature overallSource overallTarget)}
    (compared : compareTraces keying first second = Ordering.gt) :
    selectSmallerTrace keying first second = second := by
  show (match compareTraces keying first second with
    | Ordering.lt => first
    | Ordering.eq => first
    | Ordering.gt => second) = second
  rw [compared]

/-- Without a `gt` verdict the selection keeps the first trace. -/
theorem selectSmallerTrace_ofNotGt {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    {first second : List (SpineAtom signature overallSource overallTarget)}
    (notGt : compareTraces keying first second ≠ Ordering.gt) :
    selectSmallerTrace keying first second = first := by
  show (match compareTraces keying first second with
    | Ordering.lt => first
    | Ordering.eq => first
    | Ordering.gt => second) = first
  cases compared : compareTraces keying first second with
  | lt => rfl
  | eq => rfl
  | gt => exact (notGt compared).elim

/-- The selection returns one of its two inputs. -/
theorem selectSmallerTrace_isEither {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (first second : List (SpineAtom signature overallSource overallTarget)) :
    selectSmallerTrace keying first second = first ∨
      selectSmallerTrace keying first second = second := by
  cases compared : compareTraces keying first second with
  | gt => exact Or.inr (selectSmallerTrace_ofGt keying compared)
  | lt =>
      exact Or.inl (selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt)))
  | eq =>
      exact Or.inl (selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt)))

/-- The selection is `leq` its first input. -/
theorem selectSmallerTrace_isLeqFirst {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (first second : List (SpineAtom signature overallSource overallTarget)) :
    IsTraceLeq keying (selectSmallerTrace keying first second) first := by
  cases compared : compareTraces keying first second with
  | gt =>
      rw [selectSmallerTrace_ofGt keying compared]
      intro isGt
      rw [compareTraces_swapSymm keying first second, compared] at isGt
      exact (nomatch isGt)
  | lt =>
      rw [selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt))]
      exact isTraceLeq_ofSelf keying first
  | eq =>
      rw [selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt))]
      exact isTraceLeq_ofSelf keying first

/-- The selection is `leq` its second input. -/
theorem selectSmallerTrace_isLeqSecond {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (first second : List (SpineAtom signature overallSource overallTarget)) :
    IsTraceLeq keying (selectSmallerTrace keying first second) second := by
  cases compared : compareTraces keying first second with
  | gt =>
      rw [selectSmallerTrace_ofGt keying compared]
      exact isTraceLeq_ofSelf keying second
  | lt =>
      rw [selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt))]
      intro isGt
      rw [compared] at isGt
      exact (nomatch isGt)
  | eq =>
      rw [selectSmallerTrace_ofNotGt keying
        (fun isGt => nomatch (compared.symm.trans isGt))]
      intro isGt
      rw [compared] at isGt
      exact (nomatch isGt)

/-- Fold the selection over a candidate list, starting from a current best. -/
def selectLeastTraceFrom {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (currentBest : List (SpineAtom signature overallSource overallTarget)) :
    List (List (SpineAtom signature overallSource overallTarget)) →
    List (SpineAtom signature overallSource overallTarget)
  | [] => currentBest
  | nextCandidate :: remainingCandidates =>
      selectLeastTraceFrom keying (selectSmallerTrace keying currentBest nextCandidate)
        remainingCandidates

/-- The fold returns its starting best or one of the candidates. -/
theorem selectLeastTraceFrom_isCurrentOrMember {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    (candidates : List (List (SpineAtom signature overallSource overallTarget))) →
    (currentBest : List (SpineAtom signature overallSource overallTarget)) →
    selectLeastTraceFrom keying currentBest candidates = currentBest ∨
      selectLeastTraceFrom keying currentBest candidates ∈ candidates
  | [], _ => Or.inl rfl
  | nextCandidate :: remainingCandidates, currentBest => by
      show selectLeastTraceFrom keying
          (selectSmallerTrace keying currentBest nextCandidate) remainingCandidates
          = currentBest ∨
        selectLeastTraceFrom keying
          (selectSmallerTrace keying currentBest nextCandidate) remainingCandidates
          ∈ nextCandidate :: remainingCandidates
      rcases selectLeastTraceFrom_isCurrentOrMember keying remainingCandidates
          (selectSmallerTrace keying currentBest nextCandidate) with isSmaller | isMember
      · rcases selectSmallerTrace_isEither keying currentBest nextCandidate
            with isFirst | isSecond
        · exact Or.inl (isSmaller.trans isFirst)
        · rw [isSmaller, isSecond]
          exact Or.inr (List.Mem.head remainingCandidates)
      · exact Or.inr (List.Mem.tail nextCandidate isMember)

/-- The fold's result is `leq` the starting best and every candidate. -/
theorem selectLeastTraceFrom_isLeqAll {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget) :
    (candidates : List (List (SpineAtom signature overallSource overallTarget))) →
    (currentBest : List (SpineAtom signature overallSource overallTarget)) →
    IsTraceLeq keying (selectLeastTraceFrom keying currentBest candidates)
        currentBest ∧
      ∀ candidate, candidate ∈ candidates →
        IsTraceLeq keying (selectLeastTraceFrom keying currentBest candidates)
          candidate
  | [], currentBest =>
      ⟨isTraceLeq_ofSelf keying currentBest, fun _ absurdMem => nomatch absurdMem⟩
  | nextCandidate :: remainingCandidates, currentBest => by
      obtain ⟨leqSmaller, leqRemaining⟩ := selectLeastTraceFrom_isLeqAll keying
        remainingCandidates (selectSmallerTrace keying currentBest nextCandidate)
      constructor
      · exact isTraceLeq_trans keying leqSmaller
          (selectSmallerTrace_isLeqFirst keying currentBest nextCandidate)
      · intro candidate candidateMem
        rcases listMemConsCases candidateMem with isNext | inRemaining
        · rw [isNext]
          exact isTraceLeq_trans keying leqSmaller
            (selectSmallerTrace_isLeqSecond keying currentBest nextCandidate)
        · exact leqRemaining candidate inRemaining

/-! ## The canonical form ★ -/

/-- ★ **The canonical representative**: the least element of the seed's saturated
~-class under the key order. -/
def canonicalTraceRepresentative {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    List (SpineAtom signature overallSource overallTarget) :=
  selectLeastTraceFrom keying seedTrace
    (saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace)

/-- The canonical representative lives in the saturated class. -/
theorem canonicalTraceRepresentative_isInClass {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuel
        seedTrace
      ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace := by
  show selectLeastTraceFrom keying seedTrace
      (saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace)
    ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace
  rcases selectLeastTraceFrom_isCurrentOrMember keying
      (saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace) seedTrace
      with isSeed | isMember
  · rw [isSeed]
    exact saturateClass_containsSeed modeDecEq modalityDecEq twoCellDecEq fuel seedTrace
  · exact isMember

/-- The canonical representative is trace-equivalent to its seed. -/
theorem canonicalTraceRepresentative_isEquivToSeed {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    AtomicTraceEquiv signature seedTrace
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuel
        seedTrace) :=
  saturateClass_isSound modeDecEq modalityDecEq twoCellDecEq
    (canonicalTraceRepresentative_isInClass keying modeDecEq modalityDecEq twoCellDecEq
      fuel seedTrace)

/-- ★ **Canonical-form invariance** — the theorem the falsified per-level extraction
could never give: gated on both frontiers exhausting, EQUIVALENT seeds produce THE
SAME canonical trace.  Equivalent seeds have the same saturated class as a set
(soundness + completeness both ways), each canonical is least over a list containing
the other, and antisymmetry of the total key order forces them equal. -/
theorem canonicalTraceRepresentative_isEquivInvariant {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : AtomKeying signature overallSource overallTarget)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {fuelOne fuelTwo : Nat}
    {seedOne seedTwo : List (SpineAtom signature overallSource overallTarget)}
    (didExhaustOne : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuelOne
      [seedOne] [seedOne] = true)
    (didExhaustTwo : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuelTwo
      [seedTwo] [seedTwo] = true)
    (seedsEquiv : AtomicTraceEquiv signature seedOne seedTwo) :
    canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne
      = canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
        fuelTwo seedTwo := by
  have firstEquivSeedOne : AtomicTraceEquiv signature seedOne
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne) :=
    canonicalTraceRepresentative_isEquivToSeed keying modeDecEq modalityDecEq
      twoCellDecEq fuelOne seedOne
  have secondEquivSeedTwo : AtomicTraceEquiv signature seedTwo
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelTwo
        seedTwo) :=
    canonicalTraceRepresentative_isEquivToSeed keying modeDecEq modalityDecEq
      twoCellDecEq fuelTwo seedTwo
  have firstInSecondClass : canonicalTraceRepresentative keying modeDecEq modalityDecEq
      twoCellDecEq fuelOne seedOne
      ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuelTwo seedTwo :=
    saturateClass_isComplete modeDecEq modalityDecEq twoCellDecEq didExhaustTwo
      (AtomicTraceEquiv.trans (AtomicTraceEquiv.symm seedsEquiv) firstEquivSeedOne)
  have secondInFirstClass : canonicalTraceRepresentative keying modeDecEq modalityDecEq
      twoCellDecEq fuelTwo seedTwo
      ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuelOne seedOne :=
    saturateClass_isComplete modeDecEq modalityDecEq twoCellDecEq didExhaustOne
      (AtomicTraceEquiv.trans seedsEquiv secondEquivSeedTwo)
  obtain ⟨_firstLeqSeed, firstLeqAll⟩ := selectLeastTraceFrom_isLeqAll keying
    (saturateClass modeDecEq modalityDecEq twoCellDecEq fuelOne seedOne) seedOne
  obtain ⟨_secondLeqSeed, secondLeqAll⟩ := selectLeastTraceFrom_isLeqAll keying
    (saturateClass modeDecEq modalityDecEq twoCellDecEq fuelTwo seedTwo) seedTwo
  have firstLeqSecond : IsTraceLeq keying
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne)
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelTwo
        seedTwo) :=
    firstLeqAll
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelTwo
        seedTwo)
      secondInFirstClass
  have secondLeqFirst : IsTraceLeq keying
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelTwo
        seedTwo)
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne) :=
    secondLeqAll
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne)
      firstInSecondClass
  cases compared : compareTraces keying
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        seedOne)
      (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelTwo
        seedTwo) with
  | eq => exact compareTraces_eqImpliesEqual keying compared
  | gt => exact (firstLeqSecond compared).elim
  | lt =>
      have swapped : compareTraces keying
          (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
            fuelTwo seedTwo)
          (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
            fuelOne seedOne) = Ordering.gt := by
        rw [compareTraces_swapSymm keying
          (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
            fuelOne seedOne)
          (canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
            fuelTwo seedTwo), compared]
        rfl
      exact (secondLeqFirst swapped).elim

end FX1Poly.Polygraph
