import LeanFX2.Algo.Soundness.HeadStepPayloadIota

namespace LeanFX2

/-! ## Closure soundness

`Term.headStep?_sound` combines the 6 per-case theorems above
into a single closed-over statement: whenever `headStep?` fires
(returns `some _`), the result is reachable via `Step` from the
source term.

This is the load-bearing soundness contract for `Algo/Eval`:
the typed evaluator never produces a result that disagrees with
the kernel's reduction relation.

The proof case-analyses on the source term's outer constructor:
* Value, neutral, and deferred redex ctors have `headStep? = none`
  definitionally; the `firedEq : none = some _` hypothesis is closed
  by `nomatch`.
* 7 firing eliminator ctors (fst, boolElim, natElim, natRec,
  listElim, optionMatch, eitherMatch) each delegate to a private
  helper that splits on the scrutinee's `headCtor` to identify which
  ι-rule fired, then applies the corresponding per-case theorem.

Zero-axiom under strict policy. -/


variable {mode : Mode} {level : Nat}

/-! ### Per-firing-eliminator helper lemmas

Each firing eliminator (`fst`, `boolElim`, `natElim`, `natRec`,
`listElim`, `optionMatch`, `eitherMatch`) hosts its proof in a
separate `private` lemma so the kernel re-checks each piece
independently (and Lean's in-file parallel elaborator can run them
concurrently), rather than re-typechecking one monster term inside a
78-arm `cases`.

Two further levers keep each helper's own proof term small:

* Each helper cites a one-shot `headStep<Ctor>Unfold` lemma (proved
  by `rfl`) to expose the `headStep?` body ONCE, instead of embedding
  the large body literal in every `match`-arm's `rw [show ... from
  rfl]`.
* `boolElim`'s `headStep?` body dispatches on `scrutineeRaw` directly
  (a dependent index of the `result` type), so its non-firing reasoning
  is hoisted into `headStepBoolElimNoneOfRawNe` (whose `headStep? =
  none` conclusion is `scrutineeRaw`-independent) plus the
  `boolScrutineeRawNe*` disequality bridges.  The helper itself then
  dispatches on the cheap `headCtor` enum like the others. -/

/-- One-shot `rfl` unfold of `headStep?` on a `fst` projection (see
`headStepNatElimUnfold` for the rationale). -/
private theorem Term.headStepFstUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    (Term.fst pairTerm).headStep?
      = (let pairHead := pairTerm.headCtor
         if pairHead == .pair then
           match Term.tryDestructPair pairTerm with
           | some ⟨_, _, firstValue, _, _⟩ => some ⟨_, firstValue⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundFst
    {scope : Nat} {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context firstType resultRaw}
    (firedEq : (Term.fst pairTerm).headStep? = some result) :
    Step (Term.fst pairTerm) result.snd := by
  rw [Term.headStepFstUnfold] at firedEq
  match headEq : pairTerm.headCtor with
  | .pair =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructPair pairTerm with
    | some ⟨_, _, firstValue, secondValue, ⟨rawEq, pairHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have pairEq : pairTerm = Term.pair firstValue secondValue :=
        eq_of_heq pairHEq
      rw [pairEq]
      exact Step.betaFstPair firstValue secondValue
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natZero | .natSucc | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

/-- `headStep?` of a `boolElim` returns a result only for the two
canonical Boolean scrutinee heads.  For every other raw head it is
`none`.

Stating the conclusion as `headStep? = none` (rather than threading a
dependent `result : Σ ..., Term context (motiveType.subst0 Ty.bool
scrutineeRaw) ...`) keeps the matcher motive INDEPENDENT of
`scrutineeRaw`: the 78-arm `match` here does not have to re-abstract a
`scrutineeRaw`-dependent result type, so its proof term -- and the
kernel's re-check of it -- is small.  The firing helper below dispatches
on the cheap `headCtor` enum and cites this lemma to discharge every
non-Boolean head in one shot. -/
private theorem Term.headStepBoolElimNoneOfRawNe
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (notTrue : scrutineeRaw ≠ RawTerm.boolTrue)
    (notFalse : scrutineeRaw ≠ RawTerm.boolFalse) :
    (Term.boolElim scrutinee thenBranch elseBranch).headStep? = none := by
  match scrutineeRaw, notTrue, notFalse with
  | .boolTrue, contra, _ => exact absurd rfl contra
  | .boolFalse, _, contra => exact absurd rfl contra
  | .var _, _, _
  | .unit, _, _
  | .lam _, _, _
  | .app _ _, _, _
  | .pair _ _, _, _
  | .fst _, _, _
  | .snd _, _, _
  | .boolElim _ _ _, _, _
  | .natZero, _, _
  | .natSucc _, _, _
  | .natElim _ _ _, _, _
  | .natRec _ _ _, _, _
  | .listNil, _, _
  | .listCons _ _, _, _
  | .listElim _ _ _, _, _
  | .optionNone, _, _
  | .optionSome _, _, _
  | .optionMatch _ _ _, _, _
  | .eitherInl _, _, _
  | .eitherInr _, _, _
  | .eitherMatch _ _ _, _, _
  | .refl _, _, _
  | .idJ _ _, _, _
  | .oeqRefl _, _, _
  | .oeqJ _ _, _, _
  | .oeqFunext _, _, _
  | .idStrictRefl _, _, _
  | .idStrictRec _ _, _, _
  | .modIntro _, _, _
  | .modElim _, _, _
  | .subsume _, _, _
  | .interval0, _, _
  | .interval1, _, _
  | .intervalOpp _, _, _
  | .intervalMeet _ _, _, _
  | .intervalJoin _ _, _, _
  | .pathLam _, _, _
  | .pathApp _ _, _, _
  | .glueIntro _ _, _, _
  | .glueElim _, _, _
  | .transp _ _, _, _
  | .transpFill _ _ _, _, _
  | .hcomp _ _, _, _
  | .recordIntro _, _, _
  | .recordProj _, _, _
  | .refineIntro _ _, _, _
  | .refineElim _, _, _
  | .codataUnfold _ _, _, _
  | .codataDest _, _, _
  | .sessionSend _ _, _, _
  | .sessionRecv _, _, _
  | .effectPerform _ _, _, _
  | .universeCode _, _, _
  | .cumulUpMarker _, _, _
  | .uaToEquiv _, _, _
  | .equivApply _ _, _, _
  | .equivIntro _ _, _, _
  | .equivApp _ _, _, _
  | .arrowCode _ _, _, _
  | .piTyCode _ _, _, _
  | .sigmaTyCode _ _, _, _
  | .productCode _ _, _, _
  | .sumCode _ _, _, _
  | .listCode _, _, _
  | .optionCode _, _, _
  | .eitherCode _ _, _, _
  | .idCode _ _ _, _, _
  | .equivCode _ _, _, _
  | .pathCompose _ _, _, _
  | .idToEquiv _, _, _
  | .oeqTrans _ _, _, _
  | .equivCompose _ _, _, _ =>
    rfl

/-- A `boolTrue`-shaped raw scrutinee forces `headCtor = boolTrue`.
The contrapositive (used below) turns a non-`boolTrue` head into a
non-`boolTrue` raw without touching the dependent `headEq` hypothesis
of the caller's `match` arm. -/
private theorem Term.boolScrutineeRawNeTrue
    {scope : Nat} {context : Ctx mode level scope}
    {scrutineeRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (headNeTrue : scrutinee.headCtor ≠ Term.HeadCtor.boolTrue) :
    scrutineeRaw ≠ RawTerm.boolTrue := by
  intro rawEq
  cases rawEq
  have scrutEq : scrutinee = Term.boolTrue :=
    eq_of_heq (Term.boolTrue_unique scrutinee Term.boolTrue)
  rw [scrutEq] at headNeTrue
  exact headNeTrue rfl

/-- A `boolFalse`-shaped raw scrutinee forces `headCtor = boolFalse`. -/
private theorem Term.boolScrutineeRawNeFalse
    {scope : Nat} {context : Ctx mode level scope}
    {scrutineeRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (headNeFalse : scrutinee.headCtor ≠ Term.HeadCtor.boolFalse) :
    scrutineeRaw ≠ RawTerm.boolFalse := by
  intro rawEq
  cases rawEq
  have scrutEq : scrutinee = Term.boolFalse :=
    eq_of_heq (Term.boolFalse_unique scrutinee Term.boolFalse)
  rw [scrutEq] at headNeFalse
  exact headNeFalse rfl

private theorem Term.headStepSoundBoolElim
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context (motiveType.subst0 Ty.bool scrutineeRaw) resultRaw}
    (firedEq :
      (Term.boolElim scrutinee thenBranch elseBranch).headStep? = some result) :
    Step (Term.boolElim scrutinee thenBranch elseBranch) result.snd := by
  -- Dispatch on the cheap `headCtor` enum.  The two firing arms
  -- discharge through the `headCtor`-keyed base helpers; every other
  -- head is rejected via `headStepBoolElimNoneOfRawNe`, which carries
  -- the (otherwise expensive) 78-arm `scrutineeRaw` reasoning in its
  -- own small, `scrutineeRaw`-independent proof term.  The two
  -- raw-disequality witnesses come from the `boolScrutineeRawNe*`
  -- helpers, keeping each `match` arm here a small term.
  match headEq : scrutinee.headCtor with
  | .boolTrue =>
    cases Term.headCtor_boolTrue_raw scrutinee headEq
    cases firedEq
    exact Term.headStep?_sound_boolElimTrue scrutinee thenBranch elseBranch headEq
  | .boolFalse =>
    cases Term.headCtor_boolFalse_raw scrutinee headEq
    cases firedEq
    exact Term.headStep?_sound_boolElimFalse scrutinee thenBranch elseBranch headEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolElim
  | .natZero | .natSucc | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    -- Head is not a canonical Boolean value, so neither Boolean raw
    -- head applies; `headStep?` is then `none`, contradicting
    -- `firedEq`.
    exact absurd firedEq (by
      rw [Term.headStepBoolElimNoneOfRawNe scrutinee thenBranch elseBranch
            (Term.boolScrutineeRawNeTrue scrutinee (by rw [headEq]; decide))
            (Term.boolScrutineeRawNeFalse scrutinee (by rw [headEq]; decide))]
      exact fun contra => nomatch contra)

/-- One-shot `rfl` unfold of `headStep?` on a `natElim`.  Hoisting the
(large) body literal into a single lemma means each firing arm cites
it instead of re-embedding the whole `if`/`tryDestruct` body -- the
literal is elaborated and kernel-checked ONCE rather than three times
across the helper's arms. -/
private theorem Term.headStepNatElimUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    (Term.natElim scrutinee zeroBranch succBranch).headStep?
      = (let scrutineeHead := scrutinee.headCtor
         if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
         else if scrutineeHead == .natSucc then
           match Term.tryDestructNatSucc scrutinee with
           | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundNatElim
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context motiveType resultRaw}
    (firedEq :
      (Term.natElim scrutinee zeroBranch succBranch).headStep? = some result) :
    Step (Term.natElim scrutinee zeroBranch succBranch) result.snd := by
  rw [Term.headStepNatElimUnfold] at firedEq
  match headEq : scrutinee.headCtor with
  | .natZero =>
    rw [headEq] at firedEq
    cases firedEq
    exact Term.headStep?_sound_natElimZero scrutinee zeroBranch succBranch headEq
  | .natSucc =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructNatSucc scrutinee with
    | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaNatElimSucc predTerm zeroBranch succBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

/-- One-shot `rfl` unfold of `headStep?` on a `natRec` (see
`headStepNatElimUnfold` for the rationale). -/
private theorem Term.headStepNatRecUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    (Term.natRec scrutinee zeroBranch succBranch).headStep?
      = (let scrutineeHead := scrutinee.headCtor
         if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
         else if scrutineeHead == .natSucc then
           match Term.tryDestructNatSucc scrutinee with
           | some ⟨_, predTerm, _⟩ =>
               some ⟨_, Term.app (Term.app succBranch predTerm)
                                  (Term.natRec predTerm zeroBranch succBranch)⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundNatRec
    {scope : Nat} {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context motiveType resultRaw}
    (firedEq :
      (Term.natRec scrutinee zeroBranch succBranch).headStep? = some result) :
    Step (Term.natRec scrutinee zeroBranch succBranch) result.snd := by
  rw [Term.headStepNatRecUnfold] at firedEq
  match headEq : scrutinee.headCtor with
  | .natZero =>
    rw [headEq] at firedEq
    cases firedEq
    exact Term.headStep?_sound_natRecZero scrutinee zeroBranch succBranch headEq
  | .natSucc =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructNatSucc scrutinee with
    | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaNatRecSucc predTerm zeroBranch succBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

/-- One-shot `rfl` unfold of `headStep?` on a `listElim` (see
`headStepNatElimUnfold` for the rationale). -/
private theorem Term.headStepListElimUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    (Term.listElim scrutinee nilBranch consBranch).headStep?
      = (let scrutineeHead := scrutinee.headCtor
         if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
         else if scrutineeHead == .listCons then
           match Term.tryDestructListCons scrutinee with
           | some ⟨_, _, headTerm, tailTerm, _⟩ =>
               some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundListElim
    {scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context motiveType resultRaw}
    (firedEq :
      (Term.listElim scrutinee nilBranch consBranch).headStep? = some result) :
    Step (Term.listElim scrutinee nilBranch consBranch) result.snd := by
  rw [Term.headStepListElimUnfold] at firedEq
  match headEq : scrutinee.headCtor with
  | .listNil =>
    rw [headEq] at firedEq
    cases firedEq
    exact Term.headStep?_sound_listElimNil scrutinee nilBranch consBranch headEq
  | .listCons =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructListCons scrutinee with
    | some ⟨_, _, headTerm, tailTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq : scrutinee = Term.listCons headTerm tailTerm :=
        eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaListElimCons headTerm tailTerm nilBranch consBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natZero | .natSucc | .natElim | .natRec
  | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

/-- One-shot `rfl` unfold of `headStep?` on an `optionMatch` (see
`headStepNatElimUnfold` for the rationale). -/
private theorem Term.headStepOptionMatchUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    (Term.optionMatch scrutinee noneBranch someBranch).headStep?
      = (let scrutineeHead := scrutinee.headCtor
         if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
         else if scrutineeHead == .optionSome then
           match Term.tryDestructOptionSome scrutinee with
           | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundOptionMatch
    {scope : Nat} {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context motiveType resultRaw}
    (firedEq :
      (Term.optionMatch scrutinee noneBranch someBranch).headStep? = some result) :
    Step (Term.optionMatch scrutinee noneBranch someBranch) result.snd := by
  rw [Term.headStepOptionMatchUnfold] at firedEq
  match headEq : scrutinee.headCtor with
  | .optionNone =>
    rw [headEq] at firedEq
    cases firedEq
    exact Term.headStep?_sound_optionMatchNone scrutinee noneBranch someBranch headEq
  | .optionSome =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructOptionSome scrutinee with
    | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq : scrutinee = Term.optionSome valueTerm :=
        eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaOptionMatchSome valueTerm noneBranch someBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natZero | .natSucc | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionMatch
  | .eitherInl | .eitherInr | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

/-- One-shot `rfl` unfold of `headStep?` on an `eitherMatch` (see
`headStepNatElimUnfold` for the rationale). -/
private theorem Term.headStepEitherMatchUnfold
    {scope : Nat} {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
      = (let scrutineeHead := scrutinee.headCtor
         if scrutineeHead == .eitherInl then
           match Term.tryDestructEitherInl scrutinee with
           | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
           | none => none
         else if scrutineeHead == .eitherInr then
           match Term.tryDestructEitherInr scrutinee with
           | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
           | none => none
         else none) := rfl

private theorem Term.headStepSoundEitherMatch
    {scope : Nat} {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    {result : Σ (resultRaw : RawTerm scope),
      Term context motiveType resultRaw}
    (firedEq :
      (Term.eitherMatch scrutinee leftBranch rightBranch).headStep? = some result) :
    Step (Term.eitherMatch scrutinee leftBranch rightBranch) result.snd := by
  rw [Term.headStepEitherMatchUnfold] at firedEq
  match headEq : scrutinee.headCtor with
  | .eitherInl =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructEitherInl scrutinee with
    | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq :
          scrutinee = Term.eitherInl (rightType := _) valueTerm :=
        eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaEitherMatchInl valueTerm leftBranch rightBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .eitherInr =>
    rw [headEq] at firedEq
    match destructEq : Term.tryDestructEitherInr scrutinee with
    | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
      rw [destructEq] at firedEq
      cases firedEq
      cases rawEq
      have scrutEq :
          scrutinee = Term.eitherInr (leftType := _) valueTerm :=
        eq_of_heq scrutineeHEq
      rw [scrutEq]
      exact Step.iotaEitherMatchInr valueTerm leftBranch rightBranch
    | none =>
      rw [destructEq] at firedEq
      nomatch firedEq
  | .var | .unit | .lam | .app | .lamPi | .appPi
  | .pair | .fst | .snd
  | .boolTrue | .boolFalse | .boolElim
  | .natZero | .natSucc | .natElim | .natRec
  | .listNil | .listCons | .listElim
  | .optionNone | .optionSome | .optionMatch
  | .eitherMatch
  | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
  | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
  | .pathLam | .pathApp
  | .glueIntro | .glueElim | .transp | .hcomp
  | .recordIntro | .recordProj | .refineIntro | .refineElim
  | .codataUnfold | .codataDest
  | .sessionSend | .sessionRecv | .effectPerform
  | .universeCode | .cumulUp
  | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
  | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
  | .equivApply
  | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
  | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
    rw [headEq] at firedEq
    nomatch firedEq

theorem Term.headStep?_sound
    {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context someType raw)
    {result : Σ (resultRaw : RawTerm scope), Term context someType resultRaw}
    (firedEq : someTerm.headStep? = some result) :
    Step someTerm result.snd := by
  cases someTerm with
  | var _ => nomatch firedEq
  | unit => nomatch firedEq
  | lam _ => nomatch firedEq
  | lamPi _ => nomatch firedEq
  | pair _ _ => nomatch firedEq
  | boolTrue => nomatch firedEq
  | boolFalse => nomatch firedEq
  | natZero => nomatch firedEq
  | natSucc _ => nomatch firedEq
  | listNil => nomatch firedEq
  | listCons _ _ => nomatch firedEq
  | optionNone => nomatch firedEq
  | optionSome _ => nomatch firedEq
  | eitherInl _ => nomatch firedEq
  | eitherInr _ => nomatch firedEq
  | refl _ _ => nomatch firedEq
  | oeqRefl _ _ => nomatch firedEq
  | oeqJ _ _ => nomatch firedEq
  | oeqFunext _ _ _ _ _ => nomatch firedEq
  | modIntro _ => nomatch firedEq
  | subsume _ => nomatch firedEq
  | interval0 => nomatch firedEq
  | interval1 => nomatch firedEq
  | intervalOpp _ => nomatch firedEq
  | intervalMeet _ _ => nomatch firedEq
  | intervalJoin _ _ => nomatch firedEq
  | pathLam _ _ _ _ => nomatch firedEq
  | glueIntro _ _ _ _ => nomatch firedEq
  | transp _ _ _ _ _ _ _ _ => nomatch firedEq
  | hcomp _ _ => nomatch firedEq
  | hcompPath _ _ _ _ => nomatch firedEq
  | recordIntro _ => nomatch firedEq
  | recordProj _ => nomatch firedEq
  | refineIntro _ _ _ => nomatch firedEq
  | refineElim _ => nomatch firedEq
  | codataUnfold _ _ => nomatch firedEq
  | codataDest _ => nomatch firedEq
  | sessionSend _ _ _ => nomatch firedEq
  | sessionRecv _ => nomatch firedEq
  | effectPerform _ _ _ _ _ _ => nomatch firedEq
  | universeCode _ _ _ _ => nomatch firedEq
  | cumulUp _ _ _ _ _ _ => nomatch firedEq
  | equivReflId _ => nomatch firedEq
  | funextRefl _ _ _ => nomatch firedEq
  | equivReflIdAtId _ _ _ _ => nomatch firedEq
  | funextReflAtId _ _ _ => nomatch firedEq
  | equivIntroHet _ _ _ _ => nomatch firedEq
  | equivApp _ _ => nomatch firedEq
  | uaIntroHet _ _ _ _ _ => nomatch firedEq
  | funextIntroHet _ _ _ _ => nomatch firedEq
  -- Phase D3.6-P3: univalence-β extractor.  Returns `none` from
  -- headStep?, so `firedEq : none = some _` is contradictory.
  | uaToEquiv _ _ _ _ _ _ _ => nomatch firedEq
  -- Phase D3.6-P4: univalence-β application.  Returns `none` from
  -- headStep?, so `firedEq : none = some _` is contradictory.
  | equivApply _ _ => nomatch firedEq
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped, all return
  -- `none` from headStep?, so `firedEq : none = some _` is contradictory).
  | arrowCode _ _ _ _ => nomatch firedEq
  | piTyCode _ _ _ _ => nomatch firedEq
  | sigmaTyCode _ _ _ _ => nomatch firedEq
  | productCode _ _ _ _ => nomatch firedEq
  | sumCode _ _ _ _ => nomatch firedEq
  | listCode _ _ _ => nomatch firedEq
  | optionCode _ _ _ => nomatch firedEq
  | eitherCode _ _ _ _ => nomatch firedEq
  | idCode _ _ _ _ _ => nomatch firedEq
  | equivCode _ _ _ _ => nomatch firedEq
  -- Eliminators not yet handled by headStep? (return none)
  | app _ _ => nomatch firedEq
  | appPi _ _ => nomatch firedEq
  | pathApp _ _ => nomatch firedEq
  | glueElim _ => nomatch firedEq
  | snd _ => nomatch firedEq
  | idJ _ _ => nomatch firedEq
  | idStrictRefl _ _ => nomatch firedEq
  | idStrictRec _ _ => nomatch firedEq
  | modElim _ => nomatch firedEq
  -- Firing eliminators.  Each delegates to its private helper above;
  -- the firing ι-rule depends on which canonical ctor the scrutinee
  -- has reduced to.
  --
  -- Pattern (from feedback_lean_match_propext_recipe.md): each helper
  -- dispatches on `scrutinee.headCtor` and cites a one-shot
  -- `headStep?` unfold lemma (`headStep<Ctor>Unfold`, proved by `rfl`)
  -- rather than re-embedding the body literal in every arm.  Hoisting
  -- the helpers AND the unfold literals keeps every proof term small,
  -- so the kernel re-checks each piece independently instead of
  -- re-typechecking one monster term.  Avoids `simp` and `by_cases`,
  -- which both leak propext on this large dep-typed match.
  | fst pairTerm =>
    exact Term.headStepSoundFst pairTerm firedEq
  | @boolElim _ _ _ _ _ _ scrutinee thenBranch elseBranch =>
    exact Term.headStepSoundBoolElim scrutinee thenBranch elseBranch firedEq
  | natElim scrutinee zeroBranch succBranch =>
    exact Term.headStepSoundNatElim scrutinee zeroBranch succBranch firedEq
  | natRec scrutinee zeroBranch succBranch =>
    exact Term.headStepSoundNatRec scrutinee zeroBranch succBranch firedEq
  | listElim scrutinee nilBranch consBranch =>
    exact Term.headStepSoundListElim scrutinee nilBranch consBranch firedEq
  | optionMatch scrutinee noneBranch someBranch =>
    exact Term.headStepSoundOptionMatch scrutinee noneBranch someBranch firedEq
  | eitherMatch scrutinee leftBranch rightBranch =>
    exact Term.headStepSoundEitherMatch scrutinee leftBranch rightBranch firedEq

end LeanFX2
