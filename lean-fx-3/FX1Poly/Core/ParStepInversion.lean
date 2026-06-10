import FX1Poly.Core.ParallelReduction

/-! # FX1Poly/Core/ParStepInversion
    — cong-only inversion of `ParStep` at the non-redex-head constructors.

The Takahashi triangle (`ParStep a b → ParStep b (completeDevelopment a)`) and its `b := a` instance
`completeDevelopment_parStep` cannot recurse directly on deep subterms (`completeDevelopment` dispatches on
the 194-constructor generator by `by_cases`, which hides the subterm relation from Lean's structural
recursion).  The viable route recurses only on the direct children spine and EXTRACTS the per-component
`ParStep`s by inverting the children's congruence reductions.

Each lemma here inverts `ParStep (mkGen C … children) target` for a constructor `C` that is NOT a
root-redex source (`lam`, `pair`, `natSucc`, `listCons`, `optionSome`, `eitherInl`, `eitherInr` — these
appear as the *function* / *scrutinee* / *witness* WITHIN a redex but are never themselves the redex
head).  For such `C` the only `ParStep` constructor whose source unifies is `cong`, so the reduct keeps
the head `C` and its components reduce pointwise.  These are exactly the constructors whose redex
contractum embeds a developed sub-component (β extracts the λ-body; ι-`fst`/`snd` extract the pair
components; ι-`natElimSucc`/`natRecSucc` extract the `succ` predecessor; ι-`listElimCons` extracts the
`cons` head and tail; ι-`optionMatchSome`/`eitherMatchInl`/`eitherMatchInr` extract the wrapped value).

## Zero-axiom verification

Each is `cases step` (unification rules out the β/ι arms — their sources are `app`/eliminator cells, not
`C`), then `cases` on the resulting `ParStepChildren` cons-spine down to `nil`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Inversion of `ParStep` at a λ.**  A parallel reduct of `lam body` is `lam body'` with the body
reduced — the extraction the triangle's β arm needs from the cong-reduced function child. -/
theorem ParStep.lam_inv {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_lam ()
      (.childCons domainAnn (.childCons body .childNil))) target) :
    ∃ (domainAnn' : RawTerm scope) (body' : RawTerm (scope + 1)),
      target = .mkGen .gen_lam () (.childCons domainAnn' (.childCons body' .childNil)) ∧
        ParStep domainAnn domainAnn' ∧ ParStep body body' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons domainStep tailStep =>
          cases tailStep with
          | cons bodyStep tailStep2 =>
              cases tailStep2 with | nil => exact ⟨_, _, rfl, domainStep, bodyStep⟩

/-- **Inversion of `ParStep` at a pair.**  A parallel reduct of `pair a b` is `pair a' b'` with both
components reduced — the extraction the `fst`/`snd` ι arms need. -/
theorem ParStep.pair_inv {scope : Nat} {firstValue secondValue : RawTerm scope}
    {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_pair ()
      (.childCons firstValue (.childCons secondValue .childNil))) target) :
    ∃ firstValue' secondValue' : RawTerm scope,
      target = .mkGen .gen_pair () (.childCons firstValue' (.childCons secondValue' .childNil)) ∧
        ParStep firstValue firstValue' ∧ ParStep secondValue secondValue' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep =>
          cases tailStep with
          | cons headStep2 tailStep2 =>
              cases tailStep2 with | nil => exact ⟨_, _, rfl, headStep, headStep2⟩

/-- **Inversion of `ParStep` at `natSucc`.**  A parallel reduct of `natSucc n` is `natSucc n'` with the
predecessor reduced — the extraction the `natElimSucc`/`natRecSucc` ι arms need. -/
theorem ParStep.natSucc_inv {scope : Nat} {predecessor : RawTerm scope} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) target) :
    ∃ predecessor' : RawTerm scope,
      target = .mkGen .gen_natSucc () (.childCons predecessor' .childNil) ∧
        ParStep predecessor predecessor' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep => cases tailStep with | nil => exact ⟨_, rfl, headStep⟩

/-- **Inversion of `ParStep` at `listCons`.**  A parallel reduct of `listCons h t` is `listCons h' t'`
with head and tail reduced — the extraction the `listElimCons` ι arm needs. -/
theorem ParStep.listCons_inv {scope : Nat} {headValue tailValue : RawTerm scope}
    {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_listCons ()
      (.childCons headValue (.childCons tailValue .childNil))) target) :
    ∃ headValue' tailValue' : RawTerm scope,
      target = .mkGen .gen_listCons () (.childCons headValue' (.childCons tailValue' .childNil)) ∧
        ParStep headValue headValue' ∧ ParStep tailValue tailValue' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep =>
          cases tailStep with
          | cons headStep2 tailStep2 =>
              cases tailStep2 with | nil => exact ⟨_, _, rfl, headStep, headStep2⟩

/-- **Inversion of `ParStep` at `optionSome`.**  A parallel reduct of `optionSome v` is `optionSome v'`
with the wrapped value reduced — the extraction the `optionMatchSome` ι arm needs. -/
theorem ParStep.optionSome_inv {scope : Nat} {value : RawTerm scope} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_optionSome () (.childCons value .childNil)) target) :
    ∃ value' : RawTerm scope,
      target = .mkGen .gen_optionSome () (.childCons value' .childNil) ∧ ParStep value value' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep => cases tailStep with | nil => exact ⟨_, rfl, headStep⟩

/-- **Inversion of `ParStep` at `eitherInl`.**  A parallel reduct of `eitherInl v` is `eitherInl v'`
with the wrapped value reduced — the extraction the `eitherMatchInl` ι arm needs. -/
theorem ParStep.eitherInl_inv {scope : Nat} {value : RawTerm scope} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_eitherInl () (.childCons value .childNil)) target) :
    ∃ value' : RawTerm scope,
      target = .mkGen .gen_eitherInl () (.childCons value' .childNil) ∧ ParStep value value' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep => cases tailStep with | nil => exact ⟨_, rfl, headStep⟩

/-- **Inversion of `ParStep` at `eitherInr`.**  A parallel reduct of `eitherInr v` is `eitherInr v'`
with the wrapped value reduced — the extraction the `eitherMatchInr` ι arm needs. -/
theorem ParStep.eitherInr_inv {scope : Nat} {value : RawTerm scope} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_eitherInr () (.childCons value .childNil)) target) :
    ∃ value' : RawTerm scope,
      target = .mkGen .gen_eitherInr () (.childCons value' .childNil) ∧ ParStep value value' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep => cases tailStep with | nil => exact ⟨_, rfl, headStep⟩

/-! ### Nullary scrutinee / witness inversions.

The redex *scrutinees*/*witnesses* with no extracted sub-component: `boolTrue`/`boolFalse` (boolElim
scrutinees), `natZero` (natElim/natRec scrutinee), `listNil` (listElim scrutinee), `optionNone`
(optionMatch scrutinee), and `refl` (idJ/idStrictRec witness).  The full triangle's cong-arm needs these
to recognize that a cong-reduced redex is STILL a syntactic redex — e.g. from `ParStep boolTrue sc'` it
learns `sc' = boolTrue`, so `boolElim sc' …` after cong is still a `boolElim`-true redex that fires.  The
nullary ones invert to a bare equality (no child reduces); `refl` keeps its witness reduced. -/

/-- **Inversion of `ParStep` at `boolTrue`.**  `boolTrue` only parallel-reduces to `boolTrue`. -/
theorem ParStep.boolTrue_inv {scope : Nat} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_boolTrue () .childNil) target) :
    target = .mkGen .gen_boolTrue () .childNil := by
  cases step with | cong gen payload childrenStep => cases childrenStep with | nil => rfl

/-- **Inversion of `ParStep` at `boolFalse`.**  `boolFalse` only parallel-reduces to `boolFalse`. -/
theorem ParStep.boolFalse_inv {scope : Nat} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_boolFalse () .childNil) target) :
    target = .mkGen .gen_boolFalse () .childNil := by
  cases step with | cong gen payload childrenStep => cases childrenStep with | nil => rfl

/-- **Inversion of `ParStep` at `natZero`.**  `natZero` only parallel-reduces to `natZero`. -/
theorem ParStep.natZero_inv {scope : Nat} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_natZero () .childNil) target) :
    target = .mkGen .gen_natZero () .childNil := by
  cases step with | cong gen payload childrenStep => cases childrenStep with | nil => rfl

/-- **Inversion of `ParStep` at `listNil`.**  `listNil` only parallel-reduces to `listNil`. -/
theorem ParStep.listNil_inv {scope : Nat} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_listNil () .childNil) target) :
    target = .mkGen .gen_listNil () .childNil := by
  cases step with | cong gen payload childrenStep => cases childrenStep with | nil => rfl

/-- **Inversion of `ParStep` at `optionNone`.**  `optionNone` only parallel-reduces to `optionNone`. -/
theorem ParStep.optionNone_inv {scope : Nat} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_optionNone () .childNil) target) :
    target = .mkGen .gen_optionNone () .childNil := by
  cases step with | cong gen payload childrenStep => cases childrenStep with | nil => rfl

/-- **Inversion of `ParStep` at `refl`.**  A parallel reduct of `refl witness` is `refl witness'` with the
witness reduced — the idJ/idStrictRec ι arms need only that the reduct is still a `refl` (the witness is
not used in the contractum, but it must be present for the redex to fire). -/
theorem ParStep.refl_inv {scope : Nat} {witness : RawTerm scope} {target : RawTerm scope}
    (step : ParStep (.mkGen .gen_refl () (.childCons witness .childNil)) target) :
    ∃ witness' : RawTerm scope,
      target = .mkGen .gen_refl () (.childCons witness' .childNil) ∧ ParStep witness witness' := by
  cases step with
  | cong gen payload childrenStep =>
      cases childrenStep with
      | cons headStep tailStep => cases tailStep with | nil => exact ⟨_, rfl, headStep⟩

end FX1Poly.Core
