import LeanFX2.Algo.RawWHNF.Projections

namespace LeanFX2

/-! ## Eq-witness recovery for the projection helpers

When a typed `Term.headStep?` dispatcher uses
`RawTerm.natSuccPred?` (etc) to detect a redex, it gets only an
Option result.  To then apply the typed `Term.natSuccDestruct`,
the dispatcher needs an Eq witness that the underlying raw IS
of the form `RawTerm.natSucc predRaw`.

These helpers recover that Eq from a `some predRaw` witness via
full-enum dispatch on the raw term.  Propext-clean (RawTerm is
non-indexed). -/

/-! Five iff-recovery lemmas, one per `?`-projection helper.
Each follows the match-with-witness pattern: combine `someTerm`
with the Eq witness, and non-matching ctors auto-discharge as
`none = some _` constructor mismatch.  Propext-clean. -/

/-- `term.natSuccPred? = some predRaw` implies `term = RawTerm.natSucc predRaw`. -/
theorem RawTerm.natSuccPred?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {predRaw : RawTerm scope}
    (witness : someTerm.natSuccPred? = some predRaw) :
    someTerm = RawTerm.natSucc predRaw :=
  match someTerm, witness with
  | .natSucc innerPred, witnessEq => by
      have someEq : (some innerPred : Option (RawTerm scope)) = some predRaw :=
        witnessEq
      injection someEq with predEq
      rw [predEq]

/-- `term.pairComponents? = some (firstRaw, secondRaw)` implies
`term = RawTerm.pair firstRaw secondRaw`. -/
theorem RawTerm.pairComponents?_eq_some
    {scope : Nat} {someTerm : RawTerm scope}
    {firstRaw secondRaw : RawTerm scope}
    (witness : someTerm.pairComponents? = some (firstRaw, secondRaw)) :
    someTerm = RawTerm.pair firstRaw secondRaw :=
  match someTerm, witness with
  | .pair innerFirst innerSecond, witnessEq => by
      have someEq :
          (some (innerFirst, innerSecond) : Option (RawTerm scope × RawTerm scope))
            = some (firstRaw, secondRaw) :=
        witnessEq
      injection someEq with pairEq
      injection pairEq with firstEq secondEq
      rw [firstEq, secondEq]

/-- `term.listConsParts? = some (h, t)` implies
`term = RawTerm.listCons h t`.  Uses direct `injection` on
both Option and Prod constructors — no propext via
`Prod.mk.injEq`. -/
theorem RawTerm.listConsParts?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {headRaw tailRaw : RawTerm scope}
    (witness : someTerm.listConsParts? = some (headRaw, tailRaw)) :
    someTerm = RawTerm.listCons headRaw tailRaw :=
  match someTerm, witness with
  | .listCons innerHead innerTail, witnessEq => by
      have someEq :
          (some (innerHead, innerTail) : Option (RawTerm scope × RawTerm scope))
            = some (headRaw, tailRaw) :=
        witnessEq
      injection someEq with pairEq
      injection pairEq with headEq tailEq
      rw [headEq, tailEq]

/-- `term.optionSomeValue? = some valueRaw` implies
`term = RawTerm.optionSome valueRaw`. -/
theorem RawTerm.optionSomeValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.optionSomeValue? = some valueRaw) :
    someTerm = RawTerm.optionSome valueRaw :=
  match someTerm, witness with
  | .optionSome innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

/-- `term.eitherInlValue? = some valueRaw` implies
`term = RawTerm.eitherInl valueRaw`. -/
theorem RawTerm.eitherInlValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.eitherInlValue? = some valueRaw) :
    someTerm = RawTerm.eitherInl valueRaw :=
  match someTerm, witness with
  | .eitherInl innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

/-- `term.eitherInrValue? = some valueRaw` implies
`term = RawTerm.eitherInr valueRaw`. -/
theorem RawTerm.eitherInrValue?_eq_some
    {scope : Nat} {someTerm : RawTerm scope} {valueRaw : RawTerm scope}
    (witness : someTerm.eitherInrValue? = some valueRaw) :
    someTerm = RawTerm.eitherInr valueRaw :=
  match someTerm, witness with
  | .eitherInr innerValue, witnessEq => by
      have someEq : (some innerValue : Option (RawTerm scope)) = some valueRaw :=
        witnessEq
      injection someEq with valueEq
      rw [valueEq]

end LeanFX2
