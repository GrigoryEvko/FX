import LeanFX2.Term.StrengtheningImage.ImageUnweaken

/-! # Term/StrengtheningImage/TotalOnWeakenCore

Total-on-weaken predicate, cast invariance, closed atom, variable, and unary basic constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Closed-atomic unweaken? totality

The headline `Term.unweaken?_weaken : ∀ originalTerm newType,
  Term.unweaken? (Term.weaken newType originalTerm) = some originalTerm`
is the universal totality theorem on the weakening image.  A full
78-case structural induction proving it is mechanical — atomic ctors
reduce by `rfl`; recursive ctors compose via the per-ctor strengthening
builders and an `IsTotalOnWeaken` predicate.

This section ships the **closed-atomic foundation**: every ctor whose
typed `Term.weaken`-of-self reduces to a syntactic `Term.<ctor>` with
no per-ctor data carried at the surface (no element type, no codomain,
no payload).  Each such case is a one-line `rfl` because:

* `Term.weaken nt (Term.<ctor>) = Term.<ctor>` definitionally — `Term.rename`
  on a 0-arg ctor reduces directly.
* `partialStrengthenTyped? (Term.<ctor>)` is the dispatcher's closed-atomic
  arm, returning a concrete `StrengtheningResult` built from
  `partialStrengthenTyped<Ctor>` whose body is trivial.
* `unweaken?` matches that success and the type/raw alignment via
  `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken` resolves to
  `Term.<ctor>` again.

The 7 ctors covered: `Term.unit`, `Term.boolTrue`, `Term.boolFalse`,
`Term.natZero`, `Term.interval0`, `Term.interval1`, plus `Term.var`
whose `Fin.succ position` shape exhibits the same structural success.

Each theorem here is a CONCRETE totality witness — not a universal
headline — and is consumable directly by Step.eta-cascade subject
reduction proofs whose source-side term is one of these atomic
constructors.  The remaining 71 recursive ctors land in follow-up
phases using the `IsTotalOnWeaken` predicate (Term-level totality
counterpart to `RawTerm.usesNewestSlot?` at the raw layer). -/

/-- Total-on-weaken predicate: a typed term whose weakening under any
new binder allows the typed strengthening dispatcher to succeed.  The
universal headline `∀ sourceTerm, IsTotalOnWeaken sourceTerm` is
provable by structural induction with 78 per-ctor cases; this file
ships the predicate plus the closed-atomic base cases. -/
def IsTotalOnWeaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) : Prop :=
  ∀ (newType : Ty level scope),
    (strengthenTyped? (Term.weaken newType sourceTerm)).isSome

/-- Cast-invariance helper: `strengthenTyped?.isSome` is invariant under
a propositional cast on the Term's `Ty` index.

This is the load-bearing helper for totality proofs of the 7
Eq.mpr-blocked ctors (appPi, snd, pair, boolElim, funextRefl,
equivIntroHet, oeqFunext): their `Term.weaken` arm produces a term
wrapped in `Eq.mpr h _` due to `Ty.subst0_rename_commute.symm ▸ ...`,
which blocks pattern-matching in the strengthening dispatcher.  This
lemma reduces the cast term's `.isSome` to the un-cast form by
discharging the equation via `cases h`.

The motive is implicit: `fun (T : Ty level (scope+1)) => Term ctx T R`
where `R` is fixed (since `weaken`'s raw-side computation has no cast). -/
theorem strengthenTyped?_isSome_castInvariant
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceTypeA sourceTypeB : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceTypeA sourceRaw)
    (typeEq : sourceTypeA = sourceTypeB) :
    (typeEq ▸ sourceTerm).strengthenTyped?.isSome =
      sourceTerm.strengthenTyped?.isSome := by
  cases typeEq
  rfl

/-- Closed-atomic totality: `Term.unit` strengthens through any
weakening.  Direct `rfl`-witness. -/
theorem isTotalOnWeaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.unit (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolTrue`. -/
theorem isTotalOnWeaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolTrue (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolFalse`. -/
theorem isTotalOnWeaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolFalse (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.natZero`. -/
theorem isTotalOnWeaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.natZero (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval0`. -/
theorem isTotalOnWeaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval0 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval1`. -/
theorem isTotalOnWeaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval1 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.var`.  The variable's renaming under
weakening lands at `Fin.succ position` which survives `dropNewest`
back to `position`. -/
theorem isTotalOnWeaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} (position : Fin scope) :
    IsTotalOnWeaken (Term.var (context := context) position) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.universeCode`.  The universe-code
ctor carries pure value-level data (`innerLevel`, `outerLevel`,
`cumulOk`, `levelLe`) — no scope-indexed payload to strengthen, so the
dispatcher's arm succeeds unconditionally and totality is direct. -/
theorem isTotalOnWeaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsTotalOnWeaken (Term.universeCode (context := context) innerLevel
      outerLevel cumulOk levelLe) := by
  intro _; rfl

/-- 1-IH non-binder totality: `Term.natSucc` is total on weaken if its
predecessor is.  Composition pattern shipped here as the canonical
template; the remaining 14 single-IH non-binder ctors (optionSome,
modIntro/Elim, subsume, eitherInl/Inr, recordIntro/Proj, refineElim,
fst, snd, intervalOpp, codataDest, sessionRecv) follow the same
unfold + split + ▸ pattern, landing per follow-up. -/
theorem isTotalOnWeaken_natSucc {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    (predecessorIH : IsTotalOnWeaken predecessor) :
    IsTotalOnWeaken (Term.natSucc predecessor) := by
  intro newType
  show (strengthenTyped? (Term.natSucc (Term.weaken newType predecessor))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next predRecurse =>
      exfalso
      have totHyp := predecessorIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType predecessor))) = true :=
        predRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.intervalOpp`.  Cubical interval
negation; sibling of `natSucc` at a different carrier type. -/
theorem isTotalOnWeaken_intervalOpp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {pointRaw : RawTerm scope}
    {point : Term context Ty.interval pointRaw}
    (pointIH : IsTotalOnWeaken point) :
    IsTotalOnWeaken (Term.intervalOpp point) := by
  intro newType
  show (strengthenTyped? (Term.intervalOpp (Term.weaken newType point))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next pointRecurse =>
      exfalso
      have totHyp := pointIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType point))) = true :=
        pointRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.optionSome`.  Option-some carries
exactly one typed payload (the wrapped value); no Ty payload to
strengthen separately. -/
theorem isTotalOnWeaken_optionSome {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.optionSome valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.optionSome (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next valueRecurse =>
      exfalso
      have totHyp := valueIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType valueTerm))) = true :=
        valueRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modIntro`.  Modal introduction;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modIntro {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modIntro innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modIntro (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modElim`.  Modal elimination;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modElim {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modElim innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modElim (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.subsume`.  Mode subsumption;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_subsume {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.subsume innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.subsume (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.cumulUp`.  Cross-level cumulativity;
carries exactly one typed payload (the source type code).  No Ty payload
to strengthen separately — the universe levels are pure Nat data. -/
theorem isTotalOnWeaken_cumulUp {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeIH : IsTotalOnWeaken typeCode) :
    IsTotalOnWeaken (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh typeCode) := by
  intro newType
  show (strengthenTyped? (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh (Term.weaken newType typeCode))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next codeRecurse =>
      exfalso
      have totHyp := codeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType typeCode))) = true :=
        codeRecurse ▸ totHyp
      cases this
  · rfl

end Term

end LeanFX2
