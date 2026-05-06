import LeanFX2.Reduction.CumulCastElim

/-! # Reduction/CumulBenton — BHKM per-Term-ctor rename arms (Pattern 2)

Per-Term-ctor rename helpers that lift an inner `ConvCumul` over
RENAMED inner subterms to an outer `ConvCumul` over RENAMED outer
terms.  Each helper is a direct mirror of the Allais arm structure
(`Reduction/CumulAllais.lean`), but using `Term.rename` instead of
`Term.substHet`.

## Why per-ctor helpers and NOT a recursive headline

A recursive headline `ConvCumul.rename_compatible_benton` of the
shape

```
ConvCumul firstTerm secondTerm →
  ConvCumul (firstTerm.rename termRenaming) (secondTerm.rename termRenaming)
```

is GENUINELY UNSHIPPABLE at zero axioms in Lean 4.29.1.  The
architectural blocker:

* `ConvCumul.viaUp` introduces a Term at an INDEPENDENT lower
  scope `scopeLow` (not the outer scope being renamed).  The
  ctor's first index `lowerTerm : Term ctxLow ...` and second
  index `Term.cumulUp ... lowerTerm : Term ctxHigh ...` live at
  fundamentally different scopes/levels.

* When trying to "rename through outer scope" (a single
  `TermRenaming` for outer scope), the LHS `lowerTerm.rename _`
  is ill-typed because `termRenaming` is for outer scope and
  `lowerTerm` is at inner scope.

* Lean 4.29.1's `cases cumulRel` / `induction cumulRel` /
  term-mode `match cumulRel with | .viaUp ...` ALL hit the
  hard wall:

  ```
  Dependent elimination failed: Failed to solve equation
    lowerLevel.toNat = higherLevel.toNat
  ```

  Even in the homogeneous-source case (firstTerm and secondTerm
  at the same outer ctx/level/scope), Lean's matcher tries to
  unify viaUp's output indices and chokes on the propositional
  level constraint.  The constraint is REAL — viaUp could only
  match if `lowerLevel = higherLevel`, but Lean cannot reduce
  this propositionally without further hypotheses.

* `recOn` works in principle, but requires a UNIFORM motive
  across all ConvCumul ctors.  No such uniform motive exists for
  "rename through outer scope" because viaUp's `lowerTerm`
  cannot be renamed by the outer-scope termRenaming.

This wall is documented in `Reduction/Cumul.lean` §1097-1124 and
verified empirically (test cases in pre-commit working sketches).

## What we ship instead

The directive's HARD ESCAPE ROUTE: per-ctor helpers that take
ALREADY-RENAMED inner ConvCumul and produce RENAMED outer
ConvCumul.  Each helper has a real body using its inputs
substantively.  Downstream callers compose them as needed.

## Reference

Benton, Hur, Kennedy, McBride, *Strongly Typed Term
Representations in Coq*, JAR 2012 §6 (the cong-by-cong
substitution-respect ladder).  FX memory
`reference_pattern_bhkm_ladder`.

## Audit

All shipped helpers verified zero-axiom under strict policy in
`Smoke/AuditCumulSubstCompat.lean`.
-/

namespace LeanFX2

/-! ## Closed-payload rename arms (refl) -/

/-- Benton rename arm for `unit`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_unit_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.unit (context := sourceCtx)).rename termRenaming)
              ((Term.unit (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `boolTrue`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_boolTrue_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.boolTrue (context := sourceCtx)).rename termRenaming)
              ((Term.boolTrue (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `boolFalse`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_boolFalse_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.boolFalse (context := sourceCtx)).rename termRenaming)
              ((Term.boolFalse (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `natZero`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_natZero_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.natZero (context := sourceCtx)).rename termRenaming)
              ((Term.natZero (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `var`: both sides rename to the same Term
(single termRenaming applied to both — identical result), refl. -/
theorem ConvCumul.rename_compatible_var_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    ConvCumul ((Term.var (context := sourceCtx) position).rename termRenaming)
              ((Term.var (context := sourceCtx) position).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `universeCode`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_universeCode_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    ConvCumul ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).rename termRenaming)
              ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `listNil`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_listNil_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (elementType : Ty level sourceScope) :
    ConvCumul ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).rename termRenaming)
              ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `optionNone`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_optionNone_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (elementType : Ty level sourceScope) :
    ConvCumul ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).rename termRenaming)
              ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `refl` (identity-type witness): closed
payload, refl. -/
theorem ConvCumul.rename_compatible_refl_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.refl (context := sourceCtx) carrier rawWitness).rename termRenaming)
              ((Term.refl (context := sourceCtx) carrier rawWitness).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `cumulUp` — Phase CUMUL-2.6 Design D.
Term.rename's cumulUp arm recurses on typeCode; result is
ConvCumul.refl on the substituted shape. -/
theorem ConvCumul.rename_compatible_cumulUp_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw) :
    ConvCumul ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).rename termRenaming)
              ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).rename termRenaming) :=
  ConvCumul.refl _

/-! ## Single-subterm cong rename arms

Each takes an already-renamed inner ConvCumul on the substituent
subterm and produces the renamed outer ConvCumul via the matching
cong rule. -/

/-- Benton rename arm for `natSucc`: single-subterm cong via `natSuccCong`. -/
theorem ConvCumul.rename_compatible_natSucc_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {predecessorRawFirst predecessorRawSecond : RawTerm sourceScope}
    {predecessorFirst : Term sourceCtx Ty.nat predecessorRawFirst}
    {predecessorSecond : Term sourceCtx Ty.nat predecessorRawSecond}
    (predecessorRel :
      ConvCumul (predecessorFirst.rename termRenaming)
                (predecessorSecond.rename termRenaming)) :
    ConvCumul ((Term.natSucc predecessorFirst).rename termRenaming)
              ((Term.natSucc predecessorSecond).rename termRenaming) :=
  ConvCumul.natSuccCong predecessorRel

/-- Benton rename arm for `optionSome`: single-subterm cong via `optionSomeCong`. -/
theorem ConvCumul.rename_compatible_optionSome_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx elementType valueRawFirst}
    {valueSecond : Term sourceCtx elementType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.optionSome valueFirst).rename termRenaming)
              ((Term.optionSome valueSecond).rename termRenaming) :=
  ConvCumul.optionSomeCong valueRel

/-- Benton rename arm for `eitherInl`: single-subterm cong via `eitherInlCong`. -/
theorem ConvCumul.rename_compatible_eitherInl_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx leftType valueRawFirst}
    {valueSecond : Term sourceCtx leftType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.eitherInl (rightType := rightType) valueFirst).rename termRenaming)
              ((Term.eitherInl (rightType := rightType) valueSecond).rename termRenaming) :=
  ConvCumul.eitherInlCong valueRel

/-- Benton rename arm for `eitherInr`: single-subterm cong via `eitherInrCong`. -/
theorem ConvCumul.rename_compatible_eitherInr_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx rightType valueRawFirst}
    {valueSecond : Term sourceCtx rightType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.eitherInr (leftType := leftType) valueFirst).rename termRenaming)
              ((Term.eitherInr (leftType := leftType) valueSecond).rename termRenaming) :=
  ConvCumul.eitherInrCong valueRel

/-- Benton rename arm for `modIntro`: single-subterm cong via `modIntroCong`. -/
theorem ConvCumul.rename_compatible_modIntro_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.modIntro innerFirst).rename termRenaming)
              ((Term.modIntro innerSecond).rename termRenaming) :=
  ConvCumul.modIntroCong innerRel

/-- Benton rename arm for `modElim`: single-subterm cong via `modElimCong`. -/
theorem ConvCumul.rename_compatible_modElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.modElim innerFirst).rename termRenaming)
              ((Term.modElim innerSecond).rename termRenaming) :=
  ConvCumul.modElimCong innerRel

/-- Benton rename arm for `subsume`: single-subterm cong via `subsumeCong`. -/
theorem ConvCumul.rename_compatible_subsume_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.subsume innerFirst).rename termRenaming)
              ((Term.subsume innerSecond).rename termRenaming) :=
  ConvCumul.subsumeCong innerRel

/-- Benton rename arm for `fst`: single-subterm cong via `fstCong`. -/
theorem ConvCumul.rename_compatible_fst_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawFirst pairRawSecond : RawTerm sourceScope}
    {pairFirst : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawFirst}
    {pairSecond : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSecond}
    (pairRel :
      ConvCumul (pairFirst.rename termRenaming)
                (pairSecond.rename termRenaming)) :
    ConvCumul ((Term.fst pairFirst).rename termRenaming)
              ((Term.fst pairSecond).rename termRenaming) :=
  ConvCumul.fstCong pairRel

/-- Benton rename arm for `snd`: single-subterm cong via `sndCong`
plus BHKM cast handling.

`Term.rename`'s `snd` arm wraps the result in
`(Ty.subst0_rename_commute ...).symm ▸ Term.snd (...)`.  The casts
on the two sides DIFFER (different pairRaws → different
`RawTerm.fst` projections), so we use `cast_eq_left_benton` for
LHS and `cast_eq_right_benton` for RHS chained with `sndCong`. -/
theorem ConvCumul.rename_compatible_snd_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawFirst pairRawSecond : RawTerm sourceScope}
    {pairFirst : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawFirst}
    {pairSecond : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSecond}
    (pairRel :
      ConvCumul (pairFirst.rename termRenaming)
                (pairSecond.rename termRenaming)) :
    ConvCumul ((Term.snd pairFirst).rename termRenaming)
              ((Term.snd pairSecond).rename termRenaming) :=
  ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
    (ConvCumul.trans (ConvCumul.sndCong pairRel)
                     (ConvCumul.cast_eq_right_benton _ _))

/-! ## Multi-subterm cong rename arms -/

/-- Benton rename arm for `app`: two-subterm cong via `appCong`. -/
theorem ConvCumul.rename_compatible_app_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType codomainType : Ty level sourceScope}
    {functionRawFirst functionRawSecond argumentRawFirst argumentRawSecond :
      RawTerm sourceScope}
    {functionFirst :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawFirst}
    {functionSecond :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawSecond}
    {argumentFirst : Term sourceCtx domainType argumentRawFirst}
    {argumentSecond : Term sourceCtx domainType argumentRawSecond}
    (functionRel :
      ConvCumul (functionFirst.rename termRenaming)
                (functionSecond.rename termRenaming))
    (argumentRel :
      ConvCumul (argumentFirst.rename termRenaming)
                (argumentSecond.rename termRenaming)) :
    ConvCumul ((Term.app functionFirst argumentFirst).rename termRenaming)
              ((Term.app functionSecond argumentSecond).rename termRenaming) :=
  ConvCumul.appCong functionRel argumentRel

/-- Benton rename arm for `appPi`: two-subterm cong via `appPiCong` plus
BHKM cast handling.

`Term.rename`'s `appPi` arm wraps the result in
`(Ty.subst0_rename_commute ...).symm ▸ Term.appPi ...`.  The
casts on the two sides differ (different argumentRaws), so we
chain `cast_eq_left_benton`, `appPiCong`, `cast_eq_right_benton`. -/
theorem ConvCumul.rename_compatible_appPi_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRawFirst functionRawSecond argumentRawFirst argumentRawSecond :
      RawTerm sourceScope}
    {functionFirst :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawFirst}
    {functionSecond :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawSecond}
    {argumentFirst : Term sourceCtx domainType argumentRawFirst}
    {argumentSecond : Term sourceCtx domainType argumentRawSecond}
    (functionRel :
      ConvCumul (functionFirst.rename termRenaming)
                (functionSecond.rename termRenaming))
    (argumentRel :
      ConvCumul (argumentFirst.rename termRenaming)
                (argumentSecond.rename termRenaming)) :
    ConvCumul ((Term.appPi functionFirst argumentFirst).rename termRenaming)
              ((Term.appPi functionSecond argumentSecond).rename termRenaming) :=
  ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
    (ConvCumul.trans (ConvCumul.appPiCong functionRel argumentRel)
                     (ConvCumul.cast_eq_right_benton _ _))

/-- Benton rename arm for `pair`: two-subterm cong via `pairCong` plus
BHKM cast handling on the second component.

`Term.rename`'s `pair` arm wraps the second component in
`Ty.subst0_rename_commute ... ▸ ...`.  The casts on the two
sides differ (firstRawFirst vs firstRawSecond), so we apply
`cast_eq_left_benton` to LHS and `cast_eq_right_benton` to RHS,
chained via `ConvCumul.trans`. -/
theorem ConvCumul.rename_compatible_pair_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRawFirst firstRawSecond secondRawFirst secondRawSecond :
      RawTerm sourceScope}
    {firstValueFirst : Term sourceCtx firstType firstRawFirst}
    {firstValueSecond : Term sourceCtx firstType firstRawSecond}
    {secondValueFirst :
      Term sourceCtx (secondType.subst0 firstType firstRawFirst) secondRawFirst}
    {secondValueSecond :
      Term sourceCtx (secondType.subst0 firstType firstRawSecond) secondRawSecond}
    (firstRel :
      ConvCumul (firstValueFirst.rename termRenaming)
                (firstValueSecond.rename termRenaming))
    (secondRel :
      ConvCumul (secondValueFirst.rename termRenaming)
                (secondValueSecond.rename termRenaming)) :
    ConvCumul ((Term.pair firstValueFirst secondValueFirst).rename termRenaming)
              ((Term.pair firstValueSecond secondValueSecond).rename termRenaming) :=
  ConvCumul.pairCong firstRel
    (ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
       (ConvCumul.trans secondRel
                        (ConvCumul.cast_eq_right_benton _ _)))

/-- Benton rename arm for `listCons`: two-subterm cong via `listConsCong`. -/
theorem ConvCumul.rename_compatible_listCons_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType : Ty level sourceScope}
    {headRawFirst headRawSecond tailRawFirst tailRawSecond : RawTerm sourceScope}
    {headFirst : Term sourceCtx elementType headRawFirst}
    {headSecond : Term sourceCtx elementType headRawSecond}
    {tailFirst : Term sourceCtx (Ty.listType elementType) tailRawFirst}
    {tailSecond : Term sourceCtx (Ty.listType elementType) tailRawSecond}
    (headRel :
      ConvCumul (headFirst.rename termRenaming)
                (headSecond.rename termRenaming))
    (tailRel :
      ConvCumul (tailFirst.rename termRenaming)
                (tailSecond.rename termRenaming)) :
    ConvCumul ((Term.listCons headFirst tailFirst).rename termRenaming)
              ((Term.listCons headSecond tailSecond).rename termRenaming) :=
  ConvCumul.listConsCong headRel tailRel

/-- Benton rename arm for `idJ`: two-subterm cong via `idJCong`. -/
theorem ConvCumul.rename_compatible_idJ_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawFirst baseRawSecond witnessRawFirst witnessRawSecond :
      RawTerm sourceScope}
    {baseFirst : Term sourceCtx motiveType baseRawFirst}
    {baseSecond : Term sourceCtx motiveType baseRawSecond}
    {witnessFirst :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawFirst}
    {witnessSecond :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSecond}
    (baseRel :
      ConvCumul (baseFirst.rename termRenaming)
                (baseSecond.rename termRenaming))
    (witnessRel :
      ConvCumul (witnessFirst.rename termRenaming)
                (witnessSecond.rename termRenaming)) :
    ConvCumul ((Term.idJ baseFirst witnessFirst).rename termRenaming)
              ((Term.idJ baseSecond witnessSecond).rename termRenaming) :=
  ConvCumul.idJCong baseRel witnessRel

/-- Benton rename arm for `boolElim`: three-subterm cong via `boolElimCong`. -/
theorem ConvCumul.rename_compatible_boolElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutineeRawFirst scrutineeRawSecond
     thenRawFirst thenRawSecond elseRawFirst elseRawSecond : RawTerm sourceScope}
    {scrutineeFirst : Term sourceCtx Ty.bool scrutineeRawFirst}
    {scrutineeSecond : Term sourceCtx Ty.bool scrutineeRawSecond}
    {thenBranchFirst : Term sourceCtx motiveType thenRawFirst}
    {thenBranchSecond : Term sourceCtx motiveType thenRawSecond}
    {elseBranchFirst : Term sourceCtx motiveType elseRawFirst}
    {elseBranchSecond : Term sourceCtx motiveType elseRawSecond}
    (scrutineeRel :
      ConvCumul (scrutineeFirst.rename termRenaming)
                (scrutineeSecond.rename termRenaming))
    (thenRel :
      ConvCumul (thenBranchFirst.rename termRenaming)
                (thenBranchSecond.rename termRenaming))
    (elseRel :
      ConvCumul (elseBranchFirst.rename termRenaming)
                (elseBranchSecond.rename termRenaming)) :
    ConvCumul (Term.rename termRenaming
                 (Term.boolElim scrutineeFirst thenBranchFirst elseBranchFirst))
              (Term.rename termRenaming
                 (Term.boolElim scrutineeSecond thenBranchSecond elseBranchSecond)) :=
  ConvCumul.boolElimCong scrutineeRel thenRel elseRel

/-! ## Binder cong rename arms

The binder cases (`lam` / `lamPi`) require a LIFTED termRenaming in
the body's recursive call.  `Term.rename`'s `lam` arm wraps the
body in `Ty.weaken_rename_commute ▸ Term.rename termRenaming.lift body`,
so the inner ConvCumul must already be on body terms renamed by
`termRenaming.lift _`.  `cast_eq_both_benton` peels the cast
identically across the two sides. -/

/-- Benton rename arm for `lam`: binder cong via `lamCong` plus BHKM
cast handling.

`Term.rename`'s `lam` arm produces
`Term.lam (Ty.weaken_rename_commute ... ▸ body.rename (termRenaming.lift _))`.
The cast `Ty.weaken_rename_commute ...` is propositional, identical
on both sides, peeled via `cast_eq_both_benton`. -/
theorem ConvCumul.rename_compatible_lam_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType codomainType : Ty level sourceScope}
    {bodyRawFirst bodyRawSecond : RawTerm (sourceScope + 1)}
    {bodyFirst : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawFirst}
    {bodySecond : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawSecond}
    (bodyRel :
      ConvCumul (bodyFirst.rename (termRenaming.lift domainType))
                (bodySecond.rename (termRenaming.lift domainType))) :
    ConvCumul ((Term.lam bodyFirst).rename termRenaming)
              ((Term.lam bodySecond).rename termRenaming) :=
  ConvCumul.lamCong (ConvCumul.cast_eq_both_benton _ bodyRel)

/-- Benton rename arm for `lamPi`: binder cong via `lamPiCong`.

`Term.rename`'s `lamPi` arm has NO cast (body type is just
codomainType in extended scope).  Direct cong application. -/
theorem ConvCumul.rename_compatible_lamPi_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRawFirst bodyRawSecond : RawTerm (sourceScope + 1)}
    {bodyFirst : Term (sourceCtx.cons domainType) codomainType bodyRawFirst}
    {bodySecond : Term (sourceCtx.cons domainType) codomainType bodyRawSecond}
    (bodyRel :
      ConvCumul (bodyFirst.rename (termRenaming.lift domainType))
                (bodySecond.rename (termRenaming.lift domainType))) :
    ConvCumul ((Term.lamPi bodyFirst).rename termRenaming)
              ((Term.lamPi bodySecond).rename termRenaming) :=
  ConvCumul.lamPiCong bodyRel

/-! ## Benton eliminator rename arms (5) -/

/-- Benton rename arm for `natElim`: three-subterm cong via `natElimCong`. -/
theorem ConvCumul.rename_compatible_natElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw zeroFirstRaw zeroSecondRaw
     succFirstRaw succSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx Ty.nat scrutFirstRaw}
    {scrutSecond : Term sourceCtx Ty.nat scrutSecondRaw}
    {zeroFirst : Term sourceCtx motiveType zeroFirstRaw}
    {zeroSecond : Term sourceCtx motiveType zeroSecondRaw}
    {succFirst : Term sourceCtx (Ty.arrow Ty.nat motiveType) succFirstRaw}
    {succSecond : Term sourceCtx (Ty.arrow Ty.nat motiveType) succSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (zeroRel :
      ConvCumul (zeroFirst.rename termRenaming) (zeroSecond.rename termRenaming))
    (succRel :
      ConvCumul (succFirst.rename termRenaming) (succSecond.rename termRenaming)) :
    ConvCumul ((Term.natElim scrutFirst zeroFirst succFirst).rename termRenaming)
              ((Term.natElim scrutSecond zeroSecond succSecond).rename termRenaming) :=
  ConvCumul.natElimCong scrutRel zeroRel succRel

/-- Benton rename arm for `natRec`: three-subterm cong via `natRecCong`. -/
theorem ConvCumul.rename_compatible_natRec_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw zeroFirstRaw zeroSecondRaw
     succFirstRaw succSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx Ty.nat scrutFirstRaw}
    {scrutSecond : Term sourceCtx Ty.nat scrutSecondRaw}
    {zeroFirst : Term sourceCtx motiveType zeroFirstRaw}
    {zeroSecond : Term sourceCtx motiveType zeroSecondRaw}
    {succFirst :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succFirstRaw}
    {succSecond :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (zeroRel :
      ConvCumul (zeroFirst.rename termRenaming) (zeroSecond.rename termRenaming))
    (succRel :
      ConvCumul (succFirst.rename termRenaming) (succSecond.rename termRenaming)) :
    ConvCumul ((Term.natRec scrutFirst zeroFirst succFirst).rename termRenaming)
              ((Term.natRec scrutSecond zeroSecond succSecond).rename termRenaming) :=
  ConvCumul.natRecCong scrutRel zeroRel succRel

/-- Benton rename arm for `listElim`: three-subterm cong via `listElimCong`. -/
theorem ConvCumul.rename_compatible_listElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw nilFirstRaw nilSecondRaw
     consFirstRaw consSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.listType elementType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.listType elementType) scrutSecondRaw}
    {nilFirst : Term sourceCtx motiveType nilFirstRaw}
    {nilSecond : Term sourceCtx motiveType nilSecondRaw}
    {consFirst :
      Term sourceCtx (Ty.arrow elementType
                       (Ty.arrow (Ty.listType elementType) motiveType)) consFirstRaw}
    {consSecond :
      Term sourceCtx (Ty.arrow elementType
                       (Ty.arrow (Ty.listType elementType) motiveType)) consSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (nilRel :
      ConvCumul (nilFirst.rename termRenaming) (nilSecond.rename termRenaming))
    (consRel :
      ConvCumul (consFirst.rename termRenaming) (consSecond.rename termRenaming)) :
    ConvCumul ((Term.listElim scrutFirst nilFirst consFirst).rename termRenaming)
              ((Term.listElim scrutSecond nilSecond consSecond).rename termRenaming) :=
  ConvCumul.listElimCong scrutRel nilRel consRel

/-- Benton rename arm for `optionMatch`: three-subterm cong via `optionMatchCong`. -/
theorem ConvCumul.rename_compatible_optionMatch_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw noneFirstRaw noneSecondRaw
     someFirstRaw someSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.optionType elementType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.optionType elementType) scrutSecondRaw}
    {noneFirst : Term sourceCtx motiveType noneFirstRaw}
    {noneSecond : Term sourceCtx motiveType noneSecondRaw}
    {someFirst : Term sourceCtx (Ty.arrow elementType motiveType) someFirstRaw}
    {someSecond : Term sourceCtx (Ty.arrow elementType motiveType) someSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (noneRel :
      ConvCumul (noneFirst.rename termRenaming) (noneSecond.rename termRenaming))
    (someRel :
      ConvCumul (someFirst.rename termRenaming) (someSecond.rename termRenaming)) :
    ConvCumul
      ((Term.optionMatch scrutFirst noneFirst someFirst).rename termRenaming)
      ((Term.optionMatch scrutSecond noneSecond someSecond).rename termRenaming) :=
  ConvCumul.optionMatchCong scrutRel noneRel someRel

/-- Benton rename arm for `eitherMatch`: three-subterm cong via `eitherMatchCong`. -/
theorem ConvCumul.rename_compatible_eitherMatch_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw leftFirstRaw leftSecondRaw
     rightFirstRaw rightSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.eitherType leftType rightType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.eitherType leftType rightType) scrutSecondRaw}
    {leftFirst : Term sourceCtx (Ty.arrow leftType motiveType) leftFirstRaw}
    {leftSecond : Term sourceCtx (Ty.arrow leftType motiveType) leftSecondRaw}
    {rightFirst : Term sourceCtx (Ty.arrow rightType motiveType) rightFirstRaw}
    {rightSecond : Term sourceCtx (Ty.arrow rightType motiveType) rightSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (leftRel :
      ConvCumul (leftFirst.rename termRenaming) (leftSecond.rename termRenaming))
    (rightRel :
      ConvCumul (rightFirst.rename termRenaming) (rightSecond.rename termRenaming)) :
    ConvCumul
      ((Term.eitherMatch scrutFirst leftFirst rightFirst).rename termRenaming)
      ((Term.eitherMatch scrutSecond leftSecond rightSecond).rename termRenaming) :=
  ConvCumul.eitherMatchCong scrutRel leftRel rightRel

end LeanFX2
